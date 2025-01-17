// Copyright 2021 The gVisor Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

#include <stdint.h>
#include <sys/syscall.h>
#include <unistd.h>

#include "gtest/gtest.h"
#include "absl/flags/flag.h"
#include "absl/strings/str_format.h"
#include "absl/time/clock.h"
#include "absl/time/time.h"
#include "test/util/capability_util.h"
#include "test/util/multiprocess_util.h"
#include "test/util/test_util.h"
#include "test/util/thread_util.h"

ABSL_FLAG(bool, processes_test_exec_swap, false,
          "If true, run the ExecSwap function.");
ABSL_FLAG(int, processes_test_exec_swap_pre_clone_pid, -1,
          "Process ID from before clone; required when using "
          "--processes_test_exec_swap.");
ABSL_FLAG(int, processes_test_exec_swap_pre_clone_tid, -1,
          "Thread ID from before clone; required when using "
          "--processes_test_exec_swap.");
ABSL_FLAG(int, processes_test_exec_swap_pre_exec_pid, -1,
          "Process ID from before exec; required when using "
          "--processes_test_exec_swap.");
ABSL_FLAG(int, processes_test_exec_swap_pre_exec_tid, -1,
          "Thread ID from before exec; required when using "
          "--processes_test_exec_swap.");
ABSL_FLAG(int, processes_test_exec_swap_pipe_fd, -1,
          "File descriptor to write data to; required when using "
          "--processes_test_exec_swap.");

namespace gvisor {
namespace testing {

int testSetPGIDOfZombie(void* arg) {
  int p[2];

  TEST_PCHECK(pipe(p) == 0);

  pid_t pid = fork();
  if (pid == 0) {
    pid = fork();
    // Create a second child to repeat one of syzkaller reproducers.
    if (pid == 0) {
      pid = getpid();
      TEST_PCHECK(setpgid(pid, 0) == 0);
      TEST_PCHECK(write(p[1], &pid, sizeof(pid)) == sizeof(pid));
      _exit(0);
    }
    TEST_PCHECK(pid > 0);
    _exit(0);
  }
  close(p[1]);
  TEST_PCHECK(pid > 0);

  // Get PID of the second child.
  pid_t cpid;
  TEST_PCHECK(read(p[0], &cpid, sizeof(cpid)) == sizeof(cpid));

  // Wait when both child processes will die.
  int c;
  TEST_PCHECK(read(p[0], &c, sizeof(c)) == 0);

  // Wait the second child process to collect its zombie.
  int status;
  TEST_PCHECK(RetryEINTR(waitpid)(cpid, &status, 0) == cpid);

  // Set the child's group.
  TEST_PCHECK(setpgid(pid, pid) == 0);

  TEST_PCHECK(RetryEINTR(waitpid)(-pid, &status, 0) == pid);

  TEST_PCHECK(status == 0);
  _exit(0);
}

TEST(Processes, SetPGIDOfZombie) {
  SKIP_IF(!ASSERT_NO_ERRNO_AND_VALUE(HaveCapability(CAP_SYS_ADMIN)));

  // Fork a test process in a new PID namespace, because it needs to manipulate
  // with reparanted processes.
  struct clone_arg {
    // Reserve some space for clone() to locate arguments and retcode in this
    // place.
    char stack[128] __attribute__((aligned(16)));
    char stack_ptr[0];
  } ca;
  pid_t pid;
  ASSERT_THAT(pid = clone(testSetPGIDOfZombie, ca.stack_ptr,
                          CLONE_NEWPID | SIGCHLD, &ca),
              SyscallSucceeds());

  int status;
  ASSERT_THAT(RetryEINTR(waitpid)(pid, &status, 0),
              SyscallSucceedsWithValue(pid));
  EXPECT_EQ(status, 0);
}

int WritePIDToPipe(void* arg) {
  int* pipe_fds = reinterpret_cast<int*>(arg);
  pid_t child_pid;
  TEST_PCHECK(child_pid = getpid());
  TEST_PCHECK(write(pipe_fds[1], &child_pid, sizeof(child_pid)) ==
              sizeof(child_pid));
  _exit(0);
}

TEST(Processes, TheadSharesSamePID) {
  int pipe_fds[2];
  ASSERT_THAT(pipe(pipe_fds), SyscallSucceeds());
  pid_t test_pid;
  ASSERT_THAT(test_pid = getpid(), SyscallSucceeds());
  EXPECT_NE(test_pid, 0);
  struct clone_arg {
    char stack[256] __attribute__((aligned(16)));
    char stack_ptr[0];
  } ca;
  ASSERT_THAT(
      clone(WritePIDToPipe, ca.stack_ptr,
            CLONE_THREAD | CLONE_SIGHAND | CLONE_VM | CLONE_FS, pipe_fds),
      SyscallSucceeds());
  pid_t pid_from_child;
  TEST_PCHECK(read(pipe_fds[0], &pid_from_child, sizeof(pid_from_child)) ==
              sizeof(pid_from_child));
  int buf;
  TEST_PCHECK(read(pipe_fds[0], &buf, sizeof(buf)) ==
              0);  // Wait for cloned thread to exit
  ASSERT_THAT(close(pipe_fds[0]), SyscallSucceeds());
  ASSERT_THAT(close(pipe_fds[1]), SyscallSucceeds());
  EXPECT_EQ(test_pid, pid_from_child);
}

// ExecSwapResult is used to carry PIDs and TIDs in ExecSwapThreadGroupLeader.
struct ExecSwapResult {
  int pipe_fd;  // FD to write result data to.

  // PID and TID before we call clone().
  pid_t pre_clone_pid;
  pid_t pre_clone_tid;

  // PID and TID before the clone calls execv().
  pid_t pre_exec_pid;
  pid_t pre_exec_tid;

  // PID and TID after the execv().
  pid_t post_exec_pid;
  pid_t post_exec_tid;
};

// ExecSwapPostExec is the third part of the ExecSwapThreadGroupLeader test.
// It is called after the test has fork()'d, clone()'d, and exec()'d into this.
// It writes all the PIDs and TIDs from each part of the test to a pipe.
int ExecSwapPostExec() {
  std::cerr << "Test exec'd." << std::endl;
  pid_t pid;
  TEST_PCHECK(pid = getpid());
  pid_t tid;
  TEST_PCHECK(tid = gettid());
  ExecSwapResult result;
  result.pipe_fd = absl::GetFlag(FLAGS_processes_test_exec_swap_pipe_fd);
  result.pre_clone_pid =
      absl::GetFlag(FLAGS_processes_test_exec_swap_pre_clone_pid);
  result.pre_clone_tid =
      absl::GetFlag(FLAGS_processes_test_exec_swap_pre_clone_tid);
  result.pre_exec_pid =
      absl::GetFlag(FLAGS_processes_test_exec_swap_pre_exec_pid);
  result.pre_exec_tid =
      absl::GetFlag(FLAGS_processes_test_exec_swap_pre_exec_tid);
  result.post_exec_pid = pid;
  result.post_exec_tid = tid;
  std::cerr << "Test writing results to pipe FD." << std::endl;
  TEST_PCHECK(write(result.pipe_fd, &result, sizeof(result)) == sizeof(result));
  if (close(result.pipe_fd) != 0) {
    std::cerr << "Failed to close pipe FD: " << errno << std::endl;
  }
  std::cerr << "Test results written out." << std::endl;
  return 0;
}

// ExecSwapPreExec is the second part of the ExecSwapThreadGroupLeader test.
// It is called after the test has fork()'d and clone()'d.
// It calls exec() with flags that cause the test binary to run
// ExecSwapPostExec.
int ExecSwapPreExec(void* arg) {
  ExecSwapResult* result = reinterpret_cast<ExecSwapResult*>(arg);
  pid_t pid;
  TEST_PCHECK(pid = getpid());
  pid_t tid;
  TEST_PCHECK(tid = gettid());

  ExecveArray const execve_argv = {
      "/proc/self/exe",
      "--processes_test_exec_swap",
      absl::StrFormat("--processes_test_exec_swap_pre_clone_pid=%d",
                      result->pre_clone_pid),
      absl::StrFormat("--processes_test_exec_swap_pre_clone_tid=%d",
                      result->pre_clone_tid),
      absl::StrFormat("--processes_test_exec_swap_pre_exec_pid=%d", pid),
      absl::StrFormat("--processes_test_exec_swap_pre_exec_tid=%d", tid),
      absl::StrFormat("--processes_test_exec_swap_pipe_fd=%d", result->pipe_fd),
  };
  TEST_PCHECK(execv("/proc/self/exe", execve_argv.get()));
  _exit(1);  // Should be unreachable.
}

// ExecSwapPreClone is the first part of the ExecSwapThreadGroupLeader test.
// It is called after the test has fork()'d.
// It calls clone() to run ExecSwapPreExec.
void ExecSwapPreClone(int* pipe_fds) {
  pid_t pid;
  ASSERT_THAT(pid = getpid(), SyscallSucceeds());
  pid_t tid;
  ASSERT_THAT(tid = gettid(), SyscallSucceeds());
  struct clone_arg {
    char stack[4096] __attribute__((aligned(16)));
    char stack_ptr[0];
  } ca;
  ExecSwapResult result;
  result.pipe_fd = pipe_fds[1];
  result.pre_clone_pid = pid;
  result.pre_clone_tid = tid;
  std::cerr << "Test cloning." << std::endl;
  ASSERT_THAT(
      clone(ExecSwapPreExec, ca.stack_ptr,
            CLONE_THREAD | CLONE_SIGHAND | CLONE_VM | CLONE_FS, &result),
      SyscallSucceeds());
  // The clone thread will call exec, so just sit around here until it does.
  absl::SleepFor(absl::Milliseconds(500));
}

TEST(Processes, ExecSwapThreadGroupLeader) {
  // This test verifies that a non-leading thread calling exec() replaces the
  // former leader of its thread group and adopts its thread ID.
  // This is the zeroth part of this test, which calls fork() to run
  // ExecSwapPreClone in a separate thread group.

  int pipe_fds[2];
  ASSERT_THAT(pipe(pipe_fds), SyscallSucceeds());
  pid_t test_pid;
  ASSERT_THAT(test_pid = getpid(), SyscallSucceeds());
  pid_t test_tid;
  ASSERT_THAT(test_tid = gettid(), SyscallSucceeds());
  std::cerr << "Test forking." << std::endl;
  pid_t fork_pid = fork();
  if (fork_pid == 0) {
    ExecSwapPreClone(pipe_fds);
    ASSERT_TRUE(false) << "Did not get replaced by execed child";
  }

  std::cerr << "Waiting for test results." << std::endl;
  ExecSwapResult result;
  TEST_PCHECK(read(pipe_fds[0], &result, sizeof(result)) == sizeof(result));

  std::cerr << "ExecSwap results:" << std::endl;
  std::cerr << "  Parent test process PID / TID:" << test_pid << " / "
            << test_tid << std::endl;
  std::cerr << "  Parent test child PID, as seen by parent:" << fork_pid
            << std::endl;
  std::cerr << "  Pre-clone PID / TID: " << result.pre_clone_pid << " / "
            << result.pre_clone_tid << std::endl;
  std::cerr << "  Pre-exec  PID / TID: " << result.pre_exec_pid << " / "
            << result.pre_exec_tid << std::endl;
  std::cerr << "  Post-exec PID / TID: " << result.post_exec_pid << " / "
            << result.post_exec_tid << std::endl;

  ASSERT_THAT(close(pipe_fds[0]), SyscallSucceeds());
  ASSERT_THAT(close(pipe_fds[1]), SyscallSucceeds());

  // Test starts out as the thread group leader of itself.
  EXPECT_EQ(test_pid, test_tid);

  // The child is a different thread group altogether.
  EXPECT_NE(test_pid, fork_pid);
  EXPECT_EQ(fork_pid, result.pre_clone_pid);  // Sanity check.

  // Before cloning, PID == TID, the child thread is leader of its thread group.
  EXPECT_EQ(result.pre_clone_pid, result.pre_clone_tid);

  // PID should not change with clone.
  EXPECT_EQ(result.pre_clone_pid, result.pre_exec_pid);

  // But TID should change with clone.
  EXPECT_NE(result.pre_clone_tid, result.pre_exec_tid);

  // So we now have PID != TID.
  EXPECT_NE(result.pre_exec_pid, result.pre_exec_tid);

  // exec'ing does not change the PID, even when done from non-leader thread.
  EXPECT_EQ(result.pre_exec_pid, result.post_exec_pid);

  // After exec, the PID is back to matching TID.
  EXPECT_EQ(result.post_exec_pid, result.post_exec_tid);

  // The TID matches the one from before clone.
  EXPECT_EQ(result.post_exec_tid, result.pre_clone_tid);
}

}  // namespace testing
}  // namespace gvisor

int main(int argc, char** argv) {
  gvisor::testing::TestInit(&argc, &argv);

  if (absl::GetFlag(FLAGS_processes_test_exec_swap)) {
    return gvisor::testing::ExecSwapPostExec();
  }
  return gvisor::testing::RunAllTests();
}
