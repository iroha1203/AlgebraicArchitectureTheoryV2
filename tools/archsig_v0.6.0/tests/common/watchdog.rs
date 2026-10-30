//! テストで起動した単一のCLI子プロセスを、製品予算と独立に監視する。
//! ArchSigは子プロセスを起動しない。stdout/stderrは同時に読み、pipeの満杯を防ぐ。

use std::io::{self, Read};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

pub struct Captured {
    pub output: Output,
    pub timed_out: bool,
}

struct Running(Child);
impl Drop for Running {
    fn drop(&mut self) {
        // try_waitや出力取得が失敗した場合にも、自分が起動したchildだけを回収する。
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

fn read(mut pipe: impl Read) -> io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    pipe.read_to_end(&mut bytes)?;
    Ok(bytes)
}

pub fn output(command: &mut Command, deadline: Duration) -> io::Result<Captured> {
    let started = Instant::now();
    let mut child = Running(
        command
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()?,
    );
    let stdout = child.0.stdout.take().expect("stdout pipe");
    let stderr = child.0.stderr.take().expect("stderr pipe");
    std::thread::scope(|scope| {
        // scopeがreaderをjoinする前に、エラー時のchild回収を済ませる。
        let mut child = child;
        let stdout = scope.spawn(|| read(stdout));
        let stderr = scope.spawn(|| read(stderr));
        let (status, timed_out) = wait(&mut child.0, deadline.saturating_sub(started.elapsed()))?;
        Ok(Captured {
            output: Output {
                status,
                stdout: stdout
                    .join()
                    .map_err(|_| io::Error::other("stdout reader panicked"))??,
                stderr: stderr
                    .join()
                    .map_err(|_| io::Error::other("stderr reader panicked"))??,
            },
            timed_out,
        })
    })
}

/// 手動で同期・signalを操作する試験にも、同じkill/wait上限を使う。
pub fn wait(child: &mut Child, deadline: Duration) -> io::Result<(ExitStatus, bool)> {
    let started = Instant::now();
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok((status, false));
        }
        if started.elapsed() >= deadline {
            let killed = child.kill();
            let status = child.wait()?;
            killed?;
            return Ok((status, true));
        }
        std::thread::sleep(
            Duration::from_millis(10).min(deadline.saturating_sub(started.elapsed())),
        );
    }
}
