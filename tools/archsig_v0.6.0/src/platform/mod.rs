//! OS 固有操作（シグナル制御・原子的リネーム・ファイル記述子出力・非 UTF-8 パス分解）の境界層。

#[cfg(not(unix))]
mod fallback;
#[cfg(unix)]
mod unix;

#[cfg(not(unix))]
use fallback as imp;
#[cfg(unix)]
use unix as imp;

use archsig_common::control::Control;
use archsig_input::result::Signal;
use std::ffi::OsStr;
use std::fmt;
use std::path::{Path, PathBuf};

/// プラットフォーム層で発生した構造化エラー。
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlatformError {
    pub operation: &'static str,
    pub message: String,
}

impl fmt::Display for PlatformError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.operation, self.message)
    }
}

impl std::error::Error for PlatformError {}

/// プロセス単位のシグナル捕捉・ブロック・配送制御。
pub struct ProcessSignals(imp::ProcessSignals);

impl ProcessSignals {
    /// SIGINT / SIGTERM ハンドラを登録する。失敗時はパニックせず `PlatformError` を返す。
    pub fn install() -> Result<Self, PlatformError> {
        imp::ProcessSignals::install().map(Self)
    }

    /// 計算中の協調中断チェック用 `Control` を生成する。
    pub fn control(&self) -> Control {
        self.0.control()
    }

    /// 既に捕捉済みのシグナルがあれば対応する終了コード（`128 + signum` 等）を返す。
    pub fn prior_signal_exit_code(&self) -> Option<i32> {
        self.0.prior_signal_exit_code()
    }

    /// 出力配送フェーズ開始を宣言し、シグナル配送用の即時終了設定とマスク解除を行う。
    pub fn begin_delivery(exit_code: u8) -> Result<(), PlatformError> {
        imp::begin_delivery(exit_code)
    }

    /// 読取専用ヘルパー向け: ファイル公開を伴わないため即座に配送フェーズへ移る。
    pub fn enter_immediate_delivery() {
        imp::enter_immediate_delivery();
    }
}

impl crate::run::Signals for ProcessSignals {
    fn freeze(&mut self) -> Option<Signal> {
        self.0.freeze()
    }
}

/// stdout へ 1 行を出力する（Unix では閉じた fd に対する EBADF を維持）。
pub fn write_stdout_line(line: &str) -> std::io::Result<()> {
    imp::write_stdout_line(line)
}

/// stderr へ 1 行を出力する。
pub fn write_stderr_line(line: &str) -> std::io::Result<()> {
    imp::write_stderr_line(line)
}

/// 既存の出力先を置き換えずにディレクトリをリネームする。
pub fn rename_noreplace(from: &Path, to: &Path) -> std::io::Result<()> {
    imp::rename_noreplace(from, to)
}

/// `--reuse` 対象ディレクトリの `result.json` を symlink を辿らずサイズ上限付きで読み込む。
pub fn read_reuse_result_nofollow(dir: &Path, max_bytes: u64) -> std::io::Result<Vec<u8>> {
    imp::read_reuse_result_nofollow(dir, max_bytes)
}

/// `ID=PATH` 形式の `--source` 引数を分解する（Unix では非 UTF-8 ファイルパスも保持）。
pub fn split_source_binding(value: &OsStr) -> Result<(String, PathBuf), &'static str> {
    imp::split_source_binding(value)
}

#[doc(hidden)]
#[cfg(unix)]
pub fn send_signal(pid: u32, signal: Signal) -> Result<(), PlatformError> {
    imp::send_signal(pid, signal)
}
