# ローカル候補バンドルの作成

`bundle-candidate.sh` は固定 commit の ArchSig 0.6.0 と利用仕様を `git archive` で取り出し、
そのソースを Cargo でビルドし、CLI・SKILL/assets・仕様・出所記録を包装します。
作成用の環境は POSIX shell、Git、Rust 2024 対応 toolchain、Cargo、
`tar`（`--uid/--gid/--no-recursion` 対応）、gzip、shasum と標準 Unix コマンドを使います。
現在の入口はビルドホスト用の Unix 実行ファイルを作ります。
CLI 利用者は Rust や包装用 runtime を準備する必要がありません。

リポジトリで以下を実行します。`source_commit` は script と `BUNDLE.md` を含む
40桁の commit hash、出力先は未存在のディレクトリを指定します。

```sh
source_commit=$(git rev-parse HEAD)
sh tools/archsig_v0.6.0/scripts/bundle-candidate.sh "$source_commit" /tmp/archsig-candidate
```

未コミットの変更は入力に入りません。ビルド入力は保存された `source.tar` の内容だけです。
既存の実行ファイルを包装するオプションはありません。
`CARGO_TARGET_DIR` に既存 cache を指定できます。Cargo は archive から展開したソースを使って
必要な再コンパイルを行います。profile は dev、target は `rustc -vV` の host、依存は `--locked`。
外部依存の初回取得にはネットワーク接続が必要です。ビルドに失敗した出力先は再使用せず、
新しい出力先を指定します。外から指定された `RUSTFLAGS` は source path remap で置換します。

出力には次を含みます。

- `archsig-0.6.0-TARGET-candidate.tar.gz`: 利用者向け候補
- `source.tar`: commit から取得した製品ソース・仕様・包装 script
- `SHA256SUMS`: 上記二つの SHA-256
- 展開済みのバンドルと `source/`: 内容確認と再ビルド用

バンドル内の `PROVENANCE.txt` に source commit/tree、source archive/binary の SHA-256、
ツールチェーンとビルド引数を記録します。archive 自身の digest は循環を避けて外側の
`SHA256SUMS` に記録します。I/O 仕様のリポジトリ相対リンクは同梱 README・SKILL に移し、
開発資料への末尾の関連リンクを省きます。I/O 仕様本文と examples、SKILL/assets は同梱します。

再現時は記録した commit を取得し、同じ toolchain と target で上記 script を実行します。
Git を使わず入力を確認する場合は `source.tar` を空ディレクトリに展開し、
`PROVENANCE.txt` の引数で Cargo を実行できます。Cargo.lock と source archive digest で入力を照合します。
同じ payload の tar は順序・所有者・mtime・gzip timestamp を固定します。
Rust toolchain・依存のビルド環境が異なる場合の binary bytes 一致は実測で確認してください。
source と binary の対応根拠は版文字列に加え、保存した archive からのビルドと digest の記録です。

候補は別の空ディレクトリへ展開し、バンドルの README の `version`・`check`・`run` を実行します。
仕様・SKILL の相対リンクも展開物だけで辿れます。公開の判断は候補作成とは別に行います。
