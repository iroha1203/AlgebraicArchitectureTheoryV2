# ArchSig 0.6.0

Law と ArchMap の二入力を検査するための独立した Rust クレートです。
第1段階の Law ライブラリを、後続の ArchMap 検査と `check/version` CLI へ接続します。

現在のライブラリは `law::check(&bytes)` で Law 全体の構文・名前・型・再帰を検査し、
型付き宣言・原式・元の byte span と manifest/digest をメモリ上に保持します。
`Program.declarations` と `Program.vocabularies` は結果表示用の表です。
後続処理は `Program.readings` の型付き宣言を直接使います。

```sh
cargo test --manifest-path tools/archsig_v0.6.0/Cargo.toml
```

テストは同梱の規範例と仕様に基づく新しい入力を検査します。
