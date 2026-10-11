# ArchSig v0.6.0

[v0.6.0 I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md)に従い、Law と ArchMap の二入力を検査する。
旧版 `tools/archsig` とは独立したクレートである。

## 現在の範囲

- Law の静的検査: 構文・版・名前・型・依存型・構造再帰・純粋性。
- 型付きの宣言と原式、出現位置、参照の解決、既定規則(`archsig::law::check_law`)。
- 語彙 manifest と digest、Law の `bytes_digest`・`model_digest`。

## テスト

```bash
cargo test --manifest-path tools/archsig_v0.6.0/Cargo.toml
```

`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md) の
`examples/` と同じ byte 列である。テストは docs を読み込まない。
