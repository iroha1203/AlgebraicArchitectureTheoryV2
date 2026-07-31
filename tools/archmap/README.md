# ArchMap

`archmap` は、ArchMap の観測・authoring・供給パイプラインを担当する CLI と
ライブラリである。scope manifest、candidate packet、extraction consistency、
coverage ledger を作成・検証し、ArchMap の入力検証と supply bench を実行する。

ArchSig の計算 crate は `tools/archsig` にあり、ArchMap と LawPolicy などの
入力から分析 artifact を計算する。CLI の責務と依存方向の裁定は
[`DESIGN.md`](DESIGN.md) に記録している。

## コマンド

詳細なフラグと入力例は [コマンドガイド](docs/commands.md) を参照する。

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --out .tmp/archmap-validation.json

cargo run --manifest-path tools/archmap/Cargo.toml -- scope-manifest \
  --repo-root . \
  --include "src/**/*.rs" \
  --out .tmp/scope-manifest.json
```

## 検証

```bash
cargo test --manifest-path tools/archmap/Cargo.toml
```
