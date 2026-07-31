# ArchMap Commands

リポジトリ checkout から実行する場合は、各コマンドの前に
`cargo run --manifest-path tools/archmap/Cargo.toml --` を付ける。

## ArchMap

ArchMap の観測 artifact を検証する。scope manifest、candidate packet、
extraction consistency、coverage ledger を併せて指定すると、authoring の
survey traceability と provenance closure も検査する。

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- archmap \
  --input tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --out .tmp/archmap-validation.json
```

authoring artifact を併せた検証:

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- archmap \
  --input archmap.json \
  --scope-manifest <run-dir>/scope-manifest.json \
  --candidate-packets '<run-dir>/candidates/*.json' \
  --extraction-consistency <run-dir>/extraction-consistency.json \
  --coverage-ledger <run-dir>/coverage-ledger.json \
  --out <run-dir>/archmap-validation.json
```

## Scope manifest

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- scope-manifest \
  --repo-root . \
  --include "src/**/*.rs" \
  --exclude "**/target/**" \
  --out .tmp/scope-manifest.json
```

`--baseline` を指定すると、既存 manifest から新規または内容が変わった
worklist row だけを出力する。

## Extraction diff

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- extraction-diff \
  --pass-a <run-dir>/pass-a/candidate-packet.json \
  --pass-b <run-dir>/pass-b/candidate-packet.json \
  --out <run-dir>/extraction-consistency.json
```

二つの survey pass を authoring atom-match-key で比較する。未一致候補は
integrator の再読と adjudication の対象として記録される。

## Supply bench

```bash
cargo run --manifest-path tools/archmap/Cargo.toml -- supply-bench \
  --pair baseline=<run-dir>/baseline/extraction-consistency.json \
  --pair candidate=<run-dir>/candidate/extraction-consistency.json \
  --out <run-dir>/supply-bench.json
```

供給ベンチの指標定義と fixture 規約は
[`docs/tool/archmap_supply_bench.md`](../../../docs/tool/archmap_supply_bench.md) を
正本とする。
