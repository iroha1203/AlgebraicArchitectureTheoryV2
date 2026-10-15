# ArchSig v0.6.0

[v0.6.0 I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md)に従い、独立Atom定義と、
その共通語彙を参照するLaw・ArchMapを検査する。
旧版 `tools/archsig` とは独立したクレートである。

## 現在の範囲

- 独立 Atom 定義の API (`archsig::definition::check_definitions`): JSON schema・namespace・
  依存 DAG・binding・原始型を検査し、meaning・入力位置・語彙 manifest と digest を保持する。
- Law の静的検査: 構文・版・名前・型・依存型・構造再帰・純粋性。
- 型付きの宣言と原式、出現位置、参照の解決、既定規則(`archsig::law::check_law`)。
- Atom定義の語彙 manifest と digest、各定義ファイルとLawの `bytes_digest`・`model_digest`。
- ArchMap の静的検査: 版・schema・ID・由来・語彙 binding・原始値の型と encoding・参照・
  依存型の所属・Map の全域性・欠測 slot の補完の存在。既知値と欠測 slot を持つ内部表現と
  `model_digest`(`archsig::archmap::check_archmap`)。
- 観測環境の準備 API (`archsig::observed::prepare_observed`): 元 byte 列・入力識別・
  digest と検査済み三表を保持し、`evaluate` / `check` の束縛・型・公開射影・
  依存順を解決する。循環は該当する問いの ID と依存グラフを保持して拒否する。
  検査済み bundle を再利用する入口と、検査・要求解決で共有する予算・取消制御を持つ。
  値の評価・回答・導出 node の生成は未実装。
- CLI の `archsig check` と `archsig version`。入力のコピー、`result.json`、stdout の receipt を
  [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md) §§5–7 に従って出す。

提供するコマンドは `check` と `version` だけであり、v0.6.0 全体の適合版ではない。
`run` は CLI の不正(`usage`)として拒否する。

## テスト

```bash
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test TARGET NAME -- --exact --test-threads=1
```

`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md) の
`examples/` と同じ byte 列である。テストは docs を読み込まない。
小さい試験名を個別に指定し、同時には一件だけ実行する。

## 利用手順

```bash
cargo build --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
```

以下の `archsig` は、作られた `tools/archsig_v0.6.0/target/debug/archsig` を指す。

共通定義とLawを検査し、語彙manifest、型付き宣言と元の位置を得る。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --out result-law
```

ArchMapを指定すると、同じ定義へのbindingと原始値・参照・由来・補完の整合性を検査する。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json --out result-both
```

`--out` は存在しない path を指定する。結果は `result-law/result.json` などに書かれ、
stdout には一行の receipt が出る。`archsig version` は版を一行で出す。

定義ファイルを複数指定する場合は `--atom-definition` を指定順に繰り返す。
読込みは明示したファイルだけで完結し、未使用の語彙・依存・importも検査して保持する。
結果は `archsig.result/2`。定義コピーは `inputs/definitions/0.json` 等に保存し、
入力ID `definition0` 等とJSON Pointerで元の定義位置を追える。
