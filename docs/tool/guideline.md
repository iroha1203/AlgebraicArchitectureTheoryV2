# Tooling 編集ガイドライン

この文書は `tools/archsig`、`tools/archview`、`tools/fieldsig`、`docs/tool` を編集するときの作業方針をまとめる。

## 境界

- ArchMap finite-poset-site shape は supplied `archmap/v0.5.1` evidence を読む source-grounded finite poset site map である。primary input は `sources` / `atoms`(subject / axis 必須) / `contexts` / `covers` であり、extraction doctrine は ArchSig 側の固定 `doctrine:aat-canonical@1` として扱う。旧 grouping field は primary field ではない。gap、projection info、concern hints、provenance、non-conclusions を primary schema に戻さない。
- 現行 AAT は Atom 公理系から architecture object を構成し、それを site / sheaf /
  law algebra / obstruction ideal / lawful locus へ持ち上げる代数幾何的アーキテクチャ論である。
  ArchMap / extractor は source code から Atom evidence や AAT measurement input を提示・検査する
  実測 surface であり、AAT の定理や完了条件を定義しない。
- LawPolicy selector は明示した law / evaluator / basis / scope / severity と `lawSurfaceRef` を選ぶ `law-policy/v0.5.1` artifact である。退役した policy pack selector は受理しない。AG evaluator を選ぶ場合は `measurementProfileRef` で `measurement-profile/v0.5.1` を選ぶ。cover、coefficient、resolution、witness variables、exactness assumption、distance rule は supplied law-equation-surface、evaluator registry、または MeasurementProfile の責務である。AAT そのものではない。
- ArchSig v0.5.1 は、ArchMap + LawPolicy + supplied law-equation-surface + MeasurementProfile の入力検証が通った `analyze` run で `archsig-measurement-packet/v0.5.1` を作る AG measurement layer である。Rust と Lean の対応を tooling contract として要求しない。
- ArchView は ArchSig が emitted した measurement / viewer artifact を AAT 代数幾何の幾何として投影する可視化レイヤーである。ArchView は新しい structural verdict を作らず、`archsig-atom-viewer-data.json`、同一ディレクトリの summary / manifest、または `archview-sequence/v0.5.1` の実測フレーム列だけを表示する。
- ArchSig の `analyze` は選ばれた LawPolicy、MeasurementProfile、evidence contract の中で
  structural verdict と analytic reading を出す。`compare` は二つの analyze run を記録レベルで比較し、
  `gate` は gate policy に従って measurement packet と比較記録をCI判断へ写像する。
- ArchSig は、未観測 runtime 全体や global semantic safety のように選ばれた evidence language の外にあるものを、
  failure、残タスク、Lean linkage requirement、長い `non-conclusion` 一覧として扱わない。外側は必要最小限の
  silence boundary として扱う。
- Review notes may exist outside ArchMap, but removed v0 fields such as `concernHints` are not current diagnostic input.
- FieldSig は explicit ArchSig handoff artifacts を bounded current architecture-evidence state として読み、SFT 側の evolution measurement / governance input へ写す。raw ArchMap observations を forecast truth として読まない。
- ArchSig validation は、schema、refs、generated middle layer、selected law-policy reading、fixture expectation など、
  明示された tooling contract を検査する。Lean theorem、実運用上の正しさ、予測精度を要求する場合は、
  それぞれ専用の theorem / fixture / dataset / issue として定義してから扱う。
- PRD や完了レビューでは、PRD 自身の acceptance criteria と実装済み test / fixture を照合する。
  PRD が要求していない巨大な一般 claim を、未完了タスクとして追加しない。
- 文書 lifecycle は [repository documentation guideline](../guideline.md) に従う。Tooling の恒久情報は
  現行仕様、schema docs、source、test、fixture に置く。

## CLI / schema 方針

- ArchSig の現行一次 workflow は `analyze` である。新しい docs、script、CI では `analyze` を使う。
- `llm-native-workflow` / `north-star-workflow`、`archsig-analysis` / `aat-analysis`、`analysis-summary`、`codebase-inspection`、`archmap-generate` は current runtime surface ではない。
- pre-v1 workflow は Git history や historical fixtures に残るだけで、現行 ArchSig surface や compatibility input として扱わない。
- JSON artifact / schema / report の互換性を壊す変更では、`docs/tool`、tool README、fixtures、validation tests を合わせて更新する。
- ArchView surface を変更する場合は、`tools/archview/README.md`、`docs/tool/README.md`、release bundle、必要な visual / workflow tests を合わせて更新する。可視化の豊かさを ArchSig の測定結論へ昇格させない。
- CLI surface を追加・変更する場合は、必要に応じて `tools/archsig/README.md`、`tools/archsig/docs/commands.md`、`tools/fieldsig/README.md`、`tools/fieldsig/docs/commands.md` を更新する。
- Rust 型共有を ArchSig / FieldSig 間の cross-tool contract として扱わない。serialized JSON artifact boundary を重視する。
- Rust source では不用意な `unwrap`, `expect`, `panic!`、placeholder 実装、claim boundary を曖昧にする fallback を避ける。
- Report / schema / CLI wording は「これは結論ではない」を主文にしない。結論、根拠、選ばれた evidence contract を
  先に出し、語らない領域は必要な場合だけ短い boundary として添える。

## テスト責務と実行経路

ArchSig の `cli` integration test target は runtime 契約だけを所有する。`cargo test
--manifest-path tools/archsig/Cargo.toml --test cli` は `analyze` / `gate` / `compare`、
schema catalog、measurement packet、evaluator の入力・出力、CLI error、決定性を検証する。
ArchView HTML、release workflow、docs、SKILL、website の文字列をこのtargetから直接検査しない。
全体の `cargo test --manifest-path tools/archsig/Cargo.toml` は、下表の専用targetも合わせて実行する。

| 対象 | source of truth | 実行経路 |
| --- | --- | --- |
| ArchSig runtime | `tools/archsig/src/` と `tools/archsig/tests/cli.rs` | `cargo test --manifest-path tools/archsig/Cargo.toml --test cli` |
| ArchMap authoring | `tools/archsig/src/authoring.rs`、`archmap` CLI、`archmap-creater` | `cargo test --manifest-path tools/archsig/Cargo.toml --lib authoring::tests` と `cargo test --manifest-path tools/archsig/Cargo.toml --test authoring` |
| ArchView artifact | `tools/archview/` と emitted viewer artifact | `cargo test --manifest-path tools/archsig/Cargo.toml --test archview_e2e`。HTML文字列検査は行わず、analyze生成物を検証する |
| ArchView UI / sequence | `tools/archview/archview.html` | `analyze`を`.tmp/archview-preview`へ出力し、`cp tools/archview/archview.html .tmp/archview-preview/`後に`python3 -m http.server 8000 --directory .tmp/archview-preview`を起動して、同一ディレクトリのviewer dataとsequenceを確認 |
| release | `.github/workflows/archsig-release.yml` | `gh workflow run archsig-release.yml -f tag=<tag>` |
| docs / skill / website | 各source fileとreview workflow | docs / skill は `git diff --check -- docs/tool tools/archsig/skills`、website は `cd website && npx @11ty/eleventy`。ArchSig runtime testには含めない |

fixtureやdocsの存在だけを確認するテストは、analyzerのgolden regressionとは呼ばない。goldenを追加する場合は、CLIを実行して packet、verdict、invariant、witness、digestなどの生成結果を期待値と比較する。

## 主要コマンド

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
```

ArchSig analyze:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v051.json \
  --out-dir .tmp/archsig-analyze
```

FieldSig handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --measurement-packet .tmp/archsig-analyze/archsig-measurement-packet.json \
  --out .tmp/fieldsig/operation-support-estimate.json
```

PR 前には次も確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
```
