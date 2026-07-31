# Tooling 編集ガイドライン

この文書は `tools/archsig`、`tools/archview`、`tools/fieldsig`、`docs/tool` を編集するときの作業方針をまとめる。

## 責務範囲(入力トライアドの正本)

- AAT は Atom と law から立つ純粋理論である。ArchSig は ArchMap と LawPolicy から
  bounded diagnostic を計算する。観測の正しさは ArchMap author の責務として扱う。
- 入力トライアド(hard rule): ArchMap は観測した atom を書く場、
  LawPolicy(law-equation-surface / MeasurementProfile を含む法・方程式側 artifact)は
  ルールと制約を書く場であり、ArchSig はこの二系統の入力から計算して結果を出力する。
  第三の入力カテゴリは存在しない(供給 contract を第三の入力として読み替える誤読を
  塞ぐための明示である)。
- 帰属は名前ではなく内容で決める。法・方程式側に帰属するのは、特定の ArchMap instance に
  依存しない規則・制約・係数・被覆・評価計画だけである。特定 instance の値(section、
  cocycle、class の零性、写像の存在)を運ぶ供給は、名称にかかわらず法側ではない。
  観測側に帰属する行は source への解決可能な ref を持つ。RepairPlan のうち作者が提案する
  修理そのもの(修理後状態と repair cochain の対象)は、この観測側の資格を満たす形で
  書かれた場合に限り提案された観測として観測側に帰属する。ArchSig が計算すべき結論を
  先渡しする slot はどちらにも帰属しない。
- どちらにも帰属しない authored データ(証明、証書、presentation、結論相当の
  supplied 判定)を、新しい入力、CLI flag、schema field、供給 slot として受け取らない。
  既存 field への同種データの追加・意味拡張・解禁語彙の追加も同じ禁止に含む。
  台帳への収載、validator の存在、結論の相対化表記、assumption ledger 記録、
  未供給時に沈黙する設計、fixture / golden lock、schema 登録や version bump は、
  いずれも帰属の代替にならない(列挙は例示であり、帰属それ自体を示さない装置は
  すべて同様)。二系統から計算できない語彙は、供給で解禁せず沈黙として扱う。
- 二系統に帰属しない導入済みの入力面は、台帳収載の有無にかかわらずこの規律に対する
  既存の負債である。返済は供給 slot 台帳(入口は docs/tool/README.md)で管理し、
  負債の存在も返済作業も新規追加の先例として引用しない。
- ウィトゲンシュタイン的責務範囲を守る。ArchSig は与えられた入力 contract から、
  選ばれた vocabulary と policy の中で語れることだけを語る。入力 contract を補完・推測・
  拡張しない。語れない領域は、失敗や残タスクではなく沈黙として扱い、必要な場合だけ
  結論の近くに最小限の boundary として書く。
- Tooling の identity は肯定形で書く。ArchSig の定義は
  「観測(ArchMap)と法・方程式(LawPolicy / law-equation-surface / MeasurementProfile)の
  二系統から bounded verdict を計算する計測層」という
  肯定形であり、結論の相対性はこの入力契約に由来する帰結として述べる。
  「theorem prover ではない」「global truth ではない」のような否定形免責を
  identity 文へ習慣的に併記しない。否定を書くのは、読者の実在する誤推論を塞ぐ場合だけ、
  結論の近くで一度に限る。

## 境界

- ArchMap finite-poset-site shape は supplied `archmap/v0.5.4` evidence を読む source-grounded finite poset site map である。primary input は `sources` / `atoms`(subject / axis 必須) / `contexts` / `covers` であり、extraction doctrine は ArchSig 側の固定 `doctrine:aat-canonical@1` として扱う。旧 grouping field は primary field ではない。gap、projection info、concern hints、provenance、non-conclusions を primary schema に戻さない。
- 現行 AAT は Atom 公理系から architecture object を構成し、それを site / sheaf /
  law algebra / obstruction ideal / lawful locus へ持ち上げる代数幾何的アーキテクチャ論である。
  ArchMap / extractor は source code から Atom evidence や AAT measurement input を提示・検査する
  実測 surface であり、AAT の定理や完了条件を定義しない。
- LawPolicy selector は明示した law / lawPair / evaluator / basis / scope / severity と `lawSurfaceRef` を選ぶ `law-policy/v0.5.4` artifact である。退役した policy pack selector は受理しない。AG evaluator を選ぶ場合は `measurementProfileRef` で `measurement-profile/v0.5.4` を選ぶ。cover、coefficient、resolution、witness variables、exactness assumption、distance rule は supplied law-equation-surface、evaluator registry、または MeasurementProfile の責務である。AAT そのものではない。
- ArchSig v0.5.4 は、ArchMap + LawPolicy + supplied law-equation-surface + MeasurementProfile の入力検証が通った `analyze` run で `archsig-measurement-packet/v0.5.4` を作る AG measurement layer である。Rust と Lean の対応を tooling contract として要求しない。
  再現可能な run では `policy-bundle` が三つの選択済み policy component と canonical fingerprint を固定し、個別 flag は同じ入力を直接渡す形である。
- ArchView は supplied ArchMap の Atom / Context / Cover を直接読む Atom-native な可視化レイヤーである。ArchMap 単独で architecture understanding を成立させ、その同じ geometry 上へ既存 ArchSig run artifact の measurement、finding、comparison、gate、明示された repair target を optional overlay として重ねる。ArchView は新しい structural verdict、source relation、repair recommendation を作らず、すべての描画と source landing を supplied artifact へ追跡可能にする。再構築前の `tools/archview/archview.html` が `archsig-atom-viewer-data.json` / `archview-sequence/v0.5.4` を読むことは現行実装上の制約であり、ArchView の恒久的な product identity ではない。
- ArchSig への入力は観測(ArchMap)と法・方程式(LawPolicy / law-equation-surface / MeasurementProfile)の
  二系統に限る(正本は本 guideline の「責務範囲(入力トライアドの正本)」)。この二系統に帰属しない
  authored 証明・証書・presentation を、新しい CLI 入力や schema slot として追加しない。
  既存の RepairPlan 系入力はこの規律に従って扱い、退役した refactor morphism / refinement data の
  供給 slot は現行入力面に置かない。返済の記録は供給 slot 台帳の負債告知に残す。
- ArchSig の `analyze` は、観測(ArchMap)と選ばれた LawPolicy / law-equation-surface / MeasurementProfile の中で
  structural verdict と analytic reading を出す。`compare` は二つの analyze run を記録レベルで比較し、
  `gate` は gate policy に従って measurement packet と比較記録をCI判断へ写像する。
  gate policy は計算済み packet と比較記録を CI 判断へ写す規則だけを書き、新しい measurement
  結論や供給された判定を gate policy / comparison の入力へ置かない。
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
- Tooling の恒久情報は
  現行仕様、schema docs、source、test、fixture に置く。

## CLI / schema 方針

- ArchSig の現行一次 workflow は `analyze` である。新しい docs、script、CI では `analyze` を使う。
- `llm-native-workflow` / `north-star-workflow`、`archsig-analysis` / `aat-analysis`、`analysis-summary`、`codebase-inspection`、`archmap-generate` は current runtime surface ではない。
- pre-v1 workflow は Git history や historical fixtures に残るだけで、現行 ArchSig surface や compatibility input として扱わない。
- JSON artifact / schema / report の互換性を壊す変更では、`docs/tool`、tool README、fixtures、validation tests を合わせて更新する。
- ArchView surface を変更する場合は、`tools/archview/README.md`、`docs/tool/README.md`、release bundle、必要な visual / workflow tests を合わせて更新する。可視化の豊かさを ArchSig の測定結論へ昇格させない。
- CLI surface を追加・変更する場合は、責務に応じて `tools/archsig/README.md`、`tools/archsig/docs/commands.md`、`tools/archmap/README.md`、`tools/archmap/docs/commands.md`、`tools/fieldsig/README.md`、`tools/fieldsig/docs/commands.md` を更新する。
- Rust 型共有を ArchSig / FieldSig 間の cross-tool contract として扱わない。serialized JSON artifact boundary を重視する。
- Rust source では不用意な `unwrap`, `expect`, `panic!`、placeholder 実装、claim boundary を曖昧にする fallback を避ける。
- Report / schema / CLI wording は「これは結論ではない」を主文にしない。結論、根拠、選ばれた入力 contract を
  先に出し、語らない領域は必要な場合だけ短い boundary として添える。

## テスト責務と実行経路

### ArchSig test ownership（hard rule）

ArchSig の Rust test は ArchSig だけを検査する。対象は ArchSig runtime、CLI、schema、validator、
evaluator、ArchSig が生成する serialized artifact の値・参照・決定性に限定する。

`tools/archsig` の unit / integration / golden test とfixtureから、次を検査することを禁止する。

- ArchView の HTML、DOM、UI、scene、内部関数、browser behavior、表示文言
- `tools/archview/` のファイル存在、内容、bundle配置
- website の source、文言、route、link、asset、layout、build結果

ArchSig artifactがArchViewに消費される場合も、ArchSig testが検査するのはserialized artifactの
ArchSig側contractまでとする。consumer実装との結合testへ拡張しない。ArchViewは`tools/archview/`が
所有するbrowser / UI test、websiteはwebsiteのbuild / browser testで検査する。

ArchSig の `cli` integration test target は runtime 契約だけを所有する。`cargo test
--manifest-path tools/archsig/Cargo.toml --test cli` は `analyze` / `gate` / `compare`、
schema catalog、measurement packet、evaluator の入力・出力、CLI error、決定性を検証する。
ArchView、release workflow、docs、SKILL、websiteをこのtargetから検査しない。
ArchSig と ArchMap の全体 test は、それぞれの crate で実行する。ArchSig の
`cli` target と ArchMap の authoring / supply target は責務を混ぜない。

| 対象 | source of truth | 実行経路 |
| --- | --- | --- |
| ArchSig runtime | `tools/archsig/src/` と `tools/archsig/tests/cli.rs` | `cargo test --manifest-path tools/archsig/Cargo.toml --test cli` |
| ArchMap authoring / supply | `tools/archmap/src/`、`tools/archmap/tests/`、`archmap-creater` | `cargo test --manifest-path tools/archmap/Cargo.toml` |
| ArchView | `tools/archview/` | ArchView自身が所有するbrowser / UI testで検証する。ArchMap単独読込、optional overlay、source landing、unsupported geometryの非描画、empty / malformed入力を同じsurfaceで確認する。ArchSigのRust testからArchViewのUI、scene、内部関数を検査しない |
| release | `.github/workflows/archsig-release.yml` | `gh workflow run archsig-release.yml -f tag=<tag>` |
| docs / skill / website | 各source fileとreview workflow | docs / skill は `git diff --check -- docs/tool tools/archsig/skills`、website は `cd website && npx @11ty/eleventy`。ArchSig runtime testには含めない |

fixtureやdocsの存在だけを確認するテストは、analyzerのgolden regressionとは呼ばない。goldenを追加する場合は、CLIを実行して packet、verdict、invariant、witness、digestなどの生成結果を期待値と比較する。

## 主要コマンド

```bash
cargo test --manifest-path tools/archsig/Cargo.toml
cargo test --manifest-path tools/archmap/Cargo.toml
cargo test --manifest-path tools/fieldsig/Cargo.toml
```

ArchSig analyze:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap tools/archsig/tests/fixtures/ag_measurement/archmap_v2.json \
  --law-policy tools/archsig/tests/fixtures/ag_measurement/law_policy_ag.json \
  --measurement-profile tools/archsig/tests/fixtures/ag_measurement/measurement_profile_ag.json \
  --law-surface tools/archsig/tests/fixtures/ag_measurement/law_surface_ag_v052.json \
  --out-dir .tmp/archsig-analyze
```

FieldSig handoff:

```bash
cargo run --manifest-path tools/fieldsig/Cargo.toml -- archsig-analysis-sft-input \
  --measurement-packet .tmp/archsig-analyze/archsig-measurement-packet.json \
  --out .tmp/fieldsig/operation-support-estimate.json
```

PR 前の共通 scan は [workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。
