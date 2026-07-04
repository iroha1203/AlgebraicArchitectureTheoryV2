# ArchSig v0.5.0 PRD-3 — v1 path の破棄と全面同期(単一 path 宣言の成立)

対象は v1 legacy path(typed evaluator / architecture distance / pr-review)の全削除と、
リポジトリの全語り(skills / docs / CI / fixture / Lean guardrail)の現行化(ロードマップ P5〜P6)。
v0.5.0 PRD 5 本の第 3 弾。**前提: PRD-1(契約基盤)と PRD-2(gate / compare = pr-review の受け皿)の
実装が受け入れ済みであること。**

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md) — §2(レガシー破棄)、
  §8 裁定1(pr-review 後継 = compare + gate)・裁定8(SKILL 受け皿)・裁定10(互換ゼロ)、
  §11(archive・Lean guardrail のユーザー決定)
- [design_legacy-triage](../note/archsig_v0_5_0/design_legacy-triage.md) — Phase C の削除リスト・
  リスク表・docs 処遇表が正
- [PRD-1](archsig_v0_5_0_prd1_legacy_purge_and_foundation.md)(v0 破棄と契約基盤)/
  [PRD-2](archsig_v0_5_0_prd2_artifact_ci.md)(gate / compare)

## 問い

**「このリポジトリの計測経路は `archmap + 選択された制度 → measurement packet` だけである」という宣言を、
機械検査(残存ゼロ検査)として成立させられるか。**

この問いを採否の判定規律として使う。

- **(採用条件)** 宣言の**反例をゼロにする**作業だけを採用する。反例とは:
  (a) 第二の計測経路(v1 typed evaluator chain、pr-review、`--strict-distance` / `--emit-raw-artifacts`)、
  (b) v1 を現行と語る語り(skills の v1 前提、docs の「The current route is: archmap/v1」、CI の v1 e2e 区間)、
  (c) AG path 自身に残る判定語の残滓(registry の判定語 predicate 3 件、判定語 atom を消費する最後のコード
  `witness-counting@1`)— 観測純化 PRD の仕上げ、
  (d) 守る対象を失う Lean guardrail 3 本(v1 reading families の claim boundary 用)。
- **(検査可能性)** 宣言は誓約ではなく検査である。受け入れ条件は「決められた語彙リストの rg 残存ゼロ
  (archive と Git history、および明示された既知の残置を除く)」に落ちなければならない。
- **(却下条件)** 宣言の検査可能性に寄与しない変更は却下する。とくに: LawPolicy / profile の新形状
  (PRD-4)、SAGA 系 evaluator(PRD-4)、SKILL の新機能(PRD-5)、viewer への投影追加(0.5.x)。
  互換機構の追加(受理窓・専用 removal error・バックフィル)はいかなる形でも却下する(裁定10)。

## Core Thesis

PRD-1 で v0 と孤児(≈40k 行)が消え、PRD-2 で pr-review の後継(compare + gate)が立った。
残る反例は v1 path(≈11k 行)と、それを現行と語る三世代ドリフト、そして AG path 内部の判定語残滓である。
本 PRD がそれらをゼロにした時点で、単一 path 宣言は「方針」から「rg で検査できる事実」に変わる。

削除の境界的意義は正確な系譜で書く(claim 規律):
v1 authored `archmap-delta-v0` の削除は**計算責務の観測者転嫁の除去**(受け皿は PRD-2 の計算層 archmap-diff)。
判定語残滓の掃除は**観測純化 PRD の仕上げ**(v0/v1 の削除にこの claim を負わせない)。

## 現状診断(証拠)

記載の行番号は設計時点の実測(design_legacy-triage)。実装時に再確認する。

1. **v1 path 本体**: `src/typed_evaluator.rs`(8,528 行)、main.rs の pr-review コマンド定義(:82-107)+
   実装(:565-710)+ helper(:173-518)、analyze の v1 分岐(:915-1040)、`--emit-raw-artifacts`。
   v1 の実用記述力は predicate 5 語ハードコード(archmap.rs:869-874)+ basis 2 種で事実上ない。
2. **三世代ドリフト**: `tools/archsig/docs/commands.md:3-6` が「The current route is: archmap/v1」と記載。
   archsig-reader / archsig-pr-reviewer SKILL は v1 前提のまま(creater → reader → pr-review ループが
   v2 で閉じていない)。lean.yml:49-201 は v1 e2e 区間。
3. **AG path 内の判定語残滓**: registry の ag.* manifest に判定語 predicate 3 件
   (`coherence.tripleMismatch` @ registry.rs:284 / `boundary-residue.mismatchSection` @ :318 /
   `section-factorization.obstructionGenerator` @ :388)。`witness-counting@1` invariant は
   判定語 atom を消費する最後の生きたコード(helper :10454-10461、emission :6252-6262、
   tests/cli.rs:1143 が `violationCount: 0` を lock)で、R3 hard-error により有効入力では
   恒常 measured_zero の vacuous verdict。
4. **Lean guardrail 3 本**: `Formal/Arch/Signature/{MonodromyMeasurement,CurvatureTransferSpectrum,
   HomotopyHolonomyStokes}.lean`(計 700 行)は v1 reading families の claim boundary 用。
   v1 削除後は守る対象が消滅する(削除はユーザー決定 2026-07-05。Formal.lean の import は
   :34 / :38 / :39 の 3 行)。
5. **二重依存**: lean.yml:164-195 の v1 handoff 区間は「archsig の v1 raw artifacts」と
   「fieldsig の `--analysis-packet` 受理」の両方に依存する。片方だけ先に消すと CI が恒常 fail する。

## Design Principles

1. **受け皿が先、削除が後**: pr-review の機能は PRD-2 の compare + gate が先に受けている。
   本 PRD は削除だけを行い、機能を足さない。
2. **互換ゼロ(裁定10)**: 受理・変換レイヤ・専用 removal error を作らない。旧 schema / 旧コマンドは
   一般エラーに落ちる。告知は README の移行表 1 枚のみ(削除物の長大な列挙を主役化しない)。
3. **同一 PR 制約**: lean.yml v1 区間の削除と FieldSig v1 `--analysis-packet` 受理の削除は同一 PR
   (現状診断 5 の二重依存)。
4. **Rust / Lean の独立**: Lean guardrail の削除は独立 PR とし、Rust 側の削除完了条件に含めない。
5. **既知の残置の明示**: viewer data の v1 語彙 emit(`moleculeGroups` / `atomEdges`)は
   0.5.x の ArchView マイルストーン(V-B2 改名 PR)で停止する。本 PRD の残存ゼロ検査は
   この 2 識別子の viewer data emitter 内出現のみを明示的に除外する(黙って除外しない)。

## 改修(本体)

### P5 群 — v1 path の削除

- **R1(共用型の先行リネーム)** `ArchMapSourceV1` は v2 が共用するため、削除に先行して
  Rust 内部名を `ArchMapSource` にリネームし、型参照をコンパイラに追わせる(schema 文字列に影響なし)。
- **R2(v1 コード削除)** 完全リストは design_legacy-triage §3.2 Phase C が正:
  `src/typed_evaluator.rs` 全体、main.rs の pr-review(定義 / 実装 / helper)と analyze v1 分岐と
  `--emit-raw-artifacts`、`--strict-distance` フラグ全廃(gate が受け皿。`--strict` への改名はしない)、
  `src/cli/analyze.rs` の v1 manifest 構築、normalizer.rs の v1 部
  (`normalize_archmap_v1` / `molecule_memberships` / `ArchMapAtomConstructorV1`)、
  archmap.rs:581-937 の v1 検証(predicate 5 語)、schema/archmap.rs の V1 型群、
  schema/law_policy.rs:172-231(TypedEvaluatorResults / ReplacementRegistry 型)、
  law-policy schema の `distanceProfileRef` フィールド削除(形状の新設は PRD-4)。
- **R3(registry 分離)** solid 5 種 + `domain.no-direct-infra-dependency@1` の manifest、
  replacement_manifests、distance profile 2 種を削除。`ag.*` evaluator manifest(語彙検証用)は
  `law_policy/registry/ag.rs` へ分離して存置。`is_known_v1_evaluator` → `is_known_evaluator`。
  分離を先・削除を後の 2 段コミットとする(AG 語彙検証を壊さない)。
- **R4(fixture / tests)** `archmap_v1/`・`pr_review/`(archmap-delta-v0 込み)・`sharded/` を
  ディレクトリごと削除。tests/cli.rs の v1 系(≈40 箇所)+ strict-distance テスト群を削除。
  残る AG 系テストを機に tests/cli.rs(17.3 千行)を `cli_analyze.rs` / `cli_validation.rs` 等に
  分割することを推奨(必須ではない)。`examples/practical-rust-service/` は v2 化済みのため存置。
- **R5(CI + FieldSig、同一 PR)** lean.yml の v1 e2e 区間(:49-201)を削除し、
  FieldSig の v1 `--analysis-packet` 受理と `tools/fieldsig/docs/commands.md` の該当記述を
  同一 PR で削除する。v2 系 e2e(PRD-2 で置換済みの analyze → gate → handoff → catalog)を唯一の e2e とする。
- **R6(告知)** `tools/archsig/README.md` の v0.5.0 節に移行表 1 枚
  (削除された surface → 現行の対応物: pr-review → compare + gate、`--strict-distance` → gate-policy、
  raw packet handoff → measurement packet、archmap-delta-v0 → compare の計算 archmap-diff、等)。
  専用 removal error は作らない。

### P6 群 — 残滓掃除と全面同期

- **R7(判定語残滓の掃除 — 観測純化の仕上げ)** registry の ag.* manifest の判定語 predicate 3 件を
  実装の実入力語彙(`sectionValue` / `support` / `cooccurrence`)に同期。
  `witness-counting@1` invariant を**代替なしで丸ごと廃止**する(helper・呼び出し・emission ブロック・
  tests/cli.rs:1143 lock・関連 fixture / golden の更新を含む。有効入力で恒常 vacuous な verdict を
  生かす理由がない)。
- **R8(skills 4 本の同期)** 書式は既存慣行(トリガー列挙 / release-bundle 自立性 / binary 解決順序 /
  停止条件明文列挙 / Recommended・Avoid 対句)を踏襲。旧フォーマットのバックフィルはどの SKILL にも
  持たせない(裁定10):
  (a) archsig-reader — v2 native へ全面改稿(読解順: summary → gate-report → packet 参照。
  references/default_law_policy.json を ag.* baseline に差し替え)、
  (b) archsig-pr-reviewer — compare + gate の報告を人間語へ翻訳する後継へ全面書き換え
  (references/source-diff-to-delta.md は廃止)、
  (c) archmap-creater — v1 フォールバック条項の削除(再設計本体は PRD-5)、
  (d) law-policy-creater — distanceProfileRef / solid pack 記述の削除(新形対応は PRD-4)。
- **R9(docs 改稿)** `tools/archsig/docs/commands.md` / `artifacts-and-boundaries.md` を
  v2 単一 path 前提で改稿(:3-6 の v1 現行記述を含む legacy 節の削除)。docs/tool の README /
  golden_corpus / llm_native_e2e_workflow / atom_handoff / law_policy.md を改稿
  (観測純化 PRD「提案中」→ 実装完了、FieldSig 段落の実装より古い記述の是正を含む)。
  `archmap_store.md` は存置し「delta は compare の計算 archmap-diff が置換、他は未実装構想」の注記を追加。
- **R10(archive 移動)** docs/archive へ:
  `tools/archsig/docs/sharded-archmap.md`、docs/tool の `archsig_analysis_packet.md` /
  `archsig_v1_migration_note.md` / `archmap_v1_output_replacement_gap_ledger.md` /
  第 1 世代 PRD + validation 6 本(monodromy / curvature spectrum / homotopy stokes)、
  第 1 世代理論ノート 4 本(docs/note の path_monodromy_obstruction_theorem /
  boundary_holonomy_conjecture / curvature_transfer_spectrum_theorem / homotopy_holonomy_stokes)、
  viewer PRD 3 本(archsig_v0_4_0_insight_viewer_prd / archsig_viewer_gluing_geometry_prd /
  archsig_measurement_faithfulness_and_ag_viewer_prd)。
  いずれもユーザー決定(2026-07-05)。gap ledger の partial 項目は v1 面の補修であり追わない。
- **R11(Lean guardrail 3 本の削除、独立 PR)**
  `Formal/Arch/Signature/{MonodromyMeasurement,CurvatureTransferSpectrum,HomotopyHolonomyStokes}.lean` を
  削除し、Formal.lean の import 3 行(:34 / :38 / :39)を除去、
  `lean_theorem_index_classical_aat.md` の該当節に archive 注記。`lake build` green を完了条件とする。
  (`Formal/Arch` 全体の archive は別件であり本 PRD に含めない。)

## Changed / Removed Fields

- **Removed**: typed evaluator chain 全体(normalized-archmap / typed-evaluator-results /
  architecture-distance / analysis-packet / summary-v1 / viewer-v1)、pr-review コマンドと
  archmap-delta-v0、`--strict-distance` / `--emit-raw-artifacts`、law-policy の `distanceProfileRef`、
  solid / domain / distance-profile / replacement の registry 登録、witness-counting@1 invariant、
  v1 fixture 3 ディレクトリ、Lean guardrail 3 本。
- **Changed**: registry の ag.* manifest predicate 3 件(判定語 → 中立語彙)、skills 4 本、
  docs の現行化、schema catalog(v1 系エントリの削除 — deprecated 掲載はしない、裁定10)。
- **Not changed**: AG path の計測挙動(witness-counting 廃止を除き verdict は不変)、
  archmap / measurement packet の形状、LawPolicy の新形状(PRD-4)。

## Failure Contract

- 旧 v1 schema・旧コマンド(pr-review)・旧フラグは一般エラーに落ちる
  (unknown subcommand / unknown flag / validation fail。専用の認識・案内・変換はしない)。
- FieldSig への v1 raw packet 入力は schema 不一致の一般 validation fail。

## Implementation Plan

各 PR の完了条件: archsig / fieldsig の cargo test green、lean.yml green、`git diff --check` +
hidden Unicode scan、**PR 説明に「どの反例((a)〜(d))をゼロにしたか」を 1 行**。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | ArchMapSourceV1 リネーム + registry の ag.* 分離(2 段コミット) | R1, R3 |
| PR-2 | v1 コード・fixture・tests 削除 + フラグ全廃 + **lean.yml v1 区間削除 + FieldSig v1 受理削除(同一 PR)** + 移行表 | R2, R4-R6 |
| PR-3 | 判定語残滓掃除(manifest 3 件 + witness-counting@1 廃止 + fixture / golden 更新) | R7 |
| PR-4 | skills 4 本の同期 | R8 |
| PR-5 | docs 改稿 + archive 移動 + 残存ゼロ検査の確定 | R9-R10 |
| PR-6 | Lean guardrail 3 本削除(独立。lake build green) | R11 |

順序は PR-1 → PR-2 → PR-3 →(PR-4 / PR-5 / PR-6 は相互独立、任意順)。

## Acceptance Criteria

1. **残存ゼロ検査(コード面)**: `typed_evaluator` / `ARCHMAP_V1_SCHEMA` / `archmap-delta-v0` /
   `strict-distance` / `emit-raw-artifacts` / `distanceProfileRef` / `replacement_manifests` が
   src / tests / fixtures / lean.yml に残存しない。
2. **残存ゼロ検査(語り面)**: `rg -n "archmap/v1|law-policy/v1|typed evaluator|distanceProfileRef|
   molecule|analysis-packet|pr-review" docs/tool tools/archsig/docs tools/fieldsig/docs
   tools/archsig/skills tools/archsig/README.md CLAUDE.md AGENTS.md` が残存ゼロ
   (docs/archive 内と README 移行表の行、および viewer data emitter 内の
   `moleculeGroups` / `atomEdges` 2 識別子〔0.5.x V-B2 で削除、Design Principles 5〕のみ除外)。
3. **判定語残滓ゼロ**: `tripleMismatch` / `mismatchSection` / `obstructionGenerator` /
   `witness-counting` が src / fixtures / docs(archive 除く)に残存しない。
4. **CLI 面**: `archsig pr-review` が unknown subcommand で fail する。`--strict-distance` /
   `--emit-raw-artifacts` が unknown flag で fail する。CLI help に v1 語彙が現れない。
5. **CI**: lean.yml から v1 e2e 区間が消え、v2 系(analyze → gate → handoff → catalog)が唯一の
   e2e として green。FieldSig への v1 packet 入力が一般 validation fail する負系テスト。
6. **Lean**: guardrail 3 本の削除後に `lake build` green。classical index の該当節に archive 注記。
   `Formal/AG/` に変更がない(diff 検査)。
7. **skills**: 4 本すべてが v2 語彙のみで書かれ、pr-reviewer 後継の手順(compare → gate → 人間語翻訳)が
   fixture で通しで実行できる。
8. **規模の参考値**(合否条件ではなく確認値): src 削減 ≈11,000 行。残る src ≈15,000 行
   (AG path + 共有 infrastructure)。
9. **問いへの遡及**: 各 PR の説明に、ゼロにした反例((a)〜(d))が 1 行で書かれている。

## Non-Goals

- LawPolicy / measurement-profile の新形状(basisLedger / finiteBounds / law surface)— PRD-4。
- SAGA 系 evaluator・repair-plan — PRD-4。
- archmap-creater の再設計本体(authoring CLI・二重抽出)— PRD-5。
- viewer data の v1 語彙(`moleculeGroups` / `atomEdges`)の emit 停止と投影追加 — 0.5.x
  ArchView マイルストーン(本 PRD では既知の残置として明示)。
- `Formal/Arch` 全体の archive — 別件(ユーザーが近日実施の意向)。
- ag_measurement.rs のモジュール分割(evaluator trait 化)— PRD-4 以降の新 evaluator 追加と同時に判断。
- 互換機構の追加 — 裁定10 により恒久非目標。
