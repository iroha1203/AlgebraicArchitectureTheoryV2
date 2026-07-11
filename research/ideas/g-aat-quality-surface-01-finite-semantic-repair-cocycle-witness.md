---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / obstruction / unifier / wildcard
candidate_type: genius-support / orientation
capability_category: semantic-obstruction / repair-coherence / projection-nonfaithfulness / certificate-transport
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
rival_advantage: ADL / conformance / dashboard / AI-review readings may preserve local pass rows and visible component refinements, but they do not certify the semantic overlap repair residual that this finite witness exposes.
origin: cycle-77
tags: [quality-surface, semantic-repair, cech-cocycle, local-global-obstruction, genius-support]
created: 2026-06-22
cycle: 77
lean: proved-in-research
---

# Finite semantic repair cocycle witness for local-pass/residual-fail atlases

## 主張

finite semantic repair atom vocabulary を Research 側に置き、semantic atom を既存の protected `BridgeComponent` へ射影する。
local branch-family adequacy checker は Cycle 76 の component-level support-lift により `none` を返す。
それにもかかわらず、別の Cech-style overlap cocycle は `repairFrontierObligation` という semantic repair residual を持ち、
semantic repair gluing exactness、すなわち semantic residual emptiness は失敗する。

つまり、local branch-family adequacy pass と同じ chart-list projection は、semantic repair overlap residual を露出しない限り
semantic repair gluing exactness を決定しない。flat Cech path は semantic residual-empty であり、同じ visible/local projection を
持つ repair-frontier residual cover は semantic residual-empty ではない。ここでの gluing exactness は Research 側の有限 semantic residual
emptiness として定義し、`HandoffCechGlobalExact` や一般の sheaf gluing theorem は主張しない。

この主張は finite semantic atoms、selected branch-family adequacy checker、explicit support-lift coverage、
Cech-style overlap support、declared semantic repair support に相対化する。
source extraction completeness、ArchMap correctness、runtime repair synthesis、canonical global semantic ontology、
global sheaf completeness、whole-codebase quality は主張しない。

## 候補種別

`genius-support` / `orientation`

## 依拠

- Cycle 65: `HandoffCechExactness.lean` の overlap support vocabulary。
- Cycle 66: `OverlapObstructionBasis.lean` の exact overlap obstruction basis。
- Cycle 75: `ArbitraryBranchFamilyAdequacy.lean` の finite branch-family adequacy checker。
- Cycle 76: `ComponentRefinementSupportLift.lean` の component-level support-lift coverage generator。
- tracking Issue #2348 の genius target seed: semantic repair-gluing obstruction theorem。

## 非自明性

単なる `HandoffCechExactness` の再名付けではない。Cycle 75/76 の local branch-family adequacy pass を同じ witness に含め、
semantic atom を repair-frontier overlap residual と semantic repair support transversal に接続する。
trace-only semantic support は residual を miss し、trace plus repair-frontier semantic support は residual を hit する。
このため、semantic atom は単なる label ではなく、repair obligation / overlap residual / gluing failure を運ぶ protected datum になる。
ただし gluing failure は、このファイル内で定義した semantic residual emptiness の失敗であり、既存 Cech global exactness の一般定理ではない。

## 数学的興味

semantic obstruction を boolean failure ではなく、semantic repair residual atom を持つ finite Cech-style residual witness として固定する。
local checker の `none` と semantic residual nonempty が共存するため、Quality Surface における semantic repair gluing の tension を
小さい有限対象で表現できる。これは target theorem の support node であり、一般の local-to-global theorem ではない。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` の中核 support node を進める。
Cycle 75/76 で作った local adequacy / support-lift machinery を、semantic repair overlap cocycle の local-pass/global-fail witness へ接続する。

## ライバルに対する有効性

ADL、static analysis、conformance checker、dashboard、AI-review は local green rows、component graph preservation、
visible union、自然言語の repair observation を扱える。しかしこの候補は、visible/local pass projection では復元できない
semantic repair overlap residual と semantic residual-emptiness failure を Lean theorem として固定する。

## SCORE 見込み

- `score_reason`: local adequacy pass と semantic repair residual obstruction を同じ finite witness に載せ、open genius target の support node を進める。G2 A の revise に合わせ、`HandoffCechGlobalExact` 風の過剰表現を落とし、semantic residual emptiness witness として expected base を 55 に下げる。
- `dullness_risk`: Cech overlap support の再包装に落ちると減点。semantic atom を residual、repair transversal、visible nonfaithfulness、local adequacy pass に接続する必要がある。
- `proof_or_evidence_plan`: Research 側 Lean ファイルで semantic atom vocabulary、projection to `BridgeComponent`、semantic repair support projection、semantic residual, semantic repair transversal, local adequacy pass, local-pass/global-fail witness, visible/local nonfaithfulness package を証明する。

## CS / SWE への帰結

local checks が全て green でも、semantic repair obligation が overlap 上に残るなら semantic residual-emptiness は失敗しうる。
viewer / dashboard / review surface は local pass を表示するだけでは足りず、semantic overlap residual への drill-down を保持する必要がある。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticRepairCocycleWitness.lean` に固定した。

- `SemanticRepairAtom`
- `semanticComponent`
- `SemanticRepairSupport`
- `semanticTraceOnlySupport`
- `semanticTraceRepairFrontierSupport`
- `componentSupportOfSemantic`
- `semanticTraceRepairFrontier_projects_to_componentSupport`
- `semanticTraceOnly_projects_to_traceOnlyComponentSupport`
- `SemanticOverlapResidual`
- `SemanticRepairCocycleResidualNonempty`
- `SemanticRepairTransversal`
- `repairFrontierSemanticResidual`
- `repairFrontierSemanticResidual_nonempty`
- `semanticTraceOnly_misses_repairFrontierResidual`
- `semanticTraceRepairFrontier_hits_residuals`
- `LocalBranchFamilyAdequacyPass`
- `localBranchFamilyAdequacy_pass`
- `SemanticRepairGluingExact`
- `semanticResidual_obstructs_globalGluing`
- `repairTransportFlat_semanticGluingExact`
- `SemanticRepairGluingObstructionWitness`
- `localSemanticRepairAdequacy_not_globalGluing`
- `SameSemanticVisibleLocalProjection`
- `flat_and_semanticResidual_same_visibleLocal`
- `visibleLocalProjection_not_faithful_to_semanticRepairGluing`
- `semanticRepairCocycleWitness_package`

G3 実績:

- `focused Lean check: ResearchLean/AG/QualitySurface/SemanticRepairCocycleWitness.lean`: pass。
- `Research package build`: pass。
- axiom probe: core semantic definitions と `SemanticRepairGluingExact` / `semanticResidual_obstructs_globalGluing` は axiom-free。flat exactness / nonfaithfulness / package は既存 Cech exactness infrastructure 由来の標準 `propext` / `Quot.sound` を継承する。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。

## 審判メモ

- 厳密性: accept / base 55 / genius support。claim boundary は finite semantic atoms / selected local checker / Cech-style overlap support / semantic residual emptiness に限定され、`HandoffCechGlobalExact` 風の一般 gluing claim はしない。G3 指摘後に flat cover の semantic residual emptiness を package に追加し、same visible/local projection が exact / non-exact semantic value を分ける形へ強化した。
- 研究価値: accept / base 55 / genius support。local adequacy pass と別 overlap residual を同じ finite witness に載せ、visible/local projection が semantic residual を忘れる点を評価。
- repo 全体価値: accept / base 55 / genius support。Lean / report / future paper seed / future projection surface への接続を持つが、主定理候補ではなく support node として扱う。
- ライバル比較: accept / base 55 / genius support。local pass / visible projection に対する semantic overlap residual の recoverability gap が主差分。
- G4 SCORE 監査: confirm / base 55 / multiplier 2.0 / penalty 0 / final +110。genius は unlock ではなく support として通常 SCORE に計上する。

## 追加 required fields

- `mathematical_interest`: local checker pass と semantic residual nonempty の共存を finite cocycle witness として表す点。
- `goal_advancement`: semantic repair-gluing obstruction theorem の support nodeを Lean-proved residual witness として進める。
- `planned_theorem_names`: `repairTransportFlat_semanticGluingExact`, `localSemanticRepairAdequacy_not_globalGluing`, `semanticTraceOnly_misses_repairFrontierResidual`, `visibleLocalProjection_not_faithful_to_semanticRepairGluing`, `semanticRepairCocycleWitness_package`
- `visible_projection`: local branch-family adequacy pass and same chart list。semantic overlap residual は忘れる。
- `protected_structure`: semantic repair atom, projection to protected component, semantic overlap residual, semantic repair transversal, semantic residual-emptiness obstruction。
- `exactness_or_minimality_claim`: semantic residual nonempty implies not `SemanticRepairGluingExact` in the selected finite witness。global canonical minimality と `HandoffCechGlobalExact` は主張しない。
- `nonfaithfulness_or_failure_mode`: visible/local pass projection is not faithful to semantic residual emptiness, since the flat cover is semantic-residual-empty while the same visible/local projection with repair-frontier residual is not.
- `previous_cycle_delta`: Cycle 75 checker and Cycle 76 component support-lift を semantic residual obstruction witness へ接続する。
- `rival_stress_test`: local pass rows / component union / AI review summary が同じでも、semantic overlap residual を保持しなければ semantic residual-emptiness failure を復元できない。
- `genius_potential`: support only, no immediate unlock
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite local-pass/global-fail semantic repair cocycle witness。

## 関連

- `research/ideas/g-aat-quality-surface-01-arbitrary-branch-family-adequacy-checker.md`
- `research/ideas/g-aat-quality-surface-01-component-refinement-support-lift.md`
- `research/ideas/g-aat-quality-surface-01-finite-cech-handoff-obstruction-exactness.md`
- `research/ideas/g-aat-quality-surface-01-overlap-obstruction-basis-repair-duality.md`

## 進捗ログ

- 2026-06-22: G1 四ロール候補 pool で finite semantic repair cocycle witness が最有力候補として収束。Cycle 77 picked とした。
- 2026-06-22: Lean 証拠を `SemanticRepairCocycleWitness.lean` に固定し、単体 `lake env lean` と `Research package build` が通った。
- 2026-06-22: G2 A の revise を受け、`HandoffCechGlobalExact` 風の強い global gluing 表現を削除し、Research 側定義 `SemanticRepairGluingExact := no semantic residual` に対する finite support witness として claim と expected SCORE を下げた。
- 2026-06-22: G2 再審査は四者 accept、base 55、multiplier 2.0、genius support。G4 SCORE 監査は final +110 を confirm。
- 2026-06-22: G3 formalization audit の revise を受け、`repairTransportFlat_semanticGluingExact` を追加し、同じ visible/local projection の flat exact / residual non-exact 分離を Lean package に含めた。
