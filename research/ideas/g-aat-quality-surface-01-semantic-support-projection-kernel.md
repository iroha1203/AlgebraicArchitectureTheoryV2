---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / obstruction / unifier / wildcard
candidate_type: genius-support / unification / projection-kernel
capability_category: semantic-obstruction / projection-nonfaithfulness / repair-coherence / certificate-transport
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: ADL / conformance / dashboard / component-projected AI-review summaries may preserve component-level repair support and local adequacy, but they do not preserve the semantic fiber needed to decide refined repair-residual closure.
origin: cycle-78
tags: [quality-surface, semantic-repair, projection-kernel, residual-fiber, genius-support]
created: 2026-06-22
cycle: 78
lean: proved-in-research
---

# Semantic support projection kernel for repair-residual closure

## 主張

Cycle 77 の semantic repair cocycle witness を一段細かくし、`repairFrontier` component の semantic fiber を
`repairFrontierSurface` と `repairFrontierObligation` に分ける。二つの refined semantic support は同じ
`BridgeComponent` support へ射影され、同じ `LocalBranchFamilyAdequacyPass` を持つ。しかし refined semantic residual
closure では、surface-reading support は obligation residual を miss し、complete / obligation-aware support は hit する。

さらに一般 criterion として、residual component fiber が singleton なら、component projection equality は semantic repair closure を反映することを証明する。
選択 witness ではこの singleton condition が壊れ、同じ component projection の下で semantic closure が分かれる。
ただし、multiple semantic atoms が同じ component に射影される任意の場合に非忠実性が生じる、という universal converse は主張しない。

これは finite semantic projection-kernel theorem であり、一般 sheaf gluing、source extraction completeness、ArchMap correctness、
runtime repair synthesis、canonical global semantic ontology、global sheaf completeness、whole-codebase quality は主張しない。

## 候補種別

`genius-support` / `unification` / `projection-kernel`

## 依拠

- Cycle 75: finite branch-family adequacy checker。
- Cycle 76: component-level support-lift coverage generator。
- Cycle 77: finite semantic repair cocycle witness and semantic residual emptiness separation。
- G1 wildcard: residual fiber singleton criterion を入れると component projection kernel としての価値が上がる、という提案。

## 非自明性

単に semantic atom を増やすだけではない。一般 theorem
`componentProjection_reflects_semanticRepairClosed_of_residualFiberSingleton` により、component projection が semantic closure を反映する十分条件を明示する。
その上で selected witness が `ResidualFiberSingleton` を満たさないこと、同じ component projection を持つ support の一方だけが
`SemanticRepairClosed` を満たすことを証明する。

このため、projection loss は boolean failure ではなく、semantic residual fiber の多重性として局所化される。

## 数学的興味

component support は `BridgeComponent` 上の coarse support であり、semantic repair closure は projection fiber 内の obligation atom を見る。
fiber が singleton なら component support は semantic closure を反映できるが、fiber が複数 atom を含むと同じ component projection でも closure が分かれる。
これは Quality Surface の semantic obstruction を、projection kernel / residual fiber criterion として読むための有限 theorem である。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` の support node を進める。
Cycle 77 が local-pass / residual-fail witness を固定したのに対し、Cycle 78 は「なぜ component/local projection が semantic residual closure を決められないのか」を
residual fiber singleton condition と selected counterexample で固定する。

## ライバルに対する有効性

ADL、static analysis、conformance checker、dashboard、component-projected AI-review summary は component-level repair support や local adequacy pass を表示できる。
しかし semantic fiber 内の `repairFrontierSurface` と `repairFrontierObligation` を区別しないと、同じ component support に見える二つの support の
semantic repair closure の差を復元できない。

## SCORE 見込み

- `score_reason`: Cycle 77 の semantic residual witness を projection-kernel criterion へ上げ、component projection が semantic closure を反映する条件と失敗例を同じ Lean package に入れる。
- `dullness_risk`: refined semantic atoms の人工的 split だけに見えると減点。generic residual fiber singleton theorem と selected counterexample の両方を theorem package に含めることで回避する。
- `proof_or_evidence_plan`: `SemanticSupportProjectionKernel.lean` で refined semantic atom、component projection、generic closure criterion、selected non-singleton fiber、same component projection / different closure witness、component-projected local adequacy package を証明する。

## CS / SWE への帰結

local pass rows や component-level repair support が一致しても、semantic obligation fiber を潰すと repair closure 判定を誤る。
viewer / dashboard / review surface は component support だけでなく semantic fiber 内の obligation residual を保持する必要がある。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticSupportProjectionKernel.lean` に固定した。

- `RefinedSemanticRepairAtom`
- `refinedSemanticComponent`
- `surfaceRepairSupport`
- `obligationRepairSupport`
- `completeRepairSupport`
- `componentSupportOfRefinedSemantic`
- `surfaceRepairSupport_projects_to_componentSupport`
- `obligationRepairSupport_projects_to_componentSupport`
- `completeRepairSupport_projects_to_componentSupport`
- `surface_and_obligation_same_componentProjection`
- `surface_and_complete_same_componentProjection`
- `SemanticComponentSupport`
- `SemanticProjectedResidual`
- `SemanticRepairClosed`
- `ResidualFiberSingleton`
- `componentProjection_reflects_semanticRepairClosed_of_residualFiberSingleton`
- `completeRepairSupport_semanticRepairClosed`
- `surfaceRepairSupport_not_semanticRepairClosed`
- `refinedSemanticProjection_not_residualFiberSingleton`
- `selected_projectionKernel_not_faithful_to_semanticRepairClosed`
- `RefinedSemanticRepairResidual`
- `RefinedSemanticRepairTransversal`
- `refinedRepairFrontierResidual`
- `surfaceRepairSupport_misses_refinedResidual`
- `obligationRepairSupport_hits_refinedResidual`
- `ComponentProjectedLocalAdequacy`
- `surfaceRepairSupport_componentProjectedAdequacy`
- `obligationRepairSupport_componentProjectedAdequacy`
- `componentProjection_not_faithful_to_refinedSemanticClearance`
- `semanticSupportProjectionKernel_package`

G3 実績:

- `focused Lean check: ResearchLean/AG/QualitySurface/SemanticSupportProjectionKernel.lean`: pass。
- `Research package build`: pass。
- axiom probe: generic projection criterion と core support/projection declarations は axiom-free。selected counterexample / component-projected adequacy / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` はない。

## 審判メモ

- 厳密性: accept / base 80 / genius support。claim boundary は finite selected witness / generic residual fiber criterion / semantic closure に限定され、Lean claim と card claim は一致している。
- 研究価値: accept / base 80 / genius support。`ResidualFiberSingleton` criterion と selected counterexample により、Cycle 77 witness を projection-kernel theorem へ一段上げる点を評価。
- repo 全体価値: accept / base 80 / genius support。Lean / report / future paper seed / future viewer drill-down への接続を持つ。人工的 split のリスクは generic criterion で緩和される。
- ライバル比較: accept / base 80 / genius support。component projection equality では semantic residual closure を復元できない点が主差分。AI-review への主張は component-projected summary に限定する。
- G4 SCORE 監査: confirm / base 80 / multiplier 2.0 / penalty 0 / final +160。total 10508 -> 10668。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: component projection が semantic closure を反映する十分条件を residual fiber singleton として与え、その失敗を selected finite witness で示す点。
- `goal_advancement`: semantic repair-gluing obstruction theorem の projection-kernel support node を Lean-proved criterion + counterexample として進める。
- `planned_theorem_names`: `componentProjection_reflects_semanticRepairClosed_of_residualFiberSingleton`, `selected_projectionKernel_not_faithful_to_semanticRepairClosed`, `componentProjection_not_faithful_to_refinedSemanticClearance`, `semanticSupportProjectionKernel_package`
- `visible_projection`: component-level repair support plus local branch-family adequacy pass。
- `protected_structure`: refined semantic atom fiber, residual fiber singleton condition, semantic repair closure, selected non-singleton fiber counterexample。
- `exactness_or_minimality_claim`: no general sheaf gluing claim。finite semantic repair closure is reflected by component projection under residual fiber singleton。non-singleton fiber generally implies nonfaithfulness という converse は主張しない。
- `nonfaithfulness_or_failure_mode`: same component projection and same local adequacy pass do not determine refined semantic residual closure when a residual component has a non-singleton semantic fiber。
- `previous_cycle_delta`: Cycle 77 local-pass / residual-fail witness を、projection-kernel criterion and selected counterexample へ強化する。
- `rival_stress_test`: component-level support rows / local adequacy pass / component-projected AI review summary が同じでも、semantic fiber obligations を保持しなければ semantic repair closure を復元できない。
- `genius_potential`: support only, no immediate unlock
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: finite residual-fiber projection-kernel criterion。

## 関連

- `research/ideas/g-aat-quality-surface-01-finite-semantic-repair-cocycle-witness.md`
- `research/ideas/g-aat-quality-surface-01-component-refinement-support-lift.md`
- `research/ideas/g-aat-quality-surface-01-arbitrary-branch-family-adequacy-checker.md`
- `research/ideas/g-aat-quality-surface-01-overlap-obstruction-basis-repair-duality.md`

## 進捗ログ

- 2026-06-22: G1 四ロール候補 pool で refined semantic support projection kernel と residual fiber singleton criterion が有力候補として収束。Cycle 78 picked とした。
- 2026-06-22: Lean 証拠を `SemanticSupportProjectionKernel.lean` に固定し、単体 `lake env lean` と `Research package build` が通った。
- 2026-06-22: G2 四審判はすべて accept、base 80、multiplier 2.0、genius support。G4 SCORE 監査は final +160 を confirm。
