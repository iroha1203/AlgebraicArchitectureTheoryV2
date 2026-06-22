---
status: picked
goal: G-aat-quality-surface-01
exploration_role: obstruction
candidate_type: genius-support / generic-criterion / projection-nonfaithfulness
capability_category: semantic-obstruction / projection-nonfaithfulness / repair-coherence / certificate-transport / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: Component projection can cover a residual component via an alias atom while missing the actual semantic residual atom, so component-equivalent supports need not preserve semantic repair closure.
origin: cycle-81
tags: [quality-surface, semantic-repair, residual-alias, projection-nonfaithfulness, generic-criterion, genius-support]
created: 2026-06-22
cycle: 81
lean: proved-in-research
---

# Semantic residual alias nonfaithfulness

## 主張

semantic residual alias gap を generic condition として定義する。
これは、source support が actual residual atom を閉じ、target support はその residual atom を欠くが、同じ protected component に写る alias atom を target support が持つ状況である。

この gap があると、source / target が component projection 上は同じに見えても、semantic repair closure は target へ反映されない。
さらに residual alias gap は `ResidualFiberSingleton` を直接 obstruct する。

## 候補種別

`genius-support` / `generic-criterion` / `projection-nonfaithfulness`

## 依拠

- Cycle 78: refined semantic repair atoms、`SemanticRepairClosed`、`ResidualFiberSingleton`、selected surface / obligation split。
- Cycle 80: selected finite atlas obstruction で必要になった component-projection reflection failure。

## 非自明性

Cycle 78 は selected non-singleton fiber counterexample を持っていた。
Cycle 81 はその失敗様式を、`ResidualAliasGap` という generic predicate に切り出す。
これにより、component projection が同じでも semantic closure が壊れる理由は、単なる “non-singleton” ではなく actual residual atom と alias atom の取り違えであることが明示される。

## 数学的興味

`ResidualFiberSingleton` は component projection が semantic repair closure を反映する十分条件である。
Cycle 81 はその反対側に、residual alias gap という明示的な obstruction criterion を置く。
つまり、semantic residual fiber の中で actual residual と alias atom が分かれると、component-level coverage は semantic closure へ faithful でなくなる。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対して、selected witness の背後にある generic failure condition を Lean theorem として固定する。
これは一般 sheaf theorem ではないが、finite atom-supported semantic repair-gluing obstruction を parametric に進めるための中核 lemma になる。

## ライバルに対する有効性

ADL、dashboard、component-projected AI-review summary は、同じ component row に写る alias atom と actual residual atom を区別しない可能性がある。
Cycle 81 は、その区別を失うと semantic repair closure を certify できないことを generic theorem と selected refined witness で示す。

## SCORE 見込み

- `score_reason`: selected counterexample を generic residual-alias obstruction criterion に引き上げ、component projection / semantic repair closure の非忠実性を axiom-free generic theorem として固定する。
- `dullness_risk`: theorem skeleton は predicate packaging に近いため、selected witness のみなら減点。価値は `ResidualAliasGap` が `ResidualFiberSingleton` failure と closure nonfaithfulness を同時に生成する generic criterion になっている点にある。
- `proof_or_evidence_plan`: `SemanticResidualAliasNonfaithfulness.lean` で generic alias-gap lemmas、selected refined repair-frontier alias gap、selected closure nonfaithfulness、universal reflection obstruction package を証明する。

## CS / SWE への帰結

component-level evidence では「repair-frontier component covered」と表示されても、その coverage が actual residual obligation atom ではなく surface alias atom 由来なら semantic repair closure は成立しない。
viewer / dashboard / review tooling は component row だけでなく semantic residual atom identity を保持する必要がある。

## 証明・根拠

Lean 証拠は `Formal/AG/Research/QualitySurface/SemanticResidualAliasNonfaithfulness.lean` に固定した。

- `SameSemanticComponentProjection`
- `ResidualAliasGap`
- `residualAliasGap_target_covers_residualComponent`
- `not_residualFiberSingleton_of_residualAliasGap`
- `semanticRepairClosed_nonfaithful_of_residualAliasGap`
- `residualAliasGap_obstructs_universal_componentReflection`
- `complete_and_surface_same_semanticComponentProjection`
- `selected_repairFrontierResidualAliasGap`
- `selected_aliasGap_covers_missed_residualComponent`
- `selected_semanticRepairClosed_nonfaithful_of_aliasGap`
- `selected_aliasGap_obstructs_componentReflection`
- `semanticResidualAliasNonfaithfulness_package`

G3 実績:

- `lake env lean Formal/AG/Research/QualitySurface/SemanticResidualAliasNonfaithfulness.lean`: pass。
- `lake build FormalAGResearch`: pass。
- axiom probe: generic alias-gap lemmas は axiom-free。selected refined repair-frontier witness / selected closure nonfaithfulness / package は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。

## 審判メモ

- 厳密性: accept / base 80 lower-bound / genius support。generic theorem と selected witness は有効。
- 研究価値: accept / base 65 / genius support。Cycle 78 / 80 の predicate-level refinement であり、主定理級ではなく support lemma。
- repo 全体価値: accept / base 70。既存 witness を再利用可能にする generic failure criterion として価値はあるが、証明核は immediate。
- ライバル比較: accept / base 85 / genius support。actual residual atom と alias atom identity の区別を失う rival への差分は明確。
- G4 SCORE 監査: confirm / base 70 / multiplier 2.0 / penalty 0 / final +140。total 10958 -> 11098。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: residual alias gap gives a generic obstruction to component-projection faithfulness for semantic repair closure.
- `goal_advancement`: semantic repair-gluing obstruction theorem の parametric failure condition を Lean-proved generic criterion として追加する。
- `planned_theorem_names`: `semanticRepairClosed_nonfaithful_of_residualAliasGap`, `not_residualFiberSingleton_of_residualAliasGap`, `semanticResidualAliasNonfaithfulness_package`
- `visible_projection`: same component projection between source and target supports。
- `protected_structure`: actual semantic residual atom, alias atom, residual fiber singleton condition, semantic repair closure。
- `exactness_or_minimality_claim`: residual alias gap prevents semantic repair closure from reflecting across component-equivalent supports。
- `nonfaithfulness_or_failure_mode`: target covers the residual component through an alias atom while missing the actual residual atom。
- `previous_cycle_delta`: Cycle 80 selected finite atlas no-reflection から、generic residual-alias obstruction criterion へ進める。
- `rival_stress_test`: component row coverage is insufficient when alias atom identity hides actual residual obligation identity。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: generic obstruction criterion for the semantic residual fiber failure behind the selected finite atlas theorem。

## 関連

- `research/ideas/g-aat-quality-surface-01-visible-local-semantic-gluing-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-semantic-support-projection-kernel.md`
- `research/ideas/g-aat-quality-surface-01-component-clearance-semantic-obstruction.md`

## 進捗ログ

- 2026-06-22: G1 generic obstruction candidate として residual alias gap を提示し、Cycle 81 picked とした。
- 2026-06-22: Lean 証拠を `SemanticResidualAliasNonfaithfulness.lean` に固定し、単体 `lake env lean`、`lake build FormalAGResearch`、axiom probe が通った。
