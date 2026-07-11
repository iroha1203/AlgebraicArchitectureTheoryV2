---
status: picked
goal: G-aat-quality-surface-01
exploration_role: unifier / indexed-atlas / genius-support
candidate_type: genius-support / indexed-transport / finite-atlas-obstruction
capability_category: semantic-obstruction / transport-naturality / repair-coherence / certificate-transport / quality-surface
expected_base_score: 84
expected_evidence_multiplier: 2.0
expected_final_score: 168
evidence_stage: proved-in-research
rival_advantage: Component-preserving per-overlap transport and exact image support still do not certify semantic repair closure unless every indexed target residual has a supported source lift.
origin: cycle-87
tags: [quality-surface, semantic-repair, indexed-transport, finite-atlas, residual-support, genius-support]
created: 2026-06-22
cycle: 87
lean: proved-in-research
---

# Semantic residual indexed transport

## 主張

semantic residual support transport は、単一 cover だけでなく indexed finite overlap family 上で扱う必要がある。
`IndexedResidualSupportTransport` は各 overlap index ごとに residual map、target residual coverage、residual atom 上の support truth preservation を持つ。
Lean では、この indexed transport が source / target の `IndexedSemanticRepairClosed` を同値に反映することを証明した。
さらに `IndexedResidualTransitionClosed` と `IndexedResidualSupportTransportWithTransitions` を導入し、選ばれた atlas edge に沿って residual atom が cross-index に運べるための transition coherence を明示した。

さらに exact indexed transported support の下で、target 側の indexed semantic repair closure は、すべての indexed target residual が supported source lift を持つことと同値になる。
selected two-index family では、flat overlap と repair-frontier overlap を同時に持つ。
`obligationAliasTransport` は各 index で component-preserving かつ exact image support を持つが、repair-frontier index で `repairFrontierObligation` を supported lift できない。
したがって selected finite semantic repair-gluing atlas obstruction は indexed residual support transport へは持ち上がらない。
加えて、repair-frontier から flat overlap へ向かう selected atlas edge では、repair-frontier residual を flat residual へ transition すること自体が不可能である。

## 候補種別

`genius-support` / `indexed-transport` / `finite-atlas-obstruction`

## 依拠

- Cycle 77: visible/local semantic gluing obstruction。
- Cycle 85: residual support transport と target supported-lift criterion。
- Cycle 86: finite residual scanner と unsupported target residual certificate。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

Cycle 85 は一つの source / target cover pair の transport criterion だった。
Cycle 87 は criterion を index family に上げ、overlap family 全体の closure reflection と selected finite atlas obstruction を同じ theorem package に入れる。
indexed closure iff の一般部は pointwise lifting に近いが、revision で selected atlas edge 上の cross-index residual transition coherence を追加した。
これにより、component-preserving exact image support が family-level repair-gluing transport にならないだけでなく、repair-frontier residual を flat overlap へ送る atlas-edge residual transition そのものが存在しないことを示す。

## 数学的興味

indexed residual support transport は、finite atlas の各 overlap chart で residual identity と support truth を保存する gluing-level transport condition である。
selected witness では flat index は residual-free だが、repair-frontier index は obligation residual を持つ。
この非対称性により、visible/local finite atlas obstruction は family-level transport failure として読める。
特に selected repair-frontier-to-flat edge は、residual-bearing overlap から residual-free overlap への transition closure を要求した瞬間に破綻する。

## GOAL への前進

open genius target `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases` に対し、
single-cover transport kernel と finite scanner certificate を indexed finite overlap family criterion と cross-index edge transition no-go へ統合した。
これは finite semantic repair-gluing obstruction theorem へ近い support node であり、threshold 12000 到達候補だが、1000 点 unlock ではない。

## ライバルに対する有効性

ADL、component dashboard、AI review summary、component-preserving migration は、各 overlap view で同じ component row や exact image support を提示できる。
しかし indexed target residual の supported lift を全 index で示せなければ、finite atlas の semantic repair closure は certify できない。
AAT は、flat overlap では問題がなくても repair-frontier overlap で semantic obligation residual が gluing transport を壊すことを Lean theorem として固定できる。

## SCORE 見込み

- `score_reason`: Cycle 85/86 の residual transport / scanner を indexed finite atlas family へ持ち上げ、selected finite semantic repair-gluing obstruction と no indexed residual support transport を同じ package に統合する。
- `dullness_risk`: indexed closure iff の一般部は pointwise lifting に近い。revision 後の価値は selected flat / repair-frontier two-index atlas obstruction、frontier-to-flat residual transition no-go、family-level no-transport theorem の接続にある。
- `proof_or_evidence_plan`: `SemanticResidualIndexedTransport.lean` で indexed closure iff、exact support / supported-lift iff、cross-index residual transition closure、missed indexed target residual obstruction、selected two-index witness、no indexed residual support transport、no transition-coherent indexed residual support transport を証明する。

## CS / SWE への帰結

quality surface の repair-gluing certification では、個別 chart や component row が green でも十分ではない。
finite overlap family の全 index で target residual atom が supported source lift を持つ必要がある。
これは component-level dashboard や AI summary では保持しにくい family-indexed residual identity condition を AAT 側で certificate 化する。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualIndexedTransport.lean` に固定した。

- `IndexedSemanticRepairClosed`
- `IndexedTransportedSemanticSupportExact`
- `IndexedTargetResidualSupportedBySource`
- `MissedIndexedTargetResidualTransport`
- `IndexedComponentPreservingSemanticTransport`
- `IndexedResidualSupportTransport`
- `IndexedResidualTransitionClosed`
- `IndexedResidualSupportTransportWithTransitions`
- `IndexedResidualSupportTransport.at`
- `indexedResidualSupportTransport_semanticRepairClosed_iff`
- `indexedResidualSupportTransportWithTransitions_semanticRepairClosed_iff`
- `indexedSemanticRepairClosed_iff_indexedTargetResidualSupported`
- `missedIndexedTargetResidualTransport_obstructs_indexedSupported`
- `missedIndexedTargetResidualTransport_obstructs_indexedSemanticRepairClosed`
- `SelectedSemanticOverlapIndex`
- `selectedIndexedCover`
- `selectedIndexedProjection`
- `selectedIndexedSourceSupport`
- `selectedIndexedTargetSupport`
- `selectedIndexedTransport`
- `selectedFrontierToFlatEdge`
- `selected_flat_no_refinedResidual`
- `selectedIndexedSource_semanticRepairClosed`
- `selectedIndexedSupportExact`
- `selectedIndexedTransport_componentPreserving`
- `selectedIndexed_missedTargetResidual`
- `selected_no_frontierToFlatResidualTransition`
- `selectedIndexedTarget_not_semanticRepairClosed`
- `selected_no_indexedResidualSupportTransport`
- `selected_no_indexedResidualSupportTransportWithTransitions`
- `semanticResidualIndexedTransport_package`

G3 初期実績:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SemanticResidualIndexedTransport.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualIndexedTransport`: pass。
- `lake build ResearchLean.AG`: pass。
- `lake env lean research/lean/ResearchLean.lean`: pass。
- `lake build`: pass。既存の `Formal/Arch/Extension/FeatureExtensionExamples.lean` linter warning のみ。
- axiom probe: indexed closure iff、transition-coherent closure iff、exact support / supported-lift iff は axiom-free。selected frontier-to-flat no-go、transition-coherent no-go、package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はない。

## 審判メモ

- G1 prior frontier: Cycle 86 report の Next Frontier は `indexed overlap-family residual support transport` を次候補として挙げた。
- G2 rigor: initial revise / base 62 / genius no。pointwise indexed lifting に近く、cross-index coherence がないとの指摘を受けた。revision 後は accept / base 78 / genius no。
- G2 revision: `IndexedResidualTransitionClosed`、`IndexedResidualSupportTransportWithTransitions`、selected frontier-to-flat residual transition no-go、transition-coherent no-go を追加し、A 審判の revise を解消した。
- G2 research value: accept / base 82 / genius no。
- G2 repo integration: accept / base 84 / genius no。
- G2 rival comparison: accept / base 84 / genius no。
- G4 SCORE 監査: reduce / base 84 / multiplier 2.0 / penalty 0 / final +168。total 11824 -> 11992。genius は support node であり unlock ではない。

## 追加 required fields

- `mathematical_interest`: family-indexed semantic repair closure preservation を indexed residual support transport / supported target residual lift / cross-index residual transition closure として特徴づける。
- `goal_advancement`: finite semantic repair-gluing obstruction theorem の family-level transport criterion と atlas-edge transition no-go を Lean-proved support node として固定する。
- `planned_theorem_names`: `indexedResidualSupportTransport_semanticRepairClosed_iff`, `indexedResidualSupportTransportWithTransitions_semanticRepairClosed_iff`, `indexedSemanticRepairClosed_iff_indexedTargetResidualSupported`, `selected_no_frontierToFlatResidualTransition`, `selected_no_indexedResidualSupportTransportWithTransitions`, `semanticResidualIndexedTransport_package`
- `visible_projection`: flat / repair-frontier two-index overlap family, selected frontier-to-flat atlas edge, and component-preserving semantic atom transport。
- `protected_structure`: indexed target residual atom, supported source lift, indexed residual support transport, cross-index residual transition closure, semantic repair closure。
- `exactness_or_minimality_claim`: exact indexed transported support の下で target indexed closure は indexed supported-lift coverage と同値。transition-coherent transport は selected atlas edge 上の residual transition closure も要求する。global canonical atlas や arbitrary sheaf gluing は主張しない。
- `nonfaithfulness_or_failure_mode`: selected repair-frontier index has a missed obligation residual, and the frontier-to-flat atlas edge cannot carry that residual into the residual-free flat overlap。
- `previous_cycle_delta`: Cycle 85 の transport criterion と Cycle 86 の finite residual diagnostic を indexed finite overlap family criterion へ統合する。
- `rival_stress_test`: component-preserving per-overlap migration cannot certify family-level semantic closure without indexed target residual lifts and selected edge residual-transition closure。
- `genius_potential`: support node
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: indexed finite-atlas transport criterion and selected no-transport obstruction.

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-transport-naturality.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-finite-scanner.md`
- `research/ideas/g-aat-quality-surface-01-visible-local-semantic-gluing-obstruction.md`

## 進捗ログ

- 2026-06-22: Cycle 87 indexed finite-atlas transport candidate として picked。
- 2026-06-22: Lean 証拠を `SemanticResidualIndexedTransport.lean` に固定し、単体 `lake env lean`、module build、`ResearchLean.AG` build、full `lake build` が通った。
- 2026-06-22: G2 rigor revise を受け、cross-index transition coherence と selected frontier-to-flat residual transition no-go を Lean 証拠へ追加した。
- 2026-06-22: G4 SCORE 監査で base 84 / final +168 に reduce 確定した。
