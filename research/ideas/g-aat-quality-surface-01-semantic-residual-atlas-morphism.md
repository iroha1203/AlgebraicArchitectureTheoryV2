---
status: picked
goal: G-aat-quality-surface-01
exploration_role: cut-locus transport / carrier-change invariance / genius-support convergence
candidate_type: finite cut-locus transport / obstruction-class-support / carrier-change
capability_category: semantic-obstruction / finite-atlas-transition / obstruction-class-support / transport-invariance / genius-support
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can move diagnostics between presentations, but they do not prove cut-locus obstruction-class transport across finite carrier changes.
origin: cycle-94
tags: [quality-surface, semantic-repair, residual-cut, atlas-transport, carrier-change, genius-support]
created: 2026-06-23
cycle: 94
lean: proved-in-research
planned_report_section: "Cycle 94: Semantic residual cut-locus transport beyond same carrier"
---

# Semantic Residual Cut-Locus Transport Beyond Same Carrier

## 主張

Cycle 93 の same-carrier atlas gauge invariance を、異なる finite index carrier 間の supplied residual cut-locus transport へ上げる。
`ResidualCutLocusEmbedding` は source residual cut pair を target residual cut pair へ送る有限 map であり、`pushResidualCutCochain` は source cochain の cut-supported support を target cochain へ push する。
source class が nonzero なら push target class も nonzero であり、target residual transition closure と transition-coherent atlas data を阻む。

さらに `ResidualCutLocusEquivalence` は target cut pair が source cut preimage を持つ cut-surjective map である。
この仮定の下で、canonical residual cut class の `CutVanishes` / `CutNonzero` は source/target 間で同値になる。

selected witness では、`SelectedExtendedOverlapIndex := Option SelectedSemanticOverlapIndex` を使って extra isolated index `none` を持つ target atlas を作る。
`none` は active edge に参加せず、target residual cuts はすべて original selected atlas の cut の image である。
これにより、selected frontier-to-flat obstruction class が carrier change 後の extended atlas へ transport され、target closure/data obstruction として残る。

この主張は finite residual cut-locus transport に限定する。
arbitrary atlas category、general atlas morphism functoriality、atom-map semantic completeness、true `H^1`、Cech quotient、coboundary quotient、`vanishing -> closure`、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、UI correctness、whole-codebase quality は含まない。

## 候補種別

`finite cut-locus transport` / `obstruction-class-support` / `carrier-change`

## 依拠

- Cycle 92: cut-noise invariant residual obstruction class reading。
- Cycle 93: same-carrier residual atlas gauge invariance。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単なる `cut_preserving` field だけなら wrapper になる。
この候補では、pushforward cochain、vanishing/nonzero iff、target obstruction theorem、cut-surjective canonical equivalence、そして `Option` carrier の concrete selected witness を揃える。
selected witness は same carrier alias ではなく、extra isolated index を持つ target carrier であり、target cuts が source cuts の image だけであることを Lean で示す。

## 数学的興味

semantic residual obstruction class が chosen finite carrier の artifact ではなく、supplied finite cut-locus transport に沿って移送できることを示す。
これは H1-style theorem そのものではないが、future repair-gluing obstruction theorem が presentation/refinement/reindexing に耐えるための carrier-change invariance を与える。

## GOAL への前進

open genius target の `finite atom-supported quality atlases` に向け、obstruction class を single carrier / same-carrier gauge から cross-carrier finite transport へ上げた。
これにより、finite atlas presentation が変わっても、residual cut-locus obstruction reading を transport できる。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は diagnostics を別表示や別 index schema へ移せる。
しかし、それらは source cut nonzero が target cut nonzero と target closure/data obstruction を theorem-level に transport する条件を持たない。
AAT 側では、cut-preserving / cut-surjective finite maps の下で obstruction class data を移送できる。

## SCORE 見込み

- `score_reason`: Cycle 93 の same-carrier invariance を cross-carrier cut-locus transport へ上げる。open genius target への強い support node だが、arbitrary atlas morphism や H1 本体ではない。
- `dullness_risk`: `cut_preserving` だけなら仮定を言い換えるだけになる。push cochain、canonical iff、selected extended carrier witness、`none` isolation、target obstruction を揃える。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasMorphism.lean` で embedding/equivalence、pushforward、canonical transport、selected extended carrier witness、theorem package を証明する。

## CS / SWE への帰結

finite architecture diagnostics を別 schema / presentation / carrier へ移すとき、単なる row copy ではなく residual cut-locus transport condition が必要になる。
source diagnostic が residual cut nonzero を持ち、その cut locus が target に transport されるなら、target 側でも transition closure/data obstruction として読むことができる。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasMorphism.lean` に固定した。

- `mapResidualPair`
- `ResidualCutLocusEmbedding`
- `ResidualCutLocusEquivalence`
- `pushResidualCutCochain`
- `pushResidualCutCochain_nonzero_of_sourceNonzero`
- `pushResidualCutCochain_targetVanishes_to_sourceVanishes`
- `pushResidualCutCochain_sourceVanishes_to_targetVanishes`
- `pushResidualCutCochain_cutVanishes_iff`
- `pushResidualCutCochain_cutNonzero_iff`
- `pushResidualCutCochain_nonzero_obstructs_targetTransitionClosure`
- `pushResidualCutCochain_nonzero_obstructs_targetTransitionCoherentData`
- `residualCutLocusEquivalence_pushCanonical_agrees_targetCanonical_onCut`
- `residualCutLocusEquivalence_preserves_canonicalCutVanishes`
- `residualCutLocusEquivalence_preserves_canonicalCutNonzero`
- `SelectedExtendedOverlapIndex`
- `selectedToExtendedIndex`
- `selectedExtendedToSelectedIndex`
- `selectedExtendedFrontierFlatEdge`
- `selectedExtendedFrontierFlatAtlasSkeleton`
- `selectedExtended_none_no_outgoing_edge`
- `selectedExtended_none_no_incoming_edge`
- `selectedExtended_none_not_cut_source`
- `selectedExtended_none_not_cut_target`
- `selectedToExtendedResidualCutEmbedding`
- `selectedToExtended_cut_surjective`
- `selectedToExtendedResidualCutEquivalence`
- `selectedExtended_pushCanonicalCutClass_nonzero`
- `selectedExtended_canonicalCutClass_nonzero`
- `selectedExtended_canonicalCutClass_obstructs_transitionClosure`
- `selectedExtended_canonicalCutClass_obstructs_transitionCoherentData`
- `semanticResidualAtlasMorphism_package`

検証実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasMorphism.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualAtlasMorphism`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: generic push/transport/canonical theorem は axiom-free。selected cut-surjectivity は標準 `propext`。selected nonzero と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、finite semantic repair atlas skeleton 間の supplied residual cut-locus embedding/equivalence、pushforward cochains、canonical vanishing/nonzero transport、selected extended carrier witness に限定する。
unchecked: arbitrary atlas morphism category、atom-map semantic completeness、projection/cover naturality、functorial sheaf transport、true H1 cohomology class、Cech quotient、coboundary quotient、vanishing-to-closure theorem、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、whole-codebase quality。

## 審判メモ

- G1 A/B/C/D: いずれも beyond-same-carrier cut-locus transport を推奨。H1-style adapter はまだ早く、carrier-change invariance を先に固定すべきと判定。
- G2 A: accept / base 88。`ResidualCutLocusEmbedding` は forward transport、canonical iff は cut-surjective equivalence に限定すること。
- G2 B: accept / base 88-90。`finite cut-locus preserving maps beyond same carrier` と表現し、arbitrary morphism と書かないこと。
- G2 revise 解決: pushforward の vanishing/nonzero を iff まで補強し、`none` の edge/cut 不参加 theorem と selected extended carrier witness を theorem package に入れた。

## 追加 required fields

- `mathematical_interest`: residual obstruction class を finite carrier change に沿って transport する。
- `goal_advancement`: same-carrier gauge invariance から cross-carrier finite cut-locus transport へ上げる。
- `planned_theorem_names`: `pushResidualCutCochain_cutNonzero_iff`, `residualCutLocusEquivalence_preserves_canonicalCutNonzero`, `semanticResidualAtlasMorphism_package`
- `visible_projection`: finite index carrier / diagnostic schema / atlas presentation。
- `protected_structure`: residual transition cut locus、cut-supported cochain pushforward、canonical vanishing/nonzero、target transition closure obstruction。
- `exactness_or_minimality_claim`: cut-surjective equivalence preserves canonical vanishing/nonzero。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: carrier/schema changes do not preserve obstruction unless residual cut-locus transport conditions are supplied。
- `previous_cycle_delta`: Cycle 93 の same-carrier gauge invariance を beyond-same-carrier transport へ拡張した。
- `rival_stress_test`: rival は diagnostics を copy/rename できても、cut-locus transport と target obstruction theorem を持たない。
- `genius_potential`: strong support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem への carrier-change invariance node。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: obstruction class が finite carrier/presentation change に耐えることを supplied cut-locus transport で固定する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-atlas-gauge.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-obstruction-class.md`
- planned report section: `Cycle 94: Semantic residual cut-locus transport beyond same carrier`

## 進捗ログ

- 2026-06-23: Cycle 94 G1/G2 で beyond-same-carrier residual cut-locus transport を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualAtlasMorphism.lean` に固定し、単体 `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
