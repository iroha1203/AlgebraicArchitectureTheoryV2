---
status: picked
goal: G-aat-quality-surface-01
exploration_role: atlas-gauge / cut-locus invariance / genius-support convergence
candidate_type: invariant-hardening / same-carrier atlas gauge / obstruction-class-support
capability_category: semantic-obstruction / finite-atlas-transition / obstruction-class-support / invariance / genius-support
expected_base_score: 86
expected_evidence_multiplier: 2.0
expected_final_score: 172
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can tolerate renamed or noisy edge rows, but they do not prove that semantic residual obstruction classes are invariant under same-carrier atlas edge-noise gauges.
origin: cycle-93
tags: [quality-surface, semantic-repair, residual-cut, atlas-gauge, invariance, genius-support]
created: 2026-06-23
cycle: 93
lean: proved-in-research
planned_report_section: "Cycle 93: Semantic residual atlas gauge invariance"
---

# Semantic Residual Atlas Gauge Invariance

## 主張

Cycle 92 の cut-noise obstruction class を、raw cochain representative の不変性から same-carrier atlas presentation の不変性へ上げる。
同じ `Index` / `Atom` carrier 上の finite semantic repair atlas skeleton が異なる raw edge family を持っていても、`IsResidualTransitionCutPair` の cut locus が同じなら、canonical residual cut class の vanishing / nonzero と nonzero obstruction reading は保存される。

selected witness では、`selectedFrontierFlatAtlasSkeleton` に reverse raw edge `(flat, repairFrontier)` を足した `selectedEdgeNoisyFrontierFlatAtlasSkeleton` を作る。
この noisy atlas は raw edge family として元の atlas と異なるが、reverse pair は `flat` が residual-free であるため residual cut pair ではない。
したがって selected original atlas と noisy atlas は同じ residual cut locus を持ち、canonical residual cut class の nonzero と closure/data obstruction が noisy atlas 側へ移る。

この主張は same-carrier cut-locus gauge invariance に限定する。
arbitrary atlas morphism、functorial sheaf transport、true `H^1`、Cech quotient、coboundary quotient、`vanishing -> closure`、global minimality、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、UI correctness、whole-codebase quality は含まない。

## 候補種別

`invariant-hardening` / `same-carrier atlas gauge` / `obstruction-class-support`

## 依拠

- Cycle 89: finite semantic atlas residual transition cut certificate。
- Cycle 90: supplied-order residual transition cut scanner exactness。
- Cycle 91: residual obstruction one-preclass。
- Cycle 92: cut-noise invariant residual obstruction class reading。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単なる `SameResidualCutLocus` preservation だけなら tautological に見える。
この候補では、selected atlas の raw edge family を実際に変更し、追加された reverse edge が active であるにもかかわらず residual cut ではないことを Lean で証明する。
raw edge presentation は違うが residual cut locus と obstruction class reading は変わらない、という atlas presentation レベルの witness を置く点が差分である。

## 数学的興味

obstruction class が選んだ finite atlas presentation の artifact ではなく、residual cut locus に相対化された invariant として読めることを固定する。
これはまだ cohomology quotient ではないが、future finite H1-style obstruction theorem で必要な「representative / presentation 変更に対する不変性」を Lean artifact として先に置く。

## GOAL への前進

open genius target の `finite atom-supported quality atlases` という語に近づく。
Cycle 92 では同一 atlas 内の cochain representative noise を殺した。
Cycle 93 では atlas skeleton の raw edge family 自体に harmless noise が入っても、semantic residual obstruction class reading が保存されることを示す。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は edge row の追加・表示順変更・疑似 diagnostic を扱える。
しかし、それらは「追加された raw edge が residual cut locus を変えないなら obstruction class は不変である」という theorem-level invariant を持たない。
AAT 側では、raw presentation noise と residual obstruction class data を分離して扱える。

## SCORE 見込み

- `score_reason`: Cycle 92 の cochain-level cut-noise class reading を atlas presentation-level edge-noise gauge invariance へ上げる。open genius target の support node として強いが、arbitrary morphism や H1 本体ではない。
- `dullness_risk`: `SameResidualCutLocus` を仮定した保存だけなら弱い。selected noisy atlas の raw edge difference、reverse edge active/non-cut、same cut locus、nonzero obstruction transfer を揃える。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasGauge.lean` で same cut locus、gauge-related cochains、canonical transfer、selected raw-edge noisy atlas witness、theorem package を証明する。

## CS / SWE への帰結

finite atlas diagnostic では、raw edge rows と obstruction class data を分けて読む必要がある。
edge row が追加されても、それが residual-present source / residual-free target の cut locus を変えないなら、semantic residual obstruction class は同じである。
これは noisy dashboard rows や ADL-level presentation differences に対する theorem-level robustness である。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasGauge.lean` に固定した。

- `SameResidualCutLocus`
- `SameResidualCutClassGaugeRelated`
- `sameResidualCutLocus_refl`
- `sameResidualCutLocus_symm`
- `sameResidualCutLocus_trans`
- `sameResidualCutClassGaugeRelated_preserves_cutVanishes`
- `sameResidualCutClassGaugeRelated_preserves_cutNonzero`
- `sameResidualCutLocus_gaugeRelated_canonical`
- `sameResidualCutLocus_preserves_canonicalCutVanishes`
- `sameResidualCutLocus_preserves_canonicalCutNonzero`
- `gaugeRelated_nonzero_obstructs_targetTransitionClosure`
- `gaugeRelated_nonzero_obstructs_targetTransitionCoherentData`
- `selectedEdgeNoisyFrontierFlatEdge`
- `selectedEdgeNoisyFrontierFlatAtlasSkeleton`
- `selectedEdgeNoisy_rawEdge_differs_from_selected`
- `selected_flatIndexedResidualNotPresent`
- `selectedEdgeNoisy_reverse_not_residualCutPair`
- `selectedEdgeNoisy_sameResidualCutLocus_selected`
- `selectedEdgeNoisy_canonicalGaugeRelated_selected`
- `selectedEdgeNoisy_canonicalCutClass_nonzero`
- `selectedEdgeNoisy_canonicalCutClass_obstructs_transitionClosure`
- `selectedEdgeNoisy_canonicalCutClass_obstructs_transitionCoherentData`
- `semanticResidualAtlasGauge_package`

検証実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualAtlasGauge.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualAtlasGauge`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: generic preservation、canonical transfer、target obstruction は axiom-free。selected witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、same `Index` / `Atom` carrier の finite semantic repair atlas skeleton、supplied same residual cut locus、cut-locus class predicates、selected raw-edge noisy atlas witness に限定する。
unchecked: arbitrary atlas morphism、functoriality、true H1 cohomology class、Cech quotient、coboundary quotient、vanishing-to-closure theorem、general sheaf gluing、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、whole-codebase quality。

## 審判メモ

- G1 A/B/C/D: いずれも atlas gauge invariance を推奨。Cycle 92 の cochain representative noise から atlas presentation noise へ上げるのが最大 leverage と判定。
- G2 A: accept / base 84 range 80-86。selected reverse edge witness が critical。
- G2 B: accept / base 86-88。same-carrier 限定は正しいが、selected raw-edge-different witness が必須。
- G2 C: accept / base 86。`SameResidualCutClassGaugeRelated` は `SameResidualCutLocus` とセットで使うこと。
- G2 D: accept / base 84-86。arbitrary morphism ではなく same-carrier cut-locus gauge と明記する条件。
- G2 revise 解決: theorem は same-carrier に限定し、reverse raw edge が active だが `flat` residual-free のため non-cut である selected witness を package に入れた。

## 追加 required fields

- `mathematical_interest`: residual cut class を same-carrier atlas presentation noise に対する invariant として読む。
- `goal_advancement`: cochain representative noise から atlas edge presentation noise へ不変性を上げる。
- `planned_theorem_names`: `sameResidualCutClassGaugeRelated_preserves_cutNonzero`, `selectedEdgeNoisy_sameResidualCutLocus_selected`, `semanticResidualAtlasGauge_package`
- `visible_projection`: raw atlas edge family / noisy diagnostic edge row。
- `protected_structure`: residual transition cut locus、canonical cut class nonzero、same-carrier gauge-related support、transition closure obstruction。
- `exactness_or_minimality_claim`: same residual cut locus preserves canonical vanishing/nonzero。global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: raw edge family may differ while residual cut locus and obstruction class are unchanged。
- `previous_cycle_delta`: Cycle 92 の cochain-level cut-noise equivalence を atlas presentation-level edge-noise gauge invariance へ上げた。
- `rival_stress_test`: rival は noisy edge rows を持てても、same residual cut locus による obstruction class preservation theorem を持たない。
- `genius_potential`: strong support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem への invariant-hardening node。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: obstruction class が chosen atlas presentation の artifact ではないことを same-carrier gauge と selected noisy witness で固定する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-obstruction-class.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-obstruction-preclass.md`
- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-scanner.md`
- planned report section: `Cycle 93: Semantic residual atlas gauge invariance`

## 進捗ログ

- 2026-06-23: Cycle 93 G1/G2 で same-carrier residual atlas gauge invariance を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualAtlasGauge.lean` に固定し、単体 `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
