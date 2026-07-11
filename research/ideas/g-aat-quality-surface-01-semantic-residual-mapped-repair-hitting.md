---
status: picked
goal: G-aat-quality-surface-01
exploration_role: cross-carrier repair necessity / mapped residual cut persistence / genius-support convergence
candidate_type: cross-carrier residual repair-hitting theorem / obstruction-class-support / repair-necessity
capability_category: semantic-obstruction / repair-necessity / cut-locus-transport / finite-atlas-transition / genius-support
expected_base_score: 90
expected_evidence_multiplier: 2.0
expected_final_score: 180
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can remap diagnostics between schemas, but they do not prove that unhit edge/present/free preservation across a carrier map transports repair-hitting necessity for residual cut obstruction classes.
origin: cycle-97
tags: [quality-surface, semantic-repair, residual-cut, repair-hitting, carrier-change, obstruction-transport, genius-support]
created: 2026-06-23
cycle: 97
lean: proved-in-research
planned_report_section: "Cycle 97: Cross-carrier residual cut repair-hitting transport"
---

# Cross-Carrier Residual Cut Repair-Hitting Transport

## 主張

Cycle 96 の same-carrier repair-hitting necessity を、finite carrier / schema change をまたぐ形へ持ち上げる。
`ResidualCutRepairTransportMap` は old atlas から new atlas への `mapIndex` と、source-side supplied bookkeeping predicates としての `edgeHit`、`sourceHit`、`targetHit` を持つ。
この map は、hit されていない old active edge、residual-present source、residual-free target を new 側へ保存する。
したがって unhit old residual cut は new residual cut へ写り、new canonical residual cut class を nonzero にする。

その結果、new canonical residual cut class が vanishes するなら、old residual cut は source-side の edge/source/target hit predicate のどこかで hit されていなければならない。
また、unhit old residual cut は new transition closure と new transition-coherent atlas data を阻む。

Cycle 95 の `ResidualCutInducingAtlasMap` は、hit predicates に依存しない保存 law を持つため、任意の source-side hit bookkeeping predicates に対して `ResidualCutRepairTransportMap` を誘導する。
この bridge は補助 corollary であり、主成果は generic `ResidualCutRepairTransportMap` の unhit preservation laws から repair-hit necessity を導く theorem である。
selected witness では `selectedToExtendedResidualCutInducingMap` と `Option SelectedSemanticOverlapIndex` extended carrier を用い、selected frontier-to-flat cut が no-hit のまま extended target obstruction として残ることを示す。

この主張は repair-hitting の必要条件である。
hit sufficiency、actual repair synthesis、global minimal repair set、vanishing-to-closure、arbitrary atlas category/functoriality、true `H^1` / Cech quotient / coboundary quotient、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、UI correctness、whole-codebase quality は含まない。

## 候補種別

`cross-carrier residual repair-hitting theorem` / `obstruction-class-support` / `repair-necessity`

## 依拠

- Cycle 95: residual cut-locus transport induced by atlas map laws。
- Cycle 96: same-carrier residual cut repair-hitting theorem。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単に cross-carrier persistence を field として仮定するだけなら Cycle 96 の wrapper になる。
この候補では、unhit edge preservation、unhit residual-present preservation、unhit residual-free preservation という三 law から mapped residual cut preservation を証明する。
さらに Cycle 95 の unconditional preservation map が、この unhit repair transport map を任意の source-side hit predicates に対して誘導することを示す。

## 数学的興味

repair-hitting necessity が同一 carrier の artifact ではなく、finite carrier/schema change に沿って移送できることを示す。
これは true functorial cohomology ではないが、future semantic repair-gluing obstruction theorem が diagnostic schema refinement / carrier extension をまたいでも repair hit obligations を保持するための中核補題になる。

## GOAL への前進

Cycle 96 で得た `obstruction vanishing -> old cut hit` を、Cycle 95 の map-law transport と結合した。
これにより、repair necessity が presentation/carrier change に耐えることを Lean theorem として固定した。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は診断を別 schema へ表示し直せる。
しかし、それらは unhit edge/present/free preservation laws から、new canonical vanishing が source-side old cut hit を必要とすることを証明しない。
AAT 側では、schema change 後に residual obstruction が消えたと主張するためにも、source-side hit obligations を失わない条件を theorem として要求できる。

## SCORE 見込み

- `score_reason`: same-carrier repair-hitting necessity を cross-carrier map-law transport へ上げる。Cycle 95 と Cycle 96 の合成だが、unhit edge/present/free laws から mapped cut preservation を直接導き、selected extended witness まで持つため high support。
- `dullness_risk`: direct persistence field だけなら wrapper。三 preservation law から cut preservation を導き、Cycle 95 bridge と selected witness を入れて回避する。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualMappedRepairHitting.lean` で transport map、mapped nonzero/no-go、target vanishing forces source hit、Cycle 95 bridge、selected Option witness、theorem package を証明する。

## CS / SWE への帰結

architecture repair の証拠が schema migration や diagnostic carrier extension をまたぐ場合でも、old residual cut が unhit のまま new schema へ保存されるなら obstruction は残る。
new dashboard が green になるには、source-side の old cut hit bookkeeping を説明できなければならない。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualMappedRepairHitting.lean` に固定した。

- `ResidualCutRepairTransportMap`
- `unhit_oldResidualCut_maps_to_newCut`
- `unhit_oldResidualCut_maps_to_newCanonicalNonzero`
- `newCanonicalVanishes_forces_mappedOldResidualCutHit`
- `newCanonicalVanishes_forces_allMappedOldResidualCutsHit`
- `unhit_oldResidualCut_maps_to_newTransitionClosureObstruction`
- `unhit_oldResidualCut_maps_to_newTransitionCoherentDataObstruction`
- `residualCutInducingAtlasMap_to_repairTransportMap`
- `residualCutInducingAtlasMap_unhit_oldCut_maps_to_newCut`
- `residualCutInducingAtlasMap_newVanishes_forces_oldCutsHit`
- `selectedToExtendedNoHitRepairTransportMap`
- `selectedToExtendedNoHit_maps_frontierFlatCut`
- `selectedToExtendedNoHit_preserves_extendedCanonicalNonzero`
- `selectedToExtended_newVanishes_requires_frontierFlatCutHit`
- `selectedToExtendedNoHit_obstructs_extendedTransitionClosure`
- `selectedToExtendedNoHit_obstructs_extendedTransitionCoherentData`
- `semanticResidualMappedRepairHitting_package`

検証実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualMappedRepairHitting.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualMappedRepairHitting`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: generic cross-carrier repair-hitting theorem 群と Cycle 95 bridge は axiom-free。selected witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、finite old/new atlas skeletons with possibly different carriers、source-side supplied bookkeeping hit predicates、unhit edge/present/free preservation laws、new canonical residual cut class nonzero / vanishing、target transition closure / coherent data no-go に限定する。
unchecked: hit sufficiency、actual repair synthesis、global minimal repair set、vanishing-to-closure theorem、arbitrary atlas category/functoriality、true H1/Cech/coboundary quotient、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、whole-codebase quality。

## 審判メモ

- G1 A/B: cross-carrier repair-hitting transport を採択候補として推奨。direct persistence field だけでは弱いので、unhit edge/present/free preservation laws から mapped cut を導く shape に修正。
- G2 A: accept / base 90 / final 180。direct law-derived transport、Cycle 95 bridge、selected witness があれば 90 を支持。
- G2 B: accept / base 88、upper 180。wrapper risk を避けるには三 preservation law から cut preservation を導くことが必須。
- G2 revise 解決: `ResidualCutRepairTransportMap` は mapped cut persistence を field にせず、unhit edge/present/free preservation fields から `unhit_oldResidualCut_maps_to_newCut` を証明した。

## 追加 required fields

- `mathematical_interest`: repair-hitting necessity を finite carrier/schema change に沿って transport する。
- `goal_advancement`: same-carrier repair hit obligation を cross-carrier map-law obligation へ上げた。
- `planned_theorem_names`: `newCanonicalVanishes_forces_allMappedOldResidualCutsHit`, `residualCutInducingAtlasMap_to_repairTransportMap`, `semanticResidualMappedRepairHitting_package`
- `visible_projection`: source-side hit predicates、carrier/schema map、new canonical residual cut class。
- `protected_structure`: residual transition cut locus、unhit edge/present/free preservation、target nonzero obstruction、source-side hit necessity。
- `exactness_or_minimality_claim`: target vanishing forces source old cuts hit under unhit preservation。global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: schema change that preserves unhit residual cut data cannot erase source repair-hit obligations。
- `previous_cycle_delta`: Cycle 96 の same-carrier repair-hitting theorem を Cycle 95 map-law transport と結合した。
- `rival_stress_test`: rival は diagnostics を remap できても、source-side hit obligations が target vanishing に必要であることを証明しない。
- `genius_potential`: strong support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem の cross-carrier repair-hitting lemma。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: repair hit obligation が finite carrier/schema change に耐えることを固定する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-cut-repair-hitting.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-atlas-map-laws.md`
- planned report section: `Cycle 97: Cross-carrier residual cut repair-hitting transport`

## 進捗ログ

- 2026-06-23: Cycle 97 G1/G2 で cross-carrier residual cut repair-hitting transport を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualMappedRepairHitting.lean` に固定し、単体 `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
