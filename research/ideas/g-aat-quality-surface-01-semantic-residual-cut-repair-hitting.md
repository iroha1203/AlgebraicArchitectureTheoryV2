---
status: picked
goal: G-aat-quality-surface-01
exploration_role: repair necessity / residual cut persistence / genius-support convergence
candidate_type: finite residual repair-hitting theorem / obstruction-class-support / repair-necessity
capability_category: semantic-obstruction / repair-necessity / finite-atlas-transition / obstruction-class-support / genius-support
expected_base_score: 88
expected_evidence_multiplier: 2.0
expected_final_score: 176
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can report residual-looking edges, but they do not prove that making a residual cut class vanish requires hitting the old cut at edge, source, or target loci under an explicit persistence law.
origin: cycle-96
tags: [quality-surface, semantic-repair, residual-cut, repair-hitting, obstruction-persistence, genius-support]
created: 2026-06-23
cycle: 96
lean: proved-in-research
planned_report_section: "Cycle 96: Residual cut obstruction repair-hitting theorem"
---

# Residual Cut Obstruction Repair-Hitting Theorem

## 主張

same-carrier の old/new finite semantic repair atlas skeleton に対して、repair が触った場所を `edgeHit`、`sourceHit`、`targetHit` として明示する。
これらの hit predicates は supplied bookkeeping predicates であり、実装差分から抽出された repair operation そのものではない。
old residual transition cut が edge/source/target のどこにも hit されていないなら new atlas にも residual cut として残る、という `UnhitResidualCutPersists` law を仮定する。
この仮定の下で、new canonical residual cut class が vanishes するなら、old residual cut は edge/source/target の少なくとも一箇所で hit されていなければならない。

反対に、unhit old residual cut が存在するなら、new canonical residual cut class は nonzero のまま残り、new transition closure と transition-coherent atlas data を阻む。

この主張は repair-hitting の必要条件である。
hit すれば repair が成功する、canonical vanishing が transition closure を含意する、actual repair synthesis がある、global minimal repair set がある、true `H^1` / Cech quotient / coboundary quotient がある、arbitrary atlas category がある、source extraction completeness や ArchMap correctness がある、とは主張しない。

## 候補種別

`finite residual repair-hitting theorem` / `obstruction-class-support` / `repair-necessity`

## 依拠

- Cycle 89: residual transition cut obstruction。
- Cycle 92: residual obstruction class modulo cut-noise。
- Cycle 95: residual cut-locus transport induced by atlas map laws。
- Cycle 1: support-local repair hitting theorem の設計パターン。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

Cycle 92-95 は residual obstruction class の existence、noise-invariance、gauge/carrier transport、map-law induction を固定した。
この候補は、その class を repair necessity へ戻す。
new canonical class を vanish させるためには、old cut が unhit のまま persistence law で残っていてはならない。
したがって repair は cut の active edge、residual-present source、residual-free target の少なくとも一箇所を触る必要がある。

`ResidualCutHit` は constructive に「三箇所すべてが unhit ではない」と定義する。
classical disjunction や repair success sufficiency は使わない。

## 数学的興味

semantic residual obstruction class を、単なる no-go certificate から repair hitting condition へ変換する。
これは true cohomology theorem ではないが、nonzero obstruction が repair に強制する局所条件を finite atlas 上で証明するため、future semantic repair-gluing obstruction theorem の repair 側の中核補題になる。

## GOAL への前進

open genius target に対して、obstruction class が「局所的に何を hit しなければ消えないか」を theorem として固定した。
transport/invariance tower から repair necessity へ一段進めた。

## ライバルに対する有効性

ADL、static analyzer、dashboard、AI summary は residual-looking edge や violation を表示できる。
しかし、それらは old/new atlas の persistence law の下で、new cut class vanishing が old residual cut hit を必要とすることを証明しない。
AAT 側では、repair が residual obstruction を消したと主張するために、edge/source/target のどこを hit したかを証明可能な条件として要求できる。

## SCORE 見込み

- `score_reason`: obstruction class を repair hitting necessity へ進める。Cycle 92-95 の invariant/transport tower より repair 側に踏み込む strong genius-support node。
- `dullness_risk`: persistence law を仮定しているため、repair success theorem ではない。selected witness と no-hit persistence、new nonzero obstruction、vanishing-forces-hit theorem を揃えて wrapper risk を下げる。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/QualitySurface/SemanticResidualCutRepairHitting.lean` で generic same-carrier theorem、selected frontier-to-flat witness、theorem package を証明する。

## CS / SWE への帰結

architecture repair が residual cut obstruction を解消したと主張するには、old cut の active edge、residual-present source、residual-free target のどこを変えたかを説明する必要がある。
単に new dashboard が green になったという observation だけでは、old cut が unhit で persistence law を満たす場合に nonzero obstruction が残る。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/QualitySurface/SemanticResidualCutRepairHitting.lean` に固定した。

- `ResidualCutHit`
- `residualCutHit_of_edgeHit`
- `residualCutHit_of_sourceHit`
- `residualCutHit_of_targetHit`
- `UnhitResidualCutPersists`
- `AllOldResidualCutsHit`
- `unhit_oldResidualCut_persists_newCut`
- `unhit_oldResidualCut_preserves_newCanonicalNonzero`
- `newCanonicalVanishes_forces_oldResidualCutHit`
- `newCanonicalVanishes_forces_allOldResidualCutsHit`
- `unhit_oldResidualCut_obstructs_newTransitionClosure`
- `unhit_oldResidualCut_obstructs_newTransitionCoherentData`
- `selectedFrontierFlatResidualCutPair`
- `selectedFrontierFlatResidualCutPair_isCut`
- `selectedNoHit_unhitResidualCutPersists`
- `selectedNoHit_preserves_canonicalNonzero`
- `selected_newCanonicalVanishes_requires_frontierFlatCutHit`
- `selectedNoHit_obstructs_transitionClosure`
- `selectedNoHit_obstructs_transitionCoherentData`
- `semanticResidualCutRepairHitting_package`

検証実績:

- `lake env lean research/lean/ResearchLean/QualitySurface/SemanticResidualCutRepairHitting.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualCutRepairHitting`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: generic repair-hitting theorem 群は axiom-free。selected witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、same-carrier old/new finite semantic repair atlas skeleton、supplied bookkeeping predicates としての explicit `edgeHit` / `sourceHit` / `targetHit`、supplied unhit persistence law、vanishing implies old residual cuts are hit、unhit old cut preserves new nonzero obstruction、new closure/data no-go に限定する。
unchecked: hit sufficiency、actual repair synthesis、global minimal repair set、vanishing-to-closure theorem、arbitrary atlas category/functoriality、true H1/Cech/coboundary quotient、source extraction completeness、ArchMap correctness、runtime repair synthesis、tooling runtime extraction、whole-codebase quality。

## 審判メモ

- G1 A/B/C/D: local-pass/global-fail taxonomy と pre-H1 adapter も候補に上がったが、repair necessity に踏み込む residual cut repair-hitting theorem が breakthrough pressure に最も合うと判断。
- G2 A/B/C: Candidate B を accept。Candidate A は wrapper risk が高く defer。base 86-90、expected final 176。genius unlock ではなく strong genius-support。
- G2 revise 解決: `ResidualCutHit` を constructive no-unhit 形式にし、persistence outside hit loci は仮定として明記し、hit sufficiency / repair synthesis は主張しない境界に固定した。

## 追加 required fields

- `mathematical_interest`: residual obstruction class を repair hitting necessity へ変換する。
- `goal_advancement`: transport/invariance tower から repair が必ず触るべき edge/source/target locus へ進めた。
- `planned_theorem_names`: `newCanonicalVanishes_forces_allOldResidualCutsHit`, `unhit_oldResidualCut_preserves_newCanonicalNonzero`, `semanticResidualCutRepairHitting_package`
- `visible_projection`: old/new finite atlas skeleton、repair-hit predicates、residual cut class vanishing。
- `protected_structure`: residual transition cut locus、canonical residual cut class、unhit persistence、transition closure/data obstruction。
- `exactness_or_minimality_claim`: vanishing forces hit under persistence。global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: repair report that does not hit an old persistent residual cut cannot justify disappearance of the residual cut obstruction。
- `previous_cycle_delta`: Cycle 95 の transport law induction の後、obstruction class を repair necessity theorem へ戻した。
- `rival_stress_test`: rival は residual-looking edges を list できても、vanishing-to-hit necessity を theorem として要求できない。
- `genius_potential`: strong support-cycle。1000 点 unlock ではなく、future finite semantic repair-gluing obstruction theorem の repair-hitting core lemma。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: nonzero residual obstruction が repair の hit locus を強制することを固定する。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-atlas-map-laws.md`
- `research/ideas/g-aat-quality-surface-01-semantic-residual-obstruction-class.md`
- planned report section: `Cycle 96: Residual cut obstruction repair-hitting theorem`

## 進捗ログ

- 2026-06-23: Cycle 96 G1/G2 で residual cut obstruction repair-hitting theorem を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualCutRepairHitting.lean` に固定し、単体 `lake env lean`、module build、`lake build ResearchLean`、axiom 監査が通った。
