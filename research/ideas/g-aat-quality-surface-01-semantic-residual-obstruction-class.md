---
status: picked
goal: G-aat-quality-surface-01
exploration_role: obstruction-class / cut-noise quotient-style reading / genius-support convergence
candidate_type: obstruction-class-support / cut-locus equivalence / projection-noise
capability_category: semantic-obstruction / finite-atlas-transition / obstruction-class-support / projection-nonfaithfulness / genius-support
expected_base_score: 82
expected_evidence_multiplier: 2.0
expected_final_score: 164
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can report raw diagnostic support, but they do not distinguish off-cut raw support noise from residual cut-locus obstruction class data with Lean-proved invariance and no-go theorems.
origin: cycle-92
tags: [quality-surface, semantic-repair, residual-cut, obstruction-class, cut-noise, genius-support]
created: 2026-06-23
cycle: 92
lean: proved-in-research
planned_report_section: "Cycle 92: Semantic residual obstruction class modulo cut-noise"
---

# Semantic Residual Obstruction Class Modulo Cut-Noise

## 主張

Cycle 91 の `ResidualObstructionOnePreclass` を、finite semantic repair atlas 上の raw cochain と cut-locus class reading に分ける。
`ResidualCutCochain` は raw support を持ち、その raw support には residual transition cut ではない pair への diagnostic noise が混じりうる。
`CutNoiseEquivalent` は `IsResidualTransitionCutPair` 上だけで support を比較し、off-cut noise を class reading から消す。

この class reading で、cut-locus 相対の `CutVanishes` / `CutNonzero` を定義し、canonical cochain の vanishing は `ResidualTransitionCut` 不在と同値、nonzero は `ResidualTransitionCut` 存在と同値であることを Lean で固定する。
さらに、selected frontier-to-flat atlas では `(flat, repairFrontier)` に余計な raw support を持つ noisy representative が canonical raw support と異なる一方、cut-locus class としては canonical と同値であり、nonzero class が residual transition closure と transition-coherent atlas data を阻む。

この主張は、Cech `H^1` class、coboundary quotient、true cohomology quotient、一般 sheaf gluing、`class vanishes -> transition closure`、global minimal representative、source extraction completeness、ArchMap correctness、runtime repair synthesis、whole-codebase quality を含まない。

## 候補種別

`obstruction-class-support` / `cut-locus equivalence` / `projection-noise`

## 依拠

- Cycle 89: finite semantic atlas residual transition cut certificate。
- Cycle 90: supplied-order residual transition cut scanner exactness。
- Cycle 91: residual obstruction one-preclass、vanishing/nonzero criterion、scanner measurement。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単なる `SameResidualObstructionSupport` の rename なら低価値である。
この候補では、raw support と cut-locus class support を明示的に分離し、selected noisy representative が canonical raw support と実際に異なることを Lean で示す。
そのうえで、off-cut raw noise があっても residual cut class、cut-locus vanishing/nonzero、transition obstruction は変わらないことを theorem package に置く。

## 数学的興味

semantic residual transition failure を、edge-local cut witness や preclass support predicate から、noise-invariant finite obstruction class reading へ一段上げる。
これはまだ Cech cohomology ではないが、H1-style obstruction theorem の手前で必要な「representative と class の分離」を Lean artifact として固定する。

## GOAL への前進

open genius target の `finite obstruction class` frontier に向け、preclass support から cut-noise invariant class reading へ進める。
dashboard / scanner / AI summary が持ちうる raw diagnostic noise を切り落とし、AAT 側が守るべき residual cut-locus obstruction data を theorem object として分離した。

## ライバルに対する有効性

ADL、static analyzer、conformance dashboard、AI summary は raw edge diagnostics や suspected failure を表示できる。
この候補の差分は、raw support の余計な off-cut entry を許しながら、それを residual cut class から消す同値と、その同値が cut-locus vanishing/nonzero を保存することを Lean で証明する点にある。

## SCORE 見込み

- `score_reason`: Cycle 91 の preclass を、off-cut raw support noise を殺す finite class reading へ上げる。open genius target への support node だが、true H1 にはまだ到達していない。
- `dullness_risk`: noisy representative の raw support difference がなければ wrapper になる。selected noisy representative、cut-locus predicates、equivalence preservation、canonical iff、scanner bridge、closure/data obstruction を揃えて wrapper risk を下げる。
- `proof_or_evidence_plan`: `Formal/AG/Research/QualitySurface/SemanticResidualObstructionClass.lean` で raw cochain、cut-noise equivalence、canonical criteria、scanner bridge、selected noisy representative、theorem package を証明する。

## CS / SWE への帰結

finite atlas diagnostic では、UI row や scanner output の raw support はそのまま obstruction class ではない。
off-cut diagnostic noise を含む representation から residual cut-locus support だけを class data として読むことで、green-looking local surface や noisy dashboard representation と、AAT の nonzero obstruction theorem を分離できる。

## 証明・根拠

Lean 証拠は `Formal/AG/Research/QualitySurface/SemanticResidualObstructionClass.lean` に固定した。

- `ResidualCutCochain`
- `canonicalResidualCutCochain`
- `CutNoiseEquivalent`
- `ResidualCutCochain.CutVanishes`
- `ResidualCutCochain.CutNonzero`
- `cutNoiseEquivalent_refl`
- `cutNoiseEquivalent_symm`
- `cutNoiseEquivalent_trans`
- `cutNoiseEquivalent_preserves_cutVanishes`
- `cutNoiseEquivalent_preserves_cutNonzero`
- `canonicalResidualCutCochain_support_exact`
- `canonicalResidualCutClass_vanishes_iff_no_cut`
- `canonicalResidualCutClass_nonzero_iff_cut`
- `residualCutClass_nonzero_obstructs_atlasTransitionClosure`
- `residualCutClass_nonzero_obstructs_transitionCoherentData`
- `firstResidualTransitionCut?_some_cutClassNonzero`
- `firstResidualTransitionCut?_none_iff_canonicalCutClassVanishes`
- `firstResidualTransitionCut?_some_obstructs_via_cutClass`
- `selected_flatFrontier_not_residualCutPair`
- `selectedBoundaryNoisyResidualCutCochain`
- `selectedBoundaryNoisy_rawSupport_differs_from_canonical`
- `selectedBoundaryNoisy_cutNoiseEquivalent_canonical`
- `selected_canonicalResidualCutClass_nonzero`
- `selectedBoundaryNoisy_residualCutClass_nonzero`
- `selectedBoundaryNoisy_residualCutClass_obstructs_transitionClosure`
- `selectedBoundaryNoisy_residualCutClass_obstructs_transitionCoherentData`
- `semanticResidualObstructionClass_package`

検証実績:

- `lake env lean Formal/AG/Research/QualitySurface/SemanticResidualObstructionClass.lean`: pass。
- `lake build Formal.AG.Research.QualitySurface.SemanticResidualObstructionClass`: pass。
- `lake build FormalAGResearch`: pass。
- `#print axioms`: `cutNoiseEquivalent_preserves_cutVanishes`、`cutNoiseEquivalent_preserves_cutNonzero`、`canonicalResidualCutClass_vanishes_iff_no_cut`、`canonicalResidualCutClass_nonzero_iff_cut` は axiom-free。scanner bridge と selected noisy equivalence は標準 `propext`。selected noisy nonzero と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。

claim boundary は、finite semantic repair atlas、selected semantic atom vocabulary、residual transition cut predicate、cut-locus class equivalence、supplied finite edge-order scanner measurement に限定する。
unchecked: true H1 cohomology class、Cech quotient、coboundary quotient、vanishing-to-closure theorem、general sheaf gluing、source extraction completeness、ArchMap correctness、runtime repair synthesis、whole-codebase quality、tooling runtime extraction。

## 審判メモ

- G1 A: accept in narrowed form。preclass から finite obstruction class へ上げる候補として推奨。ただし H1 / coboundary quotient は除外。
- G1 B: mismatch minimality を推奨。Cycle 92 本体ではなく、次候補または rival separation に回す。
- G1 C: pre-H1 boundary criterion を推奨。H1 本体ではなく境界・保存・非零 obstruction を固定する方針。
- G1 D: local-pass/global-fail taxonomy を推奨。Cycle 92 では class reading を優先し、taxonomy は次 frontier とする。
- G2 A: accept / base 80。boundary-noisy representative が必須。なければ wrapper。
- G2 B: revise / base 78-84。`Vanishes` / `Nonzero` は raw support ではなく cut-locus 相対に定義すること。
- G2 C: revise / base 82。raw support vanishing preservation は偽なので、class-level predicates に限定すること。
- G2 D: revise / base 82。selected noisy witness は `(flat, repairFrontier)` の off-cut raw support difference と class equivalence を両方持つこと。
- G2 revise 解決: `CutVanishes` / `CutNonzero` を cut-locus 相対に定義し、selected noisy representative の raw support difference と `CutNoiseEquivalent` を Lean package に入れた。

## 追加 required fields

- `mathematical_interest`: residual transition cut support を raw representative と cut-locus class reading に分離する。
- `goal_advancement`: preclass support predicate から noise-invariant finite obstruction class reading へ上げる。
- `planned_theorem_names`: `cutNoiseEquivalent_preserves_cutNonzero`, `canonicalResidualCutClass_nonzero_iff_cut`, `selectedBoundaryNoisy_cutNoiseEquivalent_canonical`, `semanticResidualObstructionClass_package`
- `visible_projection`: raw diagnostic support / scanner output / dashboard-like edge row。
- `protected_structure`: residual cut locus、cut-locus vanishing/nonzero、off-cut raw support noise、transition-coherent data obstruction。
- `exactness_or_minimality_claim`: cut-noise equivalence preserves cut-locus vanishing/nonzero; canonical cut class is exact for residual cut existence。global minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: raw diagnostic support may differ while residual cut class is unchanged。
- `previous_cycle_delta`: Cycle 91 の preclass support exactnessを、off-cut raw noise を消す class reading へ拡張した。
- `rival_stress_test`: rival は raw diagnostic row を出せても、off-cut noise と obstruction class support の同値不変性を theorem artifact として保持しない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、future finite H1-style obstruction theorem への support node。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: representative/class 分離を導入し、obstruction-class frontier に必要な finite cut-locus equivalence layer を置く。

## 関連

- `research/ideas/g-aat-quality-surface-01-semantic-residual-obstruction-preclass.md`
- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-scanner.md`
- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-theorem.md`
- planned report section: `Cycle 92: Semantic residual obstruction class modulo cut-noise`

## 進捗ログ

- 2026-06-23: Cycle 92 G1/G2 で cut-noise invariant residual obstruction class reading を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualObstructionClass.lean` に固定し、単体 `lake env lean`、module build、`lake build FormalAGResearch`、axiom 監査が通った。
