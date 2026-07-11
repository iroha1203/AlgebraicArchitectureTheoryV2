---
status: picked
goal: G-aat-quality-surface-01
exploration_role: obstruction / preclass / vanishing-boundary / genius-support convergence
candidate_type: obstruction-preclass / vanishing-nonzero criterion / genius-support
capability_category: semantic-obstruction / finite-atlas-transition / obstruction-class-support / genius-support
expected_base_score: 80
expected_evidence_multiplier: 2.0
expected_final_score: 160
evidence_stage: proved-in-research
rival_advantage: Static analyzers, ADL tools, dashboards, and AI summaries can report failed edges or suspected violations, but they do not expose an order-independent residual obstruction support predicate with proved vanishing/nonzero criteria and closure/data obstruction theorems.
origin: cycle-91
tags: [quality-surface, semantic-repair, residual-cut, obstruction-preclass, vanishing, genius-support]
created: 2026-06-23
cycle: 91
lean: proved-in-research
planned_report_section: "Cycle 91: Semantic residual obstruction one-preclass"
---

# Semantic Residual Obstruction One-Preclass

## 主張

Cycle 89 の `ResidualTransitionCut` と Cycle 90 の scanner exactness を、finite semantic repair atlas 上の residual obstruction one-preclass へ持ち上げる。
preclass は edge family 上の support predicate であり、その support は `IsResidualTransitionCutPair` と exact に一致する。
preclass の vanishing は `ResidualTransitionCut` 不在と同値であり、nonzero support は residual transition closure と transition-coherent atlas data を阻む。
Cycle 90 の scanner は、この preclass の support/nonzero/vanishing を測る supplied edge-order 相対の measurement として接続される。

この主張は、Cech `H^1` class、coboundary quotient、canonical cohomology class、一般 sheaf gluing、`vanishing -> transition closure`、source extraction completeness、ArchMap correctness、runtime repair synthesis、whole-codebase quality を含まない。

## 候補種別

`obstruction-preclass` / `vanishing-nonzero criterion` / `genius-support`

## 依拠

- Cycle 89: finite semantic atlas residual transition cut certificate。
- Cycle 90: supplied-order residual transition cut scanner exactness。
- Cycle 77/80: local-pass / semantic residual-fail witness と finite semantic repair-gluing obstruction。
- open genius target: `Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases`。

## 非自明性

単なる `Nonempty (ResidualTransitionCut atlas)` の別名では低価値になる。
この候補では、edge family 上の support predicate、support exactness、vanishing/nonzero criteria、nonzero obstruction theorem、scanner measurement、selected nonzero witness を同じ package に置く。
Cycle 90 の supplied-order dependence を preclass の measurement 層へ退け、主対象を atlas edge family 上の order-independent support predicate にする。

## 数学的興味

semantic residual transition failure を、edge-local cut witness でも scanner result でもなく、degree-one obstruction preclass の support として読む。
これはまだ quotient cohomology ではないが、future finite obstruction class / vanishing-nonvanishing theorem / local-pass-global-fail taxonomy の前段になる。

## GOAL への前進

open genius target の `finite obstruction class` frontier に向け、cut certificate と scanner exactness を one-preclass language へ上げる。
`vanishes` / `nonzero` という finite obstruction vocabulary を Lean-proved にすることで、次 cycle の local-pass/global-fail taxonomy や H1-style vanishing criterion に接続する。

## ライバルに対する有効性

ADL や static analyzer は failed edge、rule violation、trace row を表示できる。
dashboard や AI summary は suspected failure を説明できる。
この候補の差分は、chosen semantic atom vocabulary と finite atlas skeleton に相対化された residual obstruction support predicateを theorem object として持ち、その vanishing/nonzero と closure/data obstruction を Lean で固定する点にある。

## SCORE 見込み

- `score_reason`: Cycle 89/90 の cut/scanner artifacts を、order-independent residual obstruction support predicate と vanishing/nonzero criterion へ上げる。open genius target への support node だが、cohomology class までは未到達。
- `dullness_risk`: support exactness だけなら name change になる。vanishing iff no cut、nonzero iff cut、nonzero obstruction、scanner measurement、selected nonzero witness を揃えて thin wrapper ではない形にする。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualObstructionPreclass.lean` で preclass structure、canonical preclass、vanishing/nonzero criteria、scanner measurement、selected nonzero package を証明する。

## CS / SWE への帰結

finite atlas diagnostic では、edge row や scanner hit を単なる UI result ではなく、residual obstruction one-preclass の support measurement として読む。
nonzero support は transition closure / transition-coherent data の no-go certificate であり、vanishing は no-cut boundary であって success certificate ではない。

## 証明・根拠の見込み

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/SemanticResidualObstructionPreclass.lean` に固定した。

- `ResidualObstructionOnePreclass`
- `residualObstructionOnePreclass`
- `ResidualObstructionOnePreclass.Vanishes`
- `ResidualObstructionOnePreclass.Nonzero`
- `SameResidualObstructionSupport`
- `residualObstructionOnePreclass_support_exact`
- `sameResidualObstructionSupport_preserves_vanishes`
- `sameResidualObstructionSupport_preserves_nonzero`
- `residualObstructionOnePreclass_vanishes_iff_no_cut`
- `residualObstructionOnePreclass_nonzero_iff_cut`
- `residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure`
- `residualObstructionOnePreclass_nonzero_obstructs_transitionCoherentData`
- `firstResidualTransitionCut?_some_preclassSupport`
- `firstResidualTransitionCut?_some_preclassNonzero`
- `firstResidualTransitionCut?_none_iff_preclassVanishes`
- `firstResidualTransitionCut?_some_obstructs_via_preclass`
- `selected_frontierFlat_residualObstructionOnePreclass_support`
- `selected_residualObstructionOnePreclass_nonzero`
- `selected_residualObstructionOnePreclass_obstructs_transitionClosure`
- `selected_residualObstructionOnePreclass_obstructs_transitionCoherentData`
- `semanticResidualObstructionPreclass_package`

G3 初期実績:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SemanticResidualObstructionPreclass.lean`: pass。
- `lake build ResearchLean.AG.QualitySurface.SemanticResidualObstructionPreclass`: pass。
- `lake build ResearchLean`: pass。
- `#print axioms`: `residualObstructionOnePreclass_vanishes_iff_no_cut`、`residualObstructionOnePreclass_nonzero_iff_cut`、`sameResidualObstructionSupport_preserves_vanishes`、`sameResidualObstructionSupport_preserves_nonzero` は axiom-free。scanner bridge は標準 `propext` のみ。selected nonzero witness と package は標準 `propext` / `Quot.sound` のみ。`sorryAx`、custom axiom、`Classical.choice`、`unsafe` はなし。
- G3 形式化品質監査: pass。preclass は H^1/cohomology/coboundary ではなく support predicate criterion に留まり、`vanishing -> closure` は主張しない。support exactness、same-support preservation、scanner measurement、selected concrete support witness は Lean とカードで一致している。
- G3.5 初回 revise 解決: candidate card に Lean 形式化品質監査要約と unresolved/unchecked boundary を追記した。aggregate import、declaration list、axiom summary は同期済み。

claim boundary は、finite semantic repair atlas、selected semantic atom vocabulary、residual transition cut predicate、canonical one-preclass support、supplied finite edge order measurement に限定する。
resolved_revisions: G2 wrapper risk は support exactness、same-support preservation、scanner measurement、selected concrete support witness を package theorem に入れて解決した。G3.5 metadata gap は本項目で解決した。
unchecked: H^1 cohomology class、coboundary quotient、vanishing-to-closure theorem、general sheaf gluing、source extraction completeness、ArchMap correctness、runtime repair synthesis、whole-codebase quality、tooling runtime extraction。

## 審判メモ

- G1 A: accept。order-independent edge-supported obstruction preclass として採択。ただし H^1 class / coboundary quotient は除外。
- G1 B: local-pass/global-fail taxonomy は価値ありだが、Cycle 91 本体ではなく次候補または package 接続に回す。
- G1 C: finite residual 1-preclass vanishing/nonvanishing criterion を accept in narrowed form。一般 cohomology ではなく preclass criterion に限定。
- G1 D: finite residual obstruction 1-preclass を最有力候補として推奨。scanner-derived、prefix-clear、closure/data obstruction、complete-order vanishing boundary を揃える条件。
- G2 A: accept / base 60 / genius no。claim boundary は守れているが wrapper risk が高いと判定。support exactness、vanishing/nonzero criterion、scanner bridge、selected nonzero を package に分けることを要求。
- G2 B: accept / base 82 / genius support。one-preclass を supplied-order 非依存の protected support predicate とし、scanner を measurement projection として位置づける条件。
- G2 C: accept / base 84 / genius no。project value は高いが H^1/coboundary/global gluing は不可。support predicate、vanishing/nonzero、scanner measurement theorem、selected nonzero witness、complete edge family assumption が必要。
- G2 D: revise / base 58 / genius no。Lean 実装は通しやすいが wrapper risk が高い。`Vanishes` / `Nonzero` と scanner bridge、selected package を明示する条件。
- G2 revise 解決: package theorem に canonical support exactness、same-support preservation for vanishing/nonzero、scanner `some -> support/nonzero`、selected concrete support witness を追加し、単なる `Nonempty ResidualTransitionCut` の名前替えに見えない interface にした。

## 追加 required fields

- `mathematical_interest`: residual transition cut support を degree-one obstruction preclass として読む。
- `goal_advancement`: scanner exactness から finite obstruction support / vanishing vocabulary へ上げる。
- `planned_theorem_names`: `residualObstructionOnePreclass_vanishes_iff_no_cut`, `residualObstructionOnePreclass_nonzero_obstructs_atlasTransitionClosure`, `semanticResidualObstructionPreclass_package`
- `visible_projection`: edge row / scanner hit / dashboard-like diagnostic。
- `protected_structure`: residual-present source、residual-free target、active edge support predicate、one-preclass vanishing/nonzero、transition-coherent data obstruction。
- `exactness_or_minimality_claim`: preclass support exactness and vanishing/nonzero criterion。minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: visible edge diagnostics do not by themselves expose the residual obstruction support predicate or its nonzero no-go theorem。
- `previous_cycle_delta`: Cycle 90 の supplied-order scanner result を preclass support measurement として吸収し、主対象を edge-family support predicate に上げる。
- `rival_stress_test`: rival は edge result を出せても、vanishing/nonzero criterion と closure/data obstruction theorem を Lean artifact として保持しない。
- `genius_potential`: support-cycle。1000 点 unlock ではなく、future finite obstruction class / coboundary-like equivalence / H1-style criterion への support node。
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: residual cut/scanner artifacts を finite obstruction-class language へ上げる preclass layer。

## 関連

- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-theorem.md`
- `research/ideas/g-aat-quality-surface-01-residual-transition-cut-scanner.md`
- `research/ideas/g-aat-quality-surface-01-finite-semantic-repair-cocycle-witness.md`
- planned report section: `Cycle 91: Semantic residual obstruction one-preclass`

## 進捗ログ

- 2026-06-23: Cycle 91 G1 で finite residual obstruction preclass / vanishing-nonzero criterion を採択。
- 2026-06-23: Lean 証拠を `SemanticResidualObstructionPreclass.lean` に固定し、単体 `lake env lean` が通った。
