---
name: repair-plan-creater
description: Create archsig-repair-plan/v0.5.6 artifacts for ArchSig SAGA descent runs with derived residuals.
---

# RepairPlan Creater

Use this skill to author `archsig-repair-plan/v0.5.6` artifacts for Stage 1
`ag.saga-descent` and Stage 2/3 supplied-data SAGA runs.

> Debt notice: the supplied slots this skill authors (faithfulness,
> trueSheafCertificate, gluingData, comparison, presentation, saga-grounding —
> the list is illustrative, not exhaustive) are existing debt against the
> input-triad rule (AGENTS.md 責務範囲). Do not cite this skill as precedent for
> adding new slots or fields; repayment is tracked by the supplied slot ledger's
> debt notice.

## Scope

- The plan declares only the finite complex (charts / overlaps / triples) and
  the faithfulness regime. The residual is derived by `analyze` from the
  observed cover sections and the law-surface witness bindings; the repair
  cochain is derived by `compare` from the head / repaired residual
  derivations; the coefficient is the selected MeasurementProfile declaration.
  Do not author residual, support, coefficient, semanticProjection, or
  primitives fields — they were retired at v0.5.5 / v0.5.6.
- Derivation prerequisites the plan relies on: every chart must belong to the
  profile-selected ArchMap cover, every overlap pair must be an observed
  restriction edge, every chart must carry exactly one observed
  `cech/sectionValue` atom, and every potentially mismatching edge must have a
  law-surface witness variable bound to it (`binding.edge`). Missing
  prerequisites make `analyze` fail closed with a named derivation fault.
- Prefer `complete-support`; use `faithfulness.mode = supplied` only when the
  supplied faithfulness, true-sheaf, gluing, and comparison evidence is
  explicit and independently checkable.
- Output is a repair-plan artifact that can be mechanically validated and then
  supplied to `archsig analyze`.

## Workflow

1. Read the selected ArchMap evidence and identify only explicit atom refs,
   contexts, overlap refs, and repair variables already present in the input
   evidence.
2. Emit a minimal `archsig-repair-plan/v0.5.6` document with:
   - The finite complex (charts / overlaps / triples) only; there is no
     primitives array.
   - `faithfulness.mode = complete-support` (or `none` / `supplied`; these are
     the only accepted mode values). Supplied mode references overlaps via
     `zeroOverlapRef`.
3. Validate first:
   - `archsig repair-plan --repair-plan <plan> --archmap <archmap> --out <report>`
4. Run the analyzer only after validation passes:
   - `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --law-surface <law-surface> --repair-plan <plan> --out-dir <run-dir>`
5. Read the resulting `archsig-measurement-packet.json` before summarizing any
   conclusion. Treat `boundaryStatements` as the source of silence and next
   required supply.

For a grounded Stage 3 run, add the validated supplied slots
`faithfulness`, `trueSheafCertificate`, `gluingData`, `comparison`, and
`grounding.kind = saga-grounding`. The law surface remains the source for
`skeleton`, `defectSources[].holdsCriterion`, and the quotient sheaf condition;
do not place those equation fields in the RepairPlan.

For `h1ComparisonData.kind = explicit`, author an evidence-shaped
`cochainMap` with `degreeZero`, `degreeOne`, and a `degreeTwo` object containing
`basisMap` and the explicit `zeroImage`. Each degree-zero/chart and
degree-one/overlap row carries a `variableMap`; each degree-two/triple row
carries its source and target triple refs. The validator recomputes inverse,
difference, zero, and differential conditions from these tables. Do not add
`degreeOneLeftInverse`, `degreeOneRightInverse`,
`differencePreserving`, `degreeTwoZeroPreserving`, or
`differentialCommutative` declaration booleans.

## Boundaries

- Do not author a supplied slot from a conclusion value. Comparison, gluing,
  true-sheaf, and faithfulness fields must be evidence-shaped and validated.
- Do not author lawSurfaceRef or Stage 2/3 law-equation fields in the RepairPlan.
- Do not place conclusion tokens such as
  `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` inside the repair-plan input.
- Do not attempt to author the residual. If the observed sections or the
  law-surface witness bindings required for derivation are missing, stop and
  report the missing observation or binding instead of weakening the plan.
