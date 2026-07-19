---
name: repair-plan-creater
description: Create archsig-repair-plan/v0.5.4 artifacts for ArchSig complete-support SAGA descent runs.
---

# RepairPlan Creater

Use this skill to author `archsig-repair-plan/v0.5.4` artifacts for Stage 1
`ag.saga-descent` and Stage 2/3 supplied-data SAGA runs.

## Scope

- Prefer `complete-support`; use `faithfulness.mode = supplied` only when the
  supplied faithfulness, coefficient, true-sheaf, gluing, and comparison
  evidence is explicit and independently checkable.
- Inputs are existing ArchMap evidence, LawPolicy basis refs, and a selected
  MeasurementProfile.
- Output is a repair-plan artifact that can be mechanically validated and then
  supplied to `archsig analyze`.

## Workflow

1. Read the selected ArchMap evidence and identify only explicit atom refs,
   contexts, overlap refs, and repair variables already present in the input
   evidence.
2. Emit a minimal `archsig-repair-plan/v0.5.4` document with:
   - `support.kind = complete` for every primitive.
   - Complete residual support variables for the chosen finite complex.
   - `faithfulness.mode = complete-support` when the complete-support alias
     witness surface is intentionally supplied by the plan.
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
- Do not infer missing support. If complete support cannot be read from
  evidence, stop and report the missing supply instead of weakening the plan.
