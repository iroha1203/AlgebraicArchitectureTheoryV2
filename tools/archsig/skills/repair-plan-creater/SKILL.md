---
name: repair-plan-creater
description: Create repair-plan/v0.5.0 artifacts for ArchSig PRD-4 complete-support SAGA descent runs.
---

# RepairPlan Creater

Use this skill to author `repair-plan/v0.5.0` artifacts for Stage 1
`ag.saga-descent` runs in complete-support mode.

## Scope

- Mode is `complete-support` only.
- Inputs are existing ArchMap evidence, LawPolicy basis refs, and a selected
  MeasurementProfile.
- Output is a repair-plan artifact that can be mechanically validated and then
  supplied to `archsig analyze`.

## Workflow

1. Read the selected ArchMap evidence and identify only explicit atom refs,
   contexts, overlap refs, and repair variables already present in the input
   evidence.
2. Emit a minimal `repair-plan/v0.5.0` document with:
   - `support.kind = complete` for every primitive.
   - Complete residual support variables for the chosen finite complex.
   - `faithfulness.mode = complete-support` when the complete-support alias
     witness surface is intentionally supplied by the plan.
3. Validate first:
   - `archsig repair-plan --repair-plan <plan> --archmap <archmap> --out <report>`
4. Run the analyzer only after validation passes:
   - `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --repair-plan <plan> --out-dir <run-dir>`
5. Read the resulting `archsig-measurement-packet.json` before summarizing any
   conclusion. Treat `boundaryStatements` as the source of silence and next
   required supply.

## Boundaries

- Do not author `faithfulness.mode = supplied`.
- Do not author comparison, grounding, true-sheaf, gluingData, lawSurfaceRef, or
  Stage 2 law-equation surfaces.
- Do not place conclusion tokens such as
  `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` inside the repair-plan input.
- Do not infer missing support. If complete support cannot be read from
  evidence, stop and report the missing supply instead of weakening the plan.
