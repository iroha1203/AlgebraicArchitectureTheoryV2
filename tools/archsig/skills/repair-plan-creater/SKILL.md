---
name: repair-plan-creater
description: Create archsig-repair-plan/v0.5.7 selected-complex artifacts for ArchSig SAGA descent runs.
---

# RepairPlan Creater

Use this skill to author `archsig-repair-plan/v0.5.7` artifacts for
`ag.saga-descent` runs. A v0.5.7 plan declares only the selected finite
complex; every SAGA supplied slot (residual, support, coefficient,
semanticProjection, primitives, faithfulness, trueSheafCertificate, gluingData,
comparison, grounding) has been retired (#3820–#3822). Do not cite this skill
as precedent for adding new slots or fields; the supplied slot ledger's debt
notice records the retirements.

## Scope

- The plan declares only the selected complex: `charts`, `overlaps`, optional
  `tripleOverlaps`, and the `enumerationComplete` author assertion. The
  residual is derived by `analyze` from the observed cover sections and the
  law-surface witness bindings; the repair reading between two runs is derived
  by `compare` from the head / repaired residual derivations
  (`residualClassAgreement`); the coefficient is the selected
  MeasurementProfile declaration.
- Derivation prerequisites the plan relies on: every chart must belong to the
  profile-selected ArchMap cover, every overlap pair must be an observed
  restriction edge, every chart must carry observed `cech/sectionValue`
  atoms, and every potentially mismatching edge must have a law-surface
  witness variable bound to it (`binding.edge`). Missing prerequisites make
  `analyze` fail closed with a named derivation fault.
- Output is a repair-plan artifact that can be mechanically validated and then
  supplied to `archsig analyze`.

## Workflow

1. Read the selected ArchMap evidence and identify the observed contexts and
   restriction edges of the profile-selected cover.
2. Emit a minimal `archsig-repair-plan/v0.5.7` document with `schema`, `id`,
   and `complex` only.
3. Validate first:
   - `archsig repair-plan --repair-plan <plan> --archmap <archmap> --out <report>`
4. Run the analyzer only after validation passes:
   - `archsig analyze --archmap <archmap> --law-policy <policy> --measurement-profile <profile> --law-surface <law-surface> --repair-plan <plan> --out-dir <run-dir>`
5. Read the resulting `archsig-measurement-packet.json` before summarizing any
   conclusion. Treat `boundaryStatements` as the source of silence and next
   required supply.

## Boundaries

- Do not author residual values, certificates, comparison data, or any other
  conclusion-shaped input; the retired slots fail loudly by field name.
- Do not author lawSurfaceRef or law-equation fields in the RepairPlan; the
  law surface owns `skeleton`, `defectSources[].holdsCriterion`, witness
  bindings, and the quotient sheaf condition.
- Do not place conclusion tokens such as
  `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` inside the repair-plan input.
