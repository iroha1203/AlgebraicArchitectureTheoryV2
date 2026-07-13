# LawPolicy Question Bank

Ask only what is needed to select evaluator manifests.

## Scope

- Which subsystem or repository slice should the policy cover?
- Should the policy be advisory review, strict CI gate, or exploratory diagnosis?
- Which source id prefixes should be in `scope`?

## Policy Selection

- Which current registry evaluator is supported by the repository evidence?
- Are there project-specific policies that need a registry evaluator before they can be selected?
- Is this an AG measurement run? If yes, which registered evaluator(s) should be
  selected: `ag.cech-obstruction`, `ag.coherence-obstruction`,
  `ag.restriction-compatibility`, `ag.section-factorization`,
  `ag.boundary-residue`, `ag.square-free-repair`, `ag.law-conflict-tor`,
  `ag.sheaf-laplacian`, `ag.period-stokes`, `ag.period-stokes-audit`,
  `ag.support-transfer`, or `ag.saga-descent`?

## AG MeasurementProfile

- Which ArchMap v2 cover id should the profile measure?
- Should `siteRef` be `archmap:/contexts` or a narrower context ref?
- Which coefficient should be selected, such as `F2`, `Q`, or `R`?
- Which EffCoeff procedure should be selected, usually `finite-linear-algebra@1`?
- Which witness variables correspond to the selected law family?
- Which resolution selector should be used, such as `taylor@1`?
- Which domain and predicate selectors should be used? Algebraic structural
  fixtures commonly use `finite-poset-site`, `rank-zero@1`,
  `rank-positive@1`, `finite-certificate@1`, and
  `five-valued-structural-verdict@1`; analytic fixtures such as Laplacian,
  period, and transfer use `R`, `analytic-zero@1`,
  `analytic-positive@1`, and `analytic-reading@1`.

## Law surface and policy bundle

- Which `law-equation-surface/v0.5.1` id supplies the selected laws and witness
  variables?
- Does every `policies[].law` or `policies[].lawPair[]` resolve to that supplied
  surface, with the evaluator and binding pair accepted by the registry
  manifest?
- If `ag.law-conflict-tor` is selected, are exactly two distinct law ids
  declared in `policies[].lawPair`?
- Should the three validated artifacts be fixed in an
  `archsig-policy-bundle/v0.5.1` for this run?
- Is the bundle output kept beside the run so `componentFingerprints` can be
  checked during reproduction?

## Basis

- Which docs, ADRs, standards, or direct user decisions justify the policy?
- Should the basis be `policy-basis:layering` or a future registry basis ref?

## Severity

- Should a measured violation be review-only, warning, or error?

## Out Of Scope

Do not ask users to hand-author:

- witness predicates
- signature axes
- coverage rules
- exactness assumptions
- distance formulas
- spectrum or homotopy profiles
- U-adequacy / Leray / theorem-hypothesis proofs

If those are needed and no current registry evaluator matches the evidence, the
evaluator registry must grow first.
