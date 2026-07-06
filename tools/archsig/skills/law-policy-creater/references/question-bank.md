# LawPolicy Question Bank

Ask only what is needed to select evaluator manifests.

## Scope

- Which subsystem or repository slice should the policy cover?
- Should the policy be advisory review, strict CI gate, or exploratory diagnosis?
- Which source id prefixes should be in `scope`?

## Policy Selection

- Is domain-to-infrastructure dependency forbidden? If yes, use `domain.no-direct-infra-dependency`.
- Are there project-specific policies that need a registry evaluator before they can be selected?
- Is this an AG measurement run? If yes, which AG evaluator(s) should be
  selected: Čech obstruction, square-free repair, law-conflict Tor, sheaf
  Laplacian, period/Stokes, support transfer, or a newer registry evaluator?

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

If those are needed, the evaluator registry must grow first.
