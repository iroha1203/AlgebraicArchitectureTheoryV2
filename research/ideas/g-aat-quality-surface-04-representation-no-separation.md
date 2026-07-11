---
goal: G-aat-quality-surface-04
cycle: 35
candidate: Representation No-Separation Exact Criterion
candidate_type: target-support
evidence_stage: proved-in-research
score_status: T4 pending
base_score: 39
evidence_multiplier: 2.0
penalty: 0
final_score: 78
target_progress: support-node
---

# Representation No-Separation Exact Criterion

Cycle 35 connects the Cycle 34 representation boundary to the obstruction route
from Cycle 31-33.

The new Lean file
`research/lean/ResearchLean/AG/QualitySurface/SemanticRepairFiniteQueryRepresentationNoSeparation.lean`
proves that, for a visible finite-query representation, a separated post-fiber
blocks:

- canonical-shadow extensionality of the represented observation;
- raw current-shadow factorization of the represented observation;
- semantic-reading adequacy for the representing package.

It also proves the decidable exact criterion:

```text
represented observation extensional
  iff no separated post-fiber
  iff raw current-shadow factorization
  iff semantic-reading adequacy existence
```

This is a support node, not a completion claim.  It does not show that semantic
soundness or representation adequacy rules out separated post-fibers.  Instead,
it fixes no-separation as the exact obligation that a future extraction theorem
must discharge before the represented observation can be treated as
current-shadow extensional.

## Lean Surface

- `not_representedFiniteTraceQueryObservation_shadowExtensional_of_queryPostFiberSeparation`
- `no_representedFiniteTraceQueryObservation_currentShadowFactor_of_queryPostFiberSeparation`
- `no_representedFiniteTraceQueryObservation_semanticReadingAdequacy_of_queryPostFiberSeparation`
- `representedFiniteTraceQueryObservation_shadowExtensional_iff_no_queryPostFiberSeparation`
- `representedFiniteTraceQueryObservation_currentShadowFactor_iff_no_queryPostFiberSeparation`
- `representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_no_queryPostFiberSeparation`
- `representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation`
- `representedFiniteTraceQueryObservation_currentShadowFactor_of_no_queryPostFiberSeparation`
- `boolFirstRepresentedFiniteTraceQueryObservation_queryPostFiberSeparation`
- `not_boolFirstRepresentedFiniteTraceQueryObservation_no_queryPostFiberSeparation`

## Boundary

The `[DecidableEq Out]` assumption is used only for the no-separation to
post-invariance exactness direction.  The obstruction direction from an
explicit separated post-fiber to failure of represented extensionality does not
require decidable output equality.

Remaining blockers:

- non-circular extraction of no-separation from semantic soundness /
  representation adequacy;
- arbitrary semantic observation factorization;
- T6 `$math-lean-review`.
