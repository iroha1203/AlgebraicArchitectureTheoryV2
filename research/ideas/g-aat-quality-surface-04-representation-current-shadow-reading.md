---
goal: G-aat-quality-surface-04
cycle: 36
candidate: Representation Current-Shadow Reading Faithfulness Criterion
candidate_type: target-support
evidence_stage: proved-in-research
score_status: T4 confirmed as support-node
base_score: 38
evidence_multiplier: 2.0
penalty: 0
final_score: 76
target_progress: support-node
---

# Representation Current-Shadow Reading Faithfulness Criterion

Cycle 36 exposes the semantic-reading premise behind the Cycle 35
no-separation boundary.

The new Lean file
`Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryRepresentationCurrentShadowReading.lean`
proves that, for a visible finite-query representation, faithfulness of the
canonical current-shadow reading for the representing package is exactly the
represented observation's current-shadow extensionality and raw
current-shadow factorization criteria.

It also proves that this faithfulness rules out separated post-fibers without a
decidable-output assumption.

## Lean Surface

- `representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_shadowExtensional`
- `representedFiniteTraceQueryObservation_shadowExtensional_of_currentShadowSemanticReading_faithful`
- `representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_shadowExtensional`
- `representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor`
- `representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowSemanticReading_faithful`
- `no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful`
- `not_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryPostFiberSeparation`
- `not_boolFirstRepresentedFiniteTraceQueryObservation_currentShadowSemanticReadingFaithful`

## Boundary

This is not a target theorem proof.  It does not derive canonical
current-shadow reading faithfulness from arbitrary semantic soundness or
representation adequacy.  Faithfulness remains a visible theorem argument and
is precisely the next obligation that a semantic-soundness extraction theorem
must discharge.

Remaining blockers:

- non-circular extraction of canonical current-shadow reading faithfulness from
  semantic soundness / representation adequacy;
- arbitrary semantic observation factorization;
- T6 `$math-lean-review`.
