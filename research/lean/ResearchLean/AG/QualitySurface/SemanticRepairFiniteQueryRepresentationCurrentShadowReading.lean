import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationNoSeparation

/-!
Cycle 36 evidence for `G-aat-quality-surface-04`.

Cycle 35 made no-separation the exact obstruction boundary for represented
finite-query observations.  This file exposes the corresponding semantic
reading premise: faithfulness of the canonical current-shadow reading for the
representing package is exactly the represented observation's current-shadow
extensionality and raw factorization criteria, and it rules out separated
post-fibers.

This is still a support node.  It does not prove that arbitrary semantic
soundness supplies current-shadow reading faithfulness; it records that
faithfulness as the next visible theorem-level obligation.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationCurrentShadowReading

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationPostInvariant
open SemanticRepairFiniteQueryRepresentationNoSeparation

universe u v w x y z

/-! ## Current-shadow reading faithfulness as represented extensionality -/

/--
For a visible representation, faithfulness of the canonical current-shadow
reading for the representing package is exactly canonical-shadow extensionality
of the represented observation.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post ↔
      ShadowExtensionalTowerObservation observe := by
  exact
    (currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) repr.package.query repr.package.post).trans
      (representedFiniteTraceQueryObservation_shadowExtensional_iff_postInvariant
        (Atom := Atom) repr).symm

/--
Canonical current-shadow reading faithfulness supplies extensionality for the
represented observation.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        repr.package.query repr.package.post) :
    ShadowExtensionalTowerObservation observe := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_shadowExtensional
      (Atom := Atom) repr).1 hfaithful

/--
Represented-observation extensionality is enough to make the representing
post-map faithful for the canonical current-shadow reading.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext :
      ShadowExtensionalTowerObservation observe) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_shadowExtensional
      (Atom := Atom) repr).2 hext

/--
For a visible representation, canonical current-shadow reading faithfulness is
exactly raw current-shadow factorization of the represented observation.
-/
theorem representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post ↔
      ∃ factor : FiniteTowerLayerShadow -> Out,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    (currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) repr.package.query repr.package.post).trans
      (representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
        (Atom := Atom) repr).symm

/--
Canonical current-shadow reading faithfulness supplies raw current-shadow
factorization for a represented finite-query observation.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_of_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        repr.package.query repr.package.post) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_currentShadowFactor
      (Atom := Atom) repr).1 hfaithful

/-! ## Faithfulness rules out represented post-fiber separation -/

/--
Canonical current-shadow reading faithfulness rules out separated post-fibers in
the representing package, without a decidable-output assumption.
-/
theorem no_queryPostFiberSeparation_of_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        repr.package.query repr.package.post) :
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    no_queryPostFiberSeparation_of_currentShadowSemanticReading_faithfulToQueryPost
      (Atom := Atom) hfaithful

/--
A separated post-fiber blocks canonical current-shadow reading faithfulness for
the representing package.
-/
theorem not_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post) :
    ¬ SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      repr.package.query repr.package.post := by
  exact
    not_currentShadowSemanticReading_faithfulToQueryPost_of_queryPostFiberSeparation
      (Atom := Atom) hsep

/-! ## Concrete obstruction compatibility -/

/--
The represented Bool first-reading observation is not faithful for the canonical
current-shadow reading.
-/
theorem not_boolFirstRepresentedFiniteTraceQueryObservation_currentShadowSemanticReadingFaithful :
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).query
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).post := by
  exact
    not_representedFiniteTraceQueryObservation_currentShadowSemanticReading_faithful_of_queryPostFiberSeparation
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservationRepresentation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost)
      boolFirstRepresentedFiniteTraceQueryObservation_queryPostFiberSeparation

end SemanticRepairFiniteQueryRepresentationCurrentShadowReading
end QualitySurface
end ResearchLean.AG
