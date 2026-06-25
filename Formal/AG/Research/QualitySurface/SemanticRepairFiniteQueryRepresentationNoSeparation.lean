import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationPostInvariant

/-!
Cycle 35 evidence for `G-aat-quality-surface-04`.

Cycle 34 tied represented finite-query observation extensionality to the exact
post-fiber invariance criterion for the representing package.  This file links
that representation boundary to the obstruction side: a separated post-fiber
blocks represented extensionality, current-shadow factorization, and semantic
reading adequacy; conversely, under decidable output equality, absence of such a
separation is exactly the represented-observation extensionality criterion.

This is still a support node.  It does not prove that semantic soundness
excludes separated post-fibers; it records the exact no-separation obligation
that a future extraction theorem must discharge.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationNoSeparation

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

universe u v w x y z

/-! ## Separation blocks represented extensionality -/

/--
A separated post-fiber in the representing package blocks canonical-shadow
extensionality of the represented observation.
-/
theorem not_representedFiniteTraceQueryObservation_shadowExtensional_of_queryPostFiberSeparation
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
    ¬ ShadowExtensionalTowerObservation observe := by
  intro hext
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      (representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
        (Atom := Atom) repr hext)

/--
A separated post-fiber in the representing package blocks raw current-shadow
factorization of the represented observation.
-/
theorem no_representedFiniteTraceQueryObservation_currentShadowFactor_of_queryPostFiberSeparation
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
    ¬ ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      (representedFiniteTraceQueryObservation_postInvariant_of_currentShadowFactor
        (Atom := Atom) repr hfactor)

/--
A separated post-fiber in the representing package blocks semantic-reading
adequacy for that package.
-/
theorem no_representedFiniteTraceQueryObservation_semanticReadingAdequacy_of_queryPostFiberSeparation
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
    ¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post := by
  intro hadeq
  have hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post :=
    (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) repr.package.query repr.package.post).1 hadeq
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      hinvariant

/-! ## Decidable exact no-separation criteria -/

/--
Under decidable output equality, represented-observation extensionality is
exactly the absence of a separated post-fiber in the representing package.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_iff_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    ShadowExtensionalTowerObservation observe ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensional_iff_postInvariant
      (Atom := Atom) repr).trans
      (not_queryPostFiberSeparation_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) repr.package.query repr.package.post).symm

/--
Under decidable output equality, raw current-shadow factorization of a
represented observation is exactly absence of a separated post-fiber.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
      (Atom := Atom) repr).trans
      (not_queryPostFiberSeparation_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) repr.package.query repr.package.post).symm

/--
Under decidable output equality, semantic-reading adequacy for the representing
package is exactly absence of a separated post-fiber.
-/
theorem representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    exists_semanticReadingAdequacy_iff_no_queryPostFiberSeparation
      (Atom := Atom) repr.package.query repr.package.post

/--
No-separation supplies canonical-shadow extensionality for a represented
finite-query observation, but only through the explicit decidable exactness
boundary.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hnoSep :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post) :
    ShadowExtensionalTowerObservation observe := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensional_iff_no_queryPostFiberSeparation
      (Atom := Atom) repr).2 hnoSep

/--
No-separation supplies raw current-shadow factorization for a represented
finite-query observation, through the explicit decidable exactness boundary.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_of_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hnoSep :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) repr.package.query repr.package.post) :
    ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T) := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_no_queryPostFiberSeparation
      (Atom := Atom) repr).2 hnoSep

/-! ## Concrete Bool obstruction compatibility -/

/--
The represented Bool first-reading observation has a separated post-fiber in
its representing package.
-/
theorem boolFirstRepresentedFiniteTraceQueryObservation_queryPostFiberSeparation :
    QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).query
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).post := by
  exact
    SemanticRepairFiniteQueryPostFiberObstruction.boolFirstQueryReadingPost_currentShadowFiber_separates

/--
The represented Bool first-reading obstruction does not satisfy no-separation.
-/
theorem not_boolFirstRepresentedFiniteTraceQueryObservation_no_queryPostFiberSeparation :
    ¬ ¬ QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).query
      (boolTrueFiniteTraceQueryObservation
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).post := by
  intro hnoSep
  exact hnoSep boolFirstRepresentedFiniteTraceQueryObservation_queryPostFiberSeparation

end SemanticRepairFiniteQueryRepresentationNoSeparation
end QualitySurface
end Formal.AG.Research
