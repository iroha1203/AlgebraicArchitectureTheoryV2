import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryCurrentShadowReading
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryCanonicalBridge

/-!
Cycle 34 evidence for `G-aat-quality-surface-04`.

Cycle 33 normalized finite-query semantic-reading adequacy to the exact
post-fiber invariance criterion.  This file connects that criterion to visible
finite-query representation certificates: if an observation is represented by a
finite query package, then canonical-shadow extensionality or raw current-shadow
factorization of the represented observation is equivalent to post-fiber
invariance of the package post-map.

This is still a support node.  It does not prove that arbitrary semantic
soundness yields extensionality; it records the exact representation boundary at
which such a theorem would discharge the finite-query post-invariance
obligation.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationPostInvariant

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryCanonicalBridge
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryPostFiberObstruction

universe u v w x y z

/-! ## Representation transports shadow extensionality to post invariance -/

/--
For a visibly represented finite-query observation, canonical-shadow
extensionality of the represented observation implies post-fiber invariance of
the representing package.
-/
theorem representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext : ShadowExtensionalTowerObservation observe) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional
      (Atom := Atom)
      (query := repr.package.query)
      (post := repr.package.post)
      (by
        intro left right hshadow
        change repr.package.observe left = repr.package.observe right
        calc
          repr.package.observe left = observe left := (repr.represents left).symm
          _ = observe right := hext left right hshadow
          _ = repr.package.observe right := repr.represents right)

/--
Post-fiber invariance of a representing package makes the represented
observation canonical-shadow extensional.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post) :
    ShadowExtensionalTowerObservation observe := by
  intro left right hshadow
  have hpackage :
      repr.package.observe left = repr.package.observe right :=
    queryTraceGeneratedObservation_shadowExtensional_of_postInvariantOnCurrentShadowFibers
      (Atom := Atom)
      (query := repr.package.query)
      (post := repr.package.post)
      hinvariant left right hshadow
  calc
    observe left = repr.package.observe left := repr.represents left
    _ = repr.package.observe right := hpackage
    _ = observe right := (repr.represents right).symm

/--
Exact representation criterion: a represented finite-query observation is
canonical-shadow extensional iff its package post-map is invariant on
current-shadow query fibers.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensional_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    ShadowExtensionalTowerObservation observe ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    ⟨representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
      (Atom := Atom) repr,
      representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
        (Atom := Atom) repr⟩

/-! ## Representation transports raw factorization to post invariance -/

/--
Raw current-shadow factorization of a represented finite-query observation is
equivalent to post-fiber invariance of the representing package.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post := by
  constructor
  · intro hfactor
    rcases hfactor with ⟨factor, hfactor⟩
    exact
      representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
        (Atom := Atom) repr
        (by
          intro left right hshadow
          calc
            observe left = factor (canonicalTowerLayerShadow left) := hfactor left
            _ = factor (canonicalTowerLayerShadow right) := by rw [hshadow]
            _ = observe right := (hfactor right).symm)
  · intro hinvariant
    have hext :
        ShadowExtensionalTowerObservation observe :=
      representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
        (Atom := Atom) repr hinvariant
    exact
      ⟨canonicalShadowFactor observe,
        fun T => shadowExtensionalObservation_factors hext T⟩

/--
Current-shadow factorization of a represented finite-query observation implies
post-fiber invariance of the representing package.
-/
theorem representedFiniteTraceQueryObservation_postInvariant_of_currentShadowFactor
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hfactor :
      ∃ factor : FiniteTowerLayerShadow -> Out,
        ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe T = factor (canonicalTowerLayerShadow T)) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
      (Atom := Atom) repr).1 hfactor

/--
For a represented finite-query observation, canonical-shadow factorization via
the representative-induced `canonicalShadowFactor` is equivalent to post-fiber
invariance of the representing package.
-/
theorem representedFiniteTraceQueryObservation_canonicalShadowFactor_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      observe T = canonicalShadowFactor observe (canonicalTowerLayerShadow T)) ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post := by
  constructor
  · intro hfactor
    exact
      representedFiniteTraceQueryObservation_postInvariant_of_currentShadowFactor
        (Atom := Atom) repr ⟨canonicalShadowFactor observe, hfactor⟩
  · intro hinvariant T
    exact
      shadowExtensionalObservation_factors
        (representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
          (Atom := Atom) repr hinvariant) T

/--
For a visibly represented finite-query observation, raw current-shadow
factorization is equivalent to existence of a semantic-reading adequacy package
for the representing finite query.
-/
theorem representedFiniteTraceQueryObservation_currentShadowFactor_iff_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T = factor (canonicalTowerLayerShadow T)) ↔
      (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
          (Atom := Atom) reading repr.package.query repr.package.post) := by
  exact
    (representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
      (Atom := Atom) repr).trans
      (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) repr.package.query repr.package.post).symm

/--
For a visibly represented finite-query observation, semantic-reading adequacy
existence for the representing query is equivalent to canonical-shadow
extensionality of the represented observation.
-/
theorem representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post) ↔
      ShadowExtensionalTowerObservation observe := by
  exact
    (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) repr.package.query repr.package.post).trans
      (representedFiniteTraceQueryObservation_shadowExtensional_iff_postInvariant
        (Atom := Atom) repr).symm

/-! ## Support-control route to post invariance -/

/--
If the current shadow determines the support-trace shadow for a visible
finite-query representation, then the representing package satisfies the exact
post-fiber invariance criterion.
-/
theorem representedFiniteTraceQueryObservation_postInvariant_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) repr.package.query repr.package.post := by
  exact
    representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom) repr hcurrent)

/--
A finite query package satisfies post-fiber invariance when its support-trace
shadow is determined by the current shadow.
-/
theorem finiteTraceQueryObservation_postInvariant_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) obs.query obs.post := by
  exact
    postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional
      (Atom := Atom)
      (query := obs.query)
      (post := obs.post)
      (finiteTraceQueryObservation_shadowExtensional_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom) obs hcurrent)

/--
Support-control supplies semantic-reading adequacy for the representing finite
query, via the current-shadow reading normalization.
-/
theorem representedFiniteTraceQueryObservation_semanticReadingAdequacy_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading repr.package.query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading repr.package.query repr.package.post := by
  exact
    (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) repr.package.query repr.package.post).2
      (representedFiniteTraceQueryObservation_postInvariant_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom) repr hcurrent)

/--
Support-control supplies semantic-reading adequacy for a finite query package.
-/
theorem finiteTraceQueryObservation_semanticReadingAdequacy_of_currentShadowDeterminesSupportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hcurrent :
      CurrentShadowDeterminesSupportTraceShadow.{u, v, w, x, y} support) :
    ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs := by
  exact
    (finiteTraceQueryObservation_exists_semanticReadingAdequacy_iff_postInvariant
      (Atom := Atom) obs).2
      (finiteTraceQueryObservation_postInvariant_of_currentShadowDeterminesSupportTraceShadow
        (Atom := Atom) obs hcurrent)

/-! ## Concrete obstruction compatibility -/

/--
The represented Bool first-reading observation is not canonical-shadow
extensional.
-/
theorem not_boolFirstRepresentedFiniteTraceQueryObservation_shadowExtensional :
    ¬ ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation
          SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).observe T) := by
  intro hext
  exact
    SemanticRepairFiniteQueryPostFiberObstruction.not_boolFirstQueryReadingPostInvariantOnCurrentShadowFibers
      (representedFiniteTraceQueryObservation_postInvariant_of_shadowExtensional
        (Atom := Bool)
        (boolTrueFiniteTraceQueryObservationRepresentation
          SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost)
        hext)

/--
The represented Bool first-reading observation has no current-shadow factor.
-/
theorem boolFirstRepresentedFiniteTraceQueryObservation_no_currentShadowFactor :
    ¬ ∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation
            SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).observe T =
          factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  exact
    SemanticRepairFiniteQueryPostFiberObstruction.not_boolFirstQueryReadingPostInvariantOnCurrentShadowFibers
      ((representedFiniteTraceQueryObservation_currentShadowFactor_iff_postInvariant
        (Atom := Bool)
        (boolTrueFiniteTraceQueryObservationRepresentation
          SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost)).1
        hfactor)

end SemanticRepairFiniteQueryRepresentationPostInvariant
end QualitySurface
end ResearchLean.AG
