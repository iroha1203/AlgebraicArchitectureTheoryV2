import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationPostInvariant
import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryRepresentationNoSeparation
import ResearchLean.AG.QualitySurface.SemanticRepairTargetFactorization

/-!
Cycle 47 evidence for `G-aat-quality-surface-04`.

Cycle 46 connected represented finite-query observations to target-surface
factorization through recovery-dependent explicit coordinate certificates.
This file separates the API entry condition from recovery: a represented
finite-query observation enters the target-surface finite-shadow factorization
API exactly when the visible finite-query data make it shadow-extensional.

The theorem package keeps the boundary explicit.  Post-invariance,
semantic-reading adequacy, no post-fiber separation, or a direct
`ShadowExtensionalTowerObservation` are theorem arguments.  None is promoted to
arbitrary semantic observation factorization, target-level representation
adequacy, global coherence, obstruction vanishing, or target theorem
completion.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryCurrentShadowReading
open SemanticRepairFiniteQueryRepresentationPostInvariant
open SemanticRepairFiniteQueryRepresentationNoSeparation
open SemanticRepairTargetSurface
open SemanticRepairTargetFactorization

universe u v w x y z r s

/-! ## Exact assignment entry boundary -/

/--
A represented finite-query observation can be packaged as a
shadow-extensional obstruction assignment exactly when the observation itself
is shadow-extensional.  The representation parameter keeps the statement at
the finite-query boundary; it does not assert arbitrary observation adequacy.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (_repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      ShadowExtensionalTowerObservation observe := by
  constructor
  · rintro ⟨assignment, hobserve⟩
    rw [← hobserve]
    exact assignment.shadow_extensional
  · intro hext
    exact
      ⟨{ observe := observe, shadow_extensional := hext }, rfl⟩

/--
For represented finite-query observations, assignment entry is exactly the
post-invariance boundary of the representing finite query package.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).trans
      (representedFiniteTraceQueryObservation_shadowExtensional_iff_postInvariant
        (Atom := Atom) repr)

/--
For represented finite-query observations, assignment entry is exactly
semantic-reading adequacy existence for the representing package.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_exists_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post) := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).trans
      (representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_shadowExtensional
        (Atom := Atom) repr).symm

/--
Under decidable output equality, assignment entry is exactly the absence of a
separated post-fiber in the representing package.
-/
theorem representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    (∃ assignment :
      ShadowExtensionalObstructionAssignment
        (Atom := Atom) Out,
      assignment.observe = observe) ↔
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post := by
  exact
    (representedFiniteTraceQueryObservation_shadowExtensionalAssignment_iff_shadowExtensional
      (Atom := Atom) repr).trans
      (representedFiniteTraceQueryObservation_shadowExtensional_iff_no_queryPostFiberSeparation
        (Atom := Atom) repr)

/-! ## Visible routes into assignment entry -/

/-- Package a directly shadow-extensional represented observation. -/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_shadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (_repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext : ShadowExtensionalTowerObservation observe) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional := hext

/-- Post-invariance packages a represented finite-query observation. -/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
      (Atom := Atom) repr hinvariant

/-- Semantic-reading adequacy packages a represented finite-query observation. -/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_exists_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hadequacy :
      ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    (representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_shadowExtensional
      (Atom := Atom) repr).1 hadequacy

/-- No-separation packages a represented finite-query observation. -/
def representedFiniteTraceQueryObservation_shadowExtensionalAssignment_of_no_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type s}
    [DecidableEq Out]
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post) :
    ShadowExtensionalObstructionAssignment
      (Atom := Atom) Out where
  observe := observe
  shadow_extensional :=
    representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation
      (Atom := Atom) repr hno

/-! ## Target-surface factorization without recovery premises -/

/--
Direct shadow-extensionality makes a represented finite-query observation read
the target surface through the finite shadow of `Obs(A)`.
-/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (_repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext : ShadowExtensionalTowerObservation observe)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  exact
    (targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext).1

/-- The full target-surface factorization package from direct extensionality. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (_repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hext : ShadowExtensionalTowerObservation observe)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  exact
    targetSurfaceShadowExtensionalObservation_universalFactorization
      (A := A) certificates observe hext

/-- Post-invariance gives target-surface finite-shadow factorization. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_postInvariant
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
        (Atom := Atom) repr hinvariant)
      A certificates

/-- Post-invariance gives the full target-surface factorization package. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_postInvariant
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_postInvariant
        (Atom := Atom) repr hinvariant)
      A certificates

/-- Semantic-reading adequacy gives target-surface finite-shadow factorization. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_exists_semanticReadingAdequacy
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hadequacy :
      ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
      (Atom := Atom) repr
      ((representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_shadowExtensional
        (Atom := Atom) repr).1 hadequacy)
      A certificates

/-- Semantic-reading adequacy gives the full target-surface factorization package. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_exists_semanticReadingAdequacy
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hadequacy :
      ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
        SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
          (Atom := Atom) reading repr.package.query ∧
        SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, s}
          (Atom := Atom) reading repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
      (Atom := Atom) repr
      ((representedFiniteTraceQueryObservation_semanticReadingAdequacy_iff_shadowExtensional
        (Atom := Atom) repr).1 hadequacy)
      A certificates

/-- No-separation gives target-surface finite-shadow factorization. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_no_queryPostFiberSeparation
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    [DecidableEq Out]
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_factors_through_ObsA_shadow_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation
        (Atom := Atom) repr hno)
      A certificates

/-- No-separation gives the full target-surface factorization package. -/
theorem targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_no_queryPostFiberSeparation
    {Atom : Type u}
    {Choice : Type z}
    {TorsorRepair : Type r}
    {Coherence : Type z}
    {StackRepair : Type r}
    {Out : Type s}
    [DecidableEq Out]
    {support : List Atom}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    (hno :
      ¬ QueryPostFiberSeparation.{u, v, w, x, y, s}
        (Atom := Atom) repr.package.query repr.package.post)
    (A :
      UniversalSemanticRepairTargetSurface
        Atom Choice TorsorRepair Coherence StackRepair)
    [DecidableEq Choice]
    [forall repair, Decidable (A.torsor.effectiveRepair repair)]
    [DecidableEq Coherence]
    [forall repair, Decidable (A.stack.effectiveRepair repair)]
    (certificates : UniversalSemanticRepairTargetCertificates A) :
    (observe (Obs_A_ofFiniteCertificates A certificates) =
      canonicalShadowFactor observe (targetSurfaceLayerShadow A certificates)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
          observe U = factor (canonicalTowerLayerShadow U)) ->
        factor (targetSurfaceLayerShadow A certificates) =
          canonicalShadowFactor observe
            (targetSurfaceLayerShadow A certificates)) := by
  exact
    targetSurfaceRepresentedFiniteTraceQueryObservation_universalFactorization_of_shadowExtensional
      (Atom := Atom) repr
      (representedFiniteTraceQueryObservation_shadowExtensional_of_no_queryPostFiberSeparation
        (Atom := Atom) repr hno)
      A certificates

end SemanticRepairFiniteQueryTargetSurfaceAdmissibilityBoundary
end QualitySurface
end ResearchLean.AG
