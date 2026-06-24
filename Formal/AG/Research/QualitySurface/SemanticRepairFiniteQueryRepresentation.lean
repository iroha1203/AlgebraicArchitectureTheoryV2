import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryObservation

/-!
Cycle 23 evidence for `G-aat-quality-surface-04`.

This file records a visible representation certificate: an arbitrary-looking
observation can use the finite query observation package only when it is
explicitly represented by such a package.  The certificate is not derived from
semantic soundness here.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentation

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation

universe u v w x y z

/-! ## Visible finite query representation certificate -/

/--
A visible certificate that an observation is represented by a finite
query-generated observation package.

The equality field is a material premise exposed at theorem boundary.  It is
not hidden inside the tower, support shadow, or observation package.
-/
structure FiniteTraceQueryObservationRepresentation
    {Atom : Type u}
    (support : List Atom)
    {Out : Type z}
    (observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out) where
  package : FiniteTraceQueryObservation support Out
  represents :
    ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      observe T = package.observe T

/--
An observation with a visible finite-query representation factors through the
support trace shadow.
-/
theorem representedFiniteTraceQueryObservation_factors_through_supportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        observe T =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  rcases
    finiteTraceQueryObservation_factors_through_supportTraceShadow
      repr.package with
    ⟨factor, hfactor⟩
  exact
    ⟨factor,
      by
        intro T
        calc
          observe T = repr.package.observe T := repr.represents T
          _ = factor (canonicalSupportTraceProbeTowerLayerShadow support T) :=
            hfactor T⟩

/--
An observation with a visible finite-query representation is extensional for
the support trace shadow.
-/
theorem representedFiniteTraceQueryObservation_supportTraceShadowExtensional
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe) :
    SupportTraceShadowExtensional support observe := by
  rcases
    representedFiniteTraceQueryObservation_factors_through_supportTraceShadow
      repr with
    ⟨factor, hfactor⟩
  exact supportTraceShadowExtensional_of_factorization factor hfactor

/--
Same support trace shadow gives equal values for any observation with a visible
finite-query representation.
-/
theorem representedFiniteTraceQueryObservation_same_of_same_supportTraceShadow
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    {observe :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom -> Out}
    (repr :
      FiniteTraceQueryObservationRepresentation support observe)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right) :
    observe left = observe right := by
  exact
    representedFiniteTraceQueryObservation_supportTraceShadowExtensional
      repr left right hshadow

/-! ## Concrete representation witness -/

/-- A visible representation certificate for the packaged Bool `[true]` query. -/
def boolTrueFiniteTraceQueryObservationRepresentation
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    FiniteTraceQueryObservationRepresentation
      SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation post).observe T) where
  package := boolTrueFiniteTraceQueryObservation post
  represents := by
    intro T
    rfl

/--
The represented Bool `[true]` query observation factors through the complete
Bool support shadow.
-/
theorem boolTrueRepresentedFiniteTraceQueryObservation_factors
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        (boolTrueFiniteTraceQueryObservation post).observe T =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport T) := by
  exact
    representedFiniteTraceQueryObservation_factors_through_supportTraceShadow
      (boolTrueFiniteTraceQueryObservationRepresentation post)

end SemanticRepairFiniteQueryRepresentation
end QualitySurface
end Formal.AG.Research
