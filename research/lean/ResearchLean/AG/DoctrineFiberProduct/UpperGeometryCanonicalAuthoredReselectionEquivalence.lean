import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredRouteTransport
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCoefficientTrivialReselection

/-!
# Canonical-authored coefficient-trivial reselection equivalences

The exact endpoint comparison isomorphisms conjugate actual composite-fiber
automorphisms at every target vertex.  Applying those conjugations edgewise
gives forward and backward maps between the canonical-authored and generated
coefficient-trivial upper reselection spaces on both routes.

Implementation notes: conjugation is performed on the existing
`CompositeFiberAut` subgroup and the existing
`CoefficientTrivialUpperEdgeReselection` structure.  No comparison law or
inverse certificate is added to the compatible input, and no parallel raw
automorphism-family wrapper is introduced.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace CompositeFiberAut

/-- Conjugation by a total-geometry isomorphism restricts from the full
automorphism group to the composite-fiber subgroup. -/
noncomputable def conjugationEquiv
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) : CompositeFiberAut G ≃ CompositeFiberAut H where
  toFun automorphism :=
    ⟨Aut.autMulEquivOfIso iso automorphism.1, by
      change
        (((iso.inv.comp automorphism.1.hom).comp iso.hom).base.base) =
          𝟙 (packagePoint H.core)
      change
        (iso.inv.base.base.comp automorphism.1.hom.base.base).comp
            iso.hom.base.base =
          𝟙 (packagePoint H.core)
      rw [automorphism.2]
      change (iso.inv ≫ iso.hom).base.base = (𝟙 H : GeometryTotalHom H H).base.base
      exact congrArg
        (fun hom : GeometryTotalHom H H => hom.base.base)
        iso.inv_hom_id⟩
  invFun automorphism :=
    ⟨(Aut.autMulEquivOfIso iso).symm automorphism.1, by
      change
        (((iso.hom.comp automorphism.1.hom).comp iso.inv).base.base) =
          𝟙 (packagePoint G.core)
      change
        (iso.hom.base.base.comp automorphism.1.hom.base.base).comp
            iso.inv.base.base =
          𝟙 (packagePoint G.core)
      rw [automorphism.2]
      change (iso.hom ≫ iso.inv).base.base = (𝟙 G : GeometryTotalHom G G).base.base
      exact congrArg
        (fun hom : GeometryTotalHom G G => hom.base.base)
        iso.hom_inv_id⟩
  left_inv automorphism := by
    apply Subtype.ext
    exact (Aut.autMulEquivOfIso iso).left_inv automorphism.1
  right_inv automorphism := by
    apply Subtype.ext
    exact (Aut.autMulEquivOfIso iso).right_inv automorphism.1

/-- The forward composite-fiber conjugation has the expected complete
geometry hom. -/
@[simp] theorem conjugationEquiv_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut G) :
    CompositeFiberAut.hom (conjugationEquiv iso automorphism) =
      (iso.inv.comp (CompositeFiberAut.hom automorphism)).comp iso.hom :=
  rfl

/-- The inverse composite-fiber conjugation has the expected complete
geometry hom. -/
@[simp] theorem conjugationEquiv_symm_hom
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (iso : G ≅ H) (automorphism : CompositeFiberAut H) :
    CompositeFiberAut.hom ((conjugationEquiv iso).symm automorphism) =
      (iso.hom.comp (CompositeFiberAut.hom automorphism)).comp iso.inv :=
  rfl

end CompositeFiberAut

namespace UpperGeometryCompatibleProblemInputData

/-! ## Actual canonical-authored reselection types -/

/-- Coefficient-trivial reselections on the actual canonical-authored base
route transport. -/
abbrev CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  CoefficientTrivialUpperEdgeReselection
    input.canonicalAuthoredBaseRouteTransport

/-- Coefficient-trivial reselections on the actual canonical-authored pulled
route transport. -/
abbrev CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  CoefficientTrivialUpperEdgeReselection
    input.canonicalAuthoredPulledRouteTransport

/-! ## Base-route composite-fiber conjugation -/

/-- Conjugate one canonical-authored base composite-fiber automorphism
forward to the generated base endpoint. -/
noncomputable def canonicalAuthoredBaseCompositeFiberAutForwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package) :
    CompositeFiberAut (input.generatedBaseRouteFixedGeometryAt i).package :=
  CompositeFiberAut.conjugationEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)
    automorphism

/-- Return one generated base composite-fiber automorphism to the
canonical-authored base endpoint. -/
noncomputable def canonicalAuthoredBaseCompositeFiberAutBackwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteFixedGeometryAt i).package) :
    CompositeFiberAut
      (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package :=
  (CompositeFiberAut.conjugationEquiv
    (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i)).symm
      automorphism

/-- Forward base conjugation has the expected complete-geometry hom. -/
@[simp] theorem canonicalAuthoredBaseCompositeFiberAutForwardAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredBaseCompositeFiberAutForwardAt i automorphism) =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i).comp
        (CompositeFiberAut.hom automorphism)).comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i) := by
  exact CompositeFiberAut.conjugationEquiv_hom _ _

/-- Backward base conjugation has the expected complete-geometry hom. -/
@[simp] theorem canonicalAuthoredBaseCompositeFiberAutBackwardAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteFixedGeometryAt i).package) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt i automorphism) =
      ((input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt i).comp
        (CompositeFiberAut.hom automorphism)).comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt i) := by
  exact CompositeFiberAut.conjugationEquiv_symm_hom _ _

/-- Backward base conjugation after forward conjugation is the identity on
the actual canonical-authored composite-fiber group. -/
theorem canonicalAuthoredBaseCompositeFiberAutBackwardAt_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredBaseRouteFixedGeometryAt i).package) :
    input.canonicalAuthoredBaseCompositeFiberAutBackwardAt i
      (input.canonicalAuthoredBaseCompositeFiberAutForwardAt i automorphism) =
      automorphism := by
  exact Equiv.symm_apply_apply
    (CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i))
    automorphism

/-- Forward base conjugation after backward conjugation is the identity on
the actual generated composite-fiber group. -/
theorem canonicalAuthoredBaseCompositeFiberAutForwardAt_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedBaseRouteFixedGeometryAt i).package) :
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt i
      (input.canonicalAuthoredBaseCompositeFiberAutBackwardAt i automorphism) =
      automorphism := by
  exact Equiv.apply_symm_apply
    (CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i))
    automorphism

/-! ## Pulled-route composite-fiber conjugation -/

/-- Conjugate one canonical-authored pulled composite-fiber automorphism
forward to the generated pulled endpoint. -/
noncomputable def canonicalAuthoredPulledCompositeFiberAutForwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package) :
    CompositeFiberAut (input.generatedPulledRouteFixedGeometryAt i).package :=
  CompositeFiberAut.conjugationEquiv
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)
    automorphism

/-- Return one generated pulled composite-fiber automorphism to the
canonical-authored pulled endpoint. -/
noncomputable def canonicalAuthoredPulledCompositeFiberAutBackwardAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedPulledRouteFixedGeometryAt i).package) :
    CompositeFiberAut
      (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package :=
  (CompositeFiberAut.conjugationEquiv
    (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i)).symm
      automorphism

/-- Forward pulled conjugation has the expected complete-geometry hom. -/
@[simp] theorem canonicalAuthoredPulledCompositeFiberAutForwardAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredPulledCompositeFiberAutForwardAt i automorphism) =
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i).comp
        (CompositeFiberAut.hom automorphism)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i) := by
  exact CompositeFiberAut.conjugationEquiv_hom _ _

/-- Backward pulled conjugation has the expected complete-geometry hom. -/
@[simp] theorem canonicalAuthoredPulledCompositeFiberAutBackwardAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedPulledRouteFixedGeometryAt i).package) :
    CompositeFiberAut.hom
        (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt i automorphism) =
      ((input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt i).comp
        (CompositeFiberAut.hom automorphism)).comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt i) := by
  exact CompositeFiberAut.conjugationEquiv_symm_hom _ _

/-- Backward pulled conjugation after forward conjugation is the identity on
the actual canonical-authored composite-fiber group. -/
theorem canonicalAuthoredPulledCompositeFiberAutBackwardAt_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.canonicalAuthoredPulledRouteFixedGeometryAt i).package) :
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt i
      (input.canonicalAuthoredPulledCompositeFiberAutForwardAt i automorphism) =
      automorphism := by
  exact Equiv.symm_apply_apply
    (CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i))
    automorphism

/-- Forward pulled conjugation after backward conjugation is the identity on
the actual generated composite-fiber group. -/
theorem canonicalAuthoredPulledCompositeFiberAutForwardAt_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut
      (input.generatedPulledRouteFixedGeometryAt i).package) :
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt i
      (input.canonicalAuthoredPulledCompositeFiberAutBackwardAt i automorphism) =
      automorphism := by
  exact Equiv.apply_symm_apply
    (CompositeFiberAut.conjugationEquiv
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i))
    automorphism

/-! ## Base-route reselection equivalence -/

/-- Conjugate an actual canonical-authored base reselection forward to the
generated base route. -/
noncomputable def canonicalAuthoredBaseCoefficientTrivialReselectionForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input) :
    GeneratedBaseCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection i j edge :=
    input.canonicalAuthoredBaseCompositeFiberAutForwardAt j
      (reselection.toUpperEdgeReselection i j edge)
  coefficient_id := by
    intro i j edge
    rw [input.canonicalAuthoredBaseCompositeFiberAutForwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
          j).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge)).geometry.coefficientHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
            j).geometry.coefficientHom) = RingHom.id k
    rw [input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id,
      reselection.coefficient_id edge,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id]
    rfl

/-- Return an actual generated base reselection to the canonical-authored base
route. -/
noncomputable def canonicalAuthoredBaseCoefficientTrivialReselectionBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input) :
    CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection i j edge :=
    input.canonicalAuthoredBaseCompositeFiberAutBackwardAt j
      (reselection.toUpperEdgeReselection i j edge)
  coefficient_id := by
    intro i j edge
    rw [input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt
          j).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge)).geometry.coefficientHom.comp
          (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt
            j).geometry.coefficientHom) = RingHom.id k
    rw [input.canonicalAuthoredBaseToGeneratedRouteExactGeometryInvAt_coefficient_id,
      reselection.coefficient_id edge,
      input.canonicalAuthoredBaseToGeneratedRouteExactGeometryHomAt_coefficient_id]
    rfl

/-- Backward after forward is the identity on the actual canonical-authored
base coefficient-trivial reselection structure. -/
theorem canonicalAuthoredBaseCoefficientTrivialReselectionBackward_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input) :
    input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
          reselection) = reselection := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  exact input.canonicalAuthoredBaseCompositeFiberAutBackwardAt_forward j
    (reselection.toUpperEdgeReselection i j edge)

/-- Forward after backward is the identity on the actual generated base
coefficient-trivial reselection structure. -/
theorem canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedBaseCoefficientTrivialUpperEdgeReselection input) :
    input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
        (input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
          reselection) = reselection := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  exact input.canonicalAuthoredBaseCompositeFiberAutForwardAt_backward j
    (reselection.toUpperEdgeReselection i j edge)

/-- Endpoint conjugation gives an equivalence between the two actual base
coefficient-trivial upper reselection spaces. -/
noncomputable def canonicalAuthoredGeneratedBaseCoefficientTrivialReselectionEquiv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalAuthoredBaseCoefficientTrivialUpperEdgeReselection input ≃
      GeneratedBaseCoefficientTrivialUpperEdgeReselection input where
  toFun := input.canonicalAuthoredBaseCoefficientTrivialReselectionForward
  invFun := input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward
  left_inv := input.canonicalAuthoredBaseCoefficientTrivialReselectionBackward_forward
  right_inv := input.canonicalAuthoredBaseCoefficientTrivialReselectionForward_backward

/-! ## Pulled-route reselection equivalence -/

/-- Conjugate an actual canonical-authored pulled reselection forward to the
generated pulled route. -/
noncomputable def canonicalAuthoredPulledCoefficientTrivialReselectionForward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    GeneratedPulledCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection i j edge :=
    input.canonicalAuthoredPulledCompositeFiberAutForwardAt j
      (reselection.toUpperEdgeReselection i j edge)
  coefficient_id := by
    intro i j edge
    rw [input.canonicalAuthoredPulledCompositeFiberAutForwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
          j).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge)).geometry.coefficientHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
            j).geometry.coefficientHom) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id,
      reselection.coefficient_id edge,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id]
    rfl

/-- Return an actual generated pulled reselection to the canonical-authored
pulled route. -/
noncomputable def canonicalAuthoredPulledCoefficientTrivialReselectionBackward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection i j edge :=
    input.canonicalAuthoredPulledCompositeFiberAutBackwardAt j
      (reselection.toUpperEdgeReselection i j edge)
  coefficient_id := by
    intro i j edge
    rw [input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_hom]
    unfold GeometryTotalHom.comp GeomReadHom.comp
    change
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt
          j).geometry.coefficientHom.comp
        ((CompositeFiberAut.hom
          (reselection.toUpperEdgeReselection i j edge)).geometry.coefficientHom.comp
          (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt
            j).geometry.coefficientHom) = RingHom.id k
    rw [input.canonicalAuthoredPulledToGeneratedRouteExactGeometryInvAt_coefficient_id,
      reselection.coefficient_id edge,
      input.canonicalAuthoredPulledToGeneratedRouteExactGeometryHomAt_coefficient_id]
    rfl

/-- Backward after forward is the identity on the actual canonical-authored
pulled coefficient-trivial reselection structure. -/
theorem canonicalAuthoredPulledCoefficientTrivialReselectionBackward_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection :
      CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input) :
    input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
          reselection) = reselection := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  exact input.canonicalAuthoredPulledCompositeFiberAutBackwardAt_forward j
    (reselection.toUpperEdgeReselection i j edge)

/-- Forward after backward is the identity on the actual generated pulled
coefficient-trivial reselection structure. -/
theorem canonicalAuthoredPulledCoefficientTrivialReselectionForward_backward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (reselection : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
        (input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
          reselection) = reselection := by
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  exact input.canonicalAuthoredPulledCompositeFiberAutForwardAt_backward j
    (reselection.toUpperEdgeReselection i j edge)

/-- Endpoint conjugation gives an equivalence between the two actual pulled
coefficient-trivial upper reselection spaces. -/
noncomputable def canonicalAuthoredGeneratedPulledCoefficientTrivialReselectionEquiv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    CanonicalAuthoredPulledCoefficientTrivialUpperEdgeReselection input ≃
      GeneratedPulledCoefficientTrivialUpperEdgeReselection input where
  toFun := input.canonicalAuthoredPulledCoefficientTrivialReselectionForward
  invFun := input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward
  left_inv := input.canonicalAuthoredPulledCoefficientTrivialReselectionBackward_forward
  right_inv := input.canonicalAuthoredPulledCoefficientTrivialReselectionForward_backward

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
