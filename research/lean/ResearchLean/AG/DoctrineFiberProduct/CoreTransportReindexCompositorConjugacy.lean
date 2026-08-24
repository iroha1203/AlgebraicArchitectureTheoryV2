import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexAdjunctionComposition

/-!
# Conjugacy of the generated finite-composition compositors

This module identifies the mate of the generated covariant compositor with the
generated selected-reindex compositor.  The comparison is derived from the
transported composite adjunction and its equality with the independently
generated direct adjunction; no mate or right-adjoint comparison is supplied by
the caller.

The categorical calculation expands transport of an adjunction across a pair
of natural isomorphisms.  Naturality of the right isomorphism and the right
triangle identity show that conjugating the left isomorphism recovers exactly
the right isomorphism.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u u1 u2 v1 v2

open CategoryTheory
open AtomFoundation CrossStageCoherence

private theorem conjugateIsoEquiv_ofNatIsoLeft_symm_ofNatIsoRight
    {C : Type u1} {D : Type u2}
    [Category.{v1} C] [Category.{v2} D]
    {L1 L2 : C ⥤ D} {R1 R2 : D ⥤ C}
    (adj : L1 ⊣ R1) (leftIso : L2 ≅ L1) (rightIso : R1 ≅ R2) :
    conjugateIsoEquiv adj
        ((adj.ofNatIsoLeft leftIso.symm).ofNatIsoRight rightIso) leftIso =
      rightIso := by
  ext X
  simp [conjugateIsoEquiv, conjugateEquiv, mateEquiv,
    Adjunction.ofNatIsoLeft, Adjunction.ofNatIsoRight]
  rw [Adjunction.homEquiv_unit]
  simp [Category.assoc]
  have naturality : rightIso.hom.app (L1.obj (R1.obj X)) ≫
        R2.map (adj.counit.app X) =
      R1.map (adj.counit.app X) ≫ rightIso.hom.app X := by
    simpa only using (rightIso.hom.naturality (adj.counit.app X)).symm
  rw [naturality]
  rw [← Category.assoc, adj.right_triangle_components]
  simp

/-- G-110(E) finite-composition mate coherence: the conjugate of the generated
covariant transport compositor under the composite generated adjunction is
exactly the generated selected-reindex compositor.  The proof uses the
producer-derived transported adjunction and its equality with the direct
generated adjunction, so the caller supplies only the two finite cartesian
presentations. -/
theorem coreTransportReindexCompositor_conjugateIsoEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    conjugateIsoEquiv
        ((coreTransportReindexAdjunction (typedRealizableHom first)).comp
          (coreTransportReindexAdjunction (typedRealizableHom second)))
        (coreTransportReindexAdjunction
          (typedRealizableHom (compPresentation first second)))
        (typedCoreFiberTransportCompositor first second) =
      selectedCoreFiberReindexCompositor first second := by
  rw [← coreTransportReindexCompositorAdjunction_eq_direct first second]
  exact conjugateIsoEquiv_ofNatIsoLeft_symm_ofNatIsoRight _ _ _

end AAT.AG.DoctrineFiberProduct
