import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualSourceRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Stored inverse-context projection of the finite-axis-fold residual kernel

The existing context projection retains the forward object action of every
actual normalized endpoint automorphism.  An exact equation transport also
stores the object action of the inverse functor inside that same context
equivalence.  These are distinct computational fields because the fixed thin
context category is a preorder rather than a skeletal order.

This file extracts that stored inverse action from every actual automorphism.
Composition reverses its order, so the projection lands in the opposite group
of context permutations.  On the existing forward-context kernel, its kernel
is precisely the locus where both stored object actions are identity.  Thinness
then determines both functors on arrows and the unit/counit, proving that the
actual context equivalence itself is the identity equivalence.

No inverse-context map or context-equivalence certificate is accepted as an
input.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- The stored inverse-functor object action of a normalized endpoint
automorphism, with its inverse supplied by the actual inverse automorphism. -/
noncomputable def finiteAxisFoldNormalizedContextBackwardEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun :=
    automorphism.hom.f.hom.base.upper.equationTransport.contextBackward
  invFun :=
    automorphism.inv.f.hom.base.upper.equationTransport.contextBackward
  left_inv context := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.equationTransport.contextBackward context)
      automorphism.inv_hom_id
    exact equality
  right_inv context := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.equationTransport.contextBackward context)
      automorphism.hom_inv_id
    exact equality

/-- The stored inverse-context action is contravariant in composition, hence
is a homomorphism to the opposite permutation group. -/
noncomputable def finiteAxisFoldNormalizedContextBackwardProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ where
  toFun automorphism :=
    MulOpposite.op (finiteAxisFoldNormalizedContextBackwardEquiv automorphism)
  map_one' := by
    apply MulOpposite.unop_injective
    apply Equiv.ext
    intro context
    rfl
  map_mul' first second := by
    apply MulOpposite.unop_injective
    apply Equiv.ext
    intro context
    rfl

/-- Restrict the stored inverse-context projection to the residual subgroup
whose forward context action is already identity. -/
noncomputable def finiteAxisFoldResidualContextKernelBackwardProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ where
  toFun remainder :=
    finiteAxisFoldNormalizedContextBackwardProjection remainder.1.1.1
  map_one' := map_one finiteAxisFoldNormalizedContextBackwardProjection
  map_mul' first second := by
    exact map_mul finiteAxisFoldNormalizedContextBackwardProjection
      first.1.1.1 second.1.1.1

/-- Residual automorphisms whose actual equation transport has identity object
actions in both its forward and stored inverse functors. -/
noncomputable abbrev FiniteAxisFoldResidualBidirectionalContextKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextKernelBackwardProjection

/-- Membership in the bidirectional kernel fixes the complete stored inverse
object function. -/
theorem finiteAxisFoldResidualBidirectionalContextKernel_contextBackward_eq_id
    (remainder : FiniteAxisFoldResidualBidirectionalContextKernel) :
    remainder.1.1.1.1.hom.f.hom.base.upper.equationTransport.contextBackward =
      _root_.id := by
  funext context
  have equality := congrArg MulOpposite.unop
    (MonoidHom.mem_ker.mp remainder.2)
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      permutation context)
    equality
  exact evaluated

private theorem finiteAxisFoldResidualContextSubsingleton_heq_of_type_eq
    {alpha beta : Sort u} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Fixing both stored context-object actions determines the complete actual
context equivalence.  Arrow maps and the unit/counit follow from thinness. -/
theorem finiteAxisFoldResidualBidirectionalContextKernel_contextEquivalence_eq_refl
    (remainder : FiniteAxisFoldResidualBidirectionalContextKernel) :
    remainder.1.1.1.1.hom.f.hom.base.upper.equationTransport.contextEquivalence =
      CategoryTheory.Equivalence.refl := by
  let equivalence :=
    remainder.1.1.1.1.hom.f.hom.base.upper.equationTransport.contextEquivalence
  have hfunctor : equivalence.functor =
      𝟭 (Site.ContextCategoryObject
        finiteAxisFoldActualDirectAdmissibleGeometry.obj.core.contextPreorder) := by
    refine CategoryTheory.Functor.ext (fun context => ?_) ?_
    · exact finiteAxisFoldResidualContextKernel_context_eq remainder.1 context
    · intros
      exact Subsingleton.elim _ _
  have hinverse : equivalence.inverse =
      𝟭 (Site.ContextCategoryObject
        finiteAxisFoldActualDirectAdmissibleGeometry.obj.core.contextPreorder) := by
    refine CategoryTheory.Functor.ext (fun context => ?_) ?_
    · exact congrFun
        (finiteAxisFoldResidualBidirectionalContextKernel_contextBackward_eq_id
          remainder) context
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldResidualContextSubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => (𝟭 (Site.ContextCategoryObject
        finiteAxisFoldActualDirectAdmissibleGeometry.obj.core.contextPreorder)) ≅ F)
    rw [hfunctor, hinverse]
    rfl
  · apply finiteAxisFoldResidualContextSubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => F ≅ (𝟭 (Site.ContextCategoryObject
        finiteAxisFoldActualDirectAdmissibleGeometry.obj.core.contextPreorder)))
    rw [hfunctor, hinverse]
    rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
