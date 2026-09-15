import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualEquationRigidity
import Formal.Util.AssertStandardAxioms

/-!
# Context-action projection of the finite-axis-fold residual kernel

After the finite axis, signature, Atom, object, operation, and equation-index
components have been fixed, an actual normalized endpoint automorphism still
acts on the complete context category.  Its inverse automorphism supplies the
inverse context action, giving a genuine permutation of all context objects.

This module records that full action and its kernel.  It does not assert that
the action is finite, trivial, source-covered, or split.  In particular, the
context `Extension` field remains a possible source of surviving action.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

private noncomputable abbrev FiniteAxisFoldResidualContextCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

/-- The complete context-object carrier at the actual direct endpoint. -/
abbrev FiniteAxisFoldResidualContextObject :=
  Site.ContextCategoryObject
    FiniteAxisFoldResidualContextCore.contextPreorder

/-- Every normalized endpoint automorphism induces a permutation of all
context objects through its actual equation-transport equivalence. -/
noncomputable def finiteAxisFoldNormalizedContextEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun :=
    automorphism.hom.f.hom.base.upper.equationTransport.contextForward
  invFun :=
    automorphism.inv.f.hom.base.upper.equationTransport.contextForward
  left_inv context := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.equationTransport.contextForward context)
      automorphism.hom_inv_id
    change automorphism.inv.f.hom.base.upper.equationTransport.contextForward
        (automorphism.hom.f.hom.base.upper.equationTransport.contextForward
          context) = context at equality
    exact equality
  right_inv context := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        hom.f.hom.base.upper.equationTransport.contextForward context)
      automorphism.inv_hom_id
    change automorphism.hom.f.hom.base.upper.equationTransport.contextForward
        (automorphism.inv.f.hom.base.upper.equationTransport.contextForward
          context) = context at equality
    exact equality

/-- Projection of the full normalized endpoint automorphism group to its
complete context-object action. -/
noncomputable def finiteAxisFoldNormalizedContextProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun := finiteAxisFoldNormalizedContextEquiv
  map_one' := by
    apply Equiv.ext
    intro context
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro context
    rfl

/-- Restriction of the complete context action to the residual
axis-and-signature kernel. -/
noncomputable def finiteAxisFoldResidualContextProjection :
    FiniteAxisFoldNormalizedAxisSignatureKernel →*
      Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun remainder := finiteAxisFoldNormalizedContextProjection remainder.1.1
  map_one' := by
    exact map_one finiteAxisFoldNormalizedContextProjection
  map_mul' first second := by
    exact map_mul finiteAxisFoldNormalizedContextProjection first.1.1 second.1.1

/-- Residual automorphisms invisible also on every context object.  No source
coverage or triviality is included in this definition. -/
noncomputable abbrev FiniteAxisFoldNormalizedAxisSignatureContextKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextProjection

/-- Membership in the context kernel fixes the complete context-forward
object function, making subsequent fiberwise local actions well-typed. -/
theorem finiteAxisFoldResidualContextKernel_contextForward_eq_id
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel) :
    remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward =
      _root_.id := by
  funext context
  have equality := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      permutation context)
    (MonoidHom.mem_ker.mp remainder.2)
  exact equality

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
