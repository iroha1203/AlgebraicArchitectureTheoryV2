import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualJointLocalProjection
import Formal.Util.AssertStandardAxioms

/-!
# Local fiber actions of the finite-axis-fold context kernel

Cycle 78 retained the complete dependent action on every context-local pair.
For an element of the context-object kernel, the base context of each pair is
fixed.  This module uses that proved kernel equality to restrict the dependent
permutations to genuine self-equivalences of the Support, Axis, and Observable
fiber over every context.

No local carrier is assumed inhabited, and no context or local value is
selected.  The result is a family over every context and every element of the
complete residual context kernel.  It does not assert that these fiber actions
are trivial, finite, source-generated, or jointly faithful.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

/-- The dependent-sum fiber over one base point. -/
private abbrev SigmaFiber {α : Type u} (β : α → Type v) (a : α) :=
  {value : Σ x, β x // value.1 = a}

/-- A dependent fiber is equivalent to the corresponding subtype of the full
Sigma carrier. -/
private def sigmaFiberEquiv {α : Type u} (β : α → Type v) (a : α) :
    β a ≃ SigmaFiber β a where
  toFun value := ⟨⟨a, value⟩, rfl⟩
  invFun value := Equiv.cast (congrArg β value.2) value.1.2
  left_inv value := rfl
  right_inv value := by
    rcases value with ⟨⟨base, value⟩, equality⟩
    change base = a at equality
    subst a
    rfl

/-- A permutation of a dependent sum whose base action is pointwise identity
restricts to a permutation of every individual fiber. -/
private noncomputable def sigmaFiberPermutation
    {α : Type u} {β : α → Type v}
    (permutation : Equiv.Perm (Σ x, β x))
    (base_fixed : ∀ value, (permutation value).1 = value.1)
    (a : α) : Equiv.Perm (SigmaFiber β a) where
  toFun value := ⟨permutation value.1, (base_fixed value.1).trans value.2⟩
  invFun value := by
    refine ⟨permutation.symm value.1, ?_⟩
    have inverse_base : (permutation.symm value.1).1 = value.1.1 := by
      symm
      simpa using base_fixed (permutation.symm value.1)
    exact inverse_base.trans value.2
  left_inv value := by
    apply Subtype.ext
    exact permutation.symm_apply_apply value.1
  right_inv value := by
    apply Subtype.ext
    exact permutation.apply_symm_apply value.1

/-- A base-fixed permutation of a dependent sum induces a self-equivalence of
each original fiber, without choosing an element of that fiber. -/
private noncomputable def sigmaFiberSelfEquiv
    {α : Type u} {β : α → Type v}
    (permutation : Equiv.Perm (Σ x, β x))
    (base_fixed : ∀ value, (permutation value).1 = value.1)
    (a : α) : Equiv.Perm (β a) :=
  (sigmaFiberEquiv β a).trans
    ((sigmaFiberPermutation permutation base_fixed a).trans
      (sigmaFiberEquiv β a).symm)

/-- Context-kernel membership fixes each actual context, stated pointwise for
the local-fiber constructions below. -/
theorem finiteAxisFoldResidualContextKernel_context_eq
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
        context = context :=
  congrFun (finiteAxisFoldResidualContextKernel_contextForward_eq_id remainder)
    context

/-- Every residual context-kernel element has a genuine permutation of the
Support fiber over every fixed context. -/
noncomputable def finiteAxisFoldResidualContextKernelSupportEquiv
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    Equiv.Perm context.ctx.Support :=
  sigmaFiberSelfEquiv
    (finiteAxisFoldNormalizedContextSupportEquiv remainder.1.1.1)
    (fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1)
    context

/-- The support-fiber permutation is the actual support comparison transported
back along the proved context-kernel equality. -/
theorem finiteAxisFoldResidualContextKernelSupportEquiv_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (support : context.ctx.Support) :
    finiteAxisFoldResidualContextKernelSupportEquiv remainder context support =
      supportEquivOfContextEq
        (finiteAxisFoldResidualContextKernel_context_eq remainder context)
        (remainder.1.1.1.hom.f.hom.geometry.supportComp context support) := by
  rfl

/-- The extracted support-fiber action preserves the original support
reading; the residual Atom rigidity theorem removes the transported Atom. -/
theorem finiteAxisFoldResidualContextKernelSupportEquiv_reads
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (support : context.ctx.Support) (atom : FiniteModel.carrier.Atom)
    (reads : context.ctx.minimal.supportReads support atom) :
    context.ctx.minimal.supportReads
      (finiteAxisFoldResidualContextKernelSupportEquiv remainder context support)
      atom := by
  rw [finiteAxisFoldResidualContextKernelSupportEquiv_apply]
  apply (supportEquivOfContextEq_reads_iff
    (finiteAxisFoldResidualContextKernel_context_eq remainder context) _ _).2
  have transported :=
    remainder.1.1.1.hom.f.hom.geometry.supportReads context support atom reads
  rw [finiteAxisFoldResidual_atomEquiv_eq_refl remainder.1] at transported
  exact transported

/-- Every residual context-kernel element has a genuine permutation of the
Axis fiber over every fixed context. -/
noncomputable def finiteAxisFoldResidualContextKernelAxisEquiv
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    Equiv.Perm context.ctx.Axis :=
  sigmaFiberSelfEquiv
    (finiteAxisFoldNormalizedContextAxisEquiv remainder.1.1.1)
    (fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1)
    context

/-- The axis-fiber permutation is the actual axis comparison transported back
along the proved context-kernel equality. -/
theorem finiteAxisFoldResidualContextKernelAxisEquiv_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (axis : context.ctx.Axis) :
    finiteAxisFoldResidualContextKernelAxisEquiv remainder context axis =
      axisEquivOfContextEq
        (finiteAxisFoldResidualContextKernel_context_eq remainder context)
        (remainder.1.1.1.hom.f.hom.geometry.axisComp context axis) := by
  rfl

/-- The extracted axis-fiber action preserves the original axis reading. -/
theorem finiteAxisFoldResidualContextKernelAxisEquiv_reads
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (axis : context.ctx.Axis)
    (reads : context.ctx.minimal.axisReads axis) :
    context.ctx.minimal.axisReads
      (finiteAxisFoldResidualContextKernelAxisEquiv remainder context axis) := by
  rw [finiteAxisFoldResidualContextKernelAxisEquiv_apply]
  apply (axisEquivOfContextEq_reads_iff
    (finiteAxisFoldResidualContextKernel_context_eq remainder context) _).2
  exact remainder.1.1.1.hom.f.hom.geometry.axisReads context axis reads

/-- Every residual context-kernel element has a genuine permutation of the
Observable fiber over every fixed context. -/
noncomputable def finiteAxisFoldResidualContextKernelObservableEquiv
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    Equiv.Perm context.ctx.Observable :=
  sigmaFiberSelfEquiv
    (finiteAxisFoldNormalizedContextObservableEquiv remainder.1.1.1)
    (fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1)
    context

/-- The observable-fiber permutation is the actual observable comparison
transported back along the proved context-kernel equality. -/
theorem finiteAxisFoldResidualContextKernelObservableEquiv_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (observable : context.ctx.Observable) :
    finiteAxisFoldResidualContextKernelObservableEquiv remainder context observable =
      observableEquivOfContextEq
        (finiteAxisFoldResidualContextKernel_context_eq remainder context)
        (remainder.1.1.1.hom.f.hom.geometry.observableComp context observable) := by
  rfl

/-- The extracted observable-fiber action preserves the original observable
reading. -/
theorem finiteAxisFoldResidualContextKernelObservableEquiv_reads
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject)
    (observable : context.ctx.Observable)
    (reads : context.ctx.minimal.observableReads observable) :
    context.ctx.minimal.observableReads
      (finiteAxisFoldResidualContextKernelObservableEquiv remainder context observable) := by
  rw [finiteAxisFoldResidualContextKernelObservableEquiv_apply]
  apply (observableEquivOfContextEq_reads_iff
    (finiteAxisFoldResidualContextKernel_context_eq remainder context) _).2
  exact remainder.1.1.1.hom.f.hom.geometry.observableReads
    context observable reads

end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
