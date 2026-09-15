import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualLocalFiberAction
import Mathlib.Algebra.Group.Pi.Lemmas
import Formal.Util.AssertStandardAxioms

/-!
# Multiplicative local-fiber projections of the finite-axis-fold residual kernel

Cycle 79 constructed the actual Support, Axis, and Observable self-equivalence
over every context for every element of the context-object kernel.  Here those
families are packaged as group homomorphisms.  The construction first restricts
the complete dependent-sum action through the subgroup of permutations that
fix every base context, so multiplicativity is inherited from the actual joint
action rather than supplied as a family of local certificates.

The three families are then combined and their joint kernel is identified as
the intersection of the three separate kernels.  No image, source generator,
nontriviality, splitting, or source coverage is asserted.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

set_option synthInstance.maxHeartbeats 100000

/-- The fiber of a dependent sum over one specified base point. -/
private abbrev LocalSigmaFiber {α : Type u} (β : α → Type v) (a : α) :=
  {value : Σ x, β x // value.1 = a}

/-- The original dependent fiber and its corresponding Sigma subtype are
equivalent without an inhabitance assumption. -/
private def localSigmaFiberEquiv {α : Type u} (β : α → Type v) (a : α) :
    β a ≃ LocalSigmaFiber β a where
  toFun value := ⟨⟨a, value⟩, rfl⟩
  invFun value := Equiv.cast (congrArg β value.2) value.1.2
  left_inv value := rfl
  right_inv value := by
    rcases value with ⟨⟨base, value⟩, equality⟩
    change base = a at equality
    subst a
    rfl

/-- Permutations of a complete dependent sum that fix every base point. -/
private def sigmaBaseFixedSubgroup {α : Type u} (β : α → Type v) :
    Subgroup (Equiv.Perm (Σ x, β x)) where
  carrier permutation := ∀ value, (permutation value).1 = value.1
  one_mem' value := rfl
  mul_mem' := by
    intro first second first_fixed second_fixed
    change (∀ value, (first value).1 = value.1) at first_fixed
    change (∀ value, (second value).1 = value.1) at second_fixed
    change ∀ value, (first (second value)).1 = value.1
    intro value
    exact (first_fixed (second value)).trans (second_fixed value)
  inv_mem' := by
    intro permutation fixed
    change (∀ value, (permutation value).1 = value.1) at fixed
    change ∀ value, (permutation.symm value).1 = value.1
    intro value
    symm
    simpa using fixed (permutation.symm value)

/-- Restriction of a base-fixed dependent permutation to the Sigma subtype over
one base point. -/
private noncomputable def baseFixedSigmaFiberPermutation
    {α : Type u} {β : α → Type v}
    (permutation : sigmaBaseFixedSubgroup β) (a : α) :
    Equiv.Perm (LocalSigmaFiber β a) where
  toFun value := by
    have fixed := permutation.2
    change ∀ input, (permutation.1 input).1 = input.1 at fixed
    exact ⟨permutation.1 value.1, (fixed value.1).trans value.2⟩
  invFun value := by
    have fixed := permutation.2
    change ∀ input, (permutation.1 input).1 = input.1 at fixed
    refine ⟨permutation.1.symm value.1, ?_⟩
    have inverse_base : (permutation.1.symm value.1).1 = value.1.1 := by
      symm
      simpa using fixed (permutation.1.symm value.1)
    exact inverse_base.trans value.2
  left_inv value := by
    apply Subtype.ext
    exact permutation.1.symm_apply_apply value.1
  right_inv value := by
    apply Subtype.ext
    exact permutation.1.apply_symm_apply value.1

/-- Restriction to one Sigma fiber is multiplicative. -/
private noncomputable def baseFixedSigmaFiberProjection
    {α : Type u} {β : α → Type v} (a : α) :
    sigmaBaseFixedSubgroup β →* Equiv.Perm (LocalSigmaFiber β a) where
  toFun permutation := baseFixedSigmaFiberPermutation permutation a
  map_one' := by
    apply Equiv.ext
    intro value
    apply Subtype.ext
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro value
    apply Subtype.ext
    rfl

/-- Restriction to one original fiber, obtained by conjugating the Sigma-fiber
restriction along the canonical fiber equivalence. -/
private noncomputable def baseFixedLocalFiberProjection
    {α : Type u} {β : α → Type v} (a : α) :
    sigmaBaseFixedSubgroup β →* Equiv.Perm (β a) :=
  (localSigmaFiberEquiv β a).symm.permCongrHom.toMonoidHom.comp
    (baseFixedSigmaFiberProjection a)

/-- The actual context-support Sigma action of every context-kernel element,
viewed in the subgroup of base-fixed permutations. -/
private noncomputable def finiteAxisFoldResidualContextKernelSupportSigmaProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      sigmaBaseFixedSubgroup
        (fun context : FiniteAxisFoldResidualContextObject => context.ctx.Support) where
  toFun remainder := ⟨
    finiteAxisFoldResidualContextSupportProjection remainder.1,
    fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1⟩
  map_one' := by
    apply Subtype.ext
    exact map_one finiteAxisFoldResidualContextSupportProjection
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul finiteAxisFoldResidualContextSupportProjection first.1 second.1

/-- The actual context-axis Sigma action of every context-kernel element,
viewed in the subgroup of base-fixed permutations. -/
private noncomputable def finiteAxisFoldResidualContextKernelAxisSigmaProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      sigmaBaseFixedSubgroup
        (fun context : FiniteAxisFoldResidualContextObject => context.ctx.Axis) where
  toFun remainder := ⟨
    finiteAxisFoldResidualContextAxisProjection remainder.1,
    fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1⟩
  map_one' := by
    apply Subtype.ext
    exact map_one finiteAxisFoldResidualContextAxisProjection
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul finiteAxisFoldResidualContextAxisProjection first.1 second.1

/-- The actual context-observable Sigma action of every context-kernel element,
viewed in the subgroup of base-fixed permutations. -/
private noncomputable def finiteAxisFoldResidualContextKernelObservableSigmaProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      sigmaBaseFixedSubgroup
        (fun context : FiniteAxisFoldResidualContextObject => context.ctx.Observable) where
  toFun remainder := ⟨
    finiteAxisFoldResidualContextObservableProjection remainder.1,
    fun value => by
      change remainder.1.1.1.hom.f.hom.base.upper.equationTransport.contextForward
          value.1 = value.1
      exact finiteAxisFoldResidualContextKernel_context_eq remainder value.1⟩
  map_one' := by
    apply Subtype.ext
    exact map_one finiteAxisFoldResidualContextObservableProjection
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul finiteAxisFoldResidualContextObservableProjection first.1 second.1

/-- Multiplicative action on the Support fiber over one arbitrary context. -/
noncomputable def finiteAxisFoldResidualContextKernelSupportFiberProjection
    (context : FiniteAxisFoldResidualContextObject) :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      Equiv.Perm context.ctx.Support :=
  (baseFixedLocalFiberProjection context).comp
    finiteAxisFoldResidualContextKernelSupportSigmaProjection

/-- Multiplicative action on the Axis fiber over one arbitrary context. -/
noncomputable def finiteAxisFoldResidualContextKernelAxisFiberProjection
    (context : FiniteAxisFoldResidualContextObject) :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      Equiv.Perm context.ctx.Axis :=
  (baseFixedLocalFiberProjection context).comp
    finiteAxisFoldResidualContextKernelAxisSigmaProjection

/-- Multiplicative action on the Observable fiber over one arbitrary context. -/
noncomputable def finiteAxisFoldResidualContextKernelObservableFiberProjection
    (context : FiniteAxisFoldResidualContextObject) :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      Equiv.Perm context.ctx.Observable :=
  (baseFixedLocalFiberProjection context).comp
    finiteAxisFoldResidualContextKernelObservableSigmaProjection

/-- The multiplicative Support projection is exactly the Cycle 79 actual
fiber action. -/
theorem finiteAxisFoldResidualContextKernelSupportFiberProjection_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelSupportFiberProjection context remainder =
      finiteAxisFoldResidualContextKernelSupportEquiv remainder context := by
  rfl

/-- The multiplicative Axis projection is exactly the Cycle 79 actual fiber
action. -/
theorem finiteAxisFoldResidualContextKernelAxisFiberProjection_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelAxisFiberProjection context remainder =
      finiteAxisFoldResidualContextKernelAxisEquiv remainder context := by
  rfl

/-- The multiplicative Observable projection is exactly the Cycle 79 actual
fiber action. -/
theorem finiteAxisFoldResidualContextKernelObservableFiberProjection_apply
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel)
    (context : FiniteAxisFoldResidualContextObject) :
    finiteAxisFoldResidualContextKernelObservableFiberProjection context remainder =
      finiteAxisFoldResidualContextKernelObservableEquiv remainder context := by
  rfl

/-- The multiplicative Support action on all context fibers at once. -/
noncomputable def finiteAxisFoldResidualContextKernelSupportFiberFamilyProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      (∀ context : FiniteAxisFoldResidualContextObject,
        Equiv.Perm context.ctx.Support) :=
  Pi.monoidHom finiteAxisFoldResidualContextKernelSupportFiberProjection

/-- The multiplicative Axis action on all context fibers at once. -/
noncomputable def finiteAxisFoldResidualContextKernelAxisFiberFamilyProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      (∀ context : FiniteAxisFoldResidualContextObject,
        Equiv.Perm context.ctx.Axis) :=
  Pi.monoidHom finiteAxisFoldResidualContextKernelAxisFiberProjection

/-- The multiplicative Observable action on all context fibers at once. -/
noncomputable def finiteAxisFoldResidualContextKernelObservableFiberFamilyProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      (∀ context : FiniteAxisFoldResidualContextObject,
        Equiv.Perm context.ctx.Observable) :=
  Pi.monoidHom finiteAxisFoldResidualContextKernelObservableFiberProjection

/-- The three complete fiberwise action families, retained separately. -/
abbrev FiniteAxisFoldResidualLocalFiberActionFamily :=
  (∀ context : FiniteAxisFoldResidualContextObject,
      Equiv.Perm context.ctx.Support) ×
    ((∀ context : FiniteAxisFoldResidualContextObject,
        Equiv.Perm context.ctx.Axis) ×
      (∀ context : FiniteAxisFoldResidualContextObject,
        Equiv.Perm context.ctx.Observable))

/-- Joint multiplicative projection to all three complete local-fiber action
families. -/
noncomputable def finiteAxisFoldResidualContextKernelLocalFiberProjection :
    FiniteAxisFoldNormalizedAxisSignatureContextKernel →*
      FiniteAxisFoldResidualLocalFiberActionFamily :=
  finiteAxisFoldResidualContextKernelSupportFiberFamilyProjection.prod
    (finiteAxisFoldResidualContextKernelAxisFiberFamilyProjection.prod
      finiteAxisFoldResidualContextKernelObservableFiberFamilyProjection)

/-- The residual context-kernel elements invisible on every Support, Axis, and
Observable fiber simultaneously. -/
noncomputable abbrev FiniteAxisFoldResidualLocalFiberKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextKernelLocalFiberProjection

/-- The joint local-fiber kernel is exactly the intersection of the three
separate family kernels. -/
theorem finiteAxisFoldResidualLocalFiberKernel_eq :
    FiniteAxisFoldResidualLocalFiberKernel =
      MonoidHom.ker
          finiteAxisFoldResidualContextKernelSupportFiberFamilyProjection ⊓
        (MonoidHom.ker
            finiteAxisFoldResidualContextKernelAxisFiberFamilyProjection ⊓
          MonoidHom.ker
            finiteAxisFoldResidualContextKernelObservableFiberFamilyProjection) := by
  ext remainder
  simp [FiniteAxisFoldResidualLocalFiberKernel,
    finiteAxisFoldResidualContextKernelLocalFiberProjection]

/-- Pointwise characterization of the exact joint kernel in terms of the
actual Cycle 79 local-fiber actions. -/
theorem finiteAxisFoldResidualLocalFiberKernel_mem_iff
    (remainder : FiniteAxisFoldNormalizedAxisSignatureContextKernel) :
    remainder ∈ FiniteAxisFoldResidualLocalFiberKernel ↔
      (∀ context : FiniteAxisFoldResidualContextObject,
        finiteAxisFoldResidualContextKernelSupportEquiv remainder context = 1) ∧
      (∀ context : FiniteAxisFoldResidualContextObject,
        finiteAxisFoldResidualContextKernelAxisEquiv remainder context = 1) ∧
      (∀ context : FiniteAxisFoldResidualContextObject,
        finiteAxisFoldResidualContextKernelObservableEquiv remainder context = 1) := by
  rw [finiteAxisFoldResidualLocalFiberKernel_eq]
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker]
  constructor
  · rintro ⟨support, axis, observable⟩
    exact ⟨fun context => by
        rw [← finiteAxisFoldResidualContextKernelSupportFiberProjection_apply]
        exact congrFun support context,
      fun context => by
        rw [← finiteAxisFoldResidualContextKernelAxisFiberProjection_apply]
        exact congrFun axis context,
      fun context => by
        rw [← finiteAxisFoldResidualContextKernelObservableFiberProjection_apply]
        exact congrFun observable context⟩
  · rintro ⟨support, axis, observable⟩
    refine ⟨funext fun context => ?_, funext fun context => ?_, funext fun context => ?_⟩
    · change finiteAxisFoldResidualContextKernelSupportFiberProjection context
          remainder = 1
      rw [finiteAxisFoldResidualContextKernelSupportFiberProjection_apply]
      exact support context
    · change finiteAxisFoldResidualContextKernelAxisFiberProjection context
          remainder = 1
      rw [finiteAxisFoldResidualContextKernelAxisFiberProjection_apply]
      exact axis context
    · change finiteAxisFoldResidualContextKernelObservableFiberProjection context
          remainder = 1
      rw [finiteAxisFoldResidualContextKernelObservableFiberProjection_apply]
      exact observable context

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
