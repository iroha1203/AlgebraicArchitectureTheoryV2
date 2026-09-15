import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextProjection
import Formal.Util.AssertStandardAxioms

/-!
# Joint context-local projections of the finite-axis-fold residual kernel

An actual normalized endpoint automorphism acts simultaneously on a context
and on every support, axis, and observable carried by that context.  Keeping the
dependent pair is essential: the local carrier at the target is indexed by the
image context, so projecting only the local value would discard part of the
actual geometry action.

The inverse normalized automorphism constructs the inverse of each dependent
action.  Thus all three actions are genuine permutations of the complete Sigma
carriers, and restrict to group homomorphisms on the axis-and-signature
residual kernel.  No finiteness, triviality, splitting, or source coverage is
claimed.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open FullGeometryNormalization

noncomputable section

/-- All context-local supports, retaining the context on which each support
depends. -/
abbrev FiniteAxisFoldResidualContextSupport :=
  Σ W : FiniteAxisFoldResidualContextObject, W.ctx.Support

/-- All context-local axes, retaining the context on which each axis depends. -/
abbrev FiniteAxisFoldResidualContextAxis :=
  Σ W : FiniteAxisFoldResidualContextObject, W.ctx.Axis

/-- All context-local observables, retaining the context on which each
observable depends. -/
abbrev FiniteAxisFoldResidualContextObservable :=
  Σ W : FiniteAxisFoldResidualContextObject, W.ctx.Observable

/-- Joint action of an actual normalized geometry morphism on a context and a
support in that context. -/
noncomputable def finiteAxisFoldContextSupportMap
    (hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
      FiniteAxisFoldNormalizedDirectGeometry) :
    FiniteAxisFoldResidualContextSupport →
      FiniteAxisFoldResidualContextSupport :=
  fun value => ⟨contextForward hom.f.hom.base value.1,
    hom.f.hom.geometry.supportComp value.1 value.2⟩

/-- Joint action of an actual normalized geometry morphism on a context and an
axis in that context. -/
noncomputable def finiteAxisFoldContextAxisMap
    (hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
      FiniteAxisFoldNormalizedDirectGeometry) :
    FiniteAxisFoldResidualContextAxis → FiniteAxisFoldResidualContextAxis :=
  fun value => ⟨contextForward hom.f.hom.base value.1,
    hom.f.hom.geometry.axisComp value.1 value.2⟩

/-- Joint action of an actual normalized geometry morphism on a context and an
observable in that context. -/
noncomputable def finiteAxisFoldContextObservableMap
    (hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
      FiniteAxisFoldNormalizedDirectGeometry) :
    FiniteAxisFoldResidualContextObservable →
      FiniteAxisFoldResidualContextObservable :=
  fun value => ⟨contextForward hom.f.hom.base value.1,
    hom.f.hom.geometry.observableComp value.1 value.2⟩

/-- The complete joint context-support action of a normalized automorphism. -/
noncomputable def finiteAxisFoldNormalizedContextSupportEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualContextSupport where
  toFun := finiteAxisFoldContextSupportMap automorphism.hom
  invFun := finiteAxisFoldContextSupportMap automorphism.inv
  left_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextSupportMap hom value)
      automorphism.hom_inv_id
    exact equality
  right_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextSupportMap hom value)
      automorphism.inv_hom_id
    exact equality

/-- The complete joint context-axis action of a normalized automorphism. -/
noncomputable def finiteAxisFoldNormalizedContextAxisEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualContextAxis where
  toFun := finiteAxisFoldContextAxisMap automorphism.hom
  invFun := finiteAxisFoldContextAxisMap automorphism.inv
  left_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextAxisMap hom value)
      automorphism.hom_inv_id
    exact equality
  right_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextAxisMap hom value)
      automorphism.inv_hom_id
    exact equality

/-- The complete joint context-observable action of a normalized
automorphism. -/
noncomputable def finiteAxisFoldNormalizedContextObservableEquiv
    (automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    Equiv.Perm FiniteAxisFoldResidualContextObservable where
  toFun := finiteAxisFoldContextObservableMap automorphism.hom
  invFun := finiteAxisFoldContextObservableMap automorphism.inv
  left_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextObservableMap hom value)
      automorphism.hom_inv_id
    exact equality
  right_inv value := by
    have equality := congrArg
      (fun hom : FiniteAxisFoldNormalizedDirectGeometry ⟶
          FiniteAxisFoldNormalizedDirectGeometry =>
        finiteAxisFoldContextObservableMap hom value)
      automorphism.inv_hom_id
    exact equality

/-- Projection to the complete joint context-support action. -/
noncomputable def finiteAxisFoldNormalizedContextSupportProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      Equiv.Perm FiniteAxisFoldResidualContextSupport where
  toFun := finiteAxisFoldNormalizedContextSupportEquiv
  map_one' := by
    apply Equiv.ext
    intro value
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro value
    rfl

/-- Projection to the complete joint context-axis action. -/
noncomputable def finiteAxisFoldNormalizedContextAxisProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      Equiv.Perm FiniteAxisFoldResidualContextAxis where
  toFun := finiteAxisFoldNormalizedContextAxisEquiv
  map_one' := by
    apply Equiv.ext
    intro value
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro value
    rfl

/-- Projection to the complete joint context-observable action. -/
noncomputable def finiteAxisFoldNormalizedContextObservableProjection :
    Aut FiniteAxisFoldNormalizedDirectGeometry →*
      Equiv.Perm FiniteAxisFoldResidualContextObservable where
  toFun := finiteAxisFoldNormalizedContextObservableEquiv
  map_one' := by
    apply Equiv.ext
    intro value
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro value
    rfl

/-- Residual-axis-and-signature-kernel projection to joint context-support
action. -/
noncomputable def finiteAxisFoldResidualContextSupportProjection :
    FiniteAxisFoldNormalizedAxisSignatureKernel →*
      Equiv.Perm FiniteAxisFoldResidualContextSupport where
  toFun remainder :=
    finiteAxisFoldNormalizedContextSupportProjection remainder.1.1
  map_one' := map_one finiteAxisFoldNormalizedContextSupportProjection
  map_mul' first second :=
    map_mul finiteAxisFoldNormalizedContextSupportProjection first.1.1 second.1.1

/-- Residual-axis-and-signature-kernel projection to joint context-axis
action. -/
noncomputable def finiteAxisFoldResidualContextAxisProjection :
    FiniteAxisFoldNormalizedAxisSignatureKernel →*
      Equiv.Perm FiniteAxisFoldResidualContextAxis where
  toFun remainder := finiteAxisFoldNormalizedContextAxisProjection remainder.1.1
  map_one' := map_one finiteAxisFoldNormalizedContextAxisProjection
  map_mul' first second :=
    map_mul finiteAxisFoldNormalizedContextAxisProjection first.1.1 second.1.1

/-- Residual-axis-and-signature-kernel projection to joint
context-observable action. -/
noncomputable def finiteAxisFoldResidualContextObservableProjection :
    FiniteAxisFoldNormalizedAxisSignatureKernel →*
      Equiv.Perm FiniteAxisFoldResidualContextObservable where
  toFun remainder :=
    finiteAxisFoldNormalizedContextObservableProjection remainder.1.1
  map_one' := map_one finiteAxisFoldNormalizedContextObservableProjection
  map_mul' first second :=
    map_mul finiteAxisFoldNormalizedContextObservableProjection first.1.1 second.1.1

/-- Residual automorphisms invisible on every dependent context-support pair. -/
noncomputable abbrev FiniteAxisFoldResidualContextSupportKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextSupportProjection

/-- Residual automorphisms invisible on every dependent context-axis pair. -/
noncomputable abbrev FiniteAxisFoldResidualContextAxisKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextAxisProjection

/-- Residual automorphisms invisible on every dependent context-observable
pair. -/
noncomputable abbrev FiniteAxisFoldResidualContextObservableKernel :=
  MonoidHom.ker finiteAxisFoldResidualContextObservableProjection

/-- Support-kernel membership fixes every context-support dependent pair. -/
theorem finiteAxisFoldResidualContextSupportKernel_apply
    (remainder : FiniteAxisFoldResidualContextSupportKernel)
    (value : FiniteAxisFoldResidualContextSupport) :
    finiteAxisFoldContextSupportMap remainder.1.1.1.hom value = value := by
  have equality := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextSupport =>
      permutation value)
    (MonoidHom.mem_ker.mp remainder.2)
  exact equality

/-- Axis-kernel membership fixes every context-axis dependent pair. -/
theorem finiteAxisFoldResidualContextAxisKernel_apply
    (remainder : FiniteAxisFoldResidualContextAxisKernel)
    (value : FiniteAxisFoldResidualContextAxis) :
    finiteAxisFoldContextAxisMap remainder.1.1.1.hom value = value := by
  have equality := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextAxis =>
      permutation value)
    (MonoidHom.mem_ker.mp remainder.2)
  exact equality

/-- Observable-kernel membership fixes every context-observable dependent
pair. -/
theorem finiteAxisFoldResidualContextObservableKernel_apply
    (remainder : FiniteAxisFoldResidualContextObservableKernel)
    (value : FiniteAxisFoldResidualContextObservable) :
    finiteAxisFoldContextObservableMap remainder.1.1.1.hom value = value := by
  have equality := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObservable =>
      permutation value)
    (MonoidHom.mem_ker.mp remainder.2)
  exact equality

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
