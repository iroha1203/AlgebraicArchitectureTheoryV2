import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryDirectRouteHoms

/-!
# Dependent carrier inverses for realization-exact factors

The strong-Cartesian factor through a direct realization normalization must
move Support, Axis, and Observable values backward and then return them to the
original forward source fiber.  This module packages the six reviewed
component cancellation laws as genuine equivalences of dependent total
spaces, and exposes their fiberwise inverse-at-forward maps.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory AtomFoundation GeometryTransport

set_option maxHeartbeats 3000000

namespace RealizationExactUpperEquivalence

/-- Realization-exact transport is an equivalence on the dependent total
space of context-indexed supports. -/
noncomputable def supportSigmaEquiv {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) :
    (Σ W : Site.ContextCategoryObject P.contextPreorder, W.ctx.Support) ≃
      (Σ W : Site.ContextCategoryObject Q.contextPreorder, W.ctx.Support) where
  toFun x := ⟨(upperCoreContextFunctor e.forward).obj x.1,
    H.homSupply.supportComp x.1 x.2⟩
  invFun x := ⟨(upperCoreContextFunctor e.backward).obj x.1,
    H.invSupply.supportComp x.1 x.2⟩
  left_inv x := by
    dsimp
    apply Sigma.ext (e.forwardBackwardContext x.1)
    exact (cast_heq _ _).symm.trans (heq_of_eq (H.support_hom_inv x.1 x.2))
  right_inv x := by
    dsimp
    apply Sigma.ext (e.backwardForwardContext x.1)
    exact (cast_heq _ _).symm.trans (heq_of_eq (H.support_inv_hom x.1 x.2))

/-- Realization-exact transport is an equivalence on the dependent total
space of context-indexed axes. -/
noncomputable def axisSigmaEquiv {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) :
    (Σ W : Site.ContextCategoryObject P.contextPreorder, W.ctx.Axis) ≃
      (Σ W : Site.ContextCategoryObject Q.contextPreorder, W.ctx.Axis) where
  toFun x := ⟨(upperCoreContextFunctor e.forward).obj x.1,
    H.homSupply.axisComp x.1 x.2⟩
  invFun x := ⟨(upperCoreContextFunctor e.backward).obj x.1,
    H.invSupply.axisComp x.1 x.2⟩
  left_inv x := by
    dsimp
    apply Sigma.ext (e.forwardBackwardContext x.1)
    exact (cast_heq _ _).symm.trans (heq_of_eq (H.axis_hom_inv x.1 x.2))
  right_inv x := by
    dsimp
    apply Sigma.ext (e.backwardForwardContext x.1)
    exact (cast_heq _ _).symm.trans (heq_of_eq (H.axis_inv_hom x.1 x.2))

/-- Realization-exact transport is an equivalence on the dependent total
space of context-indexed observables. -/
noncomputable def observableSigmaEquiv {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e) :
    (Σ W : Site.ContextCategoryObject P.contextPreorder, W.ctx.Observable) ≃
      (Σ W : Site.ContextCategoryObject Q.contextPreorder, W.ctx.Observable) where
  toFun x := ⟨(upperCoreContextFunctor e.forward).obj x.1,
    H.homSupply.observableComp x.1 x.2⟩
  invFun x := ⟨(upperCoreContextFunctor e.backward).obj x.1,
    H.invSupply.observableComp x.1 x.2⟩
  left_inv x := by
    dsimp
    apply Sigma.ext (e.forwardBackwardContext x.1)
    exact (cast_heq _ _).symm.trans
      (heq_of_eq (H.observable_hom_inv x.1 x.2))
  right_inv x := by
    dsimp
    apply Sigma.ext (e.backwardForwardContext x.1)
    exact (cast_heq _ _).symm.trans
      (heq_of_eq (H.observable_inv_hom x.1 x.2))

/-- Backward support transport at a forward context, returned to the literal
source context fiber. -/
noncomputable def supportInverseAtForward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (support : ((upperCoreContextFunctor e.forward).obj W).ctx.Support) :
    W.ctx.Support :=
  cast (congrArg (fun X => X.ctx.Support) (e.forwardBackwardContext W))
    (H.invSupply.supportComp _ support)

/-- Backward axis transport at a forward context, returned to the literal
source context fiber. -/
noncomputable def axisInverseAtForward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (axis : ((upperCoreContextFunctor e.forward).obj W).ctx.Axis) : W.ctx.Axis :=
  cast (congrArg (fun X => X.ctx.Axis) (e.forwardBackwardContext W))
    (H.invSupply.axisComp _ axis)

/-- Backward observable transport at a forward context, returned to the
literal source context fiber. -/
noncomputable def observableInverseAtForward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (observable : ((upperCoreContextFunctor e.forward).obj W).ctx.Observable) :
    W.ctx.Observable :=
  cast (congrArg (fun X => X.ctx.Observable) (e.forwardBackwardContext W))
    (H.invSupply.observableComp _ observable)

/-- The support inverse-at-forward reflects the selected support reading. -/
theorem supportInverseAtForward_reads {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (support : ((upperCoreContextFunctor e.forward).obj W).ctx.Support)
    (atom : U.Atom)
    (hread : ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.supportReads
      support (e.forward.atomEquiv atom)) :
    W.ctx.minimal.supportReads (H.supportInverseAtForward W support) atom := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Support := ⟨(upperCoreContextFunctor e.forward).obj W, support⟩
  have hback :
      ((H.supportSigmaEquiv).symm target).1.ctx.minimal.supportReads
        ((H.supportSigmaEquiv).symm target).2
        (e.backward.atomEquiv (e.forward.atomEquiv atom)) :=
    H.invSupply.supportReads _ support (e.forward.atomEquiv atom) hread
  have hsource :
      (⟨W, H.supportInverseAtForward W support⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Support) =
        (H.supportSigmaEquiv).symm target := by
    dsimp [supportSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  rw [← hsource] at hback
  simpa only [e.forwardBackwardAtom atom] using hback

/-- The axis inverse-at-forward reflects the selected axis reading. -/
theorem axisInverseAtForward_reads {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (axis : ((upperCoreContextFunctor e.forward).obj W).ctx.Axis)
    (hread : ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.axisReads axis) :
    W.ctx.minimal.axisReads (H.axisInverseAtForward W axis) := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Axis := ⟨(upperCoreContextFunctor e.forward).obj W, axis⟩
  have hback :
      ((H.axisSigmaEquiv).symm target).1.ctx.minimal.axisReads
        ((H.axisSigmaEquiv).symm target).2 :=
    H.invSupply.axisReads _ axis hread
  have hsource :
      (⟨W, H.axisInverseAtForward W axis⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Axis) =
        (H.axisSigmaEquiv).symm target := by
    dsimp [axisSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  rw [← hsource] at hback
  exact hback

/-- The observable inverse-at-forward reflects the selected observable
reading. -/
theorem observableInverseAtForward_reads {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (observable : ((upperCoreContextFunctor e.forward).obj W).ctx.Observable)
    (hread : ((upperCoreContextFunctor e.forward).obj W).ctx.minimal.observableReads
      observable) :
    W.ctx.minimal.observableReads (H.observableInverseAtForward W observable) := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Observable := ⟨(upperCoreContextFunctor e.forward).obj W, observable⟩
  have hback :
      ((H.observableSigmaEquiv).symm target).1.ctx.minimal.observableReads
        ((H.observableSigmaEquiv).symm target).2 :=
    H.invSupply.observableReads _ observable hread
  have hsource :
      (⟨W, H.observableInverseAtForward W observable⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Observable) =
        (H.observableSigmaEquiv).symm target := by
    dsimp [observableSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  rw [← hsource] at hback
  exact hback

/-- Forward support transport cancels the fiberwise inverse-at-forward map. -/
theorem support_forward_inverse {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (support : ((upperCoreContextFunctor e.forward).obj W).ctx.Support) :
    H.homSupply.supportComp W (H.supportInverseAtForward W support) = support := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Support := ⟨(upperCoreContextFunctor e.forward).obj W, support⟩
  have hsource :
      (⟨W, H.supportInverseAtForward W support⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Support) =
        (H.supportSigmaEquiv).symm target := by
    dsimp [supportSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  have htotal : H.supportSigmaEquiv
      ⟨W, H.supportInverseAtForward W support⟩ = target := by
    rw [hsource]
    exact Equiv.apply_symm_apply _ _
  dsimp [supportSigmaEquiv, target] at htotal
  exact eq_of_heq (Sigma.ext_iff.mp htotal).2

/-- Forward axis transport cancels the fiberwise inverse-at-forward map. -/
theorem axis_forward_inverse {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (axis : ((upperCoreContextFunctor e.forward).obj W).ctx.Axis) :
    H.homSupply.axisComp W (H.axisInverseAtForward W axis) = axis := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Axis := ⟨(upperCoreContextFunctor e.forward).obj W, axis⟩
  have hsource :
      (⟨W, H.axisInverseAtForward W axis⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Axis) =
        (H.axisSigmaEquiv).symm target := by
    dsimp [axisSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  have htotal : H.axisSigmaEquiv
      ⟨W, H.axisInverseAtForward W axis⟩ = target := by
    rw [hsource]
    exact Equiv.apply_symm_apply _ _
  dsimp [axisSigmaEquiv, target] at htotal
  exact eq_of_heq (Sigma.ext_iff.mp htotal).2

/-- Forward observable transport cancels the fiberwise inverse-at-forward map. -/
theorem observable_forward_inverse {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (observable : ((upperCoreContextFunctor e.forward).obj W).ctx.Observable) :
    H.homSupply.observableComp W
      (H.observableInverseAtForward W observable) = observable := by
  let target : Σ V : Site.ContextCategoryObject Q.contextPreorder,
      V.ctx.Observable := ⟨(upperCoreContextFunctor e.forward).obj W, observable⟩
  have hsource :
      (⟨W, H.observableInverseAtForward W observable⟩ :
        Σ V : Site.ContextCategoryObject P.contextPreorder, V.ctx.Observable) =
        (H.observableSigmaEquiv).symm target := by
    dsimp [observableSigmaEquiv, target]
    apply Sigma.ext (e.forwardBackwardContext W).symm
    exact cast_heq _ _
  have htotal : H.observableSigmaEquiv
      ⟨W, H.observableInverseAtForward W observable⟩ = target := by
    rw [hsource]
    exact Equiv.apply_symm_apply _ _
  dsimp [observableSigmaEquiv, target] at htotal
  exact eq_of_heq (Sigma.ext_iff.mp htotal).2

/-- The fiberwise support inverse also cancels forward support transport. -/
theorem support_inverse_forward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) (support : W.ctx.Support) :
    H.supportInverseAtForward W (H.homSupply.supportComp W support) = support :=
  H.support_hom_inv W support

/-- The fiberwise axis inverse also cancels forward axis transport. -/
theorem axis_inverse_forward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) (axis : W.ctx.Axis) :
    H.axisInverseAtForward W (H.homSupply.axisComp W axis) = axis :=
  H.axis_hom_inv W axis

/-- The fiberwise observable inverse also cancels forward observable transport. -/
theorem observable_inverse_forward {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder)
    (observable : W.ctx.Observable) :
    H.observableInverseAtForward W
      (H.homSupply.observableComp W observable) = observable :=
  H.observable_hom_inv W observable

end RealizationExactUpperEquivalence

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
