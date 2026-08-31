import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationFactorCarriers

/-!
# Naturality of realization-exact carrier inverses

The inverse-at-forward carrier maps used by a Cartesian factor must commute
with Support and Axis restriction and with contravariant Observable
restriction.  Injectivity of the forward realization maps reduces all three
claims to the reviewed forward naturality and cancellation laws.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory AtomFoundation GeometryTransport

set_option maxHeartbeats 3000000

namespace RealizationExactUpperEquivalence

/-- Forward support transport is injective at every source context. -/
theorem supportComp_injective {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) :
    Function.Injective (H.homSupply.supportComp W) := by
  intro left right h
  rw [← H.support_inverse_forward W left,
    ← H.support_inverse_forward W right, h]

/-- Forward axis transport is injective at every source context. -/
theorem axisComp_injective {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) :
    Function.Injective (H.homSupply.axisComp W) := by
  intro left right h
  rw [← H.axis_inverse_forward W left,
    ← H.axis_inverse_forward W right, h]

/-- Forward observable transport is injective at every source context. -/
theorem observableComp_injective {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    (W : Site.ContextCategoryObject P.contextPreorder) :
    Function.Injective (H.homSupply.observableComp W) := by
  intro left right h
  rw [← H.observable_inverse_forward W left,
    ← H.observable_inverse_forward W right, h]

/-- The support inverse-at-forward commutes with context restriction. -/
theorem supportInverseAtForward_naturality {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    {W V : Site.ContextCategoryObject P.contextPreorder} (w : W ⟶ V)
    (support : ((upperCoreContextFunctor e.forward).obj W).ctx.Support) :
    (P.contextPreorder.morphism (leOfHom w)).supportMap
        (H.supportInverseAtForward W support) =
      H.supportInverseAtForward V
        ((Q.contextPreorder.morphism
          (leOfHom ((upperCoreContextFunctor e.forward).map w))).supportMap
            support) := by
  apply H.supportComp_injective V
  rw [H.support_forward_inverse]
  rw [← H.homSupply.support_naturality w
    (H.supportInverseAtForward W support)]
  rw [H.support_forward_inverse]

/-- The axis inverse-at-forward commutes with context restriction. -/
theorem axisInverseAtForward_naturality {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    {W V : Site.ContextCategoryObject P.contextPreorder} (w : W ⟶ V)
    (axis : ((upperCoreContextFunctor e.forward).obj W).ctx.Axis) :
    (P.contextPreorder.morphism (leOfHom w)).axisMap
        (H.axisInverseAtForward W axis) =
      H.axisInverseAtForward V
        ((Q.contextPreorder.morphism
          (leOfHom ((upperCoreContextFunctor e.forward).map w))).axisMap axis) := by
  apply H.axisComp_injective V
  rw [H.axis_forward_inverse]
  rw [← H.homSupply.axis_naturality w (H.axisInverseAtForward W axis)]
  rw [H.axis_forward_inverse]

/-- The observable inverse-at-forward commutes with contravariant context
restriction. -/
theorem observableInverseAtForward_naturality {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {e : ExactUpperEquivalence P Q}
    (H : RealizationExactUpperEquivalence e)
    {W V : Site.ContextCategoryObject P.contextPreorder} (w : W ⟶ V)
    (observable : ((upperCoreContextFunctor e.forward).obj V).ctx.Observable) :
    (P.contextPreorder.morphism (leOfHom w)).observableRestrict
        (H.observableInverseAtForward V observable) =
      H.observableInverseAtForward W
        ((Q.contextPreorder.morphism
          (leOfHom ((upperCoreContextFunctor e.forward).map w))).observableRestrict
            observable) := by
  apply H.observableComp_injective W
  rw [H.observable_forward_inverse]
  rw [← H.homSupply.observable_naturality w
    (H.observableInverseAtForward V observable)]
  rw [H.observable_forward_inverse]

end RealizationExactUpperEquivalence

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
