import ResearchLean.AG.RelativeRepairComposition.W5LocalRepairs
import Mathlib.CategoryTheory.Discrete.Basic

/-! # The complete original W5 overlap groupoid and every actual label

Both endpoints are physically fixed, so every full original vertex label is
zero. All overlap repair values remain distinct objects. The entire original
actual overlap groupoid is discrete F2 with both object and hom inverses.
-/
namespace AAT.AG.RelativeRepairComposition.W5ActualArrows
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations W5ActualRepairs W5LocalRepairs
attribute [local instance] W5LocalRepairs.globalAction W5LocalRepairs.localAction
variable (b₁ b₂ : ZMod 2)
/-- Every original global actual label vanishes at all physical endpoints. -/
theorem global_label_zero
    (a : gaugeLabels geometry (reference b₁ b₂) fixedRegion.vertices fixedRegion.edges) : a = 0 := by
  apply Subtype.ext
  funext v
  exact a.2.1 v (Set.mem_univ _)
/-- Every full local actual arrow retains the zero original label at every selected vertex. -/
theorem local_arrow_label (U : ClosedRegion geometry) {R Q : LocalCategory b₁ b₂ U} (f : R ⟶ Q) :
    f.1.toAdd = 0 := labels_zero b₁ b₂ U _
/-- A local actual arrow exists only between literally equal complete original repair objects. -/
theorem local_object_eq (U : ClosedRegion geometry) {R Q : LocalCategory b₁ b₂ U} (f : R ⟶ Q) : R = Q := by
  have hl : (show Multiplicative (LocalLabels b₁ b₂ U) from f.1) =
      (1 : Multiplicative (LocalLabels b₁ b₂ U)) :=
    Multiplicative.toAdd.injective (local_arrow_label b₁ b₂ U f)
  have hf := f.2
  change (show Multiplicative (LocalLabels b₁ b₂ U) from f.1) • R.back = Q.back at hf
  rw [hl,one_smul] at hf
  rcases R with ⟨r,R⟩
  rcases Q with ⟨q,Q⟩
  cases r
  cases q
  exact congrArg (fun X : LocalRepairs b₁ b₂ U => (X : LocalCategory b₁ b₂ U)) hf
/-- Every local actual hom-set retains all original permitted arrows and has at most one arrow. -/
theorem local_hom_unique (U : ClosedRegion geometry) {R Q : LocalCategory b₁ b₂ U} (f g : R ⟶ Q) : f = g := by
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  rw [local_arrow_label b₁ b₂ U f,local_arrow_label b₁ b₂ U g]
/-- The entire actual overlap categorical object family has both inverse F2 coordinates. -/
noncomputable def overlapObjectEquiv : LocalCategory b₁ b₂ overlap ≃ ZMod 2 where
  toFun R := overlapValueEquiv b₁ b₂ R.back
  invFun u := ((overlapValueEquiv b₁ b₂).symm u : LocalCategory b₁ b₂ overlap)
  left_inv R := by
    rcases R with ⟨r,R⟩
    cases r
    exact congrArg (fun X : LocalRepairs b₁ b₂ overlap => (X : LocalCategory b₁ b₂ overlap))
      ((overlapValueEquiv b₁ b₂).symm_apply_apply R)
  right_inv u := (overlapValueEquiv b₁ b₂).apply_symm_apply u
/-- Whole overlap arrows exist exactly when the actual original shared values coincide. -/
theorem overlap_hom_iff (R Q : LocalCategory b₁ b₂ overlap) :
    Nonempty (R ⟶ Q) ↔ overlapObjectEquiv b₁ b₂ R = overlapObjectEquiv b₁ b₂ Q := by
  constructor
  · rintro ⟨f⟩
    exact congrArg (overlapObjectEquiv b₁ b₂) (local_object_eq b₁ b₂ overlap f)
  · intro h
    have hq : R = Q := (overlapObjectEquiv b₁ b₂).injective h
    subst Q
    exact ⟨𝟙 R⟩
/-- A categorical value preserved by every full arrow defines a functor to its discrete value category. -/
def discreteValueFunctor {C : Type*} [Category C] {D : Type*} (v : C → D)
    (hv : ∀ {R Q : C}, (R ⟶ Q) → v R = v Q) : C ⥤ Discrete D where
  obj R := Discrete.mk (v R)
  map f := Discrete.eqToHom' (hv f)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _
/-- Reading the whole actual shared value maps every original overlap arrow to the discrete equality. -/
noncomputable def overlapFunctor : LocalCategory b₁ b₂ overlap ⥤ Discrete (ZMod 2) :=
  discreteValueFunctor (overlapObjectEquiv b₁ b₂)
    (fun f => congrArg (overlapObjectEquiv b₁ b₂) (local_object_eq b₁ b₂ overlap f))
/-- The complete original overlap groupoid is discrete F2 on all actual objects and every full arrow. -/
noncomputable def overlapDiscreteEquivalence : LocalCategory b₁ b₂ overlap ≌ Discrete (ZMod 2) := by
  let F := overlapFunctor b₁ b₂
  letI : F.Full := {
    map_surjective := by
      intro R Q f
      exact ⟨((overlap_hom_iff b₁ b₂ R Q).mpr (Discrete.eq_of_hom f)).some,Subsingleton.elim _ _⟩ }
  letI : F.Faithful := {
    map_injective := by
      intro R Q f g _
      exact local_hom_unique b₁ b₂ overlap f g }
  letI : F.EssSurj := {
    mem_essImage := by
      intro u
      refine ⟨(overlapObjectEquiv b₁ b₂).symm u.as,⟨?_⟩⟩
      exact eqToIso (by
        change Discrete.mk ((overlapObjectEquiv b₁ b₂) ((overlapObjectEquiv b₁ b₂).symm u.as)) = u
        rw [Equiv.apply_symm_apply]) }
  letI : F.IsEquivalence := {}
  exact F.asEquivalence

end AAT.AG.RelativeRepairComposition.W5ActualArrows
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5ActualArrows
