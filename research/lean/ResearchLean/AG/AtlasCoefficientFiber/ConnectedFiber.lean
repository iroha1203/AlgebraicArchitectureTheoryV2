import ResearchLean.AG.AtlasCoefficientFiber.ConstantLimit

/-!
# G-135 A：局所包含の成分同定API

## Implementation notes

各対象への到達と、同じ対象へ至る二つの原像のzigzag連結性から、
mathlib ConnectedComponentsの両方向同型を構成する。
成分全単射そのものをfieldに置く案は採らない。二条件は一般APIの方向仮定であり、
原始Φ・Γへの適用では別々にセルincidenceから放電する必要がある。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory
universe u
variable {J K : Type u} [Category.{u} J] [Category.{u} K]

/-- 共通の行先への到達と原像の連結性から、局所包含の成分全単射を構成する一般API。 -/
def componentEquivOfCommonTargets (F : J ⥤ K)
    (hr : ∀ y : K, ∃ x : J, Nonempty (F.obj x ⟶ y))
    (hu : ∀ y : K, ∀ x x' : J, (F.obj x ⟶ y) → (F.obj x' ⟶ y) → Zigzag x x') :
    CategoryTheory.ConnectedComponents J ≃ CategoryTheory.ConnectedComponents K where
  toFun := F.mapConnectedComponents
  invFun := Quotient.lift (fun y => CategoryTheory.ConnectedComponents.mk (hr y).choose)
    (fun _ _ hh => invariant_of_zigzag
      (fun y => CategoryTheory.ConnectedComponents.mk (hr y).choose)
      (fun {y z} f => Quotient.sound
        (hu z (hr y).choose (hr z).choose
          ((Classical.choice (hr y).choose_spec) ≫ f) (Classical.choice (hr z).choose_spec))) hh)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | h j =>
      exact Quotient.sound (hu (F.obj j) (hr (F.obj j)).choose j
        (Classical.choice (hr (F.obj j)).choose_spec) (𝟙 _))
  right_inv x := by
    induction x using Quotient.inductionOn with
    | h y =>
      exact Quotient.sound (Zigzag.of_hom (Classical.choice (hr y).choose_spec))

/-- 成分同型の順向きは入力関手の標準成分写像。定義所有者API。 -/
@[simp] theorem componentEquivOfCommonTargets_apply (F : J ⥤ K)
    (hr : ∀ y : K, ∃ x : J, Nonempty (F.obj x ⟶ y))
    (hu : ∀ y : K, ∀ x x' : J, (F.obj x ⟶ y) → (F.obj x' ⟶ y) → Zigzag x x')
    (x : CategoryTheory.ConnectedComponents J) :
    componentEquivOfCommonTargets F hr hu x = F.mapConnectedComponents x := rfl

/-- 成分同型の逆向きは到達producerの原像成分。選択の値ではなく成分が一意となる。 -/
@[simp] theorem componentEquivOfCommonTargets_symm_mk (F : J ⥤ K)
    (hr : ∀ y : K, ∃ x : J, Nonempty (F.obj x ⟶ y))
    (hu : ∀ y : K, ∀ x x' : J, (F.obj x ⟶ y) → (F.obj x' ⟶ y) → Zigzag x x') (y : K) :
    (componentEquivOfCommonTargets F hr hu).symm (CategoryTheory.ConnectedComponents.mk y) =
      CategoryTheory.ConnectedComponents.mk (hr y).choose := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.componentEquivOfCommonTargets
#print axioms AAT.AG.AtlasCoefficientFiber.componentEquivOfCommonTargets_apply
#print axioms AAT.AG.AtlasCoefficientFiber.componentEquivOfCommonTargets_symm_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
