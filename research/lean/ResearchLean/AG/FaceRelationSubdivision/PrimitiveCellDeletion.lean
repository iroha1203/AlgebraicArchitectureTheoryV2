import ResearchLean.AG.FaceRelationSubdivision.CellPresentationEquiv
import Formal.Util.AssertStandardAxioms

/-!
# 指定セルを除いた名前の復元

## Implementation notes

原始名から除外部分型を作り、直和のfreshタグを除いた元の名前へ戻す。
旧入力や表示同型を供給する案を採らず、名前の等号判定だけで両逆を構成する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
universe u

/-- 一つの原始セル名を除外した部分型とfreshタグから元の全名前を復元する。 -/
def deleteOneEquiv {I : Type u} (x : I) : ({i : I // i ≠ x} ⊕ PUnit.{u+1}) ≃ I := by
  classical
  exact {
    toFun := fun i => match i with | .inl i => i.1 | .inr _ => x
    invFun := fun i => if h : i = x then .inr PUnit.unit else .inl ⟨i, h⟩
    left_inv := by
      rintro (i | a)
      · simp [i.2]
      · cases a; simp
    right_inv := by intro i; dsimp only; split_ifs with h; exact h.symm; rfl }

/-- 保持した名前は変更しない。 -/
@[simp] theorem deleteOneEquiv_old {I : Type u} (x : I) (i : {i : I // i ≠ x}) :
    deleteOneEquiv x (.inl i) = i.1 := rfl
/-- freshタグは指定された削除名へ戻す。 -/
@[simp] theorem deleteOneEquiv_new {I : Type u} (x : I) :
    deleteOneEquiv x (.inr PUnit.unit) = x := rfl

/-- 二つの異なる削除名を、保持名前と二つのfreshタグから復元する。 -/
def deleteTwoEquiv {I : Type u} (x y : I) (hxy : x ≠ y) :
    ({i : I // i ≠ x ∧ i ≠ y} ⊕ Bool) ≃ I := by
  classical
  exact {
    toFun := fun i => match i with | .inl i => i.1 | .inr false => x | .inr true => y
    invFun := fun i => if hx : i = x then .inr false
      else if hy : i = y then .inr true else .inl ⟨i, hx, hy⟩
    left_inv := by
      rintro (i | a)
      · simp [i.2.1, i.2.2]
      · cases a
        · simp
        · simp [Ne.symm hxy]
    right_inv := by
      intro i
      dsimp only
      split_ifs with hx hy
      · exact hx.symm
      · exact hy.symm
      · rfl }

/-- 二名削除でも保持した名前を変更しない。 -/
@[simp] theorem deleteTwoEquiv_old {I : Type u} (x y : I) (hxy : x ≠ y)
    (i : {i : I // i ≠ x ∧ i ≠ y}) : deleteTwoEquiv x y hxy (.inl i) = i.1 := rfl
/-- 第0タグの原始名。 -/
@[simp] theorem deleteTwoEquiv_false {I : Type u} (x y : I) (hxy : x ≠ y) :
    deleteTwoEquiv x y hxy (.inr false) = x := rfl
/-- 第1タグの原始名。 -/
@[simp] theorem deleteTwoEquiv_true {I : Type u} (x y : I) (hxy : x ≠ y) :
    deleteTwoEquiv x y hxy (.inr true) = y := rfl

/-- 単射な指定削除名の族を、保持部分型と同じ族のfreshタグで復元する。 -/
def deleteFamilyEquiv {I J : Type u} (f : J → I) (hf : Function.Injective f) :
    ({i : I // ∀ j, i ≠ f j} ⊕ J) ≃ I := by
  classical
  exact {
    toFun := fun i => match i with | .inl i => i.1 | .inr j => f j
    invFun := fun i => if h : ∃ j, f j = i then .inr (Classical.choose h)
      else .inl ⟨i, fun j hj => h ⟨j, hj.symm⟩⟩
    left_inv := by
      rintro (i | j)
      · dsimp only
        split_ifs with h
        · obtain ⟨j, hj⟩ := h; exact False.elim (i.2 j hj.symm)
        · rfl
      · dsimp only
        split_ifs with h
        · congr 1; exact hf (Classical.choose_spec h)
        · exact False.elim (h ⟨j, rfl⟩)
    right_inv := by
      intro i
      dsimp only
      split_ifs with h
      · exact Classical.choose_spec h
      · rfl }

/-- 保持名の計算成分。 -/
@[simp] theorem deleteFamilyEquiv_old {I J : Type u} (f : J → I) (hf : Function.Injective f)
    (i : {i : I // ∀ j, i ≠ f j}) : deleteFamilyEquiv f hf (.inl i) = i.1 := rfl
/-- 各freshタグは同じ指定名へ戻す。 -/
@[simp] theorem deleteFamilyEquiv_new {I J : Type u} (f : J → I) (hf : Function.Injective f)
    (j : J) : deleteFamilyEquiv f hf (.inr j) = f j := rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
