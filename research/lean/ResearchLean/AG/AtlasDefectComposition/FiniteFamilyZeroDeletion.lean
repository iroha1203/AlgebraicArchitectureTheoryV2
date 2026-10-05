import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Formal.Util.AssertStandardAxioms
/-! # 零成分を除く有限複体族の指定同型

Implementation notes: 実座標制限の逆は除いた座標への零延長である。
除いた各実加群の零性を必要条件として明示し、実署名適用で放電する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.FiniteFamilyZeroDeletion
attribute [local instance] Classical.propDecidable
universe u v
variable {J : Type u} (F : J → CochainComplex (ModuleCat.{max u v} ℚ) ℤ)
variable (p : J → Prop)
/-- 指定成分だけを保持する元の座標制限。 -/
def restrictDegree (m : ℤ) : ((j : J) → (F j).X m) →ₗ[ℚ] ((j : Subtype p) → (F j.1).X m) :=
  LinearMap.pi (fun j => LinearMap.proj j.1)
/-- 実成分制限の元評価。 -/
@[simp] theorem restrictDegree_apply (m : ℤ) (x : (j : J) → (F j).X m) (j : Subtype p) :
    restrictDegree F p m x j = x j.1 := rfl
/-- 除いた成分を零で復元する指定座標射。 -/
def extendDegree (m : ℤ) : ((j : Subtype p) → (F j.1).X m) →ₗ[ℚ] ((j : J) → (F j).X m) := by
  classical
  exact LinearMap.pi (fun j : J => if h : p j then
    (LinearMap.proj (⟨j,h⟩ : Subtype p) : ((j : Subtype p) → (F j.1).X m) →ₗ[ℚ] (F j).X m) else 0)
/-- 零延長の元評価。成分選択以外に任意の値を補わない。 -/
@[simp] theorem extendDegree_apply (m : ℤ) (x : (j : Subtype p) → (F j.1).X m) (j : J) :
    extendDegree F p m x j = if h : p j then x ⟨j,h⟩ else 0 := by
  classical
  unfold extendDegree
  by_cases h : p j <;> simp [h]
variable (hzero : ∀ j, ¬ p j → ∀ m, Subsingleton ((F j).X m))
/-- 除いた成分の実零性から全次数の制限同値を生成する。 -/
def degreeEquiv (m : ℤ) : ((j : J) → (F j).X m) ≃ₗ[ℚ] ((j : Subtype p) → (F j.1).X m) :=
  LinearEquiv.ofLinear (restrictDegree F p m) (extendDegree F p m)
    (by
      classical
      ext x j
      simp only [LinearMap.comp_apply,restrictDegree_apply,extendDegree_apply,dif_pos j.2,LinearMap.id_apply])
    (by
      classical
      ext x j
      simp only [LinearMap.comp_apply,extendDegree_apply,restrictDegree_apply,LinearMap.id_apply]
      by_cases hj : p j
      · rw [dif_pos hj]
      · letI := hzero j hj m
        exact Subsingleton.elim _ _)
/-- 指定成分制限は元の成分微分と可換である。 -/
theorem degreeEquiv_d (m : ℤ) (x : (FiniteComplexFamily.complex F).X m) :
    degreeEquiv F p hzero (m+1) ((FiniteComplexFamily.complex F).d m (m+1) x) =
      (FiniteComplexFamily.complex (fun j : Subtype p => F j.1)).d m (m+1) (degreeEquiv F p hzero m x) := by
  funext j
  change restrictDegree F p (m+1) _ j = _
  simp only [restrictDegree_apply,FiniteComplexFamily.d_apply]
  rfl
/-- 除いた実成分が全次数で零なら、元の族から選択族への指定複体同型。 -/
def iso : FiniteComplexFamily.complex F ≅ FiniteComplexFamily.complex (fun j : Subtype p => F j.1) :=
  HomologicalComplex.Hom.isoOfComponents (fun m => (degreeEquiv F p hzero m).toModuleIso) (by
    intro m n h
    change m+1=n at h
    subst n
    ext x
    exact (degreeEquiv_d F p hzero m x).symm)
/-- 零成分削除の順射は元の指定座標制限そのものである。 -/
@[simp] theorem iso_apply (m : ℤ) (x : (FiniteComplexFamily.complex F).X m) (j : Subtype p) :
    (iso F p hzero).hom.f m x j = x j.1 := rfl
end AAT.AG.AtlasDefectComposition.FiniteFamilyZeroDeletion
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.FiniteFamilyZeroDeletion
