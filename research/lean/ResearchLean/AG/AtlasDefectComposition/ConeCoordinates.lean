import ResearchLean.AG.AtlasDefectComposition.ZeroExtension
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Formal.Util.AssertStandardAxioms
/-! # 標準錐の成分と符号

G-133 CのD(u)^m=C'^m×C^(m+1)を標準mappingConeの全次数へ同定する。

Implementation notes: 既存mappingConeのinr/inlとsnd/fstからLinearEquivを作り、
source-shift/targetの標準biproduct順序をtarget/sourceへ明示交換する。
別の閉じた錐recordは作らない。零延長以外の標準複体にも使えるAPIとする。
-/

noncomputable section
open CategoryTheory Limits HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open CochainComplex
universe w
variable {F G : CochainComplex (ModuleCat.{w} ℚ) ℤ} (φ : F ⟶ G)
/-- 標準錐の次数別成分をカードCのtarget/source順序へ交換する両方向同型。 -/
def coneCoordinateEquiv (m : ℤ) :
    (mappingCone φ).X m ≃ₗ[ℚ] G.X m × F.X (m + 1) where
  toFun z := ((mappingCone.snd φ).v m m (by simp) z,
    (mappingCone.fst φ).1.v m (m+1) rfl z)
  invFun p := (mappingCone.inr φ).f m p.1 +
    (mappingCone.inl φ).v (m+1) m (by simp) p.2
  left_inv z := by
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ (mappingCone φ).X m => f z)
      (mappingCone.id_X φ m (m+1) rfl)
    simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply, add_comm] using h
  right_inv p := by
    apply Prod.ext <;> dsimp only <;>
      simp only [map_add, ← ModuleCat.comp_apply, mappingCone.inl_v_snd_v,
        mappingCone.inl_v_fst_v, mappingCone.inr_f_snd_v, mappingCone.inr_f_fst_v,
        ModuleCat.hom_zero, LinearMap.zero_apply, ModuleCat.id_apply, zero_add, add_zero]
  map_add' x y := by ext <;> simp
  map_smul' r x := by ext <;> simp

/-- Cのtarget成分は標準錐のsecond projectionで読む。 -/
@[simp] theorem coneCoordinateEquiv_snd (m : ℤ) (z : (mappingCone φ).X m) :
    (coneCoordinateEquiv φ m z).1 = (mappingCone.snd φ).v m m (by simp) z := rfl
/-- Cのshifted source成分は標準錐のfirst projectionで読む。 -/
@[simp] theorem coneCoordinateEquiv_fst (m : ℤ) (z : (mappingCone φ).X m) :
    (coneCoordinateEquiv φ m z).2 = (mappingCone.fst φ).1.v m (m+1) rfl z := rfl

/-- 次数別同型の逆構成はtarget成分をそのまま復元する。 -/
@[simp] theorem coneCoordinateEquiv_symm_snd (m : ℤ) (p : G.X m × F.X (m+1)) :
    (mappingCone.snd φ).v m m (by simp) ((coneCoordinateEquiv φ m).symm p) = p.1 := by
  have h := congrArg Prod.fst ((coneCoordinateEquiv φ m).apply_symm_apply p)
  exact h
/-- 次数別同型の逆構成はshifted source成分をそのまま復元する。 -/
@[simp] theorem coneCoordinateEquiv_symm_fst (m : ℤ) (p : G.X m × F.X (m+1)) :
    (mappingCone.fst φ).1.v m (m+1) rfl ((coneCoordinateEquiv φ m).symm p) = p.2 := by
  have h := congrArg Prod.snd ((coneCoordinateEquiv φ m).apply_symm_apply p)
  exact h

/-- カードCの順序と負号の微分を、標準錐の両projection APIから全整数次数で導く。 -/
theorem coneCoordinateEquiv_d (m : ℤ) (p : G.X m × F.X (m+1)) :
    coneCoordinateEquiv φ (m+1)
      ((mappingCone φ).d m (m+1) ((coneCoordinateEquiv φ m).symm p)) =
      (G.d m (m+1) p.1 + φ.f (m+1) p.2, -F.d (m+1) (m+1+1) p.2) := by
  apply Prod.ext
  · rw [coneCoordinateEquiv_snd]
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ G.X (m+1) =>
      f ((coneCoordinateEquiv φ m).symm p)) (mappingCone.d_snd_v φ m (m+1) rfl)
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      coneCoordinateEquiv_symm_snd, coneCoordinateEquiv_symm_fst, add_comm] using h
  · rw [coneCoordinateEquiv_fst]
    have h := congrArg (fun f : (mappingCone φ).X m ⟶ F.X (m+1+1) =>
      f ((coneCoordinateEquiv φ m).symm p))
        (mappingCone.d_fst_v φ m (m+1) (m+1+1) rfl rfl)
    simpa only [ModuleCat.comp_apply, ModuleCat.hom_neg, LinearMap.neg_apply,
      coneCoordinateEquiv_symm_fst, map_neg] using h

/-- T0の実生成Homを零延長した標準写像錐。 -/
def comparisonCone {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : CochainComplex (ModuleCat.{w} ℚ) ℤ :=
  mappingCone (zeroExtensionMap f)

/-- 有限次元のsource/target次数から標準錐の同じ次数の有限次元性を導く。 -/
instance coneDegreeFiniteDimensional (m : ℤ)
    [FiniteDimensional ℚ (F.X (m+1))] [FiniteDimensional ℚ (G.X m)] :
    FiniteDimensional ℚ ((mappingCone φ).X m) :=
  FiniteDimensional.of_injective (coneCoordinateEquiv φ m).toLinearMap
    (coneCoordinateEquiv φ m).injective

/-- 三項複体の比較錐は次数-1/0/1/2以外に零対象を持つ。 -/
theorem comparisonCone_isZero {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) (m : ℤ)
    (hneg : m ≠ -1) (h₀ : m ≠ 0) (h₁ : m ≠ 1) (h₂ : m ≠ 2) :
    IsZero ((comparisonCone f).X m) := by
  apply (mappingCone.isZero_X_iff (zeroExtensionMap f) m).mpr
  constructor
  · exact degreeObject_isZero C (m+1) (by omega) (by omega) (by omega)
  · exact degreeObject_isZero D m h₀ h₁ h₂

/-- 次数-1の標準錐は元のsource次数0に一致する。 -/
def comparisonConeMinusOneEquiv {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : (comparisonCone f).X (-1) ≃ₗ[ℚ] C.C0 := by
  letI : Subsingleton ((zeroExtension D).X (-1)) := by
    apply ModuleCat.subsingleton_of_isZero
    simpa only [zeroExtension_X] using
      (degreeObject_isZero D (-1) (by decide) (by decide) (by decide))
  letI : Unique ((zeroExtension D).X (-1)) := { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  exact (coneCoordinateEquiv (zeroExtensionMap f) (-1)).trans
    (LinearEquiv.uniqueProd (R := ℚ))

/-- 次数0の標準錐はtarget次数0とsource次数1の積である。 -/
def comparisonConeZeroEquiv {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : (comparisonCone f).X 0 ≃ₗ[ℚ] D.C0 × C.C1 :=
  coneCoordinateEquiv (zeroExtensionMap f) 0

/-- 次数1の標準錐はtarget次数1とsource次数2の積である。 -/
def comparisonConeOneEquiv {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : (comparisonCone f).X 1 ≃ₗ[ℚ] D.C1 × C.C2 :=
  coneCoordinateEquiv (zeroExtensionMap f) 1

/-- 次数2の標準錐は元のtarget次数2に一致する。 -/
def comparisonConeTwoEquiv {C D : TwoPhase.ThreeCochainComplex.{0,w} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) : (comparisonCone f).X 2 ≃ₗ[ℚ] D.C2 := by
  letI : Subsingleton ((zeroExtension C).X (2+1)) := by
    apply ModuleCat.subsingleton_of_isZero
    simpa only [zeroExtension_X] using
      (degreeObject_isZero C (2+1) (by decide) (by decide) (by decide))
  letI : Unique ((zeroExtension C).X (2+1)) := { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  exact (coneCoordinateEquiv (zeroExtensionMap f) 2).trans
    (LinearEquiv.prodUnique (R := ℚ))

end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
