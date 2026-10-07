import ResearchLean.AG.AtlasCoefficientFiber.DegenerateSubcomplex
import ResearchLean.AG.AtlasDefectComposition.EndpointHomology
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# G-135 A・B：Q=L*と同じ細cochainの制限

## Implementation notes

Qは原始Lの実制限微分を双対化して作る。細側の独立したcochainからの射は
同じ自由chain双対同型とSubmodule.dualRestrictで生成する。
各次数の全射性は体上の双対制限の一般定理から得る。
H⁰Qの零性はL₁→L₀の原始全射性から導き、入力certificateには置かない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- Lの二微分を双対化すると、同じsquare-zeroによりcochain条件が成立する。 -/
theorem restrictionDifferential_square (z : Module.Dual ℚ (degenerateL0 M A)) :
    (degenerateBoundary2 M A).dualMap ((degenerateBoundary1 M A).dualMap z) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply]
  have hx := LinearMap.congr_fun (degenerateBoundary_square M A) x
  rw [LinearMap.comp_apply, LinearMap.zero_apply] at hx
  rw [hx, map_zero, LinearMap.zero_apply]

/-- Q_Aは指定L_Aの同じ微分の有限ℚ双対複体。 -/
abbrev restrictionComplex : ThreeCochainComplex ℚ where
  C0 := Module.Dual ℚ (degenerateL0 M A)
  C1 := Module.Dual ℚ (degenerateL1 M A)
  C2 := Module.Dual ℚ (degenerateL2 M A)
  d0 := (degenerateBoundary1 M A).dualMap
  d1 := (degenerateBoundary2 M A).dualMap
  d1_comp_d0 := restrictionDifferential_square M A

/-- Qの第一微分は同じL境界で評価する。 -/
@[simp] theorem restrictionComplex_d0_apply (z : Module.Dual ℚ (degenerateL0 M A))
    (x : degenerateL1 M A) :
    ((restrictionComplex M A).d0 z : Module.Dual ℚ (degenerateL1 M A)) x = z (degenerateBoundary1 M A x) := rfl

/-- Qの第二微分は同じL境界で評価する。 -/
@[simp] theorem restrictionComplex_d1_apply (z : Module.Dual ℚ (degenerateL1 M A))
    (x : degenerateL2 M A) :
    ((restrictionComplex M A).d1 z : Module.Dual ℚ (degenerateL2 M A)) x = z (degenerateBoundary2 M A x) := rfl

/-- 細次数0 cochainを同じL₀へ制限する。 -/
def restriction0 : (Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) →ₗ[ℚ]
    (restrictionComplex M A).C0 :=
  (degenerateL0 M A).dualRestrict.comp (freeDualEquiv _).toLinearMap

/-- 細次数1 cochainを同じL₁へ制限する。 -/
def restriction1 : (Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) →ₗ[ℚ]
    (restrictionComplex M A).C1 :=
  (degenerateL1 M A).dualRestrict.comp (freeDualEquiv _).toLinearMap

/-- 細次数2 cochainを同じL₂へ制限する。 -/
def restriction2 : (Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) →ₗ[ℚ]
    (restrictionComplex M A).C2 :=
  (degenerateL2 M A).dualRestrict.comp (freeDualEquiv _).toLinearMap

/-- 次数0の制限は元の同じchain上での双対評価。 -/
@[simp] theorem restriction0_apply
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : degenerateL0 M A) :
    (restriction0 M A z : Module.Dual ℚ (degenerateL0 M A)) x = freeDualEquiv _ z x.1 := rfl

/-- 次数1の制限は元の同じchain上での双対評価。 -/
@[simp] theorem restriction1_apply
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : degenerateL1 M A) :
    (restriction1 M A z : Module.Dual ℚ (degenerateL1 M A)) x = freeDualEquiv _ z x.1 := rfl

/-- 次数2の制限は元の同じchain上での双対評価。 -/
@[simp] theorem restriction2_apply
    (z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) (x : degenerateL2 M A) :
    (restriction2 M A z : Module.Dual ℚ (degenerateL2 M A)) x = freeDualEquiv _ z x.1 := rfl

/-- 体上の双対制限の全射性から次数0制限を全射とする。 -/
theorem restriction0_surjective : Function.Surjective (restriction0 M A) :=
  (Subspace.dualRestrict_surjective (W := degenerateL0 M A)).comp (freeDualEquiv _).surjective

/-- 体上の双対制限の全射性から次数1制限を全射とする。 -/
theorem restriction1_surjective : Function.Surjective (restriction1 M A) :=
  (Subspace.dualRestrict_surjective (W := degenerateL1 M A)).comp (freeDualEquiv _).surjective

/-- 体上の双対制限の全射性から次数2制限を全射とする。 -/
theorem restriction2_surjective : Function.Surjective (restriction2 M A) :=
  (Subspace.dualRestrict_surjective (W := degenerateL2 M A)).comp (freeDualEquiv _).surjective

/-- 元の同じ支持chain双対式による、制限の第一cochain条件。 -/
theorem restriction_comm0
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C0) :
    restriction1 M A ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d0 z) =
      (restrictionComplex M A).d0 (restriction0 M A z) := by
  apply LinearMap.ext
  intro x
  rw [restriction1_apply, restrictionComplex_d0_apply, restriction0_apply, degenerateBoundary1_val]
  exact (chainD1_dual Nf (comparisonFactor qc qf h ⁻¹' A) z x.1).symm

/-- 元の同じ支持chain双対式による、制限の第二cochain条件。 -/
theorem restriction_comm1
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1) :
    restriction2 M A ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 z) =
      (restrictionComplex M A).d1 (restriction1 M A z) := by
  apply LinearMap.ext
  intro x
  rw [restriction2_apply, restrictionComplex_d1_apply, restriction1_apply, degenerateBoundary2_val]
  exact (chainD2_dual Nf (comparisonFactor qc qf h ⁻¹' A) z x.1).symm

/-- 細側の実cochainからQへ、同じ三次数制限で生成した射。 -/
def restrictionHom : ThreeCochainComplex.Hom
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) (restrictionComplex M A) where
  f0 := restriction0 M A
  f1 := restriction1 M A
  f2 := restriction2 M A
  comm0 := restriction_comm0 M A
  comm1 := restriction_comm1 M A

/-- 制限射の次数0計算成分。 -/
@[simp] theorem restrictionHom_f0 : (restrictionHom M A).f0 = restriction0 M A := rfl
/-- 制限射の次数1計算成分。 -/
@[simp] theorem restrictionHom_f1 : (restrictionHom M A).f1 = restriction1 M A := rfl
/-- 制限射の次数2計算成分。 -/
@[simp] theorem restrictionHom_f2 : (restrictionHom M A).f2 = restriction2 M A := rfl

/-- L₁→L₀の原始全射性によりQの第一微分は単射。 -/
theorem restrictionComplex_d0_injective : Function.Injective (restrictionComplex M A).d0 := by
  intro z w hz
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := degenerateBoundary1_surjective M A y
  exact LinearMap.congr_fun hz x

/-- Qの第一微分の核は零部分空間。 -/
theorem restrictionComplex_d0_ker : LinearMap.ker (restrictionComplex M A).d0 = ⊥ :=
  LinearMap.ker_eq_bot.mpr (restrictionComplex_d0_injective M A)

/-- 原始Lの全射性から、標準ℤ添字homologyとしてH⁰Q=0を導く。 -/
theorem restrictionComplex_H0_isZero :
    Limits.IsZero ((zeroExtension (restrictionComplex M A)).homology (0 : ℤ)) := by
  letI : Subsingleton (LinearMap.ker (restrictionComplex M A).d0) :=
    Submodule.subsingleton_iff_eq_bot.mpr (restrictionComplex_d0_ker M A)
  exact Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (oldH0Iso (restrictionComplex M A)).symm

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.restrictionDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex_d0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex_d1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.restriction_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.restriction_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionHom
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex_d0_injective
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex_d0_ker
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionComplex_H0_isZero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
