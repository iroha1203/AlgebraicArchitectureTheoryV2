import ResearchLean.AG.AtlasDefectComposition.WitnessThreeInput
import ResearchLean.AG.AtlasDefectComposition.FullSupportIncidence
import ResearchLean.AG.AtlasDefectComposition.HomologyDimensions
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation
import Mathlib.Data.Fin.VecNotation
import Formal.Util.AssertStandardAxioms
/-! # W3bの実incidenceの核・像

rankを供給せず、原始端点・面の差分から定数核と三つの自由面成分を構成する。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open CanonicalResolution ResolutionInvariance TwoPhase
/-- W3b粗側d⁰の核を定数値へ同定する。 -/
def tetrahedronConstants : LinearMap.ker (namedComplex B₀).d0 ≃ₗ[ℚ] ℚ where
  toFun x := x.val 0
  invFun r := ⟨fun _ => r,by
    apply (mem_ker_namedComplex_d0_iff B₀ _).mpr
    intro e
    exact sub_self r⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have h (e : Fin 6) : x.val (tetrahedron.edgeRight e) -
        x.val (tetrahedron.edgeLeft e) = 0 :=
      (mem_ker_namedComplex_d0_iff B₀ x.val).mp x.property e
    fin_cases i
    · rfl
    · exact (sub_eq_zero.mp (h 0)).symm
    · exact (sub_eq_zero.mp (h 1)).symm
    · exact (sub_eq_zero.mp (h 2)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- W3b細側d⁰の核を定数値へ同定する。 -/
def triangleConstants : LinearMap.ker (namedComplex B₁).d0 ≃ₗ[ℚ] ℚ where
  toFun x := x.val 0
  invFun r := ⟨fun _ => r,by
    apply (mem_ker_namedComplex_d0_iff B₁ _).mpr
    intro e
    exact sub_self r⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    have h (e : Fin 3) : x.val (filledTriangle.edgeRight e)-
        x.val (filledTriangle.edgeLeft e)=0 :=
      (mem_ker_namedComplex_d0_iff B₁ x.val).mp x.property e
    fin_cases i
    · rfl
    · exact (sub_eq_zero.mp (h 0)).symm
    · exact (sub_eq_zero.mp (h 1)).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 四面体の面像は先頭三面を自由に持ち、第四面を交代和で復元する。 -/
def tetrahedronFaceImage : LinearMap.range (namedComplex B₀).d1 ≃ₗ[ℚ] (Fin 3 → ℚ) where
  toFun x := ![x.val 0,x.val 1,x.val 2]
  invFun a := ⟨![a 0,a 1,a 2,a 0-a 1+a 2],by
    refine ⟨![0,0,0,a 0,a 1,a 2],?_⟩
    funext f
    fin_cases f <;> simp only [namedComplex_d1_apply] <;> simp⟩
  left_inv x := by
    apply Subtype.ext
    obtain ⟨z,hz⟩ := x.property
    have hv : x.val = (namedComplex B₀).d1 z := hz.symm
    change ![x.val 0,x.val 1,x.val 2,x.val 0-x.val 1+x.val 2] = x.val
    rw [hv]
    funext f
    fin_cases f <;> simp only [namedComplex_d1_apply] <;> simp
    ring
  right_inv a := by funext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl
  map_smul' _ _ := by ext i; fin_cases i <;> rfl
/-- 充填三角形の実面差分は全射である。 -/
theorem triangleFace_surjective : Function.Surjective (namedComplex B₁).d1 := by
  intro z
  refine ⟨![0,0,z 0],?_⟩
  funext f
  fin_cases f
  simp only [namedComplex_d1_apply]
  simp
/-- 四面体の原始d⁰のrankは3。 -/
theorem tetrahedron_d0_rank : Module.finrank ℚ (LinearMap.range (namedComplex B₀).d0) = 3 := by
  have h := (namedComplex B₀).d0.finrank_range_add_finrank_ker
  have hk := tetrahedronConstants.finrank_eq
  simp only [Module.finrank_self] at hk
  have hc : Module.finrank ℚ (namedComplex B₀).C0 = 4 := by
    change Module.finrank ℚ (Fin 4 → ℚ) = 4
    simp
  omega
/-- 四面体の原始d¹のrankは3。 -/
theorem tetrahedron_d1_rank : Module.finrank ℚ (LinearMap.range (namedComplex B₀).d1) = 3 := by
  rw [tetrahedronFaceImage.finrank_eq]
  simp
/-- 充填三角形の原始d⁰のrankは2。 -/
theorem triangle_d0_rank : Module.finrank ℚ (LinearMap.range (namedComplex B₁).d0) = 2 := by
  have h := (namedComplex B₁).d0.finrank_range_add_finrank_ker
  have hk := triangleConstants.finrank_eq
  simp only [Module.finrank_self] at hk
  have hc : Module.finrank ℚ (namedComplex B₁).C0 = 3 := by
    change Module.finrank ℚ (Fin 3 → ℚ) = 3
    simp
  omega
/-- 充填三角形の原始d¹のrankは1。 -/
theorem triangle_d1_rank : Module.finrank ℚ (LinearMap.range (namedComplex B₁).d1) = 1 := by
  rw [LinearMap.range_eq_top.mpr triangleFace_surjective]
  change Module.finrank ℚ (⊤ : Submodule ℚ (Fin 1 → ℚ)) = 1
  simp
/-- 四面体の指定三項複体の全homology次元。 -/
theorem tetrahedron_homology_dimensions :
    Module.finrank ℚ ((zeroExtension (namedComplex B₀)).homology 0) = 1 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex B₀)).homology 1) = 0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex B₀)).homology 2) = 1 := by
  have h0 := standardH0_dimension (namedComplex B₀)
  have h1 := standardH1_dimension (namedComplex B₀)
  have h2 := standardH2_dimension (namedComplex B₀)
  rw [tetrahedron_d0_rank] at h0
  rw [tetrahedron_d0_rank,tetrahedron_d1_rank] at h1
  rw [tetrahedron_d1_rank] at h2
  have c0 : Module.finrank ℚ (namedComplex B₀).C0 = 4 := by change Module.finrank ℚ (Fin 4 → ℚ)=4; simp
  have c1 : Module.finrank ℚ (namedComplex B₀).C1 = 6 := by change Module.finrank ℚ (Fin 6 → ℚ)=6; simp
  have c2 : Module.finrank ℚ (namedComplex B₀).C2 = 4 := by change Module.finrank ℚ (Fin 4 → ℚ)=4; simp
  omega
/-- 充填三角形の指定三項複体の全homology次元。 -/
theorem triangle_homology_dimensions :
    Module.finrank ℚ ((zeroExtension (namedComplex B₁)).homology 0) = 1 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex B₁)).homology 1) = 0 ∧
    Module.finrank ℚ ((zeroExtension (namedComplex B₁)).homology 2) = 0 := by
  have h0 := standardH0_dimension (namedComplex B₁)
  have h1 := standardH1_dimension (namedComplex B₁)
  have h2 := standardH2_dimension (namedComplex B₁)
  rw [triangle_d0_rank] at h0
  rw [triangle_d0_rank,triangle_d1_rank] at h1
  rw [triangle_d1_rank] at h2
  have c0 : Module.finrank ℚ (namedComplex B₁).C0 = 3 := by change Module.finrank ℚ (Fin 3 → ℚ)=3; simp
  have c1 : Module.finrank ℚ (namedComplex B₁).C1 = 3 := by change Module.finrank ℚ (Fin 3 → ℚ)=3; simp
  have c2 : Module.finrank ℚ (namedComplex B₁).C2 = 1 := by change Module.finrank ℚ (Fin 1 → ℚ)=1; simp
  omega
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
