import ResearchLean.AG.AtlasDefectComposition.WitnessThreeConeRanks
import ResearchLean.AG.AtlasDefectComposition.NamedHomology
import ResearchLean.AG.AtlasDefectComposition.ComplexIsoRanks
import Formal.Util.AssertStandardAxioms
/-! # W3の原始入力から生成した比較と標準錐の確定値

名付きセル計算を、同じSource/Law/支持入力の実block全成分同型に沿って移す。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition.WitnessThree
open ResolutionInvariance
/-- W3aの原始入力から既存生成関数が作る実block比較。 -/
abbrev actualA := MA.generatedBlockComparisonHom laws adequate₀ adequate₁ label
/-- W3bの原始入力から既存生成関数が作る実block比較。 -/
abbrev actualB := MB.generatedBlockComparisonHom laws adequate₀ adequate₁ label
/-- W3aの実生成標準錐と名付き標準錐の同型。 -/
def actualA_coneIso := fullBlockNamedConeIso MA laws adequate₀ adequate₁
  (fun _ => rfl) (fullSupport_edge A₀ (fun _ => rfl)) (fullSupport_face A₀ (fun _ => rfl))
  (fun _ => rfl) (fullSupport_edge A₁ (fun _ => rfl)) (fullSupport_face A₁ (fun _ => rfl)) label
/-- W3bの実生成標準錐と名付き標準錐の同型。 -/
def actualB_coneIso := fullBlockNamedConeIso MB laws adequate₀ adequate₁
  (fun _ => rfl) (fullSupport_edge B₀ (fun _ => rfl)) (fullSupport_face B₀ (fun _ => rfl))
  (fun _ => rfl) (fullSupport_edge B₁ (fun _ => rfl)) (fullSupport_face B₁ (fun _ => rfl)) label
/-- W3aの実生成比較の標準homology欠損を全次数で移す。 -/
theorem actualA_defect_named (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap actualA) m).hom =
      blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedA) m).hom :=
  fullBlockNamedHomology_defect MA laws adequate₀ adequate₁ _ _ _ _ _ _ label m
/-- W3bの実生成比較の標準homology欠損を全次数で移す。 -/
theorem actualB_defect_named (m : ℤ) :
    blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap actualB) m).hom =
      blockDefect (HomologicalComplex.homologyMap (zeroExtensionMap namedB) m).hom :=
  fullBlockNamedHomology_defect MB laws adequate₀ adequate₁ _ _ _ _ _ _ label m
/-- W3aの実既存H¹比較の欠損は零。 -/
theorem actualA_H1_defect : blockDefect actualA.h1Map = (0,0) := by
  rw [←standardH1_defect,actualA_defect_named]
  exact namedA_H1_defect
/-- W3bの実既存H¹比較の欠損は零。 -/
theorem actualB_H1_defect : blockDefect actualB.h1Map = (0,0) := by
  rw [←standardH1_defect,actualB_defect_named]
  exact namedB_H1_defect
/-- W3aの実生成標準H⁰余核は1次元であり、H¹欠損から失われる追加項を実現する。 -/
theorem actualA_H0_cokernel_dimension :
    Module.finrank ℚ ((zeroExtension (A₁.lawValueBlockComplex laws adequate₁ label)).homology 0 ⧸
      LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap actualA) 0).hom) = 1 := by
  rw [←blockDefect_cokernel_dimension,actualA_defect_named,namedA_H0_defect]
/-- W3bの実生成標準H²核は1次元であり、H¹欠損から失われる追加項を実現する。 -/
theorem actualB_H2_kernel_dimension :
    Module.finrank ℚ (LinearMap.ker
      (HomologicalComplex.homologyMap (zeroExtensionMap actualB) 2).hom) = 1 := by
  rw [←blockDefect_kernel_dimension,actualB_defect_named,namedB_H2_defect]
/-- W3aの実生成標準錐のhomologyは名付き計算と全次数で一致する。 -/
theorem actualA_cone_homology_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone actualA).homology m) =
      Module.finrank ℚ ((comparisonCone namedA).homology m) :=
  (HomologicalComplex.homologyMapIso actualA_coneIso m).toLinearEquiv.finrank_eq
/-- W3bの実生成標準錐のhomologyは名付き計算と全次数で一致する。 -/
theorem actualB_cone_homology_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone actualB).homology m) =
      Module.finrank ℚ ((comparisonCone namedB).homology m) :=
  (HomologicalComplex.homologyMapIso actualB_coneIso m).toLinearEquiv.finrank_eq
/-- W3aの実生成標準錐の全四次数homology次元。 -/
theorem actualA_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone actualA).homology (-1)) = 0 ∧
    Module.finrank ℚ ((comparisonCone actualA).homology 0) = 1 ∧
    Module.finrank ℚ ((comparisonCone actualA).homology 1) = 0 ∧
    Module.finrank ℚ ((comparisonCone actualA).homology 2) = 0 := by
  simp only [actualA_cone_homology_dimension]
  exact namedA_cone_homology_dimensions
/-- W3bの実生成標準錐の全四次数homology次元。 -/
theorem actualB_cone_homology_dimensions :
    Module.finrank ℚ ((comparisonCone actualB).homology (-1)) = 0 ∧
    Module.finrank ℚ ((comparisonCone actualB).homology 0) = 0 ∧
    Module.finrank ℚ ((comparisonCone actualB).homology 1) = 1 ∧
    Module.finrank ℚ ((comparisonCone actualB).homology 2) = 0 := by
  simp only [actualB_cone_homology_dimension]
  exact namedB_cone_homology_dimensions
/-- W3bの実生成標準錐の空間次元は名付き計算と全次数で一致する。 -/
theorem actualB_cone_degree_dimension (m : ℤ) :
    Module.finrank ℚ ((comparisonCone actualB).X m) =
      Module.finrank ℚ ((comparisonCone namedB).X m) :=
  ((HomologicalComplex.eval _ _ m).mapIso actualB_coneIso).toLinearEquiv.finrank_eq
/-- W3bの実生成標準錐の指定四空間の次元。 -/
theorem actualB_cone_dimensions :
    Module.finrank ℚ ((comparisonCone actualB).X (-1)) = 4 ∧
    Module.finrank ℚ ((comparisonCone actualB).X 0) = 9 ∧
    Module.finrank ℚ ((comparisonCone actualB).X 1) = 7 ∧
    Module.finrank ℚ ((comparisonCone actualB).X 2) = 1 := by
  simp only [actualB_cone_degree_dimension]
  exact namedB_cone_dimensions
/-- W3bの実生成標準錐の指定三微分のrank。 -/
theorem actualB_cone_differential_ranks :
    Module.finrank ℚ (LinearMap.range ((comparisonCone actualB).d (-1) 0).hom) = 4 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone actualB).d 0 1).hom) = 5 ∧
    Module.finrank ℚ (LinearMap.range ((comparisonCone actualB).d 1 2).hom) = 1 := by
  rw [complexIso_d_rank actualB_coneIso (-1) 0,complexIso_d_rank actualB_coneIso 0 1,
    complexIso_d_rank actualB_coneIso 1 2]
  exact namedB_cone_differential_ranks
end AAT.AG.AtlasDefectComposition.WitnessThree
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessThree
