import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import Formal.Util.AssertStandardAxioms
/-! # 次数別短完全列の自然性

任意のchain-map可換正方形から、実余核・錐homology・次核の射を構成する。
原始比較、Law分解、台制限はこの同じ正方形APIへ接続する。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
universe w
variable {F G F' G' : CochainComplex (ModuleCat.{w} ℚ) ℤ}
variable (φ : F ⟶ G) (φ' : F' ⟶ G') (a : F ⟶ F') (b : G ⟶ G')
variable (comm : φ ≫ b = a ≫ φ')
include comm in
/-- 実比較の可換正方形は全次数の実homology mapで可換である。 -/
theorem homology_square (m : ℤ) :
    HomologicalComplex.homologyMap φ m ≫ HomologicalComplex.homologyMap b m =
      HomologicalComplex.homologyMap a m ≫ HomologicalComplex.homologyMap φ' m := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, comm]
/-- 可換正方形のtarget射が誘導する実余核射。 -/
def homologyCokernelMap (m : ℤ) :
    (G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) →ₗ[ℚ]
    (G'.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ' m).hom) :=
  (LinearMap.range (HomologicalComplex.homologyMap φ m).hom).mapQ _
    (HomologicalComplex.homologyMap b m).hom (by
      rintro y ⟨x,rfl⟩
      refine ⟨HomologicalComplex.homologyMap a m x, ?_⟩
      exact (congrArg (fun f : F.homology m ⟶ G'.homology m => f x)
        (homology_square φ φ' a b comm m)).symm)
/-- 可換正方形のsource射が誘導する実核射。 -/
def homologyKernelMap (m : ℤ) :
    LinearMap.ker (HomologicalComplex.homologyMap φ m).hom →ₗ[ℚ]
      LinearMap.ker (HomologicalComplex.homologyMap φ' m).hom :=
  ((HomologicalComplex.homologyMap a m).hom.comp
    (LinearMap.ker (HomologicalComplex.homologyMap φ m).hom).subtype).codRestrict _ (by
      intro x
      have h := congrArg (fun f : F.homology m ⟶ G'.homology m => f x.val)
        (homology_square φ φ' a b comm m)
      simp only [ModuleCat.comp_apply] at h
      change HomologicalComplex.homologyMap φ' m (HomologicalComplex.homologyMap a m x.val) = 0
      rw [← h, show HomologicalComplex.homologyMap φ m x.val = 0 from x.property, map_zero])
/-- 実余核射の代表元評価。 -/
@[simp] theorem homologyCokernelMap_mk (m : ℤ) (y : G.homology m) :
    homologyCokernelMap φ φ' a b comm m
      ((LinearMap.range (HomologicalComplex.homologyMap φ m).hom).mkQ y) =
      (LinearMap.range (HomologicalComplex.homologyMap φ' m).hom).mkQ
        (HomologicalComplex.homologyMap b m y) := rfl
/-- 実核射の値の評価。 -/
@[simp] theorem homologyKernelMap_val (m : ℤ)
    (x : LinearMap.ker (HomologicalComplex.homologyMap φ m).hom) :
    (homologyKernelMap φ φ' a b comm m x).val = HomologicalComplex.homologyMap a m x.val := rfl
/-- 次数別短完全列の余核包含は任意可換正方形について自然である。 -/
theorem coneCokernelInclusion_natural (m : ℤ)
    (y : G.homology m ⧸ LinearMap.range (HomologicalComplex.homologyMap φ m).hom) :
    HomologicalComplex.homologyMap (mappingCone.map φ φ' a b comm) m
      (coneCokernelInclusion φ m y) =
    coneCokernelInclusion φ' m (homologyCokernelMap φ φ' a b comm m y) := by
  obtain ⟨y,rfl⟩ := (LinearMap.range (HomologicalComplex.homologyMap φ m).hom).mkQ_surjective y
  rw [coneCokernelInclusion_mk, homologyCokernelMap_mk, coneCokernelInclusion_mk]
  have h := (mappingCone.triangleMap φ φ' a b comm).comm₂
  change mappingCone.inr φ ≫ mappingCone.map φ φ' a b comm = b ≫ mappingCone.inr φ' at h
  have hh := congrArg (fun f : G ⟶ mappingCone φ' => HomologicalComplex.homologyMap f m) h
  simp only [HomologicalComplex.homologyMap_comp] at hh
  exact congrArg (fun f : G.homology m ⟶ (mappingCone φ').homology m => f y) hh
/-- 次数別短完全列の次核射は任意可換正方形について自然である。 -/
theorem coneKernelProjection_natural (m : ℤ) (x : (mappingCone φ).homology m) :
    coneKernelProjection φ' m
      (HomologicalComplex.homologyMap (mappingCone.map φ φ' a b comm) m x) =
      homologyKernelMap φ φ' a b comm (m+1) (coneKernelProjection φ m x) := by
  apply Subtype.ext
  rw [coneKernelProjection_val, homologyKernelMap_val, coneKernelProjection_val]
  exact congrArg (fun f : (mappingCone φ).homology m ⟶ F'.homology (m+1) => f x)
    (coneConnecting_natural φ φ' a b comm m)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
