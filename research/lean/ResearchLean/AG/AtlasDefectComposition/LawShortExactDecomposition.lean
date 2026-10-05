import ResearchLean.AG.AtlasDefectComposition.LawProjection
import Formal.Util.AssertStandardAxioms
/-! # 次数別短完全列の実Law成分可換図式

Implementation notes: 実projection正方形の核・余核射と標準錐射を用いる。包含と次核射の可換式は標準錐の自然性から導き、別の分裂や任意の基底を選ばない。
-/
noncomputable section
open CategoryTheory HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} [Fintype Source]
variable {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
variable (M : TargetSupportedNerveMorphism q r h N E) (hr : laws.Adequate r)
/-- 実余核族の同定の成分は同じprojection正方形の実余核射である。 -/
theorem lawStandardCokernelFamilyEquiv_component (m : ℤ)
    (x : (zeroExtension (E.lawGeneratedComplex laws hr)).homology m ⧸ LinearMap.range
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom)
    (l : LawValueLabel laws) : lawStandardCokernelFamilyEquiv N E laws ha M hr m x l =
      homologyCokernelMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr))
        (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))
        (lawBlockZeroExtensionProjection N laws ha l) (lawBlockZeroExtensionProjection E laws hr l)
        (lawBlockZeroExtensionProjection_natural N E laws ha M hr l) m x := by
  obtain ⟨x,rfl⟩ := (LinearMap.range
    (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom).mkQ_surjective x
  rw [lawStandardCokernelFamilyEquiv_mk,homologyCokernelMap_mk,
    lawStandardHomologyEquiv_component]
/-- 実核族の同定の成分は同じprojection正方形の実核射である。 -/
theorem lawStandardKernelFamilyEquiv_component (m : ℤ)
    (x : LinearMap.ker (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom)
    (l : LawValueLabel laws) : lawStandardKernelFamilyEquiv N E laws ha M hr m x l =
      homologyKernelMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr))
        (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l))
        (lawBlockZeroExtensionProjection N laws ha l) (lawBlockZeroExtensionProjection E laws hr l)
        (lawBlockZeroExtensionProjection_natural N E laws ha M hr l) m x := by
  apply Subtype.ext
  rw [lawStandardKernelFamilyEquiv_val,homologyKernelMap_val,lawStandardHomologyEquiv_component]
/-- 標準錐短完全列の余核包含は全ラベル・全次数で同じ実包含へ分解される。 -/
theorem lawConeCokernelInclusion_component (m : ℤ)
    (x : (zeroExtension (E.lawGeneratedComplex laws hr)).homology m ⧸ LinearMap.range
      (homologyMap (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m).hom)
    (l : LawValueLabel laws) : lawConeHomologyEquiv N E laws ha M hr m
      (coneCokernelInclusion (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x) l =
    coneCokernelInclusion (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m
      (lawStandardCokernelFamilyEquiv N E laws ha M hr m x l) := by
  rw [lawConeHomologyEquiv_component,lawStandardCokernelFamilyEquiv_component]
  exact coneCokernelInclusion_natural _ _ _ _ _ m x
/-- 標準錐短完全列の次核射も全ラベル・全次数で同じ実射へ分解される。 -/
theorem lawConeKernelProjection_component (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (M.generatedComparisonHom laws ha hr))).homology m)
    (l : LawValueLabel laws) : lawStandardKernelFamilyEquiv N E laws ha M hr (m+1)
      (coneKernelProjection (zeroExtensionMap (M.generatedComparisonHom laws ha hr)) m x) l =
    coneKernelProjection (zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) m
      (lawConeHomologyEquiv N E laws ha M hr m x l) := by
  rw [lawConeHomologyEquiv_component,lawStandardKernelFamilyEquiv_component]
  exact (coneKernelProjection_natural _ _ _ _ _ m x).symm
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
