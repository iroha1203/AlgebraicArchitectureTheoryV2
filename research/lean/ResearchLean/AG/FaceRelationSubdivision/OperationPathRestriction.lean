import ResearchLean.AG.FaceRelationSubdivision.OperationPathMaps
import ResearchLean.AG.FaceRelationSubdivision.MixedRestrictionHom

/-!
# 原始有限列の全支持包含自然性

## Implementation notes

reading因子逆像の包含からRaw出力の一般自然性を具体適用する。
各Aで選んだ抽象同型を入力にせず、同じ直接r/s/h/kを全支持で使う。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath
variable (path : PrimitiveOperationPath qc Nc qf Nf) {A B : Set qc.Target}

/-- 全支持包含は同じ原始reading因子逆像で保たれる。 -/
theorem targetSubset_mono (h : A ⊆ B) : path.targetSubset A ⊆ path.targetSubset B :=
  fun _ hx => h hx
/-- 原始有限列の同じ実R射は全支持制限と可換。 -/
theorem subsetR_restrict_square (h : A ⊆ B) :
    cochainComp (path.subsetR B) (subsetRestrictHom Nf (path.targetSubset_mono h)) =
      cochainComp (subsetRestrictHom Nc (h)) (path.subsetR A) := by
  rw [subsetR_eq_raw, subsetR_eq_raw]
  exact path.rawEquivalence.targetR_restrict_square h (path.targetSubset_mono h)
    (path.source_subset_eq A) (path.source_subset_eq B)

/-- 同じ実R射と支持制限は旧H1商でも可換。 -/
theorem subsetR_restrict_h1_square (h : A ⊆ B) :
    (subsetRestrictHom Nf (path.targetSubset_mono h)).h1Map.comp (path.subsetR B).h1Map =
      (path.subsetR A).h1Map.comp (subsetRestrictHom Nc (h)).h1Map := by
  have he := congrArg ThreeCochainComplex.Hom.h1Map (path.subsetR_restrict_square h)
  simpa only [cochainComp_h1Map] using he

/-- 同じ実R射と支持制限は標準零延長の全次数でも可換。 -/
theorem subsetR_restrict_zeroExtension_square (h : A ⊆ B) :
    zeroExtensionMap (path.subsetR B) ≫ zeroExtensionMap (subsetRestrictHom Nf (path.targetSubset_mono h)) =
      zeroExtensionMap (subsetRestrictHom Nc (h)) ≫ zeroExtensionMap (path.subsetR A) := by
  have he := congrArg zeroExtensionMap (path.subsetR_restrict_square h)
  simpa only [zeroExtensionMap_comp] using he

/-- 原始有限列の同じ実S射は全支持制限と可換。 -/
theorem subsetS_restrict_square (h : A ⊆ B) :
    cochainComp (path.subsetS B) (subsetRestrictHom Nc (h)) =
      cochainComp (subsetRestrictHom Nf (path.targetSubset_mono h)) (path.subsetS A) := by
  rw [subsetS_eq_raw, subsetS_eq_raw]
  exact path.rawEquivalence.targetS_restrict_square h (path.targetSubset_mono h)
    (path.source_subset_eq A) (path.source_subset_eq B)

/-- 同じ実S射と支持制限は旧H1商でも可換。 -/
theorem subsetS_restrict_h1_square (h : A ⊆ B) :
    (subsetRestrictHom Nc (h)).h1Map.comp (path.subsetS B).h1Map =
      (path.subsetS A).h1Map.comp (subsetRestrictHom Nf (path.targetSubset_mono h)).h1Map := by
  have he := congrArg ThreeCochainComplex.Hom.h1Map (path.subsetS_restrict_square h)
  simpa only [cochainComp_h1Map] using he

/-- 同じ実S射と支持制限は標準零延長の全次数でも可換。 -/
theorem subsetS_restrict_zeroExtension_square (h : A ⊆ B) :
    zeroExtensionMap (path.subsetS B) ≫ zeroExtensionMap (subsetRestrictHom Nc (h)) =
      zeroExtensionMap (subsetRestrictHom Nf (path.targetSubset_mono h)) ≫ zeroExtensionMap (path.subsetS A) := by
  have he := congrArg zeroExtensionMap (path.subsetS_restrict_square h)
  simpa only [zeroExtensionMap_comp] using he

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
