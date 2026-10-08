import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationHomology
import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationAbsent
import ResearchLean.AG.FaceRelationSubdivision.PresentationInverse
import ResearchLean.AG.FaceRelationSubdivision.SubsetComposition
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics

/-!
# G-135 D：面複製のcanonical原比較と同じH¹保存

## Implementation notes

自己readingの逆像等号は細複体全体を輸送する。
元G-134 subsetHomは独立aSubnerve比較と全三成分で同定し、
元旧面sectionによるH¹の両逆を同じ標準射へ移す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u

/-- 全三項複体のtarget等号輸送を標準射の可換正方形へ移す。 -/
theorem subsetTransportStandard_square {C D E : ThreeCochainComplex.{0,u} ℚ}
    (hDE : D = E) (f : ThreeCochainComplex.Hom C D) :
    zeroExtensionMap f ≫ (eqToIso (congrArg zeroExtension hDE)).hom =
      zeroExtensionMap (subsetTransportHom hDE f) := by
  cases hDE
  rw [FaceRelationSubdivision.transportHom_rfl]
  simp only [eqToIso_refl, Iso.refl_hom, Category.comp_id]

namespace FaceClone
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (F : N.nerve.FaceComponent) (A : Set q.Target)

/-- 同じ原面複製のcanonical細複体を、元自己reading等号で移す。 -/
def fineStandardIso : zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
    (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A)) ≅
      zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A) :=
  eqToIso (congrArg (fun B => zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex B))
    (FaceRelationSubdivision.self_preimage A))

/-- 面複製の独立canonical Homは元subset Homと全三成分で一致する。 -/
theorem comparison_transport :
    subsetTransportHom (congrArg (FaceDuplication.supported N F).targetSubsetComplex
      (FaceRelationSubdivision.self_preimage A))
      ((FaceDuplication.comparison N F).aSubnerveComparisonHom A) =
        FaceDuplication.subsetHom N F A :=
  targetSubsetComparisonHom_transport (FaceDuplication.comparison N F) A _ A
    (FaceRelationSubdivision.self_preimage A) (fun _ ht => ht) (FaceDuplication.subset_compatible A)

/-- 標準複体の同じ輸送正方形は独立比較の全次数射を保持する。 -/
theorem comparison_standard_square :
    zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A) ≫
      (fineStandardIso N F A).hom = zeroExtensionMap (FaceDuplication.subsetHom N F A) := by
  exact (subsetTransportStandard_square _ _).trans
    (congrArg zeroExtensionMap (comparison_transport N F A))

/-- canonical細H¹から元G-134細H¹への同じ輸送座標。 -/
def fineH1Equiv :
    (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology (1 : ℤ) ≃ₗ[ℚ]
      (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A)).homology (1 : ℤ) :=
  (homologyMapIso (fineStandardIso N F A) 1).toLinearEquiv
/-- 細座標の順射は実等号輸送のhomology射。 -/
@[simp] theorem fineH1Equiv_apply (x) : fineH1Equiv N F A x =
    homologyMap (fineStandardIso N F A).hom 1 x := rfl

/-- 同じ元sectionによるH¹保存をcanonical標準複体へ接続する両方向同型。 -/
def nativeH1Equiv : (zeroExtension (N.targetSubsetComplex A)).homology (1 : ℤ) ≃ₗ[ℚ]
    (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology (1 : ℤ) :=
  (oldH1Equiv (N.targetSubsetComplex A)).symm.trans
    ((FaceDuplication.subsetH1Equiv N F A).trans
      ((oldH1Equiv ((FaceDuplication.supported N F).targetSubsetComplex A)).trans
        (fineH1Equiv N F A).symm))
/-- H¹保存の順写像は独立canonical原比較そのもの。 -/
theorem nativeH1Equiv_apply (x) : nativeH1Equiv N F A x =
    homologyMap (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 1 x := by
  apply (fineH1Equiv N F A).injective
  dsimp only [nativeH1Equiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply]
  have he : (FaceDuplication.subsetH1Equiv N F A)
      ((oldH1Equiv (N.targetSubsetComplex A)).symm x) =
      (FaceDuplication.subsetHom N F A).h1Map
        ((oldH1Equiv (N.targetSubsetComplex A)).symm x) :=
    LinearMap.congr_fun (FaceDuplication.subsetH1Equiv_toLinearMap N F A) _
  rw [he, oldH1Equiv_natural, LinearEquiv.apply_symm_apply]
  rw [fineH1Equiv_apply, ← ModuleCat.comp_apply, ← homologyMap_comp,
    comparison_standard_square]

/-- 原旧H¹商上にも同じ比較の両方向同型を戻す。 -/
def oldH1Equiv : (N.targetSubsetComplex A).H1 ≃ₗ[ℚ]
    ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A)).H1 :=
  (AtlasDefectComposition.oldH1Equiv (N.targetSubsetComplex A)).trans
    ((nativeH1Equiv N F A).trans
      (AtlasDefectComposition.oldH1Equiv ((FaceDuplication.supported N F).targetSubsetComplex
        (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).symm)
/-- 元旧商同型の順射も同じ独立原比較。 -/
theorem oldH1Equiv_apply (x) : oldH1Equiv N F A x =
    ((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map x := by
  apply (AtlasDefectComposition.oldH1Equiv _).injective
  dsimp only [oldH1Equiv, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, nativeH1Equiv_apply, oldH1Equiv_natural]
/-- 標準H¹の原比較へ逆座標を送ると同じ細元を回復する。 -/
theorem nativeH1Equiv_symm_apply (y) :
    homologyMap (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 1
      ((nativeH1Equiv N F A).symm y) = y := by
  rw [← nativeH1Equiv_apply, LinearEquiv.apply_symm_apply]
/-- 標準H¹の原比較から逆に戻すと同じ粗元を回復する。 -/
theorem nativeH1Equiv_apply_symm (x) : (nativeH1Equiv N F A).symm
    (homologyMap (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 1 x) = x := by
  rw [← nativeH1Equiv_apply, LinearEquiv.symm_apply_apply]
/-- 元旧商の原比較へ逆座標を送ると同じ細元を回復する。 -/
theorem oldH1Equiv_symm_apply (y) :
    ((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map
      ((oldH1Equiv N F A).symm y) = y := by
  rw [← oldH1Equiv_apply, LinearEquiv.apply_symm_apply]
/-- 元旧商の原比較から逆に戻すと同じ粗元を回復する。 -/
theorem oldH1Equiv_apply_symm (x) : (oldH1Equiv N F A).symm
    (((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map x) = x := by
  rw [← oldH1Equiv_apply, LinearEquiv.symm_apply_apply]
/-- 同じ原比較の旧H¹は全Aで全単射。 -/
theorem H1_bijective : Function.Bijective
    ((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map := by
  have hh : ⇑(oldH1Equiv N F A) =
      ⇑((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map :=
    funext (oldH1Equiv_apply N F A)
  rw [← hh]
  exact (oldH1Equiv N F A).bijective
/-- 同じ元blockDefectの両成分は零。 -/
theorem defect_zero : blockDefect ((FaceDuplication.comparison N F).aSubnerveComparisonHom A).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (H1_bijective N F A)

end FaceClone
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.subsetTransportStandard_square
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.fineStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.comparison_transport
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.comparison_standard_square
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.fineH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.fineH1Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH1Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.oldH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.oldH1Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH1Equiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH1Equiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.oldH1Equiv_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.oldH1Equiv_apply_symm
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.H1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.defect_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
