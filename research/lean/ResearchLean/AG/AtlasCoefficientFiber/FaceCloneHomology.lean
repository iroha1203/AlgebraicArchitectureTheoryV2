import ResearchLean.AG.AtlasCoefficientFiber.FaceCloneCoefficient
import ResearchLean.AG.AtlasDefectComposition.LinearConjugation

/-!
# G-135 D：面複製の同じH²余核と三錐

## Implementation notes

canonical輸送と元εの可換正方形を実H²射の商へ降ろす。
非零類は元fresh面だけ1の代表を旧・標準商の可逆座標で移す。
選択面のH²非零性と、非選択面の全次数保存を同じ原比較で扱う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
namespace FaceClone
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (F : N.nerve.FaceComponent) (A : Set q.Target)

/-- 原canonical細homologyと元G-134細homologyを全整数次数で両方向同定する。 -/
def nativeFineHomologyEquiv (n : ℤ) :
    (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology n ≃ₗ[ℚ]
      (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex A)).homology n :=
  (homologyMapIso (fineStandardIso N F A) n).toLinearEquiv
/-- 全次数の細座標は同じ等号輸送の実射。 -/
@[simp] theorem nativeFineHomologyEquiv_apply (n : ℤ) (x) :
    nativeFineHomologyEquiv N F A n x = homologyMap (fineStandardIso N F A).hom n x := rfl
/-- 全次数で独立canonical比較は元比較と同じ可換homology射。 -/
theorem nativeHomology_square (n : ℤ) (x) :
    nativeFineHomologyEquiv N F A n
      (homologyMap (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) n x) =
        homologyMap (zeroExtensionMap (FaceDuplication.subsetHom N F A)) n x := by
  rw [nativeFineHomologyEquiv_apply, ← ModuleCat.comp_apply, ← homologyMap_comp,
    comparison_standard_square]

/-- 同じcanonical原H²余核を元fresh差を読む旧H²余核へ移す。 -/
def nativeH2CokernelOldEquiv :
    ((zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap
        (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 2).hom) ≃ₗ[ℚ]
    (((((FaceDuplication.supported N F).targetSubsetComplex A).C2 ⧸
      LinearMap.range ((FaceDuplication.supported N F).targetSubsetComplex A).d1)) ⧸
      LinearMap.range (oldH2Map (FaceDuplication.subsetHom N F A))) :=
  (LinearConjugation.cokernelEquiv _ _ (LinearEquiv.refl ℚ _)
    (nativeFineHomologyEquiv N F A 2) (nativeHomology_square N F A 2)).trans
      (FaceDuplication.standardH2CokernelOldEquiv N F A)
/-- 選択面を含む同じ原H²比較の余核はℚ。 -/
def nativeH2CokernelEquiv (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    ((zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap
        (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 2).hom) ≃ₗ[ℚ] ℚ :=
  (nativeH2CokernelOldEquiv N F A).trans (FaceDuplication.oldH2CokernelEquiv N F A hF)

/-- 元fresh面単独1の余核類を実商の可逆座標でcanonical原H²余核へ移す。 -/
def nativeFreshCokernelClass :
    (zeroExtension ((FaceDuplication.supported N F).targetSubsetComplex
      (comparisonFactor q q (Reading.coarserThan_refl q) ⁻¹' A))).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap
        (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 2).hom :=
  (nativeH2CokernelOldEquiv N F A).symm
    ((LinearMap.range (oldH2Map (FaceDuplication.subsetHom N F A))).mkQ
      ((LinearMap.range ((FaceDuplication.supported N F).targetSubsetComplex A).d1).mkQ
        (FaceDuplication.freshOnly N F A 1)))
/-- canonical原余核のfresh類は同じ原始差で1となる。 -/
theorem nativeFreshCokernelClass_value (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    nativeH2CokernelEquiv N F A hF (nativeFreshCokernelClass N F A) = 1 := by
  dsimp only [nativeH2CokernelEquiv, nativeFreshCokernelClass, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, FaceDuplication.oldH2CokernelEquiv_mk,
    FaceDuplication.difference_freshOnly]
/-- 同じ元fresh面のcanonical原H²余核類は非零。 -/
theorem nativeFreshCokernelClass_nonzero (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    nativeFreshCokernelClass N F A ≠ 0 := by
  intro hz
  have hh := congrArg (nativeH2CokernelEquiv N F A hF) hz
  rw [nativeFreshCokernelClass_value, map_zero] at hh
  exact one_ne_zero hh

/-- 同じ原total錐を全三成分輸送で元G-134錐へ両方向同定する。 -/
def totalConeIso : totalCone (FaceDuplication.comparison N F) A ≅
    comparisonCone (FaceDuplication.subsetHom N F A) :=
  coneMapIso _ _ (Iso.refl _) (fineStandardIso N F A)
    (by simpa only [Iso.refl_hom, Category.id_comp] using comparison_standard_square N F A)
/-- 原total錐同型の順射は同じ標準可換正方形射。 -/
@[simp] theorem totalConeIso_hom : (totalConeIso N F A).hom =
    mappingCone.map (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A))
      (zeroExtensionMap (FaceDuplication.subsetHom N F A)) (𝟙 _)
      (fineStandardIso N F A).hom (by
        simpa only [Category.id_comp] using comparison_standard_square N F A) := rfl
/-- 原total錐の全元はtarget輸送とsource保持の二座標を持つ。 -/
theorem totalConeIso_apply (n : ℤ) (z : (totalCone (FaceDuplication.comparison N F) A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (FaceDuplication.subsetHom N F A)) n
      ((totalConeIso N F A).hom.f n z) =
        ((fineStandardIso N F A).hom.f n
          (coneCoordinateEquiv (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) n z).1,
          (coneCoordinateEquiv (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) n z).2) := by
  rw [totalConeIso_hom]
  exact coneCoordinateEquiv_map _ _ (𝟙 _) (fineStandardIso N F A).hom
    (by simpa only [Category.id_comp] using comparison_standard_square N F A) n z
/-- 原η錐の全元は元P評価とsource保持の二座標を持つ。 -/
theorem coefficientConeIso_apply (n : ℤ) (z : (coefficientCone (FaceDuplication.comparison N F) A).X n) :
    coneCoordinateEquiv (zeroExtensionMap (FaceDuplication.subsetHom N F A)) n
      ((coefficientConeIso N F A).hom.f n z) =
        ((coefficientStandardIso N F A).hom.f n
          (coneCoordinateEquiv (zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A)) n z).1,
          (coneCoordinateEquiv (zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A)) n z).2) := by
  rw [coefficientConeIso_hom]
  exact coneCoordinateEquiv_map _ _ (𝟙 _) (coefficientStandardIso N F A).hom
    (by simpa only [Category.id_comp] using unit_standard_square N F A) n z
/-- 原η錐同型は同じ三錐triangle第一射と元total輸送の合成である。 -/
theorem coefficientConeIso_first :
    (coefficientCompositionTriangle (FaceDuplication.comparison N F) A).mor₁ ≫
      (totalConeIso N F A).hom = (coefficientConeIso N F A).hom := by
  ext n z
  apply (coneCoordinateEquiv (zeroExtensionMap (FaceDuplication.subsetHom N F A)) n).injective
  simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply]
  refine (totalConeIso_apply N F A n _).trans
    (Eq.trans ?_ (coefficientConeIso_apply N F A n z).symm)
  rw [coefficientCompositionTriangle_first,
    coefficientStandardIso_hom, HomologicalComplex.comp_f, ModuleCat.comp_apply]
/-- 選択面について同じ原total錐のH²はℚ。 -/
def totalConeH2Equiv (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    (totalCone (FaceDuplication.comparison N F) A).homology (2 : ℤ) ≃ₗ[ℚ] ℚ :=
  (homologyMapIso (totalConeIso N F A) 2).toLinearEquiv.trans
    (FaceDuplication.coneH2Equiv N F A hF)
/-- 選択面について同じ原η錐のH²もℚ。 -/
def coefficientConeH2Equiv (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    (coefficientCone (FaceDuplication.comparison N F) A).homology (2 : ℤ) ≃ₗ[ℚ] ℚ :=
  (homologyMapIso (coefficientConeIso N F A) 2).toLinearEquiv.trans
    (FaceDuplication.coneH2Equiv N F A hF)

/-- 元ε座標で同じηのH²写像は独立原uのH²写像となる。 -/
theorem unitH2_square (x) :
    (homologyMapIso (evaluationIso N F A) 2).toLinearEquiv
      (homologyMap (zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A)) 2 x) =
        homologyMap (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) 2 x := by
  rw [Iso.toLinearEquiv_apply, homologyMapIso_hom, evaluationIso_hom,
    ← ModuleCat.comp_apply, ← homologyMap_comp, ← standardComparison_factorization]
/-- 同じ原ηのH²余核も実ε可逆座標を通してℚとなる。 -/
def coefficientH2CokernelEquiv (hF : ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) :
    ((zeroExtension (pushforwardComplex (FaceDuplication.comparison N F) A)).homology (2 : ℤ) ⧸
      LinearMap.range (homologyMap (zeroExtensionMap (unitHom (FaceDuplication.comparison N F) A)) 2).hom) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv _ _ (LinearEquiv.refl ℚ _)
    (homologyMapIso (evaluationIso N F A) 2).toLinearEquiv (unitH2_square N F A)).trans
      (nativeH2CokernelEquiv N F A hF)

/-- 非選択面では同じcanonical原比較は全整数次数で全単射。 -/
theorem absent_homology_bijective (hF : ¬ ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) (n : ℤ) :
    Function.Bijective (homologyMap
      (zeroExtensionMap ((FaceDuplication.comparison N F).aSubnerveComparisonHom A)) n).hom :=
  (LinearConjugation.bijective_iff _ _ (LinearEquiv.refl ℚ _)
    (nativeFineHomologyEquiv N F A n) (nativeHomology_square N F A n)).mpr
      (FaceDuplication.absent_homology_bijective N F A hF n)
/-- 非選択面では同じ原total錐は全整数次数で零。 -/
theorem absent_totalCone_zero (hF : ¬ ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) (n : ℤ) :
    IsZero ((totalCone (FaceDuplication.comparison N F) A).homology n) :=
  cone_homology_isZero_of_bijective _ (absent_homology_bijective N F A hF) n
/-- 非選択面では同じ原η錐も全整数次数で零。 -/
theorem absent_coefficientCone_zero (hF : ¬ ∃ t, t ∈ N.faceSupport F ∧ t ∈ A) (n : ℤ) :
    IsZero ((coefficientCone (FaceDuplication.comparison N F) A).homology n) :=
  IsZero.of_iso
    (cone_homology_isZero_of_bijective _ (FaceDuplication.absent_homology_bijective N F A hF) n)
      (homologyMapIso (coefficientConeIso N F A) n)

end FaceClone
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeFineHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeFineHomologyEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeHomology_square
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH2CokernelOldEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeH2CokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeFreshCokernelClass
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeFreshCokernelClass_value
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.nativeFreshCokernelClass_nonzero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.totalConeIso
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.totalConeIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.totalConeIso_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientConeIso_apply
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientConeIso_first
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.totalConeH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientConeH2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.unitH2_square
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.coefficientH2CokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.absent_homology_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.absent_totalCone_zero
#print axioms AAT.AG.AtlasCoefficientFiber.FaceClone.absent_coefficientCone_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
