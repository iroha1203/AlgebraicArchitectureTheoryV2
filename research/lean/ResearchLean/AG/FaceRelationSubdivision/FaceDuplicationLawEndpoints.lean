import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationAbsent
import ResearchLean.AG.FaceRelationSubdivision.FaceDuplicationLaw
import Formal.Util.AssertStandardAxioms

/-! # 面複製の独立実Law端次数

## Implementation notes

Law/block射は既存原始生成を保ち、whole-three fiber/family自然性を用いる。
同型の共役でLaw比較を定義する方法は採らない。選択されない成分も全次数で扱う。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
namespace FaceDuplication
variable (N : TargetSupportedNerve q) (F : N.nerve.FaceComponent)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)
/-- 同じ原始block射と同じsubset射の標準自然性。 -/
theorem block_endpoint_natural (l : LawValueLabel laws) (n : ℤ)
    (x : (zeroExtension (N.lawValueBlockComplex laws ha l)).homology n) :
    (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso (supported N F) laws ha l _ rfl) n).hom
        (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) n x) =
      homologyMap (zeroExtensionMap (subsetHom N F (labelValueFiber laws q ha l))) n
        ((homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso N laws ha l _ rfl) n).hom x) :=
  lawBlockSelectedSubsetHomology_natural N (supported N F) laws ha (comparison N F) ha l
    _ _ rfl rfl (subset_compatible _) n x
/-- 全発生ラベルで同じ実標準H⁰比較はbijective。 -/
theorem blockStandardH0_bijective (l : LawValueLabel laws) : Function.Bijective
    (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 0) :=
  (LinearConjugation.bijective_iff
    (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 0).hom
    (homologyMap (zeroExtensionMap (subsetHom N F (labelValueFiber laws q ha l))) 0).hom
    (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso N laws ha l _ rfl) 0).toLinearEquiv
    (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso (supported N F) laws ha l _ rfl) 0).toLinearEquiv
    (block_endpoint_natural N F laws ha l 0)).mpr (subsetStandardH0_bijective N F _)
/-- 同じ実blockH⁰の線形同値。 -/
def blockStandardH0Equiv (l : LawValueLabel laws) :
    (zeroExtension (N.lawValueBlockComplex laws ha l)).homology 0 ≃ₗ[ℚ]
    (zeroExtension ((supported N F).lawValueBlockComplex laws ha l)).homology 0 :=
  LinearEquiv.ofBijective (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 0).hom
    (blockStandardH0_bijective N F laws ha l)
/-- 同値の正方向は同じ独立実block射。 -/
@[simp] theorem blockStandardH0Equiv_apply (l : LawValueLabel laws)
    (x : (zeroExtension (N.lawValueBlockComplex laws ha l)).homology 0) :
    blockStandardH0Equiv N F laws ha l x =
      homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 0 x := rfl
/-- 全発生ラベルで同じ実標準H²比較は単射。 -/
theorem blockStandardH2_injective (l : LawValueLabel laws) : Function.Injective
    (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) 2) := by
  intro x y h
  apply (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso N laws ha l _ rfl) 2).toLinearEquiv.injective
  apply subsetStandardH2_injective N F (labelValueFiber laws q ha l)
  exact (block_endpoint_natural N F laws ha l 2 x).symm.trans
    ((congrArg (homologyMapIso
      (lawBlockSelectedSubsetZeroExtensionIso (supported N F) laws ha l _ rfl) 2).hom h).trans
        (block_endpoint_natural N F laws ha l 2 y))
/-- 同じ全Law H⁰線形同値。ラベル重複を保持する。 -/
def lawStandardH0Equiv : (zeroExtension (N.lawGeneratedComplex laws ha)).homology 0 ≃ₗ[ℚ]
    (zeroExtension ((supported N F).lawGeneratedComplex laws ha)).homology 0 :=
  (lawStandardHomologyEquiv N laws ha 0).trans
    ((LinearEquiv.piCongrRight (fun l => blockStandardH0Equiv N F laws ha l)).trans
      (lawStandardHomologyEquiv (supported N F) laws ha 0).symm)
/-- 全Law同値も同じ独立生成射を読む。 -/
theorem lawStandardH0Equiv_apply (x : (zeroExtension (N.lawGeneratedComplex laws ha)).homology 0) :
    lawStandardH0Equiv N F laws ha x = homologyMap (zeroExtensionMap (lawHom N F laws ha)) 0 x := by
  apply (lawStandardHomologyEquiv (supported N F) laws ha 0).injective
  simp only [lawStandardH0Equiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext l
  simp only [LinearEquiv.piCongrRight_apply, blockStandardH0Equiv_apply]
  exact ((comparison N F).lawStandardHomology_natural laws ha ha 0 x l).symm
/-- 同じ全Law標準H⁰射はbijective。 -/
theorem lawStandardH0_bijective : Function.Bijective
    (homologyMap (zeroExtensionMap (lawHom N F laws ha)) 0) := by
  have he : ⇑(lawStandardH0Equiv N F laws ha) =
      ⇑(homologyMap (zeroExtensionMap (lawHom N F laws ha)) 0) :=
    funext (lawStandardH0Equiv_apply N F laws ha)
  rw [← he]
  exact (lawStandardH0Equiv N F laws ha).bijective
/-- 同じ全Law標準H²射は単射。 -/
theorem lawStandardH2_injective : Function.Injective
    (homologyMap (zeroExtensionMap (lawHom N F laws ha)) 2) := by
  intro x y h
  apply (lawStandardHomologyEquiv N laws ha 2).injective
  funext l
  apply blockStandardH2_injective N F laws ha l
  exact ((comparison N F).lawStandardHomology_natural laws ha ha 2 x l).symm.trans
    ((congrArg (fun z => lawStandardHomologyEquiv (supported N F) laws ha 2 z l) h).trans
      ((comparison N F).lawStandardHomology_natural laws ha ha 2 y l))
/-- 面が非選択のラベルでは、同じ実block比較は全整数次数同型。 -/
theorem blockAbsent_bijective (l : LawValueLabel laws)
    (hF : ¬ ∃ t, t ∈ N.faceSupport F ∧ t ∈ labelValueFiber laws q ha l) (n : ℤ) :
    Function.Bijective (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) n) :=
  (LinearConjugation.bijective_iff
    (homologyMap (zeroExtensionMap (blockHom N F laws ha l)) n).hom
    (homologyMap (zeroExtensionMap (subsetHom N F (labelValueFiber laws q ha l))) n).hom
    (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso N laws ha l _ rfl) n).toLinearEquiv
    (homologyMapIso (lawBlockSelectedSubsetZeroExtensionIso (supported N F) laws ha l _ rfl) n).toLinearEquiv
    (block_endpoint_natural N F laws ha l n)).mpr (absent_homology_bijective N F _ hF n)
end FaceDuplication
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
