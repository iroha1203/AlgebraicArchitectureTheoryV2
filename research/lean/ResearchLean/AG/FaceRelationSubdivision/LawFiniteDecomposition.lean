import ResearchLean.AG.FaceRelationSubdivision.LawComparisonDecomposition
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteBlockHom
import ResearchLean.AG.AtlasDefectComposition.FiniteDefectFamily
import ResearchLean.AG.AtlasDefectComposition.FiniteConeFamily
import ResearchLean.AG.AtlasDefectComposition.ConeEquivalence
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import ResearchLean.AG.UniformInvariance.DefectSemantics

/-!
# 原始有限和の同じ全Law・ラベル射と診断分解

## Implementation notes

各原始非零項のラベル保存から独立Law射とblock射の自然性を証明する。
次元一致で射の接続を代替する案は採らず、実核・余核・標準錐の同値を構成する。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 標準複体の有限積から、同じラベル族の有限直和を得る局所API。 -/
local instance lawFiniteDecompositionBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source] {q : Reading Source}
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 既存Law族次数0は同じラベル座標制限そのもの。 -/
theorem lawFamily0Equiv_eq_read (N : TargetSupportedNerve q) (x) (l) :
    lawFamily0Equiv N laws ha x l = lawBlockRead laws ha N.chartSupport l x := by
  funext y
  rw [lawFamily0Equiv_apply, lawBlockRead_apply]
/-- 既存Law族次数1は同じラベル座標制限そのもの。 -/
theorem lawFamily1Equiv_eq_read (N : TargetSupportedNerve q) (x) (l) :
    lawFamily1Equiv N laws ha x l = lawBlockRead laws ha N.edgeSupport l x := by
  funext y
  rw [lawFamily1Equiv_apply, lawBlockRead_apply]
/-- 既存Law族次数2は同じラベル座標制限そのもの。 -/
theorem lawFamily2Equiv_eq_read (N : TargetSupportedNerve q) (x) (l) :
    lawFamily2Equiv N laws ha x l = lawBlockRead laws ha N.faceSupport l x := by
  funext y
  rw [lawFamily2Equiv_apply, lawBlockRead_apply]

variable {Nc Nf : TargetSupportedNerve q}
variable (M0 : SupportedBasisMap Nf.chartSupport Nc.chartSupport)
variable (M1 : SupportedBasisMap Nf.edgeSupport Nc.edgeSupport)
variable (M2 : SupportedBasisMap Nf.faceSupport Nc.faceSupport)
variable (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw =
    M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw =
    M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 原始独立Law有限和次数0は同じ独立block有限和と可換。 -/
theorem lawFiniteFamily_natural0 (x) (l) :
    lawFamily0Equiv Nf laws ha ((lawFiniteHom M0 M1 M2 h0 h1 laws ha).f0 x) l =
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f0 (lawFamily0Equiv Nc laws ha x l) := by
  rw [lawFamily0Equiv_eq_read, lawFamily0Equiv_eq_read, lawFiniteHom_f0, blockFiniteHom_f0]
  exact M0.lawDual_block laws ha l x
/-- 原始独立Law有限和次数1は同じ独立block有限和と可換。 -/
theorem lawFiniteFamily_natural1 (x) (l) :
    lawFamily1Equiv Nf laws ha ((lawFiniteHom M0 M1 M2 h0 h1 laws ha).f1 x) l =
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f1 (lawFamily1Equiv Nc laws ha x l) := by
  rw [lawFamily1Equiv_eq_read, lawFamily1Equiv_eq_read, lawFiniteHom_f1, blockFiniteHom_f1]
  exact M1.lawDual_block laws ha l x
/-- 原始独立Law有限和次数2は同じ独立block有限和と可換。 -/
theorem lawFiniteFamily_natural2 (x) (l) :
    lawFamily2Equiv Nf laws ha ((lawFiniteHom M0 M1 M2 h0 h1 laws ha).f2 x) l =
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f2 (lawFamily2Equiv Nc laws ha x l) := by
  rw [lawFamily2Equiv_eq_read, lawFamily2Equiv_eq_read, lawFiniteHom_f2, blockFiniteHom_f2]
  exact M2.lawDual_block laws ha l x

/-- 原始Law/block有限和の同じ全三成分族正方形。 -/
theorem lawFiniteFamily_square : cochainComp (lawFiniteHom M0 M1 M2 h0 h1 laws ha)
    (lawFamilyCochainEquiv Nf laws ha).toHom =
      cochainComp (lawFamilyCochainEquiv Nc laws ha).toHom
        (ThreeComplexFamily.map (fun l => Nc.lawValueBlockComplex laws ha l)
          (fun l => Nf.lawValueBlockComplex laws ha l)
          (fun l => blockFiniteHom laws ha M0 M1 M2 h0 h1 l)) :=
  LawMapDecomposition.family_square Nc Nf laws ha ha _ _
    (lawFiniteFamily_natural0 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural1 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural2 laws ha M0 M1 M2 h0 h1)

/-- 同じ独立原始有限和を全次数の標準Law/ラベル射へ接続。 -/
theorem lawFiniteZeroExtension_square : zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha) ≫
    (lawZeroExtensionIso Nf laws ha).hom = (lawZeroExtensionIso Nc laws ha).hom ≫
      FiniteComplexFamily.map (fun l => zeroExtension (Nc.lawValueBlockComplex laws ha l))
        (fun l => zeroExtension (Nf.lawValueBlockComplex laws ha l))
        (fun l => zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l)) :=
  LawMapDecomposition.zeroExtension_square Nc Nf laws ha ha _ _
    (lawFiniteFamily_natural0 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural1 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural2 laws ha M0 M1 M2 h0 h1)

/-- 同じ原始有限和の全次数homologyも同じラベル射に分解する。 -/
theorem lawFiniteStandardHomology_natural (m : ℤ)
    (x : (zeroExtension (Nc.lawGeneratedComplex laws ha)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv Nf laws ha m
        (homologyMap (zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha)) m x) l =
      homologyMap (zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l)) m
        (lawStandardHomologyEquiv Nc laws ha m x l) :=
  LawMapDecomposition.standard_homology_natural Nc Nf laws ha ha _ _
    (lawFiniteFamily_natural0 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural1 laws ha M0 M1 M2 h0 h1)
    (lawFiniteFamily_natural2 laws ha M0 M1 M2 h0 h1) m x l

/-- 同じ原始有限和は旧H1商でも各独立ラベル射へ分解する。 -/
theorem lawFiniteH1Family_natural (x : (Nc.lawGeneratedComplex laws ha).H1) (l : LawValueLabel laws) :
    lawH1FamilyEquiv Nf laws ha ((lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map x) l =
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map (lawH1FamilyEquiv Nc laws ha x l) :=
  LawMapDecomposition.h1_natural Nc Nf laws ha ha _ _
    (lawFiniteFamily_natural1 laws ha M0 M1 M2 h0 h1) x l

/-- 同じ原始有限和の既存H1族比較正方形。 -/
theorem lawFiniteH1Family_square (x : (Nc.lawGeneratedComplex laws ha).H1) :
    lawH1FamilyEquiv Nf laws ha ((lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map x) =
      FiniteLinearFamily.map (fun l => (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map)
        (lawH1FamilyEquiv Nc laws ha x) := by
  funext l
  exact lawFiniteH1Family_natural laws ha M0 M1 M2 h0 h1 x l

/-- 原始独立Law有限和の実H1核は同じ独立ラベル核の族。 -/
def lawFiniteKernelFamilyEquiv :
    LinearMap.ker (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → LinearMap.ker (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map) :=
  (LinearConjugation.kernelEquiv _ _ (lawH1FamilyEquiv Nc laws ha)
    (lawH1FamilyEquiv Nf laws ha) (lawFiniteH1Family_square laws ha M0 M1 M2 h0 h1)).trans
      (FiniteLinearFamily.kernelEquiv _)

/-- 原始独立Law有限和の実H1余核は同じ独立ラベル余核の族。 -/
def lawFiniteCokernelFamilyEquiv :
    ((Nf.lawGeneratedComplex laws ha).H1 ⧸ LinearMap.range (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (Nf.lawValueBlockComplex laws ha l).H1 ⧸
        LinearMap.range (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map) :=
  (LinearConjugation.cokernelEquiv _ _ (lawH1FamilyEquiv Nc laws ha)
    (lawH1FamilyEquiv Nf laws ha) (lawFiniteH1Family_square laws ha M0 M1 M2 h0 h1)).trans
      (FiniteLinearFamily.cokernelEquiv _)

/-- 実核同定は同じsource H1類のラベル成分を読む。 -/
@[simp] theorem lawFiniteKernelFamilyEquiv_val
    (x : LinearMap.ker (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map) (l : LawValueLabel laws) :
    (lawFiniteKernelFamilyEquiv laws ha M0 M1 M2 h0 h1 x l).val =
      lawH1FamilyEquiv Nc laws ha x.val l := rfl

/-- 実余核同定は同じtarget H1代表元の各ラベル商類を読む。 -/
@[simp] theorem lawFiniteCokernelFamilyEquiv_mk (x : (Nf.lawGeneratedComplex laws ha).H1)
    (l : LawValueLabel laws) : lawFiniteCokernelFamilyEquiv laws ha M0 M1 M2 h0 h1
      ((LinearMap.range (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map).mkQ x) l =
        (LinearMap.range (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map).mkQ
          (lawH1FamilyEquiv Nf laws ha x l) := by
  rw [lawFiniteCokernelFamilyEquiv, LinearEquiv.trans_apply,
    LinearConjugation.cokernelEquiv_mk, FiniteLinearFamily.cokernelEquiv_mk]

/-- 原始実有限和の欠損は重複を保持した全発生ラベルの実欠損の和。 -/
theorem lawFiniteDefect_sum : blockDefect (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map =
    (∑ l, (blockDefect (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map).1,
      ∑ l, (blockDefect (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map).2) := by
  apply Prod.ext
  · simp only [blockDefect_kernel_dimension]
    rw [(lawFiniteKernelFamilyEquiv laws ha M0 M1 M2 h0 h1).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
  · simp only [blockDefect_cokernel_dimension]
    rw [(lawFiniteCokernelFamilyEquiv laws ha M0 M1 M2 h0 h1).finrank_eq]
    exact Module.finrank_pi_fintype ℚ

/-- 全Law実有限和射の同じ標準錐を実ラベル錐の族へ接続。 -/
def lawFiniteConeFamilyIso : mappingCone (zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha)) ≅
    FiniteComplexFamily.complex (fun l =>
      mappingCone (zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l))) :=
  coneMapIso _ _ (lawZeroExtensionIso Nc laws ha) (lawZeroExtensionIso Nf laws ha)
      (lawFiniteZeroExtension_square laws ha M0 M1 M2 h0 h1) ≪≫
    FiniteConeFamily.iso (fun l => zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l))

/-- 同じ独立有限和の実錐を重複を保ったラベル錐の有限直和へ接続。 -/
def lawFiniteConeDirectSumIso : mappingCone (zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha)) ≅
    biproduct (fun l => mappingCone (zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l))) :=
  lawFiniteConeFamilyIso laws ha M0 M1 M2 h0 h1 ≪≫ FiniteComplexFamily.directSumIso _

/-- 同じ実Law有限和錐の全整数次数を同じラベル錐へ読む。 -/
def lawFiniteConeHomologyEquiv (m : ℤ) :
    (mappingCone (zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha))).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) →
        (mappingCone (zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l))).homology m) :=
  (homologyMapIso (lawFiniteConeFamilyIso laws ha M0 M1 M2 h0 h1) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)

/-- 実有限和錐族の順射は同じ二段の標準構成。 -/
@[simp] theorem lawFiniteConeFamilyIso_hom : (lawFiniteConeFamilyIso laws ha M0 M1 M2 h0 h1).hom =
    (coneMapIso _ _ (lawZeroExtensionIso Nc laws ha) (lawZeroExtensionIso Nf laws ha)
      (lawFiniteZeroExtension_square laws ha M0 M1 M2 h0 h1)).hom ≫
        (FiniteConeFamily.iso (fun l => zeroExtensionMap (blockFiniteHom laws ha M0 M1 M2 h0 h1 l))).hom := rfl

/-- 同じ有限和錐homology族の成分は実projectionの写像。 -/
theorem lawFiniteConeHomologyEquiv_component (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (lawFiniteHom M0 M1 M2 h0 h1 laws ha))).homology m)
    (l : LawValueLabel laws) : lawFiniteConeHomologyEquiv laws ha M0 M1 M2 h0 h1 m x l =
      homologyMap ((lawFiniteConeFamilyIso laws ha M0 M1 M2 h0 h1).hom ≫
        FiniteComplexFamily.projection _ l) m x := by
  rw [lawFiniteConeHomologyEquiv, LinearEquiv.trans_apply,
    FiniteComplexFamily.homologyEquiv_component, homologyMap_comp]
  rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
