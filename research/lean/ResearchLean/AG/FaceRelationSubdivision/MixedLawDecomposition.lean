import ResearchLean.AG.FaceRelationSubdivision.LawFiniteDecomposition
import ResearchLean.AG.FaceRelationSubdivision.MixedLawBlockHom

/-!
# 混在reading原始有限和の同じ実診断分解

## Implementation notes

原始項ごとの実全Law/block可換式で既存の族比較bridgeを放電する。
同じH1射の核・余核と同じ標準錐を全発生ラベルに分解し、ラベル重複を保持する。
次元一致だけによる保存主張は採らない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 標準有限積から複体の有限双積を得て、実Law錐の有限直和APIへ局所適用する。 -/
local instance mixedLawDecompositionBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
variable (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
variable (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
variable (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 原始独立Law有限和次数0は同じ独立block有限和と可換。 -/
theorem mixedLawFiniteFamily_natural0 (x) (l) :
    lawFamily0Equiv Nf laws hf ((mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).f0 x) l =
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).f0 (lawFamily0Equiv Nc laws hc x l) := by
  rw [lawFamily0Equiv_eq_read, lawFamily0Equiv_eq_read, mixedLawFiniteHom_f0, mixedBlockFiniteHom_f0]
  exact M0.mixedLawDual_block laws hf hc l x
/-- 原始独立Law有限和次数1は同じ独立block有限和と可換。 -/
theorem mixedLawFiniteFamily_natural1 (x) (l) :
    lawFamily1Equiv Nf laws hf ((mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).f1 x) l =
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).f1 (lawFamily1Equiv Nc laws hc x l) := by
  rw [lawFamily1Equiv_eq_read, lawFamily1Equiv_eq_read, mixedLawFiniteHom_f1, mixedBlockFiniteHom_f1]
  exact M1.mixedLawDual_block laws hf hc l x
/-- 原始独立Law有限和次数2は同じ独立block有限和と可換。 -/
theorem mixedLawFiniteFamily_natural2 (x) (l) :
    lawFamily2Equiv Nf laws hf ((mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).f2 x) l =
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).f2 (lawFamily2Equiv Nc laws hc x l) := by
  rw [lawFamily2Equiv_eq_read, lawFamily2Equiv_eq_read, mixedLawFiniteHom_f2, mixedBlockFiniteHom_f2]
  exact M2.mixedLawDual_block laws hf hc l x

/-- 原始Law/block有限和の同じ全三成分族正方形。 -/
theorem mixedLawFiniteFamily_square : cochainComp (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1)
    (lawFamilyCochainEquiv Nf laws hf).toHom =
      cochainComp (lawFamilyCochainEquiv Nc laws hc).toHom
        (ThreeComplexFamily.map (fun l => Nc.lawValueBlockComplex laws hc l)
          (fun l => Nf.lawValueBlockComplex laws hf l)
          (fun l => mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l)) :=
  LawMapDecomposition.family_square Nc Nf laws hc hf _ _
    (mixedLawFiniteFamily_natural0 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural1 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural2 laws hc hf M0 M1 M2 h0 h1)

/-- 同じ独立原始有限和を全次数の標準Law/ラベル射へ接続。 -/
theorem mixedLawFiniteZeroExtension_square : zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1) ≫
    (lawZeroExtensionIso Nf laws hf).hom = (lawZeroExtensionIso Nc laws hc).hom ≫
      FiniteComplexFamily.map (fun l => zeroExtension (Nc.lawValueBlockComplex laws hc l))
        (fun l => zeroExtension (Nf.lawValueBlockComplex laws hf l))
        (fun l => zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l)) :=
  LawMapDecomposition.zeroExtension_square Nc Nf laws hc hf _ _
    (mixedLawFiniteFamily_natural0 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural1 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural2 laws hc hf M0 M1 M2 h0 h1)

/-- 同じ原始有限和の全次数homologyも同じラベル射に分解する。 -/
theorem mixedLawFiniteStandardHomology_natural (m : ℤ)
    (x : (zeroExtension (Nc.lawGeneratedComplex laws hc)).homology m) (l : LawValueLabel laws) :
    lawStandardHomologyEquiv Nf laws hf m
        (homologyMap (zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1)) m x) l =
      homologyMap (zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l)) m
        (lawStandardHomologyEquiv Nc laws hc m x l) :=
  LawMapDecomposition.standard_homology_natural Nc Nf laws hc hf _ _
    (mixedLawFiniteFamily_natural0 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural1 laws hc hf M0 M1 M2 h0 h1)
    (mixedLawFiniteFamily_natural2 laws hc hf M0 M1 M2 h0 h1) m x l

/-- 同じ原始有限和は旧H1商でも各独立ラベル射へ分解する。 -/
theorem mixedLawFiniteH1Family_natural (x : (Nc.lawGeneratedComplex laws hc).H1) (l : LawValueLabel laws) :
    lawH1FamilyEquiv Nf laws hf ((mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map x) l =
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map (lawH1FamilyEquiv Nc laws hc x l) :=
  LawMapDecomposition.h1_natural Nc Nf laws hc hf _ _
    (mixedLawFiniteFamily_natural1 laws hc hf M0 M1 M2 h0 h1) x l

/-- 同じ原始有限和の既存H1族比較正方形。 -/
theorem mixedLawFiniteH1Family_square (x : (Nc.lawGeneratedComplex laws hc).H1) :
    lawH1FamilyEquiv Nf laws hf ((mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map x) =
      FiniteLinearFamily.map (fun l => (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map)
        (lawH1FamilyEquiv Nc laws hc x) := by
  funext l
  exact mixedLawFiniteH1Family_natural laws hc hf M0 M1 M2 h0 h1 x l

/-- 原始独立Law有限和の実H1核は同じ独立ラベル核の族。 -/
def mixedLawFiniteKernelFamilyEquiv :
    LinearMap.ker (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → LinearMap.ker (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map) :=
  (LinearConjugation.kernelEquiv _ _ (lawH1FamilyEquiv Nc laws hc)
    (lawH1FamilyEquiv Nf laws hf) (mixedLawFiniteH1Family_square laws hc hf M0 M1 M2 h0 h1)).trans
      (FiniteLinearFamily.kernelEquiv _)

/-- 原始独立Law有限和の実H1余核は同じ独立ラベル余核の族。 -/
def mixedLawFiniteCokernelFamilyEquiv :
    ((Nf.lawGeneratedComplex laws hf).H1 ⧸ LinearMap.range (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map) ≃ₗ[ℚ]
      ((l : LawValueLabel laws) → (Nf.lawValueBlockComplex laws hf l).H1 ⧸
        LinearMap.range (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map) :=
  (LinearConjugation.cokernelEquiv _ _ (lawH1FamilyEquiv Nc laws hc)
    (lawH1FamilyEquiv Nf laws hf) (mixedLawFiniteH1Family_square laws hc hf M0 M1 M2 h0 h1)).trans
      (FiniteLinearFamily.cokernelEquiv _)

/-- 実核同定は同じsource H1類のラベル成分を読む。 -/
@[simp] theorem mixedLawFiniteKernelFamilyEquiv_val
    (x : LinearMap.ker (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map) (l : LawValueLabel laws) :
    (mixedLawFiniteKernelFamilyEquiv laws hc hf M0 M1 M2 h0 h1 x l).val =
      lawH1FamilyEquiv Nc laws hc x.val l := rfl

/-- 実余核同定は同じtarget H1代表元の各ラベル商類を読む。 -/
@[simp] theorem mixedLawFiniteCokernelFamilyEquiv_mk (x : (Nf.lawGeneratedComplex laws hf).H1)
    (l : LawValueLabel laws) : mixedLawFiniteCokernelFamilyEquiv laws hc hf M0 M1 M2 h0 h1
      ((LinearMap.range (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map).mkQ x) l =
        (LinearMap.range (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map).mkQ
          (lawH1FamilyEquiv Nf laws hf x l) := by
  rw [mixedLawFiniteCokernelFamilyEquiv, LinearEquiv.trans_apply,
    LinearConjugation.cokernelEquiv_mk, FiniteLinearFamily.cokernelEquiv_mk]

/-- 原始実有限和の欠損は重複を保持した全発生ラベルの実欠損の和。 -/
theorem mixedLawFiniteDefect_sum : blockDefect (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1).h1Map =
    (∑ l, (blockDefect (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map).1,
      ∑ l, (blockDefect (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l).h1Map).2) := by
  apply Prod.ext
  · simp only [blockDefect_kernel_dimension]
    rw [(mixedLawFiniteKernelFamilyEquiv laws hc hf M0 M1 M2 h0 h1).finrank_eq]
    exact Module.finrank_pi_fintype ℚ
  · simp only [blockDefect_cokernel_dimension]
    rw [(mixedLawFiniteCokernelFamilyEquiv laws hc hf M0 M1 M2 h0 h1).finrank_eq]
    exact Module.finrank_pi_fintype ℚ

/-- 全Law実有限和射の同じ標準錐を実ラベル錐の族へ接続。 -/
def mixedLawFiniteConeFamilyIso : mappingCone (zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1)) ≅
    FiniteComplexFamily.complex (fun l =>
      mappingCone (zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l))) :=
  coneMapIso _ _ (lawZeroExtensionIso Nc laws hc) (lawZeroExtensionIso Nf laws hf)
      (mixedLawFiniteZeroExtension_square laws hc hf M0 M1 M2 h0 h1) ≪≫
    FiniteConeFamily.iso (fun l => zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l))

/-- 同じ独立有限和の実錐を重複を保ったラベル錐の有限直和へ接続。 -/
def mixedLawFiniteConeDirectSumIso : mappingCone (zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1)) ≅
    biproduct (fun l => mappingCone (zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l))) :=
  mixedLawFiniteConeFamilyIso laws hc hf M0 M1 M2 h0 h1 ≪≫ FiniteComplexFamily.directSumIso _

/-- 同じ実Law有限和錐の全整数次数を同じラベル錐へ読む。 -/
def mixedLawFiniteConeHomologyEquiv (m : ℤ) :
    (mappingCone (zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1))).homology m ≃ₗ[ℚ]
      ((l : LawValueLabel laws) →
        (mappingCone (zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l))).homology m) :=
  (homologyMapIso (mixedLawFiniteConeFamilyIso laws hc hf M0 M1 M2 h0 h1) m).toLinearEquiv.trans
    (FiniteComplexFamily.homologyEquiv _ m)

/-- 実有限和錐族の順射は同じ二段の標準構成。 -/
@[simp] theorem mixedLawFiniteConeFamilyIso_hom : (mixedLawFiniteConeFamilyIso laws hc hf M0 M1 M2 h0 h1).hom =
    (coneMapIso _ _ (lawZeroExtensionIso Nc laws hc) (lawZeroExtensionIso Nf laws hf)
      (mixedLawFiniteZeroExtension_square laws hc hf M0 M1 M2 h0 h1)).hom ≫
        (FiniteConeFamily.iso (fun l => zeroExtensionMap (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1 l))).hom := rfl

/-- 同じ有限和錐homology族の成分は実projectionの写像。 -/
theorem mixedLawFiniteConeHomologyEquiv_component (m : ℤ)
    (x : (mappingCone (zeroExtensionMap (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h0 h1))).homology m)
    (l : LawValueLabel laws) : mixedLawFiniteConeHomologyEquiv laws hc hf M0 M1 M2 h0 h1 m x l =
      homologyMap ((mixedLawFiniteConeFamilyIso laws hc hf M0 M1 M2 h0 h1).hom ≫
        FiniteComplexFamily.projection _ l) m x := by
  rw [mixedLawFiniteConeHomologyEquiv, LinearEquiv.trans_apply,
    FiniteComplexFamily.homologyEquiv_component, homologyMap_comp]
  rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
