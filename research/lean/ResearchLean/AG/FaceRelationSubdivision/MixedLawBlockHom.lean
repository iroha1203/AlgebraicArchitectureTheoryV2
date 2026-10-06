import ResearchLean.AG.FaceRelationSubdivision.MixedLawBlock
import ResearchLean.AG.FaceRelationSubdivision.MixedLawFiniteHom
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteBlockHom

/-!
# 混在reading原始有限和の同じ実block Hom

## Implementation notes

各block成分を独立有限和で置き、同じ原始fiber射との等号から微分可換性を導く。
全Law projection正方形も原始項を照合し、実H1商への接続を保持する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable (Nc : TargetSupportedNerve qc) (Nf : TargetSupportedNerve qf)
variable (laws : FiniteLawFamily Source) (hc : laws.Adequate qc) (hf : laws.Adequate qf)
variable (M0 : SupportedBasisMap (sourceSupport qf Nf.chartSupport) (sourceSupport qc Nc.chartSupport))
variable (M1 : SupportedBasisMap (sourceSupport qf Nf.edgeSupport) (sourceSupport qc Nc.edgeSupport))
variable (M2 : SupportedBasisMap (sourceSupport qf Nf.faceSupport) (sourceSupport qc Nc.faceSupport))
variable (h01 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw = M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (h12 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw = M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 同じ原始三成分から独立生成する実block Hom。 -/
def mixedBlockFiniteHom (l : LawValueLabel laws) :
    ThreeCochainComplex.Hom (Nc.lawValueBlockComplex laws hc l)
      (Nf.lawValueBlockComplex laws hf l) where
  f0 := M0.mixedLawBlockDual laws hf hc l
  f1 := M1.mixedLawBlockDual laws hf hc l
  f2 := M2.mixedLawBlockDual laws hf hc l
  comm0 z := by
    apply (blockFiberEquiv laws hf Nf.edgeSupport l).injective
    exact (M1.mixedLawBlockDual_fiber laws hf hc l ((Nc.lawValueBlockComplex laws hc l).d0 z)).trans
      ((congrArg (dualCellMap (M1.mixedSelected (labelValueFiber laws qf hf l)
          (labelValueFiber laws qc hc l) (labelFiber_source_preimage laws hf hc l)))
          (blockFiber_d0 laws hc Nc l z)).trans
        (((mixedSubsetFiniteHom M0 M1 M2 h01 h12 (labelValueFiber laws qc hc l)
            (labelValueFiber laws qf hf l) (labelFiber_source_preimage laws hf hc l)).comm0
              (blockFiberEquiv laws hc Nc.chartSupport l z)).trans
          ((congrArg (Nf.targetSubsetComplex (labelValueFiber laws qf hf l)).d0
            (M0.mixedLawBlockDual_fiber laws hf hc l z).symm).trans
            (blockFiber_d0 laws hf Nf l (M0.mixedLawBlockDual laws hf hc l z)).symm)))
  comm1 z := by
    apply (blockFiberEquiv laws hf Nf.faceSupport l).injective
    exact (M2.mixedLawBlockDual_fiber laws hf hc l ((Nc.lawValueBlockComplex laws hc l).d1 z)).trans
      ((congrArg (dualCellMap (M2.mixedSelected (labelValueFiber laws qf hf l)
          (labelValueFiber laws qc hc l) (labelFiber_source_preimage laws hf hc l)))
          (blockFiber_d1 laws hc Nc l z)).trans
        (((mixedSubsetFiniteHom M0 M1 M2 h01 h12 (labelValueFiber laws qc hc l)
            (labelValueFiber laws qf hf l) (labelFiber_source_preimage laws hf hc l)).comm1
              (blockFiberEquiv laws hc Nc.edgeSupport l z)).trans
          ((congrArg (Nf.targetSubsetComplex (labelValueFiber laws qf hf l)).d1
            (M1.mixedLawBlockDual_fiber laws hf hc l z).symm).trans
            (blockFiber_d1 laws hf Nf l (M1.mixedLawBlockDual laws hf hc l z)).symm)))
/-- 実block Homの次数0は独立原始有限和。 -/
@[simp] theorem mixedBlockFiniteHom_f0 (l) :
    (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l).f0 = M0.mixedLawBlockDual laws hf hc l := rfl
/-- 実block Homの次数1は独立原始有限和。 -/
@[simp] theorem mixedBlockFiniteHom_f1 (l) :
    (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l).f1 = M1.mixedLawBlockDual laws hf hc l := rfl
/-- 実block Homの次数2は独立原始有限和。 -/
@[simp] theorem mixedBlockFiniteHom_f2 (l) :
    (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l).f2 = M2.mixedLawBlockDual laws hf hc l := rfl

/-- 全三成分で独立block有限和と同じ独立原始fiber射は可換。 -/
theorem mixedBlockFiniteFiber_square (l) :
    cochainComp (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l)
      (Nf.lawValueBlockTargetSubsetComplexEquiv laws hf l).toHom =
    cochainComp (Nc.lawValueBlockTargetSubsetComplexEquiv laws hc l).toHom
      (mixedSubsetFiniteHom M0 M1 M2 h01 h12 (labelValueFiber laws qc hc l)
        (labelValueFiber laws qf hf l) (labelFiber_source_preimage laws hf hc l)) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    exact M0.mixedLawBlockDual_fiber laws hf hc l z
  · apply LinearMap.ext; intro z
    exact M1.mixedLawBlockDual_fiber laws hf hc l z
  · apply LinearMap.ext; intro z
    exact M2.mixedLawBlockDual_fiber laws hf hc l z

/-- 全三成分で独立全Law有限和と独立block有限和の同じ実射は可換。 -/
theorem mixedLawFiniteBlock_square (l) :
    cochainComp (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12) (lawBlockHom laws hf Nf l) =
      cochainComp (lawBlockHom laws hc Nc l) (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, lawBlockHom_f0, lawBlockHom_f0,
      mixedLawFiniteHom_f0, mixedBlockFiniteHom_f0]
    exact M0.mixedLawDual_block laws hf hc l z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, lawBlockHom_f1, lawBlockHom_f1,
      mixedLawFiniteHom_f1, mixedBlockFiniteHom_f1]
    exact M1.mixedLawDual_block laws hf hc l z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, lawBlockHom_f2, lawBlockHom_f2,
      mixedLawFiniteHom_f2, mixedBlockFiniteHom_f2]
    exact M2.mixedLawDual_block laws hf hc l z

/-- 同じblock/fiber正方形は既存H1商でも可換。 -/
theorem mixedBlockFiniteFiber_h1_square (l) :
    (Nf.lawValueBlockTargetSubsetComplexEquiv laws hf l).toHom.h1Map.comp
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l).h1Map =
    (mixedSubsetFiniteHom M0 M1 M2 h01 h12 (labelValueFiber laws qc hc l)
      (labelValueFiber laws qf hf l) (labelFiber_source_preimage laws hf hc l)).h1Map.comp
        (Nc.lawValueBlockTargetSubsetComplexEquiv laws hc l).toHom.h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map
    (mixedBlockFiniteFiber_square Nc Nf laws hc hf M0 M1 M2 h01 h12 l)
  simpa only [cochainComp_h1Map] using h

/-- 同じ全Law/block正方形は既存H1商でも可換。 -/
theorem mixedLawFiniteBlock_h1_square (l) :
    (lawBlockHom laws hf Nf l).h1Map.comp (mixedLawFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12).h1Map =
      (mixedBlockFiniteHom Nc Nf laws hc hf M0 M1 M2 h01 h12 l).h1Map.comp (lawBlockHom laws hc Nc l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map
    (mixedLawFiniteBlock_square Nc Nf laws hc hf M0 M1 M2 h01 h12 l)
  simpa only [cochainComp_h1Map] using h

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
