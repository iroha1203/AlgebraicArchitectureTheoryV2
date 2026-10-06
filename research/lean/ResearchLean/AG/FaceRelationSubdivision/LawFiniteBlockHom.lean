import ResearchLean.AG.FaceRelationSubdivision.LawFiniteBlock
import Formal.Util.AssertStandardAxioms

/-!
# 原始有限和の同じ実block Hom

## Implementation notes

block有限和の全三成分を使い、微分可換性を同じfiber射から証明する。
同型による射の存在だけで有限和の成分等号を代替しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {q : Reading Source}
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- 同じblock/fiber座標同定の実微分d0可換式。 -/
theorem blockFiber_d0 (N : ResolutionInvariance.TargetSupportedNerve q)
    (l : LawValueLabel laws) (z : (N.lawValueBlockComplex laws ha l).C0) :
    blockFiberEquiv laws ha N.edgeSupport l ((N.lawValueBlockComplex laws ha l).d0 z) =
      (N.targetSubsetComplex (labelValueFiber laws q ha l)).d0
        (blockFiberEquiv laws ha N.chartSupport l z) :=
  N.labelFiberCochainEquiv_comm0 laws ha l z
/-- 同じblock/fiber座標同定の実微分d1可換式。 -/
theorem blockFiber_d1 (N : ResolutionInvariance.TargetSupportedNerve q)
    (l : LawValueLabel laws) (z : (N.lawValueBlockComplex laws ha l).C1) :
    blockFiberEquiv laws ha N.faceSupport l ((N.lawValueBlockComplex laws ha l).d1 z) =
      (N.targetSubsetComplex (labelValueFiber laws q ha l)).d1
        (blockFiberEquiv laws ha N.edgeSupport l z) :=
  N.labelFiberCochainEquiv_comm1 laws ha l z

/-- 全Lawの同じfiber projectionを実blockへ読むcochain Hom。 -/
def lawBlockHom (N : ResolutionInvariance.TargetSupportedNerve q) (l : LawValueLabel laws) :
    ThreeCochainComplex.Hom (N.lawGeneratedComplex laws ha) (N.lawValueBlockComplex laws ha l) :=
  cochainComp (lawFiberHom laws ha N l) (N.lawValueBlockTargetSubsetComplexEquiv laws ha l).symm.toHom

/-- 同じ実block projectionの次数0は座標制限そのもの。 -/
@[simp] theorem lawBlockHom_f0 (N) (l) :
    (lawBlockHom laws ha N l).f0 = lawBlockRead laws ha N.chartSupport l := by
  apply LinearMap.ext
  intro z
  apply (blockFiberEquiv laws ha N.chartSupport l).injective
  exact (LinearEquiv.apply_symm_apply (blockFiberEquiv laws ha N.chartSupport l) _).trans
    (blockFiberEquiv_read laws ha N.chartSupport l z).symm

/-- 同じ実block projectionの次数1は座標制限そのもの。 -/
@[simp] theorem lawBlockHom_f1 (N) (l) :
    (lawBlockHom laws ha N l).f1 = lawBlockRead laws ha N.edgeSupport l := by
  apply LinearMap.ext
  intro z
  apply (blockFiberEquiv laws ha N.edgeSupport l).injective
  exact (LinearEquiv.apply_symm_apply (blockFiberEquiv laws ha N.edgeSupport l) _).trans
    (blockFiberEquiv_read laws ha N.edgeSupport l z).symm

/-- 同じ実block projectionの次数2は座標制限そのもの。 -/
@[simp] theorem lawBlockHom_f2 (N) (l) :
    (lawBlockHom laws ha N l).f2 = lawBlockRead laws ha N.faceSupport l := by
  apply LinearMap.ext
  intro z
  apply (blockFiberEquiv laws ha N.faceSupport l).injective
  exact (LinearEquiv.apply_symm_apply (blockFiberEquiv laws ha N.faceSupport l) _).trans
    (blockFiberEquiv_read laws ha N.faceSupport l z).symm


variable {Nc Nf : ResolutionInvariance.TargetSupportedNerve q}
variable (M0 : SupportedBasisMap Nf.chartSupport Nc.chartSupport)
variable (M1 : SupportedBasisMap Nf.edgeSupport Nc.edgeSupport)
variable (M2 : SupportedBasisMap Nf.faceSupport Nc.faceSupport)
variable (h0 : (TargetSupportedNerve.rawD1 Nc).raw.comp M1.raw =
    M0.raw.comp (TargetSupportedNerve.rawD1 Nf).raw)
variable (h1 : (TargetSupportedNerve.rawD2 Nc).raw.comp M2.raw =
    M1.raw.comp (TargetSupportedNerve.rawD2 Nf).raw)

/-- 同じ原始三成分を独立生成した実block Hom。 -/
def blockFiniteHom (l : LawValueLabel laws) :
    ThreeCochainComplex.Hom (Nc.lawValueBlockComplex laws ha l)
      (Nf.lawValueBlockComplex laws ha l) where
  f0 := M0.lawBlockDual laws ha l
  f1 := M1.lawBlockDual laws ha l
  f2 := M2.lawBlockDual laws ha l
  comm0 z := by
    apply (blockFiberEquiv laws ha Nf.edgeSupport l).injective
    exact (M1.lawBlockDual_fiber laws ha l ((Nc.lawValueBlockComplex laws ha l).d0 z)).trans
      ((congrArg (dualCellMap (M1.selected (labelValueFiber laws q ha l)))
          (blockFiber_d0 laws ha Nc l z)).trans
        (((subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)).comm0
            (blockFiberEquiv laws ha Nc.chartSupport l z)).trans
          ((congrArg (Nf.targetSubsetComplex (labelValueFiber laws q ha l)).d0
            (M0.lawBlockDual_fiber laws ha l z).symm).trans
            (blockFiber_d0 laws ha Nf l (M0.lawBlockDual laws ha l z)).symm)))

  comm1 z := by
    apply (blockFiberEquiv laws ha Nf.faceSupport l).injective
    exact (M2.lawBlockDual_fiber laws ha l ((Nc.lawValueBlockComplex laws ha l).d1 z)).trans
      ((congrArg (dualCellMap (M2.selected (labelValueFiber laws q ha l)))
          (blockFiber_d1 laws ha Nc l z)).trans
        (((subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)).comm1
            (blockFiberEquiv laws ha Nc.edgeSupport l z)).trans
          ((congrArg (Nf.targetSubsetComplex (labelValueFiber laws q ha l)).d1
            (M1.lawBlockDual_fiber laws ha l z).symm).trans
            (blockFiber_d1 laws ha Nf l (M1.lawBlockDual laws ha l z)).symm)))

/-- 実block Homの次数0有限和。 -/
@[simp] theorem blockFiniteHom_f0 (l) :
    (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f0 = M0.lawBlockDual laws ha l := rfl
/-- 実block Homの次数1有限和。 -/
@[simp] theorem blockFiniteHom_f1 (l) :
    (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f1 = M1.lawBlockDual laws ha l := rfl
/-- 実block Homの次数2有限和。 -/
@[simp] theorem blockFiniteHom_f2 (l) :
    (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).f2 = M2.lawBlockDual laws ha l := rfl

/-- 全三成分で、独立block有限和と同じ原始fiber射は可換。 -/
theorem blockFiniteFiber_square (l) :
    cochainComp (blockFiniteHom laws ha M0 M1 M2 h0 h1 l)
      (Nf.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom =
    cochainComp (Nc.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom
      (subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    exact M0.lawBlockDual_fiber laws ha l z
  · apply LinearMap.ext
    intro z
    exact M1.lawBlockDual_fiber laws ha l z
  · apply LinearMap.ext
    intro z
    exact M2.lawBlockDual_fiber laws ha l z

/-- 同じblock/fiber正方形の既存H1写像等号。 -/
theorem blockFiniteFiber_h1_square (l) :
    (Nf.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom.h1Map.comp
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map =
    (subsetFiniteHom M0 M1 M2 h0 h1 (labelValueFiber laws q ha l)).h1Map.comp
      (Nc.lawValueBlockTargetSubsetComplexEquiv laws ha l).toHom.h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map
    (blockFiniteFiber_square laws ha M0 M1 M2 h0 h1 l)
  simpa only [cochainComp_h1Map] using h

/-- 全三成分で、独立全Law有限和と独立block有限和の実射は可換。 -/
theorem lawFiniteBlock_square (l) :
    cochainComp (lawFiniteHom M0 M1 M2 h0 h1 laws ha) (lawBlockHom laws ha Nf l) =
      cochainComp (lawBlockHom laws ha Nc l) (blockFiniteHom laws ha M0 M1 M2 h0 h1 l) := by
  apply cochain_ext
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f0, cochainComp_f0]
    rw [lawBlockHom_f0, lawBlockHom_f0, lawFiniteHom_f0, blockFiniteHom_f0]
    exact M0.lawDual_block laws ha l z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f1, cochainComp_f1]
    rw [lawBlockHom_f1, lawBlockHom_f1, lawFiniteHom_f1, blockFiniteHom_f1]
    exact M1.lawDual_block laws ha l z
  · apply LinearMap.ext
    intro z
    rw [cochainComp_f2, cochainComp_f2]
    rw [lawBlockHom_f2, lawBlockHom_f2, lawFiniteHom_f2, blockFiniteHom_f2]
    exact M2.lawDual_block laws ha l z

/-- 同じ全Law/block正方形の実H1商も可換。 -/
theorem lawFiniteBlock_h1_square (l) :
    (lawBlockHom laws ha Nf l).h1Map.comp (lawFiniteHom M0 M1 M2 h0 h1 laws ha).h1Map =
      (blockFiniteHom laws ha M0 M1 M2 h0 h1 l).h1Map.comp (lawBlockHom laws ha Nc l).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map
    (lawFiniteBlock_square laws ha M0 M1 M2 h0 h1 l)
  simpa only [cochainComp_h1Map] using h

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
