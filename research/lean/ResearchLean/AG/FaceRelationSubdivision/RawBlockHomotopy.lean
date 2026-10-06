import ResearchLean.AG.FaceRelationSubdivision.MixedLawBlockHom
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHomotopy
import ResearchLean.AG.FaceRelationSubdivision.ElementaryBlockHomotopy

/-!
# 同じ混在reading原始r/sの実block標準ホモトピー同値

## Implementation notes

全ラベルで独立生成したblock射を原始fiber射へ三成分で照合してから
同じfiber標準ホモトピーを移す。対象同型だけによる保存証明は採らない。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source] {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (laws : FiniteLawFamily Source)
variable (hc : laws.Adequate qc) (hf : laws.Adequate qf) (l : LawValueLabel laws)

/-- 同じ原始rの独立実block比較。 -/
def blockR := mixedBlockFiniteHom Nc Nf laws hc hf P.r0 P.r1 P.r2 P.r_comm01 P.r_comm12 l
/-- 同じ原始sの独立実逆block比較。 -/
def blockS := mixedBlockFiniteHom Nf Nc laws hf hc P.s0 P.s1 P.s2 P.s_comm01 P.s_comm12 l
/-- 実block Rの次数0は同じ独立原始有限和。 -/
@[simp] theorem blockR_f0 : (P.blockR laws hc hf l).f0 = P.r0.mixedLawBlockDual laws hf hc l := rfl
/-- 実block Rの次数1は同じ独立原始有限和。 -/
@[simp] theorem blockR_f1 : (P.blockR laws hc hf l).f1 = P.r1.mixedLawBlockDual laws hf hc l := rfl
/-- 実block Rの次数2は同じ独立原始有限和。 -/
@[simp] theorem blockR_f2 : (P.blockR laws hc hf l).f2 = P.r2.mixedLawBlockDual laws hf hc l := rfl
/-- 実block Sの次数0は同じ独立原始有限和。 -/
@[simp] theorem blockS_f0 : (P.blockS laws hc hf l).f0 = P.s0.mixedLawBlockDual laws hc hf l := rfl
/-- 実block Sの次数1は同じ独立原始有限和。 -/
@[simp] theorem blockS_f1 : (P.blockS laws hc hf l).f1 = P.s1.mixedLawBlockDual laws hc hf l := rfl
/-- 実block Sの次数2は同じ独立原始有限和。 -/
@[simp] theorem blockS_f2 : (P.blockS laws hc hf l).f2 = P.s2.mixedLawBlockDual laws hc hf l := rfl

/-- 同じ実block順射は全三成分で独立実fiber射へ接続する。 -/
theorem blockR_fiber :
    cochainComp (P.blockR laws hc hf l) (Nf.lawValueBlockTargetSubsetComplexEquiv laws hf l).toHom =
      cochainComp (Nc.lawValueBlockTargetSubsetComplexEquiv laws hc l).toHom
        (P.targetRHom (labelValueFiber laws qc hc l) (labelValueFiber laws qf hf l)
          (labelFiber_source_preimage laws hf hc l)) :=
  mixedBlockFiniteFiber_square Nc Nf laws hc hf P.r0 P.r1 P.r2 P.r_comm01 P.r_comm12 l

/-- 同じ実block逆射も全三成分で独立実fiber逆射へ接続する。 -/
theorem blockS_fiber :
    cochainComp (P.blockS laws hc hf l) (Nc.lawValueBlockTargetSubsetComplexEquiv laws hc l).toHom =
      cochainComp (Nf.lawValueBlockTargetSubsetComplexEquiv laws hf l).toHom
        (P.targetSHom (labelValueFiber laws qc hc l) (labelValueFiber laws qf hf l)
          (labelFiber_source_preimage laws hf hc l)) :=
  mixedBlockFiniteFiber_square Nf Nc laws hf hc P.s0 P.s1 P.s2 P.s_comm01 P.s_comm12 l

/-- 原始fiber補正から同じ独立block正逆射の標準同値を生成する。 -/
def blockHomotopyEquiv := transportHomotopyEquiv
  (P.targetHomotopyEquiv (labelValueFiber laws qc hc l) (labelValueFiber laws qf hf l)
    (labelFiber_source_preimage laws hf hc l))
  (lawBlockFiberZeroExtensionIso Nc laws hc l) (lawBlockFiberZeroExtensionIso Nf laws hf l)

/-- 移送後の標準順射は独立生成した同じ実block比較。 -/
theorem blockHomotopyEquiv_hom : (P.blockHomotopyEquiv laws hc hf l).hom =
    zeroExtensionMap (P.blockR laws hc hf l) := by
  apply transportHomotopyEquiv_hom_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    targetHomotopyEquiv_hom, ← zeroExtensionMap_comp, ← zeroExtensionMap_comp, blockR_fiber]

/-- 移送後の標準逆射も独立生成した同じ実逆block比較。 -/
theorem blockHomotopyEquiv_inv : (P.blockHomotopyEquiv laws hc hf l).inv =
    zeroExtensionMap (P.blockS laws hc hf l) := by
  apply transportHomotopyEquiv_inv_eq
  rw [lawBlockFiberZeroExtensionIso_hom, lawBlockFiberZeroExtensionIso_hom,
    targetHomotopyEquiv_inv, ← zeroExtensionMap_comp, ← zeroExtensionMap_comp, blockS_fiber]

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
