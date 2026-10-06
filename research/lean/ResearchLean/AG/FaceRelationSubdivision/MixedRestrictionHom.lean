import ResearchLean.AG.FaceRelationSubdivision.MixedSupportRestriction
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom
import ResearchLean.AG.FaceRelationSubdivision.SubsetRestriction

/-!
# 混在readingの同じ実射と支持制限

## Implementation notes

原始有限和の包含自然性を双対化し、実複体の全三成分へ渡す。
逆射と両補正も同じ基底包含を使う。各Aで無関係な同値を選ぶ案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf)
variable {Ac Bc : Set qc.Target} {Af Bf : Set qf.Target}
variable (hc : Ac ⊆ Bc) (hf : Af ⊆ Bf)
variable (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac) (hB : qf.read ⁻¹' Bf = qc.read ⁻¹' Bc)

/-- 全三成分で同じ実R射と支持制限は可換。 -/
theorem targetR_restrict_square :
    cochainComp (P.targetRHom Bc Bf hB) (subsetRestrictHom Nf hf) =
      cochainComp (subsetRestrictHom Nc hc) (P.targetRHom Ac Af hA) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, targetRHom_f0, targetRHom_f0,
      subsetRestrictHom_f0, subsetRestrictHom_f0]
    exact LinearMap.congr_fun (P.r0.mixedSelected_dual_restrict_natural Af Bf Ac Bc hf hc hA hB) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, targetRHom_f1, targetRHom_f1,
      subsetRestrictHom_f1, subsetRestrictHom_f1]
    exact LinearMap.congr_fun (P.r1.mixedSelected_dual_restrict_natural Af Bf Ac Bc hf hc hA hB) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, targetRHom_f2, targetRHom_f2,
      subsetRestrictHom_f2, subsetRestrictHom_f2]
    exact LinearMap.congr_fun (P.r2.mixedSelected_dual_restrict_natural Af Bf Ac Bc hf hc hA hB) z
/-- 同じ実R射の支持制限正方形は既存H1でも可換。 -/
theorem targetR_restrict_h1_square :
    (subsetRestrictHom Nf hf).h1Map.comp (P.targetRHom Bc Bf hB).h1Map =
      (P.targetRHom Ac Af hA).h1Map.comp (subsetRestrictHom Nc hc).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (P.targetR_restrict_square hc hf hA hB)
  simpa only [cochainComp_h1Map] using h
/-- 全三成分で同じ実S射と支持制限は可換。 -/
theorem targetS_restrict_square :
    cochainComp (P.targetSHom Bc Bf hB) (subsetRestrictHom Nc hc) =
      cochainComp (subsetRestrictHom Nf hf) (P.targetSHom Ac Af hA) := by
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [cochainComp_f0, cochainComp_f0, targetSHom_f0, targetSHom_f0,
      subsetRestrictHom_f0, subsetRestrictHom_f0]
    exact LinearMap.congr_fun (P.s0.mixedSelected_dual_restrict_natural Ac Bc Af Bf hc hf hA.symm hB.symm) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f1, cochainComp_f1, targetSHom_f1, targetSHom_f1,
      subsetRestrictHom_f1, subsetRestrictHom_f1]
    exact LinearMap.congr_fun (P.s1.mixedSelected_dual_restrict_natural Ac Bc Af Bf hc hf hA.symm hB.symm) z
  · apply LinearMap.ext; intro z
    rw [cochainComp_f2, cochainComp_f2, targetSHom_f2, targetSHom_f2,
      subsetRestrictHom_f2, subsetRestrictHom_f2]
    exact LinearMap.congr_fun (P.s2.mixedSelected_dual_restrict_natural Ac Bc Af Bf hc hf hA.symm hB.symm) z
/-- 同じ実S射の支持制限正方形は既存H1でも可換。 -/
theorem targetS_restrict_h1_square :
    (subsetRestrictHom Nc hc).h1Map.comp (P.targetSHom Bc Bf hB).h1Map =
      (P.targetSHom Ac Af hA).h1Map.comp (subsetRestrictHom Nf hf).h1Map := by
  have h := congrArg ThreeCochainComplex.Hom.h1Map (P.targetS_restrict_square hc hf hA hB)
  simpa only [cochainComp_h1Map] using h
/-- 同じ原始補正h0の実双対も支持制限と可換。 -/
theorem target_h0_restrict_natural :
    (selectedRestrict Nf.chartSupport hf).comp (dualCellMap (P.h0.mixedSelected Bf Bf rfl)) =
      (dualCellMap (P.h0.mixedSelected Af Af rfl)).comp
        (selectedRestrict Nf.edgeSupport hf) :=
  P.h0.mixedSelected_dual_restrict_natural Af Bf Af Bf hf hf rfl rfl

/-- 同じ原始補正h1の実双対も支持制限と可換。 -/
theorem target_h1_restrict_natural :
    (selectedRestrict Nf.edgeSupport hf).comp (dualCellMap (P.h1.mixedSelected Bf Bf rfl)) =
      (dualCellMap (P.h1.mixedSelected Af Af rfl)).comp
        (selectedRestrict Nf.faceSupport hf) :=
  P.h1.mixedSelected_dual_restrict_natural Af Bf Af Bf hf hf rfl rfl

/-- 同じ原始補正k0の実双対も支持制限と可換。 -/
theorem target_k0_restrict_natural :
    (selectedRestrict Nc.chartSupport hc).comp (dualCellMap (P.k0.mixedSelected Bc Bc rfl)) =
      (dualCellMap (P.k0.mixedSelected Ac Ac rfl)).comp
        (selectedRestrict Nc.edgeSupport hc) :=
  P.k0.mixedSelected_dual_restrict_natural Ac Bc Ac Bc hc hc rfl rfl

/-- 同じ原始補正k1の実双対も支持制限と可換。 -/
theorem target_k1_restrict_natural :
    (selectedRestrict Nc.edgeSupport hc).comp (dualCellMap (P.k1.mixedSelected Bc Bc rfl)) =
      (dualCellMap (P.k1.mixedSelected Ac Ac rfl)).comp
        (selectedRestrict Nc.faceSupport hc) :=
  P.k1.mixedSelected_dual_restrict_natural Ac Bc Ac Bc hc hc rfl rfl

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
