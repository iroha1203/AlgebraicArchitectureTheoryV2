import ResearchLean.AG.FaceRelationSubdivision.OperationPathFunctor
import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetTransport

/-!
# 原始有限列の同じ実subset射の空列と連結

## Implementation notes

支持逆像の原始等号で複体全体を移送し、全三成分の直接射を段階合成へ接続する。
対象型の一致を非公式に省略する案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {qc qm qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nm : TargetSupportedNerve qm} {Nf : TargetSupportedNerve qf}
namespace PrimitiveOperationPath
/-- 空列の同じ実subset R射は、全対象等号移送後に恒等。 -/
theorem subsetR_nil (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    subsetTransportHom (congrArg N.targetSubsetComplex (targetSubset_nil N A)) ((nil N).subsetR A) =
      cochainId (N.targetSubsetComplex A) := by
  rw [subsetR_eq_raw, rawEquivalence_nil, RawChainEquivalence.targetRHom_transport (hAf := targetSubset_nil N A)]
  exact RawChainEquivalence.targetRHom_refl N A

/-- 空列の同じ実subset S射は、全対象等号移送後に恒等。 -/
theorem subsetS_nil (N : TargetSupportedNerve qc) (A : Set qc.Target) :
    subsetSourceTransportHom (congrArg N.targetSubsetComplex (targetSubset_nil N A)) ((nil N).subsetS A) =
      cochainId (N.targetSubsetComplex A) := by
  rw [subsetS_eq_raw, rawEquivalence_nil, RawChainEquivalence.targetSHom_transport (hAf := targetSubset_nil N A)]
  exact RawChainEquivalence.targetSHom_refl N A

variable (P : PrimitiveOperationPath qc Nc qm Nm) (Q : PrimitiveOperationPath qm Nm qf Nf)
/-- 連結列の直接subset R射は、同じ支持対象移送後に段階合成。 -/
theorem subsetR_append (A : Set qc.Target) :
    subsetTransportHom (congrArg Nf.targetSubsetComplex (P.targetSubset_append Q A))
      ((P.append Q).subsetR A) = cochainComp (P.subsetR A) (Q.subsetR (P.targetSubset A)) := by
  rw [subsetR_eq_raw, rawEquivalence_append, RawChainEquivalence.targetRHom_transport (hAf := P.targetSubset_append Q A),
    subsetR_eq_raw, subsetR_eq_raw]
  exact P.rawEquivalence.targetRHom_trans Q.rawEquivalence A (P.targetSubset A)
    (Q.targetSubset (P.targetSubset A)) (P.source_subset_eq A) (Q.source_subset_eq (P.targetSubset A))

/-- 連結列の直接subset S射は、同じ支持対象移送後に段階合成。 -/
theorem subsetS_append (A : Set qc.Target) :
    subsetSourceTransportHom (congrArg Nf.targetSubsetComplex (P.targetSubset_append Q A))
      ((P.append Q).subsetS A) = cochainComp (Q.subsetS (P.targetSubset A)) (P.subsetS A) := by
  rw [subsetS_eq_raw, rawEquivalence_append, RawChainEquivalence.targetSHom_transport (hAf := P.targetSubset_append Q A),
    subsetS_eq_raw, subsetS_eq_raw]
  exact P.rawEquivalence.targetSHom_trans Q.rawEquivalence A (P.targetSubset A)
    (Q.targetSubset (P.targetSubset A)) (P.source_subset_eq A) (Q.source_subset_eq (P.targetSubset A))

end PrimitiveOperationPath
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
