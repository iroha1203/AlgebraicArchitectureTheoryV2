import ResearchLean.AG.FaceRelationSubdivision.SupportedBasis
import Formal.Util.AssertStandardAxioms

/-!
# 原始全セルchainから任意の支持chainへ

## Implementation notes

微分を全セル名の基底像として先に構成し、各非零項への台包含をK1から導く。
Aごとに基底式を別々に再実装する案は自然性と有限和の検算を重複させるため採らない。
選択セルへの零延長を通して、既存SupportedChainの同じ微分との一致を検査する。
-/

noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source : Type u} {q : Reading Source}
namespace TargetSupportedNerve
variable (N : ResolutionInvariance.TargetSupportedNerve q)

/-- 辺の右端点の原始基底射。K1台包含は交差から導く。 -/
def rightBasis : SupportedBasisMap N.edgeSupport N.chartSupport :=
  SupportedBasisMap.ofSingle N.nerve.edgeRight
    (fun e _ ht => ((N.mem_edgeSupport_iff e _).mp ht).2)

/-- 辺の左端点の原始基底射。 -/
def leftBasis : SupportedBasisMap N.edgeSupport N.chartSupport :=
  SupportedBasisMap.ofSingle N.nerve.edgeLeft
    (fun e _ ht => ((N.mem_edgeSupport_iff e _).mp ht).1)

/-- 面の第0辺の原始基底射。 -/
def face0Basis : SupportedBasisMap N.faceSupport N.edgeSupport :=
  SupportedBasisMap.ofSingle N.nerve.faceEdge0
    (fun f _ ht => ((N.mem_faceSupport_iff f _).mp ht).1)

/-- 面の第1辺の原始基底射。 -/
def face1Basis : SupportedBasisMap N.faceSupport N.edgeSupport :=
  SupportedBasisMap.ofSingle N.nerve.faceEdge1
    (fun f _ ht => ((N.mem_faceSupport_iff f _).mp ht).2.1)

/-- 面の第2辺の原始基底射。 -/
def face2Basis : SupportedBasisMap N.faceSupport N.edgeSupport :=
  SupportedBasisMap.ofSingle N.nerve.faceEdge2
    (fun f _ ht => ((N.mem_faceSupport_iff f _).mp ht).2.2)

/-- 台を保つ全セルchainの端点差分。 -/
def rawD1 : SupportedBasisMap N.edgeSupport N.chartSupport :=
  (rightBasis N).add (leftBasis N).neg

/-- 台を保つ全セルchainの三辺符号和。 -/
def rawD2 : SupportedBasisMap N.faceSupport N.edgeSupport :=
  ((face0Basis N).add (face1Basis N).neg).add (face2Basis N)

/-- 原始d1のセル像。loopでも同じ式で相殺する。 -/
@[simp] theorem rawD1_basis (e : N.nerve.EdgeComponent) :
    (rawD1 N).basisImage e = Finsupp.single (N.nerve.edgeRight e) 1 -
      Finsupp.single (N.nerve.edgeLeft e) 1 := by
  simp [rawD1, rightBasis, leftBasis, SupportedBasisMap.add_basis,
    SupportedBasisMap.neg_basis, SupportedBasisMap.ofSingle_basis, sub_eq_add_neg]

/-- 原始d2のセル像。重複出現の三つの符号位置を保持する。 -/
@[simp] theorem rawD2_basis (f : N.nerve.FaceComponent) :
    (rawD2 N).basisImage f = Finsupp.single (N.nerve.faceEdge0 f) 1 -
      Finsupp.single (N.nerve.faceEdge1 f) 1 + Finsupp.single (N.nerve.faceEdge2 f) 1 := by
  simp [rawD2, face0Basis, face1Basis, face2Basis, SupportedBasisMap.add_basis,
    SupportedBasisMap.neg_basis, SupportedBasisMap.ofSingle_basis, sub_eq_add_neg]

/-- 全セルの二微分も、原始triangle incidenceから零に合成する。 -/
theorem rawD1_comp_rawD2 : (rawD1 N).raw.comp (rawD2 N).raw = 0 := by
  apply Finsupp.lhom_ext
  intro f a
  simp only [LinearMap.comp_apply, LinearMap.zero_apply, SupportedBasisMap.raw_single,
    rawD1_basis, rawD2_basis, map_smul, map_sub, map_add, one_smul]
  rw [N.faceEdge0_left, N.faceEdge0_right, N.faceEdge1_right]
  abel_nf
  simp


/-- 全セル微分を任意Aへ制限したd1は既存の同じ支持chain微分。 -/
theorem selected_rawD1 (A : Set q.Target) : (rawD1 N).selected A = chainD1 N A := by
  apply Finsupp.lhom_ext
  intro e a
  rw [SupportedBasisMap.selected_single, rawD1_basis, chainD1_single]
  congr 1
  rw [Finsupp.subtypeDomain_sub]
  change _ = Finsupp.single (N.targetSubsetEdgeRight A e) 1 -
    Finsupp.single (N.targetSubsetEdgeLeft A e) 1
  exact congrArg₂ (· - ·)
    (subtypeDomain_single_selected N.chartSupport A (N.targetSubsetEdgeRight A e) 1)
    (subtypeDomain_single_selected N.chartSupport A (N.targetSubsetEdgeLeft A e) 1)

/-- 全セル微分を任意Aへ制限したd2は既存の同じ支持chain微分。 -/
theorem selected_rawD2 (A : Set q.Target) : (rawD2 N).selected A = chainD2 N A := by
  apply Finsupp.lhom_ext
  intro f a
  rw [SupportedBasisMap.selected_single, rawD2_basis, chainD2_single]
  congr 1
  rw [Finsupp.subtypeDomain_add, Finsupp.subtypeDomain_sub]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· - ·)
      (subtypeDomain_single_selected N.edgeSupport A (N.targetSubsetFaceEdge0 A f) 1)
      (subtypeDomain_single_selected N.edgeSupport A (N.targetSubsetFaceEdge1 A f) 1))
    (subtypeDomain_single_selected N.edgeSupport A (N.targetSubsetFaceEdge2 A f) 1)

end TargetSupportedNerve
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
