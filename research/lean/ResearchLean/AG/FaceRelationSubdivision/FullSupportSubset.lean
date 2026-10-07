import ResearchLean.AG.FaceRelationSubdivision.IncidenceNamedComparison
import Formal.Util.AssertStandardAxioms
/-!
# 全台入力の全非空 subset を原始セル表へ同定する

## Implementation notes

A の一点から各セルの選択証明を生成する。選択証明は proof irrelevant である。
実比較を named 射から定義せず、原始 subset 生成後に全三成分正方形を証明する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
/-- 非空 A と全台から得る同じセル名の選択。 -/
def fullSelected {T I : Type u} (s : I → Set T) (hs : ∀ i, s i=Set.univ) (A : Set T) (hA : A.Nonempty) (i : I) :
    {i : I // ∃ t, t ∈ s i ∧ t ∈ A} := ⟨i,by obtain ⟨t,ht⟩ := hA; exact ⟨t,by rw [hs]; exact Set.mem_univ _,ht⟩⟩
/-- 非空全台選択はセル名を保つ。 -/
@[simp] theorem fullSelected_val {T I : Type u} (s : I → Set T) (hs : ∀ i, s i=Set.univ) (A : Set T) (hA : A.Nonempty) (i : I) :
    (fullSelected s hs A hA i).val=i := rfl
/-- 全台選択 cochain と原始名前 cochain の両逆。 -/
def fullSelectedCochain {T I : Type u} (s : I → Set T) (hs : ∀ i, s i=Set.univ) (A : Set T) (hA : A.Nonempty) :
    ({i : I // ∃ t, t ∈ s i ∧ t ∈ A} → ℚ) ≃ₗ[ℚ] (I → ℚ) where
  toFun z i := z (fullSelected s hs A hA i)
  invFun z i := z i.val
  left_inv z := by funext i; congr 1
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 全台選択 cochain 同定の公開評価。 -/
@[simp] theorem fullSelectedCochain_apply {T I : Type u} (s : I → Set T) (hs : ∀ i, s i=Set.univ) (A : Set T) (hA : A.Nonempty) (z) (i) :
    fullSelectedCochain s hs A hA z i=z (fullSelected s hs A hA i) := rfl
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
variable (hs : ∀ v, N.chartSupport v=Set.univ) (A : Set q.Target) (hA : A.Nonempty)
/-- 全非空 subset の実三項複体を原始名付き表へ移す全三成分同型。 -/
def fullSubsetNamedEquiv : ThreeCochainComplex.CochainEquiv (N.targetSubsetComplex A) (namedComplex N) where
  e0 := fullSelectedCochain N.chartSupport hs A hA
  e1 := fullSelectedCochain N.edgeSupport (fullSupport_edge N hs) A hA
  e2 := fullSelectedCochain N.faceSupport (fullSupport_face N hs) A hA
  comm0 := by
    intro z
    funext e
    rw [namedComplex_d0_apply]
    change (N.targetSubsetComplex A).d0 z (fullSelected N.edgeSupport (fullSupport_edge N hs) A hA e) =
      z (fullSelected N.chartSupport hs A hA (N.nerve.edgeRight e)) -
      z (fullSelected N.chartSupport hs A hA (N.nerve.edgeLeft e))
    rw [N.targetSubsetComplex_d0_apply]
    congr 1
  comm1 := by
    intro z
    funext f
    rw [namedComplex_d1_apply]
    change (N.targetSubsetComplex A).d1 z (fullSelected N.faceSupport (fullSupport_face N hs) A hA f) =
      z (fullSelected N.edgeSupport (fullSupport_edge N hs) A hA (N.nerve.faceEdge0 f)) -
      z (fullSelected N.edgeSupport (fullSupport_edge N hs) A hA (N.nerve.faceEdge1 f)) +
      z (fullSelected N.edgeSupport (fullSupport_edge N hs) A hA (N.nerve.faceEdge2 f))
    rw [N.targetSubsetComplex_d1_apply]
    congr 1
/-- 全台 subset 同型の次数0評価。 -/
@[simp] theorem fullSubsetNamedEquiv_e0 (z) (v) : (fullSubsetNamedEquiv N hs A hA).e0 z v=
    z (fullSelected N.chartSupport hs A hA v) := rfl
/-- 全台 subset 同型の次数1評価。 -/
@[simp] theorem fullSubsetNamedEquiv_e1 (z) (e) : (fullSubsetNamedEquiv N hs A hA).e1 z e=
    z (fullSelected N.edgeSupport (fullSupport_edge N hs) A hA e) := rfl
/-- 全台 subset 同型の次数2評価。 -/
@[simp] theorem fullSubsetNamedEquiv_e2 (z) (f) : (fullSubsetNamedEquiv N hs A hA).e2 z f=
    z (fullSelected N.faceSupport (fullSupport_face N hs) A hA f) := rfl
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
