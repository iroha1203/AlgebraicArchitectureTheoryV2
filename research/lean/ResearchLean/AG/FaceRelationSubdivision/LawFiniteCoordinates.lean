import ResearchLean.AG.FaceRelationSubdivision.ChainDualMap
import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms

/-!
# 原始有限和からのLaw座標生成

## Implementation notes

非零原始係数ごとに同じセル像・Law・値の座標をK1支持包含から生成する。
発生targetはproofであり座標名でない。fiber共役から射を定義する方法は、
独立生成というDの義務を消すため用いない。有限和を自由加群へ延長して双対化する。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {q : Reading Source}
variable {si : I → Set q.Target} {sj : J → Set q.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap si sj) (laws : FiniteLawFamily Source)
variable (ha : laws.Adequate q)

/-- 非零セル像へ同じLaw/valueを輸送する。保存結論は入力でない。 -/
def lawCoordinate (x : CellCoordinate laws q ha I si) (j : J)
    (hj : M.basisImage x.cell j ≠ 0) : CellCoordinate laws q ha J sj where
  cell := j
  law := x.law
  value := x.value
  generated := by
    obtain ⟨t, ht, hv⟩ := x.generated
    exact ⟨t, M.support_compatible x.cell j hj ht, hv⟩

/-- 輸送座標は原始像の同じセル名。 -/
@[simp] theorem lawCoordinate_cell (x) (j) (hj) :
    (M.lawCoordinate laws ha x j hj).cell = j := rfl
/-- 輸送座標は同じLaw名。 -/
@[simp] theorem lawCoordinate_law (x) (j) (hj) :
    (M.lawCoordinate laws ha x j hj).law = x.law := rfl
/-- 輸送座標は同じLaw値。 -/
@[simp] theorem lawCoordinate_value (x) (j) (hj) :
    (M.lawCoordinate laws ha x j hj).value = x.value := rfl
/-- 輸送は発生ラベルを保ち、同じ台の別Law名を潰さない。 -/
theorem lawCoordinate_label (x) (j) (hj) :
    (M.lawCoordinate laws ha x j hj).lawValueLabel laws q ha J sj =
      x.lawValueLabel laws q ha I si := by
  apply LawValueLabel.ext <;> rfl

/-- 原始セル像の有限supportを、そのままLaw座標の基底有限和へ移す。 -/
def lawBasis (x : CellCoordinate laws q ha I si) :
    CellCoordinate laws q ha J sj →₀ ℚ :=
  ∑ j ∈ (M.basisImage x.cell).support.attach,
    Finsupp.single (M.lawCoordinate laws ha x j.1 (Finsupp.mem_support_iff.mp j.2))
      (M.basisImage x.cell j.1)

/-- 入力座標上の基底有限和を自由線形延長する。 -/
def lawRaw : (CellCoordinate laws q ha I si →₀ ℚ) →ₗ[ℚ]
    (CellCoordinate laws q ha J sj →₀ ℚ) := freeMap (M.lawBasis laws ha)

/-- 同じ原始基底像の実cochain双対。 -/
def lawDual : (CellCoordinate laws q ha J sj → ℚ) →ₗ[ℚ]
    (CellCoordinate laws q ha I si → ℚ) := dualCellMap (M.lawRaw laws ha)

/-- 原始Law座標chain射の基底評価。 -/
@[simp] theorem lawRaw_single (x) (a : ℚ) :
    M.lawRaw laws ha (Finsupp.single x a) = a • M.lawBasis laws ha x :=
  freeMap_single _ _ _

/-- 実Law双対は原始非零係数と同じLaw座標を直接有限和で評価する。 -/
theorem lawDual_apply (z) (x) :
    M.lawDual laws ha z x =
      ∑ j ∈ (M.basisImage x.cell).support.attach,
        M.basisImage x.cell j.1 *
          z (M.lawCoordinate laws ha x j.1 (Finsupp.mem_support_iff.mp j.2)) := by
  rw [lawDual, dualCellMap_apply, lawRaw_single, one_smul, lawBasis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

/-- 原始基底像が零なら実Law射の同じ入力座標も零。 -/
theorem lawDual_apply_zero (z) (x) (h : M.basisImage x.cell = 0) :
    M.lawDual laws ha z x = 0 := by
  rw [lawDual_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [h, Finsupp.zero_apply, zero_mul]

/-- 原始単一セル像のLaw双対は同じ生成座標の評価。 -/
theorem lawDual_apply_single (z) (x) (j : J)
    (h : M.basisImage x.cell = Finsupp.single j 1) :
    M.lawDual laws ha z x =
      z (M.lawCoordinate laws ha x j (by rw [h]; simp)) := by
  classical
  rw [lawDual_apply]
  let j' : {j // j ∈ (M.basisImage x.cell).support} :=
    ⟨j, Finsupp.mem_support_iff.mpr (by rw [h]; simp)⟩
  rw [Finset.sum_eq_single j']
  · simp only [j', h, Finsupp.single_eq_same, one_mul]
  · intro k hk hkj
    have hne : k.1 ≠ j := by
      intro he
      exact hkj (Subtype.ext he)
    simp [h, hne]
  · intro hn
    exact False.elim (hn (Finset.mem_attach _ j'))

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
