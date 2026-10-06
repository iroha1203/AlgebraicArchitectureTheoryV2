import ResearchLean.AG.FaceRelationSubdivision.SourceSupportedBasis
import ResearchLean.AG.FaceRelationSubdivision.LawFiniteFiber

/-!
# 異なるreadingの同じ原始有限和を実支持セルへ生成する

## Implementation notes

各非零係数の支持適合をSourceで検査し、元targetの同じ選択セル名を作る。
自由線形延長の零延長を原始射と照合する。cochain対象同型から射を定義する案は
独立生成を失うため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {qi qj : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))
variable (Ai : Set qi.Target) (Aj : Set qj.Target)
variable (hA : qi.read ⁻¹' Ai = qj.read ⁻¹' Aj)

/-- 同じ原始非零項の支持から実出力選択セルを生成する。 -/
def mixedSelectedCell (i : Selected si Ai) (j : J) (hne : M.basisImage i.1 j ≠ 0) : Selected sj Aj :=
  ⟨j, by
    obtain ⟨t, ht, hAi⟩ := i.2
    obtain ⟨x, rfl⟩ := qi.surjective t
    have hx : x ∈ qj.read ⁻¹' Aj := by
      rw [← hA]
      exact hAi
    exact ⟨qj.read x, M.support_compatible i.1 j hne ht, hx⟩⟩

/-- 実選択セルの基底名は同じ原始名。 -/
@[simp] theorem mixedSelectedCell_val (i) (j) (hne) :
    (M.mixedSelectedCell Ai Aj hA i j hne).1 = j := rfl

/-- 原始係数を同じ実選択基底へ直接運ぶ有限和。 -/
def mixedSelectedBasis (i : Selected si Ai) : Selected sj Aj →₀ ℚ :=
  ∑ j ∈ (M.basisImage i.1).support.attach,
    Finsupp.single (M.mixedSelectedCell Ai Aj hA i j.1 (Finsupp.mem_support_iff.mp j.2))
      (M.basisImage i.1 j.1)

/-- 同じ原始有限和の実選択chain射。 -/
def mixedSelected : (Selected si Ai →₀ ℚ) →ₗ[ℚ] (Selected sj Aj →₀ ℚ) :=
  freeMap (M.mixedSelectedBasis Ai Aj hA)

/-- 実選択chain射の独立基底評価。 -/
@[simp] theorem mixedSelected_single (i) (a : ℚ) :
    M.mixedSelected Ai Aj hA (Finsupp.single i a) = a • M.mixedSelectedBasis Ai Aj hA i :=
  freeMap_single _ _ _

/-- 実選択基底有限和の零延長は同じ全セル原始像。 -/
theorem mixedSelectedEmbed_basis (i : Selected si Ai) :
    selectedEmbed sj Aj (M.mixedSelectedBasis Ai Aj hA i) = M.basisImage i.1 := by
  classical
  rw [mixedSelectedBasis, map_sum]
  have hh : (∑ j ∈ (M.basisImage i.1).support.attach,
      Finsupp.single j.1 (M.basisImage i.1 j.1)) = M.basisImage i.1 :=
    (Finset.sum_attach _ (fun j : J => Finsupp.single j (M.basisImage i.1 j))).trans
      (Finsupp.sum_single (M.basisImage i.1))
  refine Eq.trans ?_ hh
  apply Finset.sum_congr rfl
  intro j hj
  rw [selectedEmbed_single, mixedSelectedCell_val]

/-- 全実選択chainで原始射と零延長は可換。 -/
theorem mixedSelectedEmbed_comm :
    (selectedEmbed sj Aj).comp (M.mixedSelected Ai Aj hA) = M.raw.comp (selectedEmbed si Ai) := by
  apply Finsupp.lhom_ext
  intro i a
  simp only [LinearMap.comp_apply, mixedSelected_single, map_smul, mixedSelectedEmbed_basis,
    selectedEmbed_single, raw_single]

/-- 零延長の実選択可換式を点ごとに公開する。 -/
theorem mixedSelectedEmbed_apply (x) :
    selectedEmbed sj Aj (M.mixedSelected Ai Aj hA x) = M.raw (selectedEmbed si Ai x) :=
  LinearMap.congr_fun (M.mixedSelectedEmbed_comm Ai Aj hA) x

/-- 独立実選択双対も同じ原始非零係数で有限和評価する。 -/
theorem mixedSelectedDual_apply (z) (i : Selected si Ai) :
    dualCellMap (M.mixedSelected Ai Aj hA) z i =
      ∑ j ∈ (M.basisImage i.1).support.attach,
        M.basisImage i.1 j.1 *
          z (M.mixedSelectedCell Ai Aj hA i j.1 (Finsupp.mem_support_iff.mp j.2)) := by
  rw [dualCellMap_apply, mixedSelected_single, one_smul, mixedSelectedBasis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

end SupportedBasisMap
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
