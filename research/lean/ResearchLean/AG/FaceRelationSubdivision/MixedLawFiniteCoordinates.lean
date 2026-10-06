import ResearchLean.AG.FaceRelationSubdivision.SourceLawCoordinates

/-!
# 異なるreadingの原始有限和からのLaw座標生成

## Implementation notes

各非零原始係数に対しSource支持包含から同じLaw/valueの出力座標を作る。
射の定義はこの独立有限和であり、Source座標との同定は項ごとに後から証明する。
対象同型の共役を射の定義にする案はDの生成順を失うため採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance
universe u
variable {Source I J : Type u} {qi qj : Reading Source}
variable {si : I → Set qi.Target} {sj : J → Set qj.Target}
namespace SupportedBasisMap
variable (M : SupportedBasisMap (sourceSupport qi si) (sourceSupport qj sj))
variable (laws : FiniteLawFamily Source) (hi : laws.Adequate qi) (hj : laws.Adequate qj)

/-- 原始像の非零項へ同じLaw/valueをSourceの発生証明から輸送。 -/
def mixedLawCoordinate (x : CellCoordinate laws qi hi I si) (j : J)
    (hne : M.basisImage x.cell j ≠ 0) : CellCoordinate laws qj hj J sj where
  cell := j
  law := x.law
  value := x.value
  generated := by
    obtain ⟨t, ht, hv⟩ := x.generated
    obtain ⟨a, rfl⟩ := qi.surjective t
    refine ⟨qj.read a, M.support_compatible x.cell j hne ht, ?_⟩
    exact (lawDescend_commutes laws qj hj x.law a).trans
      ((lawDescend_commutes laws qi hi x.law a).symm.trans hv)

/-- 輸送は同じ原始セル名。 -/
@[simp] theorem mixedLawCoordinate_cell (x) (j) (hne) :
    (M.mixedLawCoordinate laws hi hj x j hne).cell = j := rfl
/-- 輸送は同じLaw名。 -/
@[simp] theorem mixedLawCoordinate_law (x) (j) (hne) :
    (M.mixedLawCoordinate laws hi hj x j hne).law = x.law := rfl
/-- 輸送は同じLaw値。 -/
@[simp] theorem mixedLawCoordinate_value (x) (j) (hne) :
    (M.mixedLawCoordinate laws hi hj x j hne).value = x.value := rfl

/-- 原始輸送は全発生ラベルを保ち、同じ台の別Law名も保持する。 -/
theorem mixedLawCoordinate_label (x) (j) (hne) :
    (M.mixedLawCoordinate laws hi hj x j hne).lawValueLabel laws qj hj J sj =
      x.lawValueLabel laws qi hi I si := by
  apply LawValueLabel.ext <;> rfl

/-- 同じ非零原始係数を実Law座標の基底有限和へ運ぶ。 -/
def mixedLawBasis (x : CellCoordinate laws qi hi I si) : CellCoordinate laws qj hj J sj →₀ ℚ :=
  ∑ j ∈ (M.basisImage x.cell).support.attach,
    Finsupp.single (M.mixedLawCoordinate laws hi hj x j.1 (Finsupp.mem_support_iff.mp j.2))
      (M.basisImage x.cell j.1)

/-- 独立な実Law基底像の自由線形延長。 -/
def mixedLawRaw : (CellCoordinate laws qi hi I si →₀ ℚ) →ₗ[ℚ]
    (CellCoordinate laws qj hj J sj →₀ ℚ) := freeMap (M.mixedLawBasis laws hi hj)

/-- 同じ原始Law有限和の実cochain双対。 -/
def mixedLawDual : (CellCoordinate laws qj hj J sj → ℚ) →ₗ[ℚ]
    (CellCoordinate laws qi hi I si → ℚ) := dualCellMap (M.mixedLawRaw laws hi hj)

/-- 実Law自由射の原始基底評価。 -/
@[simp] theorem mixedLawRaw_single (x) (a : ℚ) :
    M.mixedLawRaw laws hi hj (Finsupp.single x a) = a • M.mixedLawBasis laws hi hj x :=
  freeMap_single _ _ _

/-- 実Law双対を同じ原始係数の有限和で直接評価。 -/
theorem mixedLawDual_apply (z) (x) :
    M.mixedLawDual laws hi hj z x =
      ∑ j ∈ (M.basisImage x.cell).support.attach,
        M.basisImage x.cell j.1 *
          z (M.mixedLawCoordinate laws hi hj x j.1 (Finsupp.mem_support_iff.mp j.2)) := by
  rw [mixedLawDual, dualCellMap_apply, mixedLawRaw_single, one_smul, mixedLawBasis, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact freeDualEquiv_single _ _ _

/-- 独立生成した輸送座標は同じSource座標輸送と一致する。 -/
theorem mixedLawCoordinate_source (x) (j) (hne) :
    M.mixedLawCoordinate laws hi hj (sourceCoordinateEquiv laws hi si x) j hne =
      sourceCoordinateEquiv laws hj sj (M.lawCoordinate laws (sourceAdequate laws) x j hne) := by
  apply CellCoordinate.ext <;> rfl

/-- 同じ原始有限和をSourceへ読んだ可換式。定義は共役でなく上の独立有限和。 -/
theorem mixedLawDual_source (z) :
    sourceCoordinateRead laws hi si (M.mixedLawDual laws hi hj z) =
      M.lawDual laws (sourceAdequate laws) (sourceCoordinateRead laws hj sj z) := by
  funext x
  rw [sourceCoordinateRead_apply, mixedLawDual_apply, lawDual_apply]
  simp only [sourceCoordinateEquiv_cell]
  apply Finset.sum_congr rfl
  intro j hj
  rw [sourceCoordinateRead_apply, mixedLawCoordinate_source]

/-- 原始基底像が零なら実Law射の同じ入力座標も零。 -/
theorem mixedLawDual_apply_zero (z) (x) (h : M.basisImage x.cell = 0) :
    M.mixedLawDual laws hi hj z x = 0 := by
  rw [mixedLawDual_apply]
  apply Finset.sum_eq_zero
  intro j hj
  simp only [h, Finsupp.zero_apply, zero_mul]

/-- 原始単一セル像のLaw双対は同じ生成座標の評価。 -/
theorem mixedLawDual_apply_single (z) (x) (j : J)
    (h : M.basisImage x.cell = Finsupp.single j 1) :
    M.mixedLawDual laws hi hj z x =
      z (M.mixedLawCoordinate laws hi hj x j (by rw [h]; simp)) := by
  classical
  rw [mixedLawDual_apply]
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
