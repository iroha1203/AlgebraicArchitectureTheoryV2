import ResearchLean.AG.AtlasGluingWidth.WidthInput
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Formal.Util.AssertStandardAxioms

/-! # 任意長の指定閉路のperiodと積分

全辺値を一周の和で測る。period零の原始関数は指定累積和で構成する。
有限個の長さの検算によらない。

## Implementation notes

ZMod.valの自然数代表による累積和を選び、一巡のwrapをperiod零で閉じる。
一般forestの根選択を導入する代替は、指定閉路に不要な選択dataと証明を増やすため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open scoped BigOperators
variable (n : ℕ) [NeZero n]

/-- 原始有向閉路の全辺値。 -/
abbrev Cochain := Concept n × Bool → ℚ
/-- 元chart値の右端−左端。 -/
def difference : (Chart n → ℚ) →ₗ[ℚ] Cochain n where
  toFun x e := x (right n e) - x (left n e)
  map_add' x y := by ext e; simp; ring
  map_smul' a x := by ext e; simp; ring
omit [NeZero n] in
/-- 公開微分評価API。 -/
@[simp] theorem difference_apply (x : Chart n → ℚ) (e : Concept n × Bool) :
    difference n x e = x (right n e) - x (left n e) := rfl
/-- 指定periodはaとbの一周和。 -/
def period : Cochain n →ₗ[ℚ] ℚ where
  toFun z := ∑ i : Concept n, (z (i, false) + z (i, true))
  map_add' x y := by simp only [Pi.add_apply]; simp [Finset.sum_add_distrib]; ring
  map_smul' a x := by simp [Finset.mul_sum, mul_add]
/-- 公開period評価API。 -/
theorem period_apply (z : Cochain n) :
    period n z = ∑ i : Concept n, (z (i, false) + z (i, true)) := rfl
/-- 添字の巡回置換により全境界のperiodは零。 -/
theorem period_difference (x : Chart n → ℚ) : period n (difference n x) = 0 := by
  have hs : (∑ i : Concept n, x (i + 1, false)) = ∑ i : Concept n, x (i, false) :=
    Equiv.sum_comp (Equiv.addRight (1 : Concept n)) (fun i => x (i, false))
  change (∑ i : Concept n,
    ((x (i, true) - x (i, false)) + (x (i + 1, false) - x (i, true)))) = 0
  simp_rw [show ∀ i : Concept n,
    (x (i, true) - x (i, false)) + (x (i + 1, false) - x (i, true)) =
      x (i + 1, false) - x (i, false) by intro i; ring]
  rw [Finset.sum_sub_distrib, hs, sub_self]
/-- 自然数代表を一度ずつ走る和は同じ概念の有限和。 -/
theorem sum_range_concept (f : Concept n → ℚ) :
    (∑ r ∈ Finset.range n, f (r : Concept n)) = ∑ i : Concept n, f i := by
  apply Finset.sum_bij (s := Finset.range n) (t := Finset.univ)
    (fun (r : ℕ) _ => (r : Concept n))
  · intros; exact Finset.mem_univ _
  · intro a ha b hb h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using hv
  · intro i _
    exact ⟨i.val, Finset.mem_range.mpr (ZMod.val_lt i), ZMod.natCast_zmod_val i⟩
  · intros; rfl
/-- 指定累積和。 -/
def cumulative (z : Cochain n) (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range r, (z ((j : Concept n), false) + z ((j : Concept n), true))
omit [NeZero n] in
/-- 一歩の累積和はそのa/b値を加える。 -/
theorem cumulative_succ (z : Cochain n) (r : ℕ) :
    cumulative n z (r + 1) = cumulative n z r + z ((r : Concept n), false) +
      z ((r : Concept n), true) := by
  rw [cumulative, Finset.sum_range_succ]
  change cumulative n z r + (z (_, false) + z (_, true)) = _
  ring
/-- 全累積和は同じperiod。 -/
theorem cumulative_full (z : Cochain n) : cumulative n z n = period n z :=
  sum_range_concept n (fun i => z (i, false) + z (i, true))
/-- period零のchart原始関数。 -/
def potential (z : Cochain n) (v : Chart n) : ℚ :=
  cumulative n z v.1.val + if v.2 then z (v.1, false) else 0
/-- 巡回 successor の代表値。 -/
theorem successor_val (i : Concept n) : (i + 1).val = (i.val + 1) % n := by
  conv_lhs => rw [← ZMod.natCast_zmod_val i, ← Nat.cast_one, ← Nat.cast_add]
  exact ZMod.val_natCast n _
/-- period零なら全辺値を同じ原始関数で積分できる。 -/
theorem difference_potential (z : Cochain n) (hz : period n z = 0) :
    difference n (potential n z) = z := by
  funext e
  rcases e with ⟨i, b⟩
  cases b
  · change (cumulative n z i.val + z (i, false)) - (cumulative n z i.val + 0) = z (i, false)
    ring
  · change (cumulative n z (i + 1).val + 0) -
      (cumulative n z i.val + z (i, false)) = z (i, true)
    have hi := ZMod.val_lt i
    have hp := cumulative_succ n z i.val
    rw [ZMod.natCast_zmod_val] at hp
    by_cases h : i.val + 1 < n
    · rw [successor_val, Nat.mod_eq_of_lt h, hp]
      ring
    · have he : i.val + 1 = n := by omega
      have hf : cumulative n z (i.val + 1) = 0 := by rw [he, cumulative_full, hz]
      rw [successor_val, he, Nat.mod_self]
      have hzero : cumulative n z 0 = 0 := by simp [cumulative]
      rw [hzero]
      linarith
/-- a₀だけに1を置く指定全閉路cochain。 -/
def generator : Cochain n := fun e => if e = (0, false) then 1 else 0
/-- 指定生成元のperiodは1。 -/
theorem period_generator : period n (generator n) = 1 := by
  classical
  simp [period, generator]
/-- 任意periodを指定生成元の倍で実現する。 -/
theorem period_surjective : Function.Surjective (period n) := by
  intro a
  refine ⟨a • generator n, ?_⟩
  rw [map_smul, period_generator]
  simp
/-- periodの核は実際の微分の像に等しい。 -/
theorem period_ker : LinearMap.ker (period n) = LinearMap.range (difference n) := by
  ext z
  constructor
  · intro hz
    exact ⟨potential n z, difference_potential n z hz⟩
  · rintro ⟨x, rfl⟩
    exact period_difference n x

/-- 指定閉路の零微分chart値は全chartで同じ定数。 -/
theorem difference_zero_constant (x : Chart n → ℚ) (hx : difference n x = 0)
    (v : Chart n) : x v = x (0, false) := by
  have ha (i : Concept n) : x (i, true) = x (i, false) := by
    have h := congrFun hx (i, false)
    change x (i, true) - x (i, false) = 0 at h
    exact sub_eq_zero.mp h
  have hb (i : Concept n) : x (i + 1, false) = x (i, true) := by
    have h := congrFun hx (i, true)
    change x (i + 1, false) - x (i, true) = 0 at h
    exact sub_eq_zero.mp h
  have hi (r : ℕ) : x ((r : Concept n), false) = x (0, false) := by
    induction r with
    | zero => simp
    | succ r ih =>
      rw [Nat.cast_add, Nat.cast_one, hb, ha, ih]
  have hv := hi v.1.val
  rw [ZMod.natCast_zmod_val] at hv
  rcases v with ⟨i, b⟩
  cases b
  · exact hv
  · exact (ha i).trans hv

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
