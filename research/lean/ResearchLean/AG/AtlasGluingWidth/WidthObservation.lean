import ResearchLean.AG.AtlasGluingWidth.WidthHomology
import Formal.Util.AssertStandardAxioms

/-! # 全有限幅の実H¹観測と一様零欠損の分離

元のG-134部分集合比較の商を使う。低幅の表示同一視は零空間の明示同型と
その可換性で行い、原始セル名や期待欠損を観測の入力にしない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open ResolutionInvariance CanonicalResolution TwoPhase
variable (n : ℕ) [NeZero n]

/-- 元の粗領域の実H¹商。 -/
abbrev coarseH1 (X : Set (Concept n)) := ((coarse n).targetSubsetComplex X).H1
/-- 元の生成因子の逆像で選ぶ細実H¹商。 -/
abbrev fineH1 (cut : Bool) (X : Set (Concept n)) :=
  ((fine n cut).targetSubsetComplex
    (comparisonFactor (coarseReading n) (fineReading n) (coarser n) ⁻¹' X)).H1
/-- 同じ原始部分集合比較の実H¹射。 -/
abbrev actualMap (cut : Bool) (X : Set (Concept n)) :=
  ((comparison n cut).aSubnerveComparisonHom X).h1Map
omit [NeZero n] in
/-- 全粗領域は空辺を持つので実H¹が零。 -/
theorem coarse_H1_zero (X : Set (Concept n)) : Subsingleton (coarseH1 n X) := by
  apply AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective
  intro z
  exact ⟨0, by funext e; exact e.1.elim⟩
/-- 真部分集合で原始比較の同じ細商も零。 -/
theorem proper_actual_H1_zero (cut : Bool) (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    Subsingleton (fineH1 n cut X) := by
  unfold fineH1
  rw [factor]
  exact proper_H1_zero n cut X hX
/-- plusの全領域で原始比較の同じ細商は零。 -/
theorem plus_actual_H1_zero (X : Set (Concept n)) : Subsingleton (fineH1 n true X) := by
  unfold fineH1
  rw [factor]
  exact plus_H1_zero n X
/-- minus全領域の元の商を同じperiodでℚへ移す。 -/
def full_actual_H1_equiv : fineH1 n false Set.univ ≃ₗ[ℚ] ℚ := by
  unfold fineH1
  rw [factor]
  exact fullH1Equiv n
/-- 零domainからの実欠損はcodomainの次元だけを読む。 -/
theorem defect_zero_domain {V W : Type*}
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] [Subsingleton V]
    [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W] (f : V →ₗ[ℚ] W) :
    blockDefect f = (0, Module.finrank ℚ W) := by
  have hr : Module.finrank ℚ (LinearMap.range f) = 0 := by
    have hle := f.finrank_range_le
    have hv : Module.finrank ℚ V = 0 := Module.finrank_zero_of_subsingleton
    omega
  rw [blockDefect_eq_finrank_sub_range, hr, Module.finrank_zero_of_subsingleton]
  simp
/-- plusは全領域で実零欠損。 -/
theorem plus_defect (X : Set (Concept n)) : blockDefect (actualMap n true X) = (0, 0) := by
  letI := coarse_H1_zero n X
  letI := plus_actual_H1_zero n X
  rw [defect_zero_domain, Module.finrank_zero_of_subsingleton]
/-- minusの全真部分集合は実零欠損。 -/
theorem proper_defect (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    blockDefect (actualMap n false X) = (0, 0) := by
  letI := coarse_H1_zero n X
  letI := proper_actual_H1_zero n false X hX
  rw [defect_zero_domain, Module.finrank_zero_of_subsingleton]
/-- minus全領域の同じ実欠損は(0,1)。 -/
theorem full_defect : blockDefect (actualMap n false Set.univ) = (0, 1) := by
  letI := coarse_H1_zero n Set.univ
  rw [defect_zero_domain, (full_actual_H1_equiv n).finrank_eq]
  simp
/-- 同じ粗空間の恒等同型。 -/
def low_coarse_equiv (X : Set (Concept n)) : coarseH1 n X ≃ₗ[ℚ] coarseH1 n X :=
  LinearEquiv.refl ℚ _
/-- 真部分集合の細実H¹零空間を明示同型で同一視する。 -/
def low_fine_equiv (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    fineH1 n true X ≃ₗ[ℚ] fineH1 n false X := by
  letI := plus_actual_H1_zero n X
  letI := proper_actual_H1_zero n false X hX
  exact LinearEquiv.ofSubsingleton _ _
/-- 明示同型で同じ実H¹比較が可換。 -/
theorem low_square (X : Set (Concept n)) (hX : X ≠ Set.univ) (x : coarseH1 n X) :
    low_fine_equiv n X hX (actualMap n true X x) =
      actualMap n false X (low_coarse_equiv n X x) := by
  letI := proper_actual_H1_zero n false X hX
  exact Subsingleton.elim _ _
/-- 同じ全真部分集合のJも等しい。 -/
theorem low_defect (X : Set (Concept n)) (hX : X ≠ Set.univ) :
    blockDefect (actualMap n true X) = blockDefect (actualMap n false X) := by
  rw [plus_defect, proper_defect n X hX]

/-- 指定幅kに対する概念数。k=0だけn=2、それ以外n=k+1。 -/
def size (k : ℕ) : ℕ := max 2 (k + 1)
/-- 全幅の概念数は零でない。 -/
instance size_neZero (k : ℕ) : NeZero (size k) := ⟨by
  have h := Nat.le_max_left 2 (k + 1)
  unfold size
  omega⟩
/-- 全幅でn≥2。 -/
theorem size_two (k : ℕ) : 2 ≤ size k := Nat.le_max_left _ _
/-- 全幅でk<n。 -/
theorem size_gt (k : ℕ) : k < size k := by
  have h := Nat.le_max_right 2 (k + 1)
  unfold size
  omega
/-- 幅k以下の全領域は真部分集合。 -/
theorem low_proper (k : ℕ) (X : Set (Concept (size k)))
    (hX : X.ncard ≤ k) : X ≠ Set.univ := by
  intro he
  subst X
  have hc : (Set.univ : Set (Concept (size k))).ncard = size k := by
    simp [Concept]
  rw [hc] at hX
  have := size_gt k
  omega
/-- 全幅の全低幅領域の明示細H¹同型。 -/
def width_fine_equiv (k : ℕ) (X : Set (Concept (size k))) (hX : X.ncard ≤ k) :=
  low_fine_equiv (size k) X (low_proper k X hX)
/-- 全幅で低幅観測は比較可換性とJ等号を同時に持つ。 -/
theorem width_observation (k : ℕ) (X : Set (Concept (size k))) (hX : X.ncard ≤ k) :
    (∀ x, width_fine_equiv k X hX (actualMap (size k) true X x) =
      actualMap (size k) false X (low_coarse_equiv (size k) X x)) ∧
    blockDefect (actualMap (size k) true X) = blockDefect (actualMap (size k) false X) :=
  ⟨low_square (size k) X (low_proper k X hX), low_defect (size k) X (low_proper k X hX)⟩
/-- 同じ全幅指定対の一様零欠損の真偽は異なる。 -/
theorem width_uniform_separation (k : ℕ) :
    (∀ X, blockDefect (actualMap (size k) true X) = (0, 0)) ∧
    ¬ (∀ X, blockDefect (actualMap (size k) false X) = (0, 0)) := by
  refine ⟨plus_defect (size k), ?_⟩
  intro h
  have hx := h Set.univ
  rw [full_defect] at hx
  exact Nat.one_ne_zero (congrArg Prod.snd hx)

/-- 観測同値は全低幅の実H¹同型・比較可換性・J等号そのもの。 -/
def LowEquivalent (k : ℕ) (a b : Bool) : Prop :=
  ∀ (X : Set (Concept (size k))), X.ncard ≤ k →
    ∃ (ec : coarseH1 (size k) X ≃ₗ[ℚ] coarseH1 (size k) X)
      (ef : fineH1 (size k) a X ≃ₗ[ℚ] fineH1 (size k) b X),
      (∀ x, ef (actualMap (size k) a X x) = actualMap (size k) b X (ec x)) ∧
      blockDefect (actualMap (size k) a X) = blockDefect (actualMap (size k) b X)
/-- 指定対は固定観測定義で同値。 -/
theorem width_lowEquivalent (k : ℕ) : LowEquivalent k true false := by
  intro X hX
  exact ⟨low_coarse_equiv (size k) X, width_fine_equiv k X hX, width_observation k X hX⟩
/-- この二入力への制限で既に、同値観測を通る一様零欠損判定は不可能。 -/
theorem no_width_classifier (k : ℕ) (decides : Bool → Prop)
    (invariant : ∀ a b, LowEquivalent k a b → (decides a ↔ decides b))
    (correct : ∀ cut, decides cut ↔
      ∀ X, blockDefect (actualMap (size k) cut X) = (0, 0)) : False := by
  have he := invariant true false (width_lowEquivalent k)
  have hs := width_uniform_separation k
  exact hs.2 ((correct false).mp (he.mp ((correct true).mpr hs.1)))
/-- k=0の指定概念数は四角形を与える2。 -/
theorem size_zero : size 0 = 2 := rfl
/-- k=0で観測される全領域は空領域だけ。 -/
theorem width_zero_region (X : Set (Concept (size 0))) (hX : X.ncard ≤ 0) : X = ∅ :=
  (Set.ncard_eq_zero (Set.toFinite X)).mp (Nat.eq_zero_of_le_zero hX)

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
