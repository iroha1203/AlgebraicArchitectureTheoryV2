import ResearchLean.AG.SafeCoarseningOrder.FiniteClassification
import ResearchLean.AG.SafeCoarseningOrder.FailureCertificates

/-!
# 原始表からの最大元・join有限判定と失敗出力

全分割対と全部分集合の有限一覧を同じ有理比較判定に通し、正の最大元、
join閉性、または実cochain失敗証拠を出力する。最大元の負の証拠は全共通上界を排除する。
## Implementation notes

全部分領域を同じ原始有理kernelへ通す。失敗の核/余核分岐も計算したJの
核成分で決める。非計算的選択は検証された有限失敗一覧と同じ実線形商から
証拠付き出力を得るために用い、未評価の排中律だけを判定結果にしない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasCoefficientFiber
open FailureCertificate
variable {S T V : Type} [Fintype T] [Fintype V]
namespace PrimitiveInput
variable (M : PrimitiveInput S T V)
/-- 原始比較の有限有理kernelが失敗を返す全部分領域。 -/
def failureRegions (R : Coarsening T V) : Finset (Finset (Quotient R.1)) := by
  classical
  exact Finset.univ.filter (fun A =>
    primitivePreservationDecision (M.quotientComparison R) (A : Set (Quotient R.1)) ≠ true)
/-- 失敗領域一覧は同じ実H¹比較の非全単射性と必要十分。 -/
theorem mem_failureRegions (R : Coarsening T V) (A : Finset (Quotient R.1)) :
    A ∈ M.failureRegions R ↔
      ¬ Function.Bijective
        ((M.quotientComparison R).aSubnerveComparisonHom (A : Set (Quotient R.1))).h1Map := by
  classical
  simp only [failureRegions,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ((primitivePreservationDecision_eq_true_iff _ _).trans
    (blockDefect_eq_zero_iff_bijective _)).not
/-- 任意のSet領域は有限表に現れるので、不安全なら失敗一覧が非空。 -/
theorem failureRegions_nonempty (R : Coarsening T V) (hn : ¬ M.Safe R) :
    (M.failureRegions R).Nonempty := by
  classical
  have hn' := (M.safe_iff_zeroDefect R).not.mp hn
  push_neg at hn'
  obtain ⟨A,hA⟩ := hn'
  let s : Finset (Quotient R.1) := Finset.univ.filter (fun t => t ∈ A)
  have heq : (s : Set (Quotient R.1)) = A := by
    ext t; simp only [s,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and]
  refine ⟨s,(M.mem_failureRegions R s).mpr ?_⟩
  rw [heq]
  exact (blockDefect_eq_zero_iff_bijective _).not.mp hA
omit [Fintype T] in
/-- 入力生成Jの核成分が零であることは、同じ実H¹写像の単射性と必要十分。 -/
theorem primitive_kernel_zero_iff (R : Coarsening T V) (A : Set (Quotient R.1)) :
    (primitiveDiagnostic (M.quotientComparison R) A).1 = 0 ↔
      Function.Injective ((M.quotientComparison R).aSubnerveComparisonHom A).h1Map := by
  let f := ((M.quotientComparison R).aSubnerveComparisonHom A).h1Map
  have hd := congrArg Prod.fst ((primitiveDiagnostic_eq_blockDefect _ _).trans
    (blockDefect_eq_finrank_sub_range f))
  have hr := f.finrank_range_add_finrank_ker
  constructor
  · intro h
    have hk : Module.finrank ℚ (LinearMap.ker f) = 0 := by
      dsimp only [Prod.fst] at hd
      omega
    exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hk)
  · intro h
    have hk := LinearMap.ker_eq_bot.mpr h
    have hkdim : Module.finrank ℚ (LinearMap.ker f) = 0 := Submodule.finrank_eq_zero.mpr hk
    dsimp only [Prod.fst] at hd
    omega

/-- 同じ商比較について、実cochain核証拠または実余核証拠を保持する出力。 -/
def RegionFailure (R : Coarsening T V) (A : Finset (Quotient R.1)) : Type :=
  Sum (KernelFailure ((M.quotientComparison R).aSubnerveComparisonHom (A : Set (Quotient R.1))))
    (CokerFailure ((M.quotientComparison R).aSubnerveComparisonHom (A : Set (Quotient R.1))))
/-- 失敗一覧の各領域について、面なし条件を原始入力から放電し代表元を生成。 -/
theorem regionFailure_exists (R : Coarsening T V) (A : Finset (Quotient R.1))
    (hA : A ∈ M.failureRegions R) : Nonempty (M.RegionFailure R A) := by
  have hc : ∀ z, ((M.quotientSupported R).targetSubsetComplex (A : Set (Quotient R.1))).d1 z = 0 := by
    intro z
    funext f
    exact f.1.elim
  have hf : ∀ z, (M.supported.targetSubsetComplex
      (comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) ⁻¹' (A : Set (Quotient R.1)))).d1 z = 0 := by
    intro z
    funext f
    exact f.1.elim
  have hn := (M.mem_failureRegions R A).mp hA
  by_cases hk : (primitiveDiagnostic (M.quotientComparison R) (A : Set (Quotient R.1))).1 = 0
  · have hi := (M.primitive_kernel_zero_iff R (A : Set (Quotient R.1))).mp hk
    exact ⟨Sum.inr (Classical.choice (cokerFailure_exists _ hc hf (fun hs => hn ⟨hi,hs⟩)))⟩
  · have hni := (M.primitive_kernel_zero_iff R (A : Set (Quotient R.1))).not.mp hk
    exact ⟨Sum.inl (Classical.choice (kernelFailure_exists _ hc hni))⟩
/-- 不安全元に付随する、有限原始領域と実cochain失敗証拠。 -/
structure UnsafeWitness (R : Coarsening T V) where
  region : Finset (Quotient R.1)
  certificate : M.RegionFailure R region
/-- 不安全元から有限失敗一覧を経由して証拠付き出力を生成する。 -/
def unsafeWitness (R : Coarsening T V) (hn : ¬ M.Safe R) : M.UnsafeWitness R := by
  classical
  let h := M.failureRegions_nonempty R hn
  let A := Classical.choose h
  exact ⟨A,Classical.choice (M.regionFailure_exists R A (Classical.choose_spec h))⟩
/-- 生成した不安全出力の領域は原始有理失敗一覧に実際に所属する。 -/
theorem unsafeWitness_region_mem (R : Coarsening T V) (hn : ¬ M.Safe R) :
    (M.unsafeWitness R hn).region ∈ M.failureRegions R := by
  exact Classical.choose_spec (M.failureRegions_nonempty R hn)

omit [Fintype T] in
/-- 出力の核/余核証拠は実比較の不安全性を保証。 -/
theorem UnsafeWitness.not_safe {R : Coarsening T V} (w : M.UnsafeWitness R) : ¬ M.Safe R := by
  intro hs
  cases w.certificate with
  | inl h => exact KernelFailure.not_injective _ h (hs (w.region : Set (Quotient R.1))).1
  | inr h => exact CokerFailure.not_surjective _ h (hs (w.region : Set (Quotient R.1))).2
variable [Fintype S]
/-- 最大元の真偽は入力生成された全極大一覧のcardで決める。 -/
def greatestDecision : Bool := decide (M.maximalCoarsenings.card = 1)
/-- 最大元Boolの正しさと完全性。 -/
theorem greatestDecision_eq_true : M.greatestDecision = true ↔
    ∃ R, IsGreatest {W | M.Safe W} R := by
  simp only [greatestDecision,decide_eq_true_eq]
  exact M.greatest_iff_card_one.symm
/-- 最大元成立時の具体的な原始分割対と全安全元に対する最大性。 -/
structure GreatestWitness where
  coarsening : Coarsening T V
  greatest : IsGreatest {W | M.Safe W} coarsening
/-- 最大元Boolから正の証拠を構成。 -/
def greatestWitness (h : M.greatestDecision = true) : M.GreatestWitness := by
  classical
  let hex := M.greatestDecision_eq_true.mp h
  exact ⟨Classical.choose hex,Classical.choose_spec hex⟩
/-- 最大元負の出力は二安全元と全共通上界の実失敗出力を含む。 -/
structure NoGreatestWitness where
  left : Coarsening T V
  right : Coarsening T V
  left_safe : M.Safe left
  right_safe : M.Safe right
  exclude : ∀ W, left ≤ W → right ≤ W → ¬ M.Safe W
  failures : ∀ W, left ≤ W → right ≤ W → M.UnsafeWitness W
/-- 最大元Boolの負の結果から全共通上界排除と個別失敗証拠を生成。 -/
theorem noGreatestWitness_exists (h : M.greatestDecision ≠ true) : Nonempty M.NoGreatestWitness := by
  classical
  have hn : ¬ ∃ R, IsGreatest {W | M.Safe W} R := M.greatestDecision_eq_true.not.mp h
  obtain ⟨R,S,hR,hS,hno⟩ := M.no_greatest_witness ⟨⊥,M.safe_bot⟩ hn
  exact ⟨⟨R,S,hR,hS,hno,fun W hRW hSW => M.unsafeWitness W (hno W hRW hSW)⟩⟩
/-- 最大元の負の有限結果から、全上界証拠を持つ原始対を選ぶ。 -/
def noGreatestWitness (h : M.greatestDecision ≠ true) : M.NoGreatestWitness :=
  Classical.choice (M.noGreatestWitness_exists h)
/-- 全安全対の実join比較を同じ有限kernelへ通す。 -/
def joinDecision : Bool := by
  classical
  exact finiteFamilyDecision (fun p : Coarsening T V × Coarsening T V =>
    if p.1 ∈ M.safeCoarsenings ∧ p.2 ∈ M.safeCoarsenings then
      allAPreservationDecision (M.quotientComparison (p.1 ⊔ p.2)) else true)
/-- joinBoolは全安全対のjoin閉性と必要十分。 -/
theorem joinDecision_eq_true : M.joinDecision = true ↔
    ∀ R S, M.Safe R → M.Safe S → M.Safe (R ⊔ S) := by
  classical
  rw [joinDecision,finiteFamilyDecision_eq_true_iff]
  constructor
  · intro h R S hR hS
    have hp := h (R,S)
    rw [if_pos ⟨(M.mem_safeCoarsenings R).mpr hR,(M.mem_safeCoarsenings S).mpr hS⟩] at hp
    exact (M.safe_iff_decision _).mpr hp
  · intro h p
    by_cases hp : p.1 ∈ M.safeCoarsenings ∧ p.2 ∈ M.safeCoarsenings
    · rw [if_pos hp]
      exact (M.safe_iff_decision _).mp (h p.1 p.2
        ((M.mem_safeCoarsenings _).mp hp.1) ((M.mem_safeCoarsenings _).mp hp.2))
    · rw [if_neg hp]
/-- join負の出力は元の二安全分割と同じjoinの実失敗証拠。 -/
structure JoinFailure where
  left : Coarsening T V
  right : Coarsening T V
  left_safe : M.Safe left
  right_safe : M.Safe right
  failure : M.UnsafeWitness (left ⊔ right)
/-- joinの負の有限判定から二安全元と実核または余核の証拠を生成。 -/
theorem joinFailure_exists (h : M.joinDecision ≠ true) : Nonempty M.JoinFailure := by
  classical
  have hn := M.joinDecision_eq_true.not.mp h
  push_neg at hn
  obtain ⟨R,S,hR,hS,hno⟩ := hn
  exact ⟨⟨R,S,hR,hS,M.unsafeWitness (R ⊔ S) hno⟩⟩
/-- join負の有限結果から実cochain証拠付きの対を出力。 -/
def joinFailure (h : M.joinDecision ≠ true) : M.JoinFailure :=
  Classical.choice (M.joinFailure_exists h)
end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
