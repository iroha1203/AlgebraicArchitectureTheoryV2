import ResearchLean.AG.AtlasGluingWidth.WidthPhi

/-! # 指定閉路の同じ係数・fiber分解

GOAL E / witnesses §4。実順像複体の空辺・空面からH¹/H²零を導き、同じ五項列の
fiberRestrictionH1を全単射、τを零とする。Cの実hidden classと同じkerτ元を保持する。

## Implementation notes

既存の独立したG-135制限射と標準τを使い、実五項列の両方向完全性を適用する。
Rを全Φ H¹と無条件に同定する代替は不正であり、原混在面が空のforestから放電する。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition AtlasCoefficientFiber
variable (n : ℕ) [NeZero n]

/-- 元の粗辺が空なので実順像H¹は零。 -/
theorem pushforward_H1_zero (X : Set (Concept n)) :
    Subsingleton (pushforwardComplex (comparison n false) X).H1 := by
  apply h1_subsingleton_of_d0_surjective
  intro z
  exact ⟨0, by funext e; exact e.1.elim⟩
/-- 元の粗面が空なので実順像H²は零。 -/
theorem pushforward_H2_zero (X : Set (Concept n)) :
    Subsingleton ((pushforwardComplex (comparison n false) X).C2 ⧸
      LinearMap.range (pushforwardComplex (comparison n false) X).d1) := by
  letI : Subsingleton (pushforwardComplex (comparison n false) X).C2 := by
    constructor
    intro a b
    funext f
    exact f.1.elim
  infer_instance
set_option synthInstance.maxHeartbeats 100000 in
/-- 元の粗空辺から同じ標準順像H¹も零。 -/
theorem pushforward_standard_H1_zero (X : Set (Concept n)) :
    Subsingleton ((zeroExtension (pushforwardComplex (comparison n false) X)).homology (1:ℤ)) := by
  letI := pushforward_H1_zero n X
  exact (oldH1Equiv _).symm.injective.subsingleton
/-- 元の粗空面から同じ標準順像H²も零。 -/
theorem pushforward_standard_H2_zero (X : Set (Concept n)) :
    Subsingleton ((zeroExtension (pushforwardComplex (comparison n false) X)).homology (2:ℤ)) := by
  letI := pushforward_H2_zero n X
  exact (oldH2Equiv _).symm.injective.subsingleton
/-- 元混在面が空なのでΓは名前付きforest条件を満たす。 -/
theorem width_gamma_forest (X : Set (Concept n)) : GammaForest (comparison n false) X := by
  intro F hF
  obtain ⟨f,_⟩ := hF
  exact f.1.1.elim
/-- 原Γ forestから同じliteral Rは全Φ H¹上の全空間。 -/
theorem width_R_top (X : Set (Concept n)) : R (comparison n false) X = ⊤ :=
  fiberR_eq_top_of_forest _ _ (width_gamma_forest n X)
/-- 実順像H²零から同じ標準τは零射。 -/
theorem width_tau_zero (X : Set (Concept n)) : connectingTau (comparison n false) X = 0 := by
  letI := pushforward_standard_H2_zero n X
  exact Subsingleton.elim _ _
/-- 実順像H¹/H²零と実五項列から同じfiber制限は全単射。 -/
theorem width_fiber_restriction_bijective (X : Set (Concept n)) :
    Function.Bijective (fiberRestrictionH1 (comparison n false) X) := by
  letI := pushforward_standard_H1_zero n X
  constructor
  · intro x y hxy
    have hz : fiberRestrictionH1 (comparison n false) X (x-y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨a,ha⟩ := (fiveTerm_exact_at_fineH1 (comparison n false) X (x-y)).mp hz
    rw [Subsingleton.elim a 0, map_zero] at ha
    exact sub_eq_zero.mp ha.symm
  · intro z
    apply (fiveTerm_exact_at_fiber (comparison n false) X z).mp
    rw [width_tau_zero, LinearMap.zero_apply]
/-- 同じfiber制限を同じliteral kerτへ制限する。 -/
def widthFiberKernelMap (X : Set (Concept n)) :
    (zeroExtension (actualSelected n X).complex).homology (1:ℤ) →ₗ[ℚ]
      LinearMap.ker (connectingTau (comparison n false) X) :=
  (fiberRestrictionH1 (comparison n false) X).codRestrict _ (by
    intro z
    change connectingTau (comparison n false) X (fiberRestrictionH1 (comparison n false) X z) = 0
    rw [width_tau_zero, LinearMap.zero_apply])
/-- 同じfiber制限による実fine H¹とliteral kerτの両方向同型。 -/
def widthFiberKernelEquiv (X : Set (Concept n)) :
    (zeroExtension (actualSelected n X).complex).homology (1:ℤ) ≃ₗ[ℚ]
      LinearMap.ker (connectingTau (comparison n false) X) :=
  LinearEquiv.ofBijective (widthFiberKernelMap n X) ⟨fun _ _ h =>
    (width_fiber_restriction_bijective n X).1 (congrArg Subtype.val h), fun z => by
      obtain ⟨x,hx⟩ := (width_fiber_restriction_bijective n X).2 z.1
      exact ⟨x, Subtype.ext hx⟩⟩
/-- kerτ同型は同じ独立G-135制限の値を保つ。 -/
@[simp] theorem widthFiberKernelEquiv_val (X : Set (Concept n))
    (z : (zeroExtension (actualSelected n X).complex).homology (1:ℤ)) :
    (widthFiberKernelEquiv n X z).val = fiberRestrictionH1 (comparison n false) X z := rfl
/-- 同じ通常Uの実fine H¹をCの同じ全セル同定からperiodへ移す。 -/
def gluingFineH1Equiv : fineH1 n false (regionA n ∪ regionB n) ≃ₗ[ℚ] ℚ :=
  (PrimitiveGluing.fineUnionEquiv (h := coarser n) (Nf := fine n false) (regionA n) (regionB n)).trans
    ((primitiveUnionH1Equiv n).trans (unionPeriodEquiv n))
/-- 同じ通常Uのliteral kerτは同じfine H¹とperiodを通じℚと同型。 -/
def gluingKernelTauEquiv : LinearMap.ker (connectingTau (comparison n false) (regionA n ∪ regionB n)) ≃ₗ[ℚ] ℚ :=
  (widthFiberKernelEquiv n (regionA n ∪ regionB n)).symm.trans
    ((oldH1Equiv _).symm.trans (gluingFineH1Equiv n))
/-- Cの同じ実hidden classを既存係数SESがliteral kerτへ送った元。 -/
def gluingKernelTauClass (hn : 2 ≤ n) (z : Bool → ℚ) :
    LinearMap.ker (connectingTau (comparison n false) (regionA n ∪ regionB n)) :=
  (CoefficientBridge.oldCoefficientRow (comparison n false) (regionA n ∪ regionB n)).g
    (gluingHiddenClass n hn z)
/-- 既存係数SESの同じkerτ元は同じfine classの独立fiber制限である。 -/
theorem gluing_kernel_tau_same (hn : 2 ≤ n) (z : Bool → ℚ) :
    gluingKernelTauClass n hn z = widthFiberKernelEquiv n (regionA n ∪ regionB n)
      (oldH1Equiv _ (gluingOldClass n hn z)) := by
  apply Subtype.ext
  exact coefficient_hidden_same n hn z
/-- CとG-135から得た同じkerτ classのperiodは同じ順序付き値差。 -/
theorem gluing_kernel_tau_value (hn : 2 ≤ n) (z : Bool → ℚ) :
    gluingKernelTauEquiv n (gluingKernelTauClass n hn z) = endpointDifference z := by
  rw [gluing_kernel_tau_same]
  dsimp only [gluingKernelTauEquiv, LinearEquiv.trans_apply]
  erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  dsimp only [gluingFineH1Equiv, LinearEquiv.trans_apply]
  rw [gluingOldClass_fineUnionEquiv]
  exact primitive_delta_period n hn z
/-- 指定MV hidden生成元は同じkerτの非零生成元。 -/
theorem gluing_kernel_tau_generator (hn : 2 ≤ n) :
    gluingKernelTauEquiv n (gluingKernelTauClass n hn (fun b => if b then 1 else 0)) = 1 ∧
      gluingKernelTauClass n hn (fun b => if b then 1 else 0) ≠ 0 := by
  have hv : gluingKernelTauEquiv n (gluingKernelTauClass n hn (fun b => if b then 1 else 0)) = 1 := by
    rw [gluing_kernel_tau_value]
    simp [endpointDifference]
  refine ⟨hv, ?_⟩
  intro hz
  rw [hz, (gluingKernelTauEquiv n).map_zero] at hv
  exact zero_ne_one hv
/-- 同じ原始局所A/Bの係数保存条件が同じ実写像で成立する。 -/
theorem local_coefficient_preservation (hn : 2 ≤ n) :
    (Function.Bijective (unitH1 (comparison n false) (regionA n)) ∧
      Function.Injective (connectingTau (comparison n false) (regionA n))) ∧
    (Function.Bijective (unitH1 (comparison n false) (regionB n)) ∧
      Function.Injective (connectingTau (comparison n false) (regionB n))) :=
  ⟨(coefficient_zeroDefect_iff _ _).mp (local_defects_zero n hn).1,
    (coefficient_zeroDefect_iff _ _).mp (local_defects_zero n hn).2⟩

/-- 原Γ forestと唯一粗chartから同じ全U Rを実Φ periodへ移す。 -/
def fullFiberREquiv : R (comparison n false) Set.univ ≃ₗ[ℚ] ℚ := by
  letI : Unique ((coarse n).ChartInTargetSubset Set.univ) :=
    uniqueOfSubsingleton (coarseRoot n Set.univ ⟨0,Set.mem_univ _⟩)
  exact (forestFiberREquiv (comparison n false) Set.univ (width_gamma_forest n Set.univ)).trans
    ((LinearEquiv.piUnique ℚ (fun c => (phiComplex (comparison n false) Set.univ c).H1)).trans
      (fullPhiH1Equiv n default))
/-- 同じ局所A Rは原始pathの実Φ H¹零性から零。 -/
theorem local_A_R_zero (hn : 2 ≤ n) : Subsingleton (R (comparison n false) (regionA n)) := by
  letI : ∀ c : (coarse n).ChartInTargetSubset (regionA n),
      Subsingleton (phiComplex (comparison n false) (regionA n) c).H1 := fun c => a_phi_H1_zero n hn c
  exact (R (comparison n false) (regionA n)).injective_subtype.subsingleton
/-- 同じ局所B Rは原始pathの実Φ H¹零性から零。 -/
theorem local_B_R_zero : Subsingleton (R (comparison n false) (regionB n)) := by
  letI : ∀ c : (coarse n).ChartInTargetSubset (regionB n),
      Subsingleton (phiComplex (comparison n false) (regionB n) c).H1 := fun c => b_phi_H1_zero n c
  exact (R (comparison n false) (regionB n)).injective_subtype.subsingleton
/-- 指定全幅サイズは全てn≥2である。 -/
theorem size_ge_two (k : ℕ) : 2 ≤ size k := Nat.le_max_left _ _
/-- 任意kで同じ指定MV hiddenとG-135 kerτの生成元が同時に発火する。 -/
theorem all_width_gluing_fires (k : ℕ) :
    gluingHiddenClass (size k) (size_ge_two k) (fun b => if b then 1 else 0) ≠ 0 ∧
    gluingKernelTauEquiv (size k)
      (gluingKernelTauClass (size k) (size_ge_two k) (fun b => if b then 1 else 0)) = 1 ∧
    Nat.card (intersection (size k)).Chart = 2 ∧
    IsEmpty (selected (size k) false (regionA (size k) ∩ regionB (size k))).Chart :=
  ⟨gluing_hidden_nonzero (size k) (size_ge_two k),
    (gluing_kernel_tau_generator (size k) (size_ge_two k)).1,
    intersection_card (size k) (size_ge_two k), region_inter_charts_empty (size k)⟩

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
