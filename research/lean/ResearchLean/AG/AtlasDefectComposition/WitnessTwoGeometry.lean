import ResearchLean.AG.AtlasDefectComposition.WitnessTwoInput
import Formal.Util.AssertStandardAxioms
/-! # W2 の署名と閉包

Implementation notes: 全粗細セルの選択を二つの元の chart の選択へ評価する。
同じ二 chart を固定し、粗側だけの別署名へ置き換えない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.WitnessTwo
open CanonicalResolution ResolutionInvariance
/-- 粗 chart の実全セル署名所属を原始支持へ評価する。 -/
theorem coarse_chart_select (A : Set Source) (c : Bool) :
    SupportSignature.coarseChart N N c ∈ alpha A ↔ ∃ t, t ∈ support c ∧ t ∈ A :=
  SupportSignature.mem_alpha_coarseChart N N coarser A c
/-- 細 chart の実全セル署名所属も同じ原始支持である。 -/
theorem fine_chart_select (A : Set Source) (c : Bool) :
    SupportSignature.fineChart N N c ∈ alpha A ↔ ∃ t, t ∈ support c ∧ t ∈ A := by
  rw [SupportSignature.mem_alpha_fineChart]
  simp only [factor_self]
/-- false chart 選択は a または b の所属を読む。 -/
theorem coarse_false_mem (A : Set Source) : SupportSignature.coarseChart N N false ∈ alpha A ↔ 0 ∈ A ∨ 1 ∈ A := by
  rw [coarse_chart_select]
  simp [support]
/-- true chart 選択は c の所属を読む。 -/
theorem coarse_true_mem (A : Set Source) : SupportSignature.coarseChart N N true ∈ alpha A ↔ 2 ∈ A := by
  rw [coarse_chart_select]
  simp [support]
/-- W2 の同署名判定は元の二 chart の選択を両側で保持する。 -/
theorem alpha_eq_iff (A B : Set Source) : alpha A = alpha B ↔
    ((0 ∈ A ∨ 1 ∈ A) ↔ (0 ∈ B ∨ 1 ∈ B)) ∧ ((2 ∈ A) ↔ (2 ∈ B)) := by
  constructor
  · intro h
    constructor
    · rw [← coarse_false_mem,← coarse_false_mem,h]
    · rw [← coarse_true_mem,← coarse_true_mem,h]
  · rintro ⟨h₀,h₂⟩
    apply Set.ext
    intro c
    rcases c with ((c | e) | f) | ((c | e) | f)
    · cases c
      · exact (coarse_false_mem A).trans (h₀.trans (coarse_false_mem B).symm)
      · exact (coarse_true_mem A).trans (h₂.trans (coarse_true_mem B).symm)
    · exact e.elim
    · exact f.elim
    · change SupportSignature.fineChart N N c ∈ alpha A ↔ SupportSignature.fineChart N N c ∈ alpha B
      rw [fine_chart_select,fine_chart_select]
      cases c
      · simpa [support] using h₀
      · simpa [support] using h₂
    · exact e.elim
    · exact f.elim
/-- W2 の署名等号も全セル選択の同じ条件で判定する。 -/
theorem sigma_eq_iff (A B : Set Source) : sigma A = sigma B ↔
    ((0 ∈ A ∨ 1 ∈ A) ↔ (0 ∈ B ∨ 1 ∈ B)) ∧ ((2 ∈ A) ↔ (2 ∈ B)) := by
  rw [SupportSignature.sigma_eq_iff,alpha_eq_iff]
/-- a と b の単独台は同じ名付き全セル署名を持つ。 -/
theorem sigma_a_eq_b : sigma {0} = sigma {1} := by rw [sigma_eq_iff]; simp
/-- a と c の単独台は異なる名付き全セル署名を持つ。 -/
theorem sigma_a_ne_c : sigma {0} ≠ sigma {2} := by
  intro h
  have h₀ := (sigma_eq_iff _ _).mp h |>.1
  simp at h₀
/-- W2 の gamma は元の両側 chart 選択を保持する条件として読める。 -/
theorem mem_gamma_alpha (A : Set Source) (t : Source) :
    t ∈ SignatureGeometry.gamma family (alpha A) ↔ ∀ c : Bool,
      t ∈ support c → ∃ s, s ∈ support c ∧ s ∈ A := by
  constructor
  · intro h c ht
    exact (coarse_chart_select A c).mp
      (h ((SupportSignature.mem_family_coarseChart N N coarser t c).mpr ht))
  · intro h c ht
    rcases c with ((c | e) | f) | ((c | e) | f)
    · exact (coarse_chart_select A c).mpr (h c ht)
    · exact e.elim
    · exact f.elim
    · apply (fine_chart_select A c).mpr
      have ht' : t ∈ support c := by
        obtain ⟨a,ha,heq⟩ := ht
        rw [factor_self] at heq
        exact heq ▸ ha
      exact h c ht'
    · exact e.elim
    · exact f.elim
/-- W2 の a の閉包は元の同じ支持を持つ a,b の台になる。 -/
theorem closure_a : SignatureGeometry.closure family {0} = ({0,1} : Set Source) := by
  ext t
  change t ∈ SignatureGeometry.gamma family (alpha {0}) ↔ t ∈ ({0,1} : Set Source)
  rw [mem_gamma_alpha]
  fin_cases t <;> simp [support,Bool.forall_bool]
end AAT.AG.AtlasDefectComposition.WitnessTwo
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.WitnessTwo
