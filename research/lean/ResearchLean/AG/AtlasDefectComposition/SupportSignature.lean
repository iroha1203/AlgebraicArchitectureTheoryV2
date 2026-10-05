import ResearchLean.AG.AtlasDefectComposition.SignatureGeometry
import ResearchLean.AG.AtlasDefectComposition.SubsetComposition
import Formal.Util.AssertStandardAxioms
/-! # 実比較の両側三次数の名付きセル署名

Implementation notes: セルの側・次数・元の名前を直和型で保持する。
各targetの粗支持membershipと細支持のcomparisonFactor像から署名を作る。
原始incidenceとOption比較は固定したままで、診断値やセル数へ置き換えない。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportSignature
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q r : Reading Source}
variable (N : TargetSupportedNerve q) (E : TargetSupportedNerve r)
/-- EのΩ。六種類を側・次数・元の名付きセルで区別する有限型。 -/
abbrev Cell := ((N.nerve.Chart ⊕ N.nerve.EdgeComponent) ⊕ N.nerve.FaceComponent) ⊕
  ((E.nerve.Chart ⊕ E.nerve.EdgeComponent) ⊕ E.nerve.FaceComponent)
/-- ΩのcoarseChartタグ。元のセル名を保持する公開注入。 -/
def coarseChart (c : N.nerve.Chart) : Cell N E := Sum.inl (Sum.inl (Sum.inl c))
/-- ΩのcoarseEdgeタグ。元のセル名を保持する公開注入。 -/
def coarseEdge (c : N.nerve.EdgeComponent) : Cell N E := Sum.inl (Sum.inl (Sum.inr c))
/-- ΩのcoarseFaceタグ。元のセル名を保持する公開注入。 -/
def coarseFace (c : N.nerve.FaceComponent) : Cell N E := Sum.inl (Sum.inr c)
/-- ΩのfineChartタグ。元のセル名を保持する公開注入。 -/
def fineChart (c : E.nerve.Chart) : Cell N E := Sum.inr (Sum.inl (Sum.inl c))
/-- ΩのfineEdgeタグ。元のセル名を保持する公開注入。 -/
def fineEdge (c : E.nerve.EdgeComponent) : Cell N E := Sum.inr (Sum.inl (Sum.inr c))
/-- ΩのfineFaceタグ。元のセル名を保持する公開注入。 -/
def fineFace (c : E.nerve.FaceComponent) : Cell N E := Sum.inr (Sum.inr c)
variable (h : q.CoarserThan r)
/-- EのS_t。細側は固定reading因子の像でtargetを読む。原始比較の値は変更しない。 -/
def family (t : q.Target) : Set (Cell N E) := fun c => match c with
  | Sum.inl (Sum.inl (Sum.inl c)) => t ∈ N.chartSupport c
  | Sum.inl (Sum.inl (Sum.inr c)) => t ∈ N.edgeSupport c
  | Sum.inl (Sum.inr c) => t ∈ N.faceSupport c
  | Sum.inr (Sum.inl (Sum.inl c)) => ∃ a ∈ E.chartSupport c, comparisonFactor q r h a = t
  | Sum.inr (Sum.inl (Sum.inr c)) => ∃ a ∈ E.edgeSupport c, comparisonFactor q r h a = t
  | Sum.inr (Sum.inr c) => ∃ a ∈ E.faceSupport c, comparisonFactor q r h a = t
/-- S_tのcoarseChart成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_coarseChart (t : q.Target) (c : N.nerve.Chart) :
    coarseChart N E c ∈ family N E h t ↔ t ∈ N.chartSupport c := Iff.rfl
/-- S_tのcoarseEdge成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_coarseEdge (t : q.Target) (c : N.nerve.EdgeComponent) :
    coarseEdge N E c ∈ family N E h t ↔ t ∈ N.edgeSupport c := Iff.rfl
/-- S_tのcoarseFace成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_coarseFace (t : q.Target) (c : N.nerve.FaceComponent) :
    coarseFace N E c ∈ family N E h t ↔ t ∈ N.faceSupport c := Iff.rfl
/-- S_tのfineChart成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_fineChart (t : q.Target) (c : E.nerve.Chart) :
    fineChart N E c ∈ family N E h t ↔ ∃ a ∈ E.chartSupport c, comparisonFactor q r h a = t := Iff.rfl
/-- S_tのfineEdge成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_fineEdge (t : q.Target) (c : E.nerve.EdgeComponent) :
    fineEdge N E c ∈ family N E h t ↔ ∃ a ∈ E.edgeSupport c, comparisonFactor q r h a = t := Iff.rfl
/-- S_tのfineFace成分を実支持へ評価するAPI補題。 -/
@[simp] theorem mem_family_fineFace (t : q.Target) (c : E.nerve.FaceComponent) :
    fineFace N E c ∈ family N E h t ↔ ∃ a ∈ E.faceSupport c, comparisonFactor q r h a = t := Iff.rfl
/-- Eの実名付き六種類を保持するalpha。 -/
abbrev alpha (A : Set q.Target) := SignatureGeometry.alpha (family N E h) A
/-- 実署名の像半束。原始セル比較Mを固定した各適用で同じ支持幾何を読む。 -/
abbrev Signature := SignatureGeometry.Signature (family N E h)
/-- Eの実subsetから全名付きセル署名への標準商射。 -/
abbrev sigma (A : Set q.Target) := SignatureGeometry.sigma (family N E h) A
/-- 実alphaのcoarseChart成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_coarseChart (A : Set q.Target) (c : N.nerve.Chart) :
    coarseChart N E c ∈ alpha N E h A ↔ ∃ t, t ∈ N.chartSupport c ∧ t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_coarseChart]
  constructor
  · rintro ⟨t,ht,hs⟩
    exact ⟨t,hs,ht⟩
  · rintro ⟨t,hs,ht⟩
    exact ⟨t,ht,hs⟩
/-- 実alphaのcoarseEdge成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_coarseEdge (A : Set q.Target) (c : N.nerve.EdgeComponent) :
    coarseEdge N E c ∈ alpha N E h A ↔ ∃ t, t ∈ N.edgeSupport c ∧ t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_coarseEdge]
  constructor
  · rintro ⟨t,ht,hs⟩
    exact ⟨t,hs,ht⟩
  · rintro ⟨t,hs,ht⟩
    exact ⟨t,ht,hs⟩
/-- 実alphaのcoarseFace成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_coarseFace (A : Set q.Target) (c : N.nerve.FaceComponent) :
    coarseFace N E c ∈ alpha N E h A ↔ ∃ t, t ∈ N.faceSupport c ∧ t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_coarseFace]
  constructor
  · rintro ⟨t,ht,hs⟩
    exact ⟨t,hs,ht⟩
  · rintro ⟨t,hs,ht⟩
    exact ⟨t,ht,hs⟩
/-- 実alphaのfineChart成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_fineChart (A : Set q.Target) (c : E.nerve.Chart) :
    fineChart N E c ∈ alpha N E h A ↔ ∃ t, t ∈ E.chartSupport c ∧ comparisonFactor q r h t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_fineChart]
  constructor
  · rintro ⟨t,ht,a,ha,heq⟩
    exact ⟨a,ha,heq.symm ▸ ht⟩
  · rintro ⟨a,ha,ht⟩
    exact ⟨comparisonFactor q r h a,ht,a,ha,rfl⟩
/-- 実alphaのfineEdge成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_fineEdge (A : Set q.Target) (c : E.nerve.EdgeComponent) :
    fineEdge N E c ∈ alpha N E h A ↔ ∃ t, t ∈ E.edgeSupport c ∧ comparisonFactor q r h t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_fineEdge]
  constructor
  · rintro ⟨t,ht,a,ha,heq⟩
    exact ⟨a,ha,heq.symm ▸ ht⟩
  · rintro ⟨a,ha,ht⟩
    exact ⟨comparisonFactor q r h a,ht,a,ha,rfl⟩
/-- 実alphaのfineFace成分は指定subsetと実支持の交差を正確に復元する。 -/
theorem mem_alpha_fineFace (A : Set q.Target) (c : E.nerve.FaceComponent) :
    fineFace N E c ∈ alpha N E h A ↔ ∃ t, t ∈ E.faceSupport c ∧ comparisonFactor q r h t ∈ A := by
  simp only [SignatureGeometry.mem_alpha,mem_family_fineFace]
  constructor
  · rintro ⟨t,ht,a,ha,heq⟩
    exact ⟨a,ha,heq.symm ▸ ht⟩
  · rintro ⟨a,ha,ht⟩
    exact ⟨comparisonFactor q r h a,ht,a,ha,rfl⟩
/-- Eの同署名は両側全三次数の選択を必要十分に同定する。粗側だけには縮めない。 -/
theorem alpha_eq_iff (A B : Set q.Target) : alpha N E h A = alpha N E h B ↔
    (∀ c : N.nerve.Chart, (∃ t, t ∈ N.chartSupport c ∧ t ∈ A) ↔ (∃ t, t ∈ N.chartSupport c ∧ t ∈ B)) ∧
    (∀ c : N.nerve.EdgeComponent, (∃ t, t ∈ N.edgeSupport c ∧ t ∈ A) ↔ (∃ t, t ∈ N.edgeSupport c ∧ t ∈ B)) ∧
    (∀ c : N.nerve.FaceComponent, (∃ t, t ∈ N.faceSupport c ∧ t ∈ A) ↔ (∃ t, t ∈ N.faceSupport c ∧ t ∈ B)) ∧
    (∀ c : E.nerve.Chart, (∃ t, t ∈ E.chartSupport c ∧ comparisonFactor q r h t ∈ A) ↔ (∃ t, t ∈ E.chartSupport c ∧ comparisonFactor q r h t ∈ B)) ∧
    (∀ c : E.nerve.EdgeComponent, (∃ t, t ∈ E.edgeSupport c ∧ comparisonFactor q r h t ∈ A) ↔ (∃ t, t ∈ E.edgeSupport c ∧ comparisonFactor q r h t ∈ B)) ∧
    (∀ c : E.nerve.FaceComponent, (∃ t, t ∈ E.faceSupport c ∧ comparisonFactor q r h t ∈ A) ↔ (∃ t, t ∈ E.faceSupport c ∧ comparisonFactor q r h t ∈ B)) := by
  constructor
  · intro hAB
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro c
      rw [← mem_alpha_coarseChart N E h,← mem_alpha_coarseChart N E h,hAB]
    · intro c
      rw [← mem_alpha_coarseEdge N E h,← mem_alpha_coarseEdge N E h,hAB]
    · intro c
      rw [← mem_alpha_coarseFace N E h,← mem_alpha_coarseFace N E h,hAB]
    · intro c
      rw [← mem_alpha_fineChart N E h,← mem_alpha_fineChart N E h,hAB]
    · intro c
      rw [← mem_alpha_fineEdge N E h,← mem_alpha_fineEdge N E h,hAB]
    · intro c
      rw [← mem_alpha_fineFace N E h,← mem_alpha_fineFace N E h,hAB]
  · rintro ⟨hc,he,hf,kc,ke,kf⟩
    ext c
    rcases c with ((c | c) | c) | ((c | c) | c)
    · change coarseChart N E c ∈ alpha N E h A ↔ coarseChart N E c ∈ alpha N E h B
      rw [mem_alpha_coarseChart,mem_alpha_coarseChart]
      exact hc c
    · change coarseEdge N E c ∈ alpha N E h A ↔ coarseEdge N E c ∈ alpha N E h B
      rw [mem_alpha_coarseEdge,mem_alpha_coarseEdge]
      exact he c
    · change coarseFace N E c ∈ alpha N E h A ↔ coarseFace N E c ∈ alpha N E h B
      rw [mem_alpha_coarseFace,mem_alpha_coarseFace]
      exact hf c
    · change fineChart N E c ∈ alpha N E h A ↔ fineChart N E c ∈ alpha N E h B
      rw [mem_alpha_fineChart,mem_alpha_fineChart]
      exact kc c
    · change fineEdge N E c ∈ alpha N E h A ↔ fineEdge N E c ∈ alpha N E h B
      rw [mem_alpha_fineEdge,mem_alpha_fineEdge]
      exact ke c
    · change fineFace N E c ∈ alpha N E h A ↔ fineFace N E c ∈ alpha N E h B
      rw [mem_alpha_fineFace,mem_alpha_fineFace]
      exact kf c
/-- 実署名等号の公開判定は同じalphaの等号である。 -/
theorem sigma_eq_iff (A B : Set q.Target) : sigma N E h A = sigma N E h B ↔ alpha N E h A = alpha N E h B :=
  SignatureGeometry.sigma_eq_iff (family N E h) A B
end AAT.AG.AtlasDefectComposition.SupportSignature
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportSignature
