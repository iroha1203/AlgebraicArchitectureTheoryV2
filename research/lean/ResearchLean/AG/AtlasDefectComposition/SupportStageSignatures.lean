import ResearchLean.AG.AtlasDefectComposition.SupportSignature
import ResearchLean.AG.AtlasDefectComposition.SubsetRestriction
import ResearchLean.AG.AtlasDefectComposition.SignatureUniversal
import Formal.Util.AssertStandardAxioms
/-! # 全段のセルを保持する共通台署名

Implementation notes: 任意の有限段の元のセルを段階・次数・名前で区別する。
すべての台は同じ基底 reading の subset から canonical 因子で引き戻す。
-/
noncomputable section
namespace AAT.AG.AtlasDefectComposition.SupportStages
open CanonicalResolution ResolutionInvariance TwoPhase
universe u v w
variable {Source : Type u} {base : Reading Source} {I : Type v}
variable (q : I → Reading Source) (N : ∀ i, TargetSupportedNerve.{u,w} (q i))
variable (h : ∀ i, base.CoarserThan (q i))
/-- 一段のセルを次数と元の名前で区別する型。 -/
abbrev StageCell (i : I) := (N i).nerve.Chart ⊕ (N i).nerve.EdgeComponent ⊕ (N i).nerve.FaceComponent
/-- 全段の全次数の元の名前を保持する共通セル型。 -/
abbrev Cell := Σ i, StageCell q N i
/-- 各段の元の支持を読む。辺・面は元の K1 支持である。 -/
def support (i : I) : StageCell q N i → Set (q i).Target
  | Sum.inl c => (N i).chartSupport c
  | Sum.inr (Sum.inl e) => (N i).edgeSupport e
  | Sum.inr (Sum.inr f) => (N i).faceSupport f
/-- 同じ基底 target から全段の元のセルを選ぶ族。 -/
def family (t : base.Target) : Set (Cell q N) := fun c =>
  ∃ a ∈ support q N c.1 c.2, comparisonFactor base (q c.1) (h c.1) a = t
/-- 全有限段の共通セル型の有限性。 -/
instance cellFinite [Finite I] : Finite (Cell q N) := by
  classical
  letI := Fintype.ofFinite I
  infer_instance
/-- 全段の名付きセル選択。 -/
abbrev alpha (A : Set base.Target) := SignatureGeometry.alpha (family q N h) A
/-- 全段のセルを保持する共通署名の像半束。 -/
abbrev Signature := SignatureGeometry.Signature (family q N h)
/-- 全段共通署名への標準商射。 -/
abbrev sigma (A : Set base.Target) := SignatureGeometry.sigma (family q N h) A
/-- 各段の全セル選択は同じ基底 subset の canonical 逆像を読む。 -/
theorem mem_alpha (A : Set base.Target) (i : I) (c : StageCell q N i) :
    (⟨i,c⟩ : Cell q N) ∈ alpha q N h A ↔ ∃ a, a ∈ support q N i c ∧ comparisonFactor base (q i) (h i) a ∈ A := by
  simp only [SignatureGeometry.mem_alpha]
  constructor
  · rintro ⟨t,ht,a,ha,heq⟩;exact ⟨a,ha,heq.symm ▸ ht⟩
  · rintro ⟨a,ha,ht⟩;exact ⟨_,ht,a,ha,rfl⟩
/-- 共通署名包含は各段の全実セル選択の包含を生成する。 -/
def stageLE {A B : Set base.Target} (hAB : alpha q N h A ⊆ alpha q N h B) (i : I) :
    SubsetRestriction.SelectedLE (N i) (comparisonFactor base (q i) (h i) ⁻¹' A)
      (comparisonFactor base (q i) (h i) ⁻¹' B) := by
  refine ⟨?_,?_,?_⟩
  · intro c hc
    exact (mem_alpha q N h B i (Sum.inl c)).mp (hAB ((mem_alpha q N h A i (Sum.inl c)).mpr hc))
  · intro e he
    exact (mem_alpha q N h B i (Sum.inr (Sum.inl e))).mp (hAB ((mem_alpha q N h A i (Sum.inr (Sum.inl e))).mpr he))
  · intro f hf
    exact (mem_alpha q N h B i (Sum.inr (Sum.inr f))).mp (hAB ((mem_alpha q N h A i (Sum.inr (Sum.inr f))).mpr hf))
/-- 共通 subset から各段へ引き戻した実部分集合複体。 -/
def stageComplex (A : Set base.Target) (i : I) := (N i).targetSubsetComplex (comparisonFactor base (q i) (h i) ⁻¹' A)
/-- 共通署名包含が全段の実 cochain 制限を生成する。 -/
def stageRestriction {A B : Set base.Target} (hAB : alpha q N h A ⊆ alpha q N h B) (i : I) :=
  SubsetRestriction.hom (N i) (stageLE q N h hAB i)
end AAT.AG.AtlasDefectComposition.SupportStages
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition.SupportStages
