import ResearchLean.AG.SafeCoarseningOrder.GeneratedComparison
import ResearchLean.AG.FaceRelationSubdivision.HereditarySpecialization
import ResearchLean.AG.UniformInvariance.UniformityReduction
import ResearchLean.AG.AtlasCoefficientFiber.FinitePreservationDecision
import ResearchLean.AG.AtlasDefectComposition.SubsetComposition

/-!
# G-137 の全A・全Law安全性と同じ実診断

A の実H¹全単射性を、全adequate Law族、J零、G-135係数/fiber条件、入力生成有限判定へ接続する。
空Aは既存支持複体の零H¹から扱い、Law値型全体の有限性を追加しない。

## Implementation notes

SafeはG-134の同じ生成比較の全A実H¹写像を使う。
既存G-107への埋め込み一致を示し、粗adequacyから細adequacyを導出する。
期待rankや比較同型を入力せず、G-135の元行列に基づく診断へ戻す。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition AtlasCoefficientFiber Cohomology
variable {S T V : Type} [Fintype V]
/-- 空Aの同じ支持複体は実H¹も零。 -/
theorem empty_h1_subsingleton {S : Type} (q : Reading S) (N : TargetSupportedNerve q) :
    Subsingleton (N.targetSubsetComplex (∅ : Set q.Target)).H1 := by
  letI : IsEmpty (N.EdgeInTargetSubset (∅ : Set q.Target)) := ⟨by
    rintro ⟨e, t, ht, hA⟩
    exact hA⟩
  letI : Subsingleton (N.targetSubsetComplex (∅ : Set q.Target)).C1 :=
    inferInstanceAs (Subsingleton (N.EdgeInTargetSubset (∅ : Set q.Target) → ℚ))
  infer_instance
namespace PrimitiveInput
variable (M : PrimitiveInput S T V) (R : Coarsening T V)
/-- T0の全Aについての同じ実H¹比較の全単射性。 -/
def Safe : Prop := ∀ A : Set (Quotient R.1),
  Function.Bijective ((M.quotientComparison R).aSubnerveComparisonHom A).h1Map
/-- 同じ実比較の全単射性と全AのJ零は必要十分。 -/
theorem safe_iff_zeroDefect : M.Safe R ↔ ∀ A : Set (Quotient R.1),
  blockDefect ((M.quotientComparison R).aSubnerveComparisonHom A).h1Map = (0,0) := by
  exact forall_congr' fun A => (blockDefect_eq_zero_iff_bijective _).symm
/-- G-135の同じ係数射の全単射性と同じτの単射性に接続。 -/
theorem safe_iff_coefficient : M.Safe R ↔ ∀ A : Set (Quotient R.1),
    Function.Bijective (unitH1 (M.quotientComparison R) A) ∧
      Function.Injective (connectingTau (M.quotientComparison R) A) := by
  exact (M.safe_iff_zeroDefect R).trans (forall_congr' fun A => coefficient_zeroDefect_iff _ _)
/-- 空Aの原始比較は両実H¹が零なので全単射。 -/
theorem empty_comparison_bijective {S : Type} {qc qf : Reading S}
    {h : qc.CoarserThan qf} {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
    (m : TargetSupportedNerveMorphism qc qf h Nc Nf) :
    Function.Bijective (m.aSubnerveComparisonHom (∅ : Set qc.Target)).h1Map := by
  letI := empty_h1_subsingleton qc Nc
  have hempty : comparisonFactor qc qf h ⁻¹' (∅ : Set qc.Target) = ∅ := Set.preimage_empty
  letI : Subsingleton (Nf.targetSubsetComplex
      (comparisonFactor qc qf h ⁻¹' (∅ : Set qc.Target))).H1 := by
    rw [hempty]
    exact empty_h1_subsingleton qf Nf
  constructor
  · exact Function.injective_of_subsingleton _
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩
variable [Fintype S]
/-- 全adequate Law族と全Aの同じ実比較の保存は必要十分。 -/
theorem safe_iff_laws : M.Safe R ↔
    ∀ (laws : FiniteLawFamily S) (ha : laws.Adequate (M.quotientReading R)),
      Function.Bijective ((M.quotientMorphism R).generatedComparisonH1Map laws ha
        (adequate_of_coarser laws (M.quotient_coarser R) ha)) := by
  constructor
  · intro hs laws ha
    apply (TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective _).mpr
      (fun A _ => by
        have hA := hs A
        rw [M.quotient_actualHom_old (R := R) A] at hA
        exact hA) laws ha
  · intro hl A
    have hu : (M.quotientMorphism R).UniformInvariance := by
      intro laws hc hf
      exact hl laws hc
    have hn := (TargetSupportedNerveMorphism.uniformInvariance_iff_allNonemptyASubnerveH1Bijective _).mp hu
    rw [M.quotient_actualHom_old (R := R) A]
    by_cases hA : A.Nonempty
    · exact hn A hA
    · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
      rw [he]
      exact empty_comparison_bijective _
/-- 原始表からのG-135全A有理判定は安全性に必要十分。 -/
theorem safe_iff_decision : M.Safe R ↔ allAPreservationDecision (M.quotientComparison R) = true := by
  exact (M.safe_iff_zeroDefect R).trans (allAPreservationDecision_eq_true_iff (M.quotientComparison R)).symm
end PrimitiveInput
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
