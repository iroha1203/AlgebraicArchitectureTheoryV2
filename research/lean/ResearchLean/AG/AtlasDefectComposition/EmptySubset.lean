import ResearchLean.AG.AtlasDefectComposition.ConeCoordinates
import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms
/-! # 空台の実部分集合複体と錐の零性

Implementation notes: 空集合が各元のセルを一つも選ばないことから、全cochain・零延長・homology・錐の零性を導く。非空台のselected true labelを空台へ仮定しない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase
universe u
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
/-- 空集合はchartを一つも選ばない。 -/
instance emptySubsetChartIsEmpty : IsEmpty (N.ChartInTargetSubset ∅) :=
  ⟨fun x => by obtain ⟨t,_,ht⟩ := x.property;exact ht⟩
/-- 空集合はedgeを一つも選ばない。 -/
instance emptySubsetEdgeIsEmpty : IsEmpty (N.EdgeInTargetSubset ∅) :=
  ⟨fun x => by obtain ⟨t,_,ht⟩ := x.property;exact ht⟩
/-- 空集合はfaceを一つも選ばない。 -/
instance emptySubsetFaceIsEmpty : IsEmpty (N.FaceInTargetSubset ∅) :=
  ⟨fun x => by obtain ⟨t,_,ht⟩ := x.property;exact ht⟩
/-- 空部分集合の次数0cochainは零加群である。 -/
instance emptySubsetC0Subsingleton : Subsingleton (N.targetSubsetComplex ∅).C0 := by
  change Subsingleton (N.ChartInTargetSubset ∅ → ℚ)
  infer_instance
/-- 空部分集合の次数1cochainは零加群である。 -/
instance emptySubsetC1Subsingleton : Subsingleton (N.targetSubsetComplex ∅).C1 := by
  change Subsingleton (N.EdgeInTargetSubset ∅ → ℚ)
  infer_instance
/-- 空部分集合の次数2cochainは零加群である。 -/
instance emptySubsetC2Subsingleton : Subsingleton (N.targetSubsetComplex ∅).C2 := by
  change Subsingleton (N.FaceInTargetSubset ∅ → ℚ)
  infer_instance
/-- 全三成分が零の実三項複体は、零延長の全次数も零である。 -/
theorem zeroExtension_isZero_X {C : ThreeCochainComplex.{0,u} ℚ}
    [Subsingleton C.C0] [Subsingleton C.C1] [Subsingleton C.C2] (m : ℤ) :
    IsZero ((zeroExtension C).X m) := by
  by_cases h₀ : m = 0
  · subst m;change IsZero (ModuleCat.of ℚ C.C0);exact ModuleCat.isZero_of_subsingleton _
  · by_cases h₁ : m = 1
    · subst m;change IsZero (ModuleCat.of ℚ C.C1);exact ModuleCat.isZero_of_subsingleton _
    · by_cases h₂ : m = 2
      · subst m;change IsZero (ModuleCat.of ℚ C.C2);exact ModuleCat.isZero_of_subsingleton _
      · exact degreeObject_isZero C m h₀ h₁ h₂
/-- 空部分集合の実零延長は全整数次数で零対象である。 -/
theorem emptySubset_isZero_X (m : ℤ) : IsZero ((zeroExtension (N.targetSubsetComplex ∅)).X m) :=
  zeroExtension_isZero_X m
/-- 空部分集合の実homologyも全整数次数で零対象である。 -/
theorem emptySubset_isZero_homology (m : ℤ) :
    IsZero ((zeroExtension (N.targetSubsetComplex ∅)).homology m) :=
  ((zeroExtension (N.targetSubsetComplex ∅)).sc m).isZero_homology_of_isZero_X₂
    (emptySubset_isZero_X N m)
/-- 空部分集合から空部分集合への実比較錐も全次数で零である。 -/
theorem emptySubsetCone_isZero_X {r : Reading Source} (E : TargetSupportedNerve r)
    (f : ThreeCochainComplex.Hom (N.targetSubsetComplex ∅) (E.targetSubsetComplex ∅)) (m : ℤ) :
    IsZero ((mappingCone (zeroExtensionMap f)).X m) :=
  (mappingCone.isZero_X_iff _ m).mpr
    ⟨emptySubset_isZero_X N (m+1),emptySubset_isZero_X E m⟩
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
