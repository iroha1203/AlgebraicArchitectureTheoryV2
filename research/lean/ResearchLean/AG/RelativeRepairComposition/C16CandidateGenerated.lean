import ResearchLean.AG.RelativeRepairComposition.C16CandidateContextRegression
import ResearchLean.AG.RelativeRepairComposition.AffineContextConclusion

/-! # The same full generated public C in the internal-candidate contextual regression -/
namespace AAT.AG.RelativeRepairComposition.C16CandidateGenerated
open TransportCoherence AbelianLiftingObstruction NativeAffine
open C16CandidateGeometry C16CandidateRepairs C16CandidateContextRegression

/-- Both original endpoints and all parallel original loop names have concrete equality. -/
instance edgeEquality (double : Bool) : DecidableEq (EdgeName (K := (input double).geometry)) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Σ _ : Unit, Bool))
/-- The one original authored face has its concrete Unit equality. -/
instance faceEquality (double : Bool) : DecidableEq (input double).geometry.TwoCell :=
  inferInstanceAs (DecidableEq Unit)
/-- The original empty physical fixed edge set is decidable from the input. -/
instance fixedEdgesDecidable (double : Bool) : DecidablePred (· ∈ (input double).fixed.edges) :=
  fun _ => isFalse (fun h => h)
/-- The original empty physical fixed face set is decidable from the input. -/
instance fixedFacesDecidable (double : Bool) : DecidablePred (· ∈ (input double).fixed.faces) :=
  fun _ => isFalse (fun h => h)
/-- Shared original edge membership reads the concrete false loop name. -/
instance sharedDecidable (double : Bool) : DecidablePred (· ∈ (input double).shared.edges) :=
  fun e => (inferInstance : DecidableEq Bool) e.2.2 false
/-- Internal original candidate membership reads the concrete true loop name. -/
instance candidateDecidable (double : Bool) : DecidablePred (· ∈ (input double).candidates) :=
  fun e => (inferInstance : DecidableEq Bool) e.2.2 true

/-- All field values are listed before either candidate permission is queried. -/
def fieldValues : FiniteElimination.Enumeration (ZMod 3) := ⟨[0,1,2],by decide⟩
/-- The full original two-loop column list is fixed before permission or boundary values. -/
def edges (double : Bool) : FiniteElimination.Enumeration (EdgeName (K := (input double).geometry)) :=
  ⟨[⟨(),(),false⟩,⟨(),(),true⟩],by
    rintro ⟨i,j,e⟩
    cases i; cases j
    cases e <;> simp⟩
/-- The single full original authored face gives the complete finite row list. -/
def faces (double : Bool) : FiniteElimination.Enumeration (input double).geometry.TwoCell :=
  ⟨[()],by intro f; cases f; simp⟩

/-- The complete original generator imposes all candidate zero equations before internal projection. -/
def relation (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :=
  (input double).generatedShared fieldValues (edges double) (faces double) (permissions double permit S)

/-- Each concrete generated relation is its independently evaluated full actual boundary range. -/
theorem relation_actual (double permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    relation double permit S = Set.range ((input double).boundary (permissions double permit S)) :=
  (input double).generated_shared_actual fieldValues (edges double) (faces double) (permissions double permit S)

/-- The original distinct candidate words yield identical C relations for every permission and shared S. -/
theorem relations_equal (permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    relation false permit S = relation true permit S := by
  rw [relation_actual,relation_actual]
  exact boundary_ranges_equal permit S

/-- This concrete all-permission equality is the general generated-C criterion for all actual strict contexts. -/
theorem generated_contextual (permit : Bool) (S : Set (EdgeName (K := boundaryGeometry))) :
    (∀ env : AffineContextInput.Environments (W := boundaryGeometry) (LW := boundaryReference)
      (RW := boundaryReference) (cW := fun f => Empty.elim f) (PW := ClosedRegion.empty) (CW := ∅) S,
      Nonempty (AffineContextInput.StrictRepairs (input false) env.1 (permissions false permit S) env.2) ↔
        Nonempty (AffineContextInput.StrictRepairs (input true) env.1 (permissions true permit S) env.2)) ↔
      relation false permit S = relation true permit S :=
  (input false).contextual_generated_strict (input true) fieldValues (edges false) (faces false)
    (edges true) (faces true) (permissions false permit S) (permissions true permit S)

end AAT.AG.RelativeRepairComposition.C16CandidateGenerated
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16CandidateGenerated
