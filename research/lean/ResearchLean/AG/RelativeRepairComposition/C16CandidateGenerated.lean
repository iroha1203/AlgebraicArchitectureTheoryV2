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

attribute [local instance] Classical.propDecidable
local notation "K₀" => geometry false
local notation "L₀" => reference false
local notation "R₀" => reference false
local notation "c₀" => (fun _ => (0 : V))
local notation "hf₀" => aligned false
local notation "P₀" => ClosedRegion.empty (K := geometry false)
local notation "W₀" => shared false
local notation "C₀" => candidates false
local notation "M₀" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K₀ L₀ R₀ c₀ hf₀))
local notation "B₀" => standardBases 1 K₀ L₀ R₀ c₀ hf₀
local notation "private₀" => privateNonshared K₀ P₀ W₀ C₀
local notation "lin₀" => edge_linear K₀ L₀ R₀ c₀ hf₀
local notation "δ₀" => ActualEquation.defectFamily (tower K₀ L₀ R₀ c₀ hf₀) P₀
  (fixed_native K₀ L₀ R₀ c₀ hf₀ P₀ (fun _ h => False.elim h))

/-- The same full candidate coordinate system accepts its zero public vector when the internal candidate is forbidden. -/
theorem boundary_public_zero_zero :
    FiniteNative.BoundaryPublicZero M₀ B₀ ClosedRegion.all P₀ private₀ C₀ ∅ 0 :=
  FiniteNative.boundary_public_zero_zero M₀ B₀ ClosedRegion.all P₀ private₀ C₀ ∅

/-- The same generated public coordinate retains actual internal value one and rejects its prohibition. -/
theorem boundary_public_zero_rejects_internal_one (S : Set (EdgeName (K := boundaryGeometry))) :
    let s := repair false true S (fun _ => 1) (fun h => Bool.noConfusion h)
    let h := boundaryEquationEquiv 1 K₀ L₀ R₀ c₀ hf₀ P₀ C₀ (input false).fixed_faces
      (permissions false true S).allowed s
    let y := FiniteNative.generatedSolutionEquiv M₀ B₀ ClosedRegion.all P₀ private₀ lin₀ δ₀
      fieldValues (edges false) (faces false) h.1
    ¬ FiniteNative.BoundaryPublicZero M₀ B₀ ClosedRegion.all P₀ private₀ C₀ ∅ y.1.1 := by
  dsimp only
  let s := repair false true S (fun _ => 1) (fun h => Bool.noConfusion h)
  let h := boundaryEquationEquiv 1 K₀ L₀ R₀ c₀ hf₀ P₀ C₀ (input false).fixed_faces
    (permissions false true S).allowed s
  let E := FiniteNative.generatedSolutionEquiv M₀ B₀ ClosedRegion.all P₀ private₀ lin₀ δ₀
    fieldValues (edges false) (faces false)
  let y := E h.1
  intro hz
  let e : EdgeName (K := K₀) := ⟨(),(),true⟩
  have hp : e ∉ private₀ := fun h => h.2.2 rfl
  have hv := FiniteNative.restored_boundary_value M₀ B₀ ClosedRegion.all P₀ private₀ lin₀ δ₀
    fieldValues (edges false) (faces false) y ⟨e,trivial⟩ hp
  have hy : E.symm y = h.1 := E.symm_apply_apply h.1
  rw [hy] at hv
  have hz' := hz ⟨e,trivial⟩ (show e ∈ C₀ \ ∅ from ⟨rfl,fun h => h⟩)
  have heval := boundary_equation_value 1 K₀ L₀ R₀ c₀ hf₀ P₀ C₀ (input false).fixed_faces
    (permissions false true S).allowed s e
  change coefficient K₀ L₀ R₀ c₀ hf₀ e.2.1 (h.1.1.1 ⟨e,trivial⟩) = _ at heval
  rw [hv,hz',map_zero] at heval
  have hs := internal_one_retained false S
  change realCorrection K₀ R₀ c₀
    (fixedEdgesForRange (P₀).edges C₀ (permissions false true S).allowed) s e = (fun _ => 1) at hs
  rw [hs] at heval
  have h01 := congrArg (fun v : V => v 0) heval
  exact (by decide : (0 : ZMod 3) ≠ 1) h01

end AAT.AG.RelativeRepairComposition.C16CandidateGenerated
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C16CandidateGenerated
