import ResearchLean.AG.RelativeRepairComposition.AffineFamilySymbolicCover
import ResearchLean.AG.RelativeRepairComposition.C15AffineFamilyRegression
import ResearchLean.AG.RelativeRepairComposition.C15SymbolicKernelRegression

/-!
# Actual nonzero affine values reach the same generated symbolic fibre

## Implementation notes

The same full original F3² shear input is passed to the general symbolic native
cover equivalence. Fixing both candidate loops is feasible exactly at the zero
parameter, while allowing the true loop is feasible at every parameter. The
fixed empty part retains all original vertex labels. No input assumes a repair
or a symbolic answer.
-/
namespace AAT.AG.RelativeRepairComposition.C15SymbolicAffineRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine
open C14AffineRegression C15AffineFamilyRegression
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

/-- All original named loops are candidates in this same full affine input. -/
def candidates : Set (EdgeName (K := K)) := Set.univ
/-- The allowed true loop is the original named candidate. -/
def allowed : Set (EdgeName (K := K)) := {e | e.2.2 = true}
/-- No original fixed face or fixed vertex is introduced. -/
abbrev P : ClosedRegion K := ClosedRegion.empty
/-- The single full original region supplies a closed cover at every degree. -/
abbrev U : Unit → ClosedRegion K := fun _ => ClosedRegion.all
/-- Every original loop name is explicitly listed before a value is chosen. -/
def edges : FiniteElimination.Enumeration (EdgeName (K := K)) :=
  ⟨[⟨(),(),false⟩,⟨(),(),true⟩],by
    intro e
    rcases e with ⟨i,j,e⟩
    cases i
    cases j
    cases e <;> simp⟩
/-- The sole original face and region have their entire finite input list. -/
def units : FiniteElimination.Enumeration Unit := ⟨[()],by intro a; cases a; simp⟩

/-- The original authored face names use the concrete Unit equality. -/
instance faceEquality : DecidableEq K.TwoCell := inferInstanceAs (DecidableEq Unit)

/-- The complete original candidate set gives a decision without a supplied repair. -/
instance candidateDecidable : DecidablePred (· ∈ candidates) := fun _ => isTrue trivial
/-- The original empty fixed part has no fixed edge, so its membership is decidable. -/
instance emptyEdgesDecidable : DecidablePred (· ∈ P.edges) := fun _ => isFalse (fun h => h)
/-- The original empty fixed part has no fixed face, so its membership is decidable. -/
instance emptyFacesDecidable : DecidablePred (· ∈ P.faces) := fun _ => isFalse (fun h => h)
/-- The full original region includes every original vertex at every region index. -/
instance regionVerticesDecidable : ∀ i, DecidablePred (· ∈ (U i).vertices) := fun _ _ => isTrue trivial
/-- The full original region includes every original named edge at every region index. -/
instance regionEdgesDecidable : ∀ i, DecidablePred (· ∈ (U i).edges) := fun _ _ => isTrue trivial
/-- The full original region includes every authored face at every region index. -/
instance regionFacesDecidable : ∀ i, DecidablePred (· ∈ (U i).faces) := fun _ _ => isTrue trivial

/-- The empty original fixed part makes the generated parameter term relative for every value. -/
theorem fixed_parameter (v : V) (f : K.TwoCell) (h : f ∈ P.faces) :
    familyDefectLinear K reference referenceTranslations (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) v f = 0 :=
  False.elim h
/-- The baseline physical fixed-face condition comes directly from the same empty fixed part. -/
theorem fixed_face (f : K.TwoCell) (h : f ∈ P.faces) :
    translation (k := ZMod 3) (baseComparison f) * GroupExtension.pathValue K reference (K.twoLeft f) =
      GroupExtension.pathValue K reference (K.twoRight f) := False.elim h

/-- Both actual range choices use exactly the same generated matrices, full kernels and section. -/
noncomputable def correspondence (S : Set (EdgeName (K := K))) (v : V) :=
  familyRealSymbolicEquivalence 2 K original reference baseComparison aligned
    originalTranslations referenceTranslations (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) P U
    fixed_parameter candidates fixed_face C15SymbolicKernelRegression.fieldValues edges units units
    ClosedRegion.indexed_cover_all S v

local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K original reference baseComparison aligned))
local notation "bases" => standardBases 2 K original reference baseComparison aligned
local notation "lin" => edge_linear K original reference baseComparison aligned
local notation "δ₀" => ActualEquation.defectFamily (tower K original reference baseComparison aligned) P
  (fixed_native K original reference baseComparison aligned P fixed_face)
local notation "Δ" => familyRelativeLinear K original reference baseComparison referenceTranslations
  (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) aligned P fixed_parameter
/-- The complete parameter fibre keeps the same full original candidate names and labels. -/
abbrev Fibre (S : Set (EdgeName (K := K))) (v : V) :=
  SymbolicCoverAction.Groupoid (M) bases P U candidates lin δ₀ Δ
    C15SymbolicKernelRegression.fieldValues edges units S v

/-- With no candidates allowed the actual fixed condition is all original loops. -/
theorem fixed_empty : fixedEdgesForRange P.edges candidates ∅ = Set.univ := by
  ext e
  simp [fixedEdgesForRange,P,ClosedRegion.empty,candidates]
/-- Allowing the original true loop fixes precisely the actual false reference loop. -/
theorem fixed_allowed : fixedEdgesForRange P.edges candidates allowed = C13RangeInput.fixed.edges := by
  ext e
  change (False ∨ True ∧ ¬ e.2.2 = true) ↔ e.2.2 = false
  cases e.2.2 <;> simp

/-- The complete generated symbolic fibre fails exactly at the actual nonzero fixed-input values. -/
theorem empty_range_iff (v : V) : Nonempty (Fibre ∅ v) ↔ v = 0 := by
  constructor
  · rintro ⟨z⟩
    have s : Repair K (refs v) (baseComparison + 0)
        (fixedEdgesForRange P.edges candidates ∅) :=
      ((correspondence ∅ v).inverse.obj z).2
    have s0 : Repair K (refs v) baseComparison Set.univ := by
      simpa only [add_zero, fixed_empty] using s
    exact (all_fixed_iff v).mp ⟨s0⟩
  · intro hv
    have hs := (all_fixed_iff v).mpr hv
    obtain ⟨s⟩ := hs
    have s' : Groupoid K (input v) (refs v) (familyComparisons K baseComparison
        (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) v)
        (family_aligned K reference referenceTranslations aligned v) P.vertices
        (fixedEdgesForRange P.edges candidates ∅) := by
      rw [fixed_empty]
      refine ⟨(),?_⟩
      change Repair K (refs v) (baseComparison + 0) Set.univ
      simpa only [add_zero] using s
    exact ⟨(correspondence ∅ v).functor.obj s'⟩

/-- The complete symbolic fibre is inhabited at every actual primitive value when the original true loop is allowed. -/
theorem allowed_range_success (v : V) : Nonempty (Fibre allowed v) := by
  have s : Groupoid K (input v) (refs v) (familyComparisons K baseComparison
      (0 : V →ₗ[ZMod 3] (K.TwoCell → V)) v)
      (family_aligned K reference referenceTranslations aligned v) P.vertices
      (fixedEdgesForRange P.edges candidates allowed) := by
    rw [fixed_allowed]
    refine ⟨(),?_⟩
    change Repair K (refs v) (baseComparison + 0) C13RangeInput.fixed.edges
    simpa only [add_zero] using allowedRepair v
  exact ⟨(correspondence allowed v).functor.obj s⟩

end AAT.AG.RelativeRepairComposition.C15SymbolicAffineRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C15SymbolicAffineRegression
