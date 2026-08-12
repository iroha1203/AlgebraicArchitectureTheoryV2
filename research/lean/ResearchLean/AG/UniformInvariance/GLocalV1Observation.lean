import ResearchLean.AG.UniformInvariance.GLocalV1V5Reduction
import Mathlib.Data.List.Permutation
import Formal.Util.AssertStandardAxioms

/-!
# Executable permanent `G_local-v1` observation

This module completes the definition-level `Obs_G` kernel required by claim
(v) of `G-107-aat-uniform-invariance-characterization`.  It turns every v5
terminal into side-local, root-preserving radius-one incidence balls, clips
all registered multiplicities at two, computes the whole scope once and every
nonempty coarse-target scope once, and minimizes the structured value over all
simultaneous target relabels preserving the computed factor.

## Implementation notes

Target codes are the first indices in explicit presentation enumerations.  The
fine enumeration is generated from the explicit source list and surjective raw
fine reading, so no noncomputable `Fintype.equivFin` enters the executable
definition.  Relabels are finite functions on target codes satisfying
bijectivity and factor commutation; identity is generated internally.  The
structured `Ord` minimum is a canonical representative of this finite orbit.
An arbitrary supplied relabel and a byte-ordered JSON minimum were rejected:
the former is a certificate escape and the latter would make the Lean value
depend on an external serialization.  No claim of byte-for-byte equality with
the Python JSON encoding is made here; the next cycle proves the registered
T3/T6 component correspondence.
-/

namespace AAT.AG.ResolutionInvariance

universe u

namespace FiniteComparisonPresentation

/-! ## Executable target coding -/

/-- Any finite subset of a covered explicit list is represented by one of its
sublists.  This is the generic completeness bridge used by state and scope
enumeration; it does not select a terminal or observation. -/
theorem exists_sublists_toFinset_eq_of_complete {α : Type*} [DecidableEq α]
    (entries : List α) (complete : ∀ value, value ∈ entries)
    (subset : Finset α) :
    ∃ values ∈ entries.sublists, values.toFinset = subset := by
  let values := entries.filter fun value => decide (value ∈ subset)
  refine ⟨values, List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext value
  simp [values, complete value]

/-- Any finite set whose members occur in an explicit list is represented by
one of the list's sublists.  Unlike the ambient-type completeness bridge, this
version records the exact bounded-state invariant used by terminal
enumeration. -/
theorem exists_sublists_toFinset_eq_of_subset {α : Type*} [DecidableEq α]
    (entries : List α) (subset : Finset α)
    (covered : ∀ value ∈ subset, value ∈ entries) :
    ∃ values ∈ entries.sublists, values.toFinset = subset := by
  let values := entries.filter fun value => decide (value ∈ subset)
  refine ⟨values, List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext value
  constructor
  · intro hvalue
    have hmem : value ∈ values := by simpa using hvalue
    exact of_decide_eq_true (List.mem_filter.mp hmem).2
  · intro hvalue
    have hmem : value ∈ values :=
      List.mem_filter.mpr ⟨covered value hvalue, by simp [hvalue]⟩
    simpa using hmem

/-- Duplicate-free explicit coarse-target enumeration. -/
def coarseTargetEntriesDedup (P : FiniteComparisonPresentation) :
    List P.CoarseTarget :=
  P.coarseTargetEntries.dedup

/-- Duplicate-free explicit fine-target enumeration generated from source
entries and the surjective raw fine reading. -/
def fineTargetEntries (P : FiniteComparisonPresentation) : List P.FineTarget :=
  (P.sourceEntries.map P.fineRead).dedup

/-- Every coarse target occurs in the duplicate-free explicit enumeration. -/
theorem coarseTargetEntriesDedup_complete (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) : target ∈ P.coarseTargetEntriesDedup := by
  simp [coarseTargetEntriesDedup, P.coarseTarget_mem_coarseTargetEntries target]

/-- Every fine target occurs in the source-generated explicit enumeration. -/
theorem fineTargetEntries_complete (P : FiniteComparisonPresentation)
    (target : P.FineTarget) : target ∈ P.fineTargetEntries := by
  obtain ⟨source, hsource⟩ := P.fineRead_surjective target
  subst target
  simp only [fineTargetEntries, List.mem_dedup, List.mem_map]
  exact ⟨source, P.source_mem_sourceEntries source, rfl⟩

/-- Executable coarse-target code. -/
def coarseTargetCode (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) : Nat :=
  P.coarseTargetEntriesDedup.idxOf target

/-- Executable fine-target code. -/
def fineTargetCode (P : FiniteComparisonPresentation)
    (target : P.FineTarget) : Nat :=
  P.fineTargetEntries.idxOf target

/-- Coarse-target coding is injective because the deduplicated enumeration is
complete. -/
theorem coarseTargetCode_injective (P : FiniteComparisonPresentation) :
    Function.Injective P.coarseTargetCode := by
  intro left right hequal
  exact (List.idxOf_inj (P.coarseTargetEntriesDedup_complete left)).mp hequal

/-- Fine-target coding is injective because the source-generated deduplicated
enumeration is complete. -/
theorem fineTargetCode_injective (P : FiniteComparisonPresentation) :
    Function.Injective P.fineTargetCode := by
  intro left right hequal
  exact (List.idxOf_inj (P.fineTargetEntries_complete left)).mp hequal

/-- Every coarse target code lies inside the generated code range. -/
theorem coarseTargetCode_lt_length (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) :
    P.coarseTargetCode target < P.coarseTargetEntriesDedup.length :=
  List.idxOf_lt_length_iff.mpr (P.coarseTargetEntriesDedup_complete target)

/-- Every fine target code lies inside the generated code range. -/
theorem fineTargetCode_lt_length (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    P.fineTargetCode target < P.fineTargetEntries.length :=
  List.idxOf_lt_length_iff.mpr (P.fineTargetEntries_complete target)

/-- The numerical identity table evaluates to the original coarse code. -/
@[simp]
theorem range_getD_coarseTargetCode (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) :
    (List.range P.coarseTargetEntriesDedup.length).getD
      (P.coarseTargetCode target) (P.coarseTargetCode target) =
        P.coarseTargetCode target := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_range (by simpa using P.coarseTargetCode_lt_length target)]
  rfl

/-- The numerical identity table evaluates to the original fine code. -/
@[simp]
theorem range_getD_fineTargetCode (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    (List.range P.fineTargetEntries.length).getD
      (P.fineTargetCode target) (P.fineTargetCode target) =
        P.fineTargetCode target := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_range (by simpa using P.fineTargetCode_lt_length target)]
  rfl

/-- Decoding an explicit fine target at its generated code returns that target. -/
@[simp]
theorem fineTargetEntries_getD_fineTargetCode
    (P : FiniteComparisonPresentation) (target : P.FineTarget) :
    P.fineTargetEntries.getD (P.fineTargetCode target) target = target := by
  simp only [fineTargetCode]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_idxOf (P.fineTargetEntries_complete target)]
  rfl

/-! ## Finite simultaneous target relabels -/

/-- A simultaneous target relabel represented by two finite code tables.
Validity is checked by `gLocalV1TargetRelabelValid`; the structure stores no
observation, expected equality, or certificate field. -/
structure GLocalV1TargetRelabel (P : FiniteComparisonPresentation) where
  coarse : List Nat
  fine : List Nat
  deriving DecidableEq, Repr, Ord

/-- Relabel one coarse target code, falling back only outside the generated
permutation domain. -/
def gLocalV1CoarseRelabelCode (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.CoarseTarget) : Nat :=
  relabel.coarse.getD (P.coarseTargetCode target) (P.coarseTargetCode target)

/-- Relabel one fine target code, falling back only outside the generated
permutation domain. -/
def gLocalV1FineRelabelCode (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.FineTarget) : Nat :=
  relabel.fine.getD (P.fineTargetCode target) (P.fineTargetCode target)

/-- Decode the relabeled fine target.  Generated permutations keep the lookup
inside `fineTargetEntries`; the fallback makes the raw candidate total. -/
def gLocalV1FineRelabelTarget (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.FineTarget) : P.FineTarget :=
  P.fineTargetEntries.getD (P.gLocalV1FineRelabelCode relabel target) target

/-- Executable validity of a simultaneous relabel: both tables are complete
permutations and the computed factor commutes on every explicit fine target. -/
def gLocalV1TargetRelabelValid (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) : Bool :=
  decide (relabel.coarse.Perm
      (List.range P.coarseTargetEntriesDedup.length)) &&
    decide (relabel.fine.Perm (List.range P.fineTargetEntries.length)) &&
    P.fineTargetEntries.all fun target =>
      P.gLocalV1CoarseRelabelCode relabel (P.computedFactor target) =
        P.coarseTargetCode
          (P.computedFactor (P.gLocalV1FineRelabelTarget relabel target))

/-- Identity target coding, generated internally. -/
def gLocalV1IdentityRelabel (P : FiniteComparisonPresentation) :
    P.GLocalV1TargetRelabel where
  coarse := List.range P.coarseTargetEntriesDedup.length
  fine := List.range P.fineTargetEntries.length

/-- Identity relabeling preserves every coarse code. -/
@[simp]
theorem gLocalV1CoarseRelabelCode_identity
    (P : FiniteComparisonPresentation) (target : P.CoarseTarget) :
    P.gLocalV1CoarseRelabelCode P.gLocalV1IdentityRelabel target =
      P.coarseTargetCode target := by
  exact P.range_getD_coarseTargetCode target

/-- Identity relabeling preserves every fine code. -/
@[simp]
theorem gLocalV1FineRelabelCode_identity
    (P : FiniteComparisonPresentation) (target : P.FineTarget) :
    P.gLocalV1FineRelabelCode P.gLocalV1IdentityRelabel target =
      P.fineTargetCode target := by
  exact P.range_getD_fineTargetCode target

/-- Identity relabeling decodes to the original fine target. -/
@[simp]
theorem gLocalV1FineRelabelTarget_identity
    (P : FiniteComparisonPresentation) (target : P.FineTarget) :
    P.gLocalV1FineRelabelTarget P.gLocalV1IdentityRelabel target = target := by
  rw [gLocalV1FineRelabelTarget, P.gLocalV1FineRelabelCode_identity]
  exact P.fineTargetEntries_getD_fineTargetCode target

/-- The internally generated identity tables satisfy permutation and factor
commutation validity. -/
theorem gLocalV1IdentityRelabel_valid (P : FiniteComparisonPresentation) :
    P.gLocalV1TargetRelabelValid P.gLocalV1IdentityRelabel = true := by
  have hcoarse :
      P.gLocalV1IdentityRelabel.coarse.Perm
        (List.range P.coarseTargetEntriesDedup.length) := by
    exact List.Perm.refl _
  have hfine :
      P.gLocalV1IdentityRelabel.fine.Perm
        (List.range P.fineTargetEntries.length) := by
    exact List.Perm.refl _
  have hcomm : P.fineTargetEntries.all (fun target =>
      P.gLocalV1CoarseRelabelCode P.gLocalV1IdentityRelabel
          (P.computedFactor target) =
        P.coarseTargetCode (P.computedFactor
          (P.gLocalV1FineRelabelTarget P.gLocalV1IdentityRelabel target))) = true := by
    rw [List.all_eq_true]
    intro target _htarget
    rw [P.gLocalV1CoarseRelabelCode_identity,
      P.gLocalV1FineRelabelTarget_identity]
    simp
  simp only [gLocalV1TargetRelabelValid, hcoarse, hfine, decide_true,
    Bool.true_and, hcomm]

/-- Finite candidate relabels.  The identity is present unconditionally; every
other candidate is generated by finite code tables, boundedness, injectivity,
and the π-commutation equation. -/
def gLocalV1TargetRelabels (P : FiniteComparisonPresentation) :
    List P.GLocalV1TargetRelabel :=
  P.gLocalV1IdentityRelabel ::
    ((List.range P.coarseTargetEntriesDedup.length).permutations.flatMap fun coarse =>
      (List.range P.fineTargetEntries.length).permutations.filterMap fun fine =>
        let relabel : P.GLocalV1TargetRelabel := ⟨coarse, fine⟩
        if P.gLocalV1TargetRelabelValid relabel then some relabel else none).dedup

/-- The generated list contains exactly the identity and the valid
factor-preserving permutation pairs. -/
theorem mem_gLocalV1TargetRelabels_iff (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) :
    relabel ∈ P.gLocalV1TargetRelabels ↔
      relabel = P.gLocalV1IdentityRelabel ∨
        P.gLocalV1TargetRelabelValid relabel = true := by
  rcases relabel with ⟨coarse, fine⟩
  simp only [gLocalV1TargetRelabels, List.mem_cons, List.mem_dedup,
    List.mem_flatMap, List.mem_filterMap, List.mem_permutations]
  constructor
  · intro h
    rcases h with hidentity | ⟨coarse', hcoarse', fine', hfine', hfilter⟩
    · exact Or.inl hidentity
    · split at hfilter
      · have heq :
            (⟨coarse', fine'⟩ : P.GLocalV1TargetRelabel) = ⟨coarse, fine⟩ :=
          Option.some.inj hfilter
        cases heq
        exact Or.inr ‹P.gLocalV1TargetRelabelValid ⟨coarse, fine⟩ = true›
      · simp at hfilter
  · intro h
    rcases h with hidentity | hvalid
    · exact Or.inl hidentity
    · apply Or.inr
      have hparts := hvalid
      simp only [gLocalV1TargetRelabelValid, Bool.and_eq_true,
        decide_eq_true_eq, List.all_eq_true] at hparts
      refine ⟨coarse, ?_, fine, ?_, ?_⟩
      · exact hparts.1.1
      · exact hparts.1.2
      · simp [hvalid]

/-- Equivalently, the candidate list is exactly the complete valid relabel
family; the explicit identity head is justified by its validity theorem. -/
theorem mem_gLocalV1TargetRelabels_iff_valid
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel) :
    relabel ∈ P.gLocalV1TargetRelabels ↔
      P.gLocalV1TargetRelabelValid relabel = true := by
  rw [P.mem_gLocalV1TargetRelabels_iff]
  constructor
  · rintro (rfl | hvalid)
    · exact P.gLocalV1IdentityRelabel_valid
    · exact hvalid
  · exact Or.inr

/-- The internally generated relabel family is nonempty. -/
theorem gLocalV1TargetRelabels_nonempty (P : FiniteComparisonPresentation) :
    P.gLocalV1TargetRelabels ≠ [] := by
  simp [gLocalV1TargetRelabels]

/-! ## Terminal cell universe and incidence -/

/-- Side-local retained cells, with chart-role and incidence-vertex copies
kept separate. -/
inductive GLocalV1Cell (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
  | coarseChart : P.CoarseChart → GLocalV1Cell P A state
  | coarseVertex : P.CoarseChart → GLocalV1Cell P A state
  | coarseEdge : P.CoarseEdge → GLocalV1Cell P A state
  | coarseFace : P.CoarseFace → GLocalV1Cell P A state
  | fineChart : P.FineChart → GLocalV1Cell P A state
  | fineVertex : P.FineChart → GLocalV1Cell P A state
  | fineEdge : P.FineEdge → GLocalV1Cell P A state
  | fineFace : P.FineFace → GLocalV1Cell P A state
  deriving DecidableEq

/-- Retained terminal cell filter.  Every scoped chart receives one chart-role
and one incidence-vertex cell; only retained edges and actual retained face
members survive. -/
def gLocalV1CellList (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    List (P.GLocalV1Cell A state) :=
  (P.coarseChartEntries.dedup.flatMap fun chart =>
      if chart ∈ P.gLocalV1CoarseCharts A then
        [.coarseChart chart, .coarseVertex chart]
      else []) ++
    (P.coarseEdgeEntries.dedup.filterMap fun edge =>
      if edge ∈ state.coarseEdges then some (.coarseEdge edge) else none) ++
    (P.coarseFaceEntries.dedup.filterMap fun face =>
      if face ∈ P.gLocalV1RetainedCoarseFaceMembers A state then
        some (.coarseFace face)
      else none) ++
    (P.fineChartEntries.dedup.flatMap fun chart =>
      if chart ∈ P.gLocalV1FineCharts A then
        [.fineChart chart, .fineVertex chart]
      else []) ++
    (P.fineEdgeEntries.dedup.filterMap fun edge =>
      if edge ∈ state.fineEdges then some (.fineEdge edge) else none) ++
    (P.fineFaceEntries.dedup.filterMap fun face =>
      if face ∈ P.gLocalV1RetainedFineFaceMembers A state then
        some (.fineFace face)
      else none)

/-- Cell side. -/
def GLocalV1Cell.side {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1Side
  | .coarseChart _ | .coarseVertex _ | .coarseEdge _ | .coarseFace _ => .coarse
  | .fineChart _ | .fineVertex _ | .fineEdge _ | .fineFace _ => .fine

/-- Cell type. -/
def GLocalV1Cell.cellType {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1CellType
  | .coarseChart _ | .fineChart _ => .chart
  | .coarseVertex _ | .fineVertex _ => .vertex
  | .coarseEdge _ | .fineEdge _ => .edge
  | .coarseFace _ | .fineFace _ => .face

/-- Actual scoped support of a cell, encoded after target relabel. -/
def gLocalV1CellSupportCodes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) : P.GLocalV1Cell A state → List Nat
  | .coarseChart chart | .coarseVertex chart =>
      (P.gLocalV1CoarseChartSupport A chart).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .coarseEdge edge =>
      (P.gLocalV1CoarseEdgeSupport A edge).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .coarseFace face =>
      (P.gLocalV1CoarseFaceSupport A face).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .fineChart chart | .fineVertex chart =>
      (P.gLocalV1FineChartSupport A chart).image
        (P.gLocalV1FineRelabelCode relabel) |>.sort (· ≤ ·)
  | .fineEdge edge =>
      (P.gLocalV1FineEdgeSupport A edge).image
        (P.gLocalV1FineRelabelCode relabel) |>.sort (· ≤ ·)
  | .fineFace face =>
      (P.gLocalV1FineFaceSupport A face).image
        (P.gLocalV1FineRelabelCode relabel) |>.sort (· ≤ ·)

/-- Factor-image codes of a cell support. -/
def gLocalV1CellPiImageCodes (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) : P.GLocalV1Cell A state → List Nat
  | .coarseChart chart | .coarseVertex chart =>
      (P.gLocalV1CoarseChartSupport A chart).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .coarseEdge edge =>
      (P.gLocalV1CoarseEdgeSupport A edge).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .coarseFace face =>
      (P.gLocalV1CoarseFaceSupport A face).image
        (P.gLocalV1CoarseRelabelCode relabel) |>.sort (· ≤ ·)
  | .fineChart chart | .fineVertex chart =>
      (P.gLocalV1FineChartSupport A chart).image
        (fun target => P.gLocalV1CoarseRelabelCode relabel
          (P.computedFactor target)) |>.sort (· ≤ ·)
  | .fineEdge edge =>
      (P.gLocalV1FineEdgeSupport A edge).image
        (fun target => P.gLocalV1CoarseRelabelCode relabel
          (P.computedFactor target)) |>.sort (· ≤ ·)
  | .fineFace face =>
      (P.gLocalV1FineFaceSupport A face).image
        (fun target => P.gLocalV1CoarseRelabelCode relabel
          (P.computedFactor target)) |>.sort (· ≤ ·)

/-- Registered binary map status. -/
def gLocalV1CellMapStatus (P : FiniteComparisonPresentation)
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1MapStatus
  | .fineEdge edge => if (P.edgeMap edge).isSome then .mapped else .none
  | .fineFace face => if (P.faceMap face).isSome then .mapped else .none
  | _ => .mapped

/-- FaceTwin class multiplicity flag for an actual coarse face. -/
def gLocalV1CoarseFaceTwinFlag (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFace) : Bool :=
  2 ≤ (P.gLocalV1CoarseFaceMembers A (P.gLocalV1CoarseFaceKey A face)).card

/-- FaceTwin class multiplicity flag for an actual fine face. -/
def gLocalV1FineFaceTwinFlag (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFace) : Bool :=
  2 ≤ (P.gLocalV1FineFaceMembers A (P.gLocalV1FineFaceKey A face)).card

/-- Closed six-flag record, false outside the registered domains. -/
def gLocalV1CellFlags (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    P.GLocalV1Cell A state → GLocalV1Flags
  | .coarseVertex chart =>
      ⟨chart ∈ P.gLocalV1CoarseCriticalVertices A state, false, false,
        false, false, false⟩
  | .fineVertex chart =>
      ⟨chart ∈ P.gLocalV1FineCriticalVertices A state, false,
        chart ∈ P.gLocalV1ActiveFineVertices A state, false, false, false⟩
  | .coarseEdge edge =>
      ⟨edge ∈ P.gLocalV1CoarseCriticalEdges A state,
        edge ∈ P.gLocalV1GuardedCoarseEdges A state, false,
        edge ∈ P.gLocalV1CoarseBridges A state,
        P.coarseEdgeLeft edge = P.coarseEdgeRight edge, false⟩
  | .fineEdge edge =>
      ⟨edge ∈ P.gLocalV1FineCriticalEdges A state, false, false,
        edge ∈ P.gLocalV1FineBridges A state,
        P.fineEdgeLeft edge = P.fineEdgeRight edge, false⟩
  | .coarseFace face =>
      ⟨false, false, false, false, false, P.gLocalV1CoarseFaceTwinFlag A face⟩
  | .fineFace face =>
      ⟨false, false, false, false, false, P.gLocalV1FineFaceTwinFlag A face⟩
  | _ => ⟨false, false, false, false, false, false⟩

/-- Permanent cell label generated from one terminal cell. -/
def gLocalV1CellLabel (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (cell : P.GLocalV1Cell A state) :
    GLocalV1CellLabel :=
  ⟨cell.side, cell.cellType, P.gLocalV1CellMapStatus cell,
    P.gLocalV1CellSupportCodes A state relabel cell,
    P.gLocalV1CellPiImageCodes A state relabel cell,
    P.gLocalV1CellFlags A state cell⟩

/-- All full slot/sign relations between two retained cells. -/
def gLocalV1IncidenceRelations (P : FiniteComparisonPresentation)
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A}
    (root neighbor : P.GLocalV1Cell A state) : List GLocalV1Relation :=
  let direct : List GLocalV1Relation := match root, neighbor with
    | .coarseChart left, .coarseVertex right
    | .coarseVertex right, .coarseChart left
    | .fineChart left, .fineVertex right
    | .fineVertex right, .fineChart left =>
        if left = right then [.chartAt] else []
    | .coarseEdge edge, .coarseVertex chart
    | .coarseVertex chart, .coarseEdge edge =>
        (if P.coarseEdgeLeft edge = chart then [.endpoint0] else []) ++
          (if P.coarseEdgeRight edge = chart then [.endpoint1] else [])
    | .fineEdge edge, .fineVertex chart
    | .fineVertex chart, .fineEdge edge =>
        (if P.fineEdgeLeft edge = chart then [.endpoint0] else []) ++
          (if P.fineEdgeRight edge = chart then [.endpoint1] else [])
    | .coarseFace face, .coarseEdge edge
    | .coarseEdge edge, .coarseFace face =>
        (if P.coarseFaceEdge0 face = edge then [.boundary0Pos] else []) ++
        (if P.coarseFaceEdge1 face = edge then [.boundary1Neg] else []) ++
        (if P.coarseFaceEdge2 face = edge then [.boundary2Pos] else [])
    | .fineFace face, .fineEdge edge
    | .fineEdge edge, .fineFace face =>
        (if P.fineFaceEdge0 face = edge then [.boundary0Pos] else []) ++
        (if P.fineFaceEdge1 face = edge then [.boundary1Neg] else []) ++
        (if P.fineFaceEdge2 face = edge then [.boundary2Pos] else [])
    | _, _ => []
  direct

/-- Collapse a full relation to the outward-stub slot registry. -/
def gLocalV1RelationStubSlot : GLocalV1Relation → GLocalV1StubSlot
  | .chartAt => .chartAt
  | .endpoint0 | .boundary0Pos => .slot0
  | .endpoint1 | .boundary1Neg => .slot1
  | .boundary2Pos => .slot2

/-! ## Executable terminal-state enumeration -/

/-- Explicit enumeration of the coarse FaceTwin keys generated by the raw
face table.  Reduction only deletes these keys, so no ambient key powerset is
needed. -/
def gLocalV1CoarseFaceClassEntries (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1CoarseFaceTwinKey A) :=
  (P.coarseFaceEntries.map (P.gLocalV1CoarseFaceKey A)).dedup

/-- Explicit enumeration of the fine FaceTwin keys generated by the raw face
table.  Reduction only deletes these keys. -/
def gLocalV1FineFaceClassEntries (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1FineFaceTwinKey A) :=
  (P.fineFaceEntries.map (P.gLocalV1FineFaceKey A)).dedup

/-- The explicit coarse key list covers every initially generated FaceTwin
class. -/
theorem gLocalV1CoarseFaceClassEntries_complete
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (key : P.GLocalV1CoarseFaceTwinKey A)
    (hkey : key ∈ P.gLocalV1CoarseFaceClasses A) :
    key ∈ P.gLocalV1CoarseFaceClassEntries A := by
  obtain ⟨face, _hface, rfl⟩ := Finset.mem_image.mp hkey
  simp only [gLocalV1CoarseFaceClassEntries, List.mem_dedup, List.mem_map]
  exact ⟨face, P.coarseFace_mem_coarseFaceEntries face, rfl⟩

/-- The explicit fine key list covers every initially generated FaceTwin
class. -/
theorem gLocalV1FineFaceClassEntries_complete
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (key : P.GLocalV1FineFaceTwinKey A)
    (hkey : key ∈ P.gLocalV1FineFaceClasses A) :
    key ∈ P.gLocalV1FineFaceClassEntries A := by
  obtain ⟨face, _hface, rfl⟩ := Finset.mem_image.mp hkey
  simp only [gLocalV1FineFaceClassEntries, List.mem_dedup, List.mem_map]
  exact ⟨face, P.fineFace_mem_fineFaceEntries face, rfl⟩

/-- Every retained-edge/FaceTwin state over the explicit raw tables.  The
terminal filter below selects the canonical leaves of the full v5 reduction;
no selected trace or terminal certificate is supplied. -/
def gLocalV1AllStateList (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1V5State A) :=
  P.coarseEdgeEntries.dedup.sublists.flatMap fun coarseEdges =>
    (P.gLocalV1CoarseFaceClassEntries A).sublists.flatMap fun coarseFaces =>
      P.fineEdgeEntries.dedup.sublists.flatMap fun fineEdges =>
        (P.gLocalV1FineFaceClassEntries A).sublists.map fun fineFaces =>
          ⟨coarseEdges.toFinset, coarseFaces.toFinset,
            fineEdges.toFinset, fineFaces.toFinset⟩

/-- The explicit state list covers every componentwise substate of the
canonical raw-table initial state. -/
theorem gLocalV1AllStateList_complete (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (hsubstate : state.SubstateOf (P.gLocalV1InitialState A)) :
    state ∈ P.gLocalV1AllStateList A := by
  rcases state with ⟨coarseEdges, coarseFaces, fineEdges, fineFaces⟩
  obtain ⟨coarseEdgeValues, hcoarseEdgeValues, hcoarseEdges⟩ :=
    exists_sublists_toFinset_eq_of_subset P.coarseEdgeEntries.dedup coarseEdges
      (fun edge _hedge => by simp [P.coarseEdge_mem_coarseEdgeEntries edge])
  obtain ⟨coarseFaceValues, hcoarseFaceValues, hcoarseFaces⟩ :=
    exists_sublists_toFinset_eq_of_subset
      (P.gLocalV1CoarseFaceClassEntries A) coarseFaces
      (fun key hkey => P.gLocalV1CoarseFaceClassEntries_complete A key
        (hsubstate.coarseFaceClasses hkey))
  obtain ⟨fineEdgeValues, hfineEdgeValues, hfineEdges⟩ :=
    exists_sublists_toFinset_eq_of_subset P.fineEdgeEntries.dedup fineEdges
      (fun edge _hedge => by simp [P.fineEdge_mem_fineEdgeEntries edge])
  obtain ⟨fineFaceValues, hfineFaceValues, hfineFaces⟩ :=
    exists_sublists_toFinset_eq_of_subset
      (P.gLocalV1FineFaceClassEntries A) fineFaces
      (fun key hkey => P.gLocalV1FineFaceClassEntries_complete A key
        (hsubstate.fineFaceClasses hkey))
  simp only [gLocalV1AllStateList, List.mem_flatMap, List.mem_map]
  refine ⟨coarseEdgeValues, hcoarseEdgeValues,
    coarseFaceValues, hcoarseFaceValues,
    fineEdgeValues, hfineEdgeValues,
    fineFaceValues, hfineFaceValues, ?_⟩
  cases hcoarseEdges
  cases hcoarseFaces
  cases hfineEdges
  cases hfineFaces
  rfl

/-- Histogram of radius-two outward stubs from one root-neighbor pair. -/
def gLocalV1OutwardStubHistogram (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (root neighbor : P.GLocalV1Cell A state) :
    GLocalV1Histogram GLocalV1OutwardStub :=
  gLocalV1Histogram <|
    (P.gLocalV1CellList A state).flatMap fun outside =>
      if outside = root then [] else
        (P.gLocalV1IncidenceRelations neighbor outside).map fun relation =>
          ⟨outside.cellType, gLocalV1RelationStubSlot relation⟩

/-- Neighbor descriptor occurrences around one root, grouped only after actual
neighbor identity has retained the complete root-neighbor relation multiset. -/
def gLocalV1NeighborDescriptors (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (root : P.GLocalV1Cell A state) :
    List GLocalV1NeighborDescriptor :=
  (P.gLocalV1CellList A state).filterMap fun neighbor =>
    let relations := P.gLocalV1IncidenceRelations root neighbor
    if relations.isEmpty then none else
      some ⟨P.gLocalV1CellLabel A state relabel neighbor,
        relations.mergeSort gLocalV1OrdLE,
        P.gLocalV1OutwardStubHistogram A state root neighbor⟩

/-- Root-preserving side-local radius-one ball. -/
def gLocalV1RootedBall (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (root : P.GLocalV1Cell A state) :
    GLocalV1RootedBall :=
  ⟨P.gLocalV1CellLabel A state relabel root,
    gLocalV1Histogram (P.gLocalV1NeighborDescriptors A state relabel root)⟩

/-- One clipped histogram over all root occurrences of all distinct terminal
states. -/
def gLocalV1TerminalBallHistogram (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (relabel : P.GLocalV1TargetRelabel) :
    GLocalV1Histogram GLocalV1RootedBall :=
  let terminals := P.gLocalV1MemoizedTerminalStates A
  gLocalV1Histogram <|
    ((P.gLocalV1AllStateList A).filter fun state => state ∈ terminals).flatMap fun state =>
        (P.gLocalV1CellList A state).map fun root =>
          P.gLocalV1RootedBall A state relabel root

/-! ## Whole, all-subset, and canonical candidate records -/

/-- Full coarse-target scope reconstructed from the explicit complete list. -/
def gLocalV1FullTargetSubset (P : FiniteComparisonPresentation) :
    Finset P.CoarseTarget :=
  P.coarseTargetEntriesDedup.toFinset

/-- The explicit full scope is extensionally the whole finite coarse target. -/
theorem gLocalV1FullTargetSubset_eq_univ (P : FiniteComparisonPresentation) :
    P.gLocalV1FullTargetSubset = Finset.univ := by
  ext target
  simp [gLocalV1FullTargetSubset,
    P.coarseTargetEntriesDedup_complete target]

/-- Whole-scope record, computed exactly once at the full target set. -/
def gLocalV1WholeRecord (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) :
    GLocalV1ScopeRecord GLocalV1WholeConditions :=
  let A : Finset P.CoarseTarget := P.gLocalV1FullTargetSubset
  ⟨P.gLocalV1WholeConditions A, P.gLocalV1PacketKindUnion A,
    P.gLocalV1TerminalBallHistogram A relabel⟩

/-- Every nonempty coarse-target subset, once each. -/
def gLocalV1NonemptyTargetSubsets (P : FiniteComparisonPresentation) :
    List (Finset P.CoarseTarget) :=
  (P.coarseTargetEntriesDedup.sublists.filterMap fun targets =>
    let A := targets.toFinset
    if A.Nonempty then some A else none).dedup

/-- A subset occurs in the executable scope list exactly when it is nonempty. -/
theorem mem_gLocalV1NonemptyTargetSubsets_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget) :
    A ∈ P.gLocalV1NonemptyTargetSubsets ↔ A.Nonempty := by
  constructor
  · intro hA
    simp only [gLocalV1NonemptyTargetSubsets, List.mem_dedup,
      List.mem_filterMap] at hA
    rcases hA with ⟨targets, _htargets, htargets⟩
    split at htargets
    · injection htargets with htargetsA
      rw [← htargetsA]
      exact ‹targets.toFinset.Nonempty›
    · simp at htargets
  · intro hA
    obtain ⟨targets, htargets, htargetsA⟩ :=
      exists_sublists_toFinset_eq_of_complete P.coarseTargetEntriesDedup
        P.coarseTargetEntriesDedup_complete A
    simp only [gLocalV1NonemptyTargetSubsets, List.mem_dedup,
      List.mem_filterMap]
    refine ⟨targets, htargets, ?_⟩
    simp [htargetsA, hA]

/-- Every nonempty target subset occurs exactly once. -/
theorem gLocalV1NonemptyTargetSubsets_nodup (P : FiniteComparisonPresentation) :
    P.gLocalV1NonemptyTargetSubsets.Nodup := by
  exact List.nodup_dedup _

/-- One nonempty-subset record.  The subset itself is deliberately absent from
the returned value. -/
def gLocalV1ARecord (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (A : Finset P.CoarseTarget) :
    GLocalV1ScopeRecord GLocalV1AConditions :=
  ⟨P.gLocalV1AConditions A, P.gLocalV1PacketKindUnion A,
    P.gLocalV1TerminalBallHistogram A relabel⟩

/-- Aggregate the seven permanent condition coordinates before histogram
clipping. -/
def gLocalV1ConditionVector (P : FiniteComparisonPresentation) :
    GLocalV1ConditionVector :=
  let whole := P.gLocalV1WholeConditions P.gLocalV1FullTargetSubset
  let subsets := P.gLocalV1NonemptyTargetSubsets
  ⟨whole.c0,
    subsets.all fun A => (P.gLocalV1AConditions A).c1,
    subsets.all fun A => (P.gLocalV1AConditions A).c2,
    subsets.all fun A => (P.gLocalV1AConditions A).c3,
    subsets.all fun A => (P.gLocalV1AConditions A).c4,
    whole.c5, whole.c6⟩

/-- Candidate observation at one internally generated factor-preserving target
relabel. -/
def gLocalV1Candidate (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) : GLocalV1ObsValue :=
  ⟨P.gLocalV1ConditionVector, P.gLocalV1WholeRecord relabel,
    gLocalV1Histogram <|
      P.gLocalV1NonemptyTargetSubsets.map fun A =>
        P.gLocalV1ARecord relabel A⟩

/-- Minimum of a nonempty list under the derived structured order. -/
def gLocalV1Minimum (fallback : GLocalV1ObsValue) :
    List GLocalV1ObsValue → GLocalV1ObsValue
  | [] => fallback
  | candidate :: candidates => candidates.foldl
      (fun best next => if gLocalV1OrdLE next best then next else best) candidate

/-- The executable permanent observation. -/
def obsG (P : FiniteComparisonPresentation) : GLocalV1ObsValue :=
  let identityCandidate := P.gLocalV1Candidate P.gLocalV1IdentityRelabel
  gLocalV1Minimum identityCandidate
    (P.gLocalV1TargetRelabels.map P.gLocalV1Candidate)

/-- `obsG` is definitionally the structured minimum over all internally
generated factor-preserving relabel candidates. -/
theorem obsG_eq_min_piPreservingRelabels (P : FiniteComparisonPresentation) :
    P.obsG =
      gLocalV1Minimum (P.gLocalV1Candidate P.gLocalV1IdentityRelabel)
        (P.gLocalV1TargetRelabels.map P.gLocalV1Candidate) := by
  rfl

end FiniteComparisonPresentation
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
