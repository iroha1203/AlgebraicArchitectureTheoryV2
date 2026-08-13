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
enumeration; it does not select a terminal or observation.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
enumeration.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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

/-- Filtering a duplicate-free ambient list by the finite set carried by one
of its sublists recovers that sublist in the ambient order.

Position: generic enumeration API used to prove that the permanent terminal
state list contains each retained-cell state exactly once in fixed GOAL claim
(v)(a).  Its premises are only sublist membership and duplicate-freeness; no
presentation, terminal, observation, or semantic label is supplied. -/
theorem filter_mem_toFinset_eq_of_sublist_nodup
    {α : Type*} [DecidableEq α] {values entries : List α}
    (hsub : values.Sublist entries) (hnodup : entries.Nodup) :
    entries.filter (fun value => value ∈ values.toFinset) = values := by
  induction hsub with
  | slnil => rfl
  | @cons values entries value hsub ih =>
      have hnot : value ∉ values := fun hvalue =>
        (List.nodup_cons.mp hnodup).1 (hsub.subset hvalue)
      have htail : entries.filter (fun candidate =>
          candidate ∈ values.toFinset) = values :=
        ih (List.nodup_cons.mp hnodup).2
      have htail' : entries.filter (fun candidate => candidate ∈ values) = values := by
        simpa only [List.mem_toFinset] using htail
      simp [hnot, htail']
  | @cons₂ values entries value hsub ih =>
      have hnot : value ∉ entries := (List.nodup_cons.mp hnodup).1
      have htail := ih (List.nodup_cons.mp hnodup).2
      have hfilter : entries.filter (fun candidate =>
          candidate ∈ (value :: values).toFinset) =
          entries.filter (fun candidate => candidate ∈ values.toFinset) := by
        apply List.filter_congr
        intro candidate hcandidate
        have hne : candidate ≠ value := by
          intro heq
          subst candidate
          exact hnot hcandidate
        simp [hne]
      rw [List.filter_cons_of_pos (by simp), hfilter, htail]

/-- On the sublists of a duplicate-free list, conversion to a finite set is
injective because every sublist retains the ambient order.

Position: generic enumeration API supporting the unique-state terminal fast
path in fixed GOAL claim (v)(a).  It consumes only explicit list provenance
and no reducer or observation result. -/
theorem sublists_toFinset_injective_of_nodup
    {α : Type*} [DecidableEq α] {entries left right : List α}
    (hnodup : entries.Nodup) (hleft : left ∈ entries.sublists)
    (hright : right ∈ entries.sublists)
    (heq : left.toFinset = right.toFinset) : left = right := by
  rw [List.mem_sublists] at hleft hright
  have hl := filter_mem_toFinset_eq_of_sublist_nodup hleft hnodup
  have hr := filter_mem_toFinset_eq_of_sublist_nodup hright hnodup
  rw [heq] at hl
  exact hl.symm.trans hr

/-- Mapping duplicate-free sublists to their finite sets remains
duplicate-free.

Position: generic enumeration API supporting the unique-state terminal fast
path in fixed GOAL claim (v)(a).  The output is derived from the complete
explicit list and carries no state, terminal, observation, or label
certificate. -/
theorem nodup_sublists_map_toFinset {α : Type*} [DecidableEq α]
    (entries : List α) (hnodup : entries.Nodup) :
    (entries.sublists.map List.toFinset).Nodup := by
  exact (List.nodup_sublists.mpr hnodup).map_on
    (fun left hleft right hright heq =>
      sublists_toFinset_injective_of_nodup hnodup hleft hright heq)

/-- Duplicate-free explicit coarse-target enumeration.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def coarseTargetEntriesDedup (P : FiniteComparisonPresentation) :
    List P.CoarseTarget :=
  P.coarseTargetEntries.dedup

/-- Duplicate-free explicit fine-target enumeration generated from source
entries and the surjective raw fine reading.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def fineTargetEntries (P : FiniteComparisonPresentation) : List P.FineTarget :=
  (P.sourceEntries.map P.fineRead).dedup

/-- Every coarse target occurs in the duplicate-free explicit enumeration.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem coarseTargetEntriesDedup_complete (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) : target ∈ P.coarseTargetEntriesDedup := by
  simp [coarseTargetEntriesDedup, P.coarseTarget_mem_coarseTargetEntries target]

/-- Every fine target occurs in the source-generated explicit enumeration.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem fineTargetEntries_complete (P : FiniteComparisonPresentation)
    (target : P.FineTarget) : target ∈ P.fineTargetEntries := by
  obtain ⟨source, hsource⟩ := P.fineRead_surjective target
  subst target
  simp only [fineTargetEntries, List.mem_dedup, List.mem_map]
  exact ⟨source, P.source_mem_sourceEntries source, rfl⟩

/-- Executable coarse-target code.

Position: target-relabel API for fixed GOAL claim (v).  The code is computed from
the duplicate-free covered coarse-target list and is later checked as a permutation;
no target name, relabel certificate, or expected code is supplied.
-/
def coarseTargetCode (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) : Nat :=
  P.coarseTargetEntriesDedup.idxOf target

/-- Executable fine-target code.

Position: target-relabel API for fixed GOAL claim (v).  The code is computed from
the source-generated fine-target list and is later checked as a permutation and
against `computedFactor`; no expected code or commutation certificate is supplied.
-/
def fineTargetCode (P : FiniteComparisonPresentation)
    (target : P.FineTarget) : Nat :=
  P.fineTargetEntries.idxOf target

/-- Expose the coarse-target code as the index in the complete deduplicated
raw target enumeration.

Position: definition-owner computation API for fixed GOAL claim (v)(a).  It
reveals only the raw enumeration lookup and supplies no expected relabel code
or observation coordinate. -/
theorem coarseTargetCode_apply (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) :
    P.coarseTargetCode target = P.coarseTargetEntriesDedup.idxOf target := by
  rfl

/-- Expose the fine-target code as the index in the complete source-generated
fine-target enumeration.

Position: definition-owner computation API for fixed GOAL claim (v)(a).  It
reveals only the raw enumeration lookup and supplies no expected relabel code
or observation coordinate. -/
theorem fineTargetCode_apply (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    P.fineTargetCode target = P.fineTargetEntries.idxOf target := by
  rfl

/-- Coarse-target coding is injective because the deduplicated enumeration is
complete.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem coarseTargetCode_injective (P : FiniteComparisonPresentation) :
    Function.Injective P.coarseTargetCode := by
  intro left right hequal
  exact (List.idxOf_inj (P.coarseTargetEntriesDedup_complete left)).mp hequal

/-- Fine-target coding is injective because the source-generated deduplicated
enumeration is complete.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem fineTargetCode_injective (P : FiniteComparisonPresentation) :
    Function.Injective P.fineTargetCode := by
  intro left right hequal
  exact (List.idxOf_inj (P.fineTargetEntries_complete left)).mp hequal

/-- Every coarse target code lies inside the generated code range.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem coarseTargetCode_lt_length (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) :
    P.coarseTargetCode target < P.coarseTargetEntriesDedup.length :=
  List.idxOf_lt_length_iff.mpr (P.coarseTargetEntriesDedup_complete target)

/-- Every fine target code lies inside the generated code range.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem fineTargetCode_lt_length (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    P.fineTargetCode target < P.fineTargetEntries.length :=
  List.idxOf_lt_length_iff.mpr (P.fineTargetEntries_complete target)

/-- The numerical identity table evaluates to the original coarse code.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
@[simp]
theorem range_getD_coarseTargetCode (P : FiniteComparisonPresentation)
    (target : P.CoarseTarget) :
    (List.range P.coarseTargetEntriesDedup.length).getD
      (P.coarseTargetCode target) (P.coarseTargetCode target) =
        P.coarseTargetCode target := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_range (by simpa using P.coarseTargetCode_lt_length target)]
  rfl

/-- The numerical identity table evaluates to the original fine code.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
@[simp]
theorem range_getD_fineTargetCode (P : FiniteComparisonPresentation)
    (target : P.FineTarget) :
    (List.range P.fineTargetEntries.length).getD
      (P.fineTargetCode target) (P.fineTargetCode target) =
        P.fineTargetCode target := by
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_range (by simpa using P.fineTargetCode_lt_length target)]
  rfl

/-- Decoding an explicit fine target at its generated code returns that target.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
observation, expected equality, or certificate field.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
structure GLocalV1TargetRelabel (P : FiniteComparisonPresentation) where
  coarse : List Nat
  fine : List Nat
  deriving DecidableEq, Repr, Ord

/-- Relabel one coarse target code, falling back only outside the generated
permutation domain.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1CoarseRelabelCode (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.CoarseTarget) : Nat :=
  relabel.coarse.getD (P.coarseTargetCode target) (P.coarseTargetCode target)

/-- Relabel one fine target code, falling back only outside the generated
permutation domain.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1FineRelabelCode (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.FineTarget) : Nat :=
  relabel.fine.getD (P.fineTargetCode target) (P.fineTargetCode target)

/-- Decode the relabeled fine target.  Generated permutations keep the lookup
inside `fineTargetEntries`; the fallback makes the raw candidate total.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1FineRelabelTarget (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (target : P.FineTarget) : P.FineTarget :=
  P.fineTargetEntries.getD (P.gLocalV1FineRelabelCode relabel target) target

/-- Executable validity of a simultaneous relabel: both tables are complete
permutations and the computed factor commutes on every explicit fine target.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1TargetRelabelValid (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) : Bool :=
  decide (relabel.coarse.Perm
      (List.range P.coarseTargetEntriesDedup.length)) &&
    decide (relabel.fine.Perm (List.range P.fineTargetEntries.length)) &&
    P.fineTargetEntries.all fun target =>
      P.gLocalV1CoarseRelabelCode relabel (P.computedFactor target) =
        P.coarseTargetCode
          (P.computedFactor (P.gLocalV1FineRelabelTarget relabel target))

/-- Relabel validity is exactly completeness of both code permutations plus
pointwise commutation with the computed factor.

Position: definition-owner elimination API for the registered T3/T6 relabel
family in fixed GOAL claim (v)(a).  Its premises are the complete finite code
tables and the raw factor equation; no relabel certificate or observation
value is supplied. -/
theorem gLocalV1TargetRelabelValid_iff
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel) :
    P.gLocalV1TargetRelabelValid relabel = true ↔
      relabel.coarse.Perm (List.range P.coarseTargetEntriesDedup.length) ∧
      relabel.fine.Perm (List.range P.fineTargetEntries.length) ∧
      ∀ target ∈ P.fineTargetEntries,
        P.gLocalV1CoarseRelabelCode relabel (P.computedFactor target) =
          P.coarseTargetCode
            (P.computedFactor (P.gLocalV1FineRelabelTarget relabel target)) := by
  simp only [gLocalV1TargetRelabelValid, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨⟨hcoarse, hfine⟩, hcommutes⟩
    exact ⟨hcoarse, hfine, hcommutes⟩
  · rintro ⟨hcoarse, hfine, hcommutes⟩
    exact ⟨⟨hcoarse, hfine⟩, hcommutes⟩

/-- Complete permutation tables commuting with the computed factor form a
valid target relabel.

Position: definition-owner constructor API for fixed GOAL claim (v)(a).  All
premises are raw finite table properties; no Boolean result or observation
certificate is supplied. -/
theorem gLocalV1TargetRelabelValid_of
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel)
    (hcoarse : relabel.coarse.Perm
      (List.range P.coarseTargetEntriesDedup.length))
    (hfine : relabel.fine.Perm (List.range P.fineTargetEntries.length))
    (hcommutes : ∀ target ∈ P.fineTargetEntries,
      P.gLocalV1CoarseRelabelCode relabel (P.computedFactor target) =
        P.coarseTargetCode
          (P.computedFactor (P.gLocalV1FineRelabelTarget relabel target))) :
    P.gLocalV1TargetRelabelValid relabel = true :=
  (P.gLocalV1TargetRelabelValid_iff relabel).2
    ⟨hcoarse, hfine, hcommutes⟩

/-- Validity exposes the complete coarse-code permutation.

Position: definition-owner projection API for fixed GOAL claim (v)(a), derived
from the raw validity equation without supplying a permutation certificate. -/
theorem gLocalV1TargetRelabelValid_coarse_perm
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel)
    (hvalid : P.gLocalV1TargetRelabelValid relabel = true) :
    relabel.coarse.Perm
      (List.range P.coarseTargetEntriesDedup.length) :=
  (P.gLocalV1TargetRelabelValid_iff relabel).1 hvalid |>.1

/-- Validity exposes the complete fine-code permutation.

Position: definition-owner projection API for fixed GOAL claim (v)(a), derived
from the raw validity equation without supplying a permutation certificate. -/
theorem gLocalV1TargetRelabelValid_fine_perm
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel)
    (hvalid : P.gLocalV1TargetRelabelValid relabel = true) :
    relabel.fine.Perm (List.range P.fineTargetEntries.length) :=
  (P.gLocalV1TargetRelabelValid_iff relabel).1 hvalid |>.2.1

/-- Validity exposes factor commutation at every fine target.

Position: definition-owner projection API for fixed GOAL claim (v)(a), derived
from validity and explicit target enumeration without a supplied commutation
certificate. -/
theorem gLocalV1TargetRelabelValid_commutes
    (P : FiniteComparisonPresentation) (relabel : P.GLocalV1TargetRelabel)
    (hvalid : P.gLocalV1TargetRelabelValid relabel = true)
    (target : P.FineTarget) :
    P.gLocalV1CoarseRelabelCode relabel (P.computedFactor target) =
      P.coarseTargetCode
        (P.computedFactor (P.gLocalV1FineRelabelTarget relabel target)) := by
  exact (P.gLocalV1TargetRelabelValid_iff relabel).1 hvalid |>.2.2
    target (P.fineTargetEntries_complete target)

/-- Evaluate the coarse code of an explicitly constructed relabel table.

Position: definition-owner computation API for fixed GOAL claim (v)(a).  It
reveals only the raw list lookup and contains no expected relabel family or
observation value. -/
@[simp] theorem gLocalV1CoarseRelabelCode_mk
    (P : FiniteComparisonPresentation) (coarse fine : List Nat)
    (target : P.CoarseTarget) :
    P.gLocalV1CoarseRelabelCode
        (⟨coarse, fine⟩ : P.GLocalV1TargetRelabel) target =
      coarse.getD (P.coarseTargetCode target) (P.coarseTargetCode target) := by
  rfl

/-- Evaluate the fine code of an explicitly constructed relabel table.

Position: definition-owner computation API for fixed GOAL claim (v)(a).  It
reveals only the raw list lookup and contains no expected relabel family,
observation value, or semantic label. -/
@[simp] theorem gLocalV1FineRelabelCode_mk
    (P : FiniteComparisonPresentation) (coarse fine : List Nat)
    (target : P.FineTarget) :
    P.gLocalV1FineRelabelCode
        (⟨coarse, fine⟩ : P.GLocalV1TargetRelabel) target =
      fine.getD (P.fineTargetCode target) (P.fineTargetCode target) := by
  rfl

/-- Evaluate the fine target decoded by an explicitly constructed relabel
table.

Position: definition-owner computation API for fixed GOAL claim (v)(a).  It
reveals only the raw code-table lookup and contains no expected relabel family
or observation value. -/
@[simp] theorem gLocalV1FineRelabelTarget_mk
    (P : FiniteComparisonPresentation) (coarse fine : List Nat)
    (target : P.FineTarget) :
    P.gLocalV1FineRelabelTarget
        (⟨coarse, fine⟩ : P.GLocalV1TargetRelabel) target =
      P.fineTargetEntries.getD
        (fine.getD (P.fineTargetCode target) (P.fineTargetCode target))
        target := by
  rfl

/-- Identity target coding, generated internally.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1IdentityRelabel (P : FiniteComparisonPresentation) :
    P.GLocalV1TargetRelabel where
  coarse := List.range P.coarseTargetEntriesDedup.length
  fine := List.range P.fineTargetEntries.length

/-- Identity relabeling preserves every coarse code.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
@[simp]
theorem gLocalV1CoarseRelabelCode_identity
    (P : FiniteComparisonPresentation) (target : P.CoarseTarget) :
    P.gLocalV1CoarseRelabelCode P.gLocalV1IdentityRelabel target =
      P.coarseTargetCode target := by
  exact P.range_getD_coarseTargetCode target

/-- Identity relabeling preserves every fine code.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
@[simp]
theorem gLocalV1FineRelabelCode_identity
    (P : FiniteComparisonPresentation) (target : P.FineTarget) :
    P.gLocalV1FineRelabelCode P.gLocalV1IdentityRelabel target =
      P.fineTargetCode target := by
  exact P.range_getD_fineTargetCode target

/-- Identity relabeling decodes to the original fine target.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
@[simp]
theorem gLocalV1FineRelabelTarget_identity
    (P : FiniteComparisonPresentation) (target : P.FineTarget) :
    P.gLocalV1FineRelabelTarget P.gLocalV1IdentityRelabel target = target := by
  rw [gLocalV1FineRelabelTarget, P.gLocalV1FineRelabelCode_identity]
  exact P.fineTargetEntries_getD_fineTargetCode target

/-- The internally generated identity tables satisfy permutation and factor
commutation validity.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
and the π-commutation equation.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1TargetRelabels (P : FiniteComparisonPresentation) :
    List P.GLocalV1TargetRelabel :=
  P.gLocalV1IdentityRelabel ::
    ((List.range P.coarseTargetEntriesDedup.length).permutations.flatMap fun coarse =>
      (List.range P.fineTargetEntries.length).permutations.filterMap fun fine =>
        let relabel : P.GLocalV1TargetRelabel := ⟨coarse, fine⟩
        if P.gLocalV1TargetRelabelValid relabel then some relabel else none).dedup

/-- The generated list contains exactly the identity and the valid
factor-preserving permutation pairs.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
family; the explicit identity head is justified by its validity theorem.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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

/-- The internally generated relabel family is nonempty.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem gLocalV1TargetRelabels_nonempty (P : FiniteComparisonPresentation) :
    P.gLocalV1TargetRelabels ≠ [] := by
  simp [gLocalV1TargetRelabels]

/-! ## Terminal cell universe and incidence -/

/-- Side-local retained cells, with chart-role and incidence-vertex copies
kept separate.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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
members survive.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Cell side.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def GLocalV1Cell.side {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1Side
  | .coarseChart _ | .coarseVertex _ | .coarseEdge _ | .coarseFace _ => .coarse
  | .fineChart _ | .fineVertex _ | .fineEdge _ | .fineFace _ => .fine

/-- Expand the side tag of one retained observation cell.

Position: definition-owner match equation for fixed GOAL claim (v)(a).  It
exposes only the raw cell constructor and carries no expected label. -/
theorem gLocalV1CellSide_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (cell : P.GLocalV1Cell A state) :
    cell.side = match cell with
      | .coarseChart _ | .coarseVertex _ | .coarseEdge _ | .coarseFace _ =>
          .coarse
      | .fineChart _ | .fineVertex _ | .fineEdge _ | .fineFace _ => .fine := by
  rfl

/-- Cell type.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def GLocalV1Cell.cellType {P : FiniteComparisonPresentation}
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1CellType
  | .coarseChart _ | .fineChart _ => .chart
  | .coarseVertex _ | .fineVertex _ => .vertex
  | .coarseEdge _ | .fineEdge _ => .edge
  | .coarseFace _ | .fineFace _ => .face

/-- Expand the role tag of one retained observation cell.

Position: definition-owner match equation for fixed GOAL claim (v)(a).  It
exposes only the raw cell constructor and carries no expected label. -/
theorem gLocalV1CellType_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (cell : P.GLocalV1Cell A state) :
    cell.cellType = match cell with
      | .coarseChart _ | .fineChart _ => .chart
      | .coarseVertex _ | .fineVertex _ => .vertex
      | .coarseEdge _ | .fineEdge _ => .edge
      | .coarseFace _ | .fineFace _ => .face := by
  rfl

/-- Actual scoped support of a cell, encoded after target relabel.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Factor-image codes of a cell support.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Registered binary map status.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1CellMapStatus (P : FiniteComparisonPresentation)
    {A : Finset P.CoarseTarget} {state : P.GLocalV1V5State A} :
    P.GLocalV1Cell A state → GLocalV1MapStatus
  | .fineEdge edge => if (P.edgeMap edge).isSome then .mapped else .none
  | .fineFace face => if (P.faceMap face).isSome then .mapped else .none
  | _ => .mapped

/-- FaceTwin class multiplicity flag for an actual coarse face.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1CoarseFaceTwinFlag (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.CoarseFace) : Bool :=
  2 ≤ (P.gLocalV1CoarseFaceMembers A (P.gLocalV1CoarseFaceKey A face)).card

/-- Injective coarse FaceTwin keys force the coarse twin flag to be false.

Position: definition-owner flag API for the registered T3/T6 observation
evaluation in fixed GOAL claim (v)(a). The premise is raw key injectivity;
no precomputed class cardinality, flag, or observation is supplied. -/
theorem gLocalV1CoarseFaceTwinFlag_eq_false_of_key_injective
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (face : P.CoarseFace)
    (hinjective : Function.Injective (P.gLocalV1CoarseFaceKey A)) :
    P.gLocalV1CoarseFaceTwinFlag A face = false := by
  have hsubset :
      P.gLocalV1CoarseFaceMembers A (P.gLocalV1CoarseFaceKey A face) ⊆
        {face} := by
    intro member hmember
    rw [gLocalV1CoarseFaceMembers, Finset.mem_filter] at hmember
    exact Finset.mem_singleton.mpr (hinjective hmember.2)
  have hcard :
      (P.gLocalV1CoarseFaceMembers A
        (P.gLocalV1CoarseFaceKey A face)).card ≤ 1 := by
    calc
      _ ≤ ({face} : Finset P.CoarseFace).card := Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton face
  simp only [gLocalV1CoarseFaceTwinFlag, decide_eq_false_iff_not]
  omega

/-- FaceTwin class multiplicity flag for an actual fine face.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1FineFaceTwinFlag (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (face : P.FineFace) : Bool :=
  2 ≤ (P.gLocalV1FineFaceMembers A (P.gLocalV1FineFaceKey A face)).card

/-- Injective fine FaceTwin keys force the fine twin flag to be false.

Position: fine-side definition-owner flag API for fixed GOAL claim (v)(a).
The only premise is raw key injectivity. -/
theorem gLocalV1FineFaceTwinFlag_eq_false_of_key_injective
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (face : P.FineFace)
    (hinjective : Function.Injective (P.gLocalV1FineFaceKey A)) :
    P.gLocalV1FineFaceTwinFlag A face = false := by
  have hsubset :
      P.gLocalV1FineFaceMembers A (P.gLocalV1FineFaceKey A face) ⊆
        {face} := by
    intro member hmember
    rw [gLocalV1FineFaceMembers, Finset.mem_filter] at hmember
    exact Finset.mem_singleton.mpr (hinjective hmember.2)
  have hcard :
      (P.gLocalV1FineFaceMembers A
        (P.gLocalV1FineFaceKey A face)).card ≤ 1 := by
    calc
      _ ≤ ({face} : Finset P.FineFace).card := Finset.card_le_card hsubset
      _ = 1 := Finset.card_singleton face
  simp only [gLocalV1FineFaceTwinFlag, decide_eq_false_iff_not]
  omega

/-- Closed six-flag record, false outside the registered domains.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Permanent cell label generated from one terminal cell.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1CellLabel (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (cell : P.GLocalV1Cell A state) :
    GLocalV1CellLabel :=
  ⟨cell.side, cell.cellType, P.gLocalV1CellMapStatus cell,
    P.gLocalV1CellSupportCodes A state relabel cell,
    P.gLocalV1CellPiImageCodes A state relabel cell,
    P.gLocalV1CellFlags A state cell⟩

/-- All full slot/sign relations between two retained cells.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-! ## Cell-observation equation API -/

/-- Expand the relabelled support-code component by cell constructor.

Position: definition-owner equation API for the registered T3/T6 evaluation
in fixed GOAL claim (v)(a).  Every branch reads derived raw support and the
generated relabel; no expected label, histogram, or observation is supplied. -/
theorem gLocalV1CellSupportCodes_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (relabel : P.GLocalV1TargetRelabel)
    (cell : P.GLocalV1Cell A state) :
    P.gLocalV1CellSupportCodes A state relabel cell =
      match cell with
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
            (P.gLocalV1FineRelabelCode relabel) |>.sort (· ≤ ·) := rfl

/-- Expand the factor-image code component by cell constructor.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  Fine
branches use the internally computed factor, while coarse branches reuse raw
support; no image-code certificate or expected label is an argument. -/
theorem gLocalV1CellPiImageCodes_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (relabel : P.GLocalV1TargetRelabel)
    (cell : P.GLocalV1Cell A state) :
    P.gLocalV1CellPiImageCodes A state relabel cell =
      match cell with
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
              (P.computedFactor target)) |>.sort (· ≤ ·) := rfl

/-- Expand the registered map-status component by cell constructor.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  The two
partial-map branches inspect the raw presentation maps; no mapped-status
certificate is accepted. -/
theorem gLocalV1CellMapStatus_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (cell : P.GLocalV1Cell A state) :
    P.gLocalV1CellMapStatus cell =
      match cell with
      | .fineEdge edge => if (P.edgeMap edge).isSome then .mapped else .none
      | .fineFace face => if (P.faceMap face).isSome then .mapped else .none
      | _ => .mapped := rfl

/-- Expand all six reducer-derived cell flags by cell constructor.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  The
right side names the generated critical, active, guarded, bridge, loop, and
FaceTwin predicates; it supplies none of their truth values. -/
theorem gLocalV1CellFlags_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (cell : P.GLocalV1Cell A state) :
    P.gLocalV1CellFlags A state cell =
      match cell with
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
          ⟨false, false, false, false, false,
            P.gLocalV1CoarseFaceTwinFlag A face⟩
      | .fineFace face =>
          ⟨false, false, false, false, false,
            P.gLocalV1FineFaceTwinFlag A face⟩
      | _ => ⟨false, false, false, false, false, false⟩ := rfl

/-- Expand the complete signed/slot incidence list of two cells by their
constructors.

Position: definition-owner equation API for the rooted-ball evaluation in
fixed GOAL claim (v)(a).  Every branch uses raw chart/edge/face incidence and
contains no supplied neighbor descriptor or observation value. -/
theorem gLocalV1IncidenceRelations_apply
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A)
    (root neighbor : P.GLocalV1Cell A state) :
    P.gLocalV1IncidenceRelations root neighbor =
      match root, neighbor with
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
      | _, _ => [] := rfl

/-- Collapse a full relation to the outward-stub slot registry.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1RelationStubSlot : GLocalV1Relation → GLocalV1StubSlot
  | .chartAt => .chartAt
  | .endpoint0 | .boundary0Pos => .slot0
  | .endpoint1 | .boundary1Neg => .slot1
  | .boundary2Pos => .slot2

/-- Expand the permanent relation-to-stub-slot projection.

Position: definition-owner match equation for fixed GOAL claim (v)(a).  Its
input is one raw incidence relation and it contains no observation result. -/
theorem gLocalV1RelationStubSlot_apply (relation : GLocalV1Relation) :
    gLocalV1RelationStubSlot relation = match relation with
      | .chartAt => .chartAt
      | .endpoint0 | .boundary0Pos => .slot0
      | .endpoint1 | .boundary1Neg => .slot1
      | .boundary2Pos => .slot2 := by
  rfl

/-! ## Executable terminal-state enumeration -/

/-- Explicit enumeration of the coarse FaceTwin keys generated by the raw
face table.  Reduction only deletes these keys, so no ambient key powerset is
needed.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1CoarseFaceClassEntries (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1CoarseFaceTwinKey A) :=
  (P.coarseFaceEntries.map (P.gLocalV1CoarseFaceKey A)).dedup

/-- Explicit enumeration of the fine FaceTwin keys generated by the raw face
table.  Reduction only deletes these keys.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1FineFaceClassEntries (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1FineFaceTwinKey A) :=
  (P.fineFaceEntries.map (P.gLocalV1FineFaceKey A)).dedup

/-- The explicit coarse key list covers every initially generated FaceTwin
class.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem gLocalV1CoarseFaceClassEntries_complete
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (key : P.GLocalV1CoarseFaceTwinKey A)
    (hkey : key ∈ P.gLocalV1CoarseFaceClasses A) :
    key ∈ P.gLocalV1CoarseFaceClassEntries A := by
  obtain ⟨face, _hface, rfl⟩ := Finset.mem_image.mp hkey
  simp only [gLocalV1CoarseFaceClassEntries, List.mem_dedup, List.mem_map]
  exact ⟨face, P.coarseFace_mem_coarseFaceEntries face, rfl⟩

/-- The explicit fine key list covers every initially generated FaceTwin
class.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
no selected trace or terminal certificate is supplied.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1AllStateList (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : List (P.GLocalV1V5State A) :=
  let coarseEdgeSets :=
    P.coarseEdgeEntries.dedup.sublists.map List.toFinset
  let coarseFaceSets :=
    (P.gLocalV1CoarseFaceClassEntries A).sublists.map List.toFinset
  let fineEdgeSets := P.fineEdgeEntries.dedup.sublists.map List.toFinset
  let fineFaceSets :=
    (P.gLocalV1FineFaceClassEntries A).sublists.map List.toFinset
  (((coarseEdgeSets.product coarseFaceSets).product fineEdgeSets).product
      fineFaceSets).map fun components =>
    ⟨components.1.1.1, components.1.1.2, components.1.2, components.2⟩

/-- The complete explicit retained-cell state enumeration contains every
state exactly once.

Position: definition-owner uniqueness API for the terminal-ball fast path in
fixed GOAL claim (v)(a).  It is derived from duplicate-free raw entry lists
and carries no reachable set, selected terminal, observation, or semantic
label. -/
theorem gLocalV1AllStateList_nodup (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) : P.gLocalV1AllStateList A |>.Nodup := by
  have hcoarseEdges :
      (P.coarseEdgeEntries.dedup.sublists.map List.toFinset).Nodup :=
    nodup_sublists_map_toFinset _ (List.nodup_dedup _)
  have hcoarseFaces :
      ((P.gLocalV1CoarseFaceClassEntries A).sublists.map List.toFinset).Nodup :=
    nodup_sublists_map_toFinset _ (by
      unfold gLocalV1CoarseFaceClassEntries
      exact List.nodup_dedup _)
  have hfineEdges :
      (P.fineEdgeEntries.dedup.sublists.map List.toFinset).Nodup :=
    nodup_sublists_map_toFinset _ (List.nodup_dedup _)
  have hfineFaces :
      ((P.gLocalV1FineFaceClassEntries A).sublists.map List.toFinset).Nodup :=
    nodup_sublists_map_toFinset _ (by
      unfold gLocalV1FineFaceClassEntries
      exact List.nodup_dedup _)
  unfold gLocalV1AllStateList
  apply List.Nodup.map
  · intro left right heq
    rcases left with ⟨⟨⟨leftCE, leftCF⟩, leftFE⟩, leftFF⟩
    rcases right with ⟨⟨⟨rightCE, rightCF⟩, rightFE⟩, rightFF⟩
    simp only at heq
    injection heq
    subst rightCE
    subst rightCF
    subst rightFE
    subst rightFF
    rfl
  · exact ((hcoarseEdges.product hcoarseFaces).product hfineEdges).product
      hfineFaces

/-- The explicit state list covers every componentwise substate of the
canonical raw-table initial state.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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
  unfold gLocalV1AllStateList
  simp only [List.mem_map]
  refine ⟨(((coarseEdgeValues.toFinset, coarseFaceValues.toFinset),
    fineEdgeValues.toFinset), fineFaceValues.toFinset), ?_, ?_⟩
  · have hce : coarseEdgeValues.toFinset ∈
        P.coarseEdgeEntries.dedup.sublists.map List.toFinset :=
      List.mem_map.mpr ⟨coarseEdgeValues, hcoarseEdgeValues, rfl⟩
    have hcf : coarseFaceValues.toFinset ∈
        (P.gLocalV1CoarseFaceClassEntries A).sublists.map List.toFinset :=
      List.mem_map.mpr ⟨coarseFaceValues, hcoarseFaceValues, rfl⟩
    have hfe : fineEdgeValues.toFinset ∈
        P.fineEdgeEntries.dedup.sublists.map List.toFinset :=
      List.mem_map.mpr ⟨fineEdgeValues, hfineEdgeValues, rfl⟩
    have hff : fineFaceValues.toFinset ∈
        (P.gLocalV1FineFaceClassEntries A).sublists.map List.toFinset :=
      List.mem_map.mpr ⟨fineFaceValues, hfineFaceValues, rfl⟩
    apply List.mem_product.mpr
    refine ⟨?_, hff⟩
    apply List.mem_product.mpr
    refine ⟨?_, hfe⟩
    apply List.mem_product.mpr
    exact ⟨hce, hcf⟩
  · cases hcoarseEdges
    cases hcoarseFaces
    cases hfineEdges
    cases hfineFaces
    rfl

/-- Histogram of radius-two outward stubs from one root-neighbor pair.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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
neighbor identity has retained the complete root-neighbor relation multiset.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Root-preserving side-local radius-one ball.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1RootedBall (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (root : P.GLocalV1Cell A state) :
    GLocalV1RootedBall :=
  ⟨P.gLocalV1CellLabel A state relabel root,
    gLocalV1Histogram (P.gLocalV1NeighborDescriptors A state relabel root)⟩

/-- One clipped histogram over all root occurrences of all distinct terminal
states.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1TerminalBallHistogram (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (relabel : P.GLocalV1TargetRelabel) :
    GLocalV1Histogram GLocalV1RootedBall :=
  let terminals := P.gLocalV1MemoizedTerminalStates A
  gLocalV1Histogram <|
    ((P.gLocalV1AllStateList A).filter fun state => state ∈ terminals).flatMap fun state =>
        (P.gLocalV1CellList A state).map fun root =>
          P.gLocalV1RootedBall A state relabel root

/-- Histogram obtained directly from the canonical initial state's complete
root list.

Position: definition-owner normal form for the packet-free terminal fast path
in fixed GOAL claim (v)(a).  It is computed from the raw initial state and a
generated relabel; no terminal set, expected histogram, observation, or
semantic label is supplied. -/
def gLocalV1InitialBallHistogram (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (relabel : P.GLocalV1TargetRelabel) :
    GLocalV1Histogram GLocalV1RootedBall :=
  gLocalV1Histogram <|
    (P.gLocalV1CellList A (P.gLocalV1InitialState A)).map fun root =>
      P.gLocalV1RootedBall A (P.gLocalV1InitialState A) relabel root

/-- Initial packet emptiness reduces the full distinct-terminal histogram to
the directly computed initial-state root histogram.

Position: definition-owner observation fast-path API for the registered T3/T6
evaluation in fixed GOAL claim (v)(a).  The only material premise is raw
initial packet emptiness; the terminal set and histogram are derived, and no
expected observation or label is supplied. -/
theorem gLocalV1TerminalBallHistogram_eq_initial_of_initial_packet_empty
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (relabel : P.GLocalV1TargetRelabel)
    (hpacket : P.gLocalV1PacketVariants A
      (P.gLocalV1InitialState A) = ∅) :
    P.gLocalV1TerminalBallHistogram A relabel =
      P.gLocalV1InitialBallHistogram A relabel := by
  have hinitial : P.gLocalV1InitialState A ∈ P.gLocalV1AllStateList A :=
    P.gLocalV1AllStateList_complete A _
      (GLocalV1V5State.substateOf_refl _)
  have hsub : [P.gLocalV1InitialState A].Sublist (P.gLocalV1AllStateList A) :=
    List.singleton_sublist.mpr hinitial
  have hfilter := filter_mem_toFinset_eq_of_sublist_nodup hsub
    (P.gLocalV1AllStateList_nodup A)
  have hfilter' :
      (P.gLocalV1AllStateList A).filter (fun state =>
        state ∈ ({P.gLocalV1InitialState A} : Finset (P.GLocalV1V5State A))) =
        [P.gLocalV1InitialState A] := by
    simpa using hfilter
  have hterminals :=
    P.gLocalV1MemoizedTerminalStates_eq_singleton_of_initial_packet_empty
      A hpacket
  unfold gLocalV1TerminalBallHistogram gLocalV1InitialBallHistogram
  rw [hterminals]
  dsimp only
  rw [hfilter']
  simp

/-! ## Whole, all-subset, and canonical candidate records -/

/-- Full coarse-target scope reconstructed from the explicit complete list.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1FullTargetSubset (P : FiniteComparisonPresentation) :
    Finset P.CoarseTarget :=
  P.coarseTargetEntriesDedup.toFinset

/-- The explicit full scope is extensionally the whole finite coarse target.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem gLocalV1FullTargetSubset_eq_univ (P : FiniteComparisonPresentation) :
    P.gLocalV1FullTargetSubset = Finset.univ := by
  ext target
  simp [gLocalV1FullTargetSubset,
    P.coarseTargetEntriesDedup_complete target]

/-- Whole-scope record, computed exactly once at the full target set.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1WholeRecord (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) :
    GLocalV1ScopeRecord GLocalV1WholeConditions :=
  let A : Finset P.CoarseTarget := P.gLocalV1FullTargetSubset
  ⟨P.gLocalV1WholeConditions A, P.gLocalV1PacketKindUnion A,
    P.gLocalV1TerminalBallHistogram A relabel⟩

/-- Every nonempty coarse-target subset, once each.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1NonemptyTargetSubsets (P : FiniteComparisonPresentation) :
    List (Finset P.CoarseTarget) :=
  (P.coarseTargetEntriesDedup.sublists.filterMap fun targets =>
    let A := targets.toFinset
    if A.Nonempty then some A else none).dedup

/-- Expand the generated nonempty-target list into the complete target-entry
enumeration used by the observation kernel.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  The
right side is the permanent exhaustive subset generator; it contains no
expected subset order, observation value, or semantic label. -/
theorem gLocalV1NonemptyTargetSubsets_apply
    (P : FiniteComparisonPresentation) :
    P.gLocalV1NonemptyTargetSubsets =
      (P.coarseTargetEntriesDedup.sublists.filterMap fun targets =>
        let A := targets.toFinset
        if A.Nonempty then some A else none).dedup := by
  rfl

/-- A subset occurs in the executable scope list exactly when it is nonempty.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
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

/-- Every nonempty target subset occurs exactly once.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem gLocalV1NonemptyTargetSubsets_nodup (P : FiniteComparisonPresentation) :
    P.gLocalV1NonemptyTargetSubsets.Nodup := by
  exact List.nodup_dedup _

/-- One nonempty-subset record.  The subset itself is deliberately absent from
the returned value.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1ARecord (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (A : Finset P.CoarseTarget) :
    GLocalV1ScopeRecord GLocalV1AConditions :=
  ⟨P.gLocalV1AConditions A, P.gLocalV1PacketKindUnion A,
    P.gLocalV1TerminalBallHistogram A relabel⟩

/-- Aggregate the seven permanent condition coordinates before histogram
clipping.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
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

/-- Expand the aggregate condition vector into its whole-scope and generated
nonempty-subset coordinates.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  Every
coordinate remains computed by the permanent condition kernel; no expected
Boolean vector, checker bit, or semantic label is supplied. -/
theorem gLocalV1ConditionVector_apply (P : FiniteComparisonPresentation) :
    P.gLocalV1ConditionVector =
      let whole := P.gLocalV1WholeConditions P.gLocalV1FullTargetSubset
      let subsets := P.gLocalV1NonemptyTargetSubsets
      ⟨whole.c0,
        subsets.all fun A => (P.gLocalV1AConditions A).c1,
        subsets.all fun A => (P.gLocalV1AConditions A).c2,
        subsets.all fun A => (P.gLocalV1AConditions A).c3,
        subsets.all fun A => (P.gLocalV1AConditions A).c4,
        whole.c5, whole.c6⟩ := by
  rfl

/-- Candidate observation at one internally generated factor-preserving target
relabel.

Position: definition in the permanent observation API supporting fixed GOAL claim (v). Any material input comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no relabel or observation certificate is supplied.
-/
def gLocalV1Candidate (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) : GLocalV1ObsValue :=
  ⟨P.gLocalV1ConditionVector, P.gLocalV1WholeRecord relabel,
    gLocalV1Histogram <|
      P.gLocalV1NonemptyTargetSubsets.map fun A =>
        P.gLocalV1ARecord relabel A⟩

/-- Minimum of a nonempty list under the derived structured order.

Position: internal minimum API used by the main `obsG` definition for fixed GOAL
claim (v).  It folds the generated candidate list under the structured order; the
fallback is the generated identity candidate, not a supplied expected observation.
-/
def gLocalV1Minimum (fallback : GLocalV1ObsValue) :
    List GLocalV1ObsValue → GLocalV1ObsValue
  | [] => fallback
  | candidate :: candidates => candidates.foldl
      (fun best next => if gLocalV1OrdLE next best then next else best) candidate

/-- A minimum fold whose fallback and every listed candidate are the same value
returns that value without requiring any law of the structured comparator.

Position: definition-owner elimination API for the registered T3/T6
observation evaluation in fixed GOAL claim (v)(a).  The equalities are proved
from all internally generated candidates; no preferred relabel, minimum
certificate, or expected comparison outcome is supplied. -/
theorem gLocalV1Minimum_eq_of_forall_mem_eq
    (fallback value : GLocalV1ObsValue) (candidates : List GLocalV1ObsValue)
    (hfallback : fallback = value)
    (hcandidates : ∀ candidate ∈ candidates, candidate = value) :
    gLocalV1Minimum fallback candidates = value := by
  cases candidates with
  | nil =>
      simpa [gLocalV1Minimum] using hfallback
  | cons candidate candidates =>
      have hcandidate : candidate = value :=
        hcandidates candidate (by simp)
      rw [gLocalV1Minimum, hcandidate]
      have htail : ∀ next ∈ candidates, next = value := by
        intro next hnext
        exact hcandidates next (by simp [hnext])
      have hfold : ∀ tail : List GLocalV1ObsValue,
          (∀ next ∈ tail, next = value) →
            tail.foldl
                (fun best next =>
                  if gLocalV1OrdLE next best then next else best)
                value = value := by
        intro tail hall
        induction tail with
        | nil => rfl
        | cons next tail ih =>
            rw [List.foldl_cons, hall next (by simp)]
            simp only [ite_self]
            apply ih
            intro later hlater
            exact hall later (by simp [hlater])
      exact hfold candidates htail

/-- The executable permanent observation.

Position: main definition-level observation for fixed GOAL claim (v).  It generates
all valid factor-preserving relabels and their candidates from the raw presentation,
then takes their structured minimum; no relabel, label, or result is supplied.
-/
def obsG (P : FiniteComparisonPresentation) : GLocalV1ObsValue :=
  let identityCandidate := P.gLocalV1Candidate P.gLocalV1IdentityRelabel
  gLocalV1Minimum identityCandidate
    (P.gLocalV1TargetRelabels.map P.gLocalV1Candidate)

/-- `obsG` is definitionally the structured minimum over all internally
generated factor-preserving relabel candidates.

Position: observation API theorem supporting fixed GOAL claim (v). Any material premise comes from complete explicit entries, reducer-generated states or terminals, and the computed factor; no supplied relabel or observation is assumed.
-/
theorem obsG_eq_min_piPreservingRelabels (P : FiniteComparisonPresentation) :
    P.obsG =
      gLocalV1Minimum (P.gLocalV1Candidate P.gLocalV1IdentityRelabel)
        (P.gLocalV1TargetRelabels.map P.gLocalV1Candidate) := by
  rfl

/-- If every internally generated factor-preserving relabel candidate has the
same value, then the executable observation has that value.

Position: definition-owner orbit elimination API for fixed GOAL claim (v)(a).
The universal premise ranges over the complete generated relabel list and is
proved from raw candidate normal forms; it supplies neither a selected relabel
nor a minimum/comparator certificate. -/
theorem obsG_eq_of_forall_mem_targetRelabels_candidate_eq
    (P : FiniteComparisonPresentation) (value : GLocalV1ObsValue)
    (hcandidates : ∀ relabel ∈ P.gLocalV1TargetRelabels,
      P.gLocalV1Candidate relabel = value) :
    P.obsG = value := by
  rw [P.obsG_eq_min_piPreservingRelabels]
  apply gLocalV1Minimum_eq_of_forall_mem_eq
  · exact hcandidates P.gLocalV1IdentityRelabel (by
      simp [gLocalV1TargetRelabels])
  · intro candidate hcandidate
    obtain ⟨relabel, hmem, rfl⟩ := List.mem_map.mp hcandidate
    exact hcandidates relabel hmem

/-! ## Definition-owner evaluation and congruence API -/

/-- Pointwise equal optional maps have equal `filterMap` outputs on a fixed
finite input list.

Position: list-congruence helper for the observation definition-owner
API in fixed GOAL claim (v)(a).  Its premise is pointwise equality on the
explicit list, not a supplied observation value or semantic label. -/
theorem gLocalV1FilterMap_congr_left {α β : Type*}
    (values : List α) (left right : α → Option β)
    (h : ∀ value ∈ values, left value = right value) :
    values.filterMap left = values.filterMap right := by
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp only [List.filterMap_cons]
      rw [h value (by simp)]
      rw [ih (fun later hlater => h later (by simp [hlater]))]

/-- Expand the retained-cell list into its six typed raw components.

Position: definition-owner equation API for the registered T3/T6 observation
evaluation in fixed GOAL claim (v)(a).  The right side uses only explicit
entry lists, retained supports, and the reducer state; it contains no expected
observation or semantic label. -/
theorem gLocalV1CellList_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A) :
    P.gLocalV1CellList A state =
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
          else none) := by
  rfl

/-- A coarse chart cell is retained exactly when its raw chart is retained.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit chart entries and target support only. -/
@[simp] theorem coarseChart_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (chart : P.CoarseChart) :
    (GLocalV1Cell.coarseChart chart : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      chart ∈ P.gLocalV1CoarseCharts A := by
  simp [gLocalV1CellList, P.coarseChart_mem_coarseChartEntries chart]

/-- A coarse vertex cell is retained exactly when its raw chart is retained.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit chart entries and target support only. -/
@[simp] theorem coarseVertex_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (chart : P.CoarseChart) :
    (GLocalV1Cell.coarseVertex chart : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      chart ∈ P.gLocalV1CoarseCharts A := by
  simp [gLocalV1CellList, P.coarseChart_mem_coarseChartEntries chart]

/-- A coarse edge cell is retained exactly when the reducer state retains its
raw edge.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit edge entries and current state only. -/
@[simp] theorem coarseEdge_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (edge : P.CoarseEdge) :
    (GLocalV1Cell.coarseEdge edge : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      edge ∈ state.coarseEdges := by
  simp [gLocalV1CellList, P.coarseEdge_mem_coarseEdgeEntries edge]

/-- A coarse face cell is retained exactly when its raw face belongs to the
state's retained face members.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit face entries and current state only. -/
@[simp] theorem coarseFace_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (face : P.CoarseFace) :
    (GLocalV1Cell.coarseFace face : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      face ∈ P.gLocalV1RetainedCoarseFaceMembers A state := by
  simp [gLocalV1CellList, P.coarseFace_mem_coarseFaceEntries face]

/-- A fine chart cell is retained exactly when its raw chart is retained.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit chart entries and canonical-preimage support only. -/
@[simp] theorem fineChart_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (chart : P.FineChart) :
    (GLocalV1Cell.fineChart chart : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      chart ∈ P.gLocalV1FineCharts A := by
  simp [gLocalV1CellList, P.fineChart_mem_fineChartEntries chart]

/-- A fine vertex cell is retained exactly when its raw chart is retained.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit chart entries and canonical-preimage support only. -/
@[simp] theorem fineVertex_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (chart : P.FineChart) :
    (GLocalV1Cell.fineVertex chart : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      chart ∈ P.gLocalV1FineCharts A := by
  simp [gLocalV1CellList, P.fineChart_mem_fineChartEntries chart]

/-- A fine edge cell is retained exactly when the reducer state retains its
raw edge.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit edge entries and current state only. -/
@[simp] theorem fineEdge_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (edge : P.FineEdge) :
    (GLocalV1Cell.fineEdge edge : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      edge ∈ state.fineEdges := by
  simp [gLocalV1CellList, P.fineEdge_mem_fineEdgeEntries edge]

/-- A fine face cell is retained exactly when its raw face belongs to the
state's retained face members.

Position: definition-owner membership API for fixed GOAL claim (v)(a), derived
from the explicit face entries and current state only. -/
@[simp] theorem fineFace_mem_gLocalV1CellList_iff
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (face : P.FineFace) :
    (GLocalV1Cell.fineFace face : P.GLocalV1Cell A state) ∈
        P.gLocalV1CellList A state ↔
      face ∈ P.gLocalV1RetainedFineFaceMembers A state := by
  simp [gLocalV1CellList, P.fineFace_mem_fineFaceEntries face]

/-- Expand one permanent cell label into its six raw observation components.

Position: definition-owner equation API for fixed GOAL claim (v)(a).  Every
component is computed from the raw cell, support, factor image, and reducer
flags; no expected label is supplied. -/
theorem gLocalV1CellLabel_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (cell : P.GLocalV1Cell A state) :
    P.gLocalV1CellLabel A state relabel cell =
      ⟨cell.side, cell.cellType, P.gLocalV1CellMapStatus cell,
        P.gLocalV1CellSupportCodes A state relabel cell,
        P.gLocalV1CellPiImageCodes A state relabel cell,
        P.gLocalV1CellFlags A state cell⟩ := by
  rfl

/-- Evaluate an outward-stub histogram through an already evaluated complete
cell list.

Position: definition-owner evaluation API for fixed GOAL claim (v)(a).  Its
premise proves the raw complete cell-list equation and supplies no histogram
or observation result. -/
theorem gLocalV1OutwardStubHistogram_eq_of_cellList_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (root neighbor : P.GLocalV1Cell A state)
    (cells : List (P.GLocalV1Cell A state))
    (hcells : P.gLocalV1CellList A state = cells) :
    P.gLocalV1OutwardStubHistogram A state root neighbor =
      gLocalV1Histogram (cells.flatMap fun outside =>
        if outside = root then [] else
          (P.gLocalV1IncidenceRelations neighbor outside).map fun relation =>
            ⟨outside.cellType, gLocalV1RelationStubSlot relation⟩) := by
  rw [gLocalV1OutwardStubHistogram, hcells]

/-- Evaluate neighbor descriptors through an already evaluated complete cell
list.

Position: definition-owner evaluation API for fixed GOAL claim (v)(a).  Its
premise proves the raw complete cell-list equation and supplies no descriptor
histogram or observation result. -/
theorem gLocalV1NeighborDescriptors_eq_of_cellList_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (relabel : P.GLocalV1TargetRelabel)
    (root : P.GLocalV1Cell A state) (cells : List (P.GLocalV1Cell A state))
    (hcells : P.gLocalV1CellList A state = cells) :
    P.gLocalV1NeighborDescriptors A state relabel root =
      cells.filterMap fun neighbor =>
        let relations := P.gLocalV1IncidenceRelations root neighbor
        if relations.isEmpty then none else
          some ⟨P.gLocalV1CellLabel A state relabel neighbor,
            relations.mergeSort gLocalV1OrdLE,
            P.gLocalV1OutwardStubHistogram A state root neighbor⟩ := by
  rw [gLocalV1NeighborDescriptors, hcells]

/-- Expand one rooted ball into its computed root label and normalized neighbor
descriptor histogram.

Position: definition-owner composition API for fixed GOAL claim (v)(a); it
contains no expected rooted ball or semantic label. -/
theorem gLocalV1RootedBall_apply (P : FiniteComparisonPresentation)
    (A : Finset P.CoarseTarget) (state : P.GLocalV1V5State A)
    (relabel : P.GLocalV1TargetRelabel) (root : P.GLocalV1Cell A state) :
    P.gLocalV1RootedBall A state relabel root =
      ⟨P.gLocalV1CellLabel A state relabel root,
        gLocalV1Histogram
          (P.gLocalV1NeighborDescriptors A state relabel root)⟩ := by
  rfl

/-- Pointwise equality of retained cell labels implies equality of neighbor
descriptor occurrence lists.

Position: definition-owner congruence API for fixed GOAL claim (v)(a).  The
premise ranges over every retained raw cell and does not supply a resulting
histogram or rooted ball. -/
theorem gLocalV1NeighborDescriptors_eq_of_cellLabel_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (left right : P.GLocalV1TargetRelabel)
    (root : P.GLocalV1Cell A state)
    (hlabels : ∀ cell ∈ P.gLocalV1CellList A state,
      P.gLocalV1CellLabel A state left cell =
        P.gLocalV1CellLabel A state right cell) :
    P.gLocalV1NeighborDescriptors A state left root =
      P.gLocalV1NeighborDescriptors A state right root := by
  unfold gLocalV1NeighborDescriptors
  apply gLocalV1FilterMap_congr_left
  intro neighbor hneighbor
  simp only
  split
  · rfl
  · rw [hlabels neighbor hneighbor]

/-- Equality of the root label and every retained-neighbor label implies
equality of the corresponding rooted balls.

Position: definition-owner congruence API for fixed GOAL claim (v)(a).  Its
premises are raw label equalities, not a supplied rooted-ball result. -/
theorem gLocalV1RootedBall_eq_of_cellLabel_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (state : P.GLocalV1V5State A) (left right : P.GLocalV1TargetRelabel)
    (root : P.GLocalV1Cell A state)
    (hroot : P.gLocalV1CellLabel A state left root =
      P.gLocalV1CellLabel A state right root)
    (hlabels : ∀ cell ∈ P.gLocalV1CellList A state,
      P.gLocalV1CellLabel A state left cell =
        P.gLocalV1CellLabel A state right cell) :
    P.gLocalV1RootedBall A state left root =
      P.gLocalV1RootedBall A state right root := by
  rw [P.gLocalV1RootedBall_apply, P.gLocalV1RootedBall_apply, hroot,
    P.gLocalV1NeighborDescriptors_eq_of_cellLabel_eq A state left right root hlabels]

/-- Evaluate the initial histogram from a proved complete rooted-ball occurrence
list.

Position: definition-owner evaluation API for fixed GOAL claim (v)(a).  The
premise establishes the complete generated occurrence list; it does not supply
the normalized histogram as a presentation field. -/
theorem gLocalV1InitialBallHistogram_eq_of_occurrences_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (relabel : P.GLocalV1TargetRelabel)
    (occurrences : List GLocalV1RootedBall)
    (hoccurrences :
      (P.gLocalV1CellList A (P.gLocalV1InitialState A)).map (fun root =>
        P.gLocalV1RootedBall A (P.gLocalV1InitialState A) relabel root) =
          occurrences) :
    P.gLocalV1InitialBallHistogram A relabel =
      gLocalV1Histogram occurrences := by
  rw [gLocalV1InitialBallHistogram, hoccurrences]

/-- Pointwise equality of all retained cell labels lifts to equality of the
complete initial rooted-ball histograms.

Position: definition-owner relabel congruence API for fixed GOAL claim (v)(a).
The premise ranges over the complete raw retained-cell list and contains no
expected observation value. -/
theorem gLocalV1InitialBallHistogram_eq_of_cellLabel_eq
    (P : FiniteComparisonPresentation) (A : Finset P.CoarseTarget)
    (left right : P.GLocalV1TargetRelabel)
    (hlabels : ∀ cell ∈ P.gLocalV1CellList A (P.gLocalV1InitialState A),
      P.gLocalV1CellLabel A (P.gLocalV1InitialState A) left cell =
        P.gLocalV1CellLabel A (P.gLocalV1InitialState A) right cell) :
    P.gLocalV1InitialBallHistogram A left =
      P.gLocalV1InitialBallHistogram A right := by
  unfold gLocalV1InitialBallHistogram
  congr 1
  apply List.map_congr_left
  intro root hroot
  exact P.gLocalV1RootedBall_eq_of_cellLabel_eq A
    (P.gLocalV1InitialState A) left right root
    (hlabels root hroot) hlabels

/-- Expand the whole-scope record into conditions, packet union, and terminal
ball histogram.

Position: definition-owner composition API for fixed GOAL claim (v)(a).  All
three components are computed by the observation kernel; none is supplied as
a certificate. -/
theorem gLocalV1WholeRecord_apply (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) :
    P.gLocalV1WholeRecord relabel =
      ⟨P.gLocalV1WholeConditions P.gLocalV1FullTargetSubset,
        P.gLocalV1PacketKindUnion P.gLocalV1FullTargetSubset,
        P.gLocalV1TerminalBallHistogram P.gLocalV1FullTargetSubset relabel⟩ := by
  rfl

/-- Expand one nonempty-target-subset record into conditions, packet union,
and terminal ball histogram.

Position: definition-owner composition API for fixed GOAL claim (v)(a).  All
three components are computed by the observation kernel; none is supplied as
a certificate. -/
theorem gLocalV1ARecord_apply (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) (A : Finset P.CoarseTarget) :
    P.gLocalV1ARecord relabel A =
      ⟨P.gLocalV1AConditions A, P.gLocalV1PacketKindUnion A,
        P.gLocalV1TerminalBallHistogram A relabel⟩ := by
  rfl

/-- Expand one relabel candidate into its aggregate, whole-scope, and
nonempty-subset components.

Position: definition-owner composition API for fixed GOAL claim (v)(a).  The
candidate is generated from the raw presentation and relabel; no expected
observation value is supplied. -/
theorem gLocalV1Candidate_apply (P : FiniteComparisonPresentation)
    (relabel : P.GLocalV1TargetRelabel) :
    P.gLocalV1Candidate relabel =
      ⟨P.gLocalV1ConditionVector, P.gLocalV1WholeRecord relabel,
        gLocalV1Histogram <|
          P.gLocalV1NonemptyTargetSubsets.map fun A =>
            P.gLocalV1ARecord relabel A⟩ := by
  rfl

end FiniteComparisonPresentation
end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
