import Mathlib.Data.List.Permutation
import Formal.Util.AssertStandardAxioms

/-!
# The permanent `G_local-v1` observation value

This module fixes the presentation-independent codomain of the observation
used in claim (v) of `G-107-aat-uniform-invariance-characterization`.  The
types below are a direct transcription of the permanent sixteen-line
`G_LOCAL_V1_SPEC` contract.  They deliberately contain no raw cell identifier,
target-subset identifier, fixture name, hash, rank, cohomology dimension, or
uniformity result.

Multiplicity is clipped at two.  Zero occurrences are represented by an
absent histogram row; every row therefore has multiplicity `one` or
`atLeastTwo`.  `gLocalV1Histogram` is the single normalization constructor used
by the observation pipeline: it sorts payloads, removes duplicate rows, and
computes the clipped count from the complete occurrence list.

## Implementation notes

Closed Lean inductives and structures mirror the sixteen rows of the permanent
`g_local_v1.py` observation contract while keeping serialization outside the
mathematical value.  Raw JSON objects and string-tagged records were rejected:
they would expose encoding choices and could carry forbidden fixture identifiers.
Exact multiplicities above two were also rejected because the permanent
grammar deliberately identifies them; the normalized clip-two histogram is the
single owner of that quotient.

The closed component orders also carry explicit `Std.TransOrd` and
`Std.LawfulEqOrd` instances.  These instances expose the laws already inherited
by the derived lexicographic comparators and let the owner prove histogram
invariance under permutation once.  Repeating fixture-specific comparator case
splits was rejected because it would duplicate the normalization kernel and
hide the reason T3's threefold and T6's sixfold occurrences have one quotient.
-/

namespace AAT.AG.ResolutionInvariance

universe u v

/-! ## Closed registries -/

/-- The side of a cell in a comparison presentation.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1Side
  | coarse
  | fine
  deriving DecidableEq, Repr, Ord

/-- The four typed cell roles retained by the radius-one incidence record.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1CellType
  | chart
  | vertex
  | edge
  | face
  deriving DecidableEq, Repr, Ord

/-- The only map-status information exposed by the permanent grammar.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1MapStatus
  | none
  | mapped
  deriving DecidableEq, Repr, Ord

/-- The four collapse-packet kinds registered by permanent `G_local-v1`.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1PacketKind
  | v4Coarse
  | v4FineOnly
  | coordinateDependency
  | closedDoubledCycle
  deriving DecidableEq, Repr, Ord

/-- Typed and signed incidence relations visible inside a rooted ball.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1Relation
  | chartAt
  | endpoint0
  | endpoint1
  | boundary0Pos
  | boundary1Neg
  | boundary2Pos
  deriving DecidableEq, Repr, Ord

/-- The coarser slot registry used by outward stubs.  Endpoint zero and face
boundary zero intentionally share `slot0`, and signs are discarded.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1StubSlot
  | chartAt
  | slot0
  | slot1
  | slot2
  deriving DecidableEq, Repr, Ord

/-- A positive occurrence count clipped at two.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1Multiplicity
  | one
  | atLeastTwo
  deriving DecidableEq, Repr, Ord

/-- Clip a natural count at two; zero is represented by no histogram row.

Position: observation-value API for the permanent multiplicity component in fixed
GOAL claim (v).  The count comes from an explicit occurrence list and is clipped
exactly as in `g_local_v1.py`; no presentation result or certificate is supplied.
-/
def gLocalV1Clip2 : Nat → Option GLocalV1Multiplicity
  | 0 => none
  | 1 => some .one
  | _ + 2 => some .atLeastTwo

/-! ## Canonical histograms -/

/-- One canonical histogram row.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1HistogramRow (α : Type u) where
  payload : α
  multiplicity : GLocalV1Multiplicity
  deriving DecidableEq, Repr, Ord

/-- A normalized list of clipped multiplicity rows.  Observation constructors
produce this type only through `gLocalV1Histogram`.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1Histogram (α : Type u) where
  rows : List (GLocalV1HistogramRow α)
  deriving DecidableEq, Repr, Ord

/-- The deterministic weak order induced by a type's `Ord` instance.

Position: ordering API used by the permanent histogram normalizer and final orbit
minimum in fixed GOAL claim (v).  Its only premise is the caller's `Ord` instance;
it receives no presentation result, relabel, or certificate.
-/
def gLocalV1OrdLE {α : Type u} [Ord α] (left right : α) : Bool :=
  (compare left right).isLE

/-- Normalize a complete occurrence list into sorted, unique, clip-two rows.

Position: canonical histogram constructor for the permanent multiplicity component
in fixed GOAL claim (v).  It consumes the complete explicit occurrence list and
computes sorting, deduplication, and clip-two counts without a supplied histogram.
-/
def gLocalV1Histogram {α : Type u} [Ord α] [DecidableEq α]
    (occurrences : List α) : GLocalV1Histogram α :=
  let sorted := occurrences.mergeSort gLocalV1OrdLE
  let payloads := sorted.eraseDups
  ⟨payloads.filterMap fun payload =>
    (gLocalV1Clip2 (occurrences.countP fun candidate => decide (candidate = payload))).map
      fun multiplicity => ⟨payload, multiplicity⟩⟩

/-- Permuting the complete occurrence list does not change its clipped
histogram.

Position: definition-owner normalization API for fixed GOAL claim (v)(a).
Its premise is only a raw occurrence permutation; it carries no expected
histogram, presentation result, observation value, or semantic label. -/
theorem gLocalV1Histogram_eq_of_perm
    {α : Type u} [Ord α] [DecidableEq α] [Std.TransOrd α]
    [Std.LawfulEqOrd α] {left right : List α}
    (hperm : left.Perm right) :
    gLocalV1Histogram left = gLocalV1Histogram right := by
  have htrans : ∀ a b c : α,
      gLocalV1OrdLE a b = true → gLocalV1OrdLE b c = true →
        gLocalV1OrdLE a c = true := by
    intro a b c hab hbc
    exact Std.TransCmp.isLE_trans hab hbc
  have htotal : ∀ a b : α,
      (gLocalV1OrdLE a b || gLocalV1OrdLE b a) = true := by
    intro a b
    simp only [gLocalV1OrdLE]
    rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := b) (b := a)]
    cases compare a b <;> decide
  have hantisymm : ∀ a b : α,
      gLocalV1OrdLE a b = true → gLocalV1OrdLE b a = true → a = b := by
    intro a b hab hba
    exact Std.LawfulEqOrd.eq_of_compare
      (Std.OrientedCmp.isLE_antisymm hab hba)
  have hsortedPerm :
      List.Perm (left.mergeSort gLocalV1OrdLE)
        (right.mergeSort gLocalV1OrdLE) :=
    (List.mergeSort_perm left gLocalV1OrdLE).trans
      (hperm.trans (List.mergeSort_perm right gLocalV1OrdLE).symm)
  have hsorted :
      left.mergeSort gLocalV1OrdLE = right.mergeSort gLocalV1OrdLE :=
    List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => hantisymm a b hab hba)
      (List.pairwise_mergeSort htrans htotal left)
      (List.pairwise_mergeSort htrans htotal right) hsortedPerm
  have hcount (payload : α) :
      left.countP (fun candidate => decide (candidate = payload)) =
        right.countP (fun candidate => decide (candidate = payload)) :=
    hperm.countP_eq _
  unfold gLocalV1Histogram
  rw [hsorted]
  simp_rw [hcount]

/-- Erasing duplicates from a nonempty constant occurrence list leaves its
single payload.

Position: canonical histogram helper for fixed GOAL claim (v)(a).  Its only
inputs are a payload and a repetition count; it carries no observation value,
presentation result, or semantic label. -/
theorem eraseDups_replicate_succ {α : Type u} [DecidableEq α]
    (payload : α) (extra : Nat) :
    (List.replicate (extra + 1) payload).eraseDups = [payload] := by
  cases extra <;> simp [List.replicate_succ, List.eraseDups_cons]

/-- Histogram multiplicity saturates after the second copy of one payload.

Position: definition-owner clip-two API for fixed GOAL claim (v)(a).  The
statement is derived from a complete constant occurrence list and assumes no
precomputed histogram or observation certificate. -/
theorem gLocalV1Histogram_replicate_add_two_eq_two
    {α : Type u} [Ord α] [DecidableEq α] (payload : α) (extra : Nat) :
    gLocalV1Histogram (List.replicate (extra + 2) payload) =
      gLocalV1Histogram [payload, payload] := by
  have hsorted :
      (List.replicate (extra + 2) payload).mergeSort gLocalV1OrdLE =
        List.replicate (extra + 2) payload :=
    List.perm_replicate.mp (List.mergeSort_perm _ _)
  rw [show [payload, payload] = List.replicate 2 payload by rfl]
  have hsortedTwo :
      (List.replicate 2 payload).mergeSort gLocalV1OrdLE =
        List.replicate 2 payload :=
    List.perm_replicate.mp (List.mergeSort_perm _ _)
  simp only [gLocalV1Histogram, hsorted, hsortedTwo]
  rw [eraseDups_replicate_succ, eraseDups_replicate_succ]
  simp [gLocalV1Clip2, List.countP_replicate]

/-- Saturating three repeated payloads is unchanged by one distinct leading
histogram occurrence.

Position: definition-owner mixed-block clip-two API for fixed GOAL claim
(v)(a). Raw premise/provenance: the complete list consists of one anchor and
three repeated payloads, without a supplied normalized result. -/
theorem gLocalV1Histogram_cons_three_eq_cons_two
    {α : Type u} [Ord α] [DecidableEq α] (anchor payload : α) :
    gLocalV1Histogram [anchor, payload, payload, payload] =
      gLocalV1Histogram [anchor, payload, payload] := by
  by_cases h : anchor = payload
  · subst anchor
    exact (gLocalV1Histogram_replicate_add_two_eq_two payload 2).trans
      (gLocalV1Histogram_replicate_add_two_eq_two payload 1).symm
  · generalize hab : gLocalV1OrdLE anchor payload = ab
    generalize hbb : gLocalV1OrdLE payload payload = bb
    have h' : payload ≠ anchor := Ne.symm h
    cases ab <;> cases bb <;>
      simp [gLocalV1Histogram, gLocalV1Clip2, List.mergeSort,
        List.eraseDups_cons, List.countP, List.countP.go, h, h', hab, hbb]

/-- Saturating six repeated payloads is unchanged by one distinct leading
histogram occurrence.

Position: definition-owner mixed-block clip-two API for fixed GOAL claim
(v)(a). Raw premise/provenance: the complete list consists of one anchor and
six repeated payloads, without a supplied normalized result. -/
theorem gLocalV1Histogram_cons_six_eq_cons_two
    {α : Type u} [Ord α] [DecidableEq α] (anchor payload : α) :
    gLocalV1Histogram
        [anchor, payload, payload, payload, payload, payload, payload] =
      gLocalV1Histogram [anchor, payload, payload] := by
  by_cases h : anchor = payload
  · subst anchor
    exact (gLocalV1Histogram_replicate_add_two_eq_two payload 5).trans
      (gLocalV1Histogram_replicate_add_two_eq_two payload 1).symm
  · generalize hab : gLocalV1OrdLE anchor payload = ab
    generalize hbb : gLocalV1OrdLE payload payload = bb
    have h' : payload ≠ anchor := Ne.symm h
    cases ab <;> cases bb <;>
      simp [gLocalV1Histogram, gLocalV1Clip2, List.mergeSort,
        List.eraseDups_cons, List.countP, List.countP.go, h, h', hab, hbb]

/-- Pointwise equal optional payload maps have equal `filterMap` outputs.

Position: definition-owner list transport helper used by histogram
normalization in fixed GOAL claim (v)(a).  Its only premise is equality on
the supplied finite input list; no observation result is supplied. -/
theorem filterMap_eq_of_eq_on_mem
    {α : Type u} {β : Type v} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) →
      xs.filterMap f = xs.filterMap g
  | [], _ => by rfl
  | a :: as, h => by
      simp only [List.filterMap_cons]
      rw [h a (by simp)]
      have ih := filterMap_eq_of_eq_on_mem (xs := as)
        (fun x hx => h x (List.mem_cons_of_mem a hx))
      cases g a <;> simp [ih]

/-- Duplicate erasure preserves membership.

Position: definition-owner list-normalization helper for the
histogram saturation API in fixed GOAL claim (v)(a). -/
theorem gLocalV1_mem_eraseDups_iff {α : Type u} [DecidableEq α]
    {value : α} : ∀ values : List α,
    value ∈ values.eraseDups ↔ value ∈ values
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      simp only [List.mem_cons]
      rw [gLocalV1_mem_eraseDups_iff]
      by_cases h : value = head
      · simp [h]
      · simp [h]
termination_by values => values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Duplicate erasure returns a sublist of the original list.

Position: definition-owner list-normalization helper for the
histogram saturation API in fixed GOAL claim (v)(a). -/
theorem gLocalV1_eraseDups_sublist {α : Type u} [DecidableEq α] :
    ∀ values : List α, values.eraseDups.Sublist values
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons]
      apply List.Sublist.cons_cons
      exact (gLocalV1_eraseDups_sublist
        (tail.filter fun candidate => !candidate == head)).trans
          List.filter_sublist
termination_by values => values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Duplicate erasure produces a duplicate-free list.

Position: definition-owner list-normalization helper for the
histogram saturation API in fixed GOAL claim (v)(a). -/
theorem gLocalV1_eraseDups_nodup {α : Type u} [DecidableEq α] :
    ∀ values : List α, values.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro hmem
        rw [gLocalV1_mem_eraseDups_iff] at hmem
        have := List.mem_filter.mp hmem
        simp at this
      · exact gLocalV1_eraseDups_nodup
          (tail.filter fun candidate => !candidate == head)
termination_by values => values.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Adding any positive context to two occurrences remains clipped at two.

Position: definition-owner arithmetic helper for the histogram
saturation API in fixed GOAL claim (v)(a). -/
theorem gLocalV1Clip2_add_extra_two
    (before after extra : Nat) :
    gLocalV1Clip2 (before + (extra + 2) + after) =
      gLocalV1Clip2 (before + 2 + after) := by
  have hleft : 2 ≤ before + (extra + 2) + after := by omega
  have hright : 2 ≤ before + 2 + after := by omega
  obtain ⟨left, hleftEq⟩ := Nat.exists_eq_add_of_le hleft
  obtain ⟨right, hrightEq⟩ := Nat.exists_eq_add_of_le hright
  rw [hleftEq, hrightEq]
  simp [gLocalV1Clip2, Nat.add_comm]

/-- A repeated payload inside any common prefix and suffix saturates after
its second occurrence.

Position: definition-owner histogram normalization API for fixed GOAL claim
(v)(a).  Its premises are only the comparison laws of the payload type; it
does not accept an expected histogram, observation value, or semantic label.
-/
theorem gLocalV1Histogram_append_replicate_add_two_eq_two
    {α : Type u} [Ord α] [DecidableEq α]
    (pre post : List α) (payload : α) (extra : Nat)
    (htrans : ∀ a b c : α,
      gLocalV1OrdLE a b = true → gLocalV1OrdLE b c = true →
        gLocalV1OrdLE a c = true)
    (htotal : ∀ a b : α,
      (gLocalV1OrdLE a b || gLocalV1OrdLE b a) = true)
    (hantisymm : ∀ a b : α,
      gLocalV1OrdLE a b = true → gLocalV1OrdLE b a = true → a = b) :
    gLocalV1Histogram
        (pre ++ List.replicate (extra + 2) payload ++ post) =
      gLocalV1Histogram (pre ++ [payload, payload] ++ post) := by
  let left := pre ++ List.replicate (extra + 2) payload ++ post
  let right := pre ++ [payload, payload] ++ post
  let leftPayloads := (left.mergeSort gLocalV1OrdLE).eraseDups
  let rightPayloads := (right.mergeSort gLocalV1OrdLE).eraseDups
  have hleftPairwise : leftPayloads.Pairwise
      (fun a b => gLocalV1OrdLE a b = true) := by
    exact (List.pairwise_mergeSort htrans htotal left).sublist
      (gLocalV1_eraseDups_sublist (left.mergeSort gLocalV1OrdLE))
  have hrightPairwise : rightPayloads.Pairwise
      (fun a b => gLocalV1OrdLE a b = true) := by
    exact (List.pairwise_mergeSort htrans htotal right).sublist
      (gLocalV1_eraseDups_sublist (right.mergeSort gLocalV1OrdLE))
  have hpayloadPerm : leftPayloads.Perm rightPayloads := by
    apply (List.perm_ext_iff_of_nodup
      (gLocalV1_eraseDups_nodup _) (gLocalV1_eraseDups_nodup _)).mpr
    intro candidate
    simp only [gLocalV1_mem_eraseDups_iff, List.mem_mergeSort, left, right]
    simp
  have hpayloads : leftPayloads = rightPayloads := by
    exact List.Perm.eq_of_pairwise
      (fun a b _ _ hab hba => hantisymm a b hab hba)
      hleftPairwise hrightPairwise hpayloadPerm
  dsimp only [leftPayloads, rightPayloads, left, right] at hpayloads
  unfold gLocalV1Histogram
  dsimp only
  rw [hpayloads]
  congr 1
  apply filterMap_eq_of_eq_on_mem
  intro candidate _
  simp only [List.countP_append, List.countP_replicate]
  by_cases h : payload = candidate
  · subst candidate
    simp only [List.countP_cons, List.countP_nil, decide_true, if_true,
      Nat.zero_add]
    rw [gLocalV1Clip2_add_extra_two]
  · have hdecide : decide (payload = candidate) = false :=
      decide_eq_false h
    simp only [List.countP_cons, List.countP_nil, hdecide,
      Bool.false_eq_true, if_false, Nat.add_zero]

/-! ## Closed observation records -/

/-- The six registered unary flags.  Flags outside their documented cell
domain are set to `false` by the observation constructor.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1Flags where
  critical : Bool
  guard : Bool
  port : Bool
  bridge : Bool
  selfLoop : Bool
  faceTwin : Bool
  deriving DecidableEq, Repr, Ord

/-- A target-relabelled cell label.  Supports and factor images are sorted
lists of relabelled target codes, never raw cell or subset identifiers.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1CellLabel where
  side : GLocalV1Side
  cellType : GLocalV1CellType
  mapStatus : GLocalV1MapStatus
  support : List Nat
  piImage : List Nat
  flags : GLocalV1Flags
  deriving DecidableEq, Repr, Ord

/-- An outward radius-two clipping stub, retaining only cell type and the
collapsed incidence slot.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1OutwardStub where
  cellType : GLocalV1CellType
  slot : GLocalV1StubSlot
  deriving DecidableEq, Repr, Ord

/-- One neighbor group in a radius-one rooted ball.  Relations retain their
full slot/sign multiplicity; outward stubs are clipped separately.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1NeighborDescriptor where
  neighborLabel : GLocalV1CellLabel
  relations : List GLocalV1Relation
  outwardStubHistogram : GLocalV1Histogram GLocalV1OutwardStub
  deriving DecidableEq, Repr, Ord

/-- A root-preserving, side-local radius-one typed incidence ball.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1RootedBall where
  rootLabel : GLocalV1CellLabel
  neighborDescriptors : GLocalV1Histogram GLocalV1NeighborDescriptor
  deriving DecidableEq, Repr, Ord

/-! ## Lawful derived orders -/

/-- The constant terminal comparator used by the derived lexicographic
`Ord` proofs below.

Position: definition-owner implementation API for the lawful histogram
saturation theorem in fixed GOAL claim (v)(a).  It carries no observation
value, presentation result, or semantic label. -/
def gLocalV1FinalEqCmp {α : Type u} : α → α → Ordering :=
  fun _ _ => .eq

/-- The terminal equality comparator is transitive.

Position: definition-owner typeclass evidence for the lawful derived-order
chain used by histogram saturation in fixed GOAL claim (v)(a). -/
instance instTransCmpGLocalV1FinalEqCmp {α : Type u} :
    Std.TransCmp (@gLocalV1FinalEqCmp α) where
  eq_swap := by intros; rfl
  isLE_trans := by simp [gLocalV1FinalEqCmp]

/-- Constructor-index comparison on observation sides is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed side registry. -/
instance instTransOrdGLocalV1Side : Std.TransOrd GLocalV1Side := by
  exact Std.TransOrd.instOn GLocalV1Side.ctorIdx

/-- Constructor-index comparison on observation sides reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed side registry. -/
instance instLawfulEqOrdGLocalV1Side : Std.LawfulEqOrd GLocalV1Side where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Constructor-index comparison on cell types is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed cell-type registry. -/
instance instTransOrdGLocalV1CellType : Std.TransOrd GLocalV1CellType := by
  exact Std.TransOrd.instOn GLocalV1CellType.ctorIdx

/-- Constructor-index comparison on cell types reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed cell-type registry. -/
instance instLawfulEqOrdGLocalV1CellType :
    Std.LawfulEqOrd GLocalV1CellType where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Constructor-index comparison on map statuses is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed map-status registry. -/
instance instTransOrdGLocalV1MapStatus : Std.TransOrd GLocalV1MapStatus := by
  exact Std.TransOrd.instOn GLocalV1MapStatus.ctorIdx

/-- Constructor-index comparison on map statuses reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed map-status registry. -/
instance instLawfulEqOrdGLocalV1MapStatus :
    Std.LawfulEqOrd GLocalV1MapStatus where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Constructor-index comparison on incidence relations is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed relation registry. -/
instance instTransOrdGLocalV1Relation : Std.TransOrd GLocalV1Relation := by
  exact Std.TransOrd.instOn GLocalV1Relation.ctorIdx

/-- Constructor-index comparison on incidence relations reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed relation registry. -/
instance instLawfulEqOrdGLocalV1Relation :
    Std.LawfulEqOrd GLocalV1Relation where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Constructor-index comparison on outward-stub slots is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed slot registry. -/
instance instTransOrdGLocalV1StubSlot : Std.TransOrd GLocalV1StubSlot := by
  exact Std.TransOrd.instOn GLocalV1StubSlot.ctorIdx

/-- Constructor-index comparison on outward-stub slots reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed slot registry. -/
instance instLawfulEqOrdGLocalV1StubSlot :
    Std.LawfulEqOrd GLocalV1StubSlot where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Constructor-index comparison on clipped multiplicities is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed multiplicity registry. -/
instance instTransOrdGLocalV1Multiplicity :
    Std.TransOrd GLocalV1Multiplicity := by
  exact Std.TransOrd.instOn GLocalV1Multiplicity.ctorIdx

/-- Constructor-index comparison on clipped multiplicities reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it is derived solely from the closed multiplicity registry. -/
instance instLawfulEqOrdGLocalV1Multiplicity :
    Std.LawfulEqOrd GLocalV1Multiplicity where
  eq_of_compare {a b} h := by
    cases a <;> cases b <;> simp_all +decide

/-- Lexicographic histogram-row comparison preserves transitivity whenever
payload comparison does.

Position: definition-owner generic order evidence for histogram saturation in
fixed GOAL claim (v)(a); its only premise is the payload order law. -/
instance instTransOrdGLocalV1HistogramRow
    {α : Type u} [Ord α] [Std.TransOrd α] :
    Std.TransOrd (GLocalV1HistogramRow α) := by
  change Std.TransCmp
    (compareLex
      (compareOn fun row : GLocalV1HistogramRow α => row.payload)
      (compareLex
        (compareOn fun row : GLocalV1HistogramRow α => row.multiplicity)
        gLocalV1FinalEqCmp))
  infer_instance

/-- Lexicographic histogram-row comparison reflects equality whenever payload
comparison does.

Position: definition-owner generic order evidence for histogram saturation in
fixed GOAL claim (v)(a); its only premise is the payload order law. -/
instance instLawfulEqOrdGLocalV1HistogramRow
    {α : Type u} [Ord α] [Std.LawfulEqOrd α] :
    Std.LawfulEqOrd (GLocalV1HistogramRow α) where
  compare_self := by
    rintro ⟨payload, multiplicity⟩
    simp only [instOrdGLocalV1HistogramRow,
      instOrdGLocalV1HistogramRow.ord, Std.ReflCmp.compare_self,
      Ordering.then_eq]
  eq_of_compare {a b} h := by
    rcases a with ⟨ap, am⟩
    rcases b with ⟨bp, bm⟩
    simp only [instOrdGLocalV1HistogramRow,
      instOrdGLocalV1HistogramRow.ord, Ordering.then_eq_eq,
      Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, _⟩
    rfl

/-- Lexicographic histogram comparison preserves transitivity whenever row
payload comparison does.

Position: definition-owner generic order evidence for histogram saturation in
fixed GOAL claim (v)(a); its only premise is the payload order law. -/
instance instTransOrdGLocalV1Histogram
    {α : Type u} [Ord α] [Std.TransOrd α] :
    Std.TransOrd (GLocalV1Histogram α) := by
  change Std.TransCmp
    (compareLex
      (compareOn fun histogram : GLocalV1Histogram α => histogram.rows)
      gLocalV1FinalEqCmp)
  infer_instance

/-- Lexicographic histogram comparison reflects equality whenever row payload
comparison does.

Position: definition-owner generic order evidence for histogram saturation in
fixed GOAL claim (v)(a); its only premise is the payload order law. -/
instance instLawfulEqOrdGLocalV1Histogram
    {α : Type u} [Ord α] [Std.LawfulEqOrd α] :
    Std.LawfulEqOrd (GLocalV1Histogram α) where
  compare_self := by
    rintro ⟨rows⟩
    simp only [instOrdGLocalV1Histogram, instOrdGLocalV1Histogram.ord,
      Std.ReflCmp.compare_self, Ordering.then_eq]
  eq_of_compare {a b} h := by
    rcases a with ⟨arows⟩
    rcases b with ⟨brows⟩
    simp only [instOrdGLocalV1Histogram, instOrdGLocalV1Histogram.ord,
      Ordering.then_eq_eq, Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, _⟩
    rfl

/-- Fieldwise lexicographic flag comparison is transitive.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only the six raw Boolean flag fields. -/
instance instTransOrdGLocalV1Flags : Std.TransOrd GLocalV1Flags := by
  change Std.TransCmp
    (compareLex (compareOn GLocalV1Flags.critical)
      (compareLex (compareOn GLocalV1Flags.guard)
        (compareLex (compareOn GLocalV1Flags.port)
          (compareLex (compareOn GLocalV1Flags.bridge)
            (compareLex (compareOn GLocalV1Flags.selfLoop)
              (compareLex (compareOn GLocalV1Flags.faceTwin)
                gLocalV1FinalEqCmp))))))
  infer_instance

/-- Fieldwise lexicographic flag comparison reflects equality.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only the six raw Boolean flag fields. -/
instance instLawfulEqOrdGLocalV1Flags : Std.LawfulEqOrd GLocalV1Flags where
  eq_of_compare {a b} h := by
    rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
    rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
    simp only [instOrdGLocalV1Flags, instOrdGLocalV1Flags.ord,
      Ordering.then_eq_eq, Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    rfl

/-- Fieldwise lexicographic cell-label comparison is transitive.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent label fields. -/
instance instTransOrdGLocalV1CellLabel : Std.TransOrd GLocalV1CellLabel := by
  change Std.TransCmp
    (compareLex (compareOn GLocalV1CellLabel.side)
      (compareLex (compareOn GLocalV1CellLabel.cellType)
        (compareLex (compareOn GLocalV1CellLabel.mapStatus)
          (compareLex (compareOn GLocalV1CellLabel.support)
            (compareLex (compareOn GLocalV1CellLabel.piImage)
              (compareLex (compareOn GLocalV1CellLabel.flags)
                gLocalV1FinalEqCmp))))))
  infer_instance

/-- Fieldwise lexicographic cell-label comparison reflects equality.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent label fields. -/
instance instLawfulEqOrdGLocalV1CellLabel :
    Std.LawfulEqOrd GLocalV1CellLabel where
  eq_of_compare {a b} h := by
    rcases a with ⟨a0, a1, a2, a3, a4, a5⟩
    rcases b with ⟨b0, b1, b2, b3, b4, b5⟩
    simp only [instOrdGLocalV1CellLabel, instOrdGLocalV1CellLabel.ord,
      Ordering.then_eq_eq, Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, _⟩
    rfl

/-- Fieldwise lexicographic outward-stub comparison is transitive.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent stub fields. -/
instance instTransOrdGLocalV1OutwardStub :
    Std.TransOrd GLocalV1OutwardStub := by
  change Std.TransCmp
    (compareLex (compareOn GLocalV1OutwardStub.cellType)
      (compareLex (compareOn GLocalV1OutwardStub.slot)
        gLocalV1FinalEqCmp))
  infer_instance

/-- Fieldwise lexicographic outward-stub comparison reflects equality.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent stub fields. -/
instance instLawfulEqOrdGLocalV1OutwardStub :
    Std.LawfulEqOrd GLocalV1OutwardStub where
  eq_of_compare {a b} h := by
    rcases a with ⟨a0, a1⟩
    rcases b with ⟨b0, b1⟩
    simp only [instOrdGLocalV1OutwardStub,
      instOrdGLocalV1OutwardStub.ord, Ordering.then_eq_eq,
      Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, _⟩
    rfl

/-- Fieldwise lexicographic neighbor-descriptor comparison is transitive.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent descriptor fields. -/
instance instTransOrdGLocalV1NeighborDescriptor :
    Std.TransOrd GLocalV1NeighborDescriptor := by
  change Std.TransCmp
    (compareLex (compareOn GLocalV1NeighborDescriptor.neighborLabel)
      (compareLex (compareOn GLocalV1NeighborDescriptor.relations)
        (compareLex
          (compareOn GLocalV1NeighborDescriptor.outwardStubHistogram)
          gLocalV1FinalEqCmp)))
  infer_instance

/-- Fieldwise lexicographic neighbor-descriptor comparison reflects equality.

Position: definition-owner order evidence for rooted-ball histogram saturation
in fixed GOAL claim (v)(a); it uses only permanent descriptor fields. -/
instance instLawfulEqOrdGLocalV1NeighborDescriptor :
    Std.LawfulEqOrd GLocalV1NeighborDescriptor where
  eq_of_compare {a b} h := by
    rcases a with ⟨a0, a1, a2⟩
    rcases b with ⟨b0, b1, b2⟩
    simp only [instOrdGLocalV1NeighborDescriptor,
      instOrdGLocalV1NeighborDescriptor.ord, Ordering.then_eq_eq,
      Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, rfl, _⟩
    rfl

/-- Fieldwise lexicographic rooted-ball comparison is transitive.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it uses only the permanent rooted-ball fields. -/
instance instTransOrdGLocalV1RootedBall :
    Std.TransOrd GLocalV1RootedBall := by
  change Std.TransCmp
    (compareLex (compareOn GLocalV1RootedBall.rootLabel)
      (compareLex
        (compareOn GLocalV1RootedBall.neighborDescriptors)
        gLocalV1FinalEqCmp))
  infer_instance

/-- Fieldwise lexicographic rooted-ball comparison reflects equality.

Position: definition-owner order evidence for histogram saturation in fixed
GOAL claim (v)(a); it uses only the permanent rooted-ball fields. -/
instance instLawfulEqOrdGLocalV1RootedBall :
    Std.LawfulEqOrd GLocalV1RootedBall where
  eq_of_compare {a b} h := by
    rcases a with ⟨a0, a1⟩
    rcases b with ⟨b0, b1⟩
    simp only [instOrdGLocalV1RootedBall,
      instOrdGLocalV1RootedBall.ord, Ordering.then_eq_eq,
      Std.LawfulEqOrd.compare_eq_iff_eq] at h
    rcases h with ⟨rfl, rfl, _⟩
    rfl

/-- Lawful derived comparison makes clip-two histogram saturation independent
of the surrounding occurrence-list context.

Position: definition-owner histogram normalization API for fixed GOAL claim
(v)(a).  Its premises are only the lawful `Ord` instances of the payload type;
it accepts no expected histogram, observation value, or semantic label. -/
theorem gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
    {α : Type u} [Ord α] [DecidableEq α] [Std.TransOrd α]
    [Std.LawfulEqOrd α]
    (pre post : List α) (payload : α) (extra : Nat) :
    gLocalV1Histogram
        (pre ++ List.replicate (extra + 2) payload ++ post) =
      gLocalV1Histogram (pre ++ [payload, payload] ++ post) := by
  apply gLocalV1Histogram_append_replicate_add_two_eq_two
  · intro a b c hab hbc
    exact Std.TransCmp.isLE_trans hab hbc
  · intro a b
    simp only [gLocalV1OrdLE]
    rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := b) (b := a)]
    cases compare a b <;> decide
  · intro a b hab hba
    exact Std.LawfulEqOrd.eq_of_compare
      (Std.OrientedCmp.isLE_antisymm hab hba)

/-- Rooted-ball histograms saturate repeated occurrences after the second copy
inside any common prefix and suffix.

Position: concrete definition-owner normalization API for the registered T3/T6
evaluation in fixed GOAL claim (v)(a).  It is derived from the rooted-ball
field order and receives no expected observation value or label. -/
theorem gLocalV1RootedBallHistogram_append_replicate_add_two_eq_two
    (pre post : List GLocalV1RootedBall)
    (payload : GLocalV1RootedBall) (extra : Nat) :
    gLocalV1Histogram
        (pre ++ List.replicate (extra + 2) payload ++ post) =
      gLocalV1Histogram (pre ++ [payload, payload] ++ post) := by
  exact gLocalV1Histogram_append_replicate_add_two_eq_two_of_lawfulOrd
    pre post payload extra

/-- Whole-scope condition coordinates.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1WholeConditions where
  c0 : Bool
  c5 : Bool
  c6 : Bool
  deriving DecidableEq, Repr, Ord

/-- Nonempty-target-subset condition coordinates.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1AConditions where
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  deriving DecidableEq, Repr, Ord

/-- A scope record formed from the universal terminal condition, the union of
all outgoing packet kinds over all reachable states, and all terminal balls.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1ScopeRecord (Conditions : Type u) where
  conditions : Conditions
  packetKindUnion : List GLocalV1PacketKind
  rootedBallHistogram : GLocalV1Histogram GLocalV1RootedBall
  deriving DecidableEq, Repr, Ord

/-- The aggregate seven-coordinate permanent condition vector.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1ConditionVector where
  c0 : Bool
  c1 : Bool
  c2 : Bool
  c3 : Bool
  c4 : Bool
  c5 : Bool
  c6 : Bool
  deriving DecidableEq, Repr, Ord

/-- Presentation-independent permanent `G_local-v1` observation value.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
structure GLocalV1ObsValue where
  aggregate : GLocalV1ConditionVector
  whole : GLocalV1ScopeRecord GLocalV1WholeConditions
  aRecordHistogram : GLocalV1Histogram (GLocalV1ScopeRecord GLocalV1AConditions)
  deriving DecidableEq, Repr, Ord

/-! ## Permanent contract inventory -/

/-- The sixteen registered contract rows, used to audit that every permanent
component has one definition-level owner in the Lean observation kernel.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
inductive GLocalV1ContractComponent
  | scope
  | terminal
  | conditions
  | packets
  | chartRole
  | ball
  | relations
  | mapStatus
  | neighbor
  | stubs
  | multiplicity
  | flags
  | supports
  | faces
  | targets
  | forbidden
  deriving DecidableEq, Repr, Ord

/-- The complete permanent contract-component registry, in specification
order.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
def gLocalV1ContractComponents : List GLocalV1ContractComponent :=
  [.scope, .terminal, .conditions, .packets, .chartRole, .ball, .relations,
    .mapStatus, .neighbor, .stubs, .multiplicity, .flags, .supports, .faces,
    .targets, .forbidden]

/-- The immutable upstream source contract hash recorded for provenance.  It
is not a field of, or input to, `GLocalV1ObsValue`.

Position: contract data/API definition for fixed GOAL claim (v). Any material input comes from the closed permanent `g_local_v1.py` value registry or an explicit occurrence list; no presentation result, semantic label, or certificate is supplied.
-/
def gLocalV1PermanentContractSha256 : String :=
  "5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8"

/-- The registry contains exactly sixteen contract components.

Position: API theorem for the fixed GOAL claim (v) observation contract. Any premise comes from the closed registry data defined in this module; it assumes no presentation result, semantic label, or certificate.
-/
theorem gLocalV1ContractComponents_length :
    gLocalV1ContractComponents.length = 16 := by
  decide

/-- Every contract component occurs exactly once in the registry.

Position: API theorem for the fixed GOAL claim (v) observation contract. Any premise comes from the closed registry data defined in this module; it assumes no presentation result, semantic label, or certificate.
-/
theorem gLocalV1ContractComponents_nodup :
    gLocalV1ContractComponents.Nodup := by
  decide

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
