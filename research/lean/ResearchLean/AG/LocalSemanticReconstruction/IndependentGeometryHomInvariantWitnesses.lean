import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Coherent primitive witnesses for every native invariant kind

Common Hom queries keep all original computational roles. Auxiliary queries
are candidate-indexed Boolean inverse-graph points, declared before selecting
either invariant family. Row rules inspect only invariant kinds, individual
evaluations, and object/index graph points. They never assert the existence of
a completed transport or an entire auxiliary coherent family.

The presentation retains auxiliary finite tables as data. A subsequent quotient
must erase their choices while preserving the entire common Hom table. This
module constructs the native invariant-transport proof from those point rules
and reads every original transport back into such a presentation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Auxiliary index references and inverse-graph points precede either selected family. -/
inductive Query where
  /-- One auxiliary value-graph point at a candidate invariant-index pair. -/
  | row (I J : Type u) (i : I) (j : J) (q : IndependentInverseGraph.Query.{u, u})

/-- Auxiliary local values are single Booleans. -/
abbrev Table := Query.{u} → Bool

/-- Project a candidate index pair without assembling any native map. -/
def row (w : Table.{u}) (I J : Type u) (i : I) (j : J) :
    IndependentInverseGraph.Table.{u, u} := fun q => w (.row I J i j q)

/-- All original common Hom data survive; only their object and index rows are used here. -/
structure Retained (I J : InvariantFamily U) (mode : Mode) where
  /-- A Boolean table on each finite subset of the original common Hom queries. -/
  family : TagChange.CoherentFamily (IndependentGeometryHomPrimitive.Query.{u, v} U mode)
  /-- The object graph has one primitive output at every input. -/
  objectRows : CoreLaws.ObjectRows (TagChange.assemble family)
  /-- Invariant indices form the original directed candidate-carrier graph. -/
  indexRows : IndependentCarrierGraph.IsLawful I.Index J.Index
    (invariant (TagChange.assemble family))

/-- Singleton readings recover every original Hom query, including context and raw roles. -/
def Retained.table {I J : InvariantFamily U} (r : Retained.{u, v} I J mode) :
    IndependentGeometryHomPrimitive.Table.{u, v} U mode := TagChange.assemble r.family

/-- Unique object rows assemble the native directed object action. -/
def Retained.objectMap {I J : InvariantFamily U} (r : Retained.{u, v} I J mode) :
    ArchitectureObject U → ArchitectureObject U := CoreLaws.objectMap r.table r.objectRows

/-- Unique invariant-index rows assemble the native directed index action. -/
def Retained.indexMap {I J : InvariantFamily U} (r : Retained.{u, v} I J mode) :
    I.Index → J.Index := IndependentCarrierGraph.assemble _ _ (invariant r.table) r.indexRows

/-- A true object point specifies exactly the reconstructed object image. -/
theorem Retained.object_point_iff {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (A B : ArchitectureObject U) : r.table (.object A B) = true ↔ r.objectMap A = B :=
  (CoreLaws.objectGraph r.table r.objectRows).edge_eq_true_iff_target_eq A B

/-- A true index point specifies exactly the reconstructed invariant image. -/
theorem Retained.index_point_iff {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (i : I.Index) (j : J.Index) :
    r.table (.invariant (.edge I.Index J.Index i j)) = true ↔ r.indexMap i = j :=
  (IndependentCarrierGraph.graph _ _ (invariant r.table) r.indexRows.2).edge_eq_true_iff_target_eq i j

/-- Retained equality preserves the whole family; proof fields introduce no distinctions. -/
@[ext] theorem Retained.ext {I J : InvariantFamily U} {r s : Retained.{u, v} I J mode}
    (h : r.family = s.family) : r = s := by
  cases r
  cases s
  cases h
  rfl

/-- Local inverse/evaluation laws for functions, pointwise iff for predicates, and rejection of mixed kinds. -/
def RowLaw (source target : Invariant U)
    (h : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (w : IndependentInverseGraph.Table.{u, u}) : Prop :=
  match source, target with
  | .function F, .function G =>
      IndependentInverseGraph.IsLawful F.Value G.Value w ∧
        ∀ A B, h (.object A B) = true →
          w (.forward (.edge F.Value G.Value (F.evaluate A) (G.evaluate B))) = true
  | .predicate P, .predicate Q =>
      ∀ A B, h (.object A B) = true → (P.holds A ↔ Q.holds B)
  | _, _ => False

/-- Original invariant kind tags decide whether a row uses auxiliary value points. -/
def isFunction : Invariant U → Bool
  | .function _ => true
  | .predicate _ => false

/-- Candidate index pairs with no function/function transport have unique inactive auxiliary responses. -/
def IsAuxTyped (I J : InvariantFamily U) (r : Retained.{u, v} I J mode) (w : Table.{u}) : Prop :=
  (∀ M N i j q, (M ≠ I.Index ∨ N ≠ J.Index) → w (.row M N i j q) = false) ∧
  ∀ i j q, (r.table (.invariant (.edge I.Index J.Index i j)) = false ∨
    isFunction (I.invariant i) = false ∨ isFunction (J.invariant j) = false) →
      w (.row I.Index J.Index i j q) = false

/-- A presentation is coherent finite data with primitive row rules, before auxiliary choice erasure. -/
structure Presentation (I J : InvariantFamily U) (mode : Mode) where
  /-- Every original Hom role remains observable. -/
  retained : Retained.{u, v} I J mode
  /-- Auxiliary inverse graphs are assembled from coherent finite Boolean tables. -/
  auxiliary : TagChange.CoherentFamily Query.{u}
  /-- Unused candidate indices and predicate rows are normalized to false. -/
  auxiliaryTyped : IsAuxTyped I J retained (TagChange.assemble auxiliary)
  /-- Each true index pair obeys its native kind's primitive row rules. -/
  rows : ∀ i j, retained.table (.invariant (.edge I.Index J.Index i j)) = true →
    RowLaw (I.invariant i) (J.invariant j) retained.table
      (row (TagChange.assemble auxiliary) I.Index J.Index i j)

/-- The original native existence conditions are the comparison target, not presentation fields. -/
abbrev Native (I J : InvariantFamily U) (mode : Mode) :=
  {r : Retained.{u, v} I J mode // ∀ i,
    Invariant.TransportedAlong (I.invariant i) (J.invariant (r.indexMap i)) id r.objectMap}

/-- Every native invariant kind is reconstructed from its primitive row law. -/
theorem transported_of_row {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (source target : Invariant U) (w : IndependentInverseGraph.Table.{u, u})
    (hl : RowLaw source target r.table w) :
    Invariant.TransportedAlong source target id r.objectMap := by
  cases source with
  | function F =>
      cases target with
      | function G =>
          refine ⟨IndependentInverseGraph.assemble F.Value G.Value w hl.1, ?_⟩
          intro A
          apply IndependentCarrierGraph.assemble_eq_of_edge
          exact hl.2 A _ ((r.object_point_iff A _).2 rfl)
      | predicate Q => exact False.elim hl
  | predicate P =>
      cases target with
      | function G => exact False.elim hl
      | predicate Q => exact fun A => hl A _ ((r.object_point_iff A _).2 rfl)

/-- Primitive coherent data produce all original invariant-transport fields at once. -/
def assemblePresentation (I J : InvariantFamily U) (p : Presentation.{u, v} I J mode) :
    Native I J mode :=
  ⟨p.retained, fun i => transported_of_row p.retained _ _ _
    (p.rows i _ ((p.retained.index_point_iff i _).2 rfl))⟩

/-- Read a native existence proof through candidate point graphs, using no extra data for predicates. -/
def readRow {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (source target : Invariant U)
    (ht : Invariant.TransportedAlong source target id r.objectMap) :
    IndependentInverseGraph.Table.{u, u} :=
  match source, target with
  | .function F, .function G => IndependentInverseGraph.read F.Value G.Value (Classical.choose ht)
  | .predicate _, .predicate _ => fun _ => false
  | .function _, .predicate _ => False.elim ht
  | .predicate _, .function _ => False.elim ht

/-- Each original transport proof supplies all point rules for its own kind. -/
theorem readRow_law {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (source target : Invariant U)
    (ht : Invariant.TransportedAlong source target id r.objectMap) :
    RowLaw source target r.table (readRow r source target ht) := by
  cases source with
  | function F =>
      cases target with
      | function G =>
          refine ⟨IndependentInverseGraph.read_isLawful _ _ _, ?_⟩
          intro A B hAB
          change ∃ e : F.Value ≃ G.Value, ∀ A, e (F.evaluate A) = G.evaluate (r.objectMap A) at ht
          change IndependentCarrierGraph.read F.Value G.Value (Classical.choose ht : F.Value ≃ G.Value)
            (.edge F.Value G.Value (F.evaluate A) (G.evaluate B)) = true
          apply (IndependentCarrierGraph.read_edge _ _ _ _ _).2
          rw [← (r.object_point_iff A B).1 hAB]
          exact Classical.choose_spec ht A
      | predicate Q => exact False.elim ht
  | predicate P =>
      cases target with
      | function G => exact False.elim ht
      | predicate Q =>
          intro A B hAB
          rw [← (r.object_point_iff A B).1 hAB]
          exact ht A

/-- A predicate in either native position forces every auxiliary point to be false. -/
theorem readRow_inactive {I J : InvariantFamily U} (r : Retained.{u, v} I J mode)
    (source target : Invariant U)
    (ht : Invariant.TransportedAlong source target id r.objectMap)
    (h : isFunction source = false ∨ isFunction target = false)
    (q : IndependentInverseGraph.Query.{u, u}) : readRow r source target ht q = false := by
  cases source <;> cases target
  · simp [isFunction] at h
  · exact False.elim ht
  · exact False.elim ht
  · rfl

/-- Read native witness points only at the selected index pair; all others are inactive. -/
def readAux (I J : InvariantFamily U) (f : Native.{u, v} I J mode) : Table.{u} := by
  classical
  intro q
  cases q with
  | row M N i j q =>
      exact if hM : M = I.Index then if hN : N = J.Index then
        if hij : f.val.indexMap (hM ▸ i) = (hN ▸ j) then
          readRow f.val (I.invariant (hM ▸ i)) (J.invariant (hN ▸ j))
            (by rw [← hij]; exact f.property (hM ▸ i)) q
        else false
      else false else false

/-- An active selected index pair recovers exactly its native witness row. -/
theorem readAux_row (I J : InvariantFamily U) (f : Native.{u, v} I J mode)
    (i : I.Index) (j : J.Index) (hij : f.val.indexMap i = j) :
    row (readAux I J f) I.Index J.Index i j =
      readRow f.val (I.invariant i) (J.invariant j)
        (by rw [← hij]; exact f.property i) := by
  subst j
  funext q
  simp [row, readAux]

/-- Native reading enforces all candidate and kind inactivity rules. -/
theorem readAux_isTyped (I J : InvariantFamily U) (f : Native.{u, v} I J mode) :
    IsAuxTyped I J f.val (readAux I J f) := by
  classical
  constructor
  · intro M N i j q hn
    rcases hn with hM | hN
    · simp [readAux, hM]
    · by_cases hM : M = I.Index
      · simp [readAux, hM, hN]
      · simp [readAux, hM]
  · intro i j q hn
    by_cases hij : f.val.indexMap i = j
    · have hpoint := (f.val.index_point_iff i j).2 hij
      have hk : isFunction (I.invariant i) = false ∨ isFunction (J.invariant j) = false := by
        rcases hn with hn | hn
        · exact False.elim (Bool.noConfusion (hn.symm.trans hpoint))
        · exact hn
      change row (readAux I J f) I.Index J.Index i j q = false
      rw [readAux_row I J f i j hij]
      exact readRow_inactive _ _ _ _ hk q
    · simp [readAux, hij]

/-- Read every original invariant family transport into one coherent primitive presentation. -/
def readPresentation (I J : InvariantFamily U) (f : Native.{u, v} I J mode) :
    Presentation I J mode where
  retained := f.val
  auxiliary := TagChange.read (readAux I J f)
  auxiliaryTyped := by
    rw [TagChange.assemble_read]
    exact readAux_isTyped I J f
  rows := by
    intro i j hij
    rw [TagChange.assemble_read, readAux_row I J f i j ((f.val.index_point_iff i j).1 hij)]
    exact readRow_law _ _ _ _

/-- Reading and assembly recover every retained computational field of the original data. -/
theorem assemble_readPresentation (I J : InvariantFamily U) (f : Native.{u, v} I J mode) :
    assemblePresentation I J (readPresentation I J f) = f := Subtype.ext rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.InvariantWitness
