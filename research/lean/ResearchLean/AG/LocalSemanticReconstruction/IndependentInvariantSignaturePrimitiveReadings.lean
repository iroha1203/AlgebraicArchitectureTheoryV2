import Formal.AG.Atom.ObjectAlgebra
import Formal.Util.AssertStandardAxioms

/-!
# Primitive invariant and signature readings

The declarations retain native index roles, value carriers, tags, and point
evaluations. Whole signatures and invariant families are outputs of assembly.
Candidate carriers are independent of a selected native reading; inactive
responses are unique, so aliases and proof choices add no object data.

## Implementation notes

Kind tags retain the native distinction between function and predicate
invariants. Carrier guards let all native value types vary while forcing
unselected candidates to one inactive response. Storing a whole invariant,
signature, or evaluation function in a cell would omit the pointwise reading
obligation, so assembly collects the individual responses instead.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentInvariantSignaturePrimitive

universe u

variable {U : AtomCarrier.{u}}

/-- An inactive optional response is uniquely absent. -/
theorem option_none {T : Type u} (x : Option T) (h : ¬ x.isSome) : x = none := by
  cases x <;> simp_all

namespace Signature

/-- The four primitive roles of an architecture signature. -/
inductive Query (U : AtomCarrier.{u}) where
  /-- Select the axis carrier. -/
  | axis
  /-- Select one dependent coordinate carrier. -/
  | coordinateType (I : Type u) (i : I)
  /-- Read axis selection at one candidate axis. -/
  | selected (I : Type u) (i : I)
  /-- Read one object coordinate at one candidate axis and carrier. -/
  | coordinate (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U)

/-- Responses are carrier references, predicates, and single coordinate values. -/
def Query.Value : Query U → Type (u + 1)
  | .axis => Type u
  | .coordinateType _ _ => Option (Type u)
  | .selected _ _ => ULift.{u + 1} Prop
  | .coordinate _ _ K _ => ULift.{u + 1} (Option K)

/-- The dependent primitive signature table. -/
abbrev Table (U : AtomCarrier.{u}) := (q : Query U) → q.Value

/-- The selected axis carrier. -/
abbrev axis (t : Table U) : Type u := t .axis

/-- Exact activation and unique inactive predicate responses. -/
structure IsTyped (t : Table U) : Prop where
  /-- Coordinate type references occur exactly on the axis carrier. -/
  coordinateType : ∀ I i, (t (.coordinateType I i)).isSome ↔ I = axis t
  /-- An inactive axis cannot be selected. -/
  selected : ∀ I i, I ≠ axis t → ¬ (t (.selected I i)).down
  /-- Coordinate values are active exactly on the declared coordinate carrier. -/
  coordinate : ∀ I i K B, (t (.coordinate I i K B)).down.isSome ↔
    t (.coordinateType I i) = some K

/-- Collect the dependent coordinate carrier at a selected axis. -/
def coordinateType (t : Table U) (ht : IsTyped t) (i : axis t) : Type u :=
  (t (.coordinateType _ i)).get ((ht.coordinateType _ i).2 rfl)

/-- The active coordinate-type response is its collected carrier. -/
theorem coordinateType_some (t : Table U) (ht : IsTyped t) (i : axis t) :
    t (.coordinateType _ i) = some (coordinateType t ht i) :=
  (Option.some_get _).symm

/-- Collect a single coordinate value. -/
def coordinate (t : Table U) (ht : IsTyped t) (B : ArchitectureObject U) (i : axis t) :
    coordinateType t ht i :=
  (t (.coordinate _ i _ B)).down.get ((ht.coordinate _ i _ B).2 (coordinateType_some t ht i))

/-- Construct the native signature after collecting its dependent point values. -/
def assemble (t : Table U) (ht : IsTyped t) : ArchitectureSignature U where
  Axis := axis t
  Coordinate := coordinateType t ht
  selected i := (t (.selected _ i)).down
  coordinate := coordinate t ht

/-- Read all primitive fields with fixed inactive responses. -/
noncomputable def read (S : ArchitectureSignature U) : Table U := by
  classical
  intro q
  cases q with
  | axis => exact S.Axis
  | coordinateType I i => exact if h : I = S.Axis then some (S.Coordinate (h ▸ i)) else none
  | selected I i => exact ⟨if h : I = S.Axis then S.selected (h ▸ i) else False⟩
  | coordinate I i K B => exact ⟨if h : I = S.Axis then
      if hK : K = S.Coordinate (h ▸ i) then some (hK.symm ▸ S.coordinate B (h ▸ i)) else none
    else none⟩

/-- Native signature readings satisfy all carrier activation conditions. -/
theorem read_isTyped (S : ArchitectureSignature U) : IsTyped (read S) where
  coordinateType I i := by
    classical
    by_cases h : I = S.Axis <;> simp [read, axis, h]
  selected I i h := by
    change I ≠ S.Axis at h
    simp [read, h]
  coordinate I i K B := by
    classical
    by_cases h : I = S.Axis
    · subst I
      by_cases hK : K = S.Coordinate i
      · simp [read, hK]
      · simp [read, hK, eq_comm]
        exact fun he => hK (Option.some.inj he)
    · simp [read, h]

/-- Collected native coordinate carriers agree exactly. -/
theorem coordinateType_read (S : ArchitectureSignature U) (i : S.Axis) :
    coordinateType (read S) (read_isTyped S) i = S.Coordinate i := by
  simp [coordinateType, read, axis]

/-- All dependent native signature fields determine the signature. -/
theorem signature_ext {S T : ArchitectureSignature U} (ha : S.Axis = T.Axis)
    (hc : HEq S.Coordinate T.Coordinate) (hs : HEq S.selected T.selected)
    (hv : HEq S.coordinate T.coordinate) : S = T := by
  cases S
  cases T
  cases ha
  cases hc
  cases hs
  cases hv
  rfl

/-- Native signatures are recovered including their dependent coordinate evaluations. -/
theorem assemble_read (S : ArchitectureSignature U) : assemble (read S) (read_isTyped S) = S := by
  apply signature_ext (S := assemble (read S) (read_isTyped S)) (T := S) rfl
  · exact heq_of_eq (funext (coordinateType_read S))
  · apply heq_of_eq
    funext i
    simp [assemble, read]
  · change HEq (coordinate (read S) (read_isTyped S)) S.coordinate
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro i i' hi
    cases hi
    simp [coordinate, coordinateType, read, axis]

/-- Read-after-assemble recovers both active and inactive signature cells. -/
theorem read_assemble (t : Table U) (ht : IsTyped t) : read (assemble t ht) = t := by
  classical
  funext q
  cases q with
  | axis => rfl
  | coordinateType I i =>
    by_cases h : I = axis t
    · subst I
      simp [read, assemble, coordinateType, Option.some_get]
    · have hn := option_none _ (mt (ht.coordinateType I i).1 h)
      simp [read, assemble, h, hn]
  | selected I i =>
    apply ULift.ext
    by_cases h : I = axis t
    · subst I
      simp [read, assemble]
    · simp [read, assemble, h, ht.selected I i h]
  | coordinate I i K B =>
    apply ULift.ext
    by_cases h : I = axis t
    · subst I
      by_cases hK : K = coordinateType t ht i
      · subst K
        simp [read, assemble, coordinate, Option.some_get]
      · have hn := option_none _ (fun hx => hK (by
          have he := (ht.coordinate _ i K B).1 hx
          rw [coordinateType_some t ht i] at he
          exact (Option.some.inj he).symm))
        simp [read, assemble, hK, hn]
    · have hn := option_none _ (fun hx => h ((ht.coordinateType I i).1 (by
          rw [(ht.coordinate I i K B).1 hx]
          rfl)))
      simp [read, assemble, h, hn]

/-- Complete native signatures correspond to exactly typed primitive point tables. -/
noncomputable def readingEquiv : ArchitectureSignature U ≃ {t : Table U // IsTyped t} where
  toFun S := ⟨read S, read_isTyped S⟩
  invFun t := assemble t.val t.property
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property)

/-- Primitive signature readings separate all native fields. -/
theorem read_injective : Function.Injective (read (U := U)) := by
  intro S T h
  apply (readingEquiv (U := U)).injective
  exact Subtype.ext h

/-- Delete coordinate responses without changing their carrier declarations. -/
def eraseCoordinates (t : Table U) : Table U
  | .coordinate _ _ _ _ => ⟨none⟩
  | q => t q

/-- A declared coordinate cannot lose its required point value. -/
theorem eraseCoordinates_not_typed (S : ArchitectureSignature U) (i : S.Axis)
    (B : ArchitectureObject U) : ¬ IsTyped (eraseCoordinates (read S)) := by
  intro ht
  have h := (ht.coordinate S.Axis i (S.Coordinate i) B).2 (by simp [eraseCoordinates, read])
  simp [eraseCoordinates] at h

end Signature

namespace Invariants

/-- Native invariant kinds with a carrier reference for function-valued readings. -/
inductive Kind where
  /-- A function-valued invariant uses this raw value carrier. -/
  | function (K : Type u)
  /-- A predicate-valued invariant has no value carrier. -/
  | predicate

/-- Primitive invariant-family query roles. -/
inductive Query (U : AtomCarrier.{u}) where
  /-- Select the index carrier. -/
  | index
  /-- Read the kind and optional value-carrier reference at one index. -/
  | kind (I : Type u) (i : I)
  /-- Read one function-invariant value on one object. -/
  | value (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U)
  /-- Read one predicate-invariant value on one object. -/
  | predicate (I : Type u) (i : I) (B : ArchitectureObject U)

/-- Invariant responses contain no complete invariant or evaluation function. -/
def Query.Value : Query U → Type (u + 1)
  | .index => Type u
  | .kind _ _ => Option Kind.{u}
  | .value _ _ K _ => ULift.{u + 1} (Option K)
  | .predicate _ _ _ => ULift.{u + 1} Prop

/-- Dependent table of invariant primitives. -/
abbrev Table (U : AtomCarrier.{u}) := (q : Query U) → q.Value

/-- The invariant index type chosen by its dedicated query. -/
abbrev index (t : Table U) : Type u := t .index

/-- Index, tag, and carrier activation; inactive predicate responses are false. -/
structure IsTyped (t : Table U) : Prop where
  /-- Every selected index has exactly one invariant kind. -/
  kind : ∀ I i, (t (.kind I i)).isSome ↔ I = index t
  /-- Function values are active exactly at the selected function-value carrier. -/
  value : ∀ I i K B, (t (.value I i K B)).down.isSome ↔
    t (.kind I i) = some (.function K)
  /-- Only predicate-tagged indices can have a true predicate response. -/
  predicate : ∀ I i B, t (.kind I i) ≠ some .predicate → ¬ (t (.predicate I i B)).down

/-- Collect the native kind of an active invariant. -/
def kind (t : Table U) (ht : IsTyped t) (i : index t) : Kind.{u} :=
  (t (.kind _ i)).get ((ht.kind _ i).2 rfl)

/-- The selected kind is exactly the active table response. -/
theorem kind_some (t : Table U) (ht : IsTyped t) (i : index t) :
    t (.kind _ i) = some (kind t ht i) := (Option.some_get _).symm

/-- Collect a value after establishing its function tag and carrier. -/
def value (t : Table U) (ht : IsTyped t) (i : index t) (K : Type u)
    (hk : kind t ht i = .function K) (B : ArchitectureObject U) : K :=
  (t (.value _ i K B)).down.get ((ht.value _ i K B).2 (by rw [kind_some t ht i, hk]))

/-- Assemble the native invariant at a single index from point responses. -/
def invariant (t : Table U) (ht : IsTyped t) (i : index t) : Invariant U :=
  match hk : kind t ht i with
  | .function K => .function ⟨K, value t ht i K hk⟩
  | .predicate => .predicate ⟨fun B => (t (.predicate _ i B)).down⟩

/-- Function-tagged assembly uses exactly the selected carrier and its point family. -/
theorem invariant_function (t : Table U) (ht : IsTyped t) (i : index t) (K : Type u)
    (hk : kind t ht i = .function K) :
    invariant t ht i = .function ⟨K, value t ht i K hk⟩ := by
  unfold invariant
  split
  next L hL =>
    have he : L = K := Kind.function.inj (hL.symm.trans hk)
    subst L
    rfl
  next hP => cases hP.symm.trans hk

/-- Predicate-tagged assembly uses exactly the predicate's point family. -/
theorem invariant_predicate (t : Table U) (ht : IsTyped t) (i : index t)
    (hk : kind t ht i = .predicate) :
    invariant t ht i = .predicate ⟨fun B => (t (.predicate _ i B)).down⟩ := by
  unfold invariant
  split
  next K hK => cases hK.symm.trans hk
  next => rfl

/-- Construct the full native invariant family. -/
def assemble (t : Table U) (ht : IsTyped t) : InvariantFamily U :=
  ⟨index t, invariant t ht⟩

/-- Read each primitive native field at its original role and arguments. -/
noncomputable def read (R : InvariantFamily U) : Table U := by
  classical
  intro q
  cases q with
  | index => exact R.Index
  | kind I i => exact if h : I = R.Index then some (match R.invariant (h ▸ i) with
      | .function F => .function F.Value
      | .predicate _ => .predicate) else none
  | value I i K B => exact ⟨if h : I = R.Index then match R.invariant (h ▸ i) with
      | .function F => if hK : K = F.Value then some (hK.symm ▸ F.evaluate B) else none
      | .predicate _ => none
    else none⟩
  | predicate I i B => exact ⟨if h : I = R.Index then match R.invariant (h ▸ i) with
      | .function _ => False
      | .predicate P => P.holds B
    else False⟩

/-- Native tags and carrier references enforce all activation rules. -/
theorem read_isTyped (R : InvariantFamily U) : IsTyped (read R) where
  kind I i := by
    classical
    by_cases h : I = R.Index <;> simp [read, index, h]
  value I i K B := by
    classical
    by_cases h : I = R.Index
    · subst I
      cases he : R.invariant i with
      | function F =>
        by_cases hK : K = F.Value
        · simp [read, he, hK]
        · simp [read, he, hK, eq_comm]
          exact fun h => hK (Kind.function.inj (Option.some.inj h))
      | predicate P =>
        simp [read, he]
        intro h
        cases Option.some.inj h
    · simp [read, h]
  predicate I i B hn := by
    classical
    by_cases h : I = R.Index
    · subst I
      cases he : R.invariant i <;> simp_all [read]
    · simp [read, h]

/-- Each native invariant is recovered with its actual dependent value type. -/
theorem invariant_read (R : InvariantFamily U) (i : R.Index) :
    invariant (read R) (read_isTyped R) i = R.invariant i := by
  cases he : R.invariant i with
  | function F =>
    have hk : kind (read R) (read_isTyped R) i = .function F.Value := by
      simp [kind, read, index, he]
    rw [invariant_function _ _ _ _ hk]
    congr
    funext B
    simp [value, read, index, he]
  | predicate P =>
    have hk : kind (read R) (read_isTyped R) i = .predicate := by
      simp [kind, read, index, he]
    rw [invariant_predicate _ _ _ hk]
    simp [read, index, he]

/-- Native families are determined by their index type and dependent invariant family. -/
theorem family_ext {R S : InvariantFamily U} (hi : R.Index = S.Index)
    (hf : HEq R.invariant S.invariant) : R = S := by
  cases R
  cases S
  cases hi
  cases hf
  rfl

/-- Assemble-after-read recovers every native invariant family. -/
theorem assemble_read (R : InvariantFamily U) : assemble (read R) (read_isTyped R) = R := by
  apply family_ext (R := assemble (read R) (read_isTyped R)) (S := R) rfl
  exact heq_of_eq (funext (invariant_read R))

/-- Wrong-tag or wrong-carrier values are uniquely inactive. -/
theorem value_none (t : Table U) (ht : IsTyped t) (I : Type u) (i : I)
    (K : Type u) (B : ArchitectureObject U) (h : t (.kind I i) ≠ some (.function K)) :
    (t (.value I i K B)).down = none := option_none _ (mt (ht.value I i K B).1 h)

/-- Reading assembled invariants restores all cells, including the unselected kind. -/
theorem read_assemble (t : Table U) (ht : IsTyped t) : read (assemble t ht) = t := by
  classical
  funext q
  cases q with
  | index => rfl
  | kind I i =>
    by_cases h : I = index t
    · subst I
      cases hk : kind t ht i with
      | function K => simp [read, assemble, invariant_function t ht i K hk, kind_some t ht i, hk]
      | predicate => simp [read, assemble, invariant_predicate t ht i hk, kind_some t ht i, hk]
    · have hn := option_none _ (mt (ht.kind I i).1 h)
      simp [read, assemble, h, hn]
  | value I i K B =>
    apply ULift.ext
    by_cases h : I = index t
    · subst I
      cases hk : kind t ht i with
      | function L =>
        by_cases hK : K = L
        · subst K
          simp [read, assemble, invariant_function t ht i L hk, value, Option.some_get]
        · have hn := value_none t ht _ i K B (by
            rw [kind_some t ht i, hk]
            exact fun he => hK (Kind.function.inj (Option.some.inj he)).symm)
          simp [read, assemble, invariant_function t ht i L hk, hK, hn]
      | predicate =>
        have hn := value_none t ht _ i K B (by
          rw [kind_some t ht i, hk]
          intro he
          cases Option.some.inj he)
        simp [read, assemble, invariant_predicate t ht i hk, hn]
    · have hi := option_none _ (mt (ht.kind I i).1 h)
      have hn := value_none t ht I i K B (by simp [hi])
      simp [read, assemble, h, hn]
  | predicate I i B =>
    apply ULift.ext
    by_cases h : I = index t
    · subst I
      cases hk : kind t ht i with
      | function K =>
        have hn := ht.predicate _ i B (by
          rw [kind_some t ht i, hk]
          intro he
          cases Option.some.inj he)
        simp [read, assemble, invariant_function t ht i K hk, hn]
      | predicate => simp [read, assemble, invariant_predicate t ht i hk]
    · have hi := option_none _ (mt (ht.kind I i).1 h)
      have hn := ht.predicate I i B (by simp [hi])
      simp [read, assemble, h, hn]

/-- All native invariant families correspond to exactly typed primitive point tables. -/
noncomputable def readingEquiv : InvariantFamily U ≃ {t : Table U // IsTyped t} where
  toFun R := ⟨read R, read_isTyped R⟩
  invFun t := assemble t.val t.property
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property)

/-- Primitive invariant readings separate kinds, carriers, and all point evaluations. -/
theorem read_injective : Function.Injective (read (U := U)) := by
  intro R S h
  apply (readingEquiv (U := U)).injective
  exact Subtype.ext h

/-- Delete function values while retaining index and kind declarations. -/
def eraseFunctionValues (t : Table U) : Table U
  | .value _ _ _ _ => ⟨none⟩
  | q => t q

/-- A function-tagged invariant must return its declared value at each object. -/
theorem eraseFunctionValues_not_typed (R : InvariantFamily U) (i : R.Index)
    (F : FunctionInvariant U) (hf : R.invariant i = .function F) (B : ArchitectureObject U) :
    ¬ IsTyped (eraseFunctionValues (read R)) := by
  intro ht
  have h := (ht.value R.Index i F.Value B).2 (by simp [eraseFunctionValues, read, hf])
  simp [eraseFunctionValues] at h

end Invariants

end AAT.AG.LocalSemanticReconstruction.IndependentInvariantSignaturePrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentInvariantSignaturePrimitive
