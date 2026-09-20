import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.Ring.Ext
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.ULift
import Formal.Util.AssertStandardAxioms

/-!
# Primitive commutative-ring readings for independent G-124 verification

The carrier is a declared type reference. Each response is one native constant
or one unary/binary operation evaluation. Seven equations construct the native
commutative-ring structure, including its derived operations. Ring structure
extensionality proves that no choices of the derived operations are lost.
The same point interface assembles arbitrary, possibly noninvertible ring homs.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRingPrimitive

universe u v w

/-- Primitive operation queries on a declared coefficient or observable carrier. -/
inductive Query (K : Type u) where
  /-- Read the additive identity. -/
  | zero
  /-- Read the multiplicative identity. -/
  | one
  /-- Read the sum of one pair. -/
  | add (a b : K)
  /-- Read the product of one pair. -/
  | mul (a b : K)
  /-- Read the additive inverse of one element. -/
  | neg (a : K)

/-- One ring element is returned per primitive query. -/
abbrev Table (K : Type u) := Query K → K

variable {K : Type u}

/-- Independent equations on the primitive operation values. -/
structure IsLawful (t : Table K) : Prop where
  /-- Addition is associative at every triple. -/
  add_assoc : ∀ a b c, t (.add (t (.add a b)) c) = t (.add a (t (.add b c)))
  /-- The selected zero is a left additive identity. -/
  zero_add : ∀ a, t (.add (t .zero) a) = a
  /-- The selected negation is a left additive inverse. -/
  neg_add_cancel : ∀ a, t (.add (t (.neg a)) a) = t .zero
  /-- Multiplication is associative at every triple. -/
  mul_assoc : ∀ a b c, t (.mul (t (.mul a b)) c) = t (.mul a (t (.mul b c)))
  /-- Multiplication commutes at every pair. -/
  mul_comm : ∀ a b, t (.mul a b) = t (.mul b a)
  /-- The selected one is a left multiplicative identity. -/
  one_mul : ∀ a, t (.mul (t .one) a) = a
  /-- Left multiplication distributes over addition at every triple. -/
  left_distrib : ∀ a b c,
    t (.mul a (t (.add b c))) = t (.add (t (.mul a b)) (t (.mul a c)))

/-- Build the whole native ring from its five primitive operation readings. -/
def assemble (t : Table K) (ht : IsLawful t) : CommRing K :=
  letI : Add K := ⟨fun a b => t (.add a b)⟩
  letI : Mul K := ⟨fun a b => t (.mul a b)⟩
  letI : Neg K := ⟨fun a => t (.neg a)⟩
  letI : Zero K := ⟨t .zero⟩
  letI : One K := ⟨t .one⟩
  CommRing.ofMinimalAxioms ht.add_assoc ht.zero_add ht.neg_add_cancel
    ht.mul_assoc ht.mul_comm ht.one_mul ht.left_distrib

/-- Read a native ring's operations one application at a time. -/
def read (R : CommRing K) : Table K :=
  letI := R
  fun q => match q with
    | .zero => 0
    | .one => 1
    | .add a b => a + b
    | .mul a b => a * b
    | .neg a => -a

/-- Every native commutative ring satisfies the independent primitive equations. -/
theorem read_isLawful (R : CommRing K) : IsLawful (read R) := by
  letI := R
  exact ⟨add_assoc, zero_add, neg_add_cancel, mul_assoc, mul_comm, one_mul, mul_add⟩

/-- Native extensionality recovers all derived ring operations as well as the primitive ones. -/
theorem assemble_read (R : CommRing K) : assemble (read R) (read_isLawful R) = R := by
  apply CommRing.ext <;> rfl

/-- Reading an assembled ring recovers every primitive value. -/
theorem read_assemble (t : Table K) (ht : IsLawful t) : read (assemble t ht) = t := by
  funext q
  cases q <;> rfl

/-- Equal primitive tables assemble to the same ring, independently of their law proofs. -/
theorem assemble_congr {t s : Table K} (ht : IsLawful t) (hs : IsLawful s) (h : t = s) :
    assemble t ht = assemble s hs := by
  cases h
  rfl

/-- All native ring structures on the declared carrier correspond to lawful primitive tables. -/
def readingEquiv : CommRing K ≃ {t : Table K // IsLawful t} where
  toFun R := ⟨read R, read_isLawful R⟩
  invFun t := assemble t.val t.property
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property)

/-- Change every multiplication result to the selected zero, leaving other readings intact. -/
def eraseMultiplication (t : Table K) : Table K
  | .mul _ _ => t .zero
  | q => t q

/-- Destroying multiplication in a nontrivial ring is rejected by the primitive unit equation. -/
theorem eraseMultiplication_not_lawful [Nontrivial K] (R : CommRing K) :
    ¬ IsLawful (eraseMultiplication (read R)) := by
  letI := R
  intro h
  have hz : (0 : K) = 1 := h.one_mul (1 : K)
  exact zero_ne_one hz

namespace Hom

variable {L : Type v} {M : Type w} [CommRing K] [CommRing L] [CommRing M]

/-- Native ring-hom equations imposed on individual input and output values. -/
structure IsLawful (t : K → L) : Prop where
  /-- The zero point is preserved. -/
  zero : t 0 = 0
  /-- The one point is preserved. -/
  one : t 1 = 1
  /-- Every addition evaluation is preserved. -/
  add : ∀ a b, t (a + b) = t a + t b
  /-- Every multiplication evaluation is preserved. -/
  mul : ∀ a b, t (a * b) = t a * t b

/-- Collect lawful point values into the native ring homomorphism. -/
def assemble (t : K → L) (ht : IsLawful t) : K →+* L where
  toFun := t
  map_zero' := ht.zero
  map_one' := ht.one
  map_add' := ht.add
  map_mul' := ht.mul

/-- A native hom provides the primitive preservation equations at every input. -/
theorem read_isLawful (f : K →+* L) : IsLawful (fun x => f x) :=
  ⟨f.map_zero, f.map_one, f.map_add, f.map_mul⟩

/-- Native ring homomorphisms are recovered by assembling their point values. -/
theorem assemble_read (f : K →+* L) : assemble (fun x => f x) (read_isLawful f) = f := by
  ext x
  rfl

/-- A lawful point family is recovered at every input after hom assembly. -/
theorem read_assemble (t : K → L) (ht : IsLawful t) :
    (fun x => assemble t ht x) = t := rfl

/-- Every native ring hom, including noninvertible ones, has a unique lawful point family. -/
def readingEquiv : (K →+* L) ≃ {t : K → L // IsLawful t} where
  toFun f := ⟨fun x => f x, read_isLawful f⟩
  invFun t := assemble t.val t.property
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property)

/-- Identity point values obey all primitive hom equations. -/
theorem id_isLawful : IsLawful (fun x : K => x) := ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Componentwise composition of lawful point families obeys the primitive equations. -/
theorem comp_isLawful (f : K → L) (hf : IsLawful f) (g : L → M) (hg : IsLawful g) :
    IsLawful (g ∘ f) where
  zero := by simp [hf.zero, hg.zero]
  one := by simp [hf.one, hg.one]
  add a b := by simp [hf.add, hg.add]
  mul a b := by simp [hf.mul, hg.mul]

/-- Pointwise identity assembles to the native identity hom. -/
theorem assemble_id : assemble (fun x : K => x) id_isLawful = RingHom.id K := by
  ext x
  rfl

/-- Pointwise composition assembles in the native hom-composition order. -/
theorem assemble_comp (f : K → L) (hf : IsLawful f) (g : L → M) (hg : IsLawful g) :
    assemble (g ∘ f) (comp_isLawful f hf g hg) = (assemble g hg).comp (assemble f hf) := by
  ext x
  rfl

end Hom

namespace Carrier

/-- A native commutative ring whose carrier may vary with the represented object. -/
abbrev Native := (K : Type u) × CommRing K

/-- Carrier-independent queries for the selected type and primitive ring evaluations. -/
inductive Query where
  /-- Select the native carrier type. -/
  | carrier
  /-- Read one primitive ring operation on a candidate carrier. -/
  | operation (K : Type u) (q : IndependentRingPrimitive.Query K)

/-- A variable-carrier response contains only a type reference or one element. -/
def Query.Value : Query.{u} → Type (u + 1)
  | .carrier => Type u
  | .operation K _ => ULift.{u + 1} (Option K)

/-- A variable-carrier primitive ring table. -/
abbrev Table := (q : Query.{u}) → q.Value

/-- The selected carrier is one primitive type-reference response. -/
abbrev carrier (t : Table.{u}) : Type u := t .carrier

/-- Exactly the selected carrier has active ring-operation values. -/
def IsTyped (t : Table.{u}) : Prop :=
  ∀ K (q : IndependentRingPrimitive.Query K),
    (t (.operation K q)).down.isSome ↔ K = carrier t

/-- Collect operation values on the chosen carrier into the fixed-carrier primitive table. -/
def active (t : Table.{u}) (ht : IsTyped t) : IndependentRingPrimitive.Table (carrier t) :=
  fun q => (t (.operation _ q)).down.get ((ht _ q).2 rfl)

/-- The local ring equations are the seven primitive equations on active values. -/
def IsLawful (t : Table.{u}) (ht : IsTyped t) : Prop :=
  IndependentRingPrimitive.IsLawful (active t ht)

/-- Construct both the native carrier and its complete commutative-ring structure. -/
def assemble (t : Table.{u}) (ht : IsTyped t) (hl : IsLawful t ht) : Native.{u} :=
  ⟨carrier t, IndependentRingPrimitive.assemble (active t ht) hl⟩

/-- Read a variable-carrier ring using only named primitive operation applications. -/
noncomputable def read (R : Native.{u}) : Table.{u} := by
  classical
  intro q
  cases q with
  | carrier => exact R.1
  | operation K q =>
    exact ⟨if h : K = R.1 then
      some (h.symm ▸ IndependentRingPrimitive.read R.2 (h ▸ q)) else none⟩

/-- Native variable-carrier rings satisfy the exact candidate activation rule. -/
theorem read_isTyped (R : Native.{u}) : IsTyped (read R) := by
  classical
  intro K q
  by_cases h : K = R.1 <;> simp [read, carrier, h]

/-- Active values are exactly the fixed-carrier reading of the native ring. -/
theorem active_read (R : Native.{u}) :
    active (read R) (read_isTyped R) = IndependentRingPrimitive.read R.2 := by
  funext q
  simp [active, read, carrier]

/-- The native ring laws generate all seven equations of the variable-carrier table. -/
theorem read_isLawful (R : Native.{u}) : IsLawful (read R) (read_isTyped R) := by
  unfold IsLawful
  rw [active_read]
  exact IndependentRingPrimitive.read_isLawful R.2

/-- Variable-carrier assembly recovers the carrier and the full native ring structure. -/
theorem assemble_read (R : Native.{u}) :
    assemble (read R) (read_isTyped R) (read_isLawful R) = R := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    change IndependentRingPrimitive.assemble (active (read R) (read_isTyped R))
      (read_isLawful R) = R.2
    exact (IndependentRingPrimitive.assemble_congr
      (read_isLawful R) (IndependentRingPrimitive.read_isLawful R.2) (active_read R)).trans
      (IndependentRingPrimitive.assemble_read R.2)

/-- Reading a variable-carrier assembly restores active and inactive operation responses. -/
theorem read_assemble (t : Table.{u}) (ht : IsTyped t) (hl : IsLawful t ht) :
    read (assemble t ht hl) = t := by
  classical
  funext q
  cases q with
  | carrier => rfl
  | operation K q =>
    apply ULift.ext
    by_cases hK : K = carrier t
    · subst K
      simp [read, assemble, IndependentRingPrimitive.read_assemble, active, Option.some_get]
    · have hn : (t (.operation K q)).down = none := by
        cases ho : (t (.operation K q)).down with
        | none => rfl
        | some x => exact False.elim (hK ((ht K q).1 (by simp [ho])))
      simp [read, assemble, hK, hn]

/-- All native commutative rings, with arbitrary carriers, correspond to primitive lawful tables. -/
noncomputable def readingEquiv :
    Native.{u} ≃ {t : Table.{u} // ∃ ht : IsTyped t, IsLawful t ht} where
  toFun R := ⟨read R, read_isTyped R, read_isLawful R⟩
  invFun t := assemble t.val t.property.choose t.property.choose_spec
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property.choose t.property.choose_spec)

end Carrier

end AAT.AG.LocalSemanticReconstruction.IndependentRingPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRingPrimitive
