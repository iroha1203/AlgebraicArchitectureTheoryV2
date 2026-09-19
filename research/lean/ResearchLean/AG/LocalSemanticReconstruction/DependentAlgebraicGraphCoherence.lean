import ResearchLean.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Dependent algebraic graph coherence

Cycle 68 of G-124 extends the independent graph presentation from ordinary
equivalences and ring homomorphisms to ring equivalences and indexed families
of equivalences.  Raw graphs remain separate from every algebraic or inverse
law.  Assembly and reading are proved inverse in both directions.

For a fixed index map, a pointwise family is also read as one graph on the
corresponding sigma types.  Equality of that tagged forward graph separates
the whole family code.  The same constructions are connected here, rather
than in a later wrapper, to the coordinate and equation-observable families
of complete geometry reading.

## Implementation notes

`RingEquivGraphData` stores two raw ring-hom graph data values; the four
operation laws in each direction and the two inverse equations live in the
separate proposition `IsRingEquivGraphCode`.  Storing a `RingEquiv` was
rejected because it would make assembly tautological.  The identity on
`Nat × Nat` is a positive fixture, while the noninvertible unital endomorphism
`(a,b) ↦ (a,a)` paired with the identity is a negative fixture.

Indexed codes are families over an arbitrary index function, not only an
index equivalence.  This matches the actual signature-axis map and context
functor object map.  A completed family is never retained: each fiber stores
only its graph code and laws, and its tagged graph is derived by assembly.
Dependent composition, two-sided readback, tagged evaluation, and tagged
separation are provided as the public API.

Context-functor morphism action, restriction naturality, the remaining
support/axis/observable families, and complete geometry-Hom assembly remain
separate obligations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace DependentAlgebraicGraphCoherence

universe u v w x

open CompleteGeometryFunctionGraphSeparation
open G122PrimitiveFunctionGraphReading
open AlgebraicGraphCoherence

/-! ## Ring-equivalence graph codes -/

/-- Raw forward and backward ring-hom graph data. -/
structure RingEquivGraphData (R : Type u) (S : Type v) where
  /-- Raw forward graph. -/
  forward : RingHomGraphData R S
  /-- Raw backward graph. -/
  backward : RingHomGraphData S R

/-- Operation-preservation and mutual-inverse equations for a raw pair of
ring-hom graphs. -/
structure IsRingEquivGraphCode (data : RingEquivGraphData R S)
    [NonAssocSemiring R] [NonAssocSemiring S] : Prop where
  /-- The forward graph preserves the semiring operations. -/
  forward_isRingHom : IsRingHomGraphCode data.forward
  /-- The backward graph preserves the semiring operations. -/
  backward_isRingHom : IsRingHomGraphCode data.backward
  /-- Backward after forward is the identity. -/
  left_inv : Function.LeftInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.backward.graph)
    (PrimitiveFunctionGraph.GraphCode.assemble data.forward.graph)
  /-- Forward after backward is the identity. -/
  right_inv : Function.RightInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.backward.graph)
    (PrimitiveFunctionGraph.GraphCode.assemble data.forward.graph)

/-- Raw bidirectional ring graphs bundled with their separate local law. -/
abbrev RingEquivGraphCode (R : Type u) (S : Type v)
    [NonAssocSemiring R] [NonAssocSemiring S] :=
  { data : RingEquivGraphData R S // IsRingEquivGraphCode data }

namespace RingEquivGraphCode

/-- Forward raw ring-hom data. -/
abbrev forwardData {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : RingHomGraphData R S :=
  code.1.forward

/-- Backward raw ring-hom data. -/
abbrev backwardData {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : RingHomGraphData S R :=
  code.1.backward

/-- Forward ring-hom graph code. -/
def forwardCode {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : RingHomGraphCode R S :=
  ⟨code.forwardData, code.2.forward_isRingHom⟩

/-- Backward ring-hom graph code. -/
def backwardCode {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : RingHomGraphCode S R :=
  ⟨code.backwardData, code.2.backward_isRingHom⟩

/-- Ring-equivalence graph codes are determined by their two raw graphs. -/
@[ext]
theorem ext {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    {first second : RingEquivGraphCode R S}
    (forward : first.forwardData.graph = second.forwardData.graph)
    (backward : first.backwardData.graph = second.backwardData.graph) :
    first = second := by
  apply Subtype.ext
  cases first with
  | mk firstData firstLaw =>
    cases second with
    | mk secondData secondLaw =>
      cases firstData with
      | mk firstForward firstBackward =>
        cases secondData with
        | mk secondForward secondBackward =>
          cases firstForward with
          | mk firstForwardGraph =>
            cases secondForward with
            | mk secondForwardGraph =>
              cases firstBackward with
              | mk firstBackwardGraph =>
                cases secondBackward with
                | mk secondBackwardGraph =>
                  change firstForwardGraph = secondForwardGraph at forward
                  change firstBackwardGraph = secondBackwardGraph at backward
                  cases forward
                  cases backward
                  rfl

/-- Assemble independent bidirectional ring graphs into a ring equivalence. -/
def assemble {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : R ≃+* S where
  toFun := code.forwardCode.assemble
  invFun := code.backwardCode.assemble
  left_inv := code.2.left_inv
  right_inv := code.2.right_inv
  map_mul' := code.forwardCode.map_mul
  map_add' := code.forwardCode.map_add

/-- Evaluation of an assembled ring equivalence uses the forward graph. -/
@[simp]
theorem assemble_apply {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) (value : R) :
    code.assemble value =
      PrimitiveFunctionGraph.GraphCode.assemble code.forwardData.graph value :=
  rfl

/-- Evaluation of the inverse uses the backward graph. -/
@[simp]
theorem assemble_symm_apply {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) (value : S) :
    code.assemble.symm value =
      PrimitiveFunctionGraph.GraphCode.assemble code.backwardData.graph value :=
  rfl

/-- Read a ring equivalence as two raw graphs and independent laws. -/
noncomputable def read {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] (equiv : R ≃+* S) :
    RingEquivGraphCode R S :=
  ⟨{
    forward := { graph := PrimitiveFunctionGraph.GraphCode.read equiv }
    backward := { graph := PrimitiveFunctionGraph.GraphCode.read equiv.symm } }, {
    forward_isRingHom := by
      constructor
      · simp
      · simp
      · intro first second
        simp
      · intro first second
        simp
    backward_isRingHom := by
      constructor
      · simp
      · simp
      · intro first second
        simp
      · intro first second
        simp
    left_inv := by simpa using equiv.left_inv
    right_inv := by simpa using equiv.right_inv }⟩

/-- Reading after assembly recovers both raw graphs. -/
@[simp]
theorem read_assemble {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : read code.assemble = code := by
  apply ext
  · change PrimitiveFunctionGraph.GraphCode.read code.assemble = _
    rw [show (code.assemble : R → S) =
      PrimitiveFunctionGraph.GraphCode.assemble code.forwardData.graph by
        funext value
        exact assemble_apply code value]
    exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · change PrimitiveFunctionGraph.GraphCode.read code.assemble.symm = _
    rw [show (code.assemble.symm : S → R) =
      PrimitiveFunctionGraph.GraphCode.assemble code.backwardData.graph by
        funext value
        exact assemble_symm_apply code value]
    exact PrimitiveFunctionGraph.GraphCode.read_assemble _

/-- Assembly after reading recovers the original ring equivalence. -/
@[simp]
theorem assemble_read {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] (equiv : R ≃+* S) :
    (read equiv).assemble = equiv := by
  apply RingEquiv.ext
  intro value
  simp [read]

/-- Independent ring-equivalence graph codes and actual ring equivalences are
explicitly equivalent. -/
noncomputable def equivRingEquiv {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] :
    RingEquivGraphCode R S ≃ (R ≃+* S) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity ring-equivalence graph code. -/
noncomputable def id (R : Type u) [NonAssocSemiring R] :
    RingEquivGraphCode R R :=
  read (RingEquiv.refl R)

/-- Composition of ring-equivalence graph codes. -/
noncomputable def comp {R : Type u} {S : Type v} {T : Type w}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (first : RingEquivGraphCode R S) (second : RingEquivGraphCode S T) :
    RingEquivGraphCode R T :=
  read (first.assemble.trans second.assemble)

/-- The assembled identity code is the identity ring equivalence. -/
@[simp]
theorem assemble_id (R : Type u) [NonAssocSemiring R] :
    (id R).assemble = RingEquiv.refl R := by
  simp [id]

/-- Assembly preserves ring-equivalence composition. -/
@[simp]
theorem assemble_comp {R : Type u} {S : Type v} {T : Type w}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (first : RingEquivGraphCode R S) (second : RingEquivGraphCode S T) :
    (comp first second).assemble = first.assemble.trans second.assemble := by
  simp [comp]

/-- A leading identity ring-equivalence code is eliminated. -/
@[simp]
theorem id_comp {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : comp (id R) code = code := by
  apply equivRingEquiv.injective
  change (comp (id R) code).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply RingEquiv.ext
  intro value
  rfl

/-- A trailing identity ring-equivalence code is eliminated. -/
@[simp]
theorem comp_id {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingEquivGraphCode R S) : comp code (id S) = code := by
  apply equivRingEquiv.injective
  change (comp code (id S)).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply RingEquiv.ext
  intro value
  rfl

/-- Ring-equivalence graph-code composition reassociates to the right. -/
@[simp]
theorem assoc {R : Type u} {S : Type v} {T : Type w} {V : Type x}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    [NonAssocSemiring V]
    (first : RingEquivGraphCode R S) (second : RingEquivGraphCode S T)
    (third : RingEquivGraphCode T V) :
    comp (comp first second) third = comp first (comp second third) := by
  apply equivRingEquiv.injective
  change (comp (comp first second) third).assemble =
    (comp first (comp second third)).assemble
  rw [assemble_comp, assemble_comp, assemble_comp, assemble_comp]
  apply RingEquiv.ext
  intro value
  rfl

/-- Identity raw data are a positive predicate fixture. -/
noncomputable def natPairIdentityData : RingEquivGraphData (Nat × Nat) (Nat × Nat) where
  forward := { graph := PrimitiveFunctionGraph.GraphCode.id }
  backward := { graph := PrimitiveFunctionGraph.GraphCode.id }

/-- The identity pair satisfies every ring-equivalence graph law. -/
theorem natPairIdentityData_isRingEquivGraphCode :
    IsRingEquivGraphCode natPairIdentityData := by
  constructor
  · constructor <;> simp [natPairIdentityData]
  · constructor <;> simp [natPairIdentityData]
  · intro value
    simp [natPairIdentityData]
  · intro value
    simp [natPairIdentityData]

/-- A noninvertible unital endomorphism of `Nat × Nat`. -/
def natPairDiagonalEndomorphism : (Nat × Nat) →+* (Nat × Nat) where
  toFun := fun value => (value.1, value.1)
  map_zero' := rfl
  map_one' := rfl
  map_add' := by intros; rfl
  map_mul' := by intros; rfl

/-- Negative raw fixture: diagonal forward graph and identity backward graph. -/
noncomputable def natPairDiagonalData :
    RingEquivGraphData (Nat × Nat) (Nat × Nat) where
  forward := {
    graph := PrimitiveFunctionGraph.GraphCode.read
      (natPairDiagonalEndomorphism : (Nat × Nat) → (Nat × Nat)) }
  backward := { graph := PrimitiveFunctionGraph.GraphCode.id }

/-- The diagonal/identity pair fails the left-inverse equation. -/
theorem natPairDiagonalData_not_isRingEquivGraphCode :
    ¬ IsRingEquivGraphCode natPairDiagonalData := by
  intro coherent
  have equality := coherent.left_inv (0, 1)
  simp [natPairDiagonalData, natPairDiagonalEndomorphism] at equality

end RingEquivGraphCode

/-! ## Indexed ordinary equivalence graph families -/

/-- Independent equivalence graph code in every fiber over a fixed index map. -/
abbrev IndexedEquivGraphCode {I : Type u} {J : Type v}
    (indexMap : I → J) (A : I → Type w) (B : J → Type x) :=
  ∀ i, EquivGraphCode (A i) (B (indexMap i))

namespace IndexedEquivGraphCode

/-- Assemble every fiber code pointwise. -/
def assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) :
    ∀ i, A i ≃ B (indexMap i) :=
  fun i => (code i).assemble

/-- Read a family of equivalences pointwise. -/
noncomputable def read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (family : ∀ i, A i ≃ B (indexMap i)) :
    IndexedEquivGraphCode indexMap A B :=
  fun i => EquivGraphCode.read (family i)

/-- Reading after pointwise assembly recovers the whole code family. -/
@[simp]
theorem read_assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) :
    read code.assemble = code := by
  funext i
  exact EquivGraphCode.read_assemble (code i)

/-- Pointwise assembly after reading recovers the whole equivalence family. -/
@[simp]
theorem assemble_read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (family : ∀ i, A i ≃ B (indexMap i)) :
    (read family).assemble = family := by
  funext i
  exact EquivGraphCode.assemble_read (family i)

/-- Indexed graph-code families and actual equivalence families are explicitly
equivalent. -/
noncomputable def equivFamily {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x} :
    IndexedEquivGraphCode indexMap A B ≃
      (∀ i, A i ≃ B (indexMap i)) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- The assembled forward family as one function on sigma types. -/
def taggedFunction {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) :
    (Σ i, A i) → (Σ j, B j) :=
  fun value => ⟨indexMap value.1, code.assemble value.1 value.2⟩

/-- Evaluate the tagged function without unfolding its implementation. -/
@[simp]
theorem taggedFunction_apply {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) (i : I) (value : A i) :
    code.taggedFunction ⟨i, value⟩ =
      ⟨indexMap i, code.assemble i value⟩ :=
  rfl

/-- Read the assembled forward family as one total-functional tagged graph. -/
noncomputable def taggedForward {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) :
    PrimitiveFunctionGraph.GraphCode (Σ i, A i) (Σ j, B j) :=
  PrimitiveFunctionGraph.GraphCode.read code.taggedFunction

/-- Tagged graph assembly evaluates the pointwise equivalence family. -/
@[simp]
theorem assemble_taggedForward {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    (code : IndexedEquivGraphCode indexMap A B) :
    PrimitiveFunctionGraph.GraphCode.assemble code.taggedForward =
      code.taggedFunction :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- The tagged forward graph separates the whole indexed equivalence code. -/
theorem taggedForward_injective {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x} :
    Function.Injective
      (taggedForward : IndexedEquivGraphCode indexMap A B → _) := by
  intro first second equality
  funext i
  apply EquivGraphCode.equivEquiv.injective
  apply Equiv.ext
  intro value
  have functionEquality : first.taggedFunction = second.taggedFunction := by
    rw [← assemble_taggedForward first, ← assemble_taggedForward second,
      equality]
  have pairEquality := congrFun functionEquality ⟨i, value⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp pairEquality).2

/-- Pointwise composition over composed index maps. -/
noncomputable def comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    (first : IndexedEquivGraphCode firstIndex A B)
    (second : IndexedEquivGraphCode secondIndex B C) :
    IndexedEquivGraphCode (secondIndex ∘ firstIndex) A C :=
  fun i => EquivGraphCode.read
    ((first i).assemble.trans (second (firstIndex i)).assemble)

/-- Assembly preserves dependent pointwise composition. -/
@[simp]
theorem assemble_comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    (first : IndexedEquivGraphCode firstIndex A B)
    (second : IndexedEquivGraphCode secondIndex B C) (i : I) :
    (comp first second).assemble i =
      (first i).assemble.trans (second (firstIndex i)).assemble := by
  exact EquivGraphCode.assemble_read _

/-- Tagged forward functions compose in the same order as their index and
fiber maps. -/
theorem taggedFunction_comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    (first : IndexedEquivGraphCode firstIndex A B)
    (second : IndexedEquivGraphCode secondIndex B C) :
    (comp first second).taggedFunction =
      second.taggedFunction ∘ first.taggedFunction := by
  funext value
  cases value with
  | mk i value =>
    simp only [taggedFunction, Function.comp_apply]
    rw [assemble_comp]
    rfl

end IndexedEquivGraphCode

/-! ## Indexed ring-equivalence graph families -/

/-- Independent ring-equivalence graph code in every fiber over a fixed
index map. -/
abbrev IndexedRingEquivGraphCode {I : Type u} {J : Type v}
    (indexMap : I → J) (A : I → Type w) (B : J → Type x)
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)] :=
  ∀ i, RingEquivGraphCode (A i) (B (indexMap i))

namespace IndexedRingEquivGraphCode

/-- Assemble every ring-equivalence fiber code pointwise. -/
def assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) :
    ∀ i, A i ≃+* B (indexMap i) :=
  fun i => (code i).assemble

/-- Read a family of ring equivalences pointwise. -/
noncomputable def read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (family : ∀ i, A i ≃+* B (indexMap i)) :
    IndexedRingEquivGraphCode indexMap A B :=
  fun i => RingEquivGraphCode.read (family i)

/-- Reading after pointwise assembly recovers the whole code family. -/
@[simp]
theorem read_assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) :
    read code.assemble = code := by
  funext i
  exact RingEquivGraphCode.read_assemble (code i)

/-- Pointwise assembly after reading recovers the whole ring-equivalence
family. -/
@[simp]
theorem assemble_read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (family : ∀ i, A i ≃+* B (indexMap i)) :
    (read family).assemble = family := by
  funext i
  exact RingEquivGraphCode.assemble_read (family i)

/-- Indexed ring graph-code families and actual ring-equivalence families are
explicitly equivalent. -/
noncomputable def equivFamily {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)] :
    IndexedRingEquivGraphCode indexMap A B ≃
      (∀ i, A i ≃+* B (indexMap i)) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- The assembled forward ring-equivalence family as one function on sigma
types. -/
def taggedFunction {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) :
    (Σ i, A i) → (Σ j, B j) :=
  fun value => ⟨indexMap value.1, code.assemble value.1 value.2⟩

/-- Evaluate the tagged ring-equivalence function without unfolding its
implementation. -/
@[simp]
theorem taggedFunction_apply {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) (i : I) (value : A i) :
    code.taggedFunction ⟨i, value⟩ =
      ⟨indexMap i, code.assemble i value⟩ :=
  rfl

/-- Read the assembled forward family as one total-functional tagged graph. -/
noncomputable def taggedForward {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) :
    PrimitiveFunctionGraph.GraphCode (Σ i, A i) (Σ j, B j) :=
  PrimitiveFunctionGraph.GraphCode.read code.taggedFunction

/-- Tagged graph assembly evaluates the pointwise ring-equivalence family. -/
@[simp]
theorem assemble_taggedForward {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    (code : IndexedRingEquivGraphCode indexMap A B) :
    PrimitiveFunctionGraph.GraphCode.assemble code.taggedForward =
      code.taggedFunction :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- The tagged forward graph separates the whole indexed ring-equivalence
code. -/
theorem taggedForward_injective {I : Type u} {J : Type v}
    {indexMap : I → J} {A : I → Type w} {B : J → Type x}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)] :
    Function.Injective
      (taggedForward : IndexedRingEquivGraphCode indexMap A B → _) := by
  intro first second equality
  funext i
  apply RingEquivGraphCode.equivRingEquiv.injective
  apply RingEquiv.ext
  intro value
  have functionEquality : first.taggedFunction = second.taggedFunction := by
    rw [← assemble_taggedForward first, ← assemble_taggedForward second,
      equality]
  have pairEquality := congrFun functionEquality ⟨i, value⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp pairEquality).2

/-- Pointwise composition over composed index maps. -/
noncomputable def comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    [∀ k, NonAssocSemiring (C k)]
    (first : IndexedRingEquivGraphCode firstIndex A B)
    (second : IndexedRingEquivGraphCode secondIndex B C) :
    IndexedRingEquivGraphCode (secondIndex ∘ firstIndex) A C :=
  fun i => RingEquivGraphCode.read
    ((first i).assemble.trans (second (firstIndex i)).assemble)

/-- Assembly preserves dependent pointwise ring-equivalence composition. -/
@[simp]
theorem assemble_comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    [∀ k, NonAssocSemiring (C k)]
    (first : IndexedRingEquivGraphCode firstIndex A B)
    (second : IndexedRingEquivGraphCode secondIndex B C) (i : I) :
    (comp first second).assemble i =
      (first i).assemble.trans (second (firstIndex i)).assemble := by
  exact RingEquivGraphCode.assemble_read _

/-- Tagged forward ring-equivalence functions compose in the same order as
their index and fiber maps. -/
theorem taggedFunction_comp {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type*} {C : K → Type*}
    [∀ i, NonAssocSemiring (A i)] [∀ j, NonAssocSemiring (B j)]
    [∀ k, NonAssocSemiring (C k)]
    (first : IndexedRingEquivGraphCode firstIndex A B)
    (second : IndexedRingEquivGraphCode secondIndex B C) :
    (comp first second).taggedFunction =
      second.taggedFunction ∘ first.taggedFunction := by
  funext value
  cases value with
  | mk i value =>
    simp only [taggedFunction, Function.comp_apply]
    rw [assemble_comp]
    rfl

end IndexedRingEquivGraphCode

/-! ## Complete-geometry dependent algebraic components -/

namespace CompleteGeometryDependentAlgebraicCode

/-- Read every signature-coordinate equivalence into an indexed graph family. -/
noncomputable def coordinate {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedEquivGraphCode morphism.base.upper.axisMap
      G.core.reading.signatureReading.Coordinate
      H.core.reading.signatureReading.Coordinate :=
  IndexedEquivGraphCode.read morphism.base.upper.coordinateEquiv

/-- Pointwise assembly recovers the actual coordinate-equivalence family. -/
@[simp]
theorem coordinate_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (coordinate morphism).assemble = morphism.base.upper.coordinateEquiv :=
  IndexedEquivGraphCode.assemble_read _

/-- The coordinate-family tagged graph is exactly the coordinate component
of complete geometry reading. -/
theorem coordinate_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (coordinate morphism).taggedForward =
      (readCompleteMapGraphs morphism).coordinate := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedEquivGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk axis coordinateValue =>
    simp only [IndexedEquivGraphCode.taggedFunction_apply]
    rw [coordinate_assemble]
    simp [coordinateMap, taggedMap, readCompleteMapGraphs]

/-- Read every equation-observable ring equivalence into an indexed graph
family. -/
noncomputable def equationObservable {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedRingEquivGraphCode (equationContextForwardMap morphism)
      G.core.algebra.equationSystem.Observable
      H.core.algebra.equationSystem.Observable :=
  IndexedRingEquivGraphCode.read
    morphism.base.upper.equationTransport.observableEquiv

/-- Pointwise assembly recovers the actual observable-ring equivalence
family. -/
@[simp]
theorem equationObservable_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (equationObservable morphism).assemble =
      morphism.base.upper.equationTransport.observableEquiv :=
  IndexedRingEquivGraphCode.assemble_read _

/-- The observable-family tagged graph is exactly the equation-observable
component of complete geometry reading. -/
theorem equationObservable_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (equationObservable morphism).taggedForward =
      (readCompleteMapGraphs morphism).equationObservable := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedRingEquivGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk context observableValue =>
    simp only [IndexedRingEquivGraphCode.taggedFunction_apply]
    rw [equationObservable_assemble]
    simp [equationObservableMap, taggedMap, readCompleteMapGraphs]
    rfl

end CompleteGeometryDependentAlgebraicCode

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence

end DependentAlgebraicGraphCoherence

end

end AAT.AG.LocalSemanticReconstruction
