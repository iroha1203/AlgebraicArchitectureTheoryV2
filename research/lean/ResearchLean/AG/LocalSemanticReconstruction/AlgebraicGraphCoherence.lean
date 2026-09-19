import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory
import Formal.Util.AssertStandardAxioms

/-!
# Independent algebraic coherence for primitive graph codes

A pair of total-functional Bool graphs, together with mutual-inverse equations
on their assembled functions, is an independent local presentation of an
equivalence.  A total-functional graph together with the four semiring
preservation equations is likewise an independent presentation of a ring
homomorphism.  Neither presentation stores the completed algebraic map.

Both presentations are proved exactly equivalent to their completed
structures by explicit read/assemble inverse laws.  Identity and composition
are defined on the local presentations and their assembled maps are computed.
The constructions are then connected in the same module to the reversible
Atom and equation-index components and the coefficient component of complete
geometry reading.  The two context-object graphs are recovered as the
underlying forward/backward functions; no strict object-level equivalence is
asserted for a categorical equivalence.

## Implementation notes

G-124(B) requires coherence to be stated as equations between local values,
not as the existence of a completed map.  Each presentation therefore splits
raw graph data from a separate `Prop` law and bundles them only with a subtype,
following `PrimitiveFunctionGraph.GraphData` / `IsTotalFunctional`.  Storing an
`Equiv`, `RingHom`, or `GeometryTotalHom` certificate was rejected because it
would make assembly tautological.  Keeping laws as fields of the raw data was
also rejected because it would obscure the data/`Prop` distinction.

The generic equivalence and ring-hom predicates have explicit positive and
negative fixtures.  The selected complete-geometry predicate has a canonical
identity positive fixture.  Its negative fixture works for every package with
nontrivial coefficients: it keeps all identity graphs except for a constant
zero coefficient graph, which fails preservation of one.  This tests the
combined predicate itself without importing a completed geometry morphism.

Dependent fiber equivalences, functor maps on context morphisms, geometry
naturality, and assembly of a complete `GeometryTotalHom` remain separate
obligations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace AlgebraicGraphCoherence

universe u v w

open CompleteGeometryFunctionGraphSeparation
open G122PrimitiveFunctionGraphReading

/-- Short name for the primitive total-functional Bool graph code. -/
abbrev GraphCode := PrimitiveFunctionGraph.GraphCode

/-! ## Equivalence graph codes -/

/-- Raw forward and backward total-functional graphs.  This is the data part
of the Cycle 67 equivalence presentation for G-124(B). -/
structure EquivGraphData (A : Type u) (B : Type v) where
  /-- Forward total-functional graph. -/
  forward : GraphCode A B
  /-- Backward total-functional graph. -/
  backward : GraphCode B A

/-- The G-124(B) local equations saying that a raw graph pair is mutually
inverse.  These are fixed-question premises, not consequences of bare graphs. -/
structure IsEquivGraphCode (data : EquivGraphData A B) : Prop where
  /-- Backward after forward is the identity. -/
  left_inv : Function.LeftInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.backward)
    (PrimitiveFunctionGraph.GraphCode.assemble data.forward)
  /-- Forward after backward is the identity. -/
  right_inv : Function.RightInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.backward)
    (PrimitiveFunctionGraph.GraphCode.assemble data.forward)

/-- Raw inverse graph data bundled with its independently stated local law. -/
abbrev EquivGraphCode (A : Type u) (B : Type v) :=
  { data : EquivGraphData A B // IsEquivGraphCode data }

namespace EquivGraphCode

/-- Forward graph accessor for the bundled local presentation. -/
abbrev forward {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    GraphCode A B := code.1.forward

/-- Backward graph accessor for the bundled local presentation. -/
abbrev backward {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    GraphCode B A := code.1.backward

/-- Left-inverse equation supplied by the local coherence predicate. -/
theorem left_inv {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    Function.LeftInverse
      (PrimitiveFunctionGraph.GraphCode.assemble code.backward)
      (PrimitiveFunctionGraph.GraphCode.assemble code.forward) :=
  code.2.left_inv

/-- Right-inverse equation supplied by the local coherence predicate. -/
theorem right_inv {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    Function.RightInverse
      (PrimitiveFunctionGraph.GraphCode.assemble code.backward)
      (PrimitiveFunctionGraph.GraphCode.assemble code.forward) :=
  code.2.right_inv

/-- Equivalence graph codes are determined by their two graph components;
the inverse laws are propositions. -/
@[ext]
theorem ext {A : Type u} {B : Type v}
    {first second : EquivGraphCode A B}
    (forward : first.forward = second.forward)
    (backward : first.backward = second.backward) : first = second := by
  apply Subtype.ext
  cases first with
  | mk firstData firstLaw =>
    cases second with
    | mk secondData secondLaw =>
      cases firstData with
      | mk firstForward firstBackward =>
        cases secondData with
        | mk secondForward secondBackward =>
          change firstForward = secondForward at forward
          change firstBackward = secondBackward at backward
          cases forward
          cases backward
          rfl

/-- Assemble an independent inverse graph pair into an equivalence. -/
def assemble {A : Type u} {B : Type v} (code : EquivGraphCode A B) : A ≃ B where
  toFun := PrimitiveFunctionGraph.GraphCode.assemble code.forward
  invFun := PrimitiveFunctionGraph.GraphCode.assemble code.backward
  left_inv := code.left_inv
  right_inv := code.right_inv

/-- Evaluation of an assembled equivalence uses its forward graph. -/
@[simp]
theorem assemble_apply {A : Type u} {B : Type v}
    (code : EquivGraphCode A B) (value : A) :
    code.assemble value =
      PrimitiveFunctionGraph.GraphCode.assemble code.forward value :=
  rfl

/-- Evaluation of the inverse assembled equivalence uses its backward graph. -/
@[simp]
theorem assemble_symm_apply {A : Type u} {B : Type v}
    (code : EquivGraphCode A B) (value : B) :
    code.assemble.symm value =
      PrimitiveFunctionGraph.GraphCode.assemble code.backward value :=
  rfl

/-- Read an equivalence as independent forward and backward Bool graphs. -/
noncomputable def read {A : Type u} {B : Type v} (equiv : A ≃ B) :
    EquivGraphCode A B :=
  ⟨{
    forward := PrimitiveFunctionGraph.GraphCode.read equiv
    backward := PrimitiveFunctionGraph.GraphCode.read equiv.symm }, {
    left_inv := by simpa using equiv.left_inv
    right_inv := by simpa using equiv.right_inv }⟩

/-- Positive fixture: the two identity graphs satisfy the inverse law. -/
noncomputable def boolIdentityData : EquivGraphData Bool Bool where
  forward := PrimitiveFunctionGraph.GraphCode.id
  backward := PrimitiveFunctionGraph.GraphCode.id

/-- The identity graph pair is a positive predicate instance. -/
theorem boolIdentityData_isEquivGraphCode :
    IsEquivGraphCode boolIdentityData := by
  constructor <;> intro value <;> simp [boolIdentityData]

/-- Negative fixture: a constant forward graph paired with the identity
backward graph. -/
noncomputable def boolConstantData : EquivGraphData Bool Bool where
  forward := PrimitiveFunctionGraph.GraphCode.read (fun _ => false)
  backward := PrimitiveFunctionGraph.GraphCode.id

/-- The constant/identity graph pair fails the left-inverse equation. -/
theorem boolConstantData_not_isEquivGraphCode :
    ¬ IsEquivGraphCode boolConstantData := by
  intro coherent
  have equality := coherent.left_inv true
  simp [boolConstantData] at equality

/-- Reading after assembly recovers both local graph codes. -/
@[simp]
theorem read_assemble {A : Type u} {B : Type v}
    (code : EquivGraphCode A B) : read code.assemble = code := by
  apply ext <;> simp [read, assemble, EquivGraphCode.forward,
    EquivGraphCode.backward]

/-- Assembly after reading recovers the original equivalence. -/
@[simp]
theorem assemble_read {A : Type u} {B : Type v} (equiv : A ≃ B) :
    (read equiv).assemble = equiv := by
  apply Equiv.ext
  intro value
  simp [read, assemble, EquivGraphCode.forward]

/-- Independent equivalence graph codes and actual equivalences are
explicitly equivalent. -/
noncomputable def equivEquiv {A : Type u} {B : Type v} :
    EquivGraphCode A B ≃ (A ≃ B) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity equivalence graph code. -/
noncomputable def id (A : Type u) : EquivGraphCode A A :=
  read (Equiv.refl A)

/-- Composition of equivalence graph codes, with the second code applied
after the first. -/
noncomputable def comp {A : Type u} {B : Type v} {C : Type w}
    (first : EquivGraphCode A B) (second : EquivGraphCode B C) :
    EquivGraphCode A C :=
  read (first.assemble.trans second.assemble)

/-- The assembled identity code is the identity equivalence. -/
@[simp]
theorem assemble_id (A : Type u) : (id A).assemble = Equiv.refl A := by
  simp [id]

/-- Assembly sends code composition to equivalence composition. -/
@[simp]
theorem assemble_comp {A : Type u} {B : Type v} {C : Type w}
    (first : EquivGraphCode A B) (second : EquivGraphCode B C) :
    (comp first second).assemble = first.assemble.trans second.assemble := by
  simp [comp]

/-- Forward graphs compose in their ordinary order. -/
theorem comp_forward {A : Type u} {B : Type v} {C : Type w}
    (first : EquivGraphCode A B) (second : EquivGraphCode B C) :
    (comp first second).forward =
      PrimitiveFunctionGraph.GraphCode.comp first.forward second.forward := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (comp first second).assemble.toFun =
    PrimitiveFunctionGraph.GraphCode.assemble
      (PrimitiveFunctionGraph.GraphCode.comp first.forward second.forward)
  rw [assemble_comp, PrimitiveFunctionGraph.GraphCode.assemble_comp]
  rfl

/-- Backward graphs compose in the reverse order. -/
theorem comp_backward {A : Type u} {B : Type v} {C : Type w}
    (first : EquivGraphCode A B) (second : EquivGraphCode B C) :
    (comp first second).backward =
      PrimitiveFunctionGraph.GraphCode.comp second.backward first.backward := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (comp first second).assemble.invFun =
    PrimitiveFunctionGraph.GraphCode.assemble
      (PrimitiveFunctionGraph.GraphCode.comp second.backward first.backward)
  rw [assemble_comp, PrimitiveFunctionGraph.GraphCode.assemble_comp]
  rfl

/-- A leading identity code is eliminated. -/
@[simp]
theorem id_comp {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    comp (id A) code = code := by
  apply equivEquiv.injective
  change (comp (id A) code).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply Equiv.ext
  intro value
  rfl

/-- A trailing identity code is eliminated. -/
@[simp]
theorem comp_id {A : Type u} {B : Type v} (code : EquivGraphCode A B) :
    comp code (id B) = code := by
  apply equivEquiv.injective
  change (comp code (id B)).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply Equiv.ext
  intro value
  rfl

/-- Composition of equivalence graph codes reassociates to the right. -/
@[simp]
theorem assoc {A : Type u} {B : Type v} {C : Type w} {D : Type*}
    (first : EquivGraphCode A B) (second : EquivGraphCode B C)
    (third : EquivGraphCode C D) :
    comp (comp first second) third = comp first (comp second third) := by
  apply equivEquiv.injective
  change (comp (comp first second) third).assemble =
    (comp first (comp second third)).assemble
  rw [assemble_comp, assemble_comp, assemble_comp, assemble_comp]
  apply Equiv.ext
  intro value
  rfl

end EquivGraphCode

/-! ## Ring-hom graph codes -/

/-- Raw graph data for the Cycle 67 ring-hom presentation of G-124(B). -/
structure RingHomGraphData (R : Type u) (S : Type v) where
  /-- Underlying total-functional graph. -/
  graph : GraphCode R S

/-- The independent zero/one/add/mul equations saying that a raw graph
assembles to a ring homomorphism.  They are fixed-question premises. -/
structure IsRingHomGraphCode (data : RingHomGraphData R S)
    [NonAssocSemiring R] [NonAssocSemiring S] : Prop where
  /-- Preservation of zero. -/
  map_zero : PrimitiveFunctionGraph.GraphCode.assemble data.graph 0 = 0
  /-- Preservation of one. -/
  map_one : PrimitiveFunctionGraph.GraphCode.assemble data.graph 1 = 1
  /-- Preservation of addition. -/
  map_add : ∀ first second,
    PrimitiveFunctionGraph.GraphCode.assemble data.graph (first + second) =
      PrimitiveFunctionGraph.GraphCode.assemble data.graph first +
        PrimitiveFunctionGraph.GraphCode.assemble data.graph second
  /-- Preservation of multiplication. -/
  map_mul : ∀ first second,
    PrimitiveFunctionGraph.GraphCode.assemble data.graph (first * second) =
      PrimitiveFunctionGraph.GraphCode.assemble data.graph first *
        PrimitiveFunctionGraph.GraphCode.assemble data.graph second

/-- Raw ring-hom graph data bundled with its independently stated local law. -/
abbrev RingHomGraphCode (R : Type u) (S : Type v)
    [NonAssocSemiring R] [NonAssocSemiring S] :=
  { data : RingHomGraphData R S // IsRingHomGraphCode data }

namespace RingHomGraphCode

/-- Underlying graph accessor for the bundled local presentation. -/
abbrev graph {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) : GraphCode R S :=
  code.1.graph

/-- Zero-preservation equation supplied by the local coherence predicate. -/
theorem map_zero {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) :
    PrimitiveFunctionGraph.GraphCode.assemble code.graph 0 = 0 :=
  code.2.map_zero

/-- One-preservation equation supplied by the local coherence predicate. -/
theorem map_one {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) :
    PrimitiveFunctionGraph.GraphCode.assemble code.graph 1 = 1 :=
  code.2.map_one

/-- Addition-preservation equation supplied by the local coherence predicate. -/
theorem map_add {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) (first second : R) :
    PrimitiveFunctionGraph.GraphCode.assemble code.graph (first + second) =
      PrimitiveFunctionGraph.GraphCode.assemble code.graph first +
        PrimitiveFunctionGraph.GraphCode.assemble code.graph second :=
  code.2.map_add first second

/-- Multiplication-preservation equation supplied by the local predicate. -/
theorem map_mul {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) (first second : R) :
    PrimitiveFunctionGraph.GraphCode.assemble code.graph (first * second) =
      PrimitiveFunctionGraph.GraphCode.assemble code.graph first *
        PrimitiveFunctionGraph.GraphCode.assemble code.graph second :=
  code.2.map_mul first second

/-- Ring-hom graph codes are determined by their graph component; all
preservation laws are propositions. -/
@[ext]
theorem ext {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    {first second : RingHomGraphCode R S}
    (graph : first.graph = second.graph) : first = second := by
  apply Subtype.ext
  cases first with
  | mk firstData firstLaw =>
    cases second with
    | mk secondData secondLaw =>
      cases firstData with
      | mk firstGraph =>
        cases secondData with
        | mk secondGraph =>
          change firstGraph = secondGraph at graph
          cases graph
          rfl

/-- Assemble operation-preserving graph data into a ring homomorphism. -/
def assemble {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) : R →+* S where
  toFun := PrimitiveFunctionGraph.GraphCode.assemble code.graph
  map_zero' := code.map_zero
  map_one' := code.map_one
  map_add' := code.map_add
  map_mul' := code.map_mul

/-- Evaluation of an assembled ring homomorphism uses its graph. -/
@[simp]
theorem assemble_apply {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) (value : R) :
    code.assemble value =
      PrimitiveFunctionGraph.GraphCode.assemble code.graph value :=
  rfl

/-- Read a ring homomorphism as a graph plus explicit preservation laws. -/
noncomputable def read {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] (hom : R →+* S) :
    RingHomGraphCode R S :=
  ⟨{
    graph := PrimitiveFunctionGraph.GraphCode.read hom }, {
    map_zero := by
      rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
      exact hom.map_zero
    map_one := by
      rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
      exact hom.map_one
    map_add := by
      intro first second
      rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
      exact hom.map_add first second
    map_mul := by
      intro first second
      rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
      exact hom.map_mul first second }⟩

/-- Positive fixture: the identity graph on naturals preserves all semiring
operations. -/
noncomputable def natIdentityData : RingHomGraphData Nat Nat where
  graph := PrimitiveFunctionGraph.GraphCode.id

/-- The natural-number identity graph is a positive predicate instance. -/
theorem natIdentityData_isRingHomGraphCode :
    IsRingHomGraphCode natIdentityData := by
  constructor <;> simp [natIdentityData]

/-- Negative fixture: the successor graph on naturals. -/
noncomputable def natSuccData : RingHomGraphData Nat Nat where
  graph := PrimitiveFunctionGraph.GraphCode.read Nat.succ

/-- The successor graph fails zero preservation. -/
theorem natSuccData_not_isRingHomGraphCode :
    ¬ IsRingHomGraphCode natSuccData := by
  intro coherent
  have equality := coherent.map_zero
  simp [natSuccData] at equality

/-- Reading after assembly recovers the independent graph code. -/
@[simp]
theorem read_assemble {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) : read code.assemble = code := by
  apply ext
  simp [read, assemble, RingHomGraphCode.graph]

/-- Assembly after reading recovers the original ring homomorphism. -/
@[simp]
theorem assemble_read {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] (hom : R →+* S) :
    (read hom).assemble = hom := by
  apply RingHom.ext
  intro value
  simp [read, assemble, RingHomGraphCode.graph]

/-- Independent ring-hom graph codes and ring homomorphisms are explicitly
equivalent. -/
noncomputable def equivRingHom {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S] :
    RingHomGraphCode R S ≃ (R →+* S) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity ring-hom graph code. -/
noncomputable def id (R : Type u) [NonAssocSemiring R] :
    RingHomGraphCode R R :=
  read (RingHom.id R)

/-- The assembled identity code is the identity ring homomorphism. -/
@[simp]
theorem assemble_id (R : Type u) [NonAssocSemiring R] :
    (id R).assemble = RingHom.id R := by
  simp [id]

/-- Composition of ring-hom graph codes, with the second code applied after
the first. -/
noncomputable def comp {R : Type u} {S : Type v} {T : Type w}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (first : RingHomGraphCode R S) (second : RingHomGraphCode S T) :
    RingHomGraphCode R T :=
  read (second.assemble.comp first.assemble)

/-- Assembly sends code composition to ring-hom composition. -/
@[simp]
theorem assemble_comp {R : Type u} {S : Type v} {T : Type w}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (first : RingHomGraphCode R S) (second : RingHomGraphCode S T) :
    (comp first second).assemble = second.assemble.comp first.assemble := by
  simp [comp]

/-- Underlying graphs compose in their ordinary order. -/
theorem comp_graph {R : Type u} {S : Type v} {T : Type w}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    (first : RingHomGraphCode R S) (second : RingHomGraphCode S T) :
    (comp first second).graph =
      PrimitiveFunctionGraph.GraphCode.comp first.graph second.graph := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (comp first second).assemble.toFun =
    PrimitiveFunctionGraph.GraphCode.assemble
      (PrimitiveFunctionGraph.GraphCode.comp first.graph second.graph)
  rw [assemble_comp, PrimitiveFunctionGraph.GraphCode.assemble_comp]
  rfl

/-- A leading identity ring-hom code is eliminated. -/
@[simp]
theorem id_comp {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) : comp (id R) code = code := by
  apply equivRingHom.injective
  change (comp (id R) code).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  ext
  rfl

/-- A trailing identity ring-hom code is eliminated. -/
@[simp]
theorem comp_id {R : Type u} {S : Type v}
    [NonAssocSemiring R] [NonAssocSemiring S]
    (code : RingHomGraphCode R S) : comp code (id S) = code := by
  apply equivRingHom.injective
  change (comp code (id S)).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  ext
  rfl

/-- Ring-hom graph-code composition reassociates to the right. -/
@[simp]
theorem assoc {R : Type u} {S : Type v} {T : Type w} {V : Type*}
    [NonAssocSemiring R] [NonAssocSemiring S] [NonAssocSemiring T]
    [NonAssocSemiring V]
    (first : RingHomGraphCode R S) (second : RingHomGraphCode S T)
    (third : RingHomGraphCode T V) :
    comp (comp first second) third = comp first (comp second third) := by
  apply equivRingHom.injective
  change (comp (comp first second) third).assemble =
    (comp first (comp second third)).assemble
  rw [assemble_comp, assemble_comp, assemble_comp, assemble_comp]
  ext
  rfl

end RingHomGraphCode

/-! ## Complete-geometry algebraic coherence -/

/-- Raw inverse graph data for the selected reversible components of one
complete graph bundle. -/
structure SelectedAlgebraicData {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (graphs : CompleteMapGraphs G H) where
  /-- Inverse graph for the lower pointed Atom action. -/
  pointedAtomInverse : GraphCode U.Atom U.Atom
  /-- Inverse graph for the upper Atom action. -/
  atomInverse : GraphCode U.Atom U.Atom
  /-- Inverse graph for the equation-index action. -/
  equationInverse : GraphCode H.core.algebra.equationSystem.Index
    G.core.algebra.equationSystem.Index

/-- The independent G-124(B) equations attached to selected algebraic
components of a raw complete graph bundle.  This proposition stores no
completed geometry morphism. -/
structure IsSelectedAlgebraicallyCoherent {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (graphs : CompleteMapGraphs G H)
    (data : SelectedAlgebraicData graphs) : Prop where
  /-- The pointed Atom graphs are mutually inverse. -/
  pointedAtomLeftInverse : Function.LeftInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.pointedAtomInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.pointedAtom)
  /-- The pointed Atom graphs are mutually inverse in the other order. -/
  pointedAtomRightInverse : Function.RightInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.pointedAtomInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.pointedAtom)
  /-- The upper Atom graphs are mutually inverse. -/
  atomLeftInverse : Function.LeftInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.atomInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.atom)
  /-- The upper Atom graphs are mutually inverse in the other order. -/
  atomRightInverse : Function.RightInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.atomInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.atom)
  /-- The equation-index graphs are mutually inverse. -/
  equationLeftInverse : Function.LeftInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.equationInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.equation)
  /-- The equation-index graphs are mutually inverse in the other order. -/
  equationRightInverse : Function.RightInverse
    (PrimitiveFunctionGraph.GraphCode.assemble data.equationInverse)
    (PrimitiveFunctionGraph.GraphCode.assemble graphs.equation)
  /-- The coefficient graph preserves zero. -/
  coefficientMapZero :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient 0 = 0
  /-- The coefficient graph preserves one. -/
  coefficientMapOne :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient 1 = 1
  /-- The coefficient graph preserves addition. -/
  coefficientMapAdd : ∀ first second,
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient
        (first + second) =
      PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient first +
        PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient second
  /-- The coefficient graph preserves multiplication. -/
  coefficientMapMul : ∀ first second,
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient
        (first * second) =
      PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient first *
        PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient second

/-- Raw selected algebraic data bundled with its separate coherence law. -/
abbrev SelectedAlgebraicCoherence {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (graphs : CompleteMapGraphs G H) :=
  { data : SelectedAlgebraicData graphs //
    IsSelectedAlgebraicallyCoherent graphs data }

namespace SelectedAlgebraicCoherence

/-- Inverse graph for the lower pointed Atom action. -/
abbrev pointedAtomInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) : GraphCode U.Atom U.Atom :=
  coherence.1.pointedAtomInverse

/-- Inverse graph for the upper Atom action. -/
abbrev atomInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) : GraphCode U.Atom U.Atom :=
  coherence.1.atomInverse

/-- Inverse graph for the equation-index action. -/
abbrev equationInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    GraphCode H.core.algebra.equationSystem.Index
      G.core.algebra.equationSystem.Index :=
  coherence.1.equationInverse

/-- Pointed Atom left-inverse law. -/
theorem pointedAtomLeftInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.LeftInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.pointedAtomInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.pointedAtom) :=
  coherence.2.pointedAtomLeftInverse

/-- Pointed Atom right-inverse law. -/
theorem pointedAtomRightInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.RightInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.pointedAtomInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.pointedAtom) :=
  coherence.2.pointedAtomRightInverse

/-- Upper Atom left-inverse law. -/
theorem atomLeftInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.LeftInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.atomInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.atom) :=
  coherence.2.atomLeftInverse

/-- Upper Atom right-inverse law. -/
theorem atomRightInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.RightInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.atomInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.atom) :=
  coherence.2.atomRightInverse

/-- Equation-index left-inverse law. -/
theorem equationLeftInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.LeftInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.equationInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.equation) :=
  coherence.2.equationLeftInverse

/-- Equation-index right-inverse law. -/
theorem equationRightInverse {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    Function.RightInverse
      (PrimitiveFunctionGraph.GraphCode.assemble coherence.equationInverse)
      (PrimitiveFunctionGraph.GraphCode.assemble graphs.equation) :=
  coherence.2.equationRightInverse

/-- Coefficient zero-preservation law. -/
theorem coefficientMapZero {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient 0 = 0 :=
  coherence.2.coefficientMapZero

/-- Coefficient one-preservation law. -/
theorem coefficientMapOne {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient 1 = 1 :=
  coherence.2.coefficientMapOne

/-- Coefficient addition-preservation law. -/
theorem coefficientMapAdd {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) (first second : G.Coefficient) :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient
        (first + second) =
      PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient first +
        PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient second :=
  coherence.2.coefficientMapAdd first second

/-- Coefficient multiplication-preservation law. -/
theorem coefficientMapMul {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {graphs : CompleteMapGraphs G H}
    (coherence : SelectedAlgebraicCoherence graphs) (first second : G.Coefficient) :
    PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient
        (first * second) =
      PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient first *
        PrimitiveFunctionGraph.GraphCode.assemble graphs.primitive.coefficient second :=
  coherence.2.coefficientMapMul first second

end SelectedAlgebraicCoherence

/-- A raw complete graph bundle equipped with independent algebraic coherence.
No global geometry morphism is retained. -/
structure SelectedAlgebraicallyCoherentCompleteMapGraphs {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  /-- The raw complete graph bundle. -/
  graphs : CompleteMapGraphs G H
  /-- Independent algebraic coherence for selected reversible and coefficient
  components. -/
  coherence : SelectedAlgebraicCoherence graphs

namespace SelectedAlgebraicallyCoherentCompleteMapGraphs

/-- Assemble the lower pointed Atom equivalence. -/
def pointedAtomEquiv {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H) : U.Atom ≃ U.Atom :=
  EquivGraphCode.assemble ⟨{
    forward := code.graphs.pointedAtom
    backward := code.coherence.pointedAtomInverse }, {
    left_inv := code.coherence.pointedAtomLeftInverse
    right_inv := code.coherence.pointedAtomRightInverse }⟩

/-- Assemble the upper Atom equivalence. -/
def atomEquiv {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H) : U.Atom ≃ U.Atom :=
  EquivGraphCode.assemble ⟨{
    forward := code.graphs.primitive.atom
    backward := code.coherence.atomInverse }, {
    left_inv := code.coherence.atomLeftInverse
    right_inv := code.coherence.atomRightInverse }⟩

/-- Assemble the equation-index equivalence. -/
def equationEquiv {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H) :
    G.core.algebra.equationSystem.Index ≃
      H.core.algebra.equationSystem.Index :=
  EquivGraphCode.assemble ⟨{
    forward := code.graphs.equation
    backward := code.coherence.equationInverse }, {
    left_inv := code.coherence.equationLeftInverse
    right_inv := code.coherence.equationRightInverse }⟩

/-- Assemble the coefficient ring homomorphism. -/
def coefficientHom {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H) :
    G.Coefficient →+* H.Coefficient :=
  RingHomGraphCode.assemble ⟨{
    graph := code.graphs.primitive.coefficient }, {
    map_zero := code.coherence.coefficientMapZero
    map_one := code.coherence.coefficientMapOne
    map_add := code.coherence.coefficientMapAdd
    map_mul := code.coherence.coefficientMapMul }⟩

/-- The assembled lower pointed Atom equivalence evaluates through the raw
forward graph. -/
@[simp]
theorem pointedAtomEquiv_apply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H)
    (atom : U.Atom) :
    code.pointedAtomEquiv atom =
      PrimitiveFunctionGraph.GraphCode.assemble code.graphs.pointedAtom atom :=
  EquivGraphCode.assemble_apply _ _

/-- The assembled upper Atom equivalence evaluates through the raw forward
graph. -/
@[simp]
theorem atomEquiv_apply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H)
    (atom : U.Atom) :
    code.atomEquiv atom =
      PrimitiveFunctionGraph.GraphCode.assemble code.graphs.primitive.atom atom :=
  EquivGraphCode.assemble_apply _ _

/-- The assembled equation-index equivalence evaluates through the raw
forward graph. -/
@[simp]
theorem equationEquiv_apply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H)
    (equation : G.core.algebra.equationSystem.Index) :
    code.equationEquiv equation =
      PrimitiveFunctionGraph.GraphCode.assemble code.graphs.equation equation :=
  EquivGraphCode.assemble_apply _ _

/-- The assembled coefficient homomorphism evaluates through the raw graph. -/
@[simp]
theorem coefficientHom_apply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (code : SelectedAlgebraicallyCoherentCompleteMapGraphs G H)
    (coefficient : G.Coefficient) :
    code.coefficientHom coefficient =
      PrimitiveFunctionGraph.GraphCode.assemble
        code.graphs.primitive.coefficient coefficient :=
  RingHomGraphCode.assemble_apply _ _

/-- Read the algebraically reversible and coefficient components of a complete
geometry morphism without retaining that morphism. -/
noncomputable def read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    SelectedAlgebraicallyCoherentCompleteMapGraphs G H where
  graphs := readCompleteMapGraphs morphism
  coherence := ⟨{
    pointedAtomInverse := PrimitiveFunctionGraph.GraphCode.read
      morphism.base.base.doctrineHom.atomEquiv.symm
    atomInverse := PrimitiveFunctionGraph.GraphCode.read
      morphism.base.upper.atomEquiv.symm
    equationInverse := PrimitiveFunctionGraph.GraphCode.read
      morphism.base.upper.equationTransport.equationEquiv.symm }, {
    pointedAtomLeftInverse := by
      simpa [readCompleteMapGraphs] using
        morphism.base.base.doctrineHom.atomEquiv.left_inv
    pointedAtomRightInverse := by
      simpa [readCompleteMapGraphs] using
        morphism.base.base.doctrineHom.atomEquiv.right_inv
    atomLeftInverse := by
      simpa [readCompleteMapGraphs, readPrimitiveMaps,
        SignedExactCoreReadingHom.atomMap] using
        morphism.base.upper.atomEquiv.left_inv
    atomRightInverse := by
      simpa [readCompleteMapGraphs, readPrimitiveMaps,
        SignedExactCoreReadingHom.atomMap] using
        morphism.base.upper.atomEquiv.right_inv
    equationLeftInverse := by
      simpa [readCompleteMapGraphs] using
        morphism.base.upper.equationTransport.equationEquiv.left_inv
    equationRightInverse := by
      simpa [readCompleteMapGraphs] using
        morphism.base.upper.equationTransport.equationEquiv.right_inv
    coefficientMapZero := by
      simp [readCompleteMapGraphs, readPrimitiveMaps]
    coefficientMapOne := by
      simp [readCompleteMapGraphs, readPrimitiveMaps]
    coefficientMapAdd := by
      simp [readCompleteMapGraphs, readPrimitiveMaps]
    coefficientMapMul := by
      simp [readCompleteMapGraphs, readPrimitiveMaps] }⟩

/-- Positive combined fixture: the raw inverse data read from the identity
geometry morphism, without retaining that morphism in the data. -/
noncomputable def identitySelectedAlgebraicData {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    SelectedAlgebraicData
      (readCompleteMapGraphs (GeometryTotalHom.id G)) :=
  (read (GeometryTotalHom.id G)).coherence.1

/-- The selected identity data satisfies every combined algebraic coherence
equation. -/
theorem identitySelectedAlgebraicData_isCoherent {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    IsSelectedAlgebraicallyCoherent
      (readCompleteMapGraphs (GeometryTotalHom.id G))
      (identitySelectedAlgebraicData G) :=
  (read (GeometryTotalHom.id G)).coherence.2

/-- Negative combined fixture: retain every identity component except for a
constant-zero coefficient graph. -/
noncomputable def coefficientZeroCompleteMapGraphs {U : AtomCarrier.{u}}
  (G : GeometryPackage.{u, v} U) : CompleteMapGraphs G G :=
  { CompleteGeometryGraphCategory.CompleteMapGraphs.id G with
    primitive :=
      { G122PrimitiveFunctionGraphReading.PrimitiveMapGraphs.id G with
        coefficient := PrimitiveFunctionGraph.GraphCode.read (fun _ => 0) } }

/-- Raw inverse data for the negative combined fixture. -/
noncomputable def coefficientZeroSelectedAlgebraicData {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    SelectedAlgebraicData (coefficientZeroCompleteMapGraphs G) where
  pointedAtomInverse := PrimitiveFunctionGraph.GraphCode.id
  atomInverse := PrimitiveFunctionGraph.GraphCode.id
  equationInverse := PrimitiveFunctionGraph.GraphCode.id

/-- A constant-zero coefficient graph cannot satisfy the combined coherence
predicate when the coefficient ring is nontrivial, because it does not
preserve one. -/
theorem coefficientZeroSelectedAlgebraicData_not_isCoherent
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    [Nontrivial G.Coefficient] :
    ¬ IsSelectedAlgebraicallyCoherent
      (coefficientZeroCompleteMapGraphs G)
      (coefficientZeroSelectedAlgebraicData G) := by
  intro coherent
  have equality := coherent.coefficientMapOne
  simp [coefficientZeroCompleteMapGraphs] at equality

/-- Reading and assembling recovers the lower pointed Atom equivalence. -/
@[simp]
theorem pointedAtomEquiv_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (read morphism).pointedAtomEquiv =
      morphism.base.base.doctrineHom.atomEquiv := by
  apply Equiv.ext
  intro atom
  simp [read, readCompleteMapGraphs]

/-- Reading and assembling recovers the upper Atom equivalence. -/
@[simp]
theorem atomEquiv_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (read morphism).atomEquiv = morphism.base.upper.atomEquiv := by
  apply Equiv.ext
  intro atom
  simp [read, readCompleteMapGraphs, readPrimitiveMaps,
    SignedExactCoreReadingHom.atomMap]

/-- Reading and assembling recovers the equation-index equivalence. -/
@[simp]
theorem equationEquiv_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (read morphism).equationEquiv =
      morphism.base.upper.equationTransport.equationEquiv := by
  apply Equiv.ext
  intro equation
  simp [read, readCompleteMapGraphs]

/-- Reading and assembling recovers the coefficient ring homomorphism. -/
@[simp]
theorem coefficientHom_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (read morphism).coefficientHom = morphism.geometry.coefficientHom := by
  apply RingHom.ext
  intro coefficient
  simp [read, readCompleteMapGraphs, readPrimitiveMaps]

/-- The forward context graph recovers the actual forward object action. -/
@[simp]
theorem contextForward_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveFunctionGraph.GraphCode.assemble
        (read morphism).graphs.contextForward =
      equationContextForwardMap morphism := by
  simp [read, readCompleteMapGraphs]

/-- The backward context graph recovers the actual backward object action. -/
@[simp]
theorem contextBackward_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveFunctionGraph.GraphCode.assemble
        (read morphism).graphs.contextBackward =
      equationContextBackwardMap morphism := by
  simp [read, readCompleteMapGraphs]

end SelectedAlgebraicallyCoherentCompleteMapGraphs

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence

end AlgebraicGraphCoherence

end


end AAT.AG.LocalSemanticReconstruction
