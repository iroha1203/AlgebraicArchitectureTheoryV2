import ResearchLean.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory
import Formal.Util.AssertStandardAxioms

/-!
# Remaining dependent component graph coherence

Cycle 70 of G-124 supplies the dependent graph-family layer needed for the
remaining operation, invariant, signature, and geometry-realization fields.
The fixed obligation is recorded in the G-124 report.  Its main reusable
results are exact read/assemble equivalences for one-index and two-index
families of arbitrary functions, together with tagged-graph separation and
composition.  Later sections use those families to state the remaining laws
without storing a completed `GeometryTotalHom`.

## Implementation notes

The family is stored fiberwise instead of as one graph on a sigma type.  A
single sigma graph would require a separate endpoint equation followed by
casts before it could produce a dependent map.  Fiberwise graph codes make
the endpoint indices part of the type, while `taggedForward` connects the
result back to the already accepted `CompleteMapGraphs` surface.  Storing the
completed dependent map or an existential global morphism was rejected
because either would make assembly circular.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation GeometryTransport

noncomputable section

namespace RemainingComponentGraphCoherence

universe u v w x y z

open CompleteGeometryFunctionGraphSeparation
open DependentAlgebraicGraphCoherence

/-- Dependent evaluation along equality of indices yields heterogeneous
equality of values. -/
theorem dependent_apply_heq
    {A : Sort u} {B : A → Sort v} (family : ∀ a, B a)
    {first second : A} (index_eq : first = second) :
    HEq (family first) (family second) := by
  cases index_eq
  rfl

namespace IndexedEquivGraphCode

/-- Reindex an indexed equivalence graph family along equality of its ambient
index map.  This exposes the dependent transport used by signature recovery. -/
def reindex
    {I : Type u} {J : Type v} {A : I → Type w} {B : J → Type x}
    {first second : I → J} (index_eq : first = second)
    (code : IndexedEquivGraphCode second A B) :
    IndexedEquivGraphCode first A B := by
  cases index_eq
  exact code

/-- Reindexing a code family along equality changes only its dependent type. -/
theorem reindex_heq
    {I : Type u} {J : Type v} {A : I → Type w} {B : J → Type x}
    {first second : I → J} (index_eq : first = second)
    (code : IndexedEquivGraphCode second A B) :
    HEq (reindex index_eq code) code := by
  cases index_eq
  rfl

/-- Reindexing changes only the dependent type of the assembled equivalence
family. -/
theorem reindex_assemble_heq
    {I : Type u} {J : Type v} {A : I → Type w} {B : J → Type x}
    {first second : I → J} (index_eq : first = second)
    (code : IndexedEquivGraphCode second A B) :
    HEq (reindex index_eq code).assemble code.assemble := by
  cases index_eq
  rfl

/-- Pointwise evaluation of a reindexed equivalence family is only dependent
transport of the original evaluation. -/
theorem reindex_assemble_apply_heq
    {I : Type u} {J : Type v} {A : I → Type w} {B : J → Type x}
    {first second : I → J} (index_eq : first = second)
    (code : IndexedEquivGraphCode second A B)
    (i : I) (value : A i) :
    HEq ((reindex index_eq code).assemble i value)
      (code.assemble i value) := by
  cases index_eq
  rfl

end IndexedEquivGraphCode

/-! ## One-index dependent function graphs -/

/-- Cycle 70 raw data for a dependent function family over a fixed index map.
Each fiber contains only a primitive total-functional graph code. -/
abbrev IndexedFunctionGraphCode
    {I : Type u} {J : Type v} (indexMap : I → J)
    (A : I → Type w) (B : J → Type x) :=
  ∀ i, PrimitiveFunctionGraph.GraphCode (A i) (B (indexMap i))

namespace IndexedFunctionGraphCode

/-- Main Cycle 70 assembler for a one-index graph family. -/
def assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    ∀ i, A i → B (indexMap i) :=
  fun i => (code i).assemble

/-- Inverse construction for the one-index main theorem, reading every
dependent function fiber as a primitive graph. -/
noncomputable def read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (family : ∀ i, A i → B (indexMap i)) :
    IndexedFunctionGraphCode indexMap A B :=
  fun i => PrimitiveFunctionGraph.GraphCode.read (family i)

/-- First main inverse law: reading after one-index assembly recovers every
fiber graph code. -/
@[simp]
theorem read_assemble {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    read code.assemble = code := by
  funext i
  exact PrimitiveFunctionGraph.GraphCode.read_assemble (code i)

/-- Second main inverse law: assembly after reading recovers the complete
dependent function family. -/
@[simp]
theorem assemble_read {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (family : ∀ i, A i → B (indexMap i)) :
    (read family).assemble = family := by
  funext i
  exact PrimitiveFunctionGraph.GraphCode.assemble_read (family i)

/-- Cycle 70 principal one-index universal property: fiber graph families are
explicitly equivalent to arbitrary dependent function families. -/
noncomputable def equivFamily
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x} :
    IndexedFunctionGraphCode indexMap A B ≃
      (∀ i, A i → B (indexMap i)) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Universal law-preserving refinement of the one-index equivalence.  Any
independently stated predicate on the assembled family is transported without
adding a completed family to the graph code. -/
noncomputable def equivLawfulFamily
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (Law : (∀ i, A i → B (indexMap i)) → Prop) :
    { code : IndexedFunctionGraphCode indexMap A B // Law code.assemble } ≃
      { family : ∀ i, A i → B (indexMap i) // Law family } where
  toFun code := ⟨code.1.assemble, code.2⟩
  invFun family := ⟨read family.1, by
    rw [assemble_read]
    exact family.2⟩
  left_inv code := by
    apply Subtype.ext
    exact read_assemble code.1
  right_inv family := by
    apply Subtype.ext
    exact assemble_read family.1

/-- Tagged ordinary function derived from the assembled one-index family.
This is the comparison API to `CompleteMapGraphs` sigma fields. -/
def taggedFunction {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    (Σ i, A i) → (Σ j, B j) :=
  CompleteGeometryFunctionGraphSeparation.taggedMap indexMap code.assemble

/-- Primitive graph of the tagged one-index function. -/
noncomputable def taggedForward
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    PrimitiveFunctionGraph.GraphCode (Σ i, A i) (Σ j, B j) :=
  PrimitiveFunctionGraph.GraphCode.read code.taggedFunction

/-- Tagged graph assembly evaluates to the dependent family with its index. -/
@[simp]
theorem assemble_taggedForward
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    code.taggedForward.assemble = code.taggedFunction :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- Tagged forward graphs jointly separate every one-index fiber graph. -/
theorem taggedForward_injective
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x} :
    Function.Injective
      (taggedForward : IndexedFunctionGraphCode indexMap A B → _) := by
  intro first second equality
  funext i
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  funext value
  have tagged_eq : first.taggedFunction = second.taggedFunction := by
    rw [← first.assemble_taggedForward, ← second.assemble_taggedForward,
      equality]
  have value_eq := congrFun tagged_eq ⟨i, value⟩
  exact eq_of_heq (Sigma.mk.inj_iff.mp value_eq).2

/-- Identity one-index family code. -/
noncomputable def id {I : Type u} {A : I → Type w} :
    IndexedFunctionGraphCode (_root_.id : I → I) A A :=
  read (fun _ => _root_.id)

/-- Componentwise composition of one-index family codes. -/
noncomputable def comp
    {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type y} {C : K → Type z}
    (first : IndexedFunctionGraphCode firstIndex A B)
    (second : IndexedFunctionGraphCode secondIndex B C) :
    IndexedFunctionGraphCode (secondIndex ∘ firstIndex) A C :=
  fun i => PrimitiveFunctionGraph.GraphCode.comp
    (first i) (second (firstIndex i))

/-- Assembly sends one-index code composition to dependent function
composition. -/
@[simp]
theorem assemble_comp
    {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type y} {C : K → Type z}
    (first : IndexedFunctionGraphCode firstIndex A B)
    (second : IndexedFunctionGraphCode secondIndex B C) :
    (comp first second).assemble =
      fun i value => second.assemble (firstIndex i) (first.assemble i value) := by
  funext i value
  simp [comp, assemble]

/-- Tagged one-index functions compose in the same order as their index and
fiber maps. -/
theorem taggedFunction_comp
    {I : Type u} {J : Type v} {K : Type w}
    {firstIndex : I → J} {secondIndex : J → K}
    {A : I → Type x} {B : J → Type y} {C : K → Type z}
    (first : IndexedFunctionGraphCode firstIndex A B)
    (second : IndexedFunctionGraphCode secondIndex B C) :
    (comp first second).taggedFunction =
      second.taggedFunction ∘ first.taggedFunction := by
  funext value
  cases value with
  | mk i value =>
      simp [taggedFunction,
        CompleteGeometryFunctionGraphSeparation.taggedMap]

/-- A leading identity one-index code is eliminated. -/
@[simp]
theorem id_comp
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    comp id code = code := by
  funext i
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (PrimitiveFunctionGraph.GraphCode.comp
      (PrimitiveFunctionGraph.GraphCode.read (_root_.id : A i → A i))
      (code i)).assemble = (code i).assemble
  rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
    PrimitiveFunctionGraph.GraphCode.assemble_read]
  rfl

/-- A trailing identity one-index code is eliminated. -/
@[simp]
theorem comp_id
    {I : Type u} {J : Type v} {indexMap : I → J}
    {A : I → Type w} {B : J → Type x}
    (code : IndexedFunctionGraphCode indexMap A B) :
    comp code id = code := by
  funext i
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (PrimitiveFunctionGraph.GraphCode.comp (code i)
      (PrimitiveFunctionGraph.GraphCode.read
        (_root_.id : B (indexMap i) → B (indexMap i)))).assemble =
    (code i).assemble
  rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
    PrimitiveFunctionGraph.GraphCode.assemble_read]
  rfl

/-- One-index graph-family composition reassociates to the right. -/
@[simp]
theorem assoc
    {I : Type u} {J : Type v} {K : Type w} {L : Type x}
    {firstIndex : I → J} {secondIndex : J → K} {thirdIndex : K → L}
    {A : I → Type y} {B : J → Type z} {C : K → Type*} {D : L → Type*}
    (first : IndexedFunctionGraphCode firstIndex A B)
    (second : IndexedFunctionGraphCode secondIndex B C)
    (third : IndexedFunctionGraphCode thirdIndex C D) :
    comp (comp first second) third = comp first (comp second third) := by
  funext i
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  simp [comp, Function.comp_def]

end IndexedFunctionGraphCode

/-! ## Two-index dependent function graphs -/

/-- Cycle 70 raw data for a function family depending on two endpoint maps.
This is the operation-map presentation required by the fixed obligation. -/
abbrev BiIndexedFunctionGraphCode
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    (firstIndex : I₁ → J₁) (secondIndex : I₂ → J₂)
    (A : I₁ → I₂ → Type y) (B : J₁ → J₂ → Type z) :=
  ∀ i j, PrimitiveFunctionGraph.GraphCode
    (A i j) (B (firstIndex i) (secondIndex j))

namespace BiIndexedFunctionGraphCode

/-- Main Cycle 70 assembler for two-endpoint graph families. -/
def assemble
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    ∀ i j, A i j → B (firstIndex i) (secondIndex j) :=
  fun i j => (code i j).assemble

/-- Inverse construction for the two-index main theorem. -/
noncomputable def read
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (family : ∀ i j, A i j → B (firstIndex i) (secondIndex j)) :
    BiIndexedFunctionGraphCode firstIndex secondIndex A B :=
  fun i j => PrimitiveFunctionGraph.GraphCode.read (family i j)

/-- First two-index inverse law. -/
@[simp]
theorem read_assemble
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    read code.assemble = code := by
  funext i j
  exact PrimitiveFunctionGraph.GraphCode.read_assemble (code i j)

/-- Second two-index inverse law. -/
@[simp]
theorem assemble_read
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (family : ∀ i j, A i j → B (firstIndex i) (secondIndex j)) :
    (read family).assemble = family := by
  funext i j
  exact PrimitiveFunctionGraph.GraphCode.assemble_read (family i j)

/-- Cycle 70 principal operation-family universal property. -/
noncomputable def equivFamily
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z} :
    BiIndexedFunctionGraphCode firstIndex secondIndex A B ≃
      (∀ i j, A i j → B (firstIndex i) (secondIndex j)) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Universal law-preserving refinement of the two-endpoint equivalence. -/
noncomputable def equivLawfulFamily
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (Law : (∀ i j, A i j → B (firstIndex i) (secondIndex j)) → Prop) :
    { code : BiIndexedFunctionGraphCode firstIndex secondIndex A B //
        Law code.assemble } ≃
      { family : ∀ i j, A i j → B (firstIndex i) (secondIndex j) //
        Law family } where
  toFun code := ⟨code.1.assemble, code.2⟩
  invFun family := ⟨read family.1, by
    rw [assemble_read]
    exact family.2⟩
  left_inv code := by
    apply Subtype.ext
    exact read_assemble code.1
  right_inv family := by
    apply Subtype.ext
    exact assemble_read family.1

/-- Tagged ordinary operation-like function retaining both endpoints. -/
def taggedFunction
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    (Σ i, Σ j, A i j) → (Σ i, Σ j, B i j) :=
  fun value => ⟨firstIndex value.1, secondIndex value.2.1,
    code.assemble value.1 value.2.1 value.2.2⟩

/-- Primitive graph of the tagged two-index function. -/
noncomputable def taggedForward
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    PrimitiveFunctionGraph.GraphCode
      (Σ i, Σ j, A i j) (Σ i, Σ j, B i j) :=
  PrimitiveFunctionGraph.GraphCode.read code.taggedFunction

/-- Tagged two-index graph assembly recovers its ordinary function. -/
@[simp]
theorem assemble_taggedForward
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    code.taggedForward.assemble = code.taggedFunction :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- Tagged two-index graphs jointly separate every endpoint-indexed fiber. -/
theorem taggedForward_injective
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z} :
    Function.Injective
      (taggedForward :
        BiIndexedFunctionGraphCode firstIndex secondIndex A B → _) := by
  intro first second equality
  funext i j
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  funext value
  have tagged_eq : first.taggedFunction = second.taggedFunction := by
    rw [← first.assemble_taggedForward, ← second.assemble_taggedForward,
      equality]
  have value_eq := congrFun tagged_eq ⟨i, j, value⟩
  have tail_eq := (Sigma.mk.inj_iff.mp value_eq).2
  exact eq_of_heq (Sigma.mk.inj_iff.mp (eq_of_heq tail_eq)).2

/-- Identity two-index family code. -/
noncomputable def id
    {I₁ : Type u} {I₂ : Type v} {A : I₁ → I₂ → Type y} :
    BiIndexedFunctionGraphCode (_root_.id : I₁ → I₁)
      (_root_.id : I₂ → I₂) A A :=
  read (fun _ _ => _root_.id)

/-- Componentwise composition of two-index family codes. -/
noncomputable def comp
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {K₁ : Type y} {K₂ : Type z}
    {firstIndex₁ : I₁ → J₁} {firstIndex₂ : I₂ → J₂}
    {secondIndex₁ : J₁ → K₁} {secondIndex₂ : J₂ → K₂}
    {A : I₁ → I₂ → Type*} {B : J₁ → J₂ → Type*}
    {C : K₁ → K₂ → Type*}
    (first : BiIndexedFunctionGraphCode firstIndex₁ firstIndex₂ A B)
    (second : BiIndexedFunctionGraphCode secondIndex₁ secondIndex₂ B C) :
    BiIndexedFunctionGraphCode (secondIndex₁ ∘ firstIndex₁)
      (secondIndex₂ ∘ firstIndex₂) A C :=
  fun i j => PrimitiveFunctionGraph.GraphCode.comp
    (first i j) (second (firstIndex₁ i) (firstIndex₂ j))

/-- Assembly sends two-index code composition to dependent function
composition. -/
@[simp]
theorem assemble_comp
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {K₁ : Type y} {K₂ : Type z}
    {firstIndex₁ : I₁ → J₁} {firstIndex₂ : I₂ → J₂}
    {secondIndex₁ : J₁ → K₁} {secondIndex₂ : J₂ → K₂}
    {A : I₁ → I₂ → Type*} {B : J₁ → J₂ → Type*}
    {C : K₁ → K₂ → Type*}
    (first : BiIndexedFunctionGraphCode firstIndex₁ firstIndex₂ A B)
    (second : BiIndexedFunctionGraphCode secondIndex₁ secondIndex₂ B C) :
    (comp first second).assemble = fun i j value =>
      second.assemble (firstIndex₁ i) (firstIndex₂ j)
        (first.assemble i j value) := by
  funext i j value
  simp [comp, assemble]

/-- Tagged two-index functions compose with both endpoint maps. -/
theorem taggedFunction_comp
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {K₁ : Type y} {K₂ : Type z}
    {firstIndex₁ : I₁ → J₁} {firstIndex₂ : I₂ → J₂}
    {secondIndex₁ : J₁ → K₁} {secondIndex₂ : J₂ → K₂}
    {A : I₁ → I₂ → Type*} {B : J₁ → J₂ → Type*}
    {C : K₁ → K₂ → Type*}
    (first : BiIndexedFunctionGraphCode firstIndex₁ firstIndex₂ A B)
    (second : BiIndexedFunctionGraphCode secondIndex₁ secondIndex₂ B C) :
    (comp first second).taggedFunction =
      second.taggedFunction ∘ first.taggedFunction := by
  funext value
  cases value with
  | mk i tail =>
      cases tail with
      | mk j value => simp [taggedFunction, comp, assemble]

/-- A leading identity two-index code is eliminated. -/
@[simp]
theorem id_comp
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    comp id code = code := by
  funext i j
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (PrimitiveFunctionGraph.GraphCode.comp
      (PrimitiveFunctionGraph.GraphCode.read (_root_.id : A i j → A i j))
      (code i j)).assemble = (code i j).assemble
  rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
    PrimitiveFunctionGraph.GraphCode.assemble_read]
  rfl

/-- A trailing identity two-index code is eliminated. -/
@[simp]
theorem comp_id
    {I₁ : Type u} {I₂ : Type v} {J₁ : Type w} {J₂ : Type x}
    {firstIndex : I₁ → J₁} {secondIndex : I₂ → J₂}
    {A : I₁ → I₂ → Type y} {B : J₁ → J₂ → Type z}
    (code : BiIndexedFunctionGraphCode firstIndex secondIndex A B) :
    comp code id = code := by
  funext i j
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  change (PrimitiveFunctionGraph.GraphCode.comp (code i j)
      (PrimitiveFunctionGraph.GraphCode.read
        (_root_.id : B (firstIndex i) (secondIndex j) →
          B (firstIndex i) (secondIndex j)))).assemble =
    (code i j).assemble
  rw [PrimitiveFunctionGraph.GraphCode.assemble_comp,
    PrimitiveFunctionGraph.GraphCode.assemble_read]
  rfl

/-- Two-index graph-family composition reassociates to the right. -/
@[simp]
theorem assoc
    {I₁ I₂ J₁ J₂ K₁ K₂ L₁ L₂ : Type*}
    {firstIndex₁ : I₁ → J₁} {firstIndex₂ : I₂ → J₂}
    {secondIndex₁ : J₁ → K₁} {secondIndex₂ : J₂ → K₂}
    {thirdIndex₁ : K₁ → L₁} {thirdIndex₂ : K₂ → L₂}
    {A : I₁ → I₂ → Type*} {B : J₁ → J₂ → Type*}
    {C : K₁ → K₂ → Type*} {D : L₁ → L₂ → Type*}
    (first : BiIndexedFunctionGraphCode firstIndex₁ firstIndex₂ A B)
    (second : BiIndexedFunctionGraphCode secondIndex₁ secondIndex₂ B C)
    (third : BiIndexedFunctionGraphCode thirdIndex₁ thirdIndex₂ C D) :
    comp (comp first second) third = comp first (comp second third) := by
  funext i j
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  simp [comp, Function.comp_def]

end BiIndexedFunctionGraphCode

/-! ## Law-preserving ordinary graphs -/

/-- Universal law-preserving refinement of the primitive function-graph
equivalence, used for the remaining invariant and raw index maps. -/
noncomputable def graphEquivLawfulFunction
    {A : Type u} {B : Type v} (Law : (A → B) → Prop) :
    { code : PrimitiveFunctionGraph.GraphCode A B // Law code.assemble } ≃
      { function : A → B // Law function } where
  toFun code := ⟨code.1.assemble, code.2⟩
  invFun function := ⟨PrimitiveFunctionGraph.GraphCode.read function.1, by
    rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
    exact function.2⟩
  left_inv code := by
    apply Subtype.ext
    exact PrimitiveFunctionGraph.GraphCode.read_assemble code.1
  right_inv function := by
    apply Subtype.ext
    exact PrimitiveFunctionGraph.GraphCode.assemble_read function.1

/-! ## Remaining core laws -/

/-- Operation naturality required by the Cycle 70 fixed obligation, stated
for an arbitrary dependent operation family and independently supplied object
and configuration maps. -/
def IsOperationNatural {U : AtomCarrier.{u}} (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (configurationMap : ∀ A,
      ConfigurationHom A.configuration (objectMap A).configuration)
    (operationMap : ∀ A B,
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)) : Prop :=
  ∀ A B (op : P.reading.operationReading.Op A B),
    ConfigurationHom.comp
        (Q.reading.operationReading.configurationMap (operationMap A B op))
        (configurationMap A) =
      ConfigurationHom.comp
        (configurationMap B)
        (P.reading.operationReading.configurationMap op)

/-- Invariant-transport law required by Cycle 70, separated from the graph of
the invariant-index function. -/
def IsInvariantTransport {U : AtomCarrier.{u}} (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (invariantMap : P.reading.invariantReading.Index →
      Q.reading.invariantReading.Index) : Prop :=
  ∀ i,
    Invariant.TransportedAlong
      (P.reading.invariantReading.invariant i)
      (Q.reading.invariantReading.invariant (invariantMap i))
      _root_.id objectMap

/-- A concrete failed operation square refutes operation naturality.  This is
the negative-instance constructor for carrier-specific fixtures. -/
theorem not_isOperationNatural_of_counterexample {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {configurationMap : ∀ A,
      ConfigurationHom A.configuration (objectMap A).configuration}
    {operationMap : ∀ A B,
      P.reading.operationReading.Op A B →
        Q.reading.operationReading.Op (objectMap A) (objectMap B)}
    {A B} (op : P.reading.operationReading.Op A B)
    (failure : ConfigurationHom.comp
        (Q.reading.operationReading.configurationMap (operationMap A B op))
        (configurationMap A) ≠
      ConfigurationHom.comp (configurationMap B)
        (P.reading.operationReading.configurationMap op)) :
    ¬ IsOperationNatural P Q objectMap configurationMap operationMap :=
  fun natural => failure (natural A B op)

/-- A failed invariant at one index refutes invariant transport. -/
theorem not_isInvariantTransport_of_counterexample {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {invariantMap : P.reading.invariantReading.Index →
      Q.reading.invariantReading.Index}
    (i : P.reading.invariantReading.Index)
    (failure : ¬ Invariant.TransportedAlong
      (P.reading.invariantReading.invariant i)
      (Q.reading.invariantReading.invariant (invariantMap i))
      _root_.id objectMap) :
    ¬ IsInvariantTransport P Q objectMap invariantMap :=
  fun transport => failure (transport i)

/-- Law-bearing operation graph code over explicit object and configuration
maps.  The ambient maps are local data, not a completed core morphism. -/
abbrev LawfulOperationGraphCode {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (configurationMap : ∀ A,
      ConfigurationHom A.configuration (objectMap A).configuration) :=
  { code : BiIndexedFunctionGraphCode objectMap objectMap
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => Q.reading.operationReading.Op A B) //
    IsOperationNatural P Q objectMap configurationMap code.assemble }

namespace LawfulOperationGraphCode

/-- Identity operation code with its naturality law. -/
noncomputable def id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    LawfulOperationGraphCode P P _root_.id
      (fun A => ConfigurationHom.id A.configuration) := by
  refine ⟨BiIndexedFunctionGraphCode.id, ?_⟩
  intro A B op
  let identityCode : BiIndexedFunctionGraphCode
      (_root_.id : ArchitectureObject U → ArchitectureObject U)
      (_root_.id : ArchitectureObject U → ArchitectureObject U)
      (fun A B => P.reading.operationReading.Op A B)
      (fun A B => P.reading.operationReading.Op A B) :=
    BiIndexedFunctionGraphCode.id
  have operation_eq : identityCode.assemble A B op = op := by
    change (BiIndexedFunctionGraphCode.read
      (fun (_ : ArchitectureObject U) (_ : ArchitectureObject U) =>
        _root_.id)).assemble A B op = op
    rw [BiIndexedFunctionGraphCode.assemble_read]
    rfl
  change ConfigurationHom.comp
      (P.reading.operationReading.configurationMap
        (identityCode.assemble A B op))
      (ConfigurationHom.id A.configuration) =
    ConfigurationHom.comp (ConfigurationHom.id B.configuration)
      (P.reading.operationReading.configurationMap op)
  rw [operation_eq]
  apply ConfigurationHom.ext
  funext atom
  rfl

/-- Componentwise composition preserves operation naturality. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    {firstConfiguration : ∀ A,
      ConfigurationHom A.configuration (firstObject A).configuration}
    {secondConfiguration : ∀ A,
      ConfigurationHom A.configuration (secondObject A).configuration}
    (first : LawfulOperationGraphCode P Q firstObject firstConfiguration)
    (second : LawfulOperationGraphCode Q R secondObject secondConfiguration) :
    LawfulOperationGraphCode P R (secondObject ∘ firstObject)
      (fun A => ConfigurationHom.comp
        (secondConfiguration (firstObject A)) (firstConfiguration A)) := by
  refine ⟨BiIndexedFunctionGraphCode.comp first.1 second.1, ?_⟩
  intro A B op
  apply ConfigurationHom.ext
  have firstLaw := congrArg ConfigurationHom.atomMap (first.2 A B op)
  have secondLaw := congrArg ConfigurationHom.atomMap
    (second.2 (firstObject A) (firstObject B) (first.1.assemble A B op))
  simp only [BiIndexedFunctionGraphCode.assemble_comp,
    ConfigurationHom.comp] at firstLaw secondLaw ⊢
  rw [← Function.comp_assoc, secondLaw, Function.comp_assoc, firstLaw,
    ← Function.comp_assoc]

/-- Assembly of lawful operation composition is pointwise function
composition. -/
theorem assemble_comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    {firstConfiguration : ∀ A,
      ConfigurationHom A.configuration (firstObject A).configuration}
    {secondConfiguration : ∀ A,
      ConfigurationHom A.configuration (secondObject A).configuration}
    (first : LawfulOperationGraphCode P Q firstObject firstConfiguration)
    (second : LawfulOperationGraphCode Q R secondObject secondConfiguration) :
    (comp first second).1.assemble = fun A B op =>
      second.1.assemble (firstObject A) (firstObject B)
        (first.1.assemble A B op) :=
  BiIndexedFunctionGraphCode.assemble_comp _ _

end LawfulOperationGraphCode

/-- Law-bearing invariant graph code over an explicit object map. -/
abbrev LawfulInvariantGraphCode {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U) :=
  { code : PrimitiveFunctionGraph.GraphCode
      P.reading.invariantReading.Index Q.reading.invariantReading.Index //
    IsInvariantTransport P Q objectMap code.assemble }

/-- Composition law for transported invariants, stated publicly for the
law-bearing invariant graph API. -/
theorem invariantTransportedAlong_comp {U : AtomCarrier.{u}}
    (I J K : Invariant U) {ι : Type w}
    (source middle target : ι → ArchitectureObject U)
    (first : Invariant.TransportedAlong I J source middle)
    (second : Invariant.TransportedAlong J K middle target) :
    Invariant.TransportedAlong I K source target := by
  cases I <;> cases J <;> cases K
  · rcases first with ⟨firstEquiv, firstEq⟩
    rcases second with ⟨secondEquiv, secondEq⟩
    exact ⟨firstEquiv.trans secondEquiv, fun A => by
      simp only [Equiv.trans_apply, firstEq, secondEq]⟩
  · exact False.elim second
  · exact False.elim first
  · exact False.elim first
  · exact False.elim first
  · exact False.elim first
  · exact False.elim second
  · exact fun A => (first A).trans (second A)

/-- Precomposition law for transported invariants. -/
theorem invariantTransportedAlong_precomp {U : AtomCarrier.{u}}
    (I J : Invariant U) {ι κ : Type w}
    (source target : ι → ArchitectureObject U) (index : κ → ι)
    (transport : Invariant.TransportedAlong I J source target) :
    Invariant.TransportedAlong I J (source ∘ index) (target ∘ index) := by
  cases I <;> cases J
  · rcases transport with ⟨equivalence, equality⟩
    exact ⟨equivalence, fun A => equality (index A)⟩
  · exact False.elim transport
  · exact False.elim transport
  · exact fun A => transport (index A)

namespace LawfulInvariantGraphCode

/-- Identity invariant code with reflexive transport. -/
noncomputable def id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    LawfulInvariantGraphCode P P _root_.id := by
  refine ⟨PrimitiveFunctionGraph.GraphCode.id, ?_⟩
  intro i
  simpa using Invariant.transportedAlong_refl
    (P.reading.invariantReading.invariant i) _root_.id

/-- Componentwise composition preserves invariant transport. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (first : LawfulInvariantGraphCode P Q firstObject)
    (second : LawfulInvariantGraphCode Q R secondObject) :
    LawfulInvariantGraphCode P R (secondObject ∘ firstObject) := by
  refine ⟨PrimitiveFunctionGraph.GraphCode.comp first.1 second.1, ?_⟩
  intro i
  simpa [Function.comp_def] using
    invariantTransportedAlong_comp _ _ _ _ _ _ (first.2 i)
      (invariantTransportedAlong_precomp _ _ _ _ firstObject
        (second.2 (first.1.assemble i)))

/-- Assembly of lawful invariant composition is ordinary function
composition. -/
theorem assemble_comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (first : LawfulInvariantGraphCode P Q firstObject)
    (second : LawfulInvariantGraphCode Q R secondObject) :
    (comp first second).1.assemble = second.1.assemble ∘ first.1.assemble := by
  simp [comp]

end LawfulInvariantGraphCode

/-! ## Geometry realization supply from graph families -/

/-- Raw Cycle 70 graph data for the three context-indexed geometry
realization families over a fixed core-package morphism. -/
structure RealizationGraphData {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) (f : PackageTotalHom P Q) where
  /-- Fiberwise support comparison graphs. -/
  support : IndexedFunctionGraphCode (coreContextFunctor f).obj
    (fun W : Site.ContextCategoryObject P.contextPreorder => W.ctx.Support)
    (fun W : Site.ContextCategoryObject Q.contextPreorder => W.ctx.Support)
  /-- Fiberwise axis comparison graphs. -/
  axis : IndexedFunctionGraphCode (coreContextFunctor f).obj
    (fun W : Site.ContextCategoryObject P.contextPreorder => W.ctx.Axis)
    (fun W : Site.ContextCategoryObject Q.contextPreorder => W.ctx.Axis)
  /-- Fiberwise observable comparison graphs. -/
  observable : IndexedFunctionGraphCode (coreContextFunctor f).obj
    (fun W : Site.ContextCategoryObject P.contextPreorder => W.ctx.Observable)
    (fun W : Site.ContextCategoryObject Q.contextPreorder => W.ctx.Observable)

/-- The independent reading-preservation and restriction-naturality laws for
Cycle 70 realization graph data.  These are the premises of the fixed
obligation, not a stored geometry lift. -/
structure IsRealizationGraphCode {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    (data : RealizationGraphData P Q f) : Prop where
  /-- Support readings are preserved under the upper Atom equivalence. -/
  supportReads : ∀ W support atom,
    W.ctx.minimal.supportReads support atom →
      ((coreContextFunctor f).obj W).ctx.minimal.supportReads
        (data.support.assemble W support) (f.upper.atomEquiv atom)
  /-- Axis readings are preserved. -/
  axisReads : ∀ W axis,
    W.ctx.minimal.axisReads axis →
      ((coreContextFunctor f).obj W).ctx.minimal.axisReads
        (data.axis.assemble W axis)
  /-- Observable readings are preserved. -/
  observableReads : ∀ W observable,
    W.ctx.minimal.observableReads observable →
      ((coreContextFunctor f).obj W).ctx.minimal.observableReads
        (data.observable.assemble W observable)
  /-- Support comparison commutes with readable restriction. -/
  support_naturality : ∀ {W V} (w : W ⟶ V) support,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).supportMap
        (data.support.assemble W support) =
      data.support.assemble V
        ((P.contextPreorder.morphism (leOfHom w)).supportMap support)
  /-- Axis comparison commutes with readable restriction. -/
  axis_naturality : ∀ {W V} (w : W ⟶ V) axis,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).axisMap
        (data.axis.assemble W axis) =
      data.axis.assemble V
        ((P.contextPreorder.morphism (leOfHom w)).axisMap axis)
  /-- Observable comparison commutes contravariantly with restriction. -/
  observable_naturality : ∀ {W V} (w : W ⟶ V) observable,
    (Q.contextPreorder.morphism
      (leOfHom ((coreContextFunctor f).map w))).observableRestrict
        (data.observable.assemble V observable) =
      data.observable.assemble W
        ((P.contextPreorder.morphism (leOfHom w)).observableRestrict observable)

/-- One failed support-reading witness refutes realization graph coherence.
Carrier-specific fixtures need not negate all nine fields. -/
theorem not_isRealizationGraphCode_of_support_counterexample
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {f : PackageTotalHom P Q} {data : RealizationGraphData P Q f}
    (W) (support : W.ctx.Support) (atom : U.Atom)
    (sourceReads : W.ctx.minimal.supportReads support atom)
    (targetFails : ¬ ((coreContextFunctor f).obj W).ctx.minimal.supportReads
      (data.support.assemble W support) (f.upper.atomEquiv atom)) :
    ¬ IsRealizationGraphCode data :=
  fun coherent => targetFails
    (coherent.supportReads W support atom sourceReads)

/-- Graph-presented Cycle 70 realization supply. -/
abbrev RealizationGraphCode {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) (f : PackageTotalHom P Q) :=
  { data : RealizationGraphData P Q f // IsRealizationGraphCode data }

namespace RealizationGraphCode

/-- Assemble the three graph families and their independent laws into the
existing `RealizationTransportSupply` API. -/
def assemble {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    (code : RealizationGraphCode P Q f) :
    RealizationTransportSupply P Q f where
  supportComp := code.1.support.assemble
  axisComp := code.1.axis.assemble
  observableComp := code.1.observable.assemble
  supportReads := code.2.supportReads
  axisReads := code.2.axisReads
  observableReads := code.2.observableReads
  support_naturality := code.2.support_naturality
  axis_naturality := code.2.axis_naturality
  observable_naturality := code.2.observable_naturality

/-- Read an existing realization supply into independent fiber graph codes and
the same local laws. -/
noncomputable def read {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    (supply : RealizationTransportSupply P Q f) :
    RealizationGraphCode P Q f :=
  ⟨{
    support := IndexedFunctionGraphCode.read supply.supportComp
    axis := IndexedFunctionGraphCode.read supply.axisComp
    observable := IndexedFunctionGraphCode.read supply.observableComp }, {
    supportReads := by
      intro W support atom h
      simpa using supply.supportReads W support atom h
    axisReads := by
      intro W axis h
      simpa using supply.axisReads W axis h
    observableReads := by
      intro W observable h
      simpa using supply.observableReads W observable h
    support_naturality := by
      intro W V w support
      simpa using supply.support_naturality w support
    axis_naturality := by
      intro W V w axis
      simpa using supply.axis_naturality w axis
    observable_naturality := by
      intro W V w observable
      simpa using supply.observable_naturality w observable }⟩

/-- Realization graph codes are determined by their three raw graph families. -/
@[ext]
theorem ext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    {first second : RealizationGraphCode P Q f}
    (support : first.1.support = second.1.support)
    (axis : first.1.axis = second.1.axis)
    (observable : first.1.observable = second.1.observable) :
    first = second := by
  apply Subtype.ext
  cases first with
  | mk firstData firstLaw =>
      cases second with
      | mk secondData secondLaw =>
          cases firstData
          cases secondData
          cases support
          cases axis
          cases observable
          rfl

/-- Realization supplies are determined by their three computational
comparison families; all remaining fields are propositions. -/
theorem supply_ext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    {first second : RealizationTransportSupply P Q f}
    (support : first.supportComp = second.supportComp)
    (axis : first.axisComp = second.axisComp)
    (observable : first.observableComp = second.observableComp) :
    first = second := by
  cases first
  cases second
  cases support
  cases axis
  cases observable
  rfl

/-- First Cycle 70 realization inverse law. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    (code : RealizationGraphCode P Q f) :
    read code.assemble = code := by
  apply ext <;> funext W
  all_goals exact PrimitiveFunctionGraph.GraphCode.read_assemble _

/-- Second Cycle 70 realization inverse law. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q}
    (supply : RealizationTransportSupply P Q f) :
    (read supply).assemble = supply := by
  apply supply_ext <;> funext W
  all_goals exact PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- Cycle 70 principal geometry-realization universal property. -/
noncomputable def equivSupply {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} {f : PackageTotalHom P Q} :
    RealizationGraphCode P Q f ≃ RealizationTransportSupply P Q f where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity realization supply, defined without a geometry morphism. -/
noncomputable def supplyId {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    RealizationTransportSupply P P (PackageTotalHom.id P) where
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Composition of realization supplies.  All three local carriers and all
reading and naturality laws compose componentwise. -/
noncomputable def supplyComp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {f : PackageTotalHom P Q} {g : PackageTotalHom Q R}
    (first : RealizationTransportSupply P Q f)
    (second : RealizationTransportSupply Q R g) :
    RealizationTransportSupply P R (PackageTotalHom.comp f g) where
  supportComp W support :=
    second.supportComp ((coreContextFunctor f).obj W)
      (first.supportComp W support)
  axisComp W axis :=
    second.axisComp ((coreContextFunctor f).obj W) (first.axisComp W axis)
  observableComp W observable :=
    second.observableComp ((coreContextFunctor f).obj W)
      (first.observableComp W observable)
  supportReads W support atom h :=
    second.supportReads ((coreContextFunctor f).obj W) _ _
      (first.supportReads W support atom h)
  axisReads W axis h :=
    second.axisReads ((coreContextFunctor f).obj W) _
      (first.axisReads W axis h)
  observableReads W observable h :=
    second.observableReads ((coreContextFunctor f).obj W) _
      (first.observableReads W observable h)
  support_naturality {W V} w support := by
    rw [second.support_naturality ((coreContextFunctor f).map w),
      first.support_naturality w]
  axis_naturality {W V} w axis := by
    rw [second.axis_naturality ((coreContextFunctor f).map w),
      first.axis_naturality w]
  observable_naturality {W V} w observable := by
    rw [second.observable_naturality ((coreContextFunctor f).map w),
      first.observable_naturality w]

/-- Identity realization graph code, obtained by the inverse of assembly. -/
noncomputable def id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    RealizationGraphCode P P (PackageTotalHom.id P) :=
  read (supplyId P)

/-- Composition of law-bearing realization graph codes. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {f : PackageTotalHom P Q} {g : PackageTotalHom Q R}
    (first : RealizationGraphCode P Q f)
    (second : RealizationGraphCode Q R g) :
    RealizationGraphCode P R (PackageTotalHom.comp f g) :=
  read (supplyComp first.assemble second.assemble)

/-- Assembly preserves the identity realization code exactly. -/
@[simp]
theorem assemble_id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    (id P).assemble = supplyId P :=
  assemble_read _

/-- Assembly preserves composition of law-bearing realization codes. -/
@[simp]
theorem assemble_comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {f : PackageTotalHom P Q} {g : PackageTotalHom Q R}
    (first : RealizationGraphCode P Q f)
    (second : RealizationGraphCode Q R g) :
    (comp first second).assemble = supplyComp first.assemble second.assemble :=
  assemble_read _

end RealizationGraphCode

/-! ## Signature graph coherence -/

/-- Independent signature-axis graph and coordinate-equivalence graph family.
The coordinate target index is derived from the assembled axis graph. -/
structure SignatureGraphData {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U) where
  /-- Raw graph of the signature-axis map. -/
  axis : PrimitiveFunctionGraph.GraphCode
    P.reading.signatureReading.Axis Q.reading.signatureReading.Axis
  /-- Fiberwise coordinate-equivalence graphs over the assembled axis map. -/
  coordinate : IndexedEquivGraphCode axis.assemble
    P.reading.signatureReading.Coordinate
    Q.reading.signatureReading.Coordinate

/-- Cycle 70 signature laws, separated from the raw axis and coordinate
graphs. -/
structure IsSignatureGraphCode {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (objectMap : ArchitectureObject U → ArchitectureObject U)
    (data : SignatureGraphData P Q) : Prop where
  /-- Selected-axis status is preserved and reflected. -/
  axis_selected_iff : ∀ i,
    P.reading.signatureReading.selected i ↔
      Q.reading.signatureReading.selected (data.axis.assemble i)
  /-- Coordinate assembly agrees with coordinates of mapped objects. -/
  coordinate_eq : ∀ A i,
    data.coordinate.assemble i
        (P.reading.signatureReading.coordinate A i) =
      Q.reading.signatureReading.coordinate
        (objectMap A) (data.axis.assemble i)

/-- One selected-axis mismatch refutes signature graph coherence. -/
theorem not_isSignatureGraphCode_of_selected_counterexample
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {data : SignatureGraphData P Q}
    (i : P.reading.signatureReading.Axis)
    (failure : ¬ (P.reading.signatureReading.selected i ↔
      Q.reading.signatureReading.selected (data.axis.assemble i))) :
    ¬ IsSignatureGraphCode objectMap data :=
  fun coherent => failure (coherent.axis_selected_iff i)

/-- Graph-presented signature coherence for the fixed object map. -/
abbrev SignatureGraphCode {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U) :=
  { data : SignatureGraphData P Q //
    IsSignatureGraphCode objectMap data }

/-- Completed signature transport used only as the output of graph assembly.
It records the two maps and the same local laws, but no core morphism. -/
structure SignatureTransportSupply {U : AtomCarrier.{u}}
    (P Q : AATCorePackage U)
    (objectMap : ArchitectureObject U → ArchitectureObject U) where
  /-- Map on signature axes. -/
  axisMap : P.reading.signatureReading.Axis →
    Q.reading.signatureReading.Axis
  /-- Coordinate equivalence over each mapped axis. -/
  coordinateEquiv : ∀ i,
    P.reading.signatureReading.Coordinate i ≃
      Q.reading.signatureReading.Coordinate (axisMap i)
  /-- Selected-axis status is preserved and reflected. -/
  axis_selected_iff : ∀ i,
    P.reading.signatureReading.selected i ↔
      Q.reading.signatureReading.selected (axisMap i)
  /-- Coordinates agree with the explicit object map. -/
  coordinate_eq : ∀ A i,
    coordinateEquiv i (P.reading.signatureReading.coordinate A i) =
      Q.reading.signatureReading.coordinate (objectMap A) (axisMap i)

namespace SignatureGraphCode

/-- Assemble signature axis and coordinate graphs into completed local
transport data. -/
def assemble {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (code : SignatureGraphCode P Q objectMap) :
    SignatureTransportSupply P Q objectMap where
  axisMap := code.1.axis.assemble
  coordinateEquiv := code.1.coordinate.assemble
  axis_selected_iff := code.2.axis_selected_iff
  coordinate_eq := code.2.coordinate_eq

/-- Read completed local signature transport into independent axis and
coordinate graph codes. -/
noncomputable def read {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (supply : SignatureTransportSupply P Q objectMap) :
    SignatureGraphCode P Q objectMap := by
  let axis := PrimitiveFunctionGraph.GraphCode.read supply.axisMap
  have axis_eq : axis.assemble = supply.axisMap :=
    PrimitiveFunctionGraph.GraphCode.assemble_read _
  let coordinate := IndexedEquivGraphCode.reindex axis_eq
    (IndexedEquivGraphCode.read supply.coordinateEquiv)
  refine ⟨⟨axis, coordinate⟩, ?_⟩
  constructor
  · intro i
    rw [axis_eq]
    exact supply.axis_selected_iff i
  · intro A i
    have value_heq : HEq
        (coordinate.assemble i
          (P.reading.signatureReading.coordinate A i))
        (supply.coordinateEquiv i
          (P.reading.signatureReading.coordinate A i)) := by
      apply HEq.trans
        (IndexedEquivGraphCode.reindex_assemble_apply_heq axis_eq
          (IndexedEquivGraphCode.read supply.coordinateEquiv) i
          (P.reading.signatureReading.coordinate A i))
      have family_eq := congrFun
        (IndexedEquivGraphCode.assemble_read supply.coordinateEquiv) i
      exact heq_of_eq (congrArg
        (fun equivalence => equivalence
          (P.reading.signatureReading.coordinate A i)) family_eq)
    have target_heq : HEq
        (Q.reading.signatureReading.coordinate
          (objectMap A) (supply.axisMap i))
        (Q.reading.signatureReading.coordinate
          (objectMap A) (axis.assemble i)) :=
      dependent_apply_heq
        (fun j => Q.reading.signatureReading.coordinate (objectMap A) j)
        (congrFun axis_eq i).symm
    exact eq_of_heq (HEq.trans value_heq
      (HEq.trans (heq_of_eq (supply.coordinate_eq A i)) target_heq))

/-- Signature graph codes are determined by the assembled axis map and
coordinate family; their remaining fields are propositions. -/
theorem ext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {first second : SignatureGraphCode P Q objectMap}
    (axis : first.1.axis = second.1.axis)
    (coordinate : HEq first.1.coordinate second.1.coordinate) :
    first = second := by
  cases first with
  | mk firstData firstLaw =>
      cases second with
      | mk secondData secondLaw =>
          cases firstData
          cases secondData
          cases axis
          cases coordinate
          rfl

/-- Completed signature supplies are determined by their two computational
families. -/
theorem supply_ext {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {first second : SignatureTransportSupply P Q objectMap}
    (axis : first.axisMap = second.axisMap)
    (coordinate : HEq first.coordinateEquiv second.coordinateEquiv) :
    first = second := by
  cases first
  cases second
  cases axis
  cases coordinate
  rfl

/-- Reading after signature assembly recovers both dependent graph families. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (code : SignatureGraphCode P Q objectMap) :
    read code.assemble = code := by
  apply ext
  · exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · cases code with
    | mk data law =>
        cases data with
        | mk axis coordinate =>
            simp only [read, assemble]
            apply HEq.trans
              (IndexedEquivGraphCode.reindex_heq
                (PrimitiveFunctionGraph.GraphCode.assemble_read axis.assemble)
                (IndexedEquivGraphCode.read coordinate.assemble))
            exact heq_of_eq (IndexedEquivGraphCode.read_assemble coordinate)

/-- Assembly after signature reading recovers both completed families. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (supply : SignatureTransportSupply P Q objectMap) :
    (read supply).assemble = supply := by
  apply supply_ext
  · exact PrimitiveFunctionGraph.GraphCode.assemble_read _
  · simp only [read, assemble]
    apply HEq.trans
      (IndexedEquivGraphCode.reindex_assemble_heq
        (PrimitiveFunctionGraph.GraphCode.assemble_read supply.axisMap)
        (IndexedEquivGraphCode.read supply.coordinateEquiv))
    exact heq_of_eq (IndexedEquivGraphCode.assemble_read _)

/-- Exact Cycle 70 equivalence between signature graph codes and completed
local signature transport. -/
noncomputable def equivSupply {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    {objectMap : ArchitectureObject U → ArchitectureObject U} :
    SignatureGraphCode P Q objectMap ≃
      SignatureTransportSupply P Q objectMap where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity completed signature transport. -/
def supplyId {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    SignatureTransportSupply P P _root_.id where
  axisMap := _root_.id
  coordinateEquiv _ := Equiv.refl _
  axis_selected_iff _ := Iff.rfl
  coordinate_eq _ _ := rfl

/-- Componentwise composition of completed local signature transports. -/
def supplyComp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (first : SignatureTransportSupply P Q firstObject)
    (second : SignatureTransportSupply Q R secondObject) :
    SignatureTransportSupply P R (secondObject ∘ firstObject) where
  axisMap := second.axisMap ∘ first.axisMap
  coordinateEquiv i :=
    (first.coordinateEquiv i).trans
      (second.coordinateEquiv (first.axisMap i))
  axis_selected_iff i :=
    (first.axis_selected_iff i).trans
      (second.axis_selected_iff (first.axisMap i))
  coordinate_eq A i := by
    simp only [Equiv.trans_apply, Function.comp_apply]
    rw [first.coordinate_eq A i]
    exact second.coordinate_eq (firstObject A) (first.axisMap i)

/-- Identity law-bearing signature graph code. -/
noncomputable def id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    SignatureGraphCode P P _root_.id :=
  read (supplyId P)

/-- Composition of law-bearing signature graph codes. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (first : SignatureGraphCode P Q firstObject)
    (second : SignatureGraphCode Q R secondObject) :
    SignatureGraphCode P R (secondObject ∘ firstObject) :=
  read (supplyComp first.assemble second.assemble)

/-- Signature assembly preserves componentwise composition. -/
@[simp]
theorem assemble_comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    {firstObject secondObject : ArchitectureObject U → ArchitectureObject U}
    (first : SignatureGraphCode P Q firstObject)
    (second : SignatureGraphCode Q R secondObject) :
    (comp first second).assemble =
      supplyComp first.assemble second.assemble :=
  assemble_read _

end SignatureGraphCode

/-! ## Actual complete-geometry component readings -/

namespace CompleteGeometryRemainingComponentCode

/-- Extract the existing realization-supply part of an actual complete
geometry morphism.  This is an output target for graph assembly, not a field
of the graph code. -/
def realizationSupply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    RealizationTransportSupply G.core H.core morphism.base where
  supportComp := morphism.geometry.supportComp
  axisComp := morphism.geometry.axisComp
  observableComp := morphism.geometry.observableComp
  supportReads := morphism.geometry.supportReads
  axisReads := morphism.geometry.axisReads
  observableReads := morphism.geometry.observableReads
  support_naturality := morphism.geometry.support_naturality
  axis_naturality := morphism.geometry.axis_naturality
  observable_naturality := morphism.geometry.observable_naturality

/-- Read all three actual realization families and their laws into one Cycle
70 graph code. -/
noncomputable def realization {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    RealizationGraphCode G.core H.core morphism.base :=
  RealizationGraphCode.read (realizationSupply morphism)

/-- Joint realization assembly recovers every actual comparison family and
its reading/naturality laws. -/
@[simp]
theorem realization_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (realization morphism).assemble = realizationSupply morphism :=
  RealizationGraphCode.assemble_read _

/-- Read the actual operation family into the Cycle 70 two-endpoint graph
presentation.  The ambient endpoint map is the actual object map, but no
completed geometry morphism is retained in the resulting code. -/
noncomputable def operation {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
  BiIndexedFunctionGraphCode morphism.base.upper.objectMap
      morphism.base.upper.objectMap
      G.core.reading.operationReading.Op
      H.core.reading.operationReading.Op :=
  BiIndexedFunctionGraphCode.read
    (fun A B op => morphism.base.upper.operationMap (A := A) (B := B) op)

/-- Operation-family assembly recovers the actual dependent operation map. -/
theorem operation_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    ∀ A B op, (operation morphism).assemble A B op =
      morphism.base.upper.operationMap (A := A) (B := B) op := by
  intro A B op
  exact congrFun
    (PrimitiveFunctionGraph.GraphCode.assemble_read
      (fun op : G.core.reading.operationReading.Op A B =>
        morphism.base.upper.operationMap (A := A) (B := B) op)) op

/-- The tagged operation graph is the existing complete-map operation field. -/
theorem operation_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (operation morphism).taggedForward =
      (readCompleteMapGraphs morphism).operation := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [BiIndexedFunctionGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk A tail =>
      cases tail with
      | mk B op =>
          simp only [BiIndexedFunctionGraphCode.taggedFunction,
            readCompleteMapGraphs,
            PrimitiveFunctionGraph.GraphCode.assemble_read, operationMap]
          rw [operation_assemble]

/-- The actual operation reading satisfies the independently stated Cycle 70
naturality law. -/
noncomputable def lawfulOperation {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    { code : BiIndexedFunctionGraphCode morphism.base.upper.objectMap
        morphism.base.upper.objectMap
        G.core.reading.operationReading.Op
        H.core.reading.operationReading.Op //
      IsOperationNatural G.core H.core morphism.base.upper.objectMap
        morphism.base.upper.configurationMap code.assemble } := by
  refine ⟨operation morphism, ?_⟩
  intro A B op
  rw [operation_assemble]
  exact morphism.base.upper.operation_naturality op

/-- Lawful-family assembly of the actual operation reading recovers the
operation map and its naturality proof as one subtype value. -/
theorem lawfulOperation_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (BiIndexedFunctionGraphCode.equivLawfulFamily
      (IsOperationNatural G.core H.core morphism.base.upper.objectMap
        morphism.base.upper.configurationMap)
      (lawfulOperation morphism)).1 =
      (fun A B op =>
        morphism.base.upper.operationMap (A := A) (B := B) op) := by
  funext A B op
  exact operation_assemble morphism A B op

/-- Read the invariant-index map as an independent primitive graph. -/
noncomputable def invariant {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveFunctionGraph.GraphCode
      G.core.reading.invariantReading.Index
      H.core.reading.invariantReading.Index :=
  PrimitiveFunctionGraph.GraphCode.read morphism.base.upper.invariantMap

/-- Invariant graph assembly recovers the actual invariant-index map. -/
@[simp]
theorem invariant_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (invariant morphism).assemble = morphism.base.upper.invariantMap :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- The independent invariant graph is the existing complete-map field. -/
theorem invariant_eq_completeGraph {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    invariant morphism = (readCompleteMapGraphs morphism).invariant := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [invariant_assemble]
  simp [readCompleteMapGraphs]

/-- The actual invariant graph satisfies the independently stated transport
law rather than storing the completed invariant map. -/
noncomputable def lawfulInvariant {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    { code : PrimitiveFunctionGraph.GraphCode
        G.core.reading.invariantReading.Index
        H.core.reading.invariantReading.Index //
      IsInvariantTransport G.core H.core morphism.base.upper.objectMap
        code.assemble } := by
  refine ⟨invariant morphism, ?_⟩
  intro i
  rw [invariant_assemble]
  exact morphism.base.upper.invariant_transport i

/-- Lawful graph assembly recovers the actual invariant-index function. -/
theorem lawfulInvariant_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (graphEquivLawfulFunction
      (IsInvariantTransport G.core H.core morphism.base.upper.objectMap)
      (lawfulInvariant morphism)).1 = morphism.base.upper.invariantMap :=
  invariant_assemble morphism

/-- Read the signature-axis map as an independent primitive graph. -/
noncomputable def signatureAxis {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    PrimitiveFunctionGraph.GraphCode
      G.core.reading.signatureReading.Axis
      H.core.reading.signatureReading.Axis :=
  PrimitiveFunctionGraph.GraphCode.read morphism.base.upper.axisMap

/-- Signature-axis graph assembly recovers the actual axis map. -/
@[simp]
theorem signatureAxis_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (signatureAxis morphism).assemble = morphism.base.upper.axisMap :=
  PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- The independent signature-axis graph is the existing complete-map field. -/
theorem signatureAxis_eq_completeGraph {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    signatureAxis morphism =
      (readCompleteMapGraphs morphism).signatureAxis := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [signatureAxis_assemble]
  simp [readCompleteMapGraphs]

/-- Read the actual coordinate-equivalence family over the independently read
signature-axis graph. -/
noncomputable def signatureCoordinate {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedEquivGraphCode (signatureAxis morphism).assemble
      G.core.reading.signatureReading.Coordinate
      H.core.reading.signatureReading.Coordinate := by
  exact IndexedEquivGraphCode.reindex (signatureAxis_assemble morphism)
    (IndexedEquivGraphCode.read morphism.base.upper.coordinateEquiv)

/-- Read the actual signature axis, coordinate equivalences, and their two
compatibility laws into one independent Cycle 70 code. -/
noncomputable def signature {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    SignatureGraphCode G.core H.core morphism.base.upper.objectMap := by
  let axis := signatureAxis morphism
  have axis_eq : axis.assemble = morphism.base.upper.axisMap :=
    signatureAxis_assemble morphism
  refine ⟨⟨axis, signatureCoordinate morphism⟩, ?_⟩
  constructor
  · intro i
    rw [axis_eq]
    exact morphism.base.upper.axis_selected_iff i
  · intro A i
    have value_heq : HEq
        ((signatureCoordinate morphism).assemble i
          (G.core.reading.signatureReading.coordinate A i))
        (morphism.base.upper.coordinateEquiv i
          (G.core.reading.signatureReading.coordinate A i)) := by
      apply HEq.trans
        (IndexedEquivGraphCode.reindex_assemble_apply_heq axis_eq
          (IndexedEquivGraphCode.read
            morphism.base.upper.coordinateEquiv) i
          (G.core.reading.signatureReading.coordinate A i))
      have family_eq := congrFun
        (IndexedEquivGraphCode.assemble_read
          morphism.base.upper.coordinateEquiv) i
      exact heq_of_eq (congrArg
        (fun equivalence => equivalence
          (G.core.reading.signatureReading.coordinate A i))
        family_eq)
    have actual_eq := morphism.base.upper.coordinate_eq A i
    have target_heq : HEq
        (H.core.reading.signatureReading.coordinate
          (morphism.base.upper.objectMap A) (morphism.base.upper.axisMap i))
        (H.core.reading.signatureReading.coordinate
          (morphism.base.upper.objectMap A) (axis.assemble i)) := by
      exact dependent_apply_heq
        (fun j => H.core.reading.signatureReading.coordinate
          (morphism.base.upper.objectMap A) j)
        (congrFun axis_eq i).symm
    exact eq_of_heq
      (HEq.trans value_heq (HEq.trans (heq_of_eq actual_eq) target_heq))

/-- Signature-code axis assembly recovers the actual signature-axis map. -/
@[simp]
theorem signature_axis_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (signature morphism).1.axis.assemble = morphism.base.upper.axisMap := by
  simpa only [signature] using signatureAxis_assemble morphism

/-- Signature-code coordinate assembly recovers the actual dependent
coordinate-equivalence family after transport along the axis equality. -/
theorem signature_coordinate_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    HEq (signature morphism).1.coordinate.assemble
      morphism.base.upper.coordinateEquiv := by
  have recovered : HEq (signatureCoordinate morphism).assemble
      morphism.base.upper.coordinateEquiv := by
    apply HEq.trans
      (IndexedEquivGraphCode.reindex_assemble_heq
        (signatureAxis_assemble morphism)
        (IndexedEquivGraphCode.read morphism.base.upper.coordinateEquiv))
    exact heq_of_eq (IndexedEquivGraphCode.assemble_read _)
  simpa only [signature] using recovered

/-- The tagged coordinate graph over the independently assembled axis is the
coordinate field of the accepted complete-map graph surface. -/
theorem signatureCoordinate_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (signatureCoordinate morphism).taggedForward =
      (readCompleteMapGraphs morphism).coordinate := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedEquivGraphCode.assemble_taggedForward]
  rw [← CompleteGeometryDependentAlgebraicCode.coordinate_taggedForward morphism,
    IndexedEquivGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk i coordinateValue =>
      simp only [IndexedEquivGraphCode.taggedFunction_apply]
      apply Sigma.ext (congrFun (signatureAxis_assemble morphism) i)
      exact IndexedEquivGraphCode.reindex_assemble_apply_heq
        (signatureAxis_assemble morphism)
        (IndexedEquivGraphCode.read morphism.base.upper.coordinateEquiv)
        i coordinateValue

/-- Read the context-indexed geometry-support family into one-index graph
codes over the actual context-object action. -/
noncomputable def support {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedFunctionGraphCode (equationContextForwardMap morphism)
      (fun W : G.site.category => W.ctx.Support)
      (fun W : H.site.category => W.ctx.Support) :=
  IndexedFunctionGraphCode.read morphism.geometry.supportComp

/-- The support projection of the joint realization code is the standalone
support reading. -/
theorem realization_support {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (realization morphism).1.support = support morphism :=
  rfl

/-- Support-family assembly recovers the actual support comparison. -/
@[simp]
theorem support_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (support morphism).assemble = morphism.geometry.supportComp :=
  IndexedFunctionGraphCode.assemble_read _

/-- The tagged support graph is the existing complete-map support field. -/
theorem support_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (support morphism).taggedForward =
      (readCompleteMapGraphs morphism).support := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedFunctionGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk W supportValue =>
      simp [IndexedFunctionGraphCode.taggedFunction,
        CompleteGeometryFunctionGraphSeparation.taggedMap,
        supportMap, readCompleteMapGraphs, support_assemble]

/-- Read the context-indexed geometry-axis family into one-index graph codes. -/
noncomputable def geometryAxis {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedFunctionGraphCode (equationContextForwardMap morphism)
      (fun W : G.site.category => W.ctx.Axis)
      (fun W : H.site.category => W.ctx.Axis) :=
  IndexedFunctionGraphCode.read morphism.geometry.axisComp

/-- The axis projection of the joint realization code is the standalone axis
reading. -/
theorem realization_axis {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (realization morphism).1.axis = geometryAxis morphism :=
  rfl

/-- Geometry-axis family assembly recovers the actual comparison. -/
@[simp]
theorem geometryAxis_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (geometryAxis morphism).assemble = morphism.geometry.axisComp :=
  IndexedFunctionGraphCode.assemble_read _

/-- The tagged geometry-axis graph is the existing complete-map field. -/
theorem geometryAxis_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (geometryAxis morphism).taggedForward =
      (readCompleteMapGraphs morphism).geometryAxis := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedFunctionGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk W axisValue =>
      simp [IndexedFunctionGraphCode.taggedFunction,
        CompleteGeometryFunctionGraphSeparation.taggedMap,
        geometryAxisMap, readCompleteMapGraphs, geometryAxis_assemble]

/-- Read the context-indexed geometry-observable family into one-index graph
codes over the actual context-object action. -/
noncomputable def geometryObservable {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IndexedFunctionGraphCode (equationContextForwardMap morphism)
      (fun W : G.site.category => W.ctx.Observable)
      (fun W : H.site.category => W.ctx.Observable) :=
  IndexedFunctionGraphCode.read morphism.geometry.observableComp

/-- The observable projection of the joint realization code is the standalone
observable reading. -/
theorem realization_observable {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (realization morphism).1.observable = geometryObservable morphism :=
  rfl

/-- Geometry-observable family assembly recovers the actual comparison. -/
@[simp]
theorem geometryObservable_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (geometryObservable morphism).assemble = morphism.geometry.observableComp :=
  IndexedFunctionGraphCode.assemble_read _

/-- The tagged geometry-observable graph is the existing complete-map field. -/
theorem geometryObservable_taggedForward {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (geometryObservable morphism).taggedForward =
      (readCompleteMapGraphs morphism).geometryObservable := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [IndexedFunctionGraphCode.assemble_taggedForward]
  funext value
  cases value with
  | mk W observableValue =>
      simp [IndexedFunctionGraphCode.taggedFunction,
        CompleteGeometryFunctionGraphSeparation.taggedMap,
        geometryObservableMap, readCompleteMapGraphs,
        geometryObservable_assemble]

/-- The raw-transport equality is the remaining raw coherence premise of
Cycle 70.  It contains no morphism data beyond the independently assembled
core and coefficient maps. -/
def IsRawTransportCoherent {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : PackageTotalHom G.core H.core)
    (coefficientHom : G.Coefficient →+* H.Coefficient) : Prop :=
  H.raw = rawTransport baseHom coefficientHom

/-- Literal inequality of the two raw endpoints is the negative instance for
raw-transport coherence. -/
theorem not_isRawTransportCoherent_of_ne {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    (failure : H.raw ≠ rawTransport baseHom coefficientHom) :
    ¬ IsRawTransportCoherent G H baseHom coefficientHom :=
  failure

/-- Actual complete geometry supplies the raw-transport coherence law. -/
theorem rawTransport_coherent {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    IsRawTransportCoherent G H morphism.base morphism.geometry.coefficientHom :=
  morphism.geometry.raw_eq

/-- Raw coherence contains the identity maps, so it is closed under the
identity operation used by complete geometry. -/
theorem rawTransport_coherent_id {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) :
    IsRawTransportCoherent G G (PackageTotalHom.id G.core)
      (RingHom.id G.Coefficient) :=
  (rawTransport_id G).symm

/-- Raw coherence is closed under complete-geometry composition with the
composite core and coefficient maps. -/
theorem rawTransport_coherent_comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : IsRawTransportCoherent G H firstBase firstCoefficient)
    (second : IsRawTransportCoherent H K secondBase secondCoefficient) :
    IsRawTransportCoherent G K
      (PackageTotalHom.comp firstBase secondBase)
      (secondCoefficient.comp firstCoefficient) := by
  calc
    K.raw = rawTransport secondBase secondCoefficient := second
    _ = rawReindex secondBase (H.raw.baseChange secondCoefficient) := rfl
    _ = rawReindex secondBase
        ((rawTransport firstBase firstCoefficient).baseChange
          secondCoefficient) := by rw [first]
    _ = rawTransport (PackageTotalHom.comp firstBase secondBase)
        (secondCoefficient.comp firstCoefficient) :=
      (rawTransport_comp firstBase secondBase firstCoefficient
        secondCoefficient).symm

/-! ## Unified remaining-component code and common-surface recovery -/

/-- The Cycle 70 remaining-component certificate over independently supplied
core and coefficient maps.  It stores graph codes and local laws only; in
particular it has no `GeometryTotalHom` field. -/
structure RemainingComponentCode {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : PackageTotalHom G.core H.core)
    (coefficientHom : G.Coefficient →+* H.Coefficient) where
  /-- Lawful graph family for binary operations. -/
  operation : { code : BiIndexedFunctionGraphCode
      baseHom.upper.objectMap baseHom.upper.objectMap
      (fun A B => G.core.reading.operationReading.Op A B)
      (fun A B => H.core.reading.operationReading.Op A B) //
    IsOperationNatural G.core H.core baseHom.upper.objectMap
      baseHom.upper.configurationMap code.assemble }
  /-- Lawful graph for invariant indices. -/
  invariant : { code : PrimitiveFunctionGraph.GraphCode
      G.core.reading.invariantReading.Index
      H.core.reading.invariantReading.Index //
    IsInvariantTransport G.core H.core baseHom.upper.objectMap code.assemble }
  /-- Signature axis and dependent coordinate graphs with their laws. -/
  signature : SignatureGraphCode G.core H.core baseHom.upper.objectMap
  /-- Three law-bearing realization graph families. -/
  realization : RealizationGraphCode G.core H.core baseHom
  /-- Raw transport is coherent with the supplied maps. -/
  rawCoherent : IsRawTransportCoherent G H baseHom coefficientHom

/-- Completed output of remaining-component assembly.  It contains the local
families and laws but still no coverage, overlap, or `GeometryTotalHom`. -/
structure RemainingComponentSupply {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U)
    (baseHom : PackageTotalHom G.core H.core)
    (coefficientHom : G.Coefficient →+* H.Coefficient) where
  /-- Completed lawful operation family. -/
  operation : { family : ∀ A B,
      G.core.reading.operationReading.Op A B →
        H.core.reading.operationReading.Op
          (baseHom.upper.objectMap A) (baseHom.upper.objectMap B) //
    IsOperationNatural G.core H.core baseHom.upper.objectMap
      baseHom.upper.configurationMap family }
  /-- Completed lawful invariant-index function. -/
  invariant : { function : G.core.reading.invariantReading.Index →
      H.core.reading.invariantReading.Index //
    IsInvariantTransport G.core H.core baseHom.upper.objectMap function }
  /-- Completed local signature transport. -/
  signature : SignatureTransportSupply G.core H.core
    baseHom.upper.objectMap
  /-- Completed realization transport supply. -/
  realization : RealizationTransportSupply G.core H.core baseHom
  /-- Raw endpoint coherence retained as a separate direction hypothesis. -/
  rawCoherent : IsRawTransportCoherent G H baseHom coefficientHom

namespace RemainingComponentCode

/-- Assemble every graph-presented field of the unified relative code. -/
def assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    (code : RemainingComponentCode G H baseHom coefficientHom) :
    RemainingComponentSupply G H baseHom coefficientHom where
  operation := ⟨code.operation.1.assemble, code.operation.2⟩
  invariant := ⟨code.invariant.1.assemble, code.invariant.2⟩
  signature := code.signature.assemble
  realization := code.realization.assemble
  rawCoherent := code.rawCoherent

/-- Read a completed relative supply back into graph codes without retaining
any completed global morphism. -/
noncomputable def read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    (supply : RemainingComponentSupply G H baseHom coefficientHom) :
    RemainingComponentCode G H baseHom coefficientHom where
  operation := ⟨BiIndexedFunctionGraphCode.read supply.operation.1, by
    rw [BiIndexedFunctionGraphCode.assemble_read]
    exact supply.operation.2⟩
  invariant := ⟨PrimitiveFunctionGraph.GraphCode.read supply.invariant.1, by
    rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
    exact supply.invariant.2⟩
  signature := SignatureGraphCode.read supply.signature
  realization := RealizationGraphCode.read supply.realization
  rawCoherent := supply.rawCoherent

/-- Unified relative codes are determined by their five component codes or
proofs. -/
theorem ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    {first second : RemainingComponentCode G H baseHom coefficientHom}
    (operation : first.operation = second.operation)
    (invariant : first.invariant = second.invariant)
    (signature : first.signature = second.signature)
    (realization : first.realization = second.realization) :
    first = second := by
  cases first
  cases second
  cases operation
  cases invariant
  cases signature
  cases realization
  rfl

/-- Unified completed supplies are determined by their four computational
families; raw coherence and all local laws are propositions. -/
theorem supply_ext {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    {first second : RemainingComponentSupply G H baseHom coefficientHom}
    (operation : first.operation = second.operation)
    (invariant : first.invariant = second.invariant)
    (signature : first.signature = second.signature)
    (realization : first.realization = second.realization) :
    first = second := by
  cases first
  cases second
  cases operation
  cases invariant
  cases signature
  cases realization
  rfl

/-- First unified inverse law. -/
@[simp]
theorem read_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    (code : RemainingComponentCode G H baseHom coefficientHom) :
    read code.assemble = code := by
  apply ext
  · apply Subtype.ext
    exact BiIndexedFunctionGraphCode.read_assemble _
  · apply Subtype.ext
    exact PrimitiveFunctionGraph.GraphCode.read_assemble _
  · exact SignatureGraphCode.read_assemble _
  · exact RealizationGraphCode.read_assemble _

/-- Second unified inverse law. -/
@[simp]
theorem assemble_read {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient}
    (supply : RemainingComponentSupply G H baseHom coefficientHom) :
    (read supply).assemble = supply := by
  apply supply_ext
  · apply Subtype.ext
    exact BiIndexedFunctionGraphCode.assemble_read _
  · apply Subtype.ext
    exact PrimitiveFunctionGraph.GraphCode.assemble_read _
  · exact SignatureGraphCode.assemble_read _
  · exact RealizationGraphCode.assemble_read _

/-- Exact equivalence between unified graph codes and their completed local
supplies, relative to the explicit ambient core and coefficient maps. -/
noncomputable def equivSupply {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    {baseHom : PackageTotalHom G.core H.core}
    {coefficientHom : G.Coefficient →+* H.Coefficient} :
    RemainingComponentCode G H baseHom coefficientHom ≃
      RemainingComponentSupply G H baseHom coefficientHom where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity unified remaining-component code. -/
noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    RemainingComponentCode G G (PackageTotalHom.id G.core)
      (RingHom.id G.Coefficient) where
  operation := LawfulOperationGraphCode.id G.core
  invariant := LawfulInvariantGraphCode.id G.core
  signature := SignatureGraphCode.id G.core
  realization := RealizationGraphCode.id G.core
  rawCoherent := rawTransport_coherent_id G

/-- Componentwise composition of unified law-bearing relative codes. -/
noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : RemainingComponentCode G H firstBase firstCoefficient)
    (second : RemainingComponentCode H K secondBase secondCoefficient) :
    RemainingComponentCode G K (PackageTotalHom.comp firstBase secondBase)
      (secondCoefficient.comp firstCoefficient) where
  operation := LawfulOperationGraphCode.comp
    (firstObject := firstBase.upper.objectMap)
    (secondObject := secondBase.upper.objectMap)
    (firstConfiguration := firstBase.upper.configurationMap)
    (secondConfiguration := secondBase.upper.configurationMap)
    first.operation second.operation
  invariant := LawfulInvariantGraphCode.comp
    (firstObject := firstBase.upper.objectMap)
    (secondObject := secondBase.upper.objectMap)
    first.invariant second.invariant
  signature := SignatureGraphCode.comp
    (firstObject := firstBase.upper.objectMap)
    (secondObject := secondBase.upper.objectMap)
    first.signature second.signature
  realization := RealizationGraphCode.comp first.realization second.realization
  rawCoherent := rawTransport_coherent_comp first.rawCoherent second.rawCoherent

/-- The operation projection of unified composition assembles pointwise. -/
theorem assemble_comp_operation {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : RemainingComponentCode G H firstBase firstCoefficient)
    (second : RemainingComponentCode H K secondBase secondCoefficient) :
    (comp first second).operation.1.assemble = fun A B op =>
      second.operation.1.assemble
        (firstBase.upper.objectMap A) (firstBase.upper.objectMap B)
        (first.operation.1.assemble A B op) := by
  change (LawfulOperationGraphCode.comp first.operation
      second.operation).1.assemble = _
  exact LawfulOperationGraphCode.assemble_comp _ _

/-- The invariant projection of unified composition assembles by function
composition. -/
theorem assemble_comp_invariant {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : RemainingComponentCode G H firstBase firstCoefficient)
    (second : RemainingComponentCode H K secondBase secondCoefficient) :
    (comp first second).invariant.1.assemble =
      second.invariant.1.assemble ∘ first.invariant.1.assemble := by
  change (LawfulInvariantGraphCode.comp first.invariant
      second.invariant).1.assemble = _
  exact LawfulInvariantGraphCode.assemble_comp _ _

/-- The signature projection of unified composition assembles to local supply
composition. -/
theorem assemble_comp_signature {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : RemainingComponentCode G H firstBase firstCoefficient)
    (second : RemainingComponentCode H K secondBase secondCoefficient) :
    (comp first second).signature.assemble =
      SignatureGraphCode.supplyComp first.signature.assemble
        second.signature.assemble := by
  change (SignatureGraphCode.comp first.signature
      second.signature).assemble = _
  exact SignatureGraphCode.assemble_comp _ _

/-- The realization projection of unified composition assembles to supply
composition. -/
theorem assemble_comp_realization {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    {firstBase : PackageTotalHom G.core H.core}
    {secondBase : PackageTotalHom H.core K.core}
    {firstCoefficient : G.Coefficient →+* H.Coefficient}
    {secondCoefficient : H.Coefficient →+* K.Coefficient}
    (first : RemainingComponentCode G H firstBase firstCoefficient)
    (second : RemainingComponentCode H K secondBase secondCoefficient) :
    (comp first second).realization.assemble =
      RealizationGraphCode.supplyComp first.realization.assemble
        second.realization.assemble := by
  change (RealizationGraphCode.comp first.realization
      second.realization).assemble = _
  exact RealizationGraphCode.assemble_comp _ _

end RemainingComponentCode

/-- Read every remaining component of an actual complete geometry morphism
into the unified graph-and-law code. -/
noncomputable def readRemaining {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    RemainingComponentCode G H morphism.base morphism.geometry.coefficientHom where
  operation := lawfulOperation morphism
  invariant := lawfulInvariant morphism
  signature := signature morphism
  realization := realization morphism
  rawCoherent := rawTransport_coherent morphism

/-- Common-surface recovery record for all graph-valued fields assembled by
the unified remaining-component code. -/
structure CompleteGraphRecovery {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H)
    (code : RemainingComponentCode G H morphism.base
      morphism.geometry.coefficientHom) : Prop where
  operation : code.operation.1.taggedForward =
    (readCompleteMapGraphs morphism).operation
  invariant : code.invariant.1 = (readCompleteMapGraphs morphism).invariant
  signatureAxis : code.signature.1.axis =
    (readCompleteMapGraphs morphism).signatureAxis
  coordinate : code.signature.1.coordinate.taggedForward =
    (readCompleteMapGraphs morphism).coordinate
  support : code.realization.1.support.taggedForward =
    (readCompleteMapGraphs morphism).support
  geometryAxis : code.realization.1.axis.taggedForward =
    (readCompleteMapGraphs morphism).geometryAxis
  geometryObservable : code.realization.1.observable.taggedForward =
    (readCompleteMapGraphs morphism).geometryObservable

/-- Reading an actual complete morphism recovers every corresponding field of
the accepted complete-map graph surface in one theorem. -/
theorem readRemaining_completeGraphRecovery {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    CompleteGraphRecovery morphism (readRemaining morphism) where
  operation := operation_taggedForward morphism
  invariant := invariant_eq_completeGraph morphism
  signatureAxis := signatureAxis_eq_completeGraph morphism
  coordinate := signatureCoordinate_taggedForward morphism
  support := support_taggedForward morphism
  geometryAxis := geometryAxis_taggedForward morphism
  geometryObservable := geometryObservable_taggedForward morphism

end CompleteGeometryRemainingComponentCode

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence

end RemainingComponentGraphCoherence

end

end AAT.AG.LocalSemanticReconstruction
