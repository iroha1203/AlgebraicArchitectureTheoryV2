import ResearchLean.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence
import Mathlib.CategoryTheory.Category.Preorder
import Formal.Util.AssertStandardAxioms

/-!
# Thin-context and observable graph coherence

Cycle 69 of G-124 presents an equivalence between preorder categories without
storing functors, natural isomorphisms, or a completed category equivalence.
The raw layer contains only two Bool-valued graphs.  A separate proposition
says that they are total-functional, that their assembled object functions
preserve readable morphisms, and supplies both directions of the unit and
counit inequalities.

Those local equations assemble the forward and inverse functors, their unit
and counit natural isomorphisms, and hence an actual category equivalence.
Reading and assembly are inverse in both directions.  The construction uses
the preorder reading itself: isomorphic objects need not be literally equal.

The second half connects this context assembly to the observable ring family
and restriction naturality of the actual equation-system transport.

## Specification and implementation notes

This module implements the Cycle 69 fixed obligation recorded in the G-124
research report.  Its main declarations are the two graph-code structures,
their equivalence and natural-isomorphism assemblers, and their complete-
geometry recovery theorems.  The remaining declarations are API lemmas or
refutation fixtures for those main declarations.  Totality, monotonicity,
unit/counit inequalities, and restriction naturality are precisely the local
premises selected by that obligation.

The data/Prop split is intentional: storing a completed functor, equivalence,
or natural isomorphism would make recovery circular.  Preorder categories are
used instead of object equality because the fixed obligation asks for genuine
unit and counit isomorphisms.  The joint observable code is dependent on its
own assembled context functor; accepting an unrelated functor was rejected
because it would not certify one coherent reading.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory GeometryTransport

noncomputable section

namespace ContextObservableGraphCoherence

universe u v w

open CompleteGeometryFunctionGraphSeparation
open DependentAlgebraicGraphCoherence

/-! ## Equivalences of preorder categories from object graphs -/

/-- Raw forward and backward object graphs for the Cycle 69 context main
construction.  The fixed obligation supplies no completed functor here. -/
structure ThinEquivalenceGraphData (C : Type u) (D : Type v) where
  /-- Forward raw datum selected by the Cycle 69 context presentation. -/
  forward : PrimitiveFunctionGraph.GraphData C D
  /-- Backward raw datum selected by the Cycle 69 context presentation. -/
  backward : PrimitiveFunctionGraph.GraphData D C

/-- Local premises for the Cycle 69 context main construction.  They are the
fixed obligation's totality, thin-morphism preservation, and two directions
of the unit and counit, kept separate from raw graph data. -/
structure IsThinEquivalenceGraphCode (data : ThinEquivalenceGraphData C D)
    [Preorder C] [Preorder D] : Prop where
  /-- Forward totality/functionality premise from the fixed obligation. -/
  forward_total : PrimitiveFunctionGraph.IsTotalFunctional data.forward
  /-- Backward totality/functionality premise from the fixed obligation. -/
  backward_total : PrimitiveFunctionGraph.IsTotalFunctional data.backward
  /-- Fixed premise that the assembled forward map preserves thin morphisms. -/
  forward_mono : Monotone
    (PrimitiveFunctionGraph.GraphCode.assemble
      (show PrimitiveFunctionGraph.GraphCode C D from
        ⟨data.forward, forward_total⟩))
  /-- Fixed premise that the assembled backward map preserves thin morphisms. -/
  backward_mono : Monotone
    (PrimitiveFunctionGraph.GraphCode.assemble
      (show PrimitiveFunctionGraph.GraphCode D C from
        ⟨data.backward, backward_total⟩))
  /-- Forward direction of the fixed unit-isomorphism premise. -/
  unit_hom : ∀ object,
    object ≤
      PrimitiveFunctionGraph.GraphCode.assemble
        (show PrimitiveFunctionGraph.GraphCode D C from
          ⟨data.backward, backward_total⟩)
        (PrimitiveFunctionGraph.GraphCode.assemble
          (show PrimitiveFunctionGraph.GraphCode C D from
            ⟨data.forward, forward_total⟩) object)
  /-- Reverse direction of the fixed unit-isomorphism premise. -/
  unit_inv : ∀ object,
    PrimitiveFunctionGraph.GraphCode.assemble
        (show PrimitiveFunctionGraph.GraphCode D C from
          ⟨data.backward, backward_total⟩)
        (PrimitiveFunctionGraph.GraphCode.assemble
          (show PrimitiveFunctionGraph.GraphCode C D from
            ⟨data.forward, forward_total⟩) object) ≤ object
  /-- Forward direction of the fixed counit-isomorphism premise. -/
  counit_hom : ∀ object,
    PrimitiveFunctionGraph.GraphCode.assemble
        (show PrimitiveFunctionGraph.GraphCode C D from
          ⟨data.forward, forward_total⟩)
        (PrimitiveFunctionGraph.GraphCode.assemble
          (show PrimitiveFunctionGraph.GraphCode D C from
            ⟨data.backward, backward_total⟩) object) ≤ object
  /-- Reverse direction of the fixed counit-isomorphism premise. -/
  counit_inv : ∀ object,
    object ≤
      PrimitiveFunctionGraph.GraphCode.assemble
        (show PrimitiveFunctionGraph.GraphCode C D from
          ⟨data.forward, forward_total⟩)
        (PrimitiveFunctionGraph.GraphCode.assemble
          (show PrimitiveFunctionGraph.GraphCode D C from
            ⟨data.backward, backward_total⟩) object)

/-- Input type of the Cycle 69 context main theorem: raw object graphs bundled
with exactly the local premises selected by the fixed obligation. -/
abbrev ThinEquivalenceGraphCode (C : Type u) (D : Type v)
    [Preorder C] [Preorder D] :=
  { data : ThinEquivalenceGraphData C D //
    IsThinEquivalenceGraphCode data }

namespace ThinEquivalenceGraphCode

/-- Constructor API for `ThinEquivalenceGraphCode`; it packages the fixed
forward-totality premise for primitive graph assembly. -/
def forwardCode {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) :
    PrimitiveFunctionGraph.GraphCode C D :=
  ⟨code.1.forward, code.2.forward_total⟩

/-- Constructor API for `ThinEquivalenceGraphCode`; it packages the fixed
backward-totality premise for primitive graph assembly. -/
def backwardCode {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) :
    PrimitiveFunctionGraph.GraphCode D C :=
  ⟨code.1.backward, code.2.backward_total⟩

/-- API lemma for `read`: proof irrelevance lets a read raw graph use the
Cycle 69 totality premise without changing the assembled function. -/
@[simp]
theorem assemble_read_val {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (function : C → D)
    (total : PrimitiveFunctionGraph.IsTotalFunctional
      (PrimitiveFunctionGraph.GraphCode.read function).1) :
    PrimitiveFunctionGraph.GraphCode.assemble
      (⟨(PrimitiveFunctionGraph.GraphCode.read function).1, total⟩ :
        PrimitiveFunctionGraph.GraphCode C D) = function := by
  have code_eq :
      (⟨(PrimitiveFunctionGraph.GraphCode.read function).1, total⟩ :
        PrimitiveFunctionGraph.GraphCode C D) =
        PrimitiveFunctionGraph.GraphCode.read function := by
    apply Subtype.ext
    rfl
  rw [code_eq]
  exact PrimitiveFunctionGraph.GraphCode.assemble_read _

/-- Extensionality API for the Cycle 69 code.  Its Prop-valued local premises
carry no additional data beyond the two raw graphs. -/
@[ext]
theorem ext {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    {first second : ThinEquivalenceGraphCode C D}
    (forward : first.1.forward = second.1.forward)
    (backward : first.1.backward = second.1.backward) : first = second := by
  apply Subtype.ext
  cases first with
  | mk firstData firstLaw =>
    cases second with
    | mk secondData secondLaw =>
      cases firstData
      cases secondData
      cases forward
      cases backward
      rfl

/-- Main-construction component: the fixed forward monotonicity premise turns
the assembled object graph into a thin-category functor. -/
def forwardFunctor {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : C ⥤ D where
  obj := code.forwardCode.assemble
  map f := homOfLE (code.2.forward_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Main-construction component: the fixed backward monotonicity premise turns
the assembled object graph into the inverse thin-category functor. -/
def backwardFunctor {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : D ⥤ C where
  obj := code.backwardCode.assemble
  map f := homOfLE (code.2.backward_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Main-construction component: the two unit inequalities required by the
fixed obligation become the unit natural isomorphism. -/
def unitIso {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) :
    Functor.id C ≅ code.forwardFunctor ⋙ code.backwardFunctor :=
  NatIso.ofComponents
    (fun object =>
      { hom := homOfLE (code.2.unit_hom object)
        inv := homOfLE (code.2.unit_inv object)
        hom_inv_id := Subsingleton.elim _ _
        inv_hom_id := Subsingleton.elim _ _ })
    (fun _ => Subsingleton.elim _ _)

/-- Main-construction component: the two counit inequalities required by the
fixed obligation become the counit natural isomorphism. -/
def counitIso {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) :
    code.backwardFunctor ⋙ code.forwardFunctor ≅ Functor.id D :=
  NatIso.ofComponents
    (fun object =>
      { hom := homOfLE (code.2.counit_hom object)
        inv := homOfLE (code.2.counit_inv object)
        hom_inv_id := Subsingleton.elim _ _
        inv_hom_id := Subsingleton.elim _ _ })
    (fun _ => Subsingleton.elim _ _)

/-- Cycle 69 main assembler from graph-presented thin functors and the fixed
unit/counit premises to an actual category equivalence. -/
def assemble {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : C ≌ D where
  functor := code.forwardFunctor
  inverse := code.backwardFunctor
  unitIso := code.unitIso
  counitIso := code.counitIso

/-- Evaluation API for the Cycle 69 assembler, exposing its connection to the
primitive forward graph without unfolding the functor. -/
@[simp]
theorem assemble_functor_obj {C : Type u} {D : Type v}
    [Preorder C] [Preorder D] (code : ThinEquivalenceGraphCode C D)
    (object : C) :
    code.assemble.functor.obj object = code.forwardCode.assemble object :=
  rfl

/-- Evaluation API for the Cycle 69 assembler, exposing its connection to the
primitive backward graph without unfolding the inverse functor. -/
@[simp]
theorem assemble_inverse_obj {C : Type u} {D : Type v}
    [Preorder C] [Preorder D] (code : ThinEquivalenceGraphCode C D)
    (object : D) :
    code.assemble.inverse.obj object = code.backwardCode.assemble object :=
  rfl

/-- Cycle 69 inverse construction: read an actual preorder-category
equivalence into independent object graphs and the selected local premises. -/
noncomputable def read {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (equivalence : C ≌ D) : ThinEquivalenceGraphCode C D :=
  ⟨{
    forward := (PrimitiveFunctionGraph.GraphCode.read equivalence.functor.obj).1
    backward := (PrimitiveFunctionGraph.GraphCode.read equivalence.inverse.obj).1 }, {
    forward_total := (PrimitiveFunctionGraph.GraphCode.read
      equivalence.functor.obj).2
    backward_total := (PrimitiveFunctionGraph.GraphCode.read
      equivalence.inverse.obj).2
    forward_mono := by
      intro first second relation
      simpa only [assemble_read_val] using
        leOfHom (equivalence.functor.map (homOfLE relation))
    backward_mono := by
      intro first second relation
      simpa only [assemble_read_val] using
        leOfHom (equivalence.inverse.map (homOfLE relation))
    unit_hom := fun object => by
      simpa only [assemble_read_val] using
        leOfHom (equivalence.unitIso.hom.app object)
    unit_inv := fun object => by
      simpa only [assemble_read_val] using
        leOfHom (equivalence.unitIso.inv.app object)
    counit_hom := fun object => by
      simpa only [assemble_read_val] using
        leOfHom (equivalence.counitIso.hom.app object)
    counit_inv := fun object => by
      simpa only [assemble_read_val] using
        leOfHom (equivalence.counitIso.inv.app object) }⟩

/-- First main inverse law for Cycle 69: reading the graph assembler recovers
the original code, including both raw graph presentations. -/
@[simp]
theorem read_assemble {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : read code.assemble = code := by
  apply ext
  · change (PrimitiveFunctionGraph.GraphCode.read
      code.assemble.functor.obj).1 = code.1.forward
    have equality : PrimitiveFunctionGraph.GraphCode.read
        code.assemble.functor.obj = code.forwardCode := by
      rw [show code.assemble.functor.obj = code.forwardCode.assemble by rfl]
      exact PrimitiveFunctionGraph.GraphCode.read_assemble _
    exact congrArg Subtype.val equality
  · change (PrimitiveFunctionGraph.GraphCode.read
      code.assemble.inverse.obj).1 = code.1.backward
    have equality : PrimitiveFunctionGraph.GraphCode.read
        code.assemble.inverse.obj = code.backwardCode := by
      rw [show code.assemble.inverse.obj = code.backwardCode.assemble by rfl]
      exact PrimitiveFunctionGraph.GraphCode.read_assemble _
    exact congrArg Subtype.val equality

/-- Second main inverse law for Cycle 69: assembly recovers any actual
thin-category equivalence read into the selected graph presentation. -/
@[simp]
theorem assemble_read {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (equivalence : C ≌ D) : (read equivalence).assemble = equivalence := by
  have functor_eq : (read equivalence).assemble.functor =
      equivalence.functor := by
    refine CategoryTheory.Functor.ext (fun object => ?_) ?_
    · change PrimitiveFunctionGraph.GraphCode.assemble
          (⟨(PrimitiveFunctionGraph.GraphCode.read
            equivalence.functor.obj).1, _⟩ :
              PrimitiveFunctionGraph.GraphCode C D) object = _
      exact congrFun (assemble_read_val equivalence.functor.obj _) object
    · intros
      exact Subsingleton.elim _ _
  have inverse_eq : (read equivalence).assemble.inverse =
      equivalence.inverse := by
    refine CategoryTheory.Functor.ext (fun object => ?_) ?_
    · change PrimitiveFunctionGraph.GraphCode.assemble
          (⟨(PrimitiveFunctionGraph.GraphCode.read
            equivalence.inverse.obj).1, _⟩ :
              PrimitiveFunctionGraph.GraphCode D C) object = _
      exact congrFun (assemble_read_val equivalence.inverse.obj _) object
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext functor_eq inverse_eq
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun functor => Functor.id C ≅ functor)
    rw [functor_eq, inverse_eq]
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun functor => functor ≅ Functor.id D)
    rw [functor_eq, inverse_eq]

/-- Cycle 69 principal context theorem, packaging the two inverse laws as an
explicit equivalence with the existing category-equivalence API. -/
noncomputable def equivEquivalence {C : Type u} {D : Type v}
    [Preorder C] [Preorder D] :
    ThinEquivalenceGraphCode C D ≃ (C ≌ D) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity constructor API for the Cycle 69 code, obtained by reading the
existing identity category equivalence rather than storing one in the code. -/
noncomputable def id (C : Type u) [Preorder C] :
    ThinEquivalenceGraphCode C C :=
  read CategoryTheory.Equivalence.refl

/-- Composition constructor API for the Cycle 69 code.  Both completed
equivalences are derived from the inputs before the composite is read back. -/
noncomputable def comp {C : Type u} {D : Type v} {E : Type w}
    [Preorder C] [Preorder D] [Preorder E]
    (first : ThinEquivalenceGraphCode C D)
    (second : ThinEquivalenceGraphCode D E) :
    ThinEquivalenceGraphCode C E :=
  read (first.assemble.trans second.assemble)

/-- Comparison API connecting code composition to the existing composition of
category equivalences; it supports the Cycle 69 closure laws below. -/
@[simp]
theorem assemble_comp {C : Type u} {D : Type v} {E : Type w}
    [Preorder C] [Preorder D] [Preorder E]
    (first : ThinEquivalenceGraphCode C D)
    (second : ThinEquivalenceGraphCode D E) :
    (comp first second).assemble = first.assemble.trans second.assemble :=
  assemble_read _

/-- Comparison API connecting the code identity to the existing identity
category equivalence; it supports the Cycle 69 unit laws below. -/
@[simp]
theorem assemble_id (C : Type u) [Preorder C] :
    (id C).assemble = CategoryTheory.Equivalence.refl :=
  assemble_read _

/-- Cycle 69 composition law at the raw forward-graph level.  Its order comes
from ordinary functor composition in the fixed obligation. -/
theorem comp_forward {C : Type u} {D : Type v} {E : Type w}
    [Preorder C] [Preorder D] [Preorder E]
    (first : ThinEquivalenceGraphCode C D)
    (second : ThinEquivalenceGraphCode D E) :
    (comp first second).1.forward =
      (PrimitiveFunctionGraph.GraphCode.comp
        first.forwardCode second.forwardCode).1 := by
  have code_eq : (comp first second).forwardCode =
      PrimitiveFunctionGraph.GraphCode.comp
        first.forwardCode second.forwardCode := by
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    change (comp first second).assemble.functor.obj =
      PrimitiveFunctionGraph.GraphCode.assemble
        (PrimitiveFunctionGraph.GraphCode.comp
          first.forwardCode second.forwardCode)
    rw [assemble_comp, PrimitiveFunctionGraph.GraphCode.assemble_comp]
    rfl
  exact congrArg Subtype.val code_eq

/-- Cycle 69 composition law at the raw backward-graph level.  The reversed
order comes from composing inverse functors. -/
theorem comp_backward {C : Type u} {D : Type v} {E : Type w}
    [Preorder C] [Preorder D] [Preorder E]
    (first : ThinEquivalenceGraphCode C D)
    (second : ThinEquivalenceGraphCode D E) :
    (comp first second).1.backward =
      (PrimitiveFunctionGraph.GraphCode.comp
        second.backwardCode first.backwardCode).1 := by
  have code_eq : (comp first second).backwardCode =
      PrimitiveFunctionGraph.GraphCode.comp
        second.backwardCode first.backwardCode := by
    apply PrimitiveFunctionGraph.GraphCode.assemble_injective
    change (comp first second).assemble.inverse.obj =
      PrimitiveFunctionGraph.GraphCode.assemble
        (PrimitiveFunctionGraph.GraphCode.comp
          second.backwardCode first.backwardCode)
    rw [assemble_comp, PrimitiveFunctionGraph.GraphCode.assemble_comp]
    rfl
  exact congrArg Subtype.val code_eq

/-- Internal API for the closure proofs: thin equivalences are determined by
their forward and inverse object maps because every relevant Hom is a
subsingleton. -/
private theorem equivalence_ext_of_obj_eq
    {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    {first second : C ≌ D}
    (forward : ∀ object, first.functor.obj object = second.functor.obj object)
    (backward : ∀ object, first.inverse.obj object = second.inverse.obj object) :
    first = second := by
  have functor_eq : first.functor = second.functor := by
    refine CategoryTheory.Functor.ext forward ?_
    intros
    exact Subsingleton.elim _ _
  have inverse_eq : first.inverse = second.inverse := by
    refine CategoryTheory.Functor.ext backward ?_
    intros
    exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext functor_eq inverse_eq
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun functor => Functor.id C ≅ functor)
    rw [functor_eq, inverse_eq]
  · apply subsingleton_heq_of_type_eq
    apply congrArg (fun functor => functor ≅ Functor.id D)
    rw [functor_eq, inverse_eq]

/-- Cycle 69 left-unit law for graph codes, derived from the two-sided
read/assemble comparison rather than assumed as an extra premise. -/
@[simp]
theorem id_comp {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : comp (id C) code = code := by
  apply equivEquivalence.injective
  change (comp (id C) code).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply equivalence_ext_of_obj_eq <;> intro object <;> rfl

/-- Cycle 69 right-unit law for graph codes, derived from the two-sided
read/assemble comparison rather than assumed as an extra premise. -/
@[simp]
theorem comp_id {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (code : ThinEquivalenceGraphCode C D) : comp code (id D) = code := by
  apply equivEquivalence.injective
  change (comp code (id D)).assemble = code.assemble
  rw [assemble_comp, assemble_id]
  apply equivalence_ext_of_obj_eq <;> intro object <;> rfl

/-- Cycle 69 associativity law for graph codes, inherited from functor
composition through the established read/assemble equivalence. -/
@[simp]
theorem assoc {C : Type u} {D : Type v} {E : Type w} {F : Type*}
    [Preorder C] [Preorder D] [Preorder E] [Preorder F]
    (first : ThinEquivalenceGraphCode C D)
    (second : ThinEquivalenceGraphCode D E)
    (third : ThinEquivalenceGraphCode E F) :
    comp (comp first second) third = comp first (comp second third) := by
  apply equivEquivalence.injective
  change (comp (comp first second) third).assemble =
    (comp first (comp second third)).assemble
  rw [assemble_comp, assemble_comp, assemble_comp, assemble_comp]
  apply equivalence_ext_of_obj_eq <;> intro object <;> rfl

end ThinEquivalenceGraphCode

/-! ## Non-vacuity fixtures -/

/-- Positive refutation-control fixture for the Cycle 69 context predicate:
identity object graphs on the Boolean preorder. -/
noncomputable def boolIdentityData : ThinEquivalenceGraphData Bool Bool := {
  forward := (PrimitiveFunctionGraph.GraphCode.read (_root_.id : Bool → Bool)).1
  backward := (PrimitiveFunctionGraph.GraphCode.read (_root_.id : Bool → Bool)).1 }

/-- Positive-instance theorem required for the Cycle 69 context predicate;
its premises come from the existing identity category equivalence. -/
theorem boolIdentityData_isThinEquivalenceGraphCode :
    IsThinEquivalenceGraphCode boolIdentityData := by
  simpa [boolIdentityData] using
    (ThinEquivalenceGraphCode.read
      (CategoryTheory.Equivalence.refl : Bool ≌ Bool)).2

/-- Negative refutation fixture for the Cycle 69 context predicate: a
constant-false forward object map paired with identity. -/
noncomputable def boolConstantData : ThinEquivalenceGraphData Bool Bool := {
  forward := (PrimitiveFunctionGraph.GraphCode.read
    (fun _ : Bool => false)).1
  backward := (PrimitiveFunctionGraph.GraphCode.read (_root_.id : Bool → Bool)).1 }

/-- Negative-instance theorem for the Cycle 69 context predicate, showing
that its inverse-counit premise is material rather than vacuous. -/
theorem boolConstantData_not_isThinEquivalenceGraphCode :
    ¬ IsThinEquivalenceGraphCode boolConstantData := by
  intro law
  have impossible := law.counit_inv true
  have true_eq_false : true = false := by
    apply le_antisymm
    · simpa [boolConstantData] using impossible
    · decide
  exact Bool.noConfusion true_eq_false

/-! ## Observable-presheaf naturality over assembled contexts -/

/-- The local observable premise selected by Cycle 69: restriction naturality
for a ring-equivalence family over the assembled context functor. -/
def IsRingFamilyRestrictionNatural
    {C : Type u} {D : Type v} [Preorder C] [Preorder D]
    (contextFunctor : C ⥤ D)
    (R : C → Type w) (S : D → Type*)
    [∀ W, CommRing (R W)] [∀ W, CommRing (S W)]
    (sourceRestrict : ∀ {W V}, (W ⟶ V) → R V →+* R W)
    (targetRestrict : ∀ {W V}, (W ⟶ V) → S V →+* S W)
    (family : ∀ W, R W ≃+* S (contextFunctor.obj W)) : Prop :=
  ∀ {W V} (f : W ⟶ V) (value : R V),
    family W (sourceRestrict f value) =
      targetRestrict (contextFunctor.map f) (family V value)

/-- API ingredient for the Cycle 69 observable refutation fixture: a concrete
nontrivial automorphism of the integer product ring. -/
def intPairSwap : (Int × Int) ≃+* (Int × Int) where
  toFun := Prod.swap
  invFun := Prod.swap
  left_inv := by rintro ⟨first, second⟩; rfl
  right_inv := by rintro ⟨first, second⟩; rfl
  map_mul' := by rintro ⟨a, b⟩ ⟨c, d⟩; rfl
  map_add' := by rintro ⟨a, b⟩ ⟨c, d⟩; rfl

/-- Negative-fixture data for Cycle 69: a pointwise ring-equivalence family
that changes from identity to factor swap along the Boolean arrow. -/
def boolIntPairFamily (index : Bool) : (Int × Int) ≃+* (Int × Int) :=
  match index with
  | false => RingEquiv.refl _
  | true => intPairSwap

/-- Negative-fixture restriction API for Cycle 69, chosen constant so the
changing pointwise family can be tested independently for naturality. -/
def boolIntPairRestrict {source target : Bool} (_ : source ⟶ target) :
    (Int × Int) →+* (Int × Int) :=
  RingHom.id _

/-- Negative-instance theorem for the Cycle 69 observable premise, proving
that pointwise ring equivalences alone do not imply restriction naturality. -/
theorem boolIntPairFamily_not_restrictionNatural :
    ¬ IsRingFamilyRestrictionNatural (Functor.id Bool)
      (fun _ => Int × Int) (fun _ => Int × Int)
      (@boolIntPairRestrict) (@boolIntPairRestrict) boolIntPairFamily := by
  intro natural
  have equality := natural
    (homOfLE (show false ≤ true by decide)) ((0, 1) : Int × Int)
  norm_num [boolIntPairRestrict, boolIntPairFamily, intPairSwap] at equality

/-- Raw data for the Cycle 69 observable main construction: low-level
pointwise ring graphs relative to a context functor.  The public joint code
below binds that parameter to its own assembled context graph code. -/
structure ObservablePresheafGraphData
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    (E : ArchitecturalEquationSystem C)
    (F : ArchitecturalEquationSystem D)
    (contextFunctor :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D) where
  /-- Pointwise graph datum inherited from the Cycle 68 indexed-code API. -/
  observable : IndexedRingEquivGraphCode contextFunctor.obj
    E.Observable F.Observable

/-- Local-law input of the Cycle 69 observable main construction.  It combines
the predecessor indexed ring-graph laws with the selected restriction
naturality premise. -/
structure IsObservablePresheafGraphCode
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {contextFunctor :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D}
    (data : ObservablePresheafGraphData E F contextFunctor) : Prop where
  /-- Restriction-naturality premise selected by the Cycle 69 obligation. -/
  observable_naturality : IsRingFamilyRestrictionNatural contextFunctor
    E.Observable F.Observable E.restrict F.restrict
    data.observable.assemble

/-- Input type of the Cycle 69 observable main theorem: observable ring graphs
bundled with their separate restriction law, but no completed natural iso. -/
abbrev ObservablePresheafGraphCode
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    (E : ArchitecturalEquationSystem C)
    (F : ArchitecturalEquationSystem D)
    (contextFunctor :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D) :=
  { data : ObservablePresheafGraphData E F contextFunctor //
    IsObservablePresheafGraphCode data }

namespace ObservablePresheafGraphCode

/-- Dependent transport API for the Cycle 69 joint code.  It changes only the
ambient functor index when context read/assemble yields a functor equality. -/
def reindex
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {first second :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D}
    (functor_eq : first = second)
    (code : ObservablePresheafGraphCode E F second) :
    ObservablePresheafGraphCode E F first := by
  cases functor_eq
  exact code

/-- Cycle 69 main observable assembler: indexed ring graphs plus the selected
restriction law produce a natural isomorphism of observable presheaves. -/
noncomputable def assembleIso
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {contextFunctor :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D}
    (code : ObservablePresheafGraphCode E F contextFunctor) :
    E.observablePresheaf ≅
      contextFunctor.op ⋙ F.observablePresheaf :=
  NatIso.ofComponents
    (fun W => (code.1.observable.assemble W.unop).toCommRingCatIso)
    (by
      intro X Y f
      apply CommRingCat.hom_ext
      ext value
      exact code.2.observable_naturality f.unop value)

/-- Transport API for the observable main assembler.  `HEq` records the
dependent type change forced by equality of ambient context functors. -/
theorem reindex_assembleIso_heq
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {first second :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D}
    (functor_eq : first = second)
    (code : ObservablePresheafGraphCode E F second) :
    HEq (reindex functor_eq code).assembleIso code.assembleIso := by
  cases functor_eq
  rfl

/-- Component API for the Cycle 69 observable assembler, connecting it to the
predecessor indexed ring-equivalence assembly without unfolding `NatIso`. -/
@[simp]
theorem assembleIso_hom_app_apply
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {contextFunctor :
      Site.ContextCategoryObject C ⥤ Site.ContextCategoryObject D}
    (code : ObservablePresheafGraphCode E F contextFunctor)
    (W : Site.ContextCategoryObject C) (value : E.Observable W) :
    code.assembleIso.hom.app (Opposite.op W) value =
      code.1.observable.assemble W value :=
  rfl

/-- Inverse construction for the Cycle 69 observable theorem: read component
graphs and the restriction premise from an actual equation-system transport
without retaining its natural iso. -/
noncomputable def readTransport
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    ObservablePresheafGraphCode E F
      transport.contextFunctor := by
  let observable : IndexedRingEquivGraphCode transport.contextFunctor.obj
      E.Observable F.Observable :=
    IndexedRingEquivGraphCode.read transport.observableEquiv
  refine ⟨⟨observable⟩, ⟨?_⟩⟩
  intro W V f value
  change observable.assemble W (E.restrict f value) = _
  have observable_eq : observable.assemble = transport.observableEquiv := by
    exact IndexedRingEquivGraphCode.assemble_read _
  rw [observable_eq]
  exact transport.observable_naturality f value

/-- Componentwise recovery API for Cycle 69, showing that observable reading
followed by assembly recovers every actual transport component. -/
theorem readTransport_observable_assemble
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap)
    (W : Site.ContextCategoryObject C) :
    ((readTransport transport).1.observable.assemble W) =
      transport.observableEquiv W := by
  apply RingEquiv.ext
  intro value
  simp [readTransport]

/-- Main observable recovery theorem for Cycle 69: assembly of the actual
transport reading is the existing observable-presheaf natural isomorphism. -/
theorem readTransport_assembleIso
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    (readTransport transport).assembleIso =
      transport.observablePresheafIso := by
  apply Iso.ext
  ext W value
  simp [assembleIso, readTransport,
    EquationSystemExactTransport.observablePresheafIso]

/-- Comparison API joining both Cycle 69 halves: actual equation transport
reads into the context graph code and recovers its context equivalence. -/
theorem readContext_assemble
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    (ThinEquivalenceGraphCode.read
      transport.contextEquivalence).assemble = transport.contextEquivalence :=
  ThinEquivalenceGraphCode.assemble_read _

end ObservablePresheafGraphCode

/-! ## Joint context and observable code -/

/-- Cycle 69 joint main input: the observable family is indexed by the functor
assembled from the same code's context graphs.  This dependent form rejects
an unrelated completed context functor. -/
structure ContextObservableGraphCode
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    (E : ArchitecturalEquationSystem C)
    (F : ArchitecturalEquationSystem D) where
  /-- Context half of the Cycle 69 joint input. -/
  context : ThinEquivalenceGraphCode
    (Site.ContextCategoryObject C) (Site.ContextCategoryObject D)
  /-- Observable half, indexed by the same input's assembled context functor. -/
  observable : ObservablePresheafGraphCode E F context.forwardFunctor

namespace ContextObservableGraphCode

/-- Inverse construction for the Cycle 69 joint theorem: read one actual
equation transport into context and observable graph data sharing one index. -/
noncomputable def read
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    ContextObservableGraphCode E F := by
  let context := ThinEquivalenceGraphCode.read transport.contextEquivalence
  have functor_eq : context.forwardFunctor = transport.contextFunctor :=
    congrArg CategoryTheory.Equivalence.functor
      (ThinEquivalenceGraphCode.assemble_read
        transport.contextEquivalence)
  exact {
    context := context
    observable := ObservablePresheafGraphCode.reindex functor_eq
      (ObservablePresheafGraphCode.readTransport transport) }

/-- Context half of the Cycle 69 joint recovery theorem, derived from the
context read/assemble inverse law. -/
@[simp]
theorem read_context_assemble
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    (read transport).context.assemble = transport.contextEquivalence := by
  exact ThinEquivalenceGraphCode.assemble_read _

/-- Observable half of the Cycle 69 joint recovery theorem.  `HEq` exposes the
necessary transport along the recovered context-functor equality. -/
theorem read_observable_assembleIso
    {U : AtomCarrier.{u}} {A₀ B₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {D : Site.ContextPreorderCategory B₀}
    {E : ArchitecturalEquationSystem C}
    {F : ArchitecturalEquationSystem D}
    {atomEquiv : U.Atom ≃ U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    (transport : EquationSystemExactTransport E F atomEquiv objectMap) :
    HEq (read transport).observable.assembleIso
      transport.observablePresheafIso := by
  let context := ThinEquivalenceGraphCode.read transport.contextEquivalence
  have functor_eq : context.forwardFunctor = transport.contextFunctor :=
    congrArg CategoryTheory.Equivalence.functor
      (ThinEquivalenceGraphCode.assemble_read
        transport.contextEquivalence)
  apply HEq.trans
    (ObservablePresheafGraphCode.reindex_assembleIso_heq functor_eq
      (ObservablePresheafGraphCode.readTransport transport))
  exact heq_of_eq
    (ObservablePresheafGraphCode.readTransport_assembleIso transport)

end ContextObservableGraphCode

/-! ## Complete-geometry connection -/

namespace CompleteGeometryContextObservableCode

/-- Required Cycle 69 connection to the existing complete-geometry API: read
context and observable coherence jointly from an actual `GeometryTotalHom`. -/
noncomputable def code {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    ContextObservableGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem :=
  ContextObservableGraphCode.read morphism.base.upper.equationTransport

/-- Projection API for the Cycle 69 complete-geometry connection, exposing its
independent context graph code without rebuilding the joint reading. -/
noncomputable def context {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    ThinEquivalenceGraphCode G.site.category H.site.category :=
  (code morphism).context

/-- Main context recovery theorem for the Cycle 69 complete-geometry
connection, relative to the existing equation transport. -/
@[simp]
theorem context_assemble {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (context morphism).assemble =
      morphism.base.upper.equationTransport.contextEquivalence :=
  ThinEquivalenceGraphCode.assemble_read _

/-- Forward comparison API required by Cycle 69: the new context reading
agrees with the predecessor complete-map graph field. -/
theorem context_forward_graph {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (context morphism).forwardCode =
      (readCompleteMapGraphs morphism).contextForward := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [show (readCompleteMapGraphs morphism).contextForward =
    PrimitiveFunctionGraph.GraphCode.read
      (equationContextForwardMap morphism) by rfl]
  rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
  funext W
  change (context morphism).assemble.functor.obj W = _
  exact congrArg (fun equivalence => equivalence.functor.obj W)
    (context_assemble morphism)

/-- Backward comparison API required by Cycle 69: the new context reading
agrees with the predecessor complete-map graph field. -/
theorem context_backward_graph {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    (context morphism).backwardCode =
      (readCompleteMapGraphs morphism).contextBackward := by
  apply PrimitiveFunctionGraph.GraphCode.assemble_injective
  rw [show (readCompleteMapGraphs morphism).contextBackward =
    PrimitiveFunctionGraph.GraphCode.read
      (equationContextBackwardMap morphism) by rfl]
  rw [PrimitiveFunctionGraph.GraphCode.assemble_read]
  funext W
  change (context morphism).assemble.inverse.obj W = _
  exact congrArg (fun equivalence => equivalence.inverse.obj W)
    (context_assemble morphism)

/-- Projection API for the Cycle 69 complete-geometry connection, reading the
observable components and restriction premise from the same actual Hom. -/
noncomputable def observable {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    ObservablePresheafGraphCode
      G.core.algebra.equationSystem H.core.algebra.equationSystem
      (context morphism).forwardFunctor :=
  (code morphism).observable

/-- Main observable recovery theorem for the Cycle 69 complete-geometry
connection, with dependent equality to the existing presheaf natural iso. -/
theorem observable_assembleIso {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} (morphism : GeometryTotalHom G H) :
    HEq (observable morphism).assembleIso
      morphism.base.upper.equationTransport.observablePresheafIso :=
  ContextObservableGraphCode.read_observable_assembleIso _

end CompleteGeometryContextObservableCode

#assert_standard_axioms_only
  AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence

end ContextObservableGraphCoherence

end

end AAT.AG.LocalSemanticReconstruction
