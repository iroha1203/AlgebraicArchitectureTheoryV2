import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor
import Mathlib.GroupTheory.Perm.Support

/-!
# Raw generators and action signatures for indexed base change

This module fixes the G-111 F0 type boundary.  Authored data consists only of
finite-support Atom permutations assembled by the `identity`, `comp`, and
`paste` syntax constructors.  The decoder below produces only an Atom
equivalence; it does not accept or construct an endofunctor value.

The semantic output signature separates the base and total endofunctors from
their soundness obligations.  F0 also fixes the types of the producer,
projection theorem, universal edge law, and identity/composition/pasting laws.
Their named inhabitants remain the K0 proof obligation rather than
caller-supplied certificates.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Intrinsically typed finite generator leaves -/

/--
One authored finite-support Atom permutation.  The table is a permutation of
the selected finite support, so extension by the identity is total by
construction.
-/
structure IndexedBCPrimitiveGenerator (U : AtomCarrier.{u}) where
  /-- Finite support on which the generator may act nontrivially. -/
  support : Finset U.Atom
  /-- Complete permutation table on the authored support. -/
  table : Equiv.Perm {atom // atom ∈ support}

namespace IndexedBCPrimitiveGenerator

/-- Decode the finite table by the identity outside its authored support. -/
def atomEquiv {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCPrimitiveGenerator U) : Equiv.Perm U.Atom :=
  Equiv.Perm.ofSubtype generator.table

/-- Primitive decoding agrees with the authored table on its support. -/
@[simp]
theorem atomEquiv_apply_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCPrimitiveGenerator U) (atom : U.Atom)
    (h : atom ∈ generator.support) :
    generator.atomEquiv atom = generator.table ⟨atom, h⟩ :=
  Equiv.Perm.ofSubtype_apply_of_mem generator.table h

/-- Primitive decoding is the identity away from the authored support. -/
@[simp]
theorem atomEquiv_apply_not_mem {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCPrimitiveGenerator U) (atom : U.Atom)
    (h : atom ∉ generator.support) :
    generator.atomEquiv atom = atom :=
  Equiv.Perm.ofSubtype_apply_of_not_mem generator.table h

/-- The authored support is exact when every listed Atom is genuinely moved. -/
def Reduced {U : AtomCarrier.{u}}
    (generator : IndexedBCPrimitiveGenerator U) : Prop :=
  ∀ atom : {atom // atom ∈ generator.support}, generator.table atom ≠ atom

/-- Finite Boolean check for exact support. -/
noncomputable def checkReduced {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCPrimitiveGenerator U) : Bool :=
  generator.support.attach.toList.all fun atom =>
    decide (generator.table atom ≠ atom)

end IndexedBCPrimitiveGenerator

/-! ## Finite generator syntax -/

/--
The raw indexed base-change language.  Every term is a finite syntax tree.
`paste` remains distinct from ordinary composition so that K0 can expose the
pasting API required by G-113 without adding semantic action values to the raw
input.
-/
inductive IndexedBCRawGenerator (U : AtomCarrier.{u}) where
  /-- Identity action code. -/
  | identity
  /-- One finite-support authored generator. -/
  | atom (generator : IndexedBCPrimitiveGenerator U)
  /-- Sequential composition of generated actions. -/
  | comp (first second : IndexedBCRawGenerator U)
  /-- Pasting constructor, retained as a named syntactic operation. -/
  | paste (first second : IndexedBCRawGenerator U)

namespace IndexedBCRawGenerator

/-- Decode a raw syntax tree to its primitive Atom permutation. -/
def atomEquiv {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    IndexedBCRawGenerator U → Equiv.Perm U.Atom
  | identity => Equiv.refl U.Atom
  | atom generator => generator.atomEquiv
  | comp first second => first.atomEquiv.trans second.atomEquiv
  | paste first second => first.atomEquiv.trans second.atomEquiv

/--
F0 well-formedness checks only the finite recursively typed syntax.  The primitive
leaf is intrinsically total because its table is an equivalence on its finite
support.  No diagnostic or action conclusion occurs in this predicate.
-/
noncomputable def checkWellFormed {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    IndexedBCRawGenerator U → Bool
  | identity => true
  | atom generator => generator.checkReduced
  | comp first second => first.checkWellFormed && second.checkWellFormed
  | paste first second => first.checkWellFormed && second.checkWellFormed

/-- The proposition read from the recursive finite syntax check. -/
def WellFormed {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCRawGenerator U) : Prop :=
  generator.checkWellFormed = true

/-- Recursive well-formedness is decidable by inspection of the finite tree. -/
noncomputable instance wellFormedDecidable {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (generator : IndexedBCRawGenerator U) : Decidable generator.WellFormed := by
  unfold WellFormed
  infer_instance

/-- The identity term is a positive well-formedness instance. -/
@[simp]
theorem wellFormed_identity {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    (identity : IndexedBCRawGenerator U).WellFormed := rfl

/-- A singleton identity table is rejected because its support is redundant. -/
theorem not_wellFormed_redundant_singleton {U : AtomCarrier.{u}}
    [DecidableEq U.Atom] (selected : U.Atom) :
    ¬(atom ({ support := {selected}, table := Equiv.refl _ } :
      IndexedBCPrimitiveGenerator U)).WellFormed := by
  simp [WellFormed, checkWellFormed, IndexedBCPrimitiveGenerator.checkReduced]

/-- The identity constructor decodes to the identity Atom permutation. -/
@[simp]
theorem atomEquiv_identity {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    (identity : IndexedBCRawGenerator U).atomEquiv = Equiv.refl U.Atom :=
  rfl

/-- Sequential syntax decodes by equivalence composition. -/
@[simp]
theorem atomEquiv_comp {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (first second : IndexedBCRawGenerator U) :
    (comp first second).atomEquiv = first.atomEquiv.trans second.atomEquiv :=
  rfl

/-- Pasting syntax has the same primitive evaluation order as composition. -/
@[simp]
theorem atomEquiv_paste {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (first second : IndexedBCRawGenerator U) :
    (paste first second).atomEquiv = first.atomEquiv.trans second.atomEquiv :=
  rfl

end IndexedBCRawGenerator

/-! ## Generated-action output signatures -/

/--
The two semantic functors produced from one raw generator.  This is an output
signature only: it stores neither their projection comparison nor any
diagnostic or cocartesian certificate.
-/
structure IndexedBaseChangeAction (U : AtomCarrier.{u}) where
  /-- Endofunctor on all pointed extraction instances over the fixed carrier. -/
  base : ExtInstCategory U ⥤ ExtInstCategory U
  /-- Endofunctor on the package total category over the same carrier. -/
  total : PackageTotalCategory U ⥤ PackageTotalCategory U

namespace IndexedBaseChangeAction

/-- The strict identity indexed action. -/
def identity (U : AtomCarrier.{u}) : IndexedBaseChangeAction U where
  base := 𝟭 (ExtInstCategory U)
  total := 𝟭 (PackageTotalCategory U)

/-- Sequential composition of indexed actions. -/
def comp {U : AtomCarrier.{u}}
    (first second : IndexedBaseChangeAction U) : IndexedBaseChangeAction U where
  base := first.base ⋙ second.base
  total := first.total ⋙ second.total

/--
F0 chooses strict binary pasting at the action level.  The raw constructor is
distinct, while its produced action must equal this named composite.
-/
def paste {U : AtomCarrier.{u}}
    (first second : IndexedBaseChangeAction U) : IndexedBaseChangeAction U :=
  comp first second

/-- The required projection square, stated separately from the action data. -/
def ProjectionCompatible {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) : Prop :=
  action.total ⋙ packageProjection U = packageProjection U ⋙ action.base

/-- Object component of the projection square. -/
theorem projectionObjEq {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible)
    (P : PackageTotalCategory U) :
    (packageProjection U).obj (action.total.obj P) =
      action.base.obj ((packageProjection U).obj P) :=
  CategoryTheory.Functor.congr_obj projection P

/--
The universal edge law explicitly ranges over every package-total morphism.
The object equalities cast both routes to the same endpoints.
-/
def UniversalEdgeLaw {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible) : Prop :=
  ∀ {P Q : PackageTotalCategory U} (edge : P ⟶ Q),
    (packageProjection U).map (action.total.map edge) ≫
        eqToHom (action.projectionObjEq projection Q) =
      eqToHom (action.projectionObjEq projection P) ≫
        action.base.map ((packageProjection U).map edge)

/-- A projection square entails the edge equation on every total morphism. -/
theorem universalEdgeLaw {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible) :
    action.UniversalEdgeLaw projection := by
  intro P Q edge
  change (action.total ⋙ packageProjection U).map edge ≫
      eqToHom (CategoryTheory.Functor.congr_obj projection Q) =
    eqToHom (CategoryTheory.Functor.congr_obj projection P) ≫
      (packageProjection U ⋙ action.base).map edge
  rw [CategoryTheory.Functor.congr_hom projection edge]
  simp

/--
Output type of the fiber action induced by a projection-compatible generated
action.  K0 must construct a named inhabitant from its projection theorem;
this family is not an authored input field.
-/
noncomputable def inducedFiberAction {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible)
    (X : ExtractionInstance U) :
    CoreFiber X ⥤ CoreFiber (action.base.obj X) where
  obj P := ⟨action.total.obj P.1, by
    exact (action.projectionObjEq projection P.1).trans
      (congrArg action.base.obj P.2)⟩
  map {P Q} edge := ⟨action.total.map edge.1, by
    apply CategoryTheory.IsHomLift.of_commsq
    change (packageProjection U).map (action.total.map edge.1) ≫
        eqToHom ((action.projectionObjEq projection Q.1).trans
          (congrArg action.base.obj Q.2)) =
      eqToHom ((action.projectionObjEq projection P.1).trans
          (congrArg action.base.obj P.2)) ≫ 𝟙 (action.base.obj X)
    letI : (packageProjection U).IsHomLift (𝟙 X) edge.1 := edge.2
    have hedge : (packageProjection U).map edge.1 ≫ eqToHom Q.2 =
        eqToHom P.2 ≫ 𝟙 X := by
      rw [CategoryTheory.IsHomLift.fac'
        (packageProjection U) (𝟙 X) edge.1]
      simp
    have hbase := congrArg (fun hom => action.base.map hom) hedge
    have hcomposite :
        (packageProjection U).map (action.total.map edge.1) ≫
            (eqToHom (action.projectionObjEq projection Q.1) ≫
              eqToHom (congrArg action.base.obj Q.2)) =
          (eqToHom (action.projectionObjEq projection P.1) ≫
            eqToHom (congrArg action.base.obj P.2)) ≫
              𝟙 (action.base.obj X) := by
      calc
        _ = ((packageProjection U).map (action.total.map edge.1) ≫
              eqToHom (action.projectionObjEq projection Q.1)) ≫
              eqToHom (congrArg action.base.obj Q.2) :=
            (Category.assoc _ _ _).symm
        _ = (eqToHom (action.projectionObjEq projection P.1) ≫
            action.base.map ((packageProjection U).map edge.1)) ≫
              eqToHom (congrArg action.base.obj Q.2) := by
                rw [action.universalEdgeLaw projection edge.1]
        _ = eqToHom (action.projectionObjEq projection P.1) ≫
            (action.base.map ((packageProjection U).map edge.1) ≫
              eqToHom (congrArg action.base.obj Q.2)) := Category.assoc _ _ _
        _ = eqToHom (action.projectionObjEq projection P.1) ≫
            (eqToHom (congrArg action.base.obj P.2) ≫
              action.base.map (𝟙 X)) := by
                rw [show action.base.map ((packageProjection U).map edge.1) ≫
                      eqToHom (congrArg action.base.obj Q.2) =
                    eqToHom (congrArg action.base.obj P.2) ≫
                    action.base.map (𝟙 X) by
                      simpa only [Functor.map_comp, eqToHom_map] using hbase]
        _ = _ := by simp
    simpa only [eqToHom_trans] using hcomposite⟩
  map_id P := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact action.total.map_id P.1
  map_comp edge₁ edge₂ := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact action.total.map_comp edge₁.1 edge₂.1

/-- The induced fiber functor is definitionally the restriction of `total`. -/
@[simp]
theorem inducedFiberAction_obj_val {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible)
    (X : ExtractionInstance U)
    (P : CoreFiber X) :
    ((action.inducedFiberAction projection X).obj P).1 =
      action.total.obj P.1 := rfl

/-- The induced fiber functor maps by the same `total` action. -/
@[simp]
theorem inducedFiberAction_map_val {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) (projection : action.ProjectionCompatible)
    (X : ExtractionInstance U)
    {P Q : CoreFiber X} (f : P ⟶ Q) :
    ((action.inducedFiberAction projection X).map f).1 =
      action.total.map f.1 := rfl

end IndexedBaseChangeAction

/-! ## F0 producer and law signatures -/

/-- The only allowable raw-to-action producer shape for K0. -/
abbrev IndexedBaseChangeProducer (U : AtomCarrier.{u}) :=
  IndexedBCRawGenerator U → IndexedBaseChangeAction U

namespace IndexedBaseChangeProducer

/-- Every produced action lies over its produced base action. -/
def ProjectionLaw {U : AtomCarrier.{u}} (producer : IndexedBaseChangeProducer U) : Prop :=
  ∀ generator, (producer generator).ProjectionCompatible

/-- Every produced projection square satisfies the explicit universal edge law. -/
def UniversalEdgeLaw {U : AtomCarrier.{u}} (producer : IndexedBaseChangeProducer U)
    (projection : producer.ProjectionLaw) : Prop :=
  ∀ generator, (producer generator).UniversalEdgeLaw (projection generator)

/-- The raw identity is sent to the strict identity action. -/
def PreservesIdentity {U : AtomCarrier.{u}} (producer : IndexedBaseChangeProducer U) : Prop :=
  producer .identity = IndexedBaseChangeAction.identity U

/-- Raw sequential composition is sent to action composition. -/
def PreservesComposition {U : AtomCarrier.{u}}
    (producer : IndexedBaseChangeProducer U) : Prop :=
  ∀ first second,
    producer (.comp first second) =
      (producer first).comp (producer second)

/-- Raw pasting is sent to the selected strict pasting action. -/
def PreservesPasting {U : AtomCarrier.{u}}
    (producer : IndexedBaseChangeProducer U) : Prop :=
  ∀ first second,
    producer (.paste first second) =
      (producer first).paste (producer second)

/--
The complete F0 law signature.  K0 must provide named proofs of every member
for its named producer; none is accepted as authored generator input.
-/
structure Laws {U : AtomCarrier.{u}} (producer : IndexedBaseChangeProducer U) : Prop where
  projection : producer.ProjectionLaw
  universalEdge : producer.UniversalEdgeLaw projection
  identity : producer.PreservesIdentity
  composition : producer.PreservesComposition
  pasting : producer.PreservesPasting

end IndexedBaseChangeProducer

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
