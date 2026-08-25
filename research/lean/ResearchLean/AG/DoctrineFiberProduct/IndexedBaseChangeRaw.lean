import ResearchLean.AG.CrossStageCoherence.CorePseudofunctor
import Mathlib.GroupTheory.Perm.Support

/-!
# Raw generators and action signatures for indexed base change

This module fixes the G-111 F0 type boundary.  Authored data consists only of
finite-support Atom permutations assembled by the `identity`, `comp`, and
`paste` syntax constructors.  The decoder below produces only an Atom
equivalence; it does not accept or construct an endofunctor value.

The semantic output signature separates the base and total endofunctors from
their soundness obligations.  Projection compatibility, induced fiber action,
canonical-lift compatibility, and cocartesian preservation are not fields.
Named producers and their theorems are therefore later proof obligations rather
than caller-supplied certificates.
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
F0 well-formedness checks only the recursively typed syntax.  The primitive
leaf is intrinsically total because its table is an equivalence on its finite
support.  No diagnostic or action conclusion occurs in this predicate.
-/
def checkWellFormed {U : AtomCarrier.{u}} : IndexedBCRawGenerator U → Bool
  | identity => true
  | atom _ => true
  | comp first second => first.checkWellFormed && second.checkWellFormed
  | paste first second => first.checkWellFormed && second.checkWellFormed

/-- The proposition read from the recursive executable syntax check. -/
def WellFormed {U : AtomCarrier.{u}} (generator : IndexedBCRawGenerator U) : Prop :=
  generator.checkWellFormed = true

/-- Recursive well-formedness is decidable by inspection of the finite tree. -/
instance wellFormedDecidable {U : AtomCarrier.{u}}
    (generator : IndexedBCRawGenerator U) : Decidable generator.WellFormed := by
  unfold WellFormed
  infer_instance

/-- Every intrinsically typed raw term passes the F0 well-formedness check. -/
theorem wellFormed {U : AtomCarrier.{u}}
    (generator : IndexedBCRawGenerator U) : generator.WellFormed := by
  induction generator <;> simp_all [WellFormed, checkWellFormed]

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

/-- The required projection square, stated separately from the action data. -/
def ProjectionCompatible {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) : Prop :=
  action.total ⋙ packageProjection U = packageProjection U ⋙ action.base

/--
Output type of the fiber action induced by a projection-compatible generated
action.  K0 must construct a named inhabitant from its projection theorem;
this family is not an authored input field.
-/
def InducedFiberAction {U : AtomCarrier.{u}}
    (action : IndexedBaseChangeAction U) : Type (u + 1) :=
  ∀ X : ExtractionInstance U,
    CoreFiber X ⥤ CoreFiber (action.base.obj X)

end IndexedBaseChangeAction

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
