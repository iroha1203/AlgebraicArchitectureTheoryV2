import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberModelEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Finite determination of general semantic lens morphisms

For fixed actual lens realizations `X` and `Y`, a morphism is read on every
state of the finite source reference fiber.  Unlike the protocol case, there
are no relations between distinct reading indices: every raw fiber map extends
through `LensRealization.ext`.  Table admissibility is therefore intrinsically
total, rather than a hidden extension certificate.

The full fiber separately supplies separation, extension, and effectiveness.
The executable path takes an explicit source-fiber enumeration, always accepts
the raw table, constructs an actual get/put-preserving Hom, and reads it back
exactly.  A constant map on a two-point product fiber records that this is the
general noninvertible Hom layer, not the invertible-change layer of Cycle 27.

Implementation notes:

* Admissibility is `True` because `LensRealization.ext` is total on fiber maps;
  it is not defined by storing a completed Hom or an extension witness.
* The actual source and target realizations remain arbitrary.  Product lenses
  occur only in the explicit noninvertible example.
* The effectiveness program uses a supplied `Fintype X.Fiber`; it does not turn
  the semantic `Finite X.Fiber` premise into an enumeration.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u

namespace LensSemanticFiniteDetermination

variable {V : Type u} {reference : V}
  (X Y : LensRealization V reference)

/-- G-124(B/D) primitive reading API: read an actual get/put-preserving lens
morphism by the accepted `LensRealization.res` at one source-fiber state. -/
def readLensHomAt (f : X ⟶ Y) (state : X.Fiber) : Y.Fiber :=
  LensRealization.res f state

/-- G-124(D) input API: the supplied `Fintype` explicitly enumerates the whole
source fiber; it is not inferred from the semantic `Finite` object premise. -/
def fullFiber [Fintype X.Fiber] : Finset X.Fiber :=
  Finset.univ

/-- G-124(D) raw-input API: one target-fiber value for every explicitly
enumerated source-fiber state, with no completed Hom field. -/
abbrev RawTable [Fintype X.Fiber] :=
  {state // state ∈ fullFiber X} → Y.Fiber

/-- G-124(D/E2) local predicate: every fiber table is admissible because the
accepted `LensRealization.ext` constructor is total; no extension certificate
is stored. -/
def TableAdmissible [Fintype X.Fiber] (_table : RawTable X Y) : Prop :=
  True

/-- Supporting API for the total G-124(D/E2) predicate: every raw table is
admissible independently of a completed Hom. -/
theorem tableAdmissible [Fintype X.Fiber] (table : RawTable X Y) :
    TableAdmissible X Y table :=
  True.intro

/-- Nonvacuity audit for G-124(D/E2): there is no inadmissible raw table.  This
records total lens extension, rather than omitting a negative test case. -/
theorem no_inadmissible_table [Fintype X.Fiber] :
    ¬ ∃ table : RawTable X Y, ¬ TableAdmissible X Y table := by
  rintro ⟨table, notAdmissible⟩
  exact notAdmissible (tableAdmissible X Y table)

/-- G-124(D/E2) main separation theorem.  It uses the accepted
`homEquivFiberMap` injectivity and the explicit full-fiber enumeration. -/
theorem fullFiber_separates [Fintype X.Fiber] :
    FiniteReading.Separates (readLensHomAt X Y) (fullFiber X) := by
  intro first second tableEquality
  apply (LensRealization.homEquivFiberMap X Y).injective
  funext state
  exact congrFun tableEquality ⟨state, Finset.mem_univ _⟩

/-- G-124(B/E2) assembly API: construct the actual get/put-preserving Hom from
a raw table by the accepted `LensRealization.ext`. -/
def assembleTable [Fintype X.Fiber] (table : RawTable X Y) : X ⟶ Y :=
  LensRealization.ext
    (fun state => table ⟨state, Finset.mem_univ _⟩)

/-- G-124(B/E2) readback API: `LensRealization.res_ext` recovers every raw table
entry from the assembled actual Hom. -/
@[simp] theorem restrict_assembleTable [Fintype X.Fiber]
    (table : RawTable X Y) :
    FiniteReading.restrict (readLensHomAt X Y) (fullFiber X)
        (assembleTable X Y table) = table := by
  funext state
  change LensRealization.res (LensRealization.ext
      (fun source => table ⟨source, Finset.mem_univ _⟩)) state.1 = table state
  rw [LensRealization.res_ext]

/-- G-124(D/E2) main extension theorem.  Total admissibility is discharged by
`assembleTable` and its `res_ext` readback, not by a certificate premise. -/
theorem fullFiber_extends [Fintype X.Fiber] :
    FiniteReading.Extends (readLensHomAt X Y) (fullFiber X)
      (TableAdmissible X Y) := by
  intro table _admissible
  exact ⟨assembleTable X Y table, restrict_assembleTable X Y table⟩

/-- G-124(D/E2) main determining theorem, combining the separately proved
full-fiber separation and extension properties. -/
theorem fullFiber_determining [Fintype X.Fiber] :
    FiniteReading.Determining (readLensHomAt X Y) (fullFiber X)
      (TableAdmissible X Y) :=
  ⟨fullFiber_separates X Y, fullFiber_extends X Y⟩

/-- G-124(D) main effectiveness program.  The explicit `Fintype X.Fiber`
enumeration drives a total decision/extension path, which always returns the
`LensRealization.ext` Hom and proves `res_ext` readback. -/
def effectivenessProgram [Fintype X.Fiber] :
    FiniteReading.EffectivenessProgram
      (readLensHomAt X Y) (fullFiber X) (TableAdmissible X Y) where
  coherenceTest _table := true
  coherenceTest_eq_true_iff table := by
    simp [TableAdmissible]
  extend? table := some (assembleTable X Y table)
  extend_eq_none_iff table := by
    simp [TableAdmissible]
  restrict_eq_of_extend_eq_some table global success := by
    cases success
    exact restrict_assembleTable X Y table

/-- G-124(D) effectiveness API, kept independent of the separation and
extension theorems and backed by the explicit enumeration program above. -/
theorem fullFiber_effective [Fintype X.Fiber] :
    FiniteReading.Effective
      (readLensHomAt X Y) (fullFiber X) (TableAdmissible X Y) :=
  ⟨effectivenessProgram X Y⟩

/-- G-124(B/D) Cycle 25 bridge API: the finite point reading is definitionally
the semantic fiber functor's accepted `LensRealization.res` component. -/
@[simp] theorem readLensHomAt_eq_semanticFiberReading
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (f : source ⟶ target) (state : source.Fiber) :
    readLensHomAt source target f state =
      (lensSemanticFiberReading input).map f state := by
  rfl

/-- G-124(B/D) closed-family bridge API: after `closedFamilyLensHom`, the same
point reading is the Cycle 25 `lensFiberValueReading` component. -/
@[simp] theorem readLensHomAt_eq_closedFamilyFiberReading
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (f : source ⟶ target) (state : source.Fiber) :
    readLensHomAt source target f state =
      (lensFiberValueReading input).map (closedFamilyLensHom f) state := by
  rfl

/-! ### A concrete noninvertible admissible table -/

/-- Concrete G-124(E2) fixture: a product lens with a two-point reference
fiber, used only to exhibit a noninvertible admitted Hom. -/
abbrev booleanFiberLens : LensRealization Unit () :=
  LensRealization.product Unit Bool ()

/-- Concrete-example enumeration: the canonical product-fiber equivalence
transports the explicit Boolean `Fintype`; no `Fintype.ofFinite` is used. -/
noncomputable local instance booleanFiberFintype :
    Fintype booleanFiberLens.Fiber :=
  Fintype.ofEquiv Bool
    (LensRealization.productFiberEquiv Unit Bool ()).symm

/-- Supporting fixture API: the distinguished false point of the Boolean
product fiber. -/
def falseFiberPoint : booleanFiberLens.Fiber :=
  (LensRealization.productFiberEquiv Unit Bool ()).symm false

/-- G-124(E2) negative-invertibility fixture: a raw table that collapses both
Boolean fiber points to `false`. -/
def constantFalseTable : RawTable booleanFiberLens booleanFiberLens :=
  fun _ => falseFiberPoint

/-- G-124(E2) fixture property: the nonbijective constant table is still
admissible in the general Hom layer. -/
theorem constantFalseTable_admissible :
    TableAdmissible booleanFiberLens booleanFiberLens constantFalseTable :=
  tableAdmissible booleanFiberLens booleanFiberLens constantFalseTable

/-- G-124(E2) fixture output: the actual Hom assembled from the constant raw
table through the same `LensRealization.ext` path as the main theorem. -/
def constantFalseHom : booleanFiberLens ⟶ booleanFiberLens :=
  assembleTable booleanFiberLens booleanFiberLens constantFalseTable

/-- G-124(E2) fixture readback: `res_ext` recovers the constant table from its
actual general lens Hom. -/
@[simp] theorem constantFalseHom_readback :
    FiniteReading.restrict
        (readLensHomAt booleanFiberLens booleanFiberLens)
        (fullFiber booleanFiberLens) constantFalseHom =
      constantFalseTable :=
  restrict_assembleTable booleanFiberLens booleanFiberLens constantFalseTable

/-- G-124(E2) anti-weakening witness: the admitted actual Hom is genuinely
noninvertible because its accepted `res` map is not injective. -/
theorem constantFalseHom_res_not_injective :
    ¬ Function.Injective (LensRealization.res constantFalseHom) := by
  intro injective
  let falsePoint :=
    (LensRealization.productFiberEquiv Unit Bool ()).symm false
  let truePoint :=
    (LensRealization.productFiberEquiv Unit Bool ()).symm true
  have imageEquality :
      LensRealization.res constantFalseHom falsePoint =
        LensRealization.res constantFalseHom truePoint := by
    simp [constantFalseHom, constantFalseTable, assembleTable]
  have pointEquality := injective imageEquality
  have boolEquality := congrArg
    (LensRealization.productFiberEquiv Unit Bool ()) pointEquality
  simp [falsePoint, truePoint] at boolEquality

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination

end LensSemanticFiniteDetermination

end AAT.AG.LocalSemanticReconstruction
