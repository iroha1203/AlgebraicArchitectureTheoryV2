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

/-- Read an actual get/put-preserving lens morphism on one source reference-
fiber state. -/
def readLensHomAt (f : X ⟶ Y) (state : X.Fiber) : Y.Fiber :=
  LensRealization.res f state

/-- The explicit finite reading set is the whole source reference fiber. -/
def fullFiber [Fintype X.Fiber] : Finset X.Fiber :=
  Finset.univ

/-- A raw table assigns one target-fiber state to every source-fiber state. -/
abbrev RawTable [Fintype X.Fiber] :=
  {state // state ∈ fullFiber X} → Y.Fiber

/-- General lens fiber tables have no cross-index equation: every such table
is admissible. -/
def TableAdmissible [Fintype X.Fiber] (_table : RawTable X Y) : Prop :=
  True

/-- Every raw lens fiber table is admissible. -/
theorem tableAdmissible [Fintype X.Fiber] (table : RawTable X Y) :
    TableAdmissible X Y table :=
  True.intro

/-- There is no inadmissible raw table; this is a theorem about total lens
extension, not an omitted negative test case. -/
theorem no_inadmissible_table [Fintype X.Fiber] :
    ¬ ∃ table : RawTable X Y, ¬ TableAdmissible X Y table := by
  rintro ⟨table, notAdmissible⟩
  exact notAdmissible (tableAdmissible X Y table)

/-- The full source-fiber table separates all actual lens morphisms. -/
theorem fullFiber_separates [Fintype X.Fiber] :
    FiniteReading.Separates (readLensHomAt X Y) (fullFiber X) := by
  intro first second tableEquality
  apply (LensRealization.homEquivFiberMap X Y).injective
  funext state
  exact congrFun tableEquality ⟨state, Finset.mem_univ _⟩

/-- Assemble a raw full table into the actual get/put-preserving lens Hom. -/
def assembleTable [Fintype X.Fiber] (table : RawTable X Y) : X ⟶ Y :=
  LensRealization.ext
    (fun state => table ⟨state, Finset.mem_univ _⟩)

/-- Reading an assembled lens Hom recovers every raw table entry exactly. -/
@[simp] theorem restrict_assembleTable [Fintype X.Fiber]
    (table : RawTable X Y) :
    FiniteReading.restrict (readLensHomAt X Y) (fullFiber X)
        (assembleTable X Y table) = table := by
  funext state
  change LensRealization.res (LensRealization.ext
      (fun source => table ⟨source, Finset.mem_univ _⟩)) state.1 = table state
  rw [LensRealization.res_ext]

/-- Every admissible raw full table extends to an actual general lens Hom. -/
theorem fullFiber_extends [Fintype X.Fiber] :
    FiniteReading.Extends (readLensHomAt X Y) (fullFiber X)
      (TableAdmissible X Y) := by
  intro table _admissible
  exact ⟨assembleTable X Y table, restrict_assembleTable X Y table⟩

/-- The full source reference fiber is determining for actual general lens
morphisms. -/
theorem fullFiber_determining [Fintype X.Fiber] :
    FiniteReading.Determining (readLensHomAt X Y) (fullFiber X)
      (TableAdmissible X Y) :=
  ⟨fullFiber_separates X Y, fullFiber_extends X Y⟩

/-- Executable extension for general lens Hom tables.  Since every fiber map
is admissible, the program always returns the directly assembled actual Hom. -/
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

/-- The full source fiber has an explicit effectiveness program independently
of its separation and extension theorems. -/
theorem fullFiber_effective [Fintype X.Fiber] :
    FiniteReading.Effective
      (readLensHomAt X Y) (fullFiber X) (TableAdmissible X Y) :=
  ⟨effectivenessProgram X Y⟩

/-- The general-lens point reading is exactly the Cycle 25 semantic fiber
reading on morphisms. -/
@[simp] theorem readLensHomAt_eq_semanticFiberReading
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (f : source ⟶ target) (state : source.Fiber) :
    readLensHomAt source target f state =
      (lensSemanticFiberReading input).map f state := by
  rfl

/-- The same point reading is the accepted closed-family fiber reading after
the semantic Hom enters through `closedFamilyLensHom`. -/
@[simp] theorem readLensHomAt_eq_closedFamilyFiberReading
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (f : source ⟶ target) (state : source.Fiber) :
    readLensHomAt source target f state =
      (lensFiberValueReading input).map (closedFamilyLensHom f) state := by
  rfl

/-! ### A concrete noninvertible admissible table -/

/-- Product lens with a two-point reference fiber. -/
abbrev booleanFiberLens : LensRealization Unit () :=
  LensRealization.product Unit Bool ()

/-- The canonical product-fiber equivalence supplies the explicit Boolean
enumeration used by the example. -/
noncomputable local instance booleanFiberFintype :
    Fintype booleanFiberLens.Fiber :=
  Fintype.ofEquiv Bool
    (LensRealization.productFiberEquiv Unit Bool ()).symm

/-- The distinguished false point of the Boolean product fiber. -/
def falseFiberPoint : booleanFiberLens.Fiber :=
  (LensRealization.productFiberEquiv Unit Bool ()).symm false

/-- A raw table that collapses both Boolean fiber points to `false`. -/
def constantFalseTable : RawTable booleanFiberLens booleanFiberLens :=
  fun _ => falseFiberPoint

/-- The constant table is admissible even though it is not bijective. -/
theorem constantFalseTable_admissible :
    TableAdmissible booleanFiberLens booleanFiberLens constantFalseTable :=
  tableAdmissible booleanFiberLens booleanFiberLens constantFalseTable

/-- The actual Hom obtained from the constant table. -/
def constantFalseHom : booleanFiberLens ⟶ booleanFiberLens :=
  assembleTable booleanFiberLens booleanFiberLens constantFalseTable

/-- The constant table reads back exactly from its actual general lens Hom. -/
@[simp] theorem constantFalseHom_readback :
    FiniteReading.restrict
        (readLensHomAt booleanFiberLens booleanFiberLens)
        (fullFiber booleanFiberLens) constantFalseHom =
      constantFalseTable :=
  restrict_assembleTable booleanFiberLens booleanFiberLens constantFalseTable

/-- The admitted actual Hom is genuinely noninvertible on its reference
fiber: its restricted map is not injective. -/
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
