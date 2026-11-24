import Formal.SHIGURE.Part1.MarkedLinearity
import Formal.SHIGURE.Part1.MarkedRationalQuotients
import Formal.SHIGURE.Part1.MarkedRealizations

/-! # Coefficient inputs and results of extra multilinear operations

Proposition 3.6 also covers a bilinear form on a marked module with
values in the fixed coefficient ring and a symbol whose first input is
a coefficient.

## Implementation notes

The operations use the finite product of the input coordinates, with
each module coordinate read through its standard quotient equivalence.
This keeps the declared coefficient sort itself as the input or result,
without adding a duplicate module sort for it.
-/

namespace SHIGURE.Marked.CoefficientExample

open Vocabulary
open RationalExample (unitKernel unitEquiv unitEquiv_projection fixedRank_one)

/-- One operation returns a coefficient and the other takes one as an argument. -/
inductive Op
  | pairing | action

/-- The two actual arities include the fixed coefficient sort. -/
def vocabulary : Vocabulary where
  SortName := Unit
  generators _ := 1
  rank _ := 1
  Multilinear := Op
  inputs
    | .pairing => [some (), some ()]
    | .action => [none, some ()]
  output
    | .pairing => none
    | .action => some ()

/-- The module uses the canonical one-coordinate marked quotient. -/
def kernels (_ : vocabulary.SortName) : Kernel ℚ 1 := unitKernel

/-- The marked generator has coordinate one in the canonical one-coordinate quotient. -/
theorem unitEquiv_mark : unitEquiv (generator unitKernel 0) = 1 := by
  rw [← projection_single, unitEquiv_projection, Pi.single_eq_same]

/-- Each input is read in the coefficient ring through the indicated coordinate. -/
noncomputable def inputCoordinate : (s : Option vocabulary.SortName) →
    quotientCarriers (V := vocabulary) kernels s →ₗ[ℚ] ℚ
  | none => LinearMap.id
  | some _ => unitEquiv.toLinearMap

/-- The canonical coordinate-one arguments retain their respective declared types. -/
def coordinateOne : (s : Option vocabulary.SortName) → quotientCarriers (V := vocabulary) kernels s
  | none => 1
  | some _ => generator unitKernel 0

/-- Coordinates of the two typed choices are both one. -/
theorem inputCoordinate_one (s : Option vocabulary.SortName) : inputCoordinate s (coordinateOne s) = 1 := by
  cases s with
  | none => rfl
  | some s => exact unitEquiv_mark

/-- The native multilinear map given by the product of the input coordinates. -/
noncomputable def productOfCoordinates (name : Op) :
    MultilinearMap ℚ (fun i : vocabulary.Position name =>
      SortCarrier ℚ ((kernelsOf (V := vocabulary) kernels name).inputs i)) ℚ :=
  letI := Fintype.ofFinite (vocabulary.Position name)
  (MultilinearMap.mkPiAlgebra ℚ (vocabulary.Position name) ℚ).compLinearMap (fun i => inputCoordinate i.1)

/-- The coordinate product is one on the typed tuple of marked units. -/
theorem productOfCoordinates_one (name : Op) :
    productOfCoordinates name (fun i => coordinateOne i.1) = 1 := by
  classical
  simp only [productOfCoordinates, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  exact Finset.prod_eq_one (fun i _ => inputCoordinate_one i.1)

/-- These are actual typed maps with coefficient input and output slots. -/
noncomputable def maps : (name : Op) → (kernelsOf (V := vocabulary) kernels name).Map
  | .pairing => productOfCoordinates .pairing
  | .action => unitEquiv.symm.toLinearMap.compMultilinearMap (productOfCoordinates .action)

/-- The form returns one in the coefficient ring on the pair of named generators. -/
theorem pairing_on_marks : maps .pairing (fun i => coordinateOne i.1) = (1 : ℚ) :=
  productOfCoordinates_one .pairing

/-- The extra action sends one and the named generator to that generator. -/
theorem action_on_one_mark : maps .action (fun i => coordinateOne i.1) = generator unitKernel 0 := by
  change unitEquiv.symm (productOfCoordinates Op.action (fun i => coordinateOne i.1)) = _
  rw [productOfCoordinates_one, ← unitEquiv_mark, LinearEquiv.symm_apply_apply]

/-- The additional form has two module inputs and a coefficient result. -/
theorem pairing_profile :
    vocabulary.arity (.multilinear Op.pairing) = ⟨[some (), some ()], none⟩ :=
  rfl

/-- The additional action has a coefficient input and a module input and result. -/
theorem action_profile :
    vocabulary.arity (.multilinear Op.action) = ⟨[none, some ()], some ()⟩ :=
  rfl

/-- No extra written Law is needed for these operations to have their declared linearity Laws. -/
def written : vocabulary.Laws where
  declarations := ⟨PEmpty, PEmpty.elim, PEmpty.elim⟩
  derived name := nomatch name

/-- The declaration context for the two typed operations and their linearity Laws. -/
noncomputable abbrev whole := DeclarationContext.full (vocabulary.presentation written)

/-- The coefficient and module maps are built as actual data on the full context. -/
noncomputable def datum : Data ℚ whole where
  kernel s _ := kernels s
  operation name keep :=
    cast (congrArg OperationKernels.Map (operationKernels_complete kernels keep).symm) (maps name)

/-- The operations and their generated Law proofs inhabit the actual ordinary marked interpretation. -/
noncomputable def realization : Realization ℚ whole where
  blocks := full_blockClosed written
  data := datum
  fixedRank _ _ := fixedRank_one unitEquiv
  satisfiesRequired name := by
    let law := whole.scopedTheory.law name
    apply (datum.contextStructure_satisfies_iff law (Declaration.lawBody_subset_of_mem name.property)).2
    change ((vocabulary.presentation written).laws.statement name.val.val).Holds datum.structureData
    cases h : name.val.val with
    | inl empty => exact PEmpty.elim empty
    | inr doc => exact holds_linearity datum doc

/-- The real mixed-type realization yields an ordinary model with those required equations. -/
noncomputable def ordinaryModel : Model (DeclarationContext.Selected.theory whole) :=
  realization.ordinaryModel

/-- A total structure with the same carriers and operations, except that the pairing is constant one. -/
noncomputable def constantPairing : Structure vocabulary.signature :=
  let regular := quotientStructure (V := vocabulary) kernels maps
  { regular with
    total := fun name => match name with
      | .coefficient f => regular.total (.coefficient f)
      | .moduleOp s f => regular.total (.moduleOp s f)
      | .multilinear .pairing => fun _ => (1 : ℚ)
      | .multilinear .action => regular.total (.multilinear .action) }

/-- The first-position additivity Law of the pairing is a declared required Law. -/
def pairingAdditivity : vocabulary.LinearityLaw :=
  .add .pairing ⟨some (), .here⟩

/-- The constant pairing fails that actual Law because its two sides give one and two. -/
theorem constantPairing_fails_additivity :
    ¬ ((vocabulary.presentation written).laws.statement (.inr pairingAdditivity)).Holds constantPairing := by
  intro held
  letI : IsEmpty (vocabulary.presentation written).signature.Partial := vocabulary.noPartial
  rw [vocabulary.linearity_statement, pairingAdditivity, LinearityLaw.statement_add, addLinearityLaw_eq,
    Law.holds_equality_totalValue_iff] at held
  have eq := held ⟨fun {s} _ => coordinateOne s⟩
  change (1 : ℚ) = 1 + 1 at eq
  norm_num at eq

/-- The actual ordinary model theory rejects the constant-pairing structure. -/
theorem constantPairing_no_ordinaryModel :
    ¬ ∃ M : Model (DeclarationContext.Selected.theory whole),
      M.obj = DeclarationContext.Selected.readStructure (ContextStructure.ofStructure whole constantPairing) := by
  rintro ⟨M, same⟩
  let required : whole.scopedTheory.LawName := ⟨⟨.inr pairingAdditivity, rfl⟩, Set.mem_univ _⟩
  let retained := Declaration.lawBody_subset_of_mem required.property
  have objectEq : (DeclarationContext.Selected.writeModel M).obj = ContextStructure.ofStructure whole constantPairing := by
    change DeclarationContext.Selected.writeStructure M.obj = _
    rw [same, DeclarationContext.Selected.write_read_structure]
  have satisfied := (DeclarationContext.Selected.writeModel M).satisfies_required required
  rw [objectEq] at satisfied
  exact constantPairing_fails_additivity
    ((ContextStructure.ofStructure_satisfies_iff whole constantPairing (whole.scopedTheory.law required) retained).1 satisfied)

end SHIGURE.Marked.CoefficientExample
