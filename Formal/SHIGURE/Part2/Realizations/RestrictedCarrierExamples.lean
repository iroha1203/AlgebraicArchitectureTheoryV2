import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# A mode with restricted carrier arrows

The carrier category has one object and the permutations of a three-state
set at each of two sorts. The operation diagrams and inputs live in the
Cartesian category of sets. The binary operation takes the second input
as a state of the first sort, so the two permutations must agree.
-/

open CategoryTheory

namespace SHIGURE.RealizationExamples

/-- Use the permutation group as the arrow set on a single carrier. -/
private abbrev Permutations := SingleObj (Equiv.Perm (Fin 3))

/-- Display each permutation as the actual state function in sets. -/
private def permutationView : Permutations ⥤ Type where
  obj _ := Fin 3
  map f := ↾fun x => (show Equiv.Perm (Fin 3) from f) x

/-- Form the product of the state sets at the given argument positions. -/
private def permutationProduct (I : Type) : (I → Permutations) ⥤ Type where
  obj _ := I → Fin 3
  map f := ↾fun x i => (show Equiv.Perm (Fin 3) from f i) (x i)

/-- Use a dependent index to identify a sort together with a specific variable occurrence. -/
private abbrev Position (Γ : List Bool) := (s : Bool) × Var Γ s

/-- Associate the arity-indexed product to a family of permutation carriers. -/
private abbrev permutationInputs (Γ : List Bool) : (Bool → Permutations) ⥤ Type :=
  Pi.comap (fun _ : Bool => Permutations) (fun i : Position Γ => i.1) ⋙ permutationProduct (Position Γ)

/-- Read a one-position state tuple at its only position. -/
private def unaryEquiv (s : Bool) : (Position [s] → Fin 3) ≃ Fin 3 where
  toFun x := x ⟨s, .here⟩
  invFun a _ := a
  left_inv x := by
    funext p
    obtain ⟨_, i⟩ := p
    cases i with
    | here => rfl
    | there i => exact nomatch i
  right_inv _ := rfl

/-- Use two sorts and one binary operation to test independently chosen carrier maps. -/
private def binarySignature : Signature where
  SortType := Bool
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[false, true], false⟩
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

/-- There is precisely one function from an empty list of positions. -/
private def permutationEmptyIso : (PUnit : Type) ≅ (Position [] → Fin 3) :=
  { hom := ↾fun _ i => nomatch i.2
    inv := ↾fun _ => PUnit.unit
    hom_inv_id := rfl
    inv_hom_id := by
      apply ConcreteCategory.hom_ext (C := Type)
      intro x
      funext i
      exact nomatch i.2 }

/-- Split the first argument from the remaining state tuple. -/
private def permutationSplitEquiv (s : Bool) (Γ : List Bool) :
    (Position (s :: Γ) → Fin 3) ≃ Fin 3 × (Position Γ → Fin 3) where
  toFun x := (x ⟨s, .here⟩, fun i => x ⟨i.1, .there i.2⟩)
  invFun x
    | ⟨_, .here⟩ => x.1
    | ⟨t, .there i⟩ => x.2 ⟨t, i⟩
  left_inv x := by
    funext p
    obtain ⟨_, i⟩ := p
    cases i <;> rfl
  right_inv _ := rfl

/-- Use sortwise permutations and Cartesian declaration inputs in the example. -/
private def permutationRule : StructureRule binarySignature (Cat.of Permutations) Unit where
  carrier _ _ := SingleObj.star (Equiv.Perm (Fin 3))
  Ambient := Cat.of Type
  view := permutationView
  view_faithful := ⟨by
    intro _ _ f g h
    exact Equiv.ext (fun x => congrArg (fun a : Fin 3 ⟶ Fin 3 => a x) h)⟩
  input := permutationInputs
  positionalInput Γ := permutationProduct (Position Γ)
  inputIso _ := Iso.refl _
  unaryIso s := NatIso.ofComponents (fun _ => (unaryEquiv s).toIso) (fun _ => rfl)
  monoidal := inferInstanceAs (MonoidalCategory (Type 0))
  fullInput := permutationInputs
  fullInput_nil := NatIso.ofComponents (fun _ => permutationEmptyIso.symm) (fun _ => rfl)
  fullInput_cons s Γ := NatIso.ofComponents (fun _ => (permutationSplitEquiv s Γ).toIso) (fun _ => rfl)
  multipleInputComparison s t Γ := 𝟙 (permutationInputs (s :: t :: Γ))
  multipleInputComparison_epi _ _ _ _ := inferInstanceAs (Epi (𝟙 _))
  pointObject := PUnit
  pointUnit := Iso.refl _
  nullaryInput := NatIso.ofComponents (fun _ => permutationEmptyIso) (by
    intro A B f
    apply ConcreteCategory.hom_ext (C := Type)
    intro x
    funext i
    exact nomatch i.2)
  total _ _ := ↾fun (xs : Position [false, true] → Fin 3) => xs ⟨true, .there .here⟩
  relation _ r := nomatch r
  domain _ p := nomatch p
  partialValue _ p := nomatch p
  quantity _ q := nomatch q

/-- The permutation example uses the actual Cartesian tuple of every declared state. -/
def permutationInputPoints : StructureInputPoints permutationRule where
  Probe := Cat.of Type
  probe := 𝟭 _
  tuplePoint P _ _ p := ↾fun x i => p i x
  tuplePoint_map P Γ {A B} f p := rfl
  tuplePoint_restrict {P Q} f Γ A p := rfl
  tuplePoint_ext Γ A {Y f g} h := by
    exact h (Position Γ → Fin 3) (fun i => ↾fun x => x i)

/-- Keep the binary signature with no additional Laws in the example. -/
private def permutationTheory : RealizationTheory where
  signature := binarySignature
  LawName := Empty
  Statement := Empty
  law := Empty.elim

/-- The three-state realization takes permutations as the allowed maps on each sort. -/
def threeStatePermutationMode (base : CoefficientRing) :
    CoefficientRealizationMode base permutationTheory where
  Object _ := Unit
  Carrier _ := Cat.of Permutations
  rule _ := permutationRule
  admissible _ _ := True
  Native := PUnit
  nativeStates _ _ := Fin 3
  nativePointSource _ _ := permutationRule.pointObject
  realizeNative _ _ := ()
  nativePoints _ _ _ x := ↾fun _ => x
  change _ _ := ()
  changePoints _ _ _ p := p
  holds _ _ statement := nomatch statement

/-- Read an endomorphism by its action on the sort used by the operation. -/
private def permutationStructureHomEquiv :
    ((show permutationRule.Category from ()) ⟶ (show permutationRule.Category from ())) ≃
      Equiv.Perm (Fin 3) where
  toFun f := f.val false
  invFun e := ⟨fun _ => e,
    { total := fun _ => by rfl
      relation := fun r => nomatch r
      partialOp := fun p => nomatch p
      quantity := fun q => nomatch q }⟩
  left_inv f := by
    apply Subtype.ext
    funext s
    cases s
    · rfl
    · apply Equiv.ext
      intro x
      exact congrArg (fun h : (Position [false, true] → Fin 3) ⟶ Fin 3 => h (fun _ => x)) (f.property.total ())
  right_inv _ := rfl

/-- Acting on only the second sort fails to preserve the binary operation. -/
theorem secondSortSwap_not_preserving :
    ¬ permutationRule.Preserves (A := ()) (B := ())
      (fun s => if (show Bool from s) = true then Equiv.swap (0 : Fin 3) 1 else Equiv.refl _) := by
  intro h
  have he := congrArg (fun f : (Position [false, true] → Fin 3) ⟶ Fin 3 => f (fun _ => 0)) (h.total ())
  exact (by decide : (0 : Fin 3) ≠ 1) he

/-- The nullary square for a specified zero holds exactly for the permutations that fix zero. -/
theorem nullaryZero_preserved_iff (σ : Equiv.Perm (Fin 3)) :
    let A : Bool → Permutations := fun _ => SingleObj.star (Equiv.Perm (Fin 3))
    let f : A ⟶ A := fun _ => σ
    let z : (permutationRule.input []).obj A ⟶ (Fin 3 : Type) := ↾fun _ => 0
    z ≫ (↾fun s : Fin 3 => σ s) = (permutationRule.input []).map f ≫ z ↔ σ 0 = 0 := by
  intro A f z
  rw [permutationRule.nullary_square_iff]
  constructor
  · intro h
    exact congrArg (fun p : (PUnit : Type) ⟶ Fin 3 => p PUnit.unit) h
  · intro h
    exact congrArg (fun y : Fin 3 => (↾fun _ : PUnit => y : (PUnit : Type) ⟶ Fin 3)) h

/-- Admit the example structure as a model of its empty Law family. -/
private def permutationModel (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (threeStatePermutationMode base).Models R :=
  ⟨(), trivial, fun l => nomatch l⟩

/-- The endomorphisms of the three-state model are exactly the allowed permutations. -/
def permutationModelHomEquiv (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (permutationModel base R ⟶ permutationModel base R) ≃ Equiv.Perm (Fin 3) :=
  (ObjectProperty.fullyFaithfulι ((threeStatePermutationMode base).modelProperty R)).homEquiv.trans
    permutationStructureHomEquiv

end SHIGURE.RealizationExamples
