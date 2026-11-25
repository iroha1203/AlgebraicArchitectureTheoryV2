import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Mathlib.Algebra.Group.End
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

private abbrev Permutations := SingleObj (Equiv.Perm (Fin 3))

private def permutationView : Permutations ⥤ Type where
  obj _ := Fin 3
  map f := ↾fun x => (show Equiv.Perm (Fin 3) from f) x

private def permutationProduct (I : Type) : (I → Permutations) ⥤ Type where
  obj _ := I → Fin 3
  map f := ↾fun x i => (show Equiv.Perm (Fin 3) from f i) (x i)

private abbrev Position (Γ : List Bool) := (s : Bool) × Var Γ s

private abbrev permutationInputs (Γ : List Bool) : (Bool → Permutations) ⥤ Type :=
  Pi.comap (fun _ : Bool => Permutations) (fun i : Position Γ => i.1) ⋙ permutationProduct (Position Γ)

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
  probes := Set.univ
  probe_ext h := by simpa using h _ (Set.mem_univ _) (𝟙 _)
  tuplePoint {P} _ _ _ p := ↾fun x i => p i x
  tuplePoint_map {P} _ Γ {A B} f p := rfl
  tuplePoint_ext Γ A {Y f g} h := by
    exact h (Position Γ → Fin 3) (Set.mem_univ _) (fun i => ↾fun x => x i)
  total _ _ := ↾fun (xs : Position [false, true] → Fin 3) => xs ⟨true, .there .here⟩
  relation _ r := nomatch r
  domain _ p := nomatch p
  partialValue _ p := nomatch p
  quantity _ q := nomatch q

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
  pointCarrier _ _ := PUnit
  pointCarrier_isProbe _ _ := Set.mem_univ _
  realizeNative _ _ := ()
  nativePoints _ _ _ x := ↾fun _ => x
  change _ _ := ()
  changePoints _ _ _ p := p
  holds _ _ statement := nomatch statement

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

private def permutationModel (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (threeStatePermutationMode base).Models R :=
  ⟨(), trivial, fun l => nomatch l⟩

/-- The endomorphisms of the three-state model are exactly the allowed permutations. -/
def permutationModelHomEquiv (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (permutationModel base R ⟶ permutationModel base R) ≃ Equiv.Perm (Fin 3) :=
  (ObjectProperty.fullyFaithfulι ((threeStatePermutationMode base).modelProperty R)).homEquiv.trans
    permutationStructureHomEquiv

end SHIGURE.RealizationExamples
