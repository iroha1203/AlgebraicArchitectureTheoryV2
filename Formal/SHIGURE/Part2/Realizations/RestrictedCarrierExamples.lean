import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.SingleObj

/-!
# A mode with restricted carrier arrows

The carrier category has one object and the permutations of a three-state
set. The operation diagrams and inputs live in the Cartesian category of
sets. The unary identity operation preserves every allowed map.
-/

open CategoryTheory
open scoped MonoidalCategory

namespace SHIGURE.RealizationExamples

private abbrev Permutations := SingleObj (Equiv.Perm (Fin 3))

private def permutationView : Permutations ⥤ Type where
  obj _ := Fin 3
  map f := ↾fun x => (show Equiv.Perm (Fin 3) from f) x

private def permutationProduct (I : Type) : (I → Permutations) ⥤ Type where
  obj _ := I → Fin 3
  map f := ↾fun x i => (show Equiv.Perm (Fin 3) from f i) (x i)

private abbrev Position (Γ : List Unit) := (s : Unit) × Var Γ s

private abbrev permutationInputs (Γ : List Unit) : (Unit → Permutations) ⥤ Type :=
  Pi.comap (fun _ : Unit => Permutations) (fun i : Position Γ => i.1) ⋙ permutationProduct (Position Γ)

private def unaryEquiv (s : Unit) : (Position [s] → Fin 3) ≃ Fin 3 where
  toFun x := x ⟨s, .here⟩
  invFun a _ := a
  left_inv x := by
    funext p
    obtain ⟨_, i⟩ := p
    cases i with
    | here => rfl
    | there i => exact nomatch i
  right_inv _ := rfl

private def emptyEquiv : (Position [] → Fin 3) ≃ PUnit where
  toFun _ := PUnit.unit
  invFun _ i := nomatch i.2
  left_inv _ := funext fun i => nomatch i.2
  right_inv _ := Subsingleton.elim _ _

private def splitEquiv (s : Unit) (Γ : List Unit) :
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

private def unarySignature : Signature where
  SortType := Unit
  Total := Unit
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[()], ()⟩
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

private def permutationRule : StructureRule unarySignature (Cat.of Permutations) Unit where
  carrier _ _ := SingleObj.star (Equiv.Perm (Fin 3))
  Ambient := Cat.of Type
  view := permutationView
  view_faithful := ⟨by
    intro _ _ f g h
    exact Equiv.ext (fun x => congrArg (fun a : Fin 3 ⟶ Fin 3 => a x) h)⟩
  monoidal := inferInstanceAs (MonoidalCategory (Type 0))
  input := permutationInputs
  positionalInput Γ := permutationProduct (Position Γ)
  inputIso _ := Iso.refl _
  unaryIso s := NatIso.ofComponents (fun _ => (unaryEquiv s).toIso) (fun _ => rfl)
  nullaryIso := NatIso.ofComponents (fun _ => emptyEquiv.toIso) (fun _ => rfl)
  consIso s Γ := NatIso.ofComponents (fun _ => (splitEquiv s Γ).toIso) (fun _ => rfl)
  total _ _ := ↾fun (xs : Position [()] → Fin 3) => xs ⟨(), .here⟩
  relation _ r := nomatch r
  domain _ p := nomatch p
  partialValue _ p := nomatch p
  quantity _ q := nomatch q

private def permutationTheory : RealizationTheory where
  signature := unarySignature
  LawName := Empty
  Statement := Empty
  law := Empty.elim

/-- The three-state unary identity realization takes permutations as its allowed maps. -/
def threeStatePermutationMode (base : CoefficientRing) :
    CoefficientRealizationMode base permutationTheory where
  Object _ := Unit
  Carrier _ := Cat.of Permutations
  rule _ := permutationRule
  admissible _ _ := True
  Native := PUnit
  nativeStates _ _ := Fin 3
  pointCarrier _ _ := PUnit
  realizeNative _ _ := ()
  nativePoints _ _ _ x := ↾fun _ => x
  change _ _ := ()
  changePoints _ _ _ p := p
  holds _ _ statement := nomatch statement

private def permutationStructureHomEquiv :
    ((show permutationRule.Category from ()) ⟶ (show permutationRule.Category from ())) ≃
      Equiv.Perm (Fin 3) where
  toFun f := f.val ()
  invFun e := ⟨fun _ => e,
    { total := fun _ => by rfl
      relation := fun r => nomatch r
      partialOp := fun p => nomatch p
      quantity := fun q => nomatch q }⟩
  left_inv f := Subtype.ext (funext fun ⟨⟩ => rfl)
  right_inv _ := rfl

private def permutationModel (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (threeStatePermutationMode base).Models R :=
  ⟨(), trivial, fun l => nomatch l⟩

/-- The endomorphisms of the three-state model are exactly the allowed permutations. -/
def permutationModelHomEquiv (base : CoefficientRing) (R : CoefficientAlgebra base) :
    (permutationModel base R ⟶ permutationModel base R) ≃ Equiv.Perm (Fin 3) :=
  (ObjectProperty.fullyFaithfulι ((threeStatePermutationMode base).modelProperty R)).homEquiv.trans
    permutationStructureHomEquiv

end SHIGURE.RealizationExamples
