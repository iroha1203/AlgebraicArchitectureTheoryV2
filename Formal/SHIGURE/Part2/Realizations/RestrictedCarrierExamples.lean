import Formal.SHIGURE.Part2.Realizations.CoefficientModels
import Mathlib.Algebra.Group.End
import Mathlib.CategoryTheory.SingleObj

/-!
# A mode with restricted carrier arrows

The carrier category has one object and the permutations of a three-state
set. The operation diagrams and inputs live in the Cartesian category of
sets. The unary identity operation preserves every allowed map.
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
  input := permutationInputs
  positionalInput Γ := permutationProduct (Position Γ)
  inputIso _ := Iso.refl _
  unaryIso s := NatIso.ofComponents (fun _ => (unaryEquiv s).toIso) (fun _ => rfl)
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

private def groupPositionInputs : (Γ : List Unit) → (Position Γ → Permutations) ⥤ Permutations
  | [] => (Functor.const _).obj (SingleObj.star (Equiv.Perm (Fin 3)))
  | s :: _ => Pi.eval (fun _ : Position (s :: _) => Permutations) ⟨s, .here⟩

private def groupInputs (Γ : List Unit) : (Unit → Permutations) ⥤ Permutations :=
  Pi.comap (fun _ : Unit => Permutations) (fun i : Position Γ => i.1) ⋙ groupPositionInputs Γ

private def permutationGroupRule : StructureRule unarySignature (Cat.of Permutations) Unit where
  carrier _ _ := SingleObj.star (Equiv.Perm (Fin 3))
  Ambient := Cat.of Permutations
  view := 𝟭 _
  view_faithful := inferInstance
  input := groupInputs
  positionalInput := groupPositionInputs
  inputIso _ := Iso.refl _
  unaryIso _ := Iso.refl _
  total _ _ := 𝟙 (SingleObj.star (Equiv.Perm (Fin 3)))
  relation _ r := nomatch r
  domain _ p := nomatch p
  partialValue _ p := nomatch p
  quantity _ q := nomatch q

/-- The permutation category itself can support primitive diagrams, using the
first declared position for nonempty inputs. -/
def permutationGroupHomEquiv :
    ((show permutationGroupRule.Category from ()) ⟶ (show permutationGroupRule.Category from ())) ≃
      Equiv.Perm (Fin 3) where
  toFun f := f.val ()
  invFun σ := ⟨fun _ => σ, by
    refine ⟨fun _ => ?_, nofun, nofun, nofun⟩
    change 𝟙 (SingleObj.star (Equiv.Perm (Fin 3))) ≫ σ = σ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]⟩
  left_inv f := Subtype.ext (funext fun ⟨⟩ => rfl)
  right_inv _ := rfl

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
