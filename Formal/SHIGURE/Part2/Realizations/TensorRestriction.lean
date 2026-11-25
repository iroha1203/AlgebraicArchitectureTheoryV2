import Formal.SHIGURE.Part1.ContextSelectedVocabulary
import Formal.SHIGURE.Part2.Realizations.TensorInputs

/-!
# Restriction of tensor structures

A declaration can use a smaller primitive signature than that of its
models. Restriction keeps its actual carriers and operations and
identifies the typed argument positions through the Part I name map.
-/

open CategoryTheory SHIGURE.TensorRealization

universe u

noncomputable section

namespace SHIGURE

variable {K L : Type u}

/-- Renaming the sorts of a context preserves exactly its argument positions. -/
def TensorPosition.mapEquiv (f : K → L) : (Γ : List K) →
    TensorPosition Γ ≃ TensorPosition (Γ.map f)
  | [] =>
    letI : IsEmpty (TensorPosition ([] : List K)) := ⟨fun i => nomatch i.2⟩
    letI : IsEmpty (TensorPosition ([] : List L)) := ⟨fun i => nomatch i.2⟩
    Equiv.equivOfIsEmpty (TensorPosition ([] : List K)) (TensorPosition ([] : List L))
  | s :: Γ => (consPositions s Γ).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (mapEquiv f Γ)).trans (consPositions (f s) (Γ.map f)))

/-- The sort and variable at an argument position are both renamed by the Part I map. -/
theorem TensorPosition.mapEquiv_apply (f : K → L) (Γ : List K) (i : TensorPosition Γ) :
    mapEquiv f Γ i = ⟨f i.1, i.2.mapSorts f⟩ := by
  induction Γ with
  | nil => exact nomatch i.2
  | cons s Γ ih =>
    obtain ⟨_, i⟩ := i
    cases i with
    | here => rfl
    | there j => simp [mapEquiv, consPositions, ih, Var.mapSorts]

private def restrictTensorOperation {R : Type u} [CommRing R] (f : K → L)
    (M : L → ModuleCat.{u} R) {a : Arity K} {b : Arity L}
    (shape : ⟨a.inputs.map f, f a.output⟩ = b) (op : TensorOperation R M b) :
    TensorOperation R (fun s => M (f s)) a := by
  subst b
  let e := TensorPosition.mapEquiv f a.inputs
  let move := (MultilinearMap.domDomCongrLinearEquiv' R R
    (fun i : TensorPosition (a.inputs.map f) => (M i.1 : Type u)) (M (f a.output)) e.symm) op
  exact move.compLinearMap fun i =>
    (eqToIso (congrArg M (congrArg Sigma.fst (TensorPosition.mapEquiv_apply f a.inputs i)).symm)).hom.hom

/-- Restrict module carriers and operations along an arity-preserving signature map. -/
def TensorStructure.restrict {R : Type u} [CommRing R] {S T : Signature.{u}}
    (A : TensorStructure R T) (names : SignatureNames S T) : TensorStructure R S where
  carrier s := A.carrier (names.onSort s)
  total f := restrictTensorOperation names.onSort A.carrier (names.totalArity f)
    (A.total (names.onTotal f))
  quantity q := restrictTensorOperation names.onSort A.carrier (names.quantityArity q)
    (A.quantity (names.onQuantity q))

namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

private theorem forgetArity_injective (V : DeclarationContext P) :
    Function.Injective (fun a : Arity (SortName V) =>
      (⟨a.inputs.map Subtype.val, a.output.val⟩ : Arity P.signature.SortType)) := by
  rintro ⟨as, a⟩ ⟨bs, b⟩ h
  have hi : as = bs := (List.map_inj_right (fun _ _ e => Subtype.val_injective e)).mp
    (congrArg Arity.inputs h)
  have ho : a = b := Subtype.val_injective (congrArg Arity.output h)
  cases hi
  cases ho
  rfl

/-- The signature of a smaller declaration context includes into the larger one. -/
def namesOfLE (h : U ≤ V) : SignatureNames (signature U) (signature V) where
  onSort s := ⟨s.val, h s.property⟩
  onTotal f := ⟨f.val, h f.property⟩
  onRel r := ⟨r.val, h r.property⟩
  onPartial p := ⟨p.val, h p.property⟩
  onQuantity q := ⟨q.val, h q.property⟩
  totalArity f := by
    apply forgetArity_injective V
    simp only [List.map_map]
    exact ((names U).totalArity f).trans ((names V).totalArity ⟨f.val, h f.property⟩).symm
  relInputs r := by
    apply (List.map_inj_right (fun _ _ e => Subtype.val_injective e)).mp
    simp only [List.map_map]
    exact ((names U).relInputs r).trans ((names V).relInputs ⟨r.val, h r.property⟩).symm
  partialArity p := by
    apply forgetArity_injective V
    simp only [List.map_map]
    exact ((names U).partialArity p).trans ((names V).partialArity ⟨p.val, h p.property⟩).symm
  quantityArity q := by
    apply forgetArity_injective V
    simp only [List.map_map]
    exact ((names U).quantityArity q).trans ((names V).quantityArity ⟨q.val, h q.property⟩).symm

end DeclarationContext.Selected

end SHIGURE
