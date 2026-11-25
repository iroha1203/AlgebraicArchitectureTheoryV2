import Formal.SHIGURE.Part2.Realizations.CopyingMode
import Formal.SHIGURE.Part2.Realizations.TensorMode

/-!
# Positive and negative examples of realization semantics

The singleton Law holds in a constant singleton carrier and fails in the
constant Boolean carrier over a nonempty base. The latter cannot be split
into constant models of this Law. In the tensor mode a required equation
compares two designated elements of an integer module.
-/

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

noncomputable section

namespace SHIGURE.RealizationExamples

/-- A signature with one carrier sort and no primitive operations. -/
def signature : Signature where
  SortType := Unit
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := Empty.elim
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

/-- Interpret the one carrier sort by a chosen set. -/
def setStructure (X : Type) : Structure signature where
  carrier _ := X
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The Law requires all pairs of states to be equal. -/
def singletonLaw : Law signature :=
  ⟨[(), ()], .truth, .atom (.eq .here (.there .here))⟩

/-- The one-sort theory with the singleton Law. -/
def singletonTheory : Theory :=
  ⟨signature, Unit, fun _ => singletonLaw⟩

/-- The coefficient scheme used in the copying examples. -/
def integerScheme : Scheme :=
  Spec (CommRingCat.of ℤ)

private theorem model_states_eq (A : Model singletonTheory)
    (x y : A.obj.carrier ()) : x = y := by
  have h : singletonLaw.Holds A.obj := A.property ()
  exact h (Assignment.cons x (Assignment.cons y Assignment.empty)) trivial

private def singletonNative : Model singletonTheory :=
  ⟨setStructure Unit, by
    intro _ a _
    change (a.get Var.here : Unit) = a.get (.there .here)
    exact @Subsingleton.elim Unit inferInstance _ _⟩

/-- The constant singleton structure is locally split with a native singleton model. -/
theorem singleton_isZariskiSplit :
    Copying.IsZariskiSplit singletonTheory (Copying.constantStructure integerScheme (setStructure Unit)) :=
  Copying.isZariskiSplit_constant singletonTheory singletonNative

/-- The constant singleton satisfies the Law on every relative test scheme. -/
theorem singleton_holds :
    (Copying.constantStructure integerScheme (setStructure Unit)).holdsLaw singletonLaw := by
  rw [SheafStructure.holdsLaw_iff]
  intro U a _
  change a ∈ (SheafPredicate.equal
    (sheafTupleProj (Γ := [(), ()]) (fun _ : Unit => Copying.constantCarrier integerScheme Unit) Var.here)
    (sheafTupleProj (fun _ : Unit => Copying.constantCarrier integerScheme Unit) (.there .here))).carrier.obj U
  rw [SheafPredicate.mem_equal_iff]
  apply LocallyConstant.ext
  intro _
  exact Subsingleton.elim _ _

/-- The constant Boolean structure fails the Law on the coefficient scheme itself. -/
theorem bool_not_holds :
    ¬ (Copying.constantStructure integerScheme (setStructure Bool)).holdsLaw singletonLaw := by
  intro h
  let T : Over integerScheme := Over.mk (𝟙 integerScheme)
  let a : (sheafTuple (fun _ : Unit => Copying.constantCarrier integerScheme Bool)
      singletonLaw.context).val.obj (op T) :=
    Assignment.cons (LocallyConstant.const T.left false)
      (Assignment.cons (LocallyConstant.const T.left true) Assignment.empty)
  have he := (SheafStructure.holdsLaw_iff _ _).mp h (op T) a (SheafPredicate.mem_truth (op T) a)
  have hEq : LocallyConstant.const T.left false = LocallyConstant.const T.left true := he
  let p : T.left := Classical.choice (inferInstance : Nonempty (PrimeSpectrum ℤ))
  exact Bool.false_ne_true (congrArg (fun f : LocallyConstant T.left Bool => f p) hEq)

/-- Even though its carrier is constant, the Boolean structure cannot be
locally isomorphic to constant native models of the singleton theory. -/
theorem bool_not_isZariskiSplit :
    ¬ Copying.IsZariskiSplit singletonTheory (Copying.constantStructure integerScheme (setStructure Bool)) := by
  rintro ⟨cover, split⟩
  let p : integerScheme := Classical.choice (inferInstance : Nonempty (PrimeSpectrum ℤ))
  obtain ⟨i, point, _⟩ := cover.exists_eq p
  obtain ⟨M, ⟨e⟩⟩ := split i
  let U := cover.X i
  let V : Over U := Over.mk (𝟙 U)
  let e' := (eqToIso (Copying.restrictConstantStructure (cover.f i) (setStructure Bool))).symm ≪≫ e
  let f : Copying.constantCarrier U Bool ⟶ Copying.constantCarrier U (M.obj.carrier ()) := e'.hom.onSort ()
  let g : Copying.constantCarrier U (M.obj.carrier ()) ⟶ Copying.constantCarrier U Bool := e'.inv.onSort ()
  have hf : f ≫ g = 𝟙 _ := congrArg (fun h => h.onSort ()) e'.hom_inv_id
  let x := LocallyConstant.const V.left false
  let y := LocallyConstant.const V.left true
  have he : f.val.app (op V) x = f.val.app (op V) y := by
    apply LocallyConstant.ext
    intro t
    exact model_states_eq M _ _
  have hleft : ∀ a : LocallyConstant V.left Bool, g.val.app (op V) (f.val.app (op V) a) = a :=
    fun a => congrArg (fun h => h.val.app (op V) a) hf
  have hxy := (hleft x).symm.trans ((congrArg (g.val.app (op V)) he).trans (hleft y))
  exact Bool.false_ne_true (congrArg (fun h : LocallyConstant V.left Bool => h point) hxy)

/-- The integer ring with its chosen coefficient structure. -/
def integers : CoefficientRing :=
  ⟨ℤ, inferInstance⟩

/-- The coefficient algebra with identity map on the integers. -/
def integerAlgebra : CoefficientAlgebra integers :=
  ⟨integers, RingHom.id ℤ⟩

/-- The common semantic category of the copying mode contains the singleton model. -/
theorem singleton_copying_model :
    Nonempty ((Copying.copyingMode integers singletonTheory).Models integerAlgebra) :=
  ⟨⟨Copying.constantStructure integerScheme (setStructure Unit), singleton_isZariskiSplit,
    fun _ => singleton_holds⟩⟩

/-- The common semantic category excludes the Boolean structure for the same Law. -/
theorem bool_not_copying_model :
    ¬ (Copying.copyingMode integers singletonTheory).modelProperty integerAlgebra
      (Copying.constantStructure integerScheme (setStructure Bool)) :=
  fun h => bool_not_isZariskiSplit h.1

/-- A single sort with two designated elements. -/
def pointedSignature : Signature where
  SortType := Unit
  Total := Bool
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity _ := ⟨[], ()⟩
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

private def emptyOperation {R : Type} [CommRing R] (M : ModuleCat R) (x : M) :
    MultilinearMap R (fun _ : TensorPosition ([] : List Unit) => M) M where
  toFun _ := x
  map_update_add' _ i _ _ := nomatch i.2
  map_update_smul' _ i _ _ := nomatch i.2

/-- Interpret the full-domain signature in a module with the given two designated elements. -/
def pointedStructure {R : Type} [CommRing R] (M : ModuleCat R) (mark : Bool → M) :
    TensorStructure R pointedSignature where
  carrier _ := M
  total f := emptyOperation M (mark f)
  quantity q := nomatch q

private def fullDomainScope : FullDomainTensorSignature pointedSignature :=
  ⟨inferInstanceAs (IsEmpty Empty), inferInstanceAs (IsEmpty Empty)⟩

/-- The full-domain scope excludes even one nullary relation symbol. -/
theorem relation_not_fullDomain :
    ¬ FullDomainTensorSignature { pointedSignature with Rel := Unit, relInputs := fun _ => [] } :=
  fun scope => scope.noRelations.false ()

/-- The two nullary operations are required to represent the same map from the tensor unit. -/
def equalMarksLaw : TensorLaw ℤ pointedSignature :=
  ⟨.unit, .sort (),
    .comp .emptyArguments (.total false), .comp .emptyArguments (.total true)⟩

/-- The tensor theory carries its written equation comparing its two designated elements. -/
def pointedTheory : TensorTheory integers pointedSignature Unit :=
  ⟨fullDomainScope, fun _ => equalMarksLaw⟩

/-- Extend both designated elements by mapping each to its unit tensor. -/
def coefficientRule : TensorCoefficientRule pointedSignature where
  change {R S} f A :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    pointedStructure (ModuleCat.of S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier ()))
      (fun n => (1 : S.Carrier) ⊗ₜ[R.Carrier] A.designated n rfl)
  carrierIso {R S} f A s :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    by
      cases s
      exact LinearEquiv.refl S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier ())
  total_unit {R S} f A n xs := by
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    change (1 : S.Carrier) ⊗ₜ[R.Carrier] A.designated n rfl =
      (1 : S.Carrier) ⊗ₜ[R.Carrier] A.total n xs
    congr 2
    apply congrArg (A.total n)
    funext i
    exact nomatch i.2
  quantity_unit _ _ q := nomatch q

private def sameMarks : TensorStructure ℤ pointedSignature :=
  pointedStructure (ModuleCat.of ℤ ℤ) (fun _ => 1)

private def differentMarks : TensorStructure ℤ pointedSignature :=
  pointedStructure (ModuleCat.of ℤ ℤ) (fun b => if b then 0 else 1)

/-- The same nonzero integer element in both operations satisfies the written tensor Law. -/
theorem integer_equal_marks_model :
    (tensorMode integers pointedTheory coefficientRule).modelProperty integerAlgebra sameMarks :=
  ⟨trivial, fun _ => rfl⟩

/-- The same required equation fails when the two operations give 1 and 0. -/
theorem integer_different_marks_not_model :
    ¬ (tensorMode integers pointedTheory coefficientRule).modelProperty integerAlgebra differentMarks := by
  intro h
  have hEq : equalMarksLaw.holds differentMarks := h.2 ()
  have hVal := LinearMap.congr_fun hEq (1 : ℤ)
  letI : IsEmpty (TensorPosition ([] : List Unit)) := ⟨fun i => nomatch i.2⟩
  have hEmpty : (PiTensorProduct.isEmptyEquiv (R := ℤ)
      (s := fun i : TensorPosition ([] : List Unit) => differentMarks.carrier i.1)
      (TensorPosition [])).symm 1 =
        PiTensorProduct.tprod ℤ (s := fun i => differentMarks.carrier i.1) (fun i => nomatch i.2) := by
    apply (PiTensorProduct.isEmptyEquiv (R := ℤ) (TensorPosition [])).injective
    rw [LinearEquiv.apply_symm_apply, PiTensorProduct.isEmptyEquiv_apply_tprod]
  change PiTensorProduct.lift (differentMarks.total false)
      ((PiTensorProduct.isEmptyEquiv (TensorPosition ([] : List Unit))).symm (1 : ℤ)) =
    PiTensorProduct.lift (differentMarks.total true)
      ((PiTensorProduct.isEmptyEquiv (TensorPosition ([] : List Unit))).symm (1 : ℤ)) at hVal
  rw [hEmpty] at hVal
  have hFalse := PiTensorProduct.lift.tprod (φ := differentMarks.total false) (fun i => nomatch i.2)
  have hTrue := PiTensorProduct.lift.tprod (φ := differentMarks.total true) (fun i => nomatch i.2)
  exact one_ne_zero (show (1 : ℤ) = 0 from hFalse.symm.trans (hVal.trans hTrue))

/-- The zero carrier map does not preserve the designated nonzero element. -/
theorem integer_zero_map_not_preserving_marks :
    ¬ (tensorStructureRule ℤ pointedSignature fullDomainScope).Preserves
      (A := sameMarks) (B := sameMarks) (fun _ => ModuleCat.ofHom 0) := by
  intro h
  let f := tensorStructureHomEquiv pointedSignature fullDomainScope sameMarks sameMarks
    ⟨fun _ => ModuleCat.ofHom 0, h⟩
  have hz := f.preserves_designated false rfl
  exact zero_ne_one (show (0 : ℤ) = 1 from hz)

end SHIGURE.RealizationExamples
