import Formal.SHIGURE.Part2.Realizations.CopyingMode
import Formal.SHIGURE.Part2.Realizations.TensorMode
import Mathlib.Algebra.Module.PUnit

/-!
# Positive and negative examples of realization semantics

The singleton Law holds in a constant singleton carrier and fails in the
constant Boolean carrier over a nonempty base. The latter cannot be split
into constant models of this Law. In the tensor scheme the identity equals
zero on the zero module and differs from zero on the integer module.
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

/-- Tensor structures for the one-sort signature are given by a single module. -/
def moduleStructure (M : ModuleCat ℤ) : TensorStructure ℤ signature where
  carrier _ := M
  total f := nomatch f
  quantity q := nomatch q

/-- The typed equation equates the identity of the carrier with zero. -/
def identityZeroLaw : TensorLaw ℤ signature :=
  ⟨.sort (), .sort (), @TensorExpression.id ℤ signature (.sort ()),
    @TensorExpression.zero ℤ signature (.sort ()) (.sort ())⟩

/-- The same tensor equation holds on the zero module. -/
theorem zeroModule_holds : identityZeroLaw.holds (moduleStructure (ModuleCat.of ℤ PUnit)) := by
  change (LinearMap.id : PUnit →ₗ[ℤ] PUnit) = 0
  apply LinearMap.ext
  intro _
  exact Subsingleton.elim _ _

/-- The tensor identity-zero equation fails on the integer module. -/
theorem integerModule_not_holds : ¬ identityZeroLaw.holds (moduleStructure (ModuleCat.of ℤ ℤ)) := by
  intro h
  change (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = 0 at h
  exact one_ne_zero (LinearMap.congr_fun h (1 : ℤ))

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

/-- Scalar extension of the carriers of the signature with no operations. -/
def coefficientRule : TensorCoefficientRule signature where
  change {R S} f A :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    { carrier := fun s => ModuleCat.of S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier s)
      total := fun op => nomatch op
      quantity := fun q => nomatch q }
  carrierIso {R S} f A s :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    LinearEquiv.refl S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier s)
  total_unit _ _ op := nomatch op
  quantity_unit _ _ q := nomatch q

/-- The tensor mode accepts the zero module as a model of the identity-zero Law. -/
theorem zero_tensor_model :
    Nonempty ((tensorMode integers singletonTheory coefficientRule (fun _ => identityZeroLaw)).Models
      integerAlgebra) :=
  ⟨⟨moduleStructure (ModuleCat.of ℤ PUnit), ⟨inferInstanceAs (IsEmpty Empty), inferInstanceAs (IsEmpty Empty)⟩,
    fun _ => zeroModule_holds⟩⟩

/-- The tensor mode excludes the integer module for the same required Law. -/
theorem integer_not_tensor_model :
    ¬ (tensorMode integers singletonTheory coefficientRule (fun _ => identityZeroLaw)).modelProperty
      integerAlgebra (moduleStructure (ModuleCat.of ℤ ℤ)) :=
  fun h => integerModule_not_holds (h.2 ())

end SHIGURE.RealizationExamples
