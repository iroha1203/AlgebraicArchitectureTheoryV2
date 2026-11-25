import Formal.SHIGURE.Part2.Realizations.CopyingMode
import Formal.SHIGURE.Part2.Realizations.CopyingReading
import Formal.SHIGURE.Part2.Realizations.RestrictedCarrierExamples
import Formal.SHIGURE.Part2.Realizations.TensorDeclarations
import Mathlib.Data.ZMod.Basic

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

local instance : CommRing integers.Carrier := integers.ring

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

private def markedElementExpr (R : Type) (b : Bool) :
    TensorExpression R pointedSignature .unit (.sort ()) :=
  .comp .emptyArguments (.total b)

/-- The two nullary operations are required to represent the same map from the tensor unit. -/
def equalMarksLaw : TensorLaw ℤ pointedSignature :=
  ⟨.unit, .sort (), markedElementExpr ℤ false, markedElementExpr ℤ true⟩

/-- The written positive Law states that the two nullary operations have the same value. -/
def equalMarksSourceLaw : Law pointedSignature :=
  ⟨[], .truth, .ex (.ex (.conj
    (.atom (.graph (.total false) (fun i => nomatch i) (.there .here)))
    (.conj (.atom (.graph (.total true) (fun i => nomatch i) .here))
      (.atom (.eq (.there .here) .here)))))⟩

private theorem markedElementExpr_at_one {R : Type} [CommRing R]
    (A : TensorStructure R pointedSignature) (b : Bool) :
    (markedElementExpr R b).eval A (1 : R) = A.designated b rfl := by
  letI : IsEmpty (TensorPosition ([] : List Unit)) := ⟨fun i => nomatch i.2⟩
  let zeroInput : ∀ i : TensorPosition ([] : List Unit), A.carrier i.1 := fun i => nomatch i.2
  let e := PiTensorProduct.isEmptyEquiv (R := R)
    (s := fun i : TensorPosition ([] : List Unit) => A.carrier i.1) (TensorPosition [])
  have he : e.symm 1 = PiTensorProduct.tprod R zeroInput := by
    apply e.injective
    exact (e.apply_symm_apply 1).trans
      (PiTensorProduct.isEmptyEquiv_apply_tprod (TensorPosition []) zeroInput).symm
  change PiTensorProduct.lift (A.total b) (e.symm 1) = A.designated b rfl
  refine (congrArg (PiTensorProduct.lift (A.total b)) he).trans
    ((PiTensorProduct.lift.tprod (φ := A.total b) zeroInput).trans ?_)
  apply congrArg (A.total b)
  funext i
  exact nomatch i.2

private theorem equalMarksSourceLaw_iff {R : Type} [CommRing R] (A : TensorStructure R pointedSignature) :
    equalMarksSourceLaw.Holds (A.elementStructure fullDomainScope) ↔
      A.designated false rfl = A.designated true rfl := by
  have htotal (b : Bool) (xs : ∀ i : TensorPosition ([] : List Unit), A.carrier i.1) :
      A.total b xs = A.designated b rfl := by
    apply congrArg (A.total b)
    funext i
    exact nomatch i.2
  simp only [equalMarksSourceLaw, Law.holds_iff, Formula.Holds, Atomic.Holds, Structure.graph_total_iff]
  change (∀ (a : Assignment (fun s => A.carrier s) []), True → ∃ x y : A.carrier (),
    A.total false _ = x ∧ A.total true _ = y ∧ x = y) ↔ _
  constructor
  · intro h
    obtain ⟨x, y, hx, hy, hxy⟩ := h Assignment.empty trivial
    exact (htotal false _).symm.trans (hx.trans (hxy.trans (hy.symm.trans (htotal true _))))
  · intro h a _
    exact ⟨A.designated false rfl, A.designated true rfl, htotal false _, htotal true _, h⟩

/-- The typed equation reads the written positive Law over every integer algebra. -/
def equalMarksReading : TensorLawReading integers fullDomainScope equalMarksSourceLaw where
  equation := equalMarksLaw
  correct S A := by
    letI := S.scalars.ring
    rw [equalMarksSourceLaw_iff]
    change (markedElementExpr S.scalars.Carrier false).eval A =
      (markedElementExpr S.scalars.Carrier true).eval A ↔ _
    constructor
    · intro h
      exact (markedElementExpr_at_one A false).symm.trans
        ((LinearMap.congr_fun h (1 : S.scalars.Carrier)).trans (markedElementExpr_at_one A true))
    · intro h
      apply LinearMap.ext_ring
      exact (markedElementExpr_at_one A false).trans (h.trans (markedElementExpr_at_one A true).symm)

private def pointedSourceTheory : Theory :=
  ⟨pointedSignature, Unit, fun _ => equalMarksSourceLaw⟩

/-- The tensor theory reads the positive Law comparing the two designated elements. -/
def pointedTheory : TensorTheory integers pointedSignature Unit :=
  TensorTheory.read pointedSourceTheory fullDomainScope (fun _ => equalMarksReading)

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
  have hEq := (TensorTheory.modelProperty_read_iff pointedSourceTheory fullDomainScope
    (fun _ => equalMarksReading) coefficientRule integerAlgebra differentMarks).mp h ()
  have hValues := (equalMarksSourceLaw_iff differentMarks).mp hEq
  exact one_ne_zero (show (1 : ℤ) = 0 from hValues)

/-- The zero carrier map does not preserve the designated nonzero element. -/
theorem integer_zero_map_not_preserving_marks :
    ¬ (tensorStructureRule ℤ pointedSignature fullDomainScope).Preserves
      (A := sameMarks) (B := sameMarks) (fun _ => ModuleCat.ofHom 0) := by
  intro h
  let f := tensorStructureHomEquiv pointedSignature fullDomainScope sameMarks sameMarks
    ⟨fun _ => ModuleCat.ofHom 0, h⟩
  have hz := f.preserves_designated false rfl
  exact zero_ne_one (show (0 : ℤ) = 1 from hz)

/-- A coefficient rule cannot send the designated integer 1 to zero under the identity map. -/
theorem integer_mark_not_erased (rule : TensorCoefficientRule pointedSignature) :
    ((rule.change (R := integers) (S := integers) (RingHom.id ℤ) sameMarks).designated false rfl) ≠ 0 := by
  let f : integers.Hom integers := RingHom.id ℤ
  letI := f.toAlgebra
  let A := rule.change f sameMarks
  let e := rule.carrierIso f sameMarks ()
  intro h
  have h' : A.designated false rfl = 0 := h
  let x : ∀ i : TensorPosition ([] : List Unit), sameMarks.carrier i.1 := fun i => nomatch i.2
  have he : A.designated false rfl = e ((1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ)) := by
    refine Eq.trans ?_ (rule.total_unit f sameMarks false x)
    apply congrArg (A.total false)
    funext i
    exact nomatch i.2
  have hz : (1 : ℤ) ⊗ₜ[ℤ] (1 : ℤ) = 0 :=
    e.injective (he.symm.trans (h'.trans (e.map_zero).symm))
  have heval := congrArg (TensorProduct.lid ℤ ℤ) hz
  exact one_ne_zero (by simpa only [TensorProduct.lid_tmul, one_smul, map_zero] using heval)

private def repeatedGraphLaw : Law pointedSignature :=
  ⟨[(), ()], .conj
    (.atom (.graph (.total false) (fun i => nomatch i) .here))
    (.atom (.graph (.total false) (fun i => nomatch i) (.there .here))),
    .atom (.eq .here (.there .here))⟩

private def markedBool : Structure pointedSignature where
  carrier _ := Bool
  total f _ := f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

private def markedBoolTheory : Theory :=
  ⟨pointedSignature, Unit, fun _ => repeatedGraphLaw⟩

private def markedBoolNative : Model markedBoolTheory :=
  ⟨markedBool, fun _ => by
    intro a h
    have hx := (markedBool.graph_total_iff false _ _).mp h.1
    have hy := (markedBool.graph_total_iff false _ _).mp h.2
    exact hx.symm.trans hy⟩

/-- The full copying structure with two Boolean states satisfies its graph Law on each test scheme. -/
theorem markedBool_copying_model :
    Nonempty ((Copying.copyingMode integers markedBoolTheory).Models integerAlgebra) := by
  let A := Copying.constantStructure integerScheme markedBool
  refine ⟨⟨A, Copying.isZariskiSplit_constant markedBoolTheory markedBoolNative, ?_⟩⟩
  intro _
  change A.holdsLaw repeatedGraphLaw
  rw [SheafStructure.holdsLaw_iff]
  intro U xs hx
  let value : sheafTuple A.carrier [(), ()] ⟶ A.carrier () :=
    sheafTupleRename A.carrier (Γ := []) (fun i => nomatch i) ≫ A.total false
  let px := sheafTupleProj (Γ := [(), ()]) A.carrier Var.here
  let py := sheafTupleProj (Γ := [(), ()]) A.carrier (.there .here)
  change xs ∈ ((SheafPredicate.equal value px).conj (SheafPredicate.equal value py)).carrier.obj U at hx
  change xs ∈ (SheafPredicate.equal px py).carrier.obj U
  obtain ⟨ha, hb⟩ := (SheafPredicate.mem_conj_iff _ _ U xs).mp hx
  exact (SheafPredicate.mem_equal_iff _ _ U xs).mpr
    (((SheafPredicate.mem_equal_iff _ _ U xs).mp ha).symm.trans
      ((SheafPredicate.mem_equal_iff _ _ U xs).mp hb))

/-- A reflexive tensor equation cannot be a reading of the two-mark Law. -/
theorem equalMarksReading_not_reflexive
    (r : TensorLawReading integers fullDomainScope equalMarksSourceLaw) :
    r.equation.left ≠ r.equation.right := by
  letI := integerAlgebra.scalars.ring
  intro h
  have yes : (r.equation.mapScalars integerAlgebra.fromBase).holds differentMarks := by
    change ((r.equation.left.mapScalars integerAlgebra.fromBase).eval differentMarks) =
      ((r.equation.right.mapScalars integerAlgebra.fromBase).eval differentMarks)
    rw [h]
  have hValues := (equalMarksSourceLaw_iff differentMarks).mp ((r.correct integerAlgebra differentMarks).mp yes)
  exact one_ne_zero (show (1 : ℤ) = 0 from hValues)

private def tensorVocabulary : Signature where
  SortType := Bool
  Total := Empty
  Rel := Empty
  Partial := Empty
  Quantity := Empty
  totalArity := Empty.elim
  relInputs := Empty.elim
  partialArity := Empty.elim
  quantityArity := Empty.elim

private def tensorPrimitives : PrimitivePresentation where
  signature := tensorVocabulary
  laws := ⟨Empty, Empty.elim, Empty.elim⟩
  derived n := nomatch n

private def tensorLawScope : DeclarationContext tensorPrimitives where
  declarations := {Declaration.sort true}
  closed := by
    intro d kept e dependency
    have hd : d = Declaration.sort true := kept
    subst d
    simp only [Declaration.sort_dependencies, Set.notMem_empty] at dependency

private def twoTorsionLaw : TensorLaw ℤ (DeclarationContext.Selected.signature tensorLawScope) :=
  let sig := DeclarationContext.Selected.signature tensorLawScope
  let s : sig.SortType := ⟨true, rfl⟩
  let carrier := TensorShape.sort s
  let left := TensorExpression.smul (2 : ℤ) (@TensorExpression.id ℤ sig carrier)
  let right := @TensorExpression.zero ℤ sig carrier carrier
  ⟨carrier, carrier, left, right⟩

private theorem twoTorsion_support :
    twoTorsionLaw.support (DeclarationContext.Selected.names tensorLawScope) =
      ({Declaration.sort true} : Set (Declaration tensorPrimitives)) := by
  simp [twoTorsionLaw, TensorLaw.support, TensorExpression.support, TensorShape.support,
    DeclarationContext.Selected.names]

private def tensorDeclarations : TensorLawDeclarations integers tensorPrimitives where
  Name := Unit
  statement _ :=
    { scope := tensorLawScope
      equation := twoTorsionLaw
      scope_exact := by
        rw [twoTorsion_support]
        apply le_antisymm
        · exact DeclarationContext.closure_le_iff.mpr (fun _ h => h)
        · exact DeclarationContext.subset_closure _ }
  required := Set.univ

private def tensorContext : TensorDeclarationContext tensorDeclarations where
  primitives := DeclarationContext.full tensorPrimitives
  noPositiveRequirement := ⟨fun l => nomatch l.val.val⟩
  retained := Set.univ
  dependencies _ _ := Set.subset_univ _

private def smallerTensorContext : TensorDeclarationContext tensorDeclarations where
  primitives := tensorLawScope
  noPositiveRequirement := ⟨fun l => nomatch l.val.val⟩
  retained := tensorContext.retained
  dependencies _ _ := by
    change twoTorsionLaw.support (DeclarationContext.Selected.names tensorLawScope) ⊆
      tensorLawScope.declarations
    rw [twoTorsion_support]
    exact fun _ h => h

/-- The same written Law is retained in a context that drops the unrelated sort. -/
theorem twoTorsion_law_retained_after_removing_sort :
    Nonempty smallerTensorContext.Required ∧
      Declaration.sort false ∉ smallerTensorContext.primitives.declarations :=
  ⟨⟨⟨(), Set.mem_univ _, Set.mem_univ _⟩⟩, fun h => Bool.false_ne_true (Declaration.sort.inj h)⟩

/-- The same declaration requires the sort that actually appears in its equation. -/
theorem twoTorsion_law_uses_its_sort (U : TensorDeclarationContext tensorDeclarations)
    (kept : (show tensorDeclarations.Name from ()) ∈ U.retained) :
    Declaration.sort true ∈ U.primitives.declarations := by
  apply U.dependencies _ kept
  change Declaration.sort true ∈ twoTorsionLaw.support (DeclarationContext.Selected.names tensorLawScope)
  rw [twoTorsion_support]
  rfl

private def contextScope : FullDomainTensorSignature tensorContext.presentation.signature :=
  ⟨⟨fun r => nomatch r.val⟩, ⟨fun p => nomatch p.val⟩⟩

private def contextRule : TensorCoefficientRule tensorContext.presentation.signature where
  change {R S} f A :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    { carrier := fun s => ModuleCat.of S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier s)
      total := fun op => nomatch op.val
      quantity := fun q => nomatch q.val }
  carrierIso {R S} f A s :=
    letI := R.ring
    letI := S.ring
    letI := f.toAlgebra
    LinearEquiv.refl S.Carrier (S.Carrier ⊗[R.Carrier] A.carrier s)
  total_unit _ _ op := nomatch op.val
  quantity_unit _ _ q := nomatch q.val

private def contextModules (M : ModuleCat ℤ) : TensorAt integers tensorContext.presentation.signature where
  carrier s := if (show Bool from s.val) then M else ModuleCat.of ℤ ℤ
  total op := nomatch op.val
  quantity q := nomatch q.val

/-- The scoped tensor declaration holds on the cyclic group of order two at
its chosen sort, even though the other sort carries an integer module. -/
theorem cyclicTwo_satisfies_selected_tensor_law :
    Nonempty (SelectedTensorModels tensorContext integerAlgebra contextScope contextRule) := by
  refine ⟨⟨contextModules (ModuleCat.of ℤ (ZMod 2)), trivial, ?_⟩⟩
  rintro ⟨l, _, _⟩
  change Unit at l
  cases l
  change (2 : ℤ) • (LinearMap.id : ZMod 2 →ₗ[ℤ] ZMod 2) = 0
  apply LinearMap.ext
  intro x
  change (2 : ℤ) • x = 0
  rw [two_zsmul, ← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- Keeping the same declaration rules out an integer module at its chosen sort. -/
theorem integer_fails_selected_tensor_law :
    ¬ (tensorContext.mode contextScope contextRule).modelProperty integerAlgebra
      (contextModules (ModuleCat.of ℤ ℤ)) := by
  intro h
  let name : tensorDeclarations.Name := ()
  have hf := h.2 ⟨name, Set.mem_univ _, Set.mem_univ _⟩
  change (2 : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ) = 0 at hf
  have he := LinearMap.congr_fun hf 1
  exact (by decide : (2 : ℤ) ≠ 0) he

end SHIGURE.RealizationExamples
