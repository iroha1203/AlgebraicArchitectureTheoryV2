import Formal.SHIGURE.Part2.Descent.Operations

/-! # Descent of the actual tensor structures and their maps

## Implementation notes

Bundle each original carrier and its overlap once, then attach the
overlap equation to each native multilinear operation. This is the
sortwise data of Lemma B.5. The two interpretations expose the existing
`TensorStructure`; a separate structure with an opaque comparison would
hide the fixed vectors and the actual primitive operations. The
comparison checks each operation on its scalar-extension generators.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct CategoryTheory TensorRealization

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [Module.FaithfullyFlat A B] {sig : Signature.{u}}

/-- Compatible structure data consist of the native sort overlaps and the actual
primitive operations with their overlap equations. -/
structure TensorDatum (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (sig : Signature.{u}) where
  /-- A descent datum for every carrier. -/
  sort : sig.SortType → DescentModule A B
  /-- Each native total operation respects the overlap. -/
  total (f : sig.Total) :
    {op : TensorOperation B (nativeFamily sort) (sig.totalArity f) //
      CompatibleOperation sort _ (sort (sig.totalArity f).output) op}
  /-- Each native quantity respects the overlap. -/
  quantity (q : sig.Quantity) :
    {op : TensorOperation B (nativeFamily sort) (sig.quantityArity q) //
      CompatibleOperation sort _ (sort (sig.quantityArity q).output) op}

namespace TensorDatum

/-- The given tensor structure over the cover. -/
def native (D : TensorDatum A B sig) : TensorStructure B sig where
  carrier := nativeFamily D.sort
  total f := (D.total f).val
  quantity q := (D.quantity q).val

/-- The descended structure uses the actual fixed vectors and descended operations. -/
def descended (D : TensorDatum A B sig) : TensorStructure A sig where
  carrier := fixedFamily D.sort
  total f := operationEquiv D.sort _ _ (D.total f)
  quantity q := operationEquiv D.sort _ _ (D.quantity q)

/-- The B.4 comparison of a carrier is the inclusion on unit tensors. -/
theorem comparison_unit (D : DescentModule A B) (x : D.datum.toCoaction.descended) :
    D.datum.toCoaction.comparisonEquiv ((1 : B) ⊗ₜ[A] x) = x.val := by
  rw [Datum.comparisonEquiv_tmul, one_smul]

private theorem compare_operation {S : Type u} (D : S → DescentModule A B) {Γ : List S}
    (E : DescentModule A B)
    (op : {op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily D i.1) E.carrier //
      CompatibleOperation D Γ E op})
    (xs : ∀ i : TensorPosition Γ, extendCarriers A (fixedFamily D) B i.1) :
    E.datum.toCoaction.comparisonEquiv
      (extendOperation A (fixedFamily D) B (N := ModuleCat.of A E.datum.toCoaction.descended)
        (operationEquiv D Γ E op) xs) =
    op.val (fun i => (D i.1).datum.toCoaction.comparisonEquiv (xs i)) := by
  let c := E.datum.toCoaction.comparisonEquiv.toLinearMap
  let F := c.compMultilinearMap (extendOperation A (fixedFamily D) B (N := ModuleCat.of A E.datum.toCoaction.descended)
        (operationEquiv D Γ E op))
  let G := op.val.compLinearMap (fun i => (D i.1).datum.toCoaction.comparisonEquiv.toLinearMap)
  change F xs = G xs
  suffices equal : F = G from MultilinearMap.congr_fun equal xs
  apply multilinear_ext_unit A (fixedFamily D) B (P := ModuleCat.of B E.carrier)
  intro x
  change E.datum.toCoaction.comparisonEquiv
      (extendOperation A (fixedFamily D) B (N := ModuleCat.of A E.datum.toCoaction.descended)
        (operationEquiv D Γ E op) (fun i => (1 : B) ⊗ₜ[A] x i)) =
    op.val (fun i => (D i.1).datum.toCoaction.comparisonEquiv ((1 : B) ⊗ₜ[A] x i))
  rw [extendOperation_unit, comparison_unit]
  simpa only [comparison_unit] using operationEquiv_apply D Γ E op.val op.property x

/-- The B.4 carrier comparisons recover all native primitive operations. -/
def comparison (D : TensorDatum A B sig) :
    TensorStructure.Hom (extendStructure A B D.descended) D.native where
  onSort s := (D.sort s).datum.toCoaction.comparisonEquiv.toLinearMap
  preservesTotal f := compare_operation D.sort _ (D.total f)
  preservesQuantity q := compare_operation D.sort _ (D.quantity q)

private theorem preserves_operation_iff {S : Type u} {Γ : List S} (D E : S → DescentModule A B)
    (P Q : DescentModule A B)
    (op : {op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily D i.1) P.carrier //
      CompatibleOperation D Γ P op})
    (op' : {op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily E i.1) Q.carrier //
      CompatibleOperation E Γ Q op})
    (f : ∀ s, (D s).carrier →ₗ[B] (E s).carrier)
    (hf : ∀ s, (D s).datum.Compatible (E s).datum (f s))
    (g : P.carrier →ₗ[B] Q.carrier) (hg : P.datum.Compatible Q.datum g) :
    (∀ x, g (op.val x) = op'.val (fun i => f i.1 (x i))) ↔
    (∀ x, P.datum.descendMap Q.datum g hg (operationEquiv D Γ P op x) =
      operationEquiv E Γ Q op' (fun i => (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1) (x i))) := by
  constructor
  · intro h x
    apply Subtype.ext
    change g (operationEquiv D Γ P op x).val =
      (operationEquiv E Γ Q op'
        (fun i => (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1) (x i))).val
    rw [operationEquiv_apply, operationEquiv_apply]
    exact h (fun i => (x i).val)
  · intro h
    let leftOp := g.compMultilinearMap op.val
    let rightOp := op'.val.compLinearMap (fun i => f i.1)
    let e (i : TensorPosition Γ) := (D i.1).datum.toCoaction.comparisonEquiv
    have afterComparison :
        leftOp.compLinearMap (fun i => (e i).toLinearMap) =
          rightOp.compLinearMap (fun i => (e i).toLinearMap) := by
      apply multilinear_ext_unit A (fixedFamily D) B (P := ModuleCat.of B Q.carrier)
      intro x
      change g (op.val (fun i => e i ((1 : B) ⊗ₜ[A] x i))) =
        op'.val (fun i => f i.1 (e i ((1 : B) ⊗ₜ[A] x i)))
      have values := congrArg Subtype.val (h x)
      change g (operationEquiv D Γ P op x).val =
        (operationEquiv E Γ Q op'
          (fun i => (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1) (x i))).val at values
      rw [operationEquiv_apply, operationEquiv_apply] at values
      simpa only [e, comparison_unit] using values
    intro y
    have same := MultilinearMap.congr_fun afterComparison (fun i => (e i).symm (y i))
    change g (op.val (fun i => e i ((e i).symm (y i)))) =
      op'.val (fun i => f i.1 (e i ((e i).symm (y i)))) at same
    simpa only [LinearEquiv.apply_symm_apply] using same

variable (D E : TensorDatum A B sig)

private abbrev CompatibleHom :=
  {f : TensorStructure.Hom D.native E.native //
    ∀ s, (D.sort s).datum.Compatible (E.sort s).datum (f.onSort s)}

private def descendedHom (f : D.CompatibleHom E) : TensorStructure.Hom D.descended E.descended where
  onSort s := (D.sort s).datum.descendMap (E.sort s).datum (f.val.onSort s) (f.property s)
  preservesTotal n := (preserves_operation_iff D.sort E.sort _ _ (D.total n) (E.total n)
    f.val.onSort f.property _ (f.property _)).1 (f.val.preservesTotal n)
  preservesQuantity n := (preserves_operation_iff D.sort E.sort _ _ (D.quantity n) (E.quantity n)
    f.val.onSort f.property _ (f.property _)).1 (f.val.preservesQuantity n)

private def liftSort (f : TensorStructure.Hom D.descended E.descended) (s : sig.SortType) :=
  ((D.sort s).datum.descendMapEquiv (E.sort s).datum).symm (f.onSort s)

private theorem descend_liftSort (f : TensorStructure.Hom D.descended E.descended) (s : sig.SortType) :
    (D.sort s).datum.descendMap (E.sort s).datum (D.liftSort E f s).val (D.liftSort E f s).property = f.onSort s :=
  ((D.sort s).datum.descendMapEquiv (E.sort s).datum).apply_symm_apply (f.onSort s)

private def liftHom (f : TensorStructure.Hom D.descended E.descended) : D.CompatibleHom E := by
  let lifts := D.liftSort E f
  let maps s := (lifts s).val
  let comp s := (lifts s).property
  refine ⟨⟨maps, ?_, ?_⟩, comp⟩
  · intro n
    apply (preserves_operation_iff D.sort E.sort _ _ (D.total n) (E.total n) maps comp _ (comp _)).2
    intro x
    simpa only [maps, comp, lifts, descend_liftSort] using f.preservesTotal n x
  · intro n
    apply (preserves_operation_iff D.sort E.sort _ _ (D.quantity n) (E.quantity n) maps comp _ (comp _)).2
    intro x
    simpa only [maps, comp, lifts, descend_liftSort] using f.preservesQuantity n x

/-- All compatible structure-preserving maps correspond to all maps of descended structures. -/
def homEquiv :
    {f : TensorStructure.Hom D.native E.native //
      ∀ s, (D.sort s).datum.Compatible (E.sort s).datum (f.onSort s)} ≃
      TensorStructure.Hom D.descended E.descended where
  toFun := D.descendedHom E
  invFun := D.liftHom E
  left_inv f := by
    apply Subtype.ext
    apply TensorStructure.Hom.ext
    funext s
    exact congrArg Subtype.val (((D.sort s).datum.descendMapEquiv (E.sort s).datum).symm_apply_apply
      ⟨f.val.onSort s, f.property s⟩)
  right_inv f := TensorStructure.Hom.ext (funext (D.descend_liftSort E f))

/-- The structure correspondence tests surjectivity on each carrier. -/
theorem homEquiv_surjective_iff
    (f : {f : TensorStructure.Hom D.native E.native //
      ∀ s, (D.sort s).datum.Compatible (E.sort s).datum (f.onSort s)}) :
    (∀ s, Function.Surjective ((D.homEquiv E f).onSort s)) ↔
      ∀ s, Function.Surjective (f.val.onSort s) :=
  forall_congr' (fun s => (D.sort s).datum.descendMap_surjective_iff (E.sort s).datum (f.val.onSort s) (f.property s))

end TensorDatum

end

end SHIGURE.CoefficientDescent
