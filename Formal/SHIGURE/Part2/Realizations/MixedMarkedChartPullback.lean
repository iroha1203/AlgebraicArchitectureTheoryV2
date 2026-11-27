import Formal.SHIGURE.Part2.Realizations.MixedMarkedChartFunctoriality
import Formal.SHIGURE.Part2.Realizations.CoordinateMultilinearBaseChange
import Formal.SHIGURE.Part2.Realizations.CoordinateMatrixBaseChange

/-! # Pullback of the actual operations and marking of a chart point -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory SHIGURE.SchemeDescent SHIGURE.TensorRealization

noncomputable section

universe u

variable {R : Type u} [CommRing R] (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m) {J : Type u} (laws : J → MixedMarkedLaw R sig m)
  {T T' : Over (Spec (CommRingCat.of R))} (g : T' ⟶ T)
  (p : T ⟶ mixedMarkedChartScheme sig rank m choice laws)

private abbrev realization {T : Over (Spec (CommRingCat.of R))}
    (p : T ⟶ mixedMarkedChartScheme sig rank m choice laws) :=
  (mixedMarkedChartRealizationEquiv sig rank m choice laws T p).val

private abbrev F (T : Scheme.{u}) := coordinateModuleSheaf T

/-- Precomposing a chart point pulls back its actual total primitive on the chosen free sheaves. -/
theorem mixedMarkedChartPoint_total_pullback (e : sig.Total) :
    let a := sig.totalArity e
    (Scheme.Modules.pullback g.left).map ((realization sig rank m choice laws p).1.total e) ≫
      (coordinateModulePullbackIso g.left (rank a.output)).hom =
    moduleMultilinearPullbackComparison g.left (fun i : TensorPosition a.inputs => F T.left (rank i.1)) ≫
      moduleMultilinearTensorMap (fun i => (coordinateModulePullbackIso g.left (rank i.1)).hom) ≫
        (realization sig rank m choice laws (g ≫ p)).1.total e := by
  let a := sig.totalArity e
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  let P := (realization sig rank m choice laws p).1
  let Q := (realization sig rank m choice laws (g ≫ p)).1
  let c := (mixedMarkedChartPointCoordinates sig rank m choice laws T p).1.total e
  let d := (mixedMarkedChartPointCoordinates sig rank m choice laws T' (g ≫ p)).1.total e
  have readP : coordinateMultilinearOperation T.left (fun i : TensorPosition a.inputs => rank i.1)
      (rank a.output) c = P.total e :=
    congrArg (fun A : FreeSchemePrimitive T.left sig rank => A.total e)
      ((freeSchemePrimitiveCoordinateEquiv T.left sig rank).symm_apply_apply P)
  have readQ : coordinateMultilinearOperation T'.left (fun i : TensorPosition a.inputs => rank i.1)
      (rank a.output) d = Q.total e :=
    congrArg (fun A : FreeSchemePrimitive T'.left sig rank => A.total e)
      ((freeSchemePrimitiveCoordinateEquiv T'.left sig rank).symm_apply_apply Q)
  have coeff : d = fun i j => g.left.appTop.hom (c i j) := by
    funext i j
    exact mixedMarkedChartPoint_primitive_precomp sig rank m choice laws g p (.total e i j)
  change (Scheme.Modules.pullback g.left).map (P.total e) ≫ _ = _ ≫ _ ≫ Q.total e
  rw [← readP, ← readQ, coeff]
  exact coordinateMultilinearOperation_pullback g.left _ _ c

/-- Precomposing a chart point pulls back its actual quantity primitive on the chosen free sheaves. -/
theorem mixedMarkedChartPoint_quantity_pullback (q : sig.Quantity) :
    let a := sig.quantityArity q
    (Scheme.Modules.pullback g.left).map ((realization sig rank m choice laws p).1.quantity q) ≫
      (coordinateModulePullbackIso g.left (rank a.output)).hom =
    moduleMultilinearPullbackComparison g.left (fun i : TensorPosition a.inputs => F T.left (rank i.1)) ≫
      moduleMultilinearTensorMap (fun i => (coordinateModulePullbackIso g.left (rank i.1)).hom) ≫
        (realization sig rank m choice laws (g ≫ p)).1.quantity q := by
  let a := sig.quantityArity q
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  let P := (realization sig rank m choice laws p).1
  let Q := (realization sig rank m choice laws (g ≫ p)).1
  let c := (mixedMarkedChartPointCoordinates sig rank m choice laws T p).1.quantity q
  let d := (mixedMarkedChartPointCoordinates sig rank m choice laws T' (g ≫ p)).1.quantity q
  have readP : coordinateMultilinearOperation T.left (fun i : TensorPosition a.inputs => rank i.1)
      (rank a.output) c = P.quantity q :=
    congrArg (fun A : FreeSchemePrimitive T.left sig rank => A.quantity q)
      ((freeSchemePrimitiveCoordinateEquiv T.left sig rank).symm_apply_apply P)
  have readQ : coordinateMultilinearOperation T'.left (fun i : TensorPosition a.inputs => rank i.1)
      (rank a.output) d = Q.quantity q :=
    congrArg (fun A : FreeSchemePrimitive T'.left sig rank => A.quantity q)
      ((freeSchemePrimitiveCoordinateEquiv T'.left sig rank).symm_apply_apply Q)
  have coeff : d = fun i j => g.left.appTop.hom (c i j) := by
    funext i j
    exact mixedMarkedChartPoint_primitive_precomp sig rank m choice laws g p (.quantity q i j)
  change (Scheme.Modules.pullback g.left).map (P.quantity q) ≫ _ = _ ≫ _ ≫ Q.quantity q
  rw [← readP, ← readQ, coeff]
  exact coordinateMultilinearOperation_pullback g.left _ _ c

private theorem markingMatrix_precomp (s : sig.SortType) :
    let P := (realization sig rank m choice laws p).2
    let Q := (realization sig rank m choice laws (g ≫ p)).2
    coordinateModuleMatrixRead T'.left (m s) (rank s) (Q.val s) =
      (coordinateModuleMatrixRead T.left (m s) (rank s) (P.val s)).map g.left.appTop.hom := by
  let P := (realization sig rank m choice laws p).2
  let Q := (realization sig rank m choice laws (g ≫ p)).2
  ext i j
  by_cases selected : j ∈ Set.range (choice s)
  · obtain ⟨k, rfl⟩ := selected
    change schemeMarkingMatricesEquiv T'.left sig rank m Q.val s i (choice s k) =
      g.left.appTop.hom (schemeMarkingMatricesEquiv T.left sig rank m P.val s i (choice s k))
    rw [P.property, Q.property]
    split <;> simp
  · exact mixedMarkedChartPoint_marking_precomp sig rank m choice laws g p ⟨s, i, j, selected⟩

/-- Precomposing a chart point pulls back the original marking sheaf maps,
including the selected columns. -/
theorem mixedMarkedChartPoint_marking_pullback (s : sig.SortType) :
    (Scheme.Modules.pullback g.left).map ((realization sig rank m choice laws p).2.val s) ≫
      (coordinateModulePullbackIso g.left (rank s)).hom =
    (coordinateModulePullbackIso g.left (m s)).hom ≫
      (realization sig rank m choice laws (g ≫ p)).2.val s := by
  let Q := (realization sig rank m choice laws (g ≫ p)).2.val s
  have square := coordinateModuleMatrix_pullback g.left (m s) (rank s)
    ((realization sig rank m choice laws p).2.val s)
  rw [← markingMatrix_precomp sig rank m choice laws g p s,
    coordinateModuleMatrixHom_read T'.left (m s) (rank s) Q] at square
  exact square

end

end SHIGURE.RealizationFamilies
