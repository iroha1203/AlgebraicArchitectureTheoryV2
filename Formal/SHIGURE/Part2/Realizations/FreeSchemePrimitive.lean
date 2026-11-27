import Formal.SHIGURE.Part2.Realizations.CoordinateMultilinearSheaf
import Formal.SHIGURE.Part2.Realizations.PrimitiveCoordinates

/-! # Primitive realizations on the chosen standard free sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SHIGURE.SchemeDescent SHIGURE.TensorRealization

noncomputable section

universe u

variable (X : Scheme.{u}) (sig : Signature.{u}) (rank : sig.SortType → ℕ)

private abbrev schemeFreeCarrier (s : sig.SortType) := coordinateModuleSheaf X (rank s)

private abbrev freePrimitiveOperation (a : Arity sig.SortType) :=
  moduleMultilinearTensor (fun i : TensorPosition a.inputs => schemeFreeCarrier X sig rank i.1) ⟶
    schemeFreeCarrier X sig rank a.output

/-- The actual sheaf morphisms specifying the primitives on the standard free carriers. -/
@[ext]
structure FreeSchemePrimitive where
  total (e : sig.Total) : freePrimitiveOperation X sig rank (sig.totalArity e)
  quantity (q : sig.Quantity) : freePrimitiveOperation X sig rank (sig.quantityArity q)

private def primitiveOperationCoordinates (a : Arity sig.SortType) :
    freePrimitiveOperation X sig rank a ≃
      ((∀ i : TensorPosition a.inputs, Fin (rank i.1)) → Fin (rank a.output) → Γ(X, ⊤)) := by
  letI : Fintype (TensorPosition a.inputs) := Fintype.ofFinite _
  exact coordinateMultilinearOperationEquiv X (fun i : TensorPosition a.inputs => rank i.1) (rank a.output)

/-- All primitive sheaf maps on the free carriers correspond to their
original global coefficients, including zero arities and ranks. -/
def freeSchemePrimitiveCoordinateEquiv :
    FreeSchemePrimitive X sig rank ≃ PrimitiveCoefficients sig rank Γ(X, ⊤) where
  toFun A :=
    { total := fun e => primitiveOperationCoordinates X sig rank (sig.totalArity e) (A.total e)
      quantity := fun q => primitiveOperationCoordinates X sig rank (sig.quantityArity q) (A.quantity q) }
  invFun c :=
    { total := fun e => (primitiveOperationCoordinates X sig rank (sig.totalArity e)).symm (c.total e)
      quantity := fun q => (primitiveOperationCoordinates X sig rank (sig.quantityArity q)).symm (c.quantity q) }
  left_inv A := by
    apply FreeSchemePrimitive.ext
    · funext e
      exact (primitiveOperationCoordinates X sig rank (sig.totalArity e)).symm_apply_apply _
    · funext q
      exact (primitiveOperationCoordinates X sig rank (sig.quantityArity q)).symm_apply_apply _
  right_inv c := by
    apply PrimitiveCoefficients.ext
    · funext e
      exact (primitiveOperationCoordinates X sig rank (sig.totalArity e)).apply_symm_apply _
    · funext q
      exact (primitiveOperationCoordinates X sig rank (sig.quantityArity q)).apply_symm_apply _

/-- The original primitive operations induce a tensor realization on the
modules of sections over any open of the test scheme. -/
def FreeSchemePrimitive.sectionStructure (A : FreeSchemePrimitive X sig rank) (U : X.Opensᵒᵖ) :
    TensorStructure (X.sheaf.val.obj U) sig where
  carrier s := (schemeFreeCarrier X sig rank s).val.obj U
  total e := (moduleMultilinearTensorHomEquiv _ _ (A.total e)).app U
  quantity q := (moduleMultilinearTensorHomEquiv _ _ (A.quantity q)).app U

/-- Reading the actual operations on global sections recovers precisely
their coefficient arrays in the chosen global bases. -/
theorem freeSchemePrimitive_globalCoefficients (A : FreeSchemePrimitive X sig rank) :
    PrimitiveCoefficients.ofTensor sig rank (A.sectionStructure X sig rank (op (⊤ : X.Opens)))
      (fun s => coordinateModuleSectionBasis X (rank s) (op (⊤ : X.Opens))) =
    freeSchemePrimitiveCoordinateEquiv X sig rank A := by
  apply PrimitiveCoefficients.ext
  · funext e a j
    change (coordinateModuleSectionBasis X (rank (sig.totalArity e).output) (op (⊤ : X.Opens))).repr
      ((moduleMultilinearTensorHomEquiv _ _ (A.total e)).app (op (⊤ : X.Opens))
        (fun i => coordinateModuleSectionBasis X (rank i.1) (op (⊤ : X.Opens)) (a i))) j = _
    rw [coordinateModuleSectionBasis_repr]
    rfl
  · funext q a j
    change (coordinateModuleSectionBasis X (rank (sig.quantityArity q).output) (op (⊤ : X.Opens))).repr
      ((moduleMultilinearTensorHomEquiv _ _ (A.quantity q)).app (op (⊤ : X.Opens))
        (fun i => coordinateModuleSectionBasis X (rank i.1) (op (⊤ : X.Opens)) (a i))) j = _
    rw [coordinateModuleSectionBasis_repr]
    rfl

/-- The actual global tensors, in their chosen bases, give the free
realization used in the affine chart equations. -/
def freeSchemePrimitive_globalStructureIso (A : FreeSchemePrimitive X sig rank) :
    A.sectionStructure X sig rank (op (⊤ : X.Opens)) ≅
      (freeSchemePrimitiveCoordinateEquiv X sig rank A).toTensor sig rank :=
  PrimitiveCoefficients.tensorIsoOfBasis sig rank _ (fun s =>
    coordinateModuleSectionBasis X (rank s) (op (⊤ : X.Opens))) ≪≫
      eqToIso (congrArg (PrimitiveCoefficients.toTensor sig rank)
        (freeSchemePrimitive_globalCoefficients X sig rank A))

end

end SHIGURE.RealizationFamilies
