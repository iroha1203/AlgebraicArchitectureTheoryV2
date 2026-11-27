import Formal.SHIGURE.Part2.Realizations.MarkedSchemeChart
import Formal.SHIGURE.Part2.Realizations.MarkingTransport

/-! # The actual named tensor structure of a based marked test scheme -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Module Opposite SHIGURE.TensorRealization

noncomputable section

universe u

variable (X : Scheme.{u}) (sig : Signature.{u}) (rank m : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank m)

private abbrev topOpen : X.Opensᵒᵖ := op (⊤ : X.Opens)

/-- The native global structure comparison is the actual coordinate projection on every carrier. -/
theorem freeSchemePrimitive_globalStructureIso_onSort (A : FreeSchemePrimitive X sig rank) (s : sig.SortType) :
    (freeSchemePrimitive_globalStructureIso X sig rank A).hom.onSort s =
      (coordinateModuleSectionIso X (rank s) (topOpen X)).hom.hom := by
  let H := freeSchemePrimitive_globalCoefficients X sig rank A
  let e := eqToIso (congrArg (PrimitiveCoefficients.toTensor sig rank) H)
  change (e.hom.onSort s).comp (coordinateModuleSectionBasis X (rank s) (topOpen X)).equivFun.toLinearMap = _
  have carrierIdentity := PrimitiveCoefficients.toTensor_eqToIso_hom_onSort sig rank H s
  change e.hom.onSort s = _ at carrierIdentity
  rw [carrierIdentity, LinearMap.id_comp]
  unfold coordinateModuleSectionBasis
  apply LinearMap.ext
  intro x
  funext i
  change ((Pi.basisFun Γ(X, ⊤) (Fin (rank s))).repr
    ((coordinateModuleSectionIso X (rank s) (topOpen X)).hom x)) i = _
  rw [← Basis.equivFun_apply, Pi.basisFun_equivFun]
  rfl

variable (P : NormalizedSchemeMarkedTensor X sig rank m choice)

/-- A named generator is its actual global section under the marking map. -/
def schemeMarkingGlobalSection (s : sig.SortType) (j : Fin (m s)) :
    (coordinateModuleSheaf X (rank s)).val.obj (topOpen X) :=
  (P.2.val s).val.app (topOpen X) (coordinateModuleUnitColumn X (m s) (topOpen X) j)

/-- The named global tensor uses the sections of the actual primitive sheaf maps
and the sections of the actual marking maps. -/
def namedSchemeMarkedStructure : TensorStructure Γ(X, ⊤) (markingSignature sig m) :=
  withMarkingOperations sig m (P.1.sectionStructure X sig rank (topOpen X))
    (schemeMarkingGlobalSection X sig rank m choice P)

/-- The complete matrix of the actual marking on sections is reconstructed from its nonselected entries. -/
theorem schemeMarkingGlobalSection_coordinates (s : sig.SortType) (j : Fin (m s)) (i : Fin (rank s)) :
    (coordinateModuleSectionIso X (rank s) (topOpen X)).hom
      (schemeMarkingGlobalSection X sig rank m choice P s j) i =
      markingMatrix sig rank m choice (normalizedSchemeMarkingEquiv X sig rank m choice P.2) s i j := by
  let r := schemeMarkingMatricesEquiv X sig rank m
  let e := normalizedMarkingMatricesEquiv (R := Γ(X, ⊤)) sig rank m choice
  let M : NormalizedMarkingMatrices sig rank m choice := ⟨r P.2.val, P.2.property⟩
  have recover := congrArg (fun z => z.val s i j) (e.symm_apply_apply M)
  exact recover.symm

/-- The chosen coordinate presentation preserves all actual marked generators and primitive operations. -/
def namedSchemeMarkedStructure_coordinateIso :
    namedSchemeMarkedStructure X sig rank m choice P ≅
      withMarkingOperations sig m
        ((freeSchemePrimitiveCoordinateEquiv X sig rank P.1).toTensor sig rank)
        (fun s j i => markingMatrix sig rank m choice
          (normalizedSchemeMarkingEquiv X sig rank m choice P.2) s i j) := by
  let e := freeSchemePrimitive_globalStructureIso X sig rank P.1
  apply markPreservingExtensionIso sig m _ e
  intro s j
  funext i
  change (e.hom.onSort s) (schemeMarkingGlobalSection X sig rank m choice P s j) i = _
  have read := freeSchemePrimitive_globalStructureIso_onSort X sig rank P.1 s
  change e.hom.onSort s = _ at read
  rw [read]
  exact schemeMarkingGlobalSection_coordinates X sig rank m choice P s j i

end

end SHIGURE.RealizationFamilies
