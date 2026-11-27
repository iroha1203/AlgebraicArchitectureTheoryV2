import Formal.SHIGURE.Part2.Realizations.CoordinateModuleMatrix
import Formal.SHIGURE.Part2.Realizations.FreeSchemePrimitive
import Formal.SHIGURE.Part2.Realizations.NormalizedMarkingMatrices

/-! # The marked chart interpreted as actual maps of free sheaves -/

namespace SHIGURE.RealizationFamilies

open AlgebraicGeometry CategoryTheory Opposite SHIGURE.TensorRealization

noncomputable section

universe u

variable (X : Scheme.{u}) (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank generators)

/-- A marking is a family of actual module sheaf maps on the free carriers. -/
abbrev SchemeMarking :=
  ∀ s, coordinateModuleSheaf X (generators s) ⟶ coordinateModuleSheaf X (rank s)

/-- The matrix of each actual marking map is read on its globally chosen unit sections. -/
def schemeMarkingMatricesEquiv :
    SchemeMarking X sig rank generators ≃
      (∀ s, Matrix (Fin (rank s)) (Fin (generators s)) Γ(X, ⊤)) :=
  Equiv.piCongrRight fun s => coordinateModuleMatrixEquiv X (generators s) (rank s)

/-- The chosen marking sections give the standard unit vectors of the carrier sheaves. -/
abbrev NormalizedSchemeMarking :=
  {π : SchemeMarking X sig rank generators //
    ∀ s i j, schemeMarkingMatricesEquiv X sig rank generators π s i (choice s j) =
      if i = j then 1 else 0}

/-- An actual marking with the selected basis is uniquely specified by
the other entries of its marking matrix. -/
def normalizedSchemeMarkingEquiv :
    NormalizedSchemeMarking X sig rank generators choice ≃
      (MarkingCoordinate sig rank generators choice → Γ(X, ⊤)) :=
  ((schemeMarkingMatricesEquiv X sig rank generators).subtypeEquiv (fun _ => Iff.rfl)).trans
    (normalizedMarkingMatricesEquiv sig rank generators choice)

/-- On each open, a chosen marking column gives the corresponding unit vector. -/
theorem normalizedSchemeMarking_selected_sections
    (P : NormalizedSchemeMarking X sig rank generators choice)
    (s : sig.SortType) (U : X.Opensᵒᵖ) (j : Fin (rank s)) :
    (P.val s).val.app U (coordinateModuleUnitColumn X (generators s) U (choice s j)) =
      coordinateModuleUnitColumn X (rank s) U j := by
  classical
  let m := generators s
  let n := rank s
  let e := coordinateModuleSectionIso X n U
  let M := coordinateModuleMatrixRead X m n (P.val s)
  apply e.toLinearEquiv.injective
  funext i
  have model : coordinateModuleMatrixHom X m n M = P.val s :=
    coordinateModuleMatrixHom_read X m n (P.val s)
  have column := coordinateModuleMatrixHom_column X m n M U i (choice s j)
  rw [model] at column
  have specified : M i (choice s j) = if i = j then 1 else 0 := P.property s i j
  change e.hom ((P.val s).val.app U (coordinateModuleUnitColumn X m U (choice s j))) i =
    e.hom (coordinateModuleUnitColumn X n U j) i
  rw [column, specified, coordinateModuleUnitColumn_coordinates]
  simp [Pi.single_apply]

/-- The actual marking map is surjective on every open of the test scheme. -/
theorem normalizedSchemeMarking_surjective_sections
    (P : NormalizedSchemeMarking X sig rank generators choice)
    (s : sig.SortType) (U : X.Opensᵒᵖ) :
    Function.Surjective ((P.val s).val.app U) := by
  intro y
  let b := coordinateModuleSectionBasis X (rank s) U
  refine ⟨∑ j, b.repr y j • coordinateModuleUnitColumn X (generators s) U (choice s j), ?_⟩
  change ((P.val s).val.app U).hom (∑ j, b.repr y j •
    coordinateModuleUnitColumn X (generators s) U (choice s j)) = y
  rw [map_sum]
  calc
    _ = ∑ j, b.repr y j • b j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul]
      have chosen := normalizedSchemeMarking_selected_sections X sig rank generators choice P s U j
      change ((P.val s).val.app U).hom (coordinateModuleUnitColumn X (generators s) U (choice s j)) =
        coordinateModuleUnitColumn X (rank s) U j at chosen
      rw [chosen]
      congr 1
      dsimp only [b, coordinateModuleSectionBasis]
      rw [Module.Basis.map_apply, Pi.basisFun_apply]
      rfl
    _ = y := b.sum_repr y

/-- A free scheme realization with the specified marking consists of the
original primitive sheaf morphisms and marking sheaf morphisms. -/
abbrev NormalizedSchemeMarkedTensor :=
  FreeSchemePrimitive X sig rank × NormalizedSchemeMarking X sig rank generators choice

/-- Reading a free marked realization gives the actual operation and marking coordinates. -/
def normalizedSchemeMarkedTensorCoordinates :
    NormalizedSchemeMarkedTensor X sig rank generators choice ≃
      MarkedCoordinatePair sig rank generators choice Γ(X, ⊤) :=
  Equiv.prodCongr (freeSchemePrimitiveCoordinateEquiv X sig rank)
    (normalizedSchemeMarkingEquiv X sig rank generators choice)

variable {R : Type u} [CommRing R]
  {J : Type u} (laws : MarkedPolynomialLaws (R := R) sig J)
  (T : Over (Spec (CommRingCat.of R)))

/-- The normalized scheme chart of marked realizations with all the specified
polynomial Laws on the actual global section structure. -/
abbrev LawfulNormalizedSchemeMarking :=
  letI := globalSectionsAlgebra T
  {P : NormalizedSchemeMarkedTensor T.left sig rank generators choice //
    ∀ j, (laws.law j).Holds (algebraMap R Γ(T.left, ⊤))
      (P.1.sectionStructure T.left sig rank (op (⊤ : T.left.Opens)))}

/-- The affine chart gives actual primitive and marking morphisms on the
chosen free sheaf carriers of every relative test scheme. -/
def markedChartRealizationEquiv :
    (T ⟶ markedChartScheme sig rank generators choice laws) ≃
      LawfulNormalizedSchemeMarking sig rank generators choice laws T := by
  letI := globalSectionsAlgebra T
  let reading := normalizedSchemeMarkedTensorCoordinates T.left sig rank generators choice
  let lawful : LawfulNormalizedSchemeMarking sig rank generators choice laws T ≃
      LawfulMarkedCoordinates sig rank generators choice laws Γ(T.left, ⊤) :=
    reading.subtypeEquiv fun A => forall_congr' fun j =>
      (laws.law j).holds_iff_of_iso (algebraMap R Γ(T.left, ⊤))
        (freeSchemePrimitive_globalStructureIso T.left sig rank A.1)
  exact (markedChartCoordinatePointEquiv sig rank generators choice laws T).trans lawful.symm

end

end SHIGURE.RealizationFamilies
