import Formal.SHIGURE.Part2.Realizations.MarkedChart

/-! # Actual markings in a chosen free chart -/

namespace SHIGURE.RealizationFamilies

open CategoryTheory Module SHIGURE.TensorRealization

noncomputable section

universe u

variable {R : Type u} [CommRing R]
  (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank generators)

/-- An original tensor realization whose chosen marking columns are its bases. -/
structure BasedMarkedTensor where
  realization : TensorStructure R sig
  basis : ∀ s, Basis (Fin (rank s)) R (realization.carrier s)
  marking : ∀ s, (Fin (generators s) → R) →ₗ[R] realization.carrier s
  selected : ∀ s j, marking s (Pi.single (choice s j) 1) = basis s j

namespace BasedMarkedTensor

variable (E : BasedMarkedTensor (R := R) sig rank generators choice)

/-- The selected basis sections imply that the original marking is surjective. -/
theorem marking_surjective (s : sig.SortType) : Function.Surjective (E.marking s) := by
  rw [← LinearMap.range_eq_top, ← (E.basis s).span_eq]
  apply le_antisymm
  · rw [(E.basis s).span_eq]
    exact le_top
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single (choice s j) 1, E.selected s j⟩

/-- The coordinates of the nonselected generators of the original marking. -/
def readMarking : MarkingCoordinate sig rank generators choice → R :=
  fun z => (E.basis z.1).equivFun (E.marking z.1 (Pi.single z.2.2.val 1)) z.2.1

/-- A basis vector has its original unit column in these coordinates. -/
private theorem basis_equivFun_apply {V : Type u} [AddCommGroup V] [Module R V]
    {n : ℕ} (b : Basis (Fin n) R V) (i j : Fin n) :
    b.equivFun (b j) i = if i = j then 1 else 0 := by
  simp [eq_comm]

/-- The reconstructed marking is the actual map read in the chosen basis. -/
theorem markingMap_readMarking (s : sig.SortType) :
    markingMap sig rank generators choice (E.readMarking sig rank generators choice) s =
      (E.basis s).equivFun.toLinearMap.comp (E.marking s) := by
  classical
  apply (Pi.basisFun R (Fin (generators s))).ext
  intro j
  rw [Pi.basisFun_apply]
  ext i
  change (markingMap sig rank generators choice (E.readMarking sig rank generators choice) s (Pi.single j 1)) i =
    (E.basis s).equivFun (E.marking s (Pi.single j 1)) i
  rw [markingMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
  change markingMatrix sig rank generators choice
      (E.readMarking sig rank generators choice) s i j = _
  by_cases selected : j ∈ Set.range (choice s)
  · obtain ⟨k, rfl⟩ := selected
    rw [markingMatrix_selected, E.selected, basis_equivFun_apply]
  · exact markingMatrix_nonselected _ _ _ _ _ _ _ _ selected

/-- An arrow preserving a surjective marking is determined by that marking. -/
theorem hom_ext_marking {F : TensorStructure R sig} {f g : E.realization ⟶ F}
    (same : ∀ s, (f.onSort s).comp (E.marking s) = (g.onSort s).comp (E.marking s)) : f = g := by
  apply TensorStructure.Hom.ext
  funext s
  ext x
  obtain ⟨y, rfl⟩ := E.marking_surjective sig rank generators choice s x
  exact LinearMap.congr_fun (same s) y

/-- The universal coordinates reconstruct the actual free structure and the actual marking. -/
def ofCoordinates (c : PrimitiveCoefficients sig rank R)
    (v : MarkingCoordinate sig rank generators choice → R) :
    BasedMarkedTensor (R := R) sig rank generators choice where
  realization := c.toTensor sig rank
  basis _ := Pi.basisFun R _
  marking := markingMap sig rank generators choice v
  selected := markingMap_selected sig rank generators choice v

/-- The normalized primitive coordinates of the original free realization. -/
def readCoefficients : PrimitiveCoefficients sig rank R :=
  PrimitiveCoefficients.ofTensor sig rank E.realization E.basis

/-- The chosen coordinates identify the original structure with the reconstructed marked structure. -/
def normalizeIso :
    E.realization ≅
      (ofCoordinates sig rank generators choice (E.readCoefficients sig rank generators choice)
        (E.readMarking sig rank generators choice)).realization :=
  PrimitiveCoefficients.tensorIsoOfBasis sig rank E.realization E.basis

/-- The actual structural isomorphism obtained by reading a basis preserves every marking column. -/
theorem normalizeIso_marking (s : sig.SortType) :
    ((E.normalizeIso sig rank generators choice).hom.onSort s).comp (E.marking s) =
      (ofCoordinates sig rank generators choice (E.readCoefficients sig rank generators choice)
        (E.readMarking sig rank generators choice)).marking s :=
  (E.markingMap_readMarking sig rank generators choice s).symm

/-- Reading a reconstructed realization recovers its original primitive coordinates. -/
theorem readCoefficients_ofCoordinates (c : PrimitiveCoefficients sig rank R)
    (v : MarkingCoordinate sig rank generators choice → R) :
    (ofCoordinates sig rank generators choice c v).readCoefficients sig rank generators choice = c :=
  PrimitiveCoefficients.ofTensor_toTensor sig rank c

/-- Reading the nonselected columns of the reconstruction returns the given entries. -/
theorem readMarking_ofCoordinates (c : PrimitiveCoefficients sig rank R)
    (v : MarkingCoordinate sig rank generators choice → R) :
    (ofCoordinates sig rank generators choice c v).readMarking sig rank generators choice = v := by
  funext z
  obtain ⟨s, i, j, h⟩ := z
  change (Pi.basisFun R (Fin (rank s))).equivFun
    (markingMap sig rank generators choice v s (Pi.single j 1)) i = _
  rw [Pi.basisFun_equivFun, LinearEquiv.refl_apply, markingMap, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one]
  exact markingMatrix_nonselected _ _ _ _ _ _ _ _ h

end BasedMarkedTensor

end

end SHIGURE.RealizationFamilies
