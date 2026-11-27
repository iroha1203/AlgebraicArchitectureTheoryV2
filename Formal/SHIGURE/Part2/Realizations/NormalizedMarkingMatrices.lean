import Formal.SHIGURE.Part2.Realizations.MarkedChartSpecialization

/-! # The full marking matrices with specified identity columns -/

namespace SHIGURE.RealizationFamilies

open SHIGURE.TensorRealization

noncomputable section

universe u

variable {R : Type u} [CommRing R]
  (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)
  (choice : MarkedBasisChoice sig rank generators)

/-- A full coordinate matrix at every sort, with the chosen columns equal to the unit columns. -/
abbrev NormalizedMarkingMatrices :=
  {P : ∀ s, Matrix (Fin (rank s)) (Fin (generators s)) R //
    ∀ s i j, P s i (choice s j) = if i = j then 1 else 0}

/-- The free marking coordinates determine the original full matrices uniquely. -/
def normalizedMarkingMatricesEquiv :
    NormalizedMarkingMatrices (R := R) sig rank generators choice ≃
      (MarkingCoordinate sig rank generators choice → R) where
  toFun P z := P.val z.1 z.2.1 z.2.2.val
  invFun v := ⟨markingMatrix sig rank generators choice v,
    markingMatrix_selected sig rank generators choice v⟩
  left_inv P := by
    apply Subtype.ext
    funext s
    ext i j
    let read (z : MarkingCoordinate sig rank generators choice) := P.val z.1 z.2.1 z.2.2.val
    change markingMatrix sig rank generators choice read s i j = P.val s i j
    by_cases selected : j ∈ Set.range (choice s)
    · obtain ⟨k, rfl⟩ := selected
      exact (markingMatrix_selected sig rank generators choice read s i k).trans
        (P.property s i k).symm
    · exact markingMatrix_nonselected sig rank generators choice read s i j selected
  right_inv v := by
    funext z
    obtain ⟨s, i, j, h⟩ := z
    exact markingMatrix_nonselected sig rank generators choice v s i j h

end

end SHIGURE.RealizationFamilies
