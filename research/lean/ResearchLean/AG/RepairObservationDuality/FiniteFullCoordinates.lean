import ResearchLean.AG.RepairObservationDuality.FullCorrectionCoordinates
import ResearchLean.AG.RepairObservationDuality.FiniteMatrixSolver
/-!
# G-131 D: one finite matrix index for every whole original correction

## Implementation notes

Flattening only rearranges the prescribed complete always and selected
coordinates. It removes no free variable and retains every original selected
candidate name. Both inverse maps are explicit coordinate functions. The
same differential can then be passed to G-130's finite matrix elimination.
-/
namespace AAT.AG.RepairObservationDuality.FiniteFullCoordinates
open TransportCoherence AbelianLiftingObstruction RelativeRepairComposition
set_option autoImplicit false
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A)
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K))) (S : Set candidates)

/-- D's matrix index retains each whole always coordinate and every selected candidate's whole kernel basis. -/
abbrev Index := FullCorrectionCoordinates.AlwaysIndex M bases P candidates ⊕
  (Σ e : S, Fin (bases.dimension e.1.1.2.1))

/-- D rearranges all prescribed correction coordinates into one finite vector with an explicit inverse. -/
def flatten : FullCorrectionCoordinates.NumericalValues M bases P candidates S ≃ₗ[k]
    (Index M bases P candidates S → k) :=
  ((LinearEquiv.refl k (FullCorrectionCoordinates.AlwaysIndex M bases P candidates → k)).prodCongr
    (LinearEquiv.piCurry k (fun (e : S) (_ : Fin (bases.dimension e.1.1.2.1)) => k)).symm).trans
    (LinearEquiv.sumArrowLequivProdArrow _ _ k k).symm

/-- The flattened always coordinate is precisely its original full prescribed coordinate. -/
theorem flatten_always (h : FullCorrectionCoordinates.NumericalValues M bases P candidates S)
    (j : FullCorrectionCoordinates.AlwaysIndex M bases P candidates) :
    flatten M bases P candidates S h (Sum.inl j) = h.1 j := rfl

/-- The flattened selected coordinate retains its original candidate name and whole kernel basis index. -/
theorem flatten_selected (h : FullCorrectionCoordinates.NumericalValues M bases P candidates S)
    (e : S) (j : Fin (bases.dimension e.1.1.2.1)) :
    flatten M bases P candidates S h (Sum.inr ⟨e,j⟩) = h.2 e j := rfl

/-- The inverse flattened vector restores each full always coordinate without choosing a representative. -/
theorem inverse_always (x : Index M bases P candidates S → k)
    (j : FullCorrectionCoordinates.AlwaysIndex M bases P candidates) :
    ((flatten M bases P candidates S).symm x).1 j = x (Sum.inl j) := rfl

/-- The inverse vector restores every selected candidate's complete prescribed basis values. -/
theorem inverse_selected (x : Index M bases P candidates S → k)
    (e : S) (j : Fin (bases.dimension e.1.1.2.1)) :
    ((flatten M bases P candidates S).symm x).2 e j = x (Sum.inr ⟨e,j⟩) := rfl

end AAT.AG.RepairObservationDuality.FiniteFullCoordinates
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteFullCoordinates
