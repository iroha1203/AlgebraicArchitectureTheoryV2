import ResearchLean.AG.RelativeRepairComposition.W1LocalDifferentials

/-!
# Complete original local equation criteria for the actual W1 reference defect

These equivalences quantify over all original local cochains before generation.
The full actual signed defect is read at each authored face. U imposes u+z=x;
V imposes u-z+v=y and retains the entire private a kernel.
-/
namespace AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
open W1LocalDifferentials
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "rhs" U => RelativeCover.r2 (M) fixedRegion (ClosedRegion.to_all U) (-actualDefect true x y)

/-- The original signed U reference defect reads the input x on its whole sole face kernel. -/
theorem left_rhs : kernelCoordinate true x y () ((rhs leftRegion).1 ⟨false, rfl⟩) = x := by
  have h := signedDefect_coordinates true x y false
  exact h

/-- The original signed V reference defect reads y on the same complete authored second face. -/
theorem right_rhs : kernelCoordinate true x y () ((rhs rightRegion).1 ⟨true, rfl⟩) = y := by
  have h := signedDefect_coordinates true x y true
  simpa only [ite_true] using h

/-- The complete independent U equation is exactly u+z=x on all its original local cochains. -/
theorem left_equation_iff (a : RelativeCover.C1 (M) leftRegion fixedRegion) :
    RelativeCover.d1 (M) leftRegion fixedRegion a = (rhs leftRegion) ↔
      value x y leftRegion a ⟨name edgeE, Or.inl rfl⟩ +
        value x y leftRegion a ⟨name edgeB, Or.inr (Or.inl rfl)⟩ = x := by
  constructor
  · intro h
    rw [← left_differential]
    rw [h]
    exact left_rhs x y
  · intro h
    apply Subtype.ext
    funext f
    rcases f with ⟨f, hf⟩
    have hf' : (f : Bool) = false := hf
    subst f
    apply (kernelCoordinate true x y ()).injective
    exact (left_differential x y a).trans (h.trans (left_rhs x y).symm)

/-- The complete independent V equation is exactly u-z+v=y, on all local cochains including every private h value. -/
theorem right_equation_iff (a : RelativeCover.C1 (M) rightRegion fixedRegion) :
    RelativeCover.d1 (M) rightRegion fixedRegion a = (rhs rightRegion) ↔
      value x y rightRegion a ⟨name edgeE, Or.inl rfl⟩ -
        value x y rightRegion a ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ +
          value x y rightRegion a ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ = y := by
  constructor
  · intro h
    rw [← right_differential]
    rw [h]
    exact right_rhs x y
  · intro h
    apply Subtype.ext
    funext f
    rcases f with ⟨f, hf⟩
    have hf' : (f : Bool) = true := hf
    subst f
    apply (kernelCoordinate true x y ()).injective
    exact (right_differential x y a).trans (h.trans (right_rhs x y).symm)

end AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1LocalEquationCriteria
