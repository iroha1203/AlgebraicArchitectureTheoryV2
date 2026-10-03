import ResearchLean.AG.RelativeRepairComposition.W1LocalInterfaces

/-!
# The original authored U,V differential values before local elimination

The formulas evaluate each complete local cochain of the original relative
complex. The physical rx,ry values vanish by their original fixed-region
membership. Both occurrences of a are retained in the second authored word;
the private h column cancels by its actual negative transport.
-/
namespace AAT.AG.RelativeRepairComposition.W1LocalDifferentials
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1Regions W1FiniteCoefficients W1RelativeCoefficients W1IndexedCover
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower true x y))

/-- Every full original local edge value is read in its entire original kernel. -/
noncomputable def value (U : ClosedRegion geometry) (a : RelativeCover.C1 (M) U fixedRegion)
    (e : U.edges) : ZMod 3 := kernelCoordinate true x y e.1.2.1 (a.1 e)

/-- Extending a full local original cochain retains every original included edge value. -/
theorem extension_value (U : ClosedRegion geometry) (a : RelativeCover.C1 (M) U fixedRegion)
    (e : EdgeName (K := geometry)) (he : e ∈ U.edges) :
    kernelCoordinate true x y e.2.1 ((ClosedRegion.e1 (M) U a.1) e) = value x y U a ⟨e, he⟩ := by
  rw [ClosedRegion.e1, Family.extend_on]
  rfl

/-- The named original loop has the same literal original terminal vertex in extension. -/
theorem extension_named (U : ClosedRegion geometry) (a : RelativeCover.C1 (M) U fixedRegion)
    (e : Fin 6) (he : name e ∈ U.edges) :
    kernelCoordinate true x y () ((ClosedRegion.e1 (M) U a.1) (name e)) =
      value x y U a ⟨name e, he⟩ :=
  extension_value x y U a (name e) he

/-- Physical fixed original edge values vanish in the full local cochain. -/
theorem fixed_value (U : ClosedRegion geometry) (a : RelativeCover.C1 (M) U fixedRegion)
    (e : U.edges) (he : e.1 ∈ fixedRegion.edges) : value x y U a e = 0 := by
  rw [value, a.2 e he, map_zero]

/-- The complete U differential reads u+z with no private edge elimination assumption. -/
theorem left_differential (a : RelativeCover.C1 (M) leftRegion fixedRegion) :
    kernelCoordinate true x y () ((RelativeCover.d1 (M) leftRegion fixedRegion a).1 ⟨false, rfl⟩) =
      value x y leftRegion a ⟨name edgeE, Or.inl rfl⟩ +
        value x y leftRegion a ⟨name edgeB, Or.inr (Or.inl rfl)⟩ := by
  change kernelCoordinate true x y () (d1 (M) (ClosedRegion.e1 (M) leftRegion a.1) false) = _
  rw [d1_first, extension_named x y leftRegion a edgeE (Or.inl rfl),
    extension_named x y leftRegion a edgeB (Or.inr (Or.inl rfl)),
    extension_named x y leftRegion a edgeRx (Or.inr (Or.inr rfl)),
    fixed_value x y leftRegion a ⟨name edgeRx, Or.inr (Or.inr rfl)⟩ (Or.inl rfl), sub_zero]

/-- The complete V differential reads u-z+v, deriving the cancellation of the entire private a kernel. -/
theorem right_differential (a : RelativeCover.C1 (M) rightRegion fixedRegion) :
    kernelCoordinate true x y () ((RelativeCover.d1 (M) rightRegion fixedRegion a).1 ⟨true, rfl⟩) =
      value x y rightRegion a ⟨name edgeE, Or.inl rfl⟩ -
        value x y rightRegion a ⟨name edgeB, Or.inr (Or.inr (Or.inl rfl))⟩ +
          value x y rightRegion a ⟨name edgeC, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩ := by
  change kernelCoordinate true x y () (d1 (M) (ClosedRegion.e1 (M) rightRegion a.1) true) = _
  rw [d1_second_negative,
    extension_named x y rightRegion a edgeE (Or.inl rfl),
    extension_named x y rightRegion a edgeB (Or.inr (Or.inr (Or.inl rfl))),
    extension_named x y rightRegion a edgeC (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
    extension_named x y rightRegion a edgeRy (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
    fixed_value x y rightRegion a ⟨name edgeRy, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩ (Or.inr rfl), sub_zero]

end AAT.AG.RelativeRepairComposition.W1LocalDifferentials
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1LocalDifferentials
