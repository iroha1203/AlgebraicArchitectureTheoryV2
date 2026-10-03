import ResearchLean.AG.RelativeRepairComposition.W1RelativeCoefficients
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeEquations
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The actual W1 always image and its full original cokernel

## Implementation notes

The source is the entire original alwaysSpace, with both u,h free. The face
reading r2-r1 is generated from the same original relative d1. Equality of its
kernel with the actual always image constructs the whole cokernel equivalence;
the signed obstruction is read from the original real defect, not supplied.
-/
namespace AAT.AG.RelativeRepairComposition.W1OriginalObstruction
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W1AffineInput W1AuthoredOperations W1Regions W1ActualRepairs
open W1FiniteCoefficients W1RelativeCoefficients
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000

variable (x y : ZMod 3)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower true x y))
local notation "D" => OriginalColumns.D (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y)

/-- Original named edge equality retains the complete one-vertex six-loop incidence. -/
local instance edgeNameDecidableEq : DecidableEq (EdgeName (K := geometry)) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Σ _ : Unit, Fin 6))

/-- All-cell membership is decided directly on every original complete edge name. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := geometry)).edges) :=
  fun _ => isTrue trivial

/-- Both full always kernel coordinates u,h give an actual original always cochain. -/
noncomputable def alwaysCochain (u h : ZMod 3) : OriginalColumns.alwaysSpace (k := ZMod 3) (M) fixedRegion candidates :=
  ⟨relativeCochain true x y u h 0 0, by
    intro e
    rcases e with ⟨e, he⟩
    rcases he with he | he <;> subst e
    · apply (kernelCoordinate true x y ()).injective
      change edgeCoordinate true x y (relativeCochain true x y u h 0 0) (name edgeB) =
        kernelCoordinate true x y () 0
      rw [relativeCochain_value, map_zero]
      simp [geometry, name, correctionValue, edgeE, edgeA, edgeB]
    · apply (kernelCoordinate true x y ()).injective
      change edgeCoordinate true x y (relativeCochain true x y u h 0 0) (name edgeC) =
        kernelCoordinate true x y () 0
      rw [relativeCochain_value, map_zero]
      simp [geometry, name, correctionValue, edgeE, edgeA, edgeB, edgeC]⟩

/-- The full original always map sends u,h to (u,u); its private h column is derived to vanish. -/
theorem always_first_value (a : OriginalColumns.alwaysSpace (k := ZMod 3) (M) fixedRegion candidates) :
    faceCoordinates true x y ((D) a) false = edgeCoordinate true x y a.1 (name edgeE) := by
  rw [OriginalColumns.D_apply, FiniteCoefficients.differential1_eq]
  have hv := relative_d1_first true x y a.1
  rw [FiniteCoefficients.differential1_eq] at hv
  rw [hv]
  have hb := a.2 ⟨name edgeB, Or.inl rfl⟩
  simp [edgeCoordinate, hb]

/-- Both authored a contributions cancel in the actual always second component, preserving every original h. -/
theorem always_second_value (a : OriginalColumns.alwaysSpace (k := ZMod 3) (M) fixedRegion candidates) :
    faceCoordinates true x y ((D) a) true = edgeCoordinate true x y a.1 (name edgeE) := by
  rw [OriginalColumns.D_apply, FiniteCoefficients.differential1_eq]
  have hv := relative_d1_second_negative x y a.1
  rw [FiniteCoefficients.differential1_eq] at hv
  rw [hv]
  have hb := a.2 ⟨name edgeB, Or.inl rfl⟩
  have hc := a.2 ⟨name edgeC, Or.inr rfl⟩
  simp [edgeCoordinate, hb, hc]

/-- The first actual always image value is precisely every full input u. -/
theorem alwaysCochain_first (u h : ZMod 3) :
    faceCoordinates true x y ((D) (alwaysCochain x y u h)) false = u := by
  rw [always_first_value]
  change edgeCoordinate true x y (relativeCochain true x y u h 0 0) (name edgeE) = u
  rw [relativeCochain_value]
  simp [name, correctionValue]

/-- The second actual always image value is the same u, for the whole private h kernel. -/
theorem alwaysCochain_second (u h : ZMod 3) :
    faceCoordinates true x y ((D) (alwaysCochain x y u h)) true = u := by
  rw [always_second_value]
  change edgeCoordinate true x y (relativeCochain true x y u h 0 0) (name edgeE) = u
  rw [relativeCochain_value]
  simp [name, correctionValue]

/-- The original face reading is the second actual kernel coordinate minus the first. -/
noncomputable def obstructionReading : RelativeCover.C2 (M) ClosedRegion.all fixedRegion →ₗ[ZMod 3] ZMod 3 :=
  ((LinearMap.proj true : (Bool → ZMod 3) →ₗ[ZMod 3] ZMod 3) - LinearMap.proj false).comp
    (faceCoordinates true x y).toLinearMap

/-- The full original obstruction reading keeps the exact difference of every original face representative. -/
theorem obstructionReading_value (c : RelativeCover.C2 (M) ClosedRegion.all fixedRegion) :
    obstructionReading x y c = faceCoordinates true x y c true - faceCoordinates true x y c false := rfl

/-- Every original full F3 value occurs as an actual whole face representative reading. -/
theorem obstructionReading_surjective : Function.Surjective (obstructionReading x y) := by
  intro d
  refine ⟨(faceCoordinates true x y).symm (fun f => if f then d else 0), ?_⟩
  rw [obstructionReading_value, LinearEquiv.apply_symm_apply]
  simp

/-- The full actual always image is exactly the kernel of the derived original difference reading. -/
theorem always_range_eq_kernel : LinearMap.range (D) = LinearMap.ker (obstructionReading x y) := by
  apply le_antisymm
  · rintro c ⟨a, rfl⟩
    change obstructionReading x y ((D) a) = 0
    rw [obstructionReading_value, always_first_value, always_second_value, sub_self]
  · intro c hc
    have he : faceCoordinates true x y c true = faceCoordinates true x y c false :=
      sub_eq_zero.mp hc
    refine ⟨alwaysCochain x y (faceCoordinates true x y c false) 0, ?_⟩
    apply (faceCoordinates true x y).injective
    funext f
    cases f
    · exact alwaysCochain_first x y _ _
    · exact (alwaysCochain_second x y _ _).trans he.symm

/-- The entire original cokernel, not an image quotient, is the full F3 original difference coordinate. -/
noncomputable def obstructionCoordinate :
    OriginalRanges.ObstructionSpace (k := ZMod 3) (M) fixedRegion candidates (original_linear true x y) ≃ₗ[ZMod 3] ZMod 3 :=
  (Submodule.quotEquivOfEq (LinearMap.range (D)) (LinearMap.ker (obstructionReading x y))
    (always_range_eq_kernel x y)).trans
      ((obstructionReading x y).quotKerEquivOfSurjective (obstructionReading_surjective x y))

/-- Every full original quotient representative evaluates by the derived difference reading. -/
theorem obstructionCoordinate_q (c : RelativeCover.C2 (M) ClosedRegion.all fixedRegion) :
    obstructionCoordinate x y (LinearInterface.q (D) c) = obstructionReading x y c := by
  rw [obstructionCoordinate, LinearEquiv.trans_apply]
  change (obstructionReading x y).quotKerEquivOfSurjective (obstructionReading_surjective x y)
    (Submodule.quotEquivOfEq _ _ (always_range_eq_kernel x y) (Submodule.Quotient.mk c)) = _
  rw [Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]

/-- The original actual obstruction is the same q(-delta) of the independently evaluated original reference defect. -/
noncomputable def obstruction := LinearInterface.q (D) (-actualDefect true x y)

/-- The actual obstruction coordinate is y-x, with sign derived from both original reference paths. -/
theorem obstruction_coordinate : obstructionCoordinate x y (obstruction x y) = y - x := by
  rw [obstruction, obstructionCoordinate_q, obstructionReading_value,
    signedDefect_coordinates, signedDefect_coordinates]
  simp

/-- Zero obstruction and equality of the two original input translations are exactly the same statement. -/
theorem obstruction_eq_zero_iff : obstruction x y = 0 ↔ y - x = 0 := by
  rw [← (obstructionCoordinate x y).map_eq_zero_iff, obstruction_coordinate]

end AAT.AG.RelativeRepairComposition.W1OriginalObstruction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W1OriginalObstruction
