import ResearchLean.AG.ResolutionInvariance.LawValueBlockComparisonFiberPrimitive
import Formal.Util.AssertStandardAxioms

/-!
# Normalizing exact law-value block cocycles along coordinate fibers

This module assembles the Cycle 18 primitive from every coarse chart fiber into
one fine degree-zero cochain.  A fine chart is evaluated by the local primitive
attached to its canonical image under `chartBlockCoordinateMap`.  Consequently,
both endpoints of a coordinate-fiber edge use the same local primitive, and the
actual residual `cycle - d0 primitive` vanishes on that edge.

The local primitives are chosen only inside the theorem proof.  They are not
stored in a condition, morphism, or certificate, and no representative chart,
path, or section is added.  This module does not yet descend the normalized
residual to a coarse cocycle or prove block `H^1` surjectivity.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution TwoPhase

universe u

variable {Source : Type u}

namespace TargetSupportedNerveMorphism

variable {coarseReading fineReading : Reading Source}
variable {hcoarser : coarseReading.CoarserThan fineReading}
variable {coarse : TargetSupportedNerve coarseReading}
variable {fine : TargetSupportedNerve fineReading}

/-- The Cycle 18 fiber primitives assemble into one fine zero-cochain whose
actual block residual vanishes on every endpoint-defined coordinate-fiber
edge.  The family of local primitives remains proof-local. -/
theorem lawValueBlockCycle_exists_coordinateFiberNormalization [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC3 : M.ConditionC3At laws hcoarse hfine label)
    (cycle :
      LinearMap.ker (fine.lawValueBlockComplex laws hfine label).d1) :
    ∃ primitive : fine.ChartBlockCoordinate laws hfine label → ℚ,
      ∀ coarseChart fineEdge,
        M.CoordinateFiberEdge laws hcoarse hfine label coarseChart fineEdge →
          cycle.1 fineEdge -
            fine.lawValueBlockD0 laws hfine label primitive fineEdge = 0 := by
  classical
  have hlocal :
      ∀ coarseChart : coarse.ChartBlockCoordinate laws hcoarse label,
        ∃ localPrimitive : fine.ChartBlockCoordinate laws hfine label → ℚ,
          ∀ fineEdge,
            M.CoordinateFiberEdge laws hcoarse hfine label coarseChart
                fineEdge →
              fine.lawValueBlockD0 laws hfine label localPrimitive fineEdge =
                cycle.1 fineEdge := fun coarseChart =>
    M.lawValueBlockCycle_exists_coordinateFiberPrimitive laws hcoarse hfine
      label hC3 cycle coarseChart
  let localPrimitive :
      coarse.ChartBlockCoordinate laws hcoarse label →
        fine.ChartBlockCoordinate laws hfine label → ℚ :=
    fun coarseChart => Classical.choose (hlocal coarseChart)
  let primitive : fine.ChartBlockCoordinate laws hfine label → ℚ :=
    fun fineChart =>
      localPrimitive
        (M.chartBlockCoordinateMap laws hcoarse hfine label fineChart)
        fineChart
  refine ⟨primitive, ?_⟩
  intro coarseChart fineEdge hedge
  have hlocalSpec :
      fine.lawValueBlockD0 laws hfine label (localPrimitive coarseChart)
          fineEdge = cycle.1 fineEdge := by
    simpa [localPrimitive] using
      (Classical.choose_spec (hlocal coarseChart) fineEdge hedge)
  rcases hedge with ⟨hleft, hright⟩
  have hassembled :
      fine.lawValueBlockD0 laws hfine label primitive fineEdge =
        fine.lawValueBlockD0 laws hfine label (localPrimitive coarseChart)
          fineEdge := by
    change
      primitive (fine.edgeRightBlockCoordinate laws hfine label fineEdge) -
          primitive (fine.edgeLeftBlockCoordinate laws hfine label fineEdge) =
        localPrimitive coarseChart
            (fine.edgeRightBlockCoordinate laws hfine label fineEdge) -
          localPrimitive coarseChart
            (fine.edgeLeftBlockCoordinate laws hfine label fineEdge)
    simp only [primitive]
    rw [hleft, hright]
  change cycle.1 fineEdge -
      fine.lawValueBlockD0 laws hfine label primitive fineEdge = 0
  rw [hassembled, hlocalSpec]
  exact sub_self _

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
