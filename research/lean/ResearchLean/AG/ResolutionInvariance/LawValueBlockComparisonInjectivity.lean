import ResearchLean.AG.ResolutionInvariance.ResolutionInvarianceConditions
import Formal.Util.AssertStandardAxioms

/-!
# Injectivity of generated comparison on exact law-value blocks

This module proves the injective half of resolution invariance on one exact
source-generated `(law, value)` block.  C0 supplies a fine occurrence above
each coarse block chart, C1 makes a fine primitive constant along each chart
fiber, C2 supplies an exact lift of every coarse block edge, and C6 prevents a
mapped coarse self-loop from changing that primitive inside its fine fiber.

Representatives chosen from the existential hypotheses occur only inside the
proof.  No section, path, primitive, inverse, or cohomology certificate is
added to the comparison data or to the condition package.  C3, C4, and C5 are
reserved for the separate surjectivity argument.
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

/-! ## Chart and endpoint lifting -/

/-- C0 transports an actual coarse K0 occurrence back to a fine occurrence,
so the canonical exact-block chart map is surjective. -/
theorem conditionC0_chartBlockCoordinateMap_surjective
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC0 : M.ConditionC0)
    (label : LawValueLabel laws) :
    Function.Surjective
      (M.chartBlockCoordinateMap laws hcoarse hfine label) := by
  intro coarseChart
  obtain ⟨coarseTarget, hcoarseTarget, hvalue⟩ := coarseChart.1.generated
  obtain ⟨fineChart, fineTarget, hchart, hfineTarget, hfactor⟩ :=
    (hC0 coarseChart.1.cell coarseTarget).mp hcoarseTarget
  let fineCoordinate : fine.ChartCoordinate laws hfine :=
    ⟨fineChart, coarseChart.1.law, coarseChart.1.value, by
      refine ⟨fineTarget, hfineTarget, ?_⟩
      calc
        lawDescend laws fineReading hfine coarseChart.1.law fineTarget =
            lawDescend laws coarseReading hcoarse coarseChart.1.law
              (comparisonFactor coarseReading fineReading hcoarser
                fineTarget) :=
          (lawDescend_comparisonFactor laws coarseReading fineReading hcoarse
            hfine hcoarser coarseChart.1.law fineTarget).symm
        _ = lawDescend laws coarseReading hcoarse coarseChart.1.law
              coarseTarget := by rw [hfactor]
        _ = coarseChart.1.value := hvalue⟩
  have hfineLabel :
      fineCoordinate.lawValueLabel laws fineReading hfine
          fine.nerve.Chart fine.chartSupport = label := by
    calc
      fineCoordinate.lawValueLabel laws fineReading hfine
          fine.nerve.Chart fine.chartSupport =
          coarseChart.1.lawValueLabel laws coarseReading hcoarse
            coarse.nerve.Chart coarse.chartSupport := by
        apply LawValueLabel.ext
        · rfl
        · rfl
      _ = label := coarseChart.2
  let fineBlock : fine.ChartBlockCoordinate laws hfine label :=
    ⟨fineCoordinate, hfineLabel⟩
  refine ⟨fineBlock, ?_⟩
  apply Subtype.ext
  apply CellCoordinate.ext
  · exact hchart
  · rfl
  · rfl

/-- An exact partial edge image identifies the transported left endpoint with
the left endpoint of the specified coarse block edge. -/
theorem chartBlockCoordinateMap_edgeLeft_of_edgeBlockCoordinateMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label)
    (hmap : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge =
      some coarseEdge) :
    M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeLeftBlockCoordinate laws hfine label fineEdge) =
      coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge := by
  unfold edgeBlockCoordinateMapOption at hmap
  split at hmap
  · contradiction
  · rename_i mappedEdge hwhole
    have hcoordinate :
        M.edgeBlockCoordinateMap laws hcoarse hfine label fineEdge mappedEdge
            hwhole = coarseEdge :=
      Option.some.inj hmap
    rw [← hcoordinate]
    exact M.chartBlockCoordinateMap_edgeLeftBlockCoordinate laws hcoarse hfine
      label fineEdge mappedEdge hwhole

/-- An exact partial edge image identifies the transported right endpoint with
the right endpoint of the specified coarse block edge. -/
theorem chartBlockCoordinateMap_edgeRight_of_edgeBlockCoordinateMapOption_eq_some
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (fineEdge : fine.EdgeBlockCoordinate laws hfine label)
    (coarseEdge : coarse.EdgeBlockCoordinate laws hcoarse label)
    (hmap : M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge =
      some coarseEdge) :
    M.chartBlockCoordinateMap laws hcoarse hfine label
        (fine.edgeRightBlockCoordinate laws hfine label fineEdge) =
      coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge := by
  unfold edgeBlockCoordinateMapOption at hmap
  split at hmap
  · contradiction
  · rename_i mappedEdge hwhole
    have hcoordinate :
        M.edgeBlockCoordinateMap laws hcoarse hfine label fineEdge mappedEdge
            hwhole = coarseEdge :=
      Option.some.inj hmap
    rw [← hcoordinate]
    exact M.chartBlockCoordinateMap_edgeRightBlockCoordinate laws hcoarse hfine
      label fineEdge mappedEdge hwhole

/-! ## Constancy of fine primitives on chart fibers -/

/-- If a pulled coarse one-cochain is the coboundary of a fine zero-cochain,
then that zero-cochain has equal values across one coordinate-fiber adjacency.
The degenerate branch uses the zero pullback; the mapped branch uses C6. -/
theorem fineZero_eq_of_coordinateFiberAdjacent
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (hC6 : M.ConditionC6)
    (label : LawValueLabel laws)
    (coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ)
    (fineZero : fine.ChartBlockCoordinate laws hfine label → ℚ)
    (hboundary :
      M.generatedBlockPullback1 laws hcoarse hfine label coarseOne =
        fine.lawValueBlockD0 laws hfine label fineZero)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (left right : fine.ChartBlockCoordinate laws hfine label)
    (hadjacent : M.CoordinateFiberAdjacent laws hcoarse hfine label
      coarseChart left right) :
    fineZero left = fineZero right := by
  obtain ⟨fineEdge, hfiber, horientation⟩ := hadjacent
  have hedge :
      fineZero (fine.edgeLeftBlockCoordinate laws hfine label fineEdge) =
        fineZero (fine.edgeRightBlockCoordinate laws hfine label fineEdge) := by
    cases hoption :
        M.edgeBlockCoordinateMapOption laws hcoarse hfine label fineEdge with
    | none =>
        have hvalue := congrFun hboundary fineEdge
        rw [M.generatedBlockPullback1_apply, hoption] at hvalue
        change 0 =
          fineZero (fine.edgeRightBlockCoordinate laws hfine label fineEdge) -
            fineZero (fine.edgeLeftBlockCoordinate laws hfine label fineEdge)
          at hvalue
        exact (sub_eq_zero.mp hvalue.symm).symm
    | some coarseEdge =>
        have hleft :=
          M.chartBlockCoordinateMap_edgeLeft_of_edgeBlockCoordinateMapOption_eq_some
            laws hcoarse hfine label fineEdge coarseEdge hoption
        have hright :=
          M.chartBlockCoordinateMap_edgeRight_of_edgeBlockCoordinateMapOption_eq_some
            laws hcoarse hfine label fineEdge coarseEdge hoption
        have hloop :
            coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge =
              coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge := by
          rw [← hleft, ← hright, hfiber.1, hfiber.2]
        exact congrArg fineZero
          (M.conditionC6_block_endpoint_reflection laws hcoarse hfine hC6 label
            fineEdge coarseEdge hoption hloop)
  rcases horientation with horientation | horientation
  · rw [horientation.1, horientation.2] at hedge
    exact hedge
  · rw [horientation.1, horientation.2] at hedge
    exact hedge.symm

/-- Under C1 connectivity, a fine primitive of a pulled coarse one-cochain is
constant on the entire exact coordinate fiber. -/
theorem fineZero_eq_of_same_coordinateFiber
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC1 : M.ConditionC1At laws hcoarse hfine label)
    (hC6 : M.ConditionC6)
    (coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ)
    (fineZero : fine.ChartBlockCoordinate laws hfine label → ℚ)
    (hboundary :
      M.generatedBlockPullback1 laws hcoarse hfine label coarseOne =
        fine.lawValueBlockD0 laws hfine label fineZero)
    (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label)
    (left right : fine.ChartBlockCoordinate laws hfine label)
    (hleft : M.chartBlockCoordinateMap laws hcoarse hfine label left =
      coarseChart)
    (hright : M.chartBlockCoordinateMap laws hcoarse hfine label right =
      coarseChart) :
    fineZero left = fineZero right := by
  have hpath := (hC1 coarseChart).2 left right hleft hright
  have hstep : ∀ {first second},
      M.CoordinateFiberAdjacent laws hcoarse hfine label coarseChart
          first second →
        fineZero first = fineZero second := by
    intro first second hadjacent
    exact M.fineZero_eq_of_coordinateFiberAdjacent laws hcoarse hfine hC6 label
      coarseOne fineZero hboundary coarseChart first second hadjacent
  exact Relation.ReflTransGen.trans_induction_on hpath
    (fun _ => rfl)
    (fun hadjacent => hstep hadjacent)
    (fun _ _ hfirst hsecond => hfirst.trans hsecond)

/-! ## Coboundary reflection and block H1 injectivity -/

/-- C0, C1, C2, and C6 reflect a fine primitive of a generated pulled
one-cochain to a coarse primitive.  The chart representatives are selected
only locally from the C0 surjectivity proof. -/
theorem exists_coarse_zero_cochain_of_generatedBlockPullback1_eq_d0
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC0 : M.ConditionC0)
    (hC1 : M.ConditionC1At laws hcoarse hfine label)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC6 : M.ConditionC6)
    (coarseOne : coarse.EdgeBlockCoordinate laws hcoarse label → ℚ)
    (fineZero : fine.ChartBlockCoordinate laws hfine label → ℚ)
    (hboundary :
      M.generatedBlockPullback1 laws hcoarse hfine label coarseOne =
        fine.lawValueBlockD0 laws hfine label fineZero) :
    ∃ coarseZero : coarse.ChartBlockCoordinate laws hcoarse label → ℚ,
      coarse.lawValueBlockD0 laws hcoarse label coarseZero = coarseOne := by
  classical
  let fineRepresentative :
      coarse.ChartBlockCoordinate laws hcoarse label →
        fine.ChartBlockCoordinate laws hfine label := fun coarseChart =>
    Classical.choose
      (M.conditionC0_chartBlockCoordinateMap_surjective laws hcoarse hfine hC0
        label coarseChart)
  have hfineRepresentative
      (coarseChart : coarse.ChartBlockCoordinate laws hcoarse label) :
      M.chartBlockCoordinateMap laws hcoarse hfine label
          (fineRepresentative coarseChart) = coarseChart :=
    Classical.choose_spec
      (M.conditionC0_chartBlockCoordinateMap_surjective laws hcoarse hfine hC0
        label coarseChart)
  let coarseZero : coarse.ChartBlockCoordinate laws hcoarse label → ℚ :=
    fun coarseChart => fineZero (fineRepresentative coarseChart)
  refine ⟨coarseZero, ?_⟩
  funext coarseEdge
  obtain ⟨fineEdge, hmap⟩ := hC2 coarseEdge
  have hleftMap :=
    M.chartBlockCoordinateMap_edgeLeft_of_edgeBlockCoordinateMapOption_eq_some
      laws hcoarse hfine label fineEdge coarseEdge hmap
  have hrightMap :=
    M.chartBlockCoordinateMap_edgeRight_of_edgeBlockCoordinateMapOption_eq_some
      laws hcoarse hfine label fineEdge coarseEdge hmap
  have hleftValue :=
    M.fineZero_eq_of_same_coordinateFiber laws hcoarse hfine label hC1 hC6
      coarseOne fineZero hboundary
      (coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge)
      (fineRepresentative
        (coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge))
      (fine.edgeLeftBlockCoordinate laws hfine label fineEdge)
      (hfineRepresentative
        (coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge))
      hleftMap
  have hrightValue :=
    M.fineZero_eq_of_same_coordinateFiber laws hcoarse hfine label hC1 hC6
      coarseOne fineZero hboundary
      (coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge)
      (fineRepresentative
        (coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge))
      (fine.edgeRightBlockCoordinate laws hfine label fineEdge)
      (hfineRepresentative
        (coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge))
      hrightMap
  have hvalue := congrFun hboundary fineEdge
  rw [M.generatedBlockPullback1_apply, hmap] at hvalue
  change
    coarseZero (coarse.edgeRightBlockCoordinate laws hcoarse label coarseEdge) -
        coarseZero (coarse.edgeLeftBlockCoordinate laws hcoarse label coarseEdge) =
      coarseOne coarseEdge
  dsimp [coarseZero]
  rw [hleftValue, hrightValue]
  exact hvalue.symm

/-- On every exact source-generated block, C0, C1, C2, and C6 make the actual
G-102 cohomology map induced by the generated comparison Hom injective. -/
theorem generatedBlockComparisonH1Map_injective [Fintype Source]
    (M : TargetSupportedNerveMorphism coarseReading fineReading hcoarser
      coarse fine)
    (laws : FiniteLawFamily Source)
    (hcoarse : laws.Adequate coarseReading)
    (hfine : laws.Adequate fineReading)
    (label : LawValueLabel laws)
    (hC0 : M.ConditionC0)
    (hC1 : M.ConditionC1At laws hcoarse hfine label)
    (hC2 : M.ConditionC2At laws hcoarse hfine label)
    (hC6 : M.ConditionC6) :
    Function.Injective
      (M.generatedBlockComparisonH1Map laws hcoarse hfine label) := by
  intro left right hequal
  apply sub_eq_zero.mp
  have hzero :
      M.generatedBlockComparisonH1Map laws hcoarse hfine label
          (left - right) = 0 := by
    rw [map_sub, hequal, sub_self]
  obtain ⟨cycle, hcycle⟩ :=
    (LinearMap.range
      (coarse.lawValueBlockComplex laws hcoarse label).boundaryToCycles).mkQ_surjective
        (left - right)
  have hcycleZero :
      M.generatedBlockComparisonH1Map laws hcoarse hfine label
          ((LinearMap.range
            (coarse.lawValueBlockComplex laws hcoarse label).boundaryToCycles).mkQ
              cycle) = 0 := by
    rw [hcycle]
    exact hzero
  change
    (LinearMap.range
      (fine.lawValueBlockComplex laws hfine label).boundaryToCycles).mkQ
        ((M.generatedBlockComparisonHom laws hcoarse hfine label).cyclesMap
          cycle) = 0 at hcycleZero
  have hfineBoundary :
      (M.generatedBlockComparisonHom laws hcoarse hfine label).cyclesMap cycle ∈
        LinearMap.range
          (fine.lawValueBlockComplex laws hfine label).boundaryToCycles :=
    (Submodule.Quotient.mk_eq_zero _).1 hcycleZero
  obtain ⟨fineZero, hfineZero⟩ := hfineBoundary
  have hpullback :
      M.generatedBlockPullback1 laws hcoarse hfine label cycle.1 =
        fine.lawValueBlockD0 laws hfine label fineZero :=
    (congrArg Subtype.val hfineZero).symm
  obtain ⟨coarseZero, hcoarseZero⟩ :=
    M.exists_coarse_zero_cochain_of_generatedBlockPullback1_eq_d0 laws
      hcoarse hfine label hC0 hC1 hC2 hC6 cycle.1 fineZero hpullback
  rw [← hcycle]
  apply (Submodule.Quotient.mk_eq_zero _).2
  refine ⟨coarseZero, ?_⟩
  apply Subtype.ext
  exact hcoarseZero

end TargetSupportedNerveMorphism

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
