import ResearchLean.AG.VisibleCycleReflection.WitnessInputs
import Formal.Util.AssertStandardAxioms

/-!
# Original integer chart sections for the specified repair witnesses

## Implementation notes

A finite original-presentation chart table is sent back to real coefficient
sections through the existing inverse normalization. Its actual differential is
used as the transition, and the original AAT state gluing theorem is applied to
that explicit correction. These helpers are instantiated with the prescribed
nonzero chart tables in W1 and W3.
-/

noncomputable section
open CategoryTheory TopologicalSpace Opposite
namespace AAT.AG.VisibleCycleReflection.FiniteInputTable
open CanonicalResolution ResolutionInvariance ObstructionDiagnosticBridge
variable (T : FiniteInputTable) (h : T.Valid)

/-- Restore original chart-group values to actual locally constant coefficient sections. -/
def chartCochain (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    ((T.actualPresentation h).faceEmptyCechComplex
      ((T.actualGeometry h).actualCechCover (T.actualPresentation h)
        (T.actualTarget h) (T.actualTarget_nonempty h))).Cn 0 := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact ((T.actualPresentation h).faceEmptyCechCochain0Equiv _).symm b

/-- Original chart normalization recovers exactly the given integer table. -/
theorem chartCochain_values (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    (T.actualPresentation h).faceEmptyCechCochain0Equiv _ (T.chartCochain h b) = b :=
by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact AddEquiv.apply_symm_apply _ b

/-- The real zero-state input with transition the actual differential of those chart sections. -/
def chartDifferenceInput (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    T.ActualLocalData h := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact {
    transition := ((T.actualPresentation h).faceEmptyCechComplex _).d 0 (T.chartCochain h b)
    localState := 0}

/-- The zero-state witness has its actual differential as its mismatch. -/
theorem chartDifferenceInput_mismatch (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    (T.chartDifferenceInput h b).actualMismatch =
      ((T.actualPresentation h).faceEmptyCechComplex _).d 0 (T.chartCochain h b)  := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  rw [GeneratorPresentation.ActualCechAffineLocalData.actualMismatch_eq]
  change _ + ((T.actualPresentation h).faceEmptyCechComplex _).d 0 0 = _
  rw [map_zero,add_zero]
  rfl

/-- Actual transition values are the original signed differences on every actual edge. -/
theorem chartDifferenceInput_transition (b : T.Chart → (T.actualPresentation h).PresentationGroup)
    (e : letI : TopologicalSpace T.Point := T.actualTopology h; Graph.Edge (T.actualGeometry h).graph) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    (T.actualPresentation h).faceEmptyCechCochain1Equiv _
      (T.chartDifferenceInput h b).transition ((T.actualGeometry h).graphEdgeEquiv.symm e) =
        b (Graph.right _ e) - b (Graph.left _ e)  := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  change (T.actualPresentation h).faceEmptyCechCochain1Equiv _
    (((T.actualPresentation h).faceEmptyCechComplex _).d 0 (T.chartCochain h b)) _ = _
  rw [GeneratorPresentation.faceEmptyCech_d0_normalizes,T.chartCochain_values]
  rfl

/-- The exact chart table is the integer correction of the same original witness. -/
theorem chartDifferenceInput_correction (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    ((T.actualPresentation h).faceEmptyCechComplex _).d 0 (T.chartCochain h b) =
      (T.chartDifferenceInput h b).actualMismatch := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact (T.chartDifferenceInput_mismatch h b).symm

/-- The original existing descent class of this actual correction input is zero. -/
theorem chartDifferenceInput_existing_zero (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    (T.chartDifferenceInput h b).existingDescentAdditiveClass = 0 :=
by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact (T.chartDifferenceInput h b).existingDescent_zero_iff_correction.mpr
    ⟨T.chartCochain h b,T.chartDifferenceInput_correction h b⟩

/-- Actual unique gluing of the corrected original chart sections through their original AAT inclusions. -/
def ActualCorrectedGluing (x : T.ActualLocalData h)
    (n : letI : TopologicalSpace T.Point := T.actualTopology h
      ((T.actualPresentation h).faceEmptyCechComplex
        ((T.actualGeometry h).actualCechCover (T.actualPresentation h)
          (T.actualTarget h) (T.actualTarget_nonempty h))).Cn 0) : Prop :=
  letI : TopologicalSpace T.Point := T.actualTopology h
  let P := T.actualPresentation h
  let K := T.actualGeometry h
  let C := K.actualCechCover P (T.actualTarget h) (T.actualTarget_nonempty h)
  ∃! s : (K.aatStateSheaf P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).carrier.obj
      (op C.base),
    ∀ i, (K.actualAffineAtlas P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).localTrivialization i le_rfl
      (K.aatChartStateEquiv P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition i
        ((K.aatStateSheaf P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).carrier.map
          (C.inclusion i).op s)) =
      K.actualChartCoordinates P (T.actualTarget h) (T.actualTarget_nonempty h) (x.localState-n) i

/-- The explicit p-n sections glue uniquely via the same original AAT chart inclusions and trivializations. -/
theorem chartDifferenceInput_gluing (b : T.Chart → (T.actualPresentation h).PresentationGroup) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    let P := T.actualPresentation h
    let K := T.actualGeometry h
    let C := K.actualCechCover P (T.actualTarget h) (T.actualTarget_nonempty h)
    let x := T.chartDifferenceInput h b
    ∃! s : (K.aatStateSheaf P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).carrier.obj
        (op C.base),
      ∀ i, (K.actualAffineAtlas P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).localTrivialization i le_rfl
          (K.aatChartStateEquiv P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition i
            ((K.aatStateSheaf P (T.actualTarget h) (T.actualTarget_nonempty h) x.transition).carrier.map
              (C.inclusion i).op s)) =
        K.actualChartCoordinates P (T.actualTarget h) (T.actualTarget_nonempty h)
          (x.localState - T.chartCochain h b) i :=
by
  letI : TopologicalSpace T.Point := T.actualTopology h
  exact (T.actualGeometry h).aat_corrected_gluing (T.actualPresentation h) (T.actualTarget h)
    (T.actualTarget_nonempty h) _ _ (T.chartDifferenceInput_correction h b)

/-- A verified original chart difference table gives exactly the original actual single-edge data. -/
theorem chartDifferenceInput_eq_singleEdgeData
    (b : T.Chart → (T.actualPresentation h).PresentationGroup)
    (label : LawValueLabel T.laws)
    (edge : letI : TopologicalSpace T.Point := T.actualTopology h; Graph.Edge (T.actualGeometry h).graph)
    (hb : letI : TopologicalSpace T.Point := T.actualTopology h
      ∀ e : Graph.Edge (T.actualGeometry h).graph,
        b (Graph.right _ e) - b (Graph.left _ e) =
          if e = edge then labelBasis (T.actualPresentation h) (T.actualReflectionCondition h) label else 0) :
    letI : TopologicalSpace T.Point := T.actualTopology h
    T.chartDifferenceInput h b = (T.actualGeometry h).singleEdgeData (T.actualTarget h)
      (T.actualTarget_nonempty h) (T.actualPresentation h) (T.actualReflectionCondition h) label edge := by
  letI : TopologicalSpace T.Point := T.actualTopology h
  have ht : (T.chartDifferenceInput h b).transition =
      ((T.actualGeometry h).singleEdgeData (T.actualTarget h) (T.actualTarget_nonempty h)
        (T.actualPresentation h) (T.actualReflectionCondition h) label edge).transition := by
    apply ((T.actualPresentation h).faceEmptyCechCochain1Equiv _).injective
    funext e
    have h1 := T.chartDifferenceInput_transition h b ((T.actualGeometry h).graphEdgeEquiv e)
    have h2 := (T.actualGeometry h).singleEdgeData_transition_value (T.actualTarget h)
      (T.actualTarget_nonempty h) (T.actualPresentation h) (T.actualReflectionCondition h)
      label edge ((T.actualGeometry h).graphEdgeEquiv e)
    simp only [Equiv.symm_apply_apply] at h1 h2
    exact h1.trans ((hb _).trans h2.symm)
  change GeneratorPresentation.ActualCechAffineLocalData.mk _ 0 =
    GeneratorPresentation.ActualCechAffineLocalData.mk _ 0
  exact congrArg (fun tr => GeneratorPresentation.ActualCechAffineLocalData.mk tr 0) ht

end AAT.AG.VisibleCycleReflection.FiniteInputTable
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection.FiniteInputTable
