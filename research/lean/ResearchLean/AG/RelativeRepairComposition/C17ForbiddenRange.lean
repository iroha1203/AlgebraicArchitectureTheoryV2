import ResearchLean.AG.RelativeRepairComposition.C17OriginalRepairs

/-! # W4's independently fixed forbidden candidate, before and after subdivision -/
namespace AAT.AG.RelativeRepairComposition.C17SubdivisionInput
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction NativeAffine

/-- The complete internal always-edge name and candidate name are distinct even though their endpoints coincide. -/
theorem chosen_ne_candidate : chosen ≠ candidate := by
  intro h
  have he := congrArg (fun e : EdgeName (K := geometry) => e.2.2) h
  exact Bool.false_ne_true he

/-- Keeping the actual candidate reference operation forbids every independent original actual repair. -/
theorem forbidden_old_no_repair : ¬ Nonempty (SupportedRepair originalTower {candidate}) := by
  rintro ⟨R⟩
  let G := NativeAffine.toRepair geometry reference reference comparison linear_faces {candidate} R
  let G0 : RealRepairs :=
    { operation := G.operation, linear := G.linear, face := G.face,
      fixed_value := by intro e he; exact he.elim }
  have hz : G0.operation (i := ()) (j := ()) true 0 = 0 := by
    have hf := G.fixed_value candidate (Set.mem_singleton candidate)
    have hv := congrArg (fun g : Op => g 0) hf
    simpa [G0,candidate,reference] using hv
  have ho := candidate_value_one G0
  exact (one_ne_zero : (1 : ZMod 3) ≠ 0) (ho.symm.trans hz)

/-- The same complete forbidden candidate has no split actual repair, by the generic actual collapse. -/
theorem forbidden_new_no_repair :
    ¬ Nonempty (SupportedRepair splitTower (Subdivision.oldEdgeSet geometry chosen {candidate})) := by
  rintro ⟨R⟩
  apply forbidden_old_no_repair
  exact ⟨Subdivision.collapseSupported originalTower chosen factors {candidate}
    (fun h => chosen_ne_candidate h) R⟩

end AAT.AG.RelativeRepairComposition.C17SubdivisionInput
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C17SubdivisionInput
