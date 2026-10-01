import ResearchLean.AG.RelativeRepairComposition.SubdivisionSolutions
import ResearchLean.AG.RelativeRepairComposition.SubdivisionIncidence

/-!
# Independent actual repairs with unchanged fixed original names

A set of fixed names excludes the selected internal always edge. Its retained
image contains exactly those same fixed actual arrows and neither factor.
Collapse and restoration use the already constructed actual solution maps.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

/-- Collapse all independent actual repairs while retaining exactly the specified original fixed arrows. -/
noncomputable def collapseSupported
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    SupportedRepair T fixed :=
  ⟨collapseSolution T chosen F R.1, by
    intro e hfixed
    have he : e ≠ chosen := fun h => hchosen (h ▸ hfixed)
    apply (solution_correction_zero_iff_edge T _ e.2.2).mp
    rw [collapseSolution_correction,collapseCorrection_old T chosen F _ e he]
    exact (solution_correction_zero_iff_edge (originalTower T chosen F) R.1
      (oldEdge K chosen e he)).mpr (R.2 (oldEdgeName K chosen e he) ⟨⟨e,he⟩,hfixed,rfl⟩)⟩

omit hchosen in
/-- Restore an independent actual repair at every fixed retained name with an arbitrary full first-factor value. -/
noncomputable def expandSupported (R : SupportedRepair T fixed)
    (r : Additive (Kernel p q F.middle)) :
    SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) :=
  ⟨expandSolution T chosen F R.1 r, by
    rintro n ⟨⟨e,he⟩,hfixed,rfl⟩
    apply (solution_correction_zero_iff_edge (originalTower T chosen F) _
      (oldEdge K chosen e he)).mp
    rw [expandSolution_correction]
    change expandCorrection T chosen F (T.solutionCorrection R.1) r (oldEdgeName K chosen e he) = 0
    rw [expandCorrection_old]
    exact (solution_correction_zero_iff_edge T R.1 e.2.2).mpr (R.2 e hfixed)⟩

/-- Collapse after arbitrary first-factor restoration recovers the actual old supported repair. -/
theorem collapse_expand_supported (R : SupportedRepair T fixed)
    (r : Additive (Kernel p q F.middle)) :
    collapseSupported T chosen F fixed hchosen (expandSupported T chosen F fixed R r) = R :=
  Subtype.ext (collapse_expand_solution T chosen F R.1 r)

/-- The actual first-factor correction restores every supported new actual repair. -/
theorem expand_collapse_supported
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    expandSupported T chosen F fixed (collapseSupported T chosen F fixed hchosen R)
      ((originalTower T chosen F).solutionCorrection R.1 (firstEdgeName K chosen)) = R :=
  Subtype.ext (expand_collapse_solution T chosen F R.1)

/-- Every new supported actual repair is an old supported actual repair paired with a full new-object kernel value. -/
noncomputable def supportedSolutionEquiv :
    SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) ≃
      SupportedRepair T fixed × Additive (Kernel p q F.middle) where
  toFun R := ⟨collapseSupported T chosen F fixed hchosen R,
    (originalTower T chosen F).solutionCorrection R.1 (firstEdgeName K chosen)⟩
  invFun R := expandSupported T chosen F fixed R.1 R.2
  left_inv := expand_collapse_supported T chosen F fixed hchosen
  right_inv R := Prod.ext (collapse_expand_supported T chosen F fixed hchosen R.1 R.2) (by
    change (originalTower T chosen F).solutionCorrection
      (expandSolution T chosen F R.1.1 R.2) (firstEdgeName K chosen) = R.2
    rw [expandSolution_correction,expandCorrection_first])

/-- Actual supported collapse has precisely the full correction collapse at every original name. -/
theorem collapseSupported_correction
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed)) :
    T.solutionCorrection (collapseSupported T chosen F fixed hchosen R).1 =
      collapseCorrection T chosen F ((originalTower T chosen F).solutionCorrection R.1) :=
  collapseSolution_correction T chosen F R.1

omit hchosen in
/-- Actual supported restoration has precisely the full restored correction at every new name. -/
theorem expandSupported_correction (R : SupportedRepair T fixed)
    (r : Additive (Kernel p q F.middle)) :
    (originalTower T chosen F).solutionCorrection (expandSupported T chosen F fixed R r).1 =
      expandCorrection T chosen F (T.solutionCorrection R.1) r :=
  expandSolution_correction T chosen F R.1 r

/-- Actual supported collapse retains precisely the full correction at each retained complete edge name. -/
theorem collapseSupported_old
    (R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    T.solutionCorrection (collapseSupported T chosen F fixed hchosen R).1 e =
      (originalTower T chosen F).solutionCorrection R.1 (oldEdgeName K chosen e he) := by
  change T.solutionCorrection (collapseSolution T chosen F R.1) e = _
  rw [collapseSolution_correction,collapseCorrection_old]

omit hchosen in
/-- Every restored supported repair retains all actual old correction values at their same complete names. -/
theorem expandSupported_old (R : SupportedRepair T fixed)
    (r : Additive (Kernel p q F.middle)) (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (originalTower T chosen F).solutionCorrection (expandSupported T chosen F fixed R r).1
      (oldEdgeName K chosen e he) = T.solutionCorrection R.1 e := by
  change (originalTower T chosen F).solutionCorrection (expandSolution T chosen F R.1 r)
    (oldEdgeName K chosen e he) = _
  rw [expandSolution_correction,expandCorrection_old]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
