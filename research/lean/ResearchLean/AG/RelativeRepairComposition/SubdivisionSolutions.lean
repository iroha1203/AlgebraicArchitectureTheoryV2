import ResearchLean.AG.RelativeRepairComposition.SubdivisionCorrectedPaths

/-!
# Collapse and restoration of independent actual coherent solutions

The actual face equations are transported first. The correction equation then
follows from the accepted original-tower coherence API. Thus every old actual
solution and every full first-factor kernel value restores a new actual
solution, with both original choice fields recovered by the inverse laws.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The actual face equations for a correction choice are exactly its original correction equation. -/
theorem correction_faces_iff_equation (h : C1 T.toTower.localCoefficients) :
    (∀ f : K.TwoCell,
      (selectedUpper K p q T.original (T.correctionChoice h)).pathLift (K.twoLeft f) ≫
        FiberAut.hom (T.comparator f) =
      (selectedUpper K p q T.original (T.correctionChoice h)).pathLift (K.twoRight f)) ↔
    d1 T.toTower.localCoefficients h = -T.toTower.defect := by
  rw [← T.toTower.correctedDefect_eq_zero_iff_d1,T.toTower.correctedDefect_eq_zero_iff_coherent]
  change (∀ f : K.TwoCell,
    (selectedUpper K p q T.original (T.correctionChoice h)).pathLift (K.twoLeft f) ≫
      FiberAut.hom (T.comparator f) =
    (selectedUpper K p q T.original (T.correctionChoice h)).pathLift (K.twoRight f)) ↔
    (∀ f : K.TwoCell,
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) (K.twoLeft f) ≫
        FiberAut.hom (T.comparator f) =
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) (K.twoRight f))
  simp only [T.correctionChoice_path]

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)

/-- The full new correction equation holds exactly when the old equation holds at the collapsed full correction. -/
theorem correction_equation_iff
    (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    d1 (originalTower T chosen F).toTower.localCoefficients h =
        -(originalTower T chosen F).toTower.defect ↔
      d1 T.toTower.localCoefficients (collapseCorrection T chosen F h) = -T.toTower.defect := by
  rw [← correction_faces_iff_equation,corrected_faces_iff,correction_faces_iff_equation]

/-- Collapse an independent actual new solution, preserving the old original input and old core choices. -/
noncomputable def collapseSolution (R : Solution (originalTower T chosen F)) : Solution T :=
  T.solutionOfCorrection
    (collapseCorrection T chosen F ((originalTower T chosen F).solutionCorrection R))
    ((correction_equation_iff T chosen F _).mp
      ((originalTower T chosen F).solutionCorrection_d1 R))

/-- Restore the actual original new-factor choices from an actual old solution and any full first-factor correction. -/
noncomputable def expandSolution (R : Solution T) (r : Additive (Kernel p q F.middle)) :
    Solution (originalTower T chosen F) :=
  (originalTower T chosen F).solutionOfCorrection
    (expandCorrection T chosen F (T.solutionCorrection R) r)
    ((correction_equation_iff T chosen F _).mpr (by
      rw [collapse_expand]
      exact T.solutionCorrection_d1 R))

/-- The correction of actual solution collapse is precisely the full correction collapse. -/
theorem collapseSolution_correction (R : Solution (originalTower T chosen F)) :
    T.solutionCorrection (collapseSolution T chosen F R) =
      collapseCorrection T chosen F ((originalTower T chosen F).solutionCorrection R) :=
  T.solutionCorrection_solutionOfCorrection _ _

/-- The correction of actual solution restoration is precisely the restored full correction. -/
theorem expandSolution_correction (R : Solution T) (r : Additive (Kernel p q F.middle)) :
    (originalTower T chosen F).solutionCorrection (expandSolution T chosen F R r) =
      expandCorrection T chosen F (T.solutionCorrection R) r :=
  (originalTower T chosen F).solutionCorrection_solutionOfCorrection _ _

/-- Collapse after restoration recovers each original actual choice at every original indexed edge. -/
theorem collapse_expand_solution (R : Solution T) (r : Additive (Kernel p q F.middle)) :
    collapseSolution T chosen F (expandSolution T chosen F R r) = R := by
  apply Solution.ext
  intro i j e
  change T.correctionChoice (collapseCorrection T chosen F
    ((originalTower T chosen F).solutionCorrection (expandSolution T chosen F R r))) e = R.choice e
  rw [expandSolution_correction,collapse_expand,T.correctionChoice_solutionCorrection]

/-- Restoration from the actual first-factor correction recovers every new original actual edge choice. -/
theorem expand_collapse_solution (R : Solution (originalTower T chosen F)) :
    expandSolution T chosen F (collapseSolution T chosen F R)
      ((originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen)) = R := by
  apply Solution.ext
  intro i j e
  change (originalTower T chosen F).correctionChoice
    (expandCorrection T chosen F (T.solutionCorrection (collapseSolution T chosen F R))
      ((originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen))) e = R.choice e
  rw [collapseSolution_correction,expand_collapse,
    (originalTower T chosen F).correctionChoice_solutionCorrection]

/-- The full new actual solution set is exactly old actual solutions paired with the full new-object kernel. -/
noncomputable def solutionEquiv : Solution (originalTower T chosen F) ≃
    Solution T × Additive (Kernel p q F.middle) where
  toFun R := ⟨collapseSolution T chosen F R,
    (originalTower T chosen F).solutionCorrection R (firstEdgeName K chosen)⟩
  invFun R := expandSolution T chosen F R.1 R.2
  left_inv := expand_collapse_solution T chosen F
  right_inv R := Prod.ext (collapse_expand_solution T chosen F R.1 R.2) (by
    change (originalTower T chosen F).solutionCorrection (expandSolution T chosen F R.1 R.2)
      (firstEdgeName K chosen) = R.2
    rw [expandSolution_correction,expandCorrection_first])

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
