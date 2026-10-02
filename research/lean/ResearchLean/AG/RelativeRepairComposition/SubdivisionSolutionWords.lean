import ResearchLean.AG.RelativeRepairComposition.SubdivisionRetainedChoices

/-! # Whole actual repaired word comparison for independently given repairs -/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- Every independent actual repair evaluates each complete substituted word to the same original actual repaired word. -/
theorem solution_path_substitute (R : Solution (originalTower T chosen F))
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original R.choice).pathLift
      (substitutePath K chosen w) =
    (selectedUpper K p q T.original (collapseSolution T chosen F R).choice).pathLift w := by
  have hn : @R.choice = (fun i j e => (originalTower T chosen F).correctionChoice
      ((originalTower T chosen F).solutionCorrection R) (i := i) (j := j) e) := by
    funext i j e
    exact ((originalTower T chosen F).correctionChoice_solutionCorrection R e).symm
  have ho : @(collapseSolution T chosen F R).choice =
      (fun i j e => T.correctionChoice (collapseCorrection T chosen F
        ((originalTower T chosen F).solutionCorrection R)) (i := i) (j := j) e) := by
    funext i j e
    rw [← T.correctionChoice_solutionCorrection (collapseSolution T chosen F R) e,
      collapseSolution_correction]
  rw [hn,ho]
  exact corrected_path_substitute T chosen F _ w

/-- The entire actual new repaired factor word equals the actual collapsed original edge, including the original nonidentity L. -/
theorem solution_factor_word (R : Solution (originalTower T chosen F)) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original R.choice).pathLift
      (factorPath K chosen) =
    (selectedUpper K p q T.original (collapseSolution T chosen F R).choice).edgeLift chosen.2.2 := by
  have h := solution_path_substitute T chosen F R
    (.cons chosen.2.2 (.nil chosen.2.1))
  rw [substitutePath,edgeWord_chosen] at h
  simpa only [substitutePath,PresentedPath.append_nil,LiftData.pathLift,Category.comp_id] using h

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
