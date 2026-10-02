import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedSolutions

/-!
# Same original choices and actual arrows at every retained complete name

The old original arrow and its old chosen core lift remain explicit. Collapse
and arbitrary first-factor restoration preserve the entire actual choice at
every retained name, and hence its same actual reselected categorical arrow.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- Collapse keeps the same full original core-lift choice at each retained complete name. -/
theorem collapseSolution_choice_old (R : Solution (originalTower T chosen F))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (collapseSolution T chosen F R).choice e.2.2 = R.choice (oldEdge K chosen e he) := by
  rw [← T.correctionChoice_solutionCorrection (collapseSolution T chosen F R) e.2.2,
    collapseSolution_correction,
    ← (originalTower T chosen F).correctionChoice_solutionCorrection R (oldEdge K chosen e he)]
  change kernelInclusion p q (T.original.object e.2.1)
      (Additive.toMul (collapseCorrection T chosen F ((originalTower T chosen F).solutionCorrection R) e)) *
      T.lift e.2.2 =
    kernelInclusion p q ((originalTower T chosen F).original.object (.inl e.2.1))
      (Additive.toMul ((originalTower T chosen F).solutionCorrection R (oldEdgeName K chosen e he))) *
      (originalTower T chosen F).lift (oldEdge K chosen e he)
  rw [collapseCorrection_old T chosen F _ e he,originalTower_lift_old]
  rfl

/-- Collapse keeps the same actual original reselected categorical arrow at every retained indexed edge. -/
theorem collapseSolution_arrow_old (R : Solution (originalTower T chosen F))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (selectedUpper K p q T.original (collapseSolution T chosen F R).choice).edgeLift e.2.2 =
      (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original R.choice).edgeLift
        (oldEdge K chosen e he) := by
  change T.original.edgeLift e.2.2 ≫ FiberAut.hom ((collapseSolution T chosen F R).choice e.2.2) =
    (originalTower T chosen F).original.edgeLift (oldEdge K chosen e he) ≫
      FiberAut.hom (R.choice (oldEdge K chosen e he))
  rw [collapseSolution_choice_old,originalTower_original_edge_old]

/-- Any full first-factor restoration keeps every arbitrary original actual core-lift choice at every retained name. -/
theorem expandSolution_choice_old (R : Solution T) (r : Additive (Kernel p q F.middle))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (expandSolution T chosen F R r).choice (oldEdge K chosen e he) = R.choice e.2.2 := by
  have h := collapseSolution_choice_old T chosen F (expandSolution T chosen F R r) e he
  rw [collapse_expand_solution] at h
  exact h.symm

/-- Any full first-factor restoration retains the same actual original reselected categorical arrow at every retained indexed edge. -/
theorem expandSolution_arrow_old (R : Solution T) (r : Additive (Kernel p q F.middle))
    (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      (expandSolution T chosen F R r).choice).edgeLift (oldEdge K chosen e he) =
      (selectedUpper K p q T.original R.choice).edgeLift e.2.2 := by
  change (originalTower T chosen F).original.edgeLift (oldEdge K chosen e he) ≫
      FiberAut.hom ((expandSolution T chosen F R r).choice (oldEdge K chosen e he)) =
    T.original.edgeLift e.2.2 ≫ FiberAut.hom (R.choice e.2.2)
  rw [expandSolution_choice_old,originalTower_original_edge_old]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
