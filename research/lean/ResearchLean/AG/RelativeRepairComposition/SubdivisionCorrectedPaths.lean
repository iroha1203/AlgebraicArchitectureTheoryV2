import ResearchLean.AG.RelativeRepairComposition.SubdivisionCorrections

/-!
# Corrected actual arrows and every full corrected substituted word

The full cochain collapse is realized by categorical composition of the actual
two corrected factors. At retained names the arbitrary original arrow and its
original chosen lift are kept. Full-word induction preserves all occurrences.
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

/-- Each corrected new actual edge is its actual reference followed by the full target-kernel correction. -/
theorem corrected_new_edge
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    {i j : (presentation K chosen).Vertex} (e : (presentation K chosen).Edge i j) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).edgeLift e =
    (referenceLiftData chosen T F).edgeLift e ≫
      FiberAut.hom (kernelInclusion p q ((originalTower T chosen F).original.object j)
        (Additive.toMul (h ⟨i,j,e⟩))) := by
  rw [(originalTower T chosen F).correctionChoice_edge]
  change (originalTower T chosen F).toTower.upper.edgeLift e ≫ _ = _
  rw [originalTower_selected_edge]
  rfl

/-- The entire corrected substituted edge word is the original actual corrected edge with its collapsed correction. -/
theorem corrected_edge_word
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    (e : EdgeName (K := K)) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).pathLift (edgeWord K chosen e) =
    (selectedUpper K p q T.original (T.correctionChoice (collapseCorrection T chosen F h))).edgeLift e.2.2 := by
  classical
  rw [T.correctionChoice_edge]
  change _ = T.toTower.upper.edgeLift e.2.2 ≫
    FiberAut.hom (kernelInclusion p q (T.original.object e.2.1)
      (Additive.toMul (collapseCorrection T chosen F h e)))
  by_cases he : e = chosen
  · subst e
    rw [edgeWord_chosen]
    change (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).edgeLift (firstEdge K chosen) ≫
      ((selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
        ((originalTower T chosen F).correctionChoice h)).edgeLift (secondEdge K chosen) ≫ 𝟙 _) = _
    rw [Category.comp_id,corrected_new_edge,corrected_new_edge]
    simp only [referenceLiftData_edge_first,referenceLiftData_edge_second]
    rw [collapseCorrection_chosen]
    exact corrected_factor_product T chosen F
      (Additive.toMul (h (firstEdgeName K chosen)))
      (Additive.toMul (h (secondEdgeName K chosen)))
  · rw [edgeWord_old K chosen e he]
    simp only [LiftData.pathLift,Category.comp_id]
    rw [corrected_new_edge,collapseCorrection_old T chosen F h e he]
    simp only [referenceLiftData_edge_old]
    rfl

/-- Every full corrected original path equals its corrected substituted actual path after collapse. -/
theorem corrected_path_substitute
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).pathLift (substitutePath K chosen w) =
    (selectedUpper K p q T.original (T.correctionChoice (collapseCorrection T chosen F h))).pathLift w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).pathLift
        ((edgeWord K chosen ⟨_,_,e⟩).append (substitutePath K chosen w)) = _
    rw [LiftData.pathLift_append,corrected_edge_word,ih]
    rfl

/-- The same actual equations on every original named face hold precisely for the collapsed correction. -/
theorem corrected_faces_iff
    (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    (∀ f : (presentation K chosen).TwoCell,
      (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
        ((originalTower T chosen F).correctionChoice h)).pathLift ((presentation K chosen).twoLeft f) ≫
        FiberAut.hom ((originalTower T chosen F).comparator f) =
      (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
        ((originalTower T chosen F).correctionChoice h)).pathLift ((presentation K chosen).twoRight f)) ↔
    (∀ f : K.TwoCell,
      (selectedUpper K p q T.original (T.correctionChoice (collapseCorrection T chosen F h))).pathLift
        (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
      (selectedUpper K p q T.original (T.correctionChoice (collapseCorrection T chosen F h))).pathLift
        (K.twoRight f)) := by
  change (∀ f : K.TwoCell,
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).pathLift (substitutePath K chosen (K.twoLeft f)) ≫
      FiberAut.hom (T.comparator f) =
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original
      ((originalTower T chosen F).correctionChoice h)).pathLift (substitutePath K chosen (K.twoRight f))) ↔ _
  simp only [corrected_path_substitute]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
