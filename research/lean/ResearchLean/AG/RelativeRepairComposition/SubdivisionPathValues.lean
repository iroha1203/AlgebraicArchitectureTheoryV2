import ResearchLean.AG.RelativeRepairComposition.SubdivisionSelection

/-!
# Actual full-word evaluation through the original two factors

The product of the given factors proves the selected edge-word equation.
Induction then substitutes every occurrence in every original word, including
all face words and all incoming and outgoing words of copied three-cell routes.
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

/-- Each substituted full edge word has exactly the old actual selected edge value. -/
theorem reference_edge_word (e : EdgeName (K := K)) :
    (referenceLiftData chosen T F).pathLift (edgeWord K chosen e) =
      T.toTower.upper.edgeLift e.2.2 := by
  classical
  by_cases he : e = chosen
  · subst e
    rw [edgeWord_chosen]
    change (referenceLiftData chosen T F).edgeLift (firstEdge K chosen) ≫
      ((referenceLiftData chosen T F).edgeLift (secondEdge K chosen) ≫ 𝟙 _) = _
    simp only [referenceLiftData,liftData,edgeAssignment_first,edgeAssignment_second,Category.comp_id]
    exact F.composite
  · rw [edgeWord_old K chosen e he]
    simp only [LiftData.pathLift,Category.comp_id,referenceLiftData,liftData,edgeAssignment_old]

/-- The substituted full reference word is the original full selected word for every typed path. -/
theorem reference_path_substitute {i j : K.Vertex} (w : K.Path i j) :
    (referenceLiftData chosen T F).pathLift (substitutePath K chosen w) =
      T.toTower.upper.pathLift w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change (referenceLiftData chosen T F).pathLift
      ((edgeWord K chosen ⟨_,_,e⟩).append (substitutePath K chosen w)) = _
    rw [LiftData.pathLift_append,reference_edge_word,ih]
    rfl

/-- Every selected original face word and route word keeps its complete actual total value. -/
theorem selected_path_substitute {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).pathLift (substitutePath K chosen w) =
      T.toTower.upper.pathLift w := by
  rw [selected_path,reference_path_substitute]

/-- The new original input has exactly the old original base value on each substituted full word. -/
theorem original_path_base_substitute {i j : K.Vertex} (w : K.Path i j) :
    (originalLiftData chosen T F).pathBase (substitutePath K chosen w) =
      T.original.pathBase w := by
  rw [← reference_path_base,← LiftData.map_pathLift,reference_path_substitute,LiftData.map_pathLift]
  exact selectedUpper_pathBase K p q T.original T.lift w

/-- Both full base words of every original named face remain equal after subdivision. -/
theorem original_face_base (f : (presentation K chosen).TwoCell) :
    (originalLiftData chosen T F).pathBase ((presentation K chosen).twoLeft f) =
      (originalLiftData chosen T F).pathBase ((presentation K chosen).twoRight f) := by
  change (originalLiftData chosen T F).pathBase (substitutePath K chosen (K.twoLeft f)) =
    (originalLiftData chosen T F).pathBase (substitutePath K chosen (K.twoRight f))
  rw [original_path_base_substitute,original_path_base_substitute]
  exact T.faceBase f

/-- The same actual comparator gives the core alignment of both full substituted face words. -/
theorem selected_core_alignment (f : (presentation K chosen).TwoCell) :
    p.map ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).pathLift ((presentation K chosen).twoLeft f)) ≫
      p.map (FiberAut.hom (T.comparator f)) =
    p.map ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).pathLift ((presentation K chosen).twoRight f)) := by
  change p.map ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
    (liftSelection T chosen F)).pathLift (substitutePath K chosen (K.twoLeft f))) ≫
      p.map (FiberAut.hom (T.comparator f)) =
    p.map ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).pathLift (substitutePath K chosen (K.twoRight f)))
  rw [selected_path_substitute,selected_path_substitute]
  exact T.coreAlignment f

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
