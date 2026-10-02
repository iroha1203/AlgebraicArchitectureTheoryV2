import ResearchLean.AG.RelativeRepairComposition.SubdivisionLiftData
import ResearchLean.AG.RelativeRepairComposition.SubdivisionValues

/-!
# Original core values, their original lifts, and actual selected references

Retained original arrows keep their specified core values and lifts. Both new
factor arrows have identity core choice and identity lift. Their selected arrows
are therefore the given actual factors; retained selected arrows remain the old
selected references.

## Implementation notes

Retained edges keep the arbitrary original core and chosen lift; the two primitive factors use identity core and lift because they already are the selected actual factors. Replacing every original arrow by its reference would erase the old choices and prevent their literal reconstruction. Keeping these selections separate gives the same original input on retained edges.
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

/-- The fixed original core choice is retained at old edges and is the identity at both actual factors. -/
def coreSelection {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    FiberAut q (p.obj ((originalLiftData chosen T F).object j)) :=
  edgeValue K chosen (fun j => FiberAut q (p.obj ((originalLiftData chosen T F).object j)))
    T.core 1 1 e

/-- Original chosen upper lifts are retained and both factor choices are the identity. -/
def liftSelection {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    FiberAut (p ⋙ q) ((originalLiftData chosen T F).object j) :=
  edgeValue K chosen (fun j => FiberAut (p ⋙ q) ((originalLiftData chosen T F).object j))
    T.lift 1 1 e

/-- All chosen upper lifts project to precisely the specified full core values. -/
theorem liftSelection_core {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    fiberPushforward p q ((originalLiftData chosen T F).object j)
      (liftSelection T chosen F e) = coreSelection T chosen F e := by
  apply edge_induction chosen _ _ _ _ e
  · intro e he
    simp only [liftSelection,coreSelection,edgeValue_old]
    exact T.lift_core e.2.2
  · simp only [liftSelection,coreSelection,edgeValue_first,map_one]
  · simp only [liftSelection,coreSelection,edgeValue_second,map_one]

/-- The full selected edge family consists of old selected references and the same actual new factors. -/
theorem selected_edge {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    (selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).edgeLift e = (referenceLiftData chosen T F).edgeLift e := by
  change (originalLiftData chosen T F).edgeLift e ≫ FiberAut.hom (liftSelection T chosen F e) = _
  apply edge_induction chosen _ _ _ _ e
  · intro e he
    simp only [originalLiftData_edge_old,referenceLiftData_edge_old,
      liftSelection,edgeValue_old]
    rfl
  · simp only [originalLiftData_edge_first,referenceLiftData_edge_first,
      liftSelection,edgeValue_first]
    change F.first ≫ 𝟙 F.middle = F.first
    exact Category.comp_id _
  · simp only [originalLiftData_edge_second,referenceLiftData_edge_second,
      liftSelection,edgeValue_second]
    change F.second ≫ 𝟙 (T.original.object chosen.2.1) = F.second
    exact Category.comp_id _

/-- The complete original and reference base edge families are the same actual mapped arrows. -/
theorem reference_base {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    (referenceLiftData chosen T F).edgeBase e = (originalLiftData chosen T F).edgeBase e := by
  rw [← original_edge_base,← selected_edge T chosen F e]
  exact reselectedEdgeLift_map_eq (originalLiftData chosen T F)
    (fun _ _ e => liftSelection T chosen F e) e

/-- Every full selected new word evaluates to exactly the full reference word. -/
theorem selected_path {i j : (presentation K chosen).Vertex}
    (w : (presentation K chosen).Path i j) :
    (selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
      (liftSelection T chosen F)).pathLift w = (referenceLiftData chosen T F).pathLift w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    simp only [LiftData.pathLift,selected_edge T chosen F e,ih]

/-- Original and reference evaluation agree in the base category along every typed new word. -/
theorem reference_path_base {i j : (presentation K chosen).Vertex}
    (w : (presentation K chosen).Path i j) :
    (referenceLiftData chosen T F).pathBase w = (originalLiftData chosen T F).pathBase w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    simp only [LiftData.pathBase,reference_base T chosen F e,ih]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
