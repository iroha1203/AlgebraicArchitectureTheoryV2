import ResearchLean.AG.RelativeRepairComposition.SubdivisionCohomologyClasses
import ResearchLean.AG.RelativeRepairComposition.SubdivisionActualDefect
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSolutionWords

/-!
# Same actual relative obstruction and old closed-word holonomy

The old fixed laws and authored three-cell laws generate the new laws. The
full actual defect is equal, and the same native H2 comparison preserves both
its class and the signed obstruction representative minus delta.

## Implementation notes

Canonical comparison and actual full-kernel defect preservation were derived
from the original path factorization, rather than supplied as assumptions.
Holonomy is the actual composite along each complete old closed word, including
its original physical arrows, evaluated on independently given new repairs.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory Limits TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (P : ClosedRegion K) (hp : chosen ∉ P.edges)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
  (K.threeLeft s) (K.threeRight s))

/-- The entire generated actual relative obstruction cocycle has precisely its original full face values. -/
theorem obstruction_cocycle_collapse :
    collapseZ2 T chosen F P hp
      (ActualRelative.obstructionCocycle (originalTower T chosen F) (oldRegion K chosen P hp)
        (fixed_face_laws T chosen F P hp hfixed) (three_laws T chosen F hsyzygy)) =
      ActualRelative.obstructionCocycle T P hfixed hsyzygy := by
  apply Subtype.ext
  apply Subtype.ext
  exact defect_substitute T chosen F

variable (candidates allowed : Set (EdgeName (K := K))) (hc : chosen ∉ candidates)

/-- The same actual native H2 comparison preserves the original relative obstruction class in every range. -/
theorem obstruction_class_collapse :
    (relativeH2Iso T chosen F P candidates allowed hp hc).hom
      (ActualRelative.obstructionClass (originalTower T chosen F) (oldRegion K chosen P hp)
        (oldEdgeSet K chosen candidates) (oldEdgeSet K chosen allowed)
        (fixed_face_laws T chosen F P hp hfixed) (three_laws T chosen F hsyzygy)) =
      ActualRelative.obstructionClass T P candidates allowed hfixed hsyzygy := by
  simp only [ActualRelative.obstructionClass_eq_mk]
  rw [relativeH2Iso_class,obstruction_cocycle_collapse]

/-- The class of the entire actual signed obstruction minus delta is preserved by precisely the same map. -/
theorem signed_obstruction_class_collapse :
    (relativeH2Iso T chosen F P candidates allowed hp hc).hom
      (QuotientAddGroup.mk (-ActualRelative.obstructionCocycle (originalTower T chosen F)
        (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed)
        (three_laws T chosen F hsyzygy))) =
      QuotientAddGroup.mk (-ActualRelative.obstructionCocycle T P hfixed hsyzygy) := by
  rw [relativeH2Iso_class]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun c : C2 T.toTower.localCoefficients => -c) (defect_substitute T chosen F)

omit hp hc P candidates allowed hfixed hsyzygy in
/-- Every old complete closed word keeps its literal actual repaired holonomy under the same collapse. -/
theorem old_closed_holonomy (R : Solution (originalTower T chosen F))
    (i : K.Vertex) (w : K.Path i i) :
    (selectedUpper (presentation K chosen) p q (originalTower T chosen F).original R.choice).pathLift
      (substitutePath K chosen w) =
    (selectedUpper K p q T.original (collapseSolution T chosen F R).choice).pathLift w :=
  solution_path_substitute T chosen F R w

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
