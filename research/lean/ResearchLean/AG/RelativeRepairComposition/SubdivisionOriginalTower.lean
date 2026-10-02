import ResearchLean.AG.RelativeRepairComposition.SubdivisionPathValues

/-!
# The actual original tower after internal-edge subdivision

The input is the same original tower and its primitive two-factor data. Core
alignment follows from full-word substitution, and commutativity at the fresh
object follows from its actual surjective kernel transport. The construction
adds no equivalence or coherence assumption.

## Implementation notes

Every tower field is generated from the original tower and primitive factors. Neither a new lawful tower nor a repair equivalence is supplied. Derived commutativity at the intermediate object avoids strengthening the fixed input hypotheses.
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

/-- The original lower strong arrows and both actual factors give all new original lower strong arrows. -/
theorem original_lower_strong {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    q.IsStronglyCocartesian ((originalLiftData chosen T F).edgeBase e)
      (p.map ((originalLiftData chosen T F).edgeLift e)) :=
  liftData_lowerStrong chosen T.original F.middle F.first F.second
    F.firstStrong F.secondStrong T.originalLowerStrong F.firstLowerStrong F.secondLowerStrong e

/-- The reference lower strong family is derived from the same two actual factors and old selected references. -/
theorem reference_lower_strong {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    q.IsStronglyCocartesian ((referenceLiftData chosen T F).edgeBase e)
      (p.map ((referenceLiftData chosen T F).edgeLift e)) :=
  liftData_lowerStrong chosen T.toTower.upper F.middle F.first F.second
    F.firstStrong F.secondStrong T.toTower.lowerStrong F.firstLowerStrong F.secondLowerStrong e

/-- Full actual kernel transport is bijective at every reference edge, including both factors. -/
theorem reference_edge_bijective {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    Function.Bijective (kernelTransportHom p q ((referenceLiftData chosen T F).edgeLift e)
      ((referenceLiftData chosen T F).edgeStrong e) (reference_lower_strong T chosen F e)) := by
  apply edge_induction chosen _ _ _ _ e
  · intro e he
    simpa only [referenceLiftData_edge_old] using T.edgeBijective e.2.2
  · simpa only [referenceLiftData_edge_first] using F.firstBijective
  · simpa only [referenceLiftData_edge_second] using F.secondBijective

/-- The selected new edge transport is exactly the transport of the corresponding actual reference. -/
theorem selected_edge_transport {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    kernelTransportHom p q
      ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
        (liftSelection T chosen F)).edgeLift e)
      ((selectedUpper (presentation K chosen) p q (originalLiftData chosen T F)
        (liftSelection T chosen F)).edgeStrong e)
      (selectedLowerStrong (presentation K chosen) p q (originalLiftData chosen T F)
        (original_lower_strong T chosen F) (liftSelection T chosen F) e) =
    kernelTransportHom p q ((referenceLiftData chosen T F).edgeLift e)
      ((referenceLiftData chosen T F).edgeStrong e) (reference_lower_strong T chosen F e) := by
  congr 1
  · exact (reference_base T chosen F e).symm
  · exact selected_edge T chosen F e

/-- The actual full kernel is commutative at every retained object and at the new intermediate object. -/
theorem original_kernel_comm (v : (presentation K chosen).Vertex)
    (a b : Kernel p q ((originalLiftData chosen T F).object v)) : a * b = b * a := by
  cases v with
  | inl v => exact T.kernelComm v a b
  | inr u => cases u; exact middle_kernel_comm T chosen F a b

/-- The complete new original tower, derived from original arrows, original core choices, and actual two-factor data. -/
def originalTower : OriginalTowerPresentation (presentation K chosen) p q where
  original := originalLiftData chosen T F
  originalLowerStrong := original_lower_strong T chosen F
  core := coreSelection T chosen F
  lift := liftSelection T chosen F
  lift_core := liftSelection_core T chosen F
  faceBase := original_face_base T chosen F
  comparator := T.comparator
  coreAlignment := selected_core_alignment T chosen F
  kernelComm := original_kernel_comm T chosen F
  edgeBijective e := by
    rw [selected_edge_transport]
    exact reference_edge_bijective T chosen F e
  comparatorCentralizes := T.comparatorCentralizes

/-- Every retained original input arrow is the same arbitrary original arrow, before its lift is selected. -/
theorem originalTower_original_edge_old (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (originalTower T chosen F).original.edgeLift (oldEdge K chosen e he) = T.original.edgeLift e.2.2 :=
  edgeAssignment_old K chosen T.original.object F.middle T.original.edgeLift F.first F.second e he

/-- Every retained original chosen lift is exactly its old lift of the same original core value. -/
theorem originalTower_lift_old (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (originalTower T chosen F).lift (oldEdge K chosen e he) = T.lift e.2.2 :=
  edgeValue_old K chosen (fun v => FiberAut (p ⋙ q) ((originalLiftData chosen T F).object v))
    T.lift 1 1 e he

/-- Every retained original core choice is exactly its old full core choice. -/
theorem originalTower_core_old (e : EdgeName (K := K)) (he : e ≠ chosen) :
    (originalTower T chosen F).core (oldEdge K chosen e he) = T.core e.2.2 :=
  edgeValue_old K chosen (fun v => FiberAut q (p.obj ((originalLiftData chosen T F).object v)))
    T.core 1 1 e he

/-- Each actual old object is retained identically in the full original tower input. -/
theorem originalTower_object_old (v : K.Vertex) :
    (originalTower T chosen F).original.object (.inl v) = T.original.object v := rfl

/-- The actual original input object at the fresh vertex is exactly the supplied actual intermediate object. -/
theorem originalTower_object_fresh :
    (originalTower T chosen F).original.object (.inr ()) = F.middle := rfl

/-- The selected full edge of the constructed original tower is the actual reference assigned to that name. -/
theorem originalTower_selected_edge {i j : (presentation K chosen).Vertex}
    (e : (presentation K chosen).Edge i j) :
    (originalTower T chosen F).toTower.upper.edgeLift e = (referenceLiftData chosen T F).edgeLift e :=
  selected_edge T chosen F e

/-- Every complete substituted original word has the same actual selected value in the constructed original tower. -/
theorem originalTower_selected_path {i j : K.Vertex} (w : K.Path i j) :
    (originalTower T chosen F).toTower.upper.pathLift (substitutePath K chosen w) =
      T.toTower.upper.pathLift w := selected_path_substitute T chosen F w

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
