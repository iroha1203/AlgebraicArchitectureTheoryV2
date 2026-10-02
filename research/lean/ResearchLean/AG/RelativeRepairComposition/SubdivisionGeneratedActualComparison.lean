import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedCoverRestoration
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedSolutions

/-!
# Independent generated local comparison commutes with full actual subdivision

## Implementation notes

New and old repairs are the original independently defined actual morphisms.
Their independent generator restorations read all actual corrections. The
local two-factor comparison is proved to agree with actual global collapse at
every original edge, before any support, orbit or external relation is read.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))


omit [Fintype I] [DecidableEq I] [∀ j, DecidablePred (· ∈ (U j).vertices)]
  [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
include hi in
/-- The internal chosen edge is absent from every full fixed permission set. -/
theorem chosen_not_fixed : chosen ∉ fixed := by
  intro h
  rcases h with hp | hc
  · exact hi.2.1 hp
  · exact hi.2.2.1 hc.1

/-- Restore the entire actual new correction in each independently generated local component. -/
noncomputable def restoredLocal
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I) :
    RelativeCover.C1 Mn (Un j) Pn :=
  ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
    (value := values j)).symm
    ((GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed R).1 j)).1

omit [Fintype (EdgeName (K := K))] in
/-- Each full restored new edge value is exactly the original actual correction. -/
theorem restoredLocal_value
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I) (e : (Un j).edges) :
    (restoredLocal T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R j).1 e =
      (originalTower T chosen factor).solutionCorrection R.1 e.1 :=
  GeneratedCoverRestoration.new_forward_edge_value T chosen factor bases U P candidates owner hi hlinear ek ee ef
    hfixed ei hc allowed R j e

omit [Fintype (EdgeName (K := K))] in
/-- All restored local old corrections are the same full actual globally collapsed correction. -/
theorem collapsed_local_value
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I) (e : (U j).edges) :
    (local1Equiv T chosen factor (U j) P hi.2.1
      (restoredLocal T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R j)).1.1 e =
    T.solutionCorrection
      (collapseSupported T chosen factor fixed
        (chosen_not_fixed chosen U P candidates owner hi allowed) R).1 e.1 := by
  by_cases hn : e.1 = chosen
  · rcases e with ⟨e,hu⟩
    change e = chosen at hn
    subst e
    rw [local1Equiv_chosen T chosen factor (U j) P hi.2.1 _ hu]
    rw [restoredLocal_value,restoredLocal_value]
    rw [collapseSupported_correction,collapseCorrection_chosen]
  · rw [local1Equiv_retained T chosen factor (U j) P hi.2.1 _ e hn]
    rw [restoredLocal_value]
    exact (collapseSupported_old T chosen factor fixed
      (chosen_not_fixed chosen U P candidates owner hi allowed) R e.1 hn).symm

/-- Every independently compared old generated component restores the same actual collapsed correction. -/
theorem compared_old_value
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I) (e : (U j).edges) :
    ((FiniteNative.generatedRelativeEquiv Mo bases (U j) P
      (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j) ek ee ef).symm
      ((GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
        (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
          hfixed ei hc allowed R)).1.1 j)).1.1 e =
    T.solutionCorrection
      (collapseSupported T chosen factor fixed
        (chosen_not_fixed chosen U P candidates owner hi allowed) R).1 e.1 := by
  have hcoord := GeneratedInterfaces.objectsEquiv_coordinates T chosen factor bases U P candidates owner hi j hlinear ek ee ef
    (value := values j)
    ((GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed R).1 j)
  have hcomp := GeneratedStrictObjects.objectsEquiv_component T chosen factor bases U P candidates owner hi hlinear ek ee ef
    (candidates \ allowed) Set.diff_subset values
    (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed R) j
  rw [← hcomp] at hcoord
  exact (congrArg (fun z => z.1.1 e) hcoord).trans
    (collapsed_local_value T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R j e)

/-- The full compared old strict generated object is the independent extraction of the actual collapsed repair. -/
theorem comparison_old_actual
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) :
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
      (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
        hfixed ei hc allowed R)).1 =
      GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed
        (collapseSupported T chosen factor fixed
          (chosen_not_fixed chosen U P candidates owner hi allowed) R) := by
  apply Subtype.ext
  funext j
  apply (FiniteNative.generatedRelativeEquiv Mo bases (U j) P
    (ClosedRegion.privateAlwaysEdges U P candidates j) hlinear (values j) ek ee ef).symm.injective
  apply Subtype.ext
  apply Subtype.ext
  funext e
  exact (compared_old_value T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R j e).trans
    (RelativeActualGeneratedCover.forward_edge_value T bases P U candidates hlinear hfixed ek ee ef ei hc allowed
      (collapseSupported T chosen factor fixed
        (chosen_not_fixed chosen U P candidates owner hi allowed) R) j e).symm

/-- The compared fresh coordinate is the full actual first-factor correction. -/
theorem comparison_fresh_actual
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) :
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
      (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
        hfixed ei hc allowed R)).2 =
      (originalTower T chosen factor).solutionCorrection R.1 (firstEdgeName K chosen) := by
  have hcoord := GeneratedInterfaces.objectsEquiv_coordinates T chosen factor bases U P candidates owner hi owner hlinear ek ee ef
    (value := values owner)
    ((GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed R).1 owner)
  have hcomp := GeneratedStrictObjects.objectsEquiv_component T chosen factor bases U P candidates owner hi hlinear ek ee ef
    (candidates \ allowed) Set.diff_subset values
    (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed R) owner
  rw [← hcomp] at hcoord
  have h := congrArg (fun z => z.2.1) hcoord
  change (SupplementFamilies.restore T chosen factor U P candidates owner hi
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
      (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
        hfixed ei hc allowed R)).2 owner).1 = (local1Equiv T chosen factor (U owner) P hi.2.1
    (restoredLocal T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R owner)).2.1 at h
  rw [SupplementFamilies.restore_owner] at h
  rw [local1Equiv_first,Family.extend_on
    (fun e : EdgeName (K := presentation K chosen) => (Mn).A e.2.1)
    (Un owner).edges _ (firstEdgeName K chosen) hi.1] at h
  exact h.trans (restoredLocal_value T chosen factor bases U P candidates owner hi hlinear ek ee ef
    hfixed ei hc allowed R owner ⟨firstEdgeName K chosen,hi.1⟩)

/-- Independent strict generation comparison is exactly full actual collapse and fresh-value extraction. -/
theorem comparison_actual
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) :
    GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
      (GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
        hfixed ei hc allowed R) =
    (GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed
      (collapseSupported T chosen factor fixed
        (chosen_not_fixed chosen U P candidates owner hi allowed) R),
      (originalTower T chosen factor).solutionCorrection R.1 (firstEdgeName K chosen)) :=
  Prod.ext
    (comparison_old_actual T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R)
    (comparison_fresh_actual T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R)

/-- Every old actual repair and every full fresh value restore the same independent new generated object. -/
theorem comparison_actual_restore
    (R : SupportedRepair T fixed) (r : Aw) :
    (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).symm
      (GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed R,r) =
    GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef
      hfixed ei hc allowed (expandSupported T chosen factor fixed R r) := by
  apply (GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).injective
  rw [Equiv.apply_symm_apply,comparison_actual,collapse_expand_supported]
  apply Prod.ext
  · rfl
  · symm
    rw [expandSupported_correction,expandCorrection_first]

/-- Full actual inverse restoration agrees at every original new edge with the explicit two-factor restoration. -/
theorem comparison_restore_edge_value
    (R : SupportedRepair T fixed) (r : Aw) (e : EdgeName (K := presentation K chosen)) :
    (originalTower T chosen factor).solutionCorrection
      ((GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed).symm
        ((GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values).symm
          (GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed R,r))).1 e =
    expandCorrection T chosen factor (T.solutionCorrection R.1) r e := by
  rw [comparison_actual_restore,Equiv.symm_apply_apply,expandSupported_correction]

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualComparison
