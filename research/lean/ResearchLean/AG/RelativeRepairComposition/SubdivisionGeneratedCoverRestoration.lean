import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedStrictObjects
import ResearchLean.AG.RelativeRepairComposition.RelativeActualGeneratedCover
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions

/-!
# Full actual subdivision repairs and independent strict generation

## Implementation notes

Both actual signed defects come from the original reference paths and authored
comparisons. Their equality is derived from actual subdivision. Both actual
repair spaces then have full inverse extraction to their own independent local
generators, with unchanged named candidate permissions.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration
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
include hi hfixed in
/-- Every original fixed face law holds on the same full substituted actual paths. -/
theorem new_fixed_laws : ∀ f ∈ (Pn).faces,
    (originalTower T chosen factor).toTower.upper.pathLift ((presentation K chosen).twoLeft f) ≫
      FiberAut.hom ((originalTower T chosen factor).comparator f) =
    (originalTower T chosen factor).toTower.upper.pathLift ((presentation K chosen).twoRight f) :=
  fixed_face_laws T chosen factor P hi.2.1 hfixed

omit [Fintype I] [DecidableEq I] [∀ j, DecidablePred (· ∈ (U j).vertices)]
  [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every independent new actual local signed defect is the transported original signed defect. -/
theorem actual_rhs (j : I) :
    -CoverEquation.defect Mn Pn
      (ActualEquation.defectFamily (originalTower T chosen factor) Pn
        (new_fixed_laws T chosen factor U P candidates owner hi hfixed)) (Un j) =
      (local2Equiv T chosen factor (U j) P).symm (values j) := by
  apply Subtype.ext
  funext f
  change -(originalTower T chosen factor).toTower.defect f.1 = -T.toTower.defect f.1
  rw [defect_substitute]

/-- Old actual full repairs and independently generated old strict objects are mutually inverse. -/
noncomputable def oldObjectEquiv : SupportedRepair T fixed ≃
    GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed) :=
  RelativeActualGeneratedCover.objectEquiv T bases P U candidates hlinear hfixed ek ee ef ei hc allowed

/-- New actual repairs and full strict actual local equations have inverse maps before generation. -/
noncomputable def newActualEquations :
    SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed) ≃
      StrictEquationObjects.NewObjects T chosen factor U P values (candidates \ allowed) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates owner hi
  letI : ∀ j, DecidablePred (· ∈ (Un j).vertices) := fun j => FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).edges) := fun j => FiniteIncidence.expandedEdgesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).faces) := fun j => FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Pn).faces) := FiniteIncidence.expandedFacesDecidable K chosen P
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen ee
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  let newFixed := new_fixed_laws T chosen factor U P candidates owner hi hfixed
  let dn := ActualEquation.defectFamily (originalTower T chosen factor) Pn newFixed
  have hpEdges : (Pn).edges = oldEdgeSet K chosen P.edges :=
    expanded_set_avoiding K chosen P.edges hi.2.1
  have hfEdges : fixedEdgesForRange (Pn).edges Cn (oldEdgeSet K chosen allowed) = oldEdgeSet K chosen fixed := by
    rw [hpEdges,← fixed_range_retained]
  let sourceEquiv : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed) ≃
      SupportedRepair (originalTower T chosen factor) (fixedEdgesForRange (Pn).edges Cn (oldEdgeSet K chosen allowed)) :=
    { toFun R := ⟨R.1,by rw [hfEdges]; exact R.2⟩
      invFun R := ⟨R.1,by rw [← hfEdges]; exact R.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  let actualEquiv := (SupportedNativeEquation.repairEquiv (originalTower T chosen factor) Pn Cn
    (oldEdgeSet K chosen allowed) newFixed).trans
    (StrictCoverRestoration.objectEquiv Mn Pn Un Cn (oldEdgeSet K chosen allowed) dn ei
      (expanded_indexed_cover K chosen U hc))
  let localEquiv : StrictSupportedCover.Objects Mn Pn Un Cn (oldEdgeSet K chosen allowed) dn ≃
      StrictEquationObjects.NewObjects T chosen factor U P values (candidates \ allowed) :=
    { toFun h := ⟨fun j => ⟨(h.1 j).1.1,by
        rw [← actual_rhs T chosen factor U P candidates owner hi hfixed j]
        exact (h.1 j).1.2⟩,by
        constructor
        · intro j e he
          have hm : e.1 ∈ Cn \ oldEdgeSet K chosen allowed := by rw [← old_set_diff]; exact he
          exact (h.1 j).2 e hm
        · intro j l e hj hl _
          exact h.2 j l e hj hl⟩
      invFun h := ⟨fun j => ⟨⟨(h.1 j).1,by
          rw [actual_rhs T chosen factor U P candidates owner hi hfixed j]
          exact (h.1 j).2⟩,by
          intro e he
          rw [← old_set_diff] at he
          exact h.2.1 j e he⟩,by
        intro j l e hj hl
        by_cases hn : l = j
        · subst l
          rfl
        · exact h.2.2 j l e hj hl hn⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  exact sourceEquiv.trans (actualEquiv.trans localEquiv)

/-- New actual full repairs and independently generated new strict objects are mutually inverse. -/
noncomputable def newObjectEquiv :
    SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed) ≃
      GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi
        hlinear ek ee ef values (candidates \ allowed) :=
  (newActualEquations T chosen factor U P candidates owner hi hfixed ei hc allowed).trans
    (GeneratedStrictObjects.newExtraction T chosen factor bases U P candidates owner hi hlinear ek ee ef
      (candidates \ allowed) Set.diff_subset values)

omit [Fintype (EdgeName (K := K))] in
/-- New extraction followed by full local generation restoration keeps each actual local equation. -/
theorem new_equation_component
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed)) (j : I) :
    (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
      (value := values j)).symm
      ((newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R).1 j) =
        ((newActualEquations T chosen factor U P candidates owner hi hfixed ei hc allowed R).1 j) :=
  (GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
    (value := values j)).symm_apply_apply _

omit [Fintype (EdgeName (K := K))] in
/-- Full new actual extraction and generation preserve the correction on every original new edge in every member. -/
theorem new_forward_edge_value
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen fixed))
    (j : I) (e : (Un j).edges) :
    ((GeneratedRelations.newGeneratedEquiv T chosen factor bases U P candidates owner hi j hlinear ek ee ef
      (value := values j)).symm
      ((newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed R).1 j)).1.1 e =
        (originalTower T chosen factor).solutionCorrection R.1 e.1 := by
  rw [new_equation_component]
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates owner hi
  letI : ∀ j, DecidablePred (· ∈ (Un j).vertices) := fun j => FiniteIncidence.expandedVerticesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).edges) := fun j => FiniteIncidence.expandedEdgesDecidable K chosen (U j)
  letI : ∀ j, DecidablePred (· ∈ (Un j).faces) := fun j => FiniteIncidence.expandedFacesDecidable K chosen (U j)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  letI : DecidablePred (· ∈ (Pn).faces) := FiniteIncidence.expandedFacesDecidable K chosen P
  letI : Fintype (EdgeName (K := presentation K chosen)) := FiniteEnumerations.edgeFintype K chosen ee
  letI : Fintype (presentation K chosen).TwoCell := inferInstanceAs (Fintype K.TwoCell)
  letI : DecidableEq (presentation K chosen).TwoCell := inferInstanceAs (DecidableEq K.TwoCell)
  let newFixed := new_fixed_laws T chosen factor U P candidates owner hi hfixed
  let dn := ActualEquation.defectFamily (originalTower T chosen factor) Pn newFixed
  have hpEdges : (Pn).edges = oldEdgeSet K chosen P.edges :=
    expanded_set_avoiding K chosen P.edges hi.2.1
  have hfEdges : fixedEdgesForRange (Pn).edges Cn (oldEdgeSet K chosen allowed) = oldEdgeSet K chosen fixed := by
    rw [hpEdges,← fixed_range_retained]
  let Rnew : SupportedRepair (originalTower T chosen factor)
      (fixedEdgesForRange (Pn).edges Cn (oldEdgeSet K chosen allowed)) :=
    ⟨R.1,by rw [hfEdges]; exact R.2⟩
  change ((SupportedNativeEquation.repairEquiv (originalTower T chosen factor) Pn Cn
    (oldEdgeSet K chosen allowed) newFixed Rnew).1.1.1 ⟨e.1,Set.mem_univ e.1⟩) = _
  exact SupportedNativeEquation.repair_value (originalTower T chosen factor) Pn Cn
    (oldEdgeSet K chosen allowed) newFixed Rnew e.1

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedCoverRestoration
