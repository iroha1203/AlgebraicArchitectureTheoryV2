import ResearchLean.AG.RelativeRepairComposition.SubdivisionDualSupports
import ResearchLean.AG.RelativeRepairComposition.SubdivisionSupportedSolutions
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification

/-!
# All actual permission ranges and minimal full dual transversals after subdivision

Name transport includes every original candidate subset. The independently
defined actual repairs, signed defect quotient and all quotient duals are used
in the same comparisons, including empty ranges and impossible full ranges.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.MinimalRanges
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)
attribute [local instance] LinearCoefficients.coefficientModules
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)
local notation "M" => T.toTower.localCoefficients
local notation "newP" => oldRegion K chosen P hp
local notation "newCandidates" => oldEdgeSet K chosen candidates
local notation "newLinear" => LinearCoefficients.edge_linear T chosen F hlinear

attribute [local instance] Classical.propDecidable
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
/-- Every retained allowed set consists exactly of the same complete original candidate names. -/
theorem allowed_eq (S : Set candidates) :
    OriginalRanges.allowed (oldEdgeSet K chosen candidates) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) =
      oldEdgeSet K chosen (OriginalRanges.allowed candidates S) := by
  ext f
  constructor
  · rintro ⟨hn,⟨e,he,hne⟩⟩
    refine ⟨⟨e.1,fun h => hc (h ▸ e.2)⟩,⟨e.2,he⟩,?_⟩
    exact congrArg Subtype.val hne
  · rintro ⟨e,⟨he,hs⟩,rfl⟩
    exact ⟨((CandidateColumns.nameEquiv candidates chosen hc) ⟨e.1,he⟩).2,⟨⟨e.1,he⟩,hs,rfl⟩⟩

/-- Every new actual fixed-name range is the retained complete original range, without either factor. -/
theorem fixed_range_eq (S : Set candidates) :
    fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) ((CandidateColumns.nameEquiv candidates chosen hc) '' S)) =
      oldEdgeSet K chosen (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) := by
  rw [allowed_eq candidates chosen hc S]
  exact (fixed_range_retained chosen P.edges candidates (OriginalRanges.allowed candidates S)).symm

/-- Every independent new actual repair is an original actual repair and any entire fresh kernel value. -/
noncomputable def repairEquiv (S : Set candidates) :
    SupportedRepair (originalTower T chosen F)
      (fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) ((CandidateColumns.nameEquiv candidates chosen hc) '' S))) ≃
    (SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) ×
      (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :=
  (Equiv.cast (congrArg (SupportedRepair (originalTower T chosen F))
    (fixed_range_eq P candidates chosen hp hc S))).trans
    (supportedSolutionEquiv T chosen F _ (chosen_not_fixed_range chosen P candidates _ hp hc))

/-- Full all-S repair existence compares the independently specified actual native repairs. -/
theorem repair_nonempty_iff (S : Set candidates) :
    Nonempty (SupportedRepair (originalTower T chosen F)
      (fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) ((CandidateColumns.nameEquiv candidates chosen hc) '' S)))) ↔
    Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) :=
  (repairEquiv T P candidates chosen F hp hc S).nonempty_congr.trans
    ⟨fun ⟨R,_⟩ => ⟨R⟩,fun ⟨R⟩ => ⟨R,0⟩⟩

/-- All full named ranges of the same actual obstruction are preserved. -/
theorem obstruction_range_iff (S : Set candidates) :
    (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ∈ NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) ∈ NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) S := by
  rw [DualSupports.mem_range_iff T P candidates chosen F hp hc hlinear houtside,
    RangeQuotient.obstruction_eq]

/-- Every permission range hits the complete actual obstruction support family exactly as before. -/
theorem obstruction_hits_iff (S : Set candidates) :
    NamedDual.Hits (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ NamedDual.Hits (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) S := by
  rw [DualSupports.hits_iff T P candidates chosen F hp hc hlinear houtside,
    RangeQuotient.obstruction_eq]

/-- Minimal full obstruction ranges correspond at their complete original candidate sets. -/
theorem minimal_obstruction_range_iff (S : Set candidates) :
    Minimal (fun V => (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ∈ NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) V) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔
      Minimal (fun V => (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) ∈ NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) V) S := by
  rw [DualSupports.minimal_range_iff T P candidates chosen F hp hc hlinear houtside,
    RangeQuotient.obstruction_eq]

/-- All minimal actual obstruction transversals correspond for every permission range. -/
theorem minimal_obstruction_hits_iff (S : Set candidates) :
    Minimal (NamedDual.Hits (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed)))) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔
      Minimal (NamedDual.Hits (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed))) S := by
  rw [DualSupports.minimal_hits_iff T P candidates chosen F hp hc hlinear houtside,
    RangeQuotient.obstruction_eq]

include hc in
/-- Zero actual obstruction is reflected by the same full quotient comparison. -/
theorem obstruction_zero_iff : (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) = 0 ↔ (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) = 0 := by
  rw [← RangeQuotient.obstruction_eq T P candidates chosen F hp hc hlinear hfixed]
  exact ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear).map_eq_zero_iff).symm

include hlinear houtside hfixed in
/-- Every minimal independently specified actual repair range corresponds to the same original minimal range. -/
theorem minimal_actual_repair_iff (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair (originalTower T chosen F) (fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) V)))) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ Minimal (fun V => Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates V)))) S :=
  (OriginalRangeClassification.minimal_repair_iff_range (k := k)
    (originalTower T chosen F) (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear) (fixed_face_laws T chosen F P hp hfixed) ((CandidateColumns.nameEquiv candidates chosen hc) '' S)).trans
    ((minimal_obstruction_range_iff T P candidates chosen F hp hc hlinear houtside hfixed S).trans
      (OriginalRangeClassification.minimal_repair_iff_range (k := k)
        T P candidates houtside hlinear hfixed S).symm)

include houtside in
/-- At zero actual obstruction the empty complete candidate range remains the unique minimal actual range. -/
theorem minimal_zero_iff (hzero : (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) = 0) (S : Set candidates) :
    Minimal (fun V => Nonempty (SupportedRepair (originalTower T chosen F) (fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) V)))) ((CandidateColumns.nameEquiv candidates chosen hc) '' S) ↔ S = ∅ := by
  rw [minimal_actual_repair_iff T P candidates chosen F hp hc hlinear houtside hfixed]
  exact OriginalRangeClassification.minimal_zero_iff (k := k) T P candidates houtside hlinear hfixed hzero S

/-- The whole nonzero actual obstruction support family retains every complete original candidate name. -/
theorem actual_support_family :
    {U : Set (oldEdgeSet K chosen candidates) | ∃ psi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k)
      (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)), psi (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ≠ 0 ∧ U = NamedDual.support (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) psi} =
    {U : Set (oldEdgeSet K chosen candidates) | ∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k)
      T.toTower.localCoefficients P candidates hlinear), phi (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) ≠ 0 ∧ U = (CandidateColumns.nameEquiv candidates chosen hc) '' NamedDual.support (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) phi} := by
  rw [DualSupports.obstruction_support_family T P candidates chosen F hp hc hlinear houtside,
    RangeQuotient.obstruction_eq]

end AAT.AG.RelativeRepairComposition.Subdivision.MinimalRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.MinimalRanges
