import ResearchLean.AG.RelativeRepairComposition.SubdivisionMinimalRanges

/-!
# Full-candidate impossibility and empty whole dual supports after subdivision

Both candidate sets and every quotient dual are independently defined. Full
actual repair failure and the complete nonzero-obstruction empty-support family
are transported by the same whole name and quotient comparisons.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.ImpossibleRanges
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
include hc in
/-- Allowing every complete original candidate preserves existence of the independently defined actual repair. -/
theorem all_actual_candidates_iff :
    Nonempty (SupportedRepair (originalTower T chosen F)
      (fixedEdgesForRange (oldRegion K chosen P hp).edges (oldEdgeSet K chosen candidates) (OriginalRanges.allowed (oldEdgeSet K chosen candidates) Set.univ))) ↔
    Nonempty (SupportedRepair T
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates Set.univ))) := by
  have h := MinimalRanges.repair_nonempty_iff T P candidates chosen F hp hc Set.univ
  rw [Set.image_univ_of_surjective (CandidateColumns.nameEquiv candidates chosen hc).surjective] at h
  exact h

include hc in
/-- The entire family of quotient duals nonzero on the actual obstruction and with empty full support is preserved. -/
theorem empty_support_duals_iff :
    (∃ psi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)), psi (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ≠ 0 ∧ NamedDual.support (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) psi = ∅) ↔
      (∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) T.toTower.localCoefficients P candidates hlinear), phi (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) ≠ 0 ∧ NamedDual.support (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) phi = ∅) := by
  have hf := MinimalRanges.actual_support_family T P candidates chosen F hp hc hlinear houtside hfixed
  have h : (∃ psi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)), psi (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) ≠ 0 ∧ ∅ = NamedDual.support (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) psi) ↔
      (∃ phi : Module.Dual k (OriginalRanges.ObstructionSpace (k := k) T.toTower.localCoefficients P candidates hlinear), phi (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) ≠ 0 ∧ ∅ = (CandidateColumns.nameEquiv candidates chosen hc) '' NamedDual.support (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) phi) :=
    Iff.of_eq (congrArg (fun family : Set (Set (oldEdgeSet K chosen candidates)) => (∅ : Set (oldEdgeSet K chosen candidates)) ∈ family) hf)
  constructor
  · rintro ⟨psi,hp,hs⟩
    obtain ⟨phi,hp',hs'⟩ := h.mp ⟨psi,hp,hs.symm⟩
    exact ⟨phi,hp',Set.image_eq_empty.mp hs'.symm⟩
  · rintro ⟨phi,hp,hs⟩
    obtain ⟨psi,hp',hs'⟩ := h.mpr ⟨phi,hp,by rw [hs]; simp⟩
    exact ⟨psi,hp',hs'.symm⟩

include hc in
/-- Every complete original permission range has a transversal exactly when the corresponding split range does. -/
theorem no_transversal_iff :
    (∀ V : Set (oldEdgeSet K chosen candidates), ¬ NamedDual.Hits (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) (-ActualEquation.defectFamily (originalTower T chosen F) (oldRegion K chosen P hp) (fixed_face_laws T chosen F P hp hfixed))) V) ↔
      (∀ S : Set candidates, ¬ NamedDual.Hits (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) (-ActualEquation.defectFamily T P hfixed)) S) := by
  constructor
  · intro h S
    exact fun hh => h ((CandidateColumns.nameEquiv candidates chosen hc) '' S)
      ((MinimalRanges.obstruction_hits_iff T P candidates chosen F hp hc hlinear houtside hfixed S).mpr hh)
  · intro h V
    have hv := MinimalRanges.obstruction_hits_iff T P candidates chosen F hp hc hlinear houtside hfixed
      ((CandidateColumns.nameEquiv candidates chosen hc).symm '' V)
    rw [(CandidateColumns.nameEquiv candidates chosen hc).image_symm_image] at hv
    exact fun hh => h _ (hv.mp hh)

end AAT.AG.RelativeRepairComposition.Subdivision.ImpossibleRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.ImpossibleRanges
