import ResearchLean.AG.RelativeRepairComposition.SubdivisionDualSupports
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeObstruction
import ResearchLean.AG.RelativeRepairComposition.SubdivisionObstruction

/-!
# Same full all-column quotient, induced d2 and native H2 under subdivision

The quotient by every candidate range is compared through the independently
defined original all-column bridges. Every face representative is preserved;
the actual native H2 comparison is the same previously constructed collapse.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.RangeCohomology
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
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
local instance newAllEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := presentation K chosen)).edges) :=
  fun _ => isTrue trivial
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
/-- The independent sum of all full candidate ranges is transported to the entire original sum. -/
theorem all_ranges_map : (NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) Set.univ).map (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear).toLinearMap = (NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) Set.univ) := by
  have h := DualSupports.range_map T P candidates chosen F hp hc hlinear houtside Set.univ
  have hi : (CandidateColumns.nameEquiv candidates chosen hc) '' Set.univ = Set.univ :=
    Set.image_univ_of_surjective (CandidateColumns.nameEquiv candidates chosen hc).surjective
  simpa only [hi] using h

/-- The actual whole always quotient descends modulo every full named candidate range. -/
noncomputable def allColumnEquiv :
    ((RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear))) ⧸ (NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) Set.univ)) ≃ₗ[k]
    ((RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear)) ⧸ (NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) Set.univ)) :=
  Submodule.Quotient.equiv _ _ (RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (all_ranges_map T P candidates chosen F hp hc hlinear houtside)

/-- Every same original face representative is retained by the all-candidate quotient comparison. -/
theorem allColumnEquiv_value (c : RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P) :
    allColumnEquiv T P candidates chosen F hp hc hlinear houtside
      ((NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) Set.univ).mkQ (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) c)) =
      (NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) Set.univ).mkQ (LinearInterface.q (OriginalColumns.D (k := k) T.toTower.localCoefficients P candidates hlinear) c) := by
  change (NamedDual.ranges (OriginalRanges.column (k := k) T.toTower.localCoefficients P candidates houtside hlinear) Set.univ).mkQ ((RangeQuotient.equivalence T P candidates chosen F hp hc hlinear) (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) c)) = _
  rw [RangeQuotient.equivalence_q]

/-- The independently defined whole face quotient by full original d1 is equivalent after subdivision. -/
noncomputable def faceQuotientEquiv : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp))) ≃ₗ[k] (RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P ⧸ LinearMap.range (FiniteCoefficients.differential1 T.toTower.localCoefficients hlinear ClosedRegion.all P)) :=
  (OriginalRangeQuotient.equivalence (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)).symm.trans ((allColumnEquiv T P candidates chosen F hp hc hlinear houtside).trans (OriginalRangeQuotient.equivalence (k := k) T.toTower.localCoefficients P candidates houtside hlinear))

/-- Every face value follows the same representative through both original all-column bridges. -/
theorem faceQuotientEquiv_value (c : RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P) :
    faceQuotientEquiv T P candidates chosen F hp hc hlinear houtside
      ((LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp))).mkQ c) = (LinearMap.range (FiniteCoefficients.differential1 T.toTower.localCoefficients hlinear ClosedRegion.all P)).mkQ c := by
  have hn : (OriginalRangeQuotient.equivalence (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)).symm ((LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp))).mkQ c) =
      (NamedDual.ranges (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)) Set.univ).mkQ (LinearInterface.q (OriginalColumns.D (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (LinearCoefficients.edge_linear T chosen F hlinear)) c) := by
    apply (OriginalRangeQuotient.equivalence (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside) (LinearCoefficients.edge_linear T chosen F hlinear)).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (OriginalRangeQuotient.equivalence_value (k := k)
      (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)
      (oldEdgeSet K chosen candidates) (CandidateColumns.retained_outside P candidates chosen hp houtside)
      (LinearCoefficients.edge_linear T chosen F hlinear) c).symm
  rw [faceQuotientEquiv,LinearEquiv.trans_apply,LinearEquiv.trans_apply,hn]
  exact (congrArg (OriginalRangeQuotient.equivalence (k := k) T.toTower.localCoefficients
    P candidates houtside hlinear)
      (allColumnEquiv_value T P candidates chosen F hp hc hlinear houtside c)).trans ( OriginalRangeQuotient.equivalence_value (k := k) T.toTower.localCoefficients
    P candidates houtside hlinear c)

include hc houtside in
/-- The independent full d1 images themselves agree on every original complete face value. -/
theorem range_differential1 : LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp)) = LinearMap.range (FiniteCoefficients.differential1 T.toTower.localCoefficients hlinear ClosedRegion.all P) := by
  ext c
  rw [← Submodule.Quotient.mk_eq_zero,← Submodule.Quotient.mk_eq_zero]
  have h := (faceQuotientEquiv T P candidates chosen F hp hc hlinear houtside).map_eq_zero_iff
    (x := ((LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp) )).mkQ c))
  simpa only [faceQuotientEquiv_value] using h.symm

/-- Both independently defined complete original d2 maps keep the same full authored three-cell values. -/
theorem differential2_eq (c : RelativeCover.C2 T.toTower.localCoefficients ClosedRegion.all P) :
    FiniteCoefficients.differential2 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp) c =
      FiniteCoefficients.differential2 T.toTower.localCoefficients hlinear ClosedRegion.all P c := by
  rw [FiniteCoefficients.differential2_eq,FiniteCoefficients.differential2_eq]
  apply Subtype.ext
  funext f
  have hn := congrFun (RelativeCover.original3_restrict (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)
    (RelativeCover.d2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) c)) f
  have hnd := congrArg (fun z : RelativeComplex.relativeC3 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) => z.1 f.1)
    (RelativeCover.original_d2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) c)
  have ho := congrFun (RelativeCover.original3_restrict T.toTower.localCoefficients P
    (RelativeCover.d2 T.toTower.localCoefficients ClosedRegion.all P c)) f
  have hod := congrArg (fun z : RelativeComplex.relativeC3 T.toTower.localCoefficients P => z.1 f.1)
    (RelativeCover.original_d2 T.toTower.localCoefficients P c)
  exact hn.symm.trans (hnd.trans ((congrFun (d2_substitute T chosen F
    (fun f => c.1 ⟨f,Set.mem_univ f⟩)) f.1).trans (hod.symm.trans ho)))

/-- The induced d2 square commutes on the whole independent full face quotient. -/
theorem inducedD2_commute (x : (RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all (oldRegion K chosen P hp) ⧸ LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp)))) :
    OriginalRangeQuotient.inducedD2 (k := k) T.toTower.localCoefficients P hlinear
      (faceQuotientEquiv T P candidates chosen F hp hc hlinear houtside x) =
    OriginalRangeQuotient.inducedD2 (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (LinearCoefficients.edge_linear T chosen F hlinear) x := by
  obtain ⟨c,rfl⟩ := (LinearMap.range (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients (LinearCoefficients.edge_linear T chosen F hlinear) ClosedRegion.all (oldRegion K chosen P hp))).mkQ_surjective x
  rw [faceQuotientEquiv_value,OriginalRangeQuotient.inducedD2_value,
    OriginalRangeQuotient.inducedD2_value]
  exact (differential2_eq T P chosen F hp hlinear c).symm

/-- Equality of both candidate index sets transports the same full cycle class through the same native iso. -/
theorem transportH2Iso_class {S V : Set (EdgeName (K := presentation K chosen))} (h : S = V)
    (i : AddCommGrpCat.of (RelativeComplex.H2 (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) S S) ≅
      AddCommGrpCat.of (RelativeComplex.H2 T.toTower.localCoefficients P ∅ ∅))
    (z : RelativeComplex.Z2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp))
    (hi : i.hom (QuotientAddGroup.mk z) = QuotientAddGroup.mk (collapseZ2 T chosen F P hp z)) :
    (h ▸ i : AddCommGrpCat.of (RelativeComplex.H2 (originalTower T chosen F).toTower.localCoefficients
      (oldRegion K chosen P hp) V V) ≅
      AddCommGrpCat.of (RelativeComplex.H2 T.toTower.localCoefficients P ∅ ∅)).hom
      (QuotientAddGroup.mk z) = QuotientAddGroup.mk (collapseZ2 T chosen F P hp z) := by
  cases h
  exact hi

/-- The empty-candidate original H2 comparison is precisely the same actual native collapse. -/
noncomputable def unrestrictedH2Iso :
    AddCommGrpCat.of (RelativeComplex.H2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) ∅ ∅) ≅
      AddCommGrpCat.of (RelativeComplex.H2 T.toTower.localCoefficients P ∅ ∅) := by
  exact (old_set_empty K chosen) ▸ relativeH2Iso T chosen F P ∅ ∅ hp (by simp)

/-- Every full native H2 representative keeps its unchanged full original face cocycle. -/
theorem unrestrictedH2Iso_class (z : RelativeComplex.Z2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)) :
    (unrestrictedH2Iso T P chosen F hp).hom (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (collapseZ2 T chosen F P hp z) := by
  exact transportH2Iso_class T P chosen F hp (old_set_empty K chosen)
    (relativeH2Iso T chosen F P ∅ ∅ hp (by simp)) z
    (relativeH2Iso_class T chosen F P ∅ ∅ hp (by simp) z)

/-- The whole original H2 class square commutes with both independently generated full d1 quotients. -/
theorem nativeH2_commute (x : RelativeComplex.H2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) ∅ ∅) :
    faceQuotientEquiv T P candidates chosen F hp hc hlinear houtside
      (OriginalNativeRangeCohomology.classMap (k := k) (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) (LinearCoefficients.edge_linear T chosen F hlinear) x).1 =
      (OriginalNativeRangeCohomology.classMap (k := k) T.toTower.localCoefficients P hlinear
        ((unrestrictedH2Iso T P chosen F hp).hom x)).1 := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective
    (RelativeComplex.d1ToZ2 (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp) ∅ ∅).range x
  change faceQuotientEquiv T P candidates chosen F hp hc hlinear houtside
    (OriginalNativeRangeCohomology.classMap (k := k)
      (originalTower T chosen F).toTower.localCoefficients (oldRegion K chosen P hp)
      (LinearCoefficients.edge_linear T chosen F hlinear) (QuotientAddGroup.mk z)).1 =
    (OriginalNativeRangeCohomology.classMap (k := k) T.toTower.localCoefficients P hlinear
      ((unrestrictedH2Iso T P chosen F hp).hom (QuotientAddGroup.mk z))).1
  rw [unrestrictedH2Iso_class T P chosen F hp z,OriginalNativeRangeCohomology.classMap_value,
    OriginalNativeRangeCohomology.classMap_value,faceQuotientEquiv_value]
  rfl

end AAT.AG.RelativeRepairComposition.Subdivision.RangeCohomology
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.RangeCohomology
