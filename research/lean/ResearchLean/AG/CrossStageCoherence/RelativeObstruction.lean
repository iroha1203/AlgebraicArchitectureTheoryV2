import ResearchLean.AG.CrossStageCoherence.SectionDecomposition

/-!
# Section-relative inner obstruction

A strict edge gauge is applied globally on top of an aligned edge section.
Its pushforward is identity, so the resulting edge section has the same core
coordinate and inherits the same alignment.  The relative inner raw cochain is
therefore `H_G`-valued.

Vanishing is defined by the `H_G` edge orbit.  Independently,
`SectionRelativeCoherentAt` is the family of authored path-factorization
equations at one shared global edge coordinate.  Their equivalence is proved
using cancellation and composite strong-cocartesian uniqueness.  The final
section proves invariance under replacement by another edge section lifting
the same core coordinate; the replacement gauge is derived edgewise in
`H_G`.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-- Apply one global strict gauge on top of a lifted edge section. -/
noncomputable def relativeUpperReselection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (edgeSection : EdgeSectionFamily data)
    (gauge : StrictEdgeReselection data.lift) :
    UpperEdgeReselection data.lift :=
  strictToUpperReselection data.lift gauge * edgeSection.lift

/-- The relative upper coordinate still projects to the same core coordinate. -/
theorem relativeUpperReselection_projects
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (edgeSection : EdgeSectionFamily data)
    (gauge : StrictEdgeReselection data.lift)
    (i j : P.Vertex) (edge : P.Edge i j) :
    compositeFiberPushforward (data.lift.geometry j)
        (relativeUpperReselection edgeSection gauge i j edge) =
      edgeSection.core i j edge := by
  change compositeFiberPushforward (data.lift.geometry j)
      (innerFiberInclusion (data.lift.geometry j) (gauge i j edge) *
        edgeSection.lift i j edge) = edgeSection.core i j edge
  rw [map_mul, edgeSection.projects]
  have kernelIdentity : compositeFiberPushforward (data.lift.geometry j)
      (innerFiberInclusion (data.lift.geometry j) (gauge i j edge)) = 1 :=
    (compositeFiberPushforward_eq_one_iff _).2 (gauge i j edge).2
  rw [kernelIdentity, one_mul]

/-- The relative coordinate packaged again as an edge section. -/
noncomputable def relativeEdgeSection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (edgeSection : EdgeSectionFamily data)
    (gauge : StrictEdgeReselection data.lift) : EdgeSectionFamily data where
  core := edgeSection.core
  lift := relativeUpperReselection edgeSection gauge
  projects := relativeUpperReselection_projects edgeSection gauge

/-- Alignment is unchanged because a relative section has the same core coordinate. -/
theorem relativeEdgeSection_alignment
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection)
    (gauge : StrictEdgeReselection data.lift) :
    CoreAlignmentAt data (relativeEdgeSection edgeSection gauge) :=
  alignment

/-- Relative inner obstruction at one total cell. -/
noncomputable def relativeInnerObstruction
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection)
    (gauge : StrictEdgeReselection data.lift) (cell : P.TwoCell) :
    InnerFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  sectionInnerObstruction data (relativeEdgeSection edgeSection gauge)
    (relativeEdgeSection_alignment edgeSection alignment gauge) cell

/-- Relative `H_G` cochain at one shared strict edge coordinate. -/
noncomputable def relativeInnerDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection)
    (gauge : StrictEdgeReselection data.lift) :
    (cell : P.TwoCell) →
      InnerFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  fun cell => relativeInnerObstruction data edgeSection alignment gauge cell

/-- Independent identity cochain for the section-relative inner obstruction. -/
noncomputable def relativeInnerIdentityCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    (cell : P.TwoCell) →
      InnerFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  fun _ => 1

/-- `InnerVanishesAt m`: the relative inner cochain meets identity in its edge orbit. -/
def InnerVanishesAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection) : Prop :=
  ∃ gauge : StrictEdgeReselection data.lift,
    relativeInnerDefectCochain data edgeSection alignment gauge =
      relativeInnerIdentityCochain data

/-- The authored comparator factors the relative reselected paths for every cell. -/
def SectionRelativeCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (gauge : StrictEdgeReselection data.lift) : Prop :=
  ∀ cell : P.TwoCell,
    (upperReselectedPathLift data.lift
      (relativeUpperReselection edgeSection gauge)
      (P.twoLeft cell)).comp
      (CompositeFiberAut.hom (data.comparator cell)) =
    upperReselectedPathLift data.lift
      (relativeUpperReselection edgeSection gauge)
      (P.twoRight cell)

/-- Existence of one global relative coordinate satisfying every cell equation. -/
def SectionRelativeCoherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data) : Prop :=
  ∃ gauge : StrictEdgeReselection data.lift,
    SectionRelativeCoherentAt data edgeSection gauge

/-- One relative inner defect is identity exactly when authored equals generated. -/
theorem relativeInnerObstruction_eq_one_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection)
    (gauge : StrictEdgeReselection data.lift) (cell : P.TwoCell) :
    relativeInnerObstruction data edgeSection alignment gauge cell = 1 ↔
      data.comparator cell =
        sectionCellComparator data (relativeEdgeSection edgeSection gauge) cell := by
  let endpoint := data.lift.geometry (P.twoTarget cell)
  let generated := sectionCellComparator data
    (relativeEdgeSection edgeSection gauge) cell
  have inclusion : innerFiberInclusion endpoint
      (relativeInnerObstruction data edgeSection alignment gauge cell) =
      data.comparator cell * generated⁻¹ := by
    exact sectionInnerObstruction_inclusion data
      (relativeEdgeSection edgeSection gauge)
      (relativeEdgeSection_alignment edgeSection alignment gauge) cell
  constructor
  · intro identity
    have rawIdentity : data.comparator cell * generated⁻¹ = 1 := by
      rw [← inclusion, identity, map_one]
    calc
      data.comparator cell =
          (data.comparator cell * generated⁻¹) * generated := by simp
      _ = 1 * generated := by rw [rawIdentity]
      _ = generated := one_mul _
  · intro authoredEq
    apply innerFiberInclusion_injective endpoint
    rw [inclusion, map_one, authoredEq]
    exact mul_inv_cancel _

/-- Relative path coherence is equivalent to identity of the relative inner cochain. -/
theorem sectionRelativeCoherentAt_iff_innerCochain_identity
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection)
    (gauge : StrictEdgeReselection data.lift) :
    SectionRelativeCoherentAt data edgeSection gauge ↔
      relativeInnerDefectCochain data edgeSection alignment gauge =
        relativeInnerIdentityCochain data := by
  constructor
  · intro coherent
    funext cell
    have authoredEqGenerated : data.comparator cell =
        sectionCellComparator data (relativeEdgeSection edgeSection gauge) cell := by
      let left := upperReselectedPathLift data.lift
        (relativeUpperReselection edgeSection gauge) (P.twoLeft cell)
      letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
          left.base.base left :=
        (upperReselectLiftData data.lift
          (relativeUpperReselection edgeSection gauge)).pathLift_compositeStrong
          (P.twoLeft cell)
      apply CompositeFiberAut.ext_of_strong_fac left
      exact (coherent cell).trans
        (upperCanonicalTwoCellComparator_fac data
          (relativeUpperReselection edgeSection gauge) cell).symm
    exact (relativeInnerObstruction_eq_one_iff
      data edgeSection alignment gauge cell).2 authoredEqGenerated
  · intro rawIdentity cell
    have rawCell : relativeInnerObstruction data edgeSection alignment gauge cell = 1 :=
      congrFun rawIdentity cell
    have authoredEqGenerated := (relativeInnerObstruction_eq_one_iff
      data edgeSection alignment gauge cell).1 rawCell
    rw [authoredEqGenerated]
    exact upperCanonicalTwoCellComparator_fac data
      (relativeUpperReselection edgeSection gauge) cell

/-- Section-relative obstruction theorem, with one global gauge outside all cells. -/
theorem innerVanishesAt_iff_sectionRelativeCoherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (edgeSection : EdgeSectionFamily data)
    (alignment : CoreAlignmentAt data edgeSection) :
    InnerVanishesAt data edgeSection alignment ↔
      SectionRelativeCoherentizable data edgeSection := by
  constructor
  · rintro ⟨gauge, rawIdentity⟩
    exact ⟨gauge,
      (sectionRelativeCoherentAt_iff_innerCochain_identity
        data edgeSection alignment gauge).2 rawIdentity⟩
  · rintro ⟨gauge, coherent⟩
    exact ⟨gauge,
      (sectionRelativeCoherentAt_iff_innerCochain_identity
        data edgeSection alignment gauge).1 coherent⟩

/-! ## Replacement of an edge section over a fixed core coordinate -/

/-- The edgewise difference of two lifts of the same core coordinate lies in `H_G`. -/
noncomputable def sectionReplacementGauge
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core) :
    StrictEdgeReselection data.lift :=
  fun i j edge => innerFiberAutOfPushforwardEqOne
    (second.lift i j edge * (first.lift i j edge)⁻¹)
    (by
      rw [map_mul, map_inv, second.projects, first.projects]
      have pointEq : first.core i j edge = second.core i j edge := by
        exact congrFun (congrFun (congrFun coreEq i) j) edge
      rw [pointEq]
      exact mul_inv_cancel _)

/-- The derived replacement gauge carries the first lifted coordinate to the second. -/
theorem sectionReplacementGauge_mul_first
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core) :
    strictToUpperReselection data.lift
        (sectionReplacementGauge first second coreEq) * first.lift =
      second.lift := by
  funext i j edge
  change (second.lift i j edge * (first.lift i j edge)⁻¹) *
      first.lift i j edge = second.lift i j edge
  simp [mul_assoc]

/-- Transfer a strict gauge when replacing the lifted edge section. -/
noncomputable def transferStrictGauge
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core)
    (gauge : StrictEdgeReselection data.lift) :
    StrictEdgeReselection data.lift :=
  gauge * (sectionReplacementGauge first second coreEq)⁻¹

/-- Transferred and original relative upper coordinates are equal. -/
theorem relativeUpperReselection_transfer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core)
    (gauge : StrictEdgeReselection data.lift) :
    relativeUpperReselection second
        (transferStrictGauge first second coreEq gauge) =
      relativeUpperReselection first gauge := by
  funext i j edge
  have replacementAt := congrFun
    (congrFun
      (congrFun
        (sectionReplacementGauge_mul_first first second coreEq) i) j) edge
  have replacementAt' :
      innerFiberInclusion (data.lift.geometry j)
          (sectionReplacementGauge first second coreEq i j edge) *
        first.lift i j edge = second.lift i j edge := by
    exact replacementAt
  calc
    relativeUpperReselection second
        (transferStrictGauge first second coreEq gauge) i j edge =
      innerFiberInclusion (data.lift.geometry j) (gauge i j edge) *
        (innerFiberInclusion (data.lift.geometry j)
          (sectionReplacementGauge first second coreEq i j edge))⁻¹ *
        second.lift i j edge := by rfl
    _ = innerFiberInclusion (data.lift.geometry j) (gauge i j edge) *
        (innerFiberInclusion (data.lift.geometry j)
          (sectionReplacementGauge first second coreEq i j edge))⁻¹ *
        (innerFiberInclusion (data.lift.geometry j)
            (sectionReplacementGauge first second coreEq i j edge) *
          first.lift i j edge) := by rw [replacementAt']
    _ = innerFiberInclusion (data.lift.geometry j) (gauge i j edge) *
        first.lift i j edge := by simp [mul_assoc]
    _ = relativeUpperReselection first gauge i j edge := by rfl

/-- Relative coherentizability is invariant under replacement over the same core gauges. -/
theorem sectionRelativeCoherentizable_replacement_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core) :
    SectionRelativeCoherentizable data first ↔
      SectionRelativeCoherentizable data second := by
  constructor
  · rintro ⟨gauge, coherent⟩
    refine ⟨transferStrictGauge first second coreEq gauge, ?_⟩
    simpa only [SectionRelativeCoherentAt,
      relativeUpperReselection_transfer first second coreEq gauge] using coherent
  · rintro ⟨gauge, coherent⟩
    refine ⟨transferStrictGauge second first coreEq.symm gauge, ?_⟩
    simpa only [SectionRelativeCoherentAt,
      relativeUpperReselection_transfer second first coreEq.symm gauge] using coherent

/-- The `H_G` orbit predicate is well-defined under edge-section replacement. -/
theorem innerVanishesAt_replacement_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (first second : EdgeSectionFamily data) (coreEq : first.core = second.core)
    (firstAlignment : CoreAlignmentAt data first)
    (secondAlignment : CoreAlignmentAt data second) :
    InnerVanishesAt data first firstAlignment ↔
      InnerVanishesAt data second secondAlignment := by
  rw [innerVanishesAt_iff_sectionRelativeCoherentizable,
    innerVanishesAt_iff_sectionRelativeCoherentizable]
  exact sectionRelativeCoherentizable_replacement_iff first second coreEq

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
