import ResearchLean.AG.CrossStageCoherence.RelativeObstruction

/-!
# Total cross-stage vanishing and compatible gluing data

The total predicate is defined only by membership of the `C_G`-valued raw
cochain in the edge-reselection orbit of the identity cochain.  Its categorical
anchor is a separate family of path equations at one shared global edge
coordinate.

An aligned section records the core coordinate and its fixed-endpoint lift.
The remaining strict coordinate is an `H_G` edge gauge.  `CompatiblePairs`
stores only these low-level coordinates, alignment, and their actual
path-factorization equation; it contains neither total nor inner vanishing as
a field.  The two directions to and from a joint gauge are constructed below.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-! ## Independent total coherence equation -/

/-- One upper edge coordinate makes every authored total comparison coherent. -/
def CrossStageCoherentAt
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) : Prop :=
  ∀ cell : P.TwoCell,
    (upperReselectedPathLift data.lift reselection
      (P.twoLeft cell)).comp
      (CompositeFiberAut.hom (data.comparator cell)) =
    upperReselectedPathLift data.lift reselection (P.twoRight cell)

/-- Existence of one global upper coordinate satisfying all total cells. -/
def CrossStageCoherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ reselection : UpperEdgeReselection data.lift,
    CrossStageCoherentAt data reselection

/-- A total raw defect is identity exactly when authored equals generated. -/
theorem upperRawTwoCellDefect_eq_one_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    upperRawTwoCellDefect data reselection cell = 1 ↔
      data.comparator cell =
        upperCanonicalTwoCellComparator data reselection cell := by
  unfold upperRawTwoCellDefect
  constructor
  · intro identity
    calc
      data.comparator cell =
          (data.comparator cell *
            (upperCanonicalTwoCellComparator data reselection cell)⁻¹) *
              upperCanonicalTwoCellComparator data reselection cell := by
        simp [mul_assoc]
      _ = 1 * upperCanonicalTwoCellComparator data reselection cell :=
        congrArg (fun element =>
          element * upperCanonicalTwoCellComparator data reselection cell)
          identity
      _ = upperCanonicalTwoCellComparator data reselection cell := one_mul _
  · intro equality
    rw [equality]
    exact mul_inv_cancel _

/-- Total path coherence is equivalent to identity of the independent raw cochain. -/
theorem crossStageCoherentAt_iff_rawCochain_identity
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    CrossStageCoherentAt data reselection ↔
      upperRawDefectCochain data reselection =
        upperIdentityDefectCochain data := by
  constructor
  · intro coherent
    funext cell
    have authoredEqCanonical : data.comparator cell =
        upperCanonicalTwoCellComparator data reselection cell := by
      let left := upperReselectedPathLift data.lift reselection (P.twoLeft cell)
      letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
          left.base.base left :=
        (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
          (P.twoLeft cell)
      apply CompositeFiberAut.ext_of_strong_fac left
      exact (coherent cell).trans
        (upperCanonicalTwoCellComparator_fac data reselection cell).symm
    exact (upperRawTwoCellDefect_eq_one_iff
      data reselection cell).2 authoredEqCanonical
  · intro rawIdentity cell
    have rawCell : upperRawTwoCellDefect data reselection cell = 1 :=
      congrFun rawIdentity cell
    have authoredEqCanonical := (upperRawTwoCellDefect_eq_one_iff
      data reselection cell).1 rawCell
    rw [authoredEqCanonical]
    exact upperCanonicalTwoCellComparator_fac data reselection cell

/-! ## Four fixed vanishing notions and their trivializers -/

/-- Core-stage vanishing is exactly the inherited G-106 orbit predicate. -/
def CoreVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  TransportObstructionVanishes data.coreData

/-- Joint vanishing has the unique provenance of the total `C_G` orbit. -/
def JointVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  InUpperReselectionOrbit data (upperIdentityDefectCochain data)

/-- A core trivializer is an edge coordinate with the actual G-106 path equations. -/
structure CoreTrivializer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) where
  reselection : EdgeReselection data.coreData.lift
  coherent : CoherentAt data.coreData reselection

/-- A strict local trivializer lives on the maximal qualified strict sector. -/
structure StrictTrivializer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) where
  reselection : StrictEdgeReselection data.lift
  coherent : StrictCoherentAt data reselection

/-- Pairwise local vanishing keeps the core and strict sectors independent. -/
def LocalPairwiseVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  Nonempty (CoreTrivializer data) ∧ Nonempty (StrictTrivializer data)

theorem coreVanishes_iff_nonempty_trivializer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    CoreVanishes data ↔ Nonempty (CoreTrivializer data) := by
  rw [CoreVanishes, transportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨reselection, coherent⟩
    exact ⟨⟨reselection, coherent⟩⟩
  · rintro ⟨trivializer⟩
    exact ⟨trivializer.reselection, trivializer.coherent⟩

theorem strictVanishes_iff_nonempty_trivializer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    StrictTransportObstructionVanishes data ↔
      Nonempty (StrictTrivializer data) := by
  rw [strictTransportObstructionVanishes_iff_coherentizable]
  constructor
  · rintro ⟨reselection, coherent⟩
    exact ⟨⟨reselection, coherent⟩⟩
  · rintro ⟨trivializer⟩
    exact ⟨trivializer.reselection, trivializer.coherent⟩

/-- The total orbit predicate has a non-definitional categorical anchor. -/
theorem jointVanishes_iff_crossStageCoherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    JointVanishes data ↔ CrossStageCoherentizable data := by
  constructor
  · rintro ⟨reselection, rawIdentity⟩
    exact ⟨reselection,
      (crossStageCoherentAt_iff_rawCochain_identity
        data reselection).2 rawIdentity⟩
  · rintro ⟨reselection, coherent⟩
    exact ⟨reselection,
      (crossStageCoherentAt_iff_rawCochain_identity
        data reselection).1 coherent⟩

/-! ## From a joint gauge to an aligned section, and back -/

/-- Regard an upper edge coordinate as its own fixed-endpoint section. -/
noncomputable def edgeSectionOfUpperReselection
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) : EdgeSectionFamily data where
  core := pushforwardEdgeReselection data.lift reselection
  lift := reselection
  projects _ _ _ := rfl

/-- Total coherence pushes to alignment of the associated core section. -/
theorem edgeSectionOfUpperReselection_alignment
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection) :
    CoreAlignmentAt data (edgeSectionOfUpperReselection data reselection) := by
  intro cell
  have projected := congrArg GeometryTotalHom.base (coherent cell)
  change (upperReselectedPathLift data.lift reselection
      (P.twoLeft cell)).base.comp
      (CompositeFiberAut.hom (data.comparator cell)).base =
    (upperReselectedPathLift data.lift reselection
      (P.twoRight cell)).base at projected
  simpa only [edgeSectionOfUpperReselection, upperReselectedPathLift_base,
    compositeFiberPushforward_hom] using projected

/-- Identity in `H_G` on top of the associated section recovers the joint gauge. -/
theorem relativeUpperReselection_edgeSection_identity
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    relativeUpperReselection (edgeSectionOfUpperReselection data reselection) 1 =
      reselection := by
  funext i j edge
  change innerFiberInclusion (data.lift.geometry j) 1 *
      reselection i j edge = reselection i j edge
  rw [map_one, one_mul]

/-- Aligned-section form of joint vanishing. -/
def AlignedSectionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ edgeSection : EdgeSectionFamily data,
    ∃ alignment : CoreAlignmentAt data edgeSection,
      InnerVanishesAt data edgeSection alignment

/-- A joint coherent gauge constructs an aligned section and an inner trivializer. -/
theorem crossStageCoherentAt_to_alignedSectionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection) :
    AlignedSectionVanishes data := by
  let edgeSection := edgeSectionOfUpperReselection data reselection
  let alignment := edgeSectionOfUpperReselection_alignment data reselection coherent
  refine ⟨edgeSection, alignment, ?_⟩
  apply (innerVanishesAt_iff_sectionRelativeCoherentizable
    data edgeSection alignment).2
  refine ⟨1, ?_⟩
  intro cell
  rw [relativeUpperReselection_edgeSection_identity data reselection]
  exact coherent cell

/-- An aligned section and relative inner trivializer compose to a joint gauge. -/
theorem alignedSectionVanishes_to_crossStageCoherentizable
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    AlignedSectionVanishes data → CrossStageCoherentizable data := by
  rintro ⟨edgeSection, alignment, innerVanishes⟩
  obtain ⟨gauge, coherent⟩ :=
    (innerVanishesAt_iff_sectionRelativeCoherentizable
      data edgeSection alignment).1 innerVanishes
  exact ⟨relativeUpperReselection edgeSection gauge, coherent⟩

/-- Non-definitional aligned-section representation of the total orbit. -/
theorem jointVanishes_iff_alignedSectionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    JointVanishes data ↔ AlignedSectionVanishes data := by
  constructor
  · intro joint
    obtain ⟨reselection, coherent⟩ :=
      (jointVanishes_iff_crossStageCoherentizable data).1 joint
    exact crossStageCoherentAt_to_alignedSectionVanishes
      data reselection coherent
  · intro aligned
    apply (jointVanishes_iff_crossStageCoherentizable data).2
    exact alignedSectionVanishes_to_crossStageCoherentizable data aligned

/-! ## Compatible-pair pullback -/

/--
Low-level compatible gluing data.  The core coordinate and its lift are stored
by `section`; `alignment` makes that core coordinate a trivializer.  The single
strict gauge is required to satisfy the section-relative path equation.  No
orbit-vanishing proposition is a field.
-/
structure CompatiblePairs
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) where
  edgeSection : EdgeSectionFamily data
  alignment : CoreAlignmentAt data edgeSection
  strictGauge : StrictEdgeReselection data.lift
  restriction : SectionRelativeCoherentAt data edgeSection strictGauge

/-- The core coordinate of a compatible pair is an actual core trivializer. -/
noncomputable def CompatiblePairs.coreTrivializer
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) : CoreTrivializer data where
  reselection := pair.edgeSection.core
  coherent := pair.alignment

/-- Pairwise vanishing with the required shared lift and strict coordinate. -/
def CompatiblePairwiseVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  Nonempty (CompatiblePairs data)

/-- Construct the single joint edge gauge carried by a compatible pair. -/
noncomputable def compatiblePairsToJointGauge
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) : UpperEdgeReselection data.lift :=
  relativeUpperReselection pair.edgeSection pair.strictGauge

/-- The constructed joint gauge satisfies every total path equation. -/
theorem compatiblePairsToJointGauge_coherent
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) :
    CrossStageCoherentAt data (compatiblePairsToJointGauge pair) :=
  pair.restriction

/-- Construct compatible low-level data from one joint coherent gauge. -/
noncomputable def jointGaugeToCompatiblePairs
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift)
    (coherent : CrossStageCoherentAt data reselection) : CompatiblePairs data where
  edgeSection := edgeSectionOfUpperReselection data reselection
  alignment := edgeSectionOfUpperReselection_alignment data reselection coherent
  strictGauge := 1
  restriction := by
    intro cell
    rw [relativeUpperReselection_edgeSection_identity data reselection]
    exact coherent cell

/-- Positive gluing theorem, with explicit constructions in both directions. -/
theorem jointVanishes_iff_compatiblePairwiseVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    JointVanishes data ↔ CompatiblePairwiseVanishes data := by
  constructor
  · intro joint
    obtain ⟨reselection, coherent⟩ :=
      (jointVanishes_iff_crossStageCoherentizable data).1 joint
    exact ⟨jointGaugeToCompatiblePairs data reselection coherent⟩
  · rintro ⟨pair⟩
    apply (jointVanishes_iff_crossStageCoherentizable data).2
    exact ⟨compatiblePairsToJointGauge pair,
      compatiblePairsToJointGauge_coherent pair⟩

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
