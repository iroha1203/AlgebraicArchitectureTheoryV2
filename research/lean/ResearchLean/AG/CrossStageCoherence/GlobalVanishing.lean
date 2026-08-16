import ResearchLean.AG.CrossStageCoherence.RelativeObstruction

/-!
# Total cross-stage vanishing and compatible gluing data

The total predicate is defined only by membership of the `C_G`-valued raw
cochain in the edge-reselection orbit of the identity cochain.  Its categorical
anchor is a separate family of path equations at one shared global edge
coordinate.

An aligned section records the core coordinate and its fixed-endpoint lift.
`CompatiblePairs` stores a core trivializer, such a lift and alignment, an
independent absolute strict trivializer, and their shared path equations on
the qualified strict faces.  It contains neither total nor inner
vanishing as a field.  The resulting joint gauge has the required core
projection and strict-face equations, while its missing all-cell equation is
exposed separately and refuted by a finite instance.

## Implementation notes

Orbit vanishing and categorical coherence remain independent definitions so
their equivalence has proof content.  `CompatiblePairs` intentionally stores
only the two stagewise trivializers and their strict-face restriction; storing
inner or all-cell coherence was rejected as conclusion-equivalent data.
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

/-- API bridge: core-orbit vanishing is exactly existence of a core trivializer. -/
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

/-- API bridge: strict-orbit vanishing is exactly existence of a strict trivializer. -/
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
The shared restriction equation between a lifted core coordinate and an
absolute strict trivializer.  It asks their composite edge coordinate to solve
only the qualified strict faces, never all two-cells of the presentation.
-/
def SharedBoundaryCompatible
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (edgeSection : EdgeSectionFamily data)
    (strictTrivializer : StrictTrivializer data) : Prop :=
  ∀ cell : StrictTwoCell data,
    (upperReselectedPathLift data.lift
      (relativeUpperReselection edgeSection strictTrivializer.reselection)
      (P.twoLeft cell.1)).comp
      (CompositeFiberAut.hom (data.comparator cell.1)) =
    upperReselectedPathLift data.lift
      (relativeUpperReselection edgeSection strictTrivializer.reselection)
      (P.twoRight cell.1)

/--
The fixed low-level Sigma/pullback data: a core trivializer, a fixed-endpoint
lift of it, core alignment, an absolute strict trivializer, and their shared
restriction equations on qualified strict faces.  Total or all-cell
section-relative coherence is deliberately absent.
-/
structure CompatiblePairs
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) where
  /-- The independently coherent core edge coordinate. -/
  coreTrivializer : CoreTrivializer data
  /-- A fixed-endpoint upper lift family. -/
  edgeSection : EdgeSectionFamily data
  /-- The lift family lies over the selected core trivializer. -/
  core_restriction : edgeSection.core = coreTrivializer.reselection
  /-- The lifted core coordinate satisfies every projected 2-cell equation. -/
  alignment : CoreAlignmentAt data edgeSection
  /-- An independently coherent absolute strict coordinate. -/
  strictTrivializer : StrictTrivializer data
  /-- Their composite coordinate solves every qualified strict face. -/
  restriction : SharedBoundaryCompatible edgeSection strictTrivializer

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
  relativeUpperReselection pair.edgeSection pair.strictTrivializer.reselection

/-- The constructed upper coordinate projects to the pair's core trivializer. -/
theorem compatiblePairsToJointGauge_projects
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) :
    pushforwardEdgeReselection data.lift
        (compatiblePairsToJointGauge pair) =
      pair.coreTrivializer.reselection := by
  rw [← pair.core_restriction]
  funext i j edge
  exact relativeUpperReselection_projects
    pair.edgeSection pair.strictTrivializer.reselection i j edge

/-- The synthesized upper coordinate satisfies every qualified strict face. -/
theorem compatiblePairsToJointGauge_strict
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) :
    ∀ cell : StrictTwoCell data,
      (upperReselectedPathLift data.lift
        (compatiblePairsToJointGauge pair) (P.twoLeft cell.1)).comp
          (CompositeFiberAut.hom (data.comparator cell.1)) =
        upperReselectedPathLift data.lift
          (compatiblePairsToJointGauge pair) (P.twoRight cell.1) :=
  pair.restriction

/--
The missing total condition for the synthesized gauge is exactly the forbidden
all-cell section-relative equation; the low-level pair does not supply it.
-/
theorem compatiblePairsToJointGauge_coherent_iff
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    {data : TwoLayerTransportData.{u, v} P U}
    (pair : CompatiblePairs data) :
    CrossStageCoherentAt data (compatiblePairsToJointGauge pair) ↔
      SectionRelativeCoherentAt data pair.edgeSection
        pair.strictTrivializer.reselection :=
  Iff.rfl

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
