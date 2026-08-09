import ResearchLean.AG.StructuralCover.RestrictionComparison
import Formal.Util.AssertStandardAxioms

/-!
# Localization on the common structural support

This module handles I3b-2 of
`G-105-aat-structural-cover-invariance`.  It first generates a common
three-term Cech complex from the base-classified `structuralSupport`, before
choosing any semantic variant.  A declared family member then identifies its
G-102 structural subcomplex with that common complex by retaining each Atom
tuple and source label.

The variant-specific structural submodules live in different ambient function
types, so literal equality of those submodules is not type-correct.  The
coefficient-level meaning of the fixed structural base is therefore given by
explicit degreewise linear equivalences to one common generated complex, with
both differential laws proved below.  `ConditionE` is used only to form the
variant structural differentials; it is not claimed as a generated fact.
-/

noncomputable section

namespace AAT.AG.StructuralCover

open Cohomology
open TwoPhase

universe u

/-- Common chart coordinates generated from base structural support. -/
abbrev CommonStructuralChartCoordinate
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :=
  Σ chart : (nerveOfStructural D family).Chart,
    {source : D.Source // structuralSupport D family source chart.1}

/-- Common edge coordinates generated from the derived intersection support. -/
abbrev CommonStructuralEdgeCoordinate
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :=
  Σ edge : (nerveOfStructural D family).EdgeComponent,
    {source : D.Source //
      structuralSupport D family source edge.1.1.1 ∧
        structuralSupport D family source edge.1.2.1}

/-- Common face coordinates generated from the derived triple support. -/
abbrev CommonStructuralFaceCoordinate
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :=
  Σ face : (nerveOfStructural D family).FaceComponent,
    {source : D.Source //
      structuralSupport D family source face.1.1.1 ∧
        structuralSupport D family source face.1.2.1.1 ∧
        structuralSupport D family source face.1.2.2.1}

/-- Finiteness of common structural chart coordinates. -/
noncomputable def commonStructuralChartFintype
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    [Fintype U.Atom] [Fintype D.Source] :
    Fintype (CommonStructuralChartCoordinate family) := by
  letI : Fintype (nerveOfStructural D family).Chart :=
    chartFintype (structuralSupport D family)
  exact Fintype.ofFinite _

/-- Finiteness of common structural edge coordinates. -/
noncomputable def commonStructuralEdgeFintype
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    [Fintype U.Atom] [Fintype D.Source] :
    Fintype (CommonStructuralEdgeCoordinate family) := by
  letI : Fintype (nerveOfStructural D family).EdgeComponent :=
    edgeFintype (structuralSupport D family)
  exact Fintype.ofFinite _

/-- Finiteness of common structural face coordinates. -/
noncomputable def commonStructuralFaceFintype
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    [Fintype U.Atom] [Fintype D.Source] :
    Fintype (CommonStructuralFaceCoordinate family) := by
  letI : Fintype (nerveOfStructural D family).FaceComponent :=
    faceFintype (structuralSupport D family)
  exact Fintype.ofFinite _

/-- Left endpoint of a common structural edge coordinate. -/
def commonStructuralEdgeLeft
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {family : DeclaredSemanticFamily D}
    (edge : CommonStructuralEdgeCoordinate family) :
    CommonStructuralChartCoordinate family :=
  ⟨(nerveOfStructural D family).edgeLeft edge.1,
    ⟨edge.2.1, edge.2.2.1⟩⟩

/-- Right endpoint of a common structural edge coordinate. -/
def commonStructuralEdgeRight
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {family : DeclaredSemanticFamily D}
    (edge : CommonStructuralEdgeCoordinate family) :
    CommonStructuralChartCoordinate family :=
  ⟨(nerveOfStructural D family).edgeRight edge.1,
    ⟨edge.2.1, edge.2.2.2⟩⟩

/-- First boundary edge of a common structural face coordinate. -/
def commonStructuralFaceEdge0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {family : DeclaredSemanticFamily D}
    (face : CommonStructuralFaceCoordinate family) :
    CommonStructuralEdgeCoordinate family :=
  ⟨(nerveOfStructural D family).faceEdge0 face.1,
    ⟨face.2.1, face.2.2.2.1, face.2.2.2.2⟩⟩

/-- Second boundary edge of a common structural face coordinate. -/
def commonStructuralFaceEdge1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {family : DeclaredSemanticFamily D}
    (face : CommonStructuralFaceCoordinate family) :
    CommonStructuralEdgeCoordinate family :=
  ⟨(nerveOfStructural D family).faceEdge1 face.1,
    ⟨face.2.1, face.2.2.1, face.2.2.2.2⟩⟩

/-- Third boundary edge of a common structural face coordinate. -/
def commonStructuralFaceEdge2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {family : DeclaredSemanticFamily D}
    (face : CommonStructuralFaceCoordinate family) :
    CommonStructuralEdgeCoordinate family :=
  ⟨(nerveOfStructural D family).faceEdge2 face.1,
    ⟨face.2.1, face.2.2.1, face.2.2.2.1⟩⟩

/-- Common label-wise degree-zero Cech differential. -/
def commonStructuralD0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :
    (CommonStructuralChartCoordinate family → ℚ) →ₗ[ℚ]
      (CommonStructuralEdgeCoordinate family → ℚ) where
  toFun cochain edge :=
    cochain (commonStructuralEdgeRight edge) -
      cochain (commonStructuralEdgeLeft edge)
  map_add' _ _ := by funext; simp; abel
  map_smul' _ _ := by funext; simp [mul_sub]

/-- Common label-wise degree-one alternating Cech differential. -/
def commonStructuralD1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :
    (CommonStructuralEdgeCoordinate family → ℚ) →ₗ[ℚ]
      (CommonStructuralFaceCoordinate family → ℚ) where
  toFun cochain face :=
    cochain (commonStructuralFaceEdge0 face) -
      cochain (commonStructuralFaceEdge1 face) +
        cochain (commonStructuralFaceEdge2 face)
  map_add' _ _ := by funext; simp; abel
  map_smul' _ _ := by funext; simp [mul_sub, mul_add]

/-- The variant-independent complex generated from base structural support. -/
noncomputable def commonStructuralComplex
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    [Fintype U.Atom] [Fintype D.Source] : ThreeCochainComplex ℚ := by
  letI : Fintype (CommonStructuralChartCoordinate family) :=
    commonStructuralChartFintype family
  letI : Fintype (CommonStructuralEdgeCoordinate family) :=
    commonStructuralEdgeFintype family
  letI : Fintype (CommonStructuralFaceCoordinate family) :=
    commonStructuralFaceFintype family
  exact {
    C0 := CommonStructuralChartCoordinate family → ℚ
    C1 := CommonStructuralEdgeCoordinate family → ℚ
    C2 := CommonStructuralFaceCoordinate family → ℚ
    d0 := commonStructuralD0 family
    d1 := commonStructuralD1 family
    d1_comp_d0 := by
      intro cochain
      funext face
      rcases face with ⟨face, label⟩
      rcases face with ⟨⟨first, second, third⟩, hface⟩
      simp [commonStructuralD0, commonStructuralD1,
        commonStructuralEdgeLeft, commonStructuralEdgeRight,
        commonStructuralFaceEdge0, commonStructuralFaceEdge1,
        commonStructuralFaceEdge2, nerveOfStructural, nerveOf] }

/-- A structural chart maps canonically to the same Atom in a family member. -/
def structuralChartIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    (chart : (nerveOfStructural D family).Chart) :
    (nerveOfVariantAll variant).Chart := by
  refine ⟨chart.1, ?_⟩
  rcases chart.2 with ⟨source, hsource⟩
  have hvariantSupport :=
    (variantStructuralSupport_iff family variant hvariant source chart.1).2 hsource
  exact ⟨source, hvariantSupport.1⟩

/-- A structural edge maps canonically to the same Atom pair in a family member. -/
def structuralEdgeIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    (edge : (nerveOfStructural D family).EdgeComponent) :
    (nerveOfVariantAll variant).EdgeComponent := by
  refine ⟨(structuralChartIntoVariant family variant hvariant edge.1.1,
      structuralChartIntoVariant family variant hvariant edge.1.2), ?_⟩
  rcases edge.2 with ⟨source, hleft, hright⟩
  have hleft' :=
    (variantStructuralSupport_iff family variant hvariant source edge.1.1.1).2 hleft
  have hright' :=
    (variantStructuralSupport_iff family variant hvariant source edge.1.2.1).2 hright
  exact ⟨source, hleft'.1, hright'.1⟩

/-- A structural face maps canonically to the same Atom triple in a family member. -/
def structuralFaceIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    (face : (nerveOfStructural D family).FaceComponent) :
    (nerveOfVariantAll variant).FaceComponent := by
  refine ⟨(structuralChartIntoVariant family variant hvariant face.1.1,
      structuralChartIntoVariant family variant hvariant face.1.2.1,
      structuralChartIntoVariant family variant hvariant face.1.2.2), ?_⟩
  rcases face.2 with ⟨source, hfirst, hsecond, hthird⟩
  have hfirst' :=
    (variantStructuralSupport_iff family variant hvariant source face.1.1.1).2 hfirst
  have hsecond' :=
    (variantStructuralSupport_iff family variant hvariant source face.1.2.1.1).2 hsecond
  have hthird' :=
    (variantStructuralSupport_iff family variant hvariant source face.1.2.2.1).2 hthird
  exact ⟨source, hfirst'.1, hsecond'.1, hthird'.1⟩

/-- Common chart coordinates retain their source label in every family member. -/
noncomputable def commonChartIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : CommonStructuralChartCoordinate family) :
    (generatedIndexing variant).expandedNerve.Chart := by
  refine ⟨structuralChartIntoVariant family variant hvariant chart.1,
    ⟨chart.2.1, ?_⟩⟩
  exact ((variantStructuralSupport_iff family variant hvariant
    chart.2.1 chart.1.1).2 chart.2.2).1

/-- Common edge coordinates retain their source label in every family member. -/
noncomputable def commonEdgeIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : CommonStructuralEdgeCoordinate family) :
    (generatedIndexing variant).expandedNerve.EdgeComponent := by
  refine ⟨structuralEdgeIntoVariant family variant hvariant edge.1,
    ⟨edge.2.1, ?_, ?_⟩⟩
  · exact ((variantStructuralSupport_iff family variant hvariant
      edge.2.1 edge.1.1.1.1).2 edge.2.2.1).1
  · exact ((variantStructuralSupport_iff family variant hvariant
      edge.2.1 edge.1.1.2.1).2 edge.2.2.2).1

/-- Common face coordinates retain their source label in every family member. -/
noncomputable def commonFaceIntoVariant
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : CommonStructuralFaceCoordinate family) :
    (generatedIndexing variant).expandedNerve.FaceComponent := by
  refine ⟨structuralFaceIntoVariant family variant hvariant face.1,
    ⟨face.2.1, ?_, ?_, ?_⟩⟩
  · exact ((variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.1.1).2 face.2.2.1).1
  · exact ((variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.2.1.1).2 face.2.2.2.1).1
  · exact ((variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.2.2.1).2 face.2.2.2.2).1

/-- Every common chart coordinate lands in the variant structural phase. -/
theorem commonChartIntoVariant_structural
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : CommonStructuralChartCoordinate family) :
    (cellFamily family).Structural
      ((generatedIndexing variant).chartPairAt
        (commonChartIntoVariant family variant hvariant chart)) := by
  rw [generated_chart_phase_iff family variant hvariant]
  exact chart.2.2.2

/-- Every common edge coordinate lands in the variant structural phase. -/
theorem commonEdgeIntoVariant_structural
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : CommonStructuralEdgeCoordinate family) :
    (cellFamily family).Structural
      ((generatedIndexing variant).edgePairAt
        (commonEdgeIntoVariant family variant hvariant edge)) := by
  rw [generated_edge_phase_iff family variant hvariant]
  exact ⟨edge.2.2.1.2, edge.2.2.2.2⟩

/-- Every common face coordinate lands in the variant structural phase. -/
theorem commonFaceIntoVariant_structural
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : CommonStructuralFaceCoordinate family) :
    (cellFamily family).Structural
      ((generatedIndexing variant).facePairAt
        (commonFaceIntoVariant family variant hvariant face)) := by
  rw [generated_face_phase_iff family variant hvariant]
  exact ⟨face.2.2.1.2, face.2.2.2.1.2, face.2.2.2.2.2⟩

/-- A structural variant chart coordinate returns to its common coordinate. -/
noncomputable def variantChartToCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing variant).expandedNerve.Chart)
    (hstructural : (cellFamily family).Structural
      ((generatedIndexing variant).chartPairAt chart)) :
    CommonStructuralChartCoordinate family := by
  have hphase :=
    (generated_chart_phase_iff family variant hvariant chart).1 hstructural
  have hsupport : structuralSupport D family chart.2.1 chart.1.1 :=
    (variantStructuralSupport_iff family variant hvariant
      chart.2.1 chart.1.1).1 ⟨chart.2.2, hphase⟩
  exact ⟨⟨chart.1.1, ⟨chart.2.1, hsupport⟩⟩,
    ⟨chart.2.1, hsupport⟩⟩

/-- A structural variant edge coordinate returns to its common coordinate. -/
noncomputable def variantEdgeToCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent)
    (hstructural : (cellFamily family).Structural
      ((generatedIndexing variant).edgePairAt edge)) :
    CommonStructuralEdgeCoordinate family := by
  have hphase :=
    (generated_edge_phase_iff family variant hvariant edge).1 hstructural
  have hleft : structuralSupport D family edge.2.1 edge.1.1.1.1 :=
    (variantStructuralSupport_iff family variant hvariant
      edge.2.1 edge.1.1.1.1).1 ⟨edge.2.2.1, hphase.1⟩
  have hright : structuralSupport D family edge.2.1 edge.1.1.2.1 :=
    (variantStructuralSupport_iff family variant hvariant
      edge.2.1 edge.1.1.2.1).1 ⟨edge.2.2.2, hphase.2⟩
  let left : (nerveOfStructural D family).Chart :=
    ⟨edge.1.1.1.1, ⟨edge.2.1, hleft⟩⟩
  let right : (nerveOfStructural D family).Chart :=
    ⟨edge.1.1.2.1, ⟨edge.2.1, hright⟩⟩
  exact ⟨⟨(left, right), ⟨edge.2.1, hleft, hright⟩⟩,
    ⟨edge.2.1, hleft, hright⟩⟩

/-- A structural variant face coordinate returns to its common coordinate. -/
noncomputable def variantFaceToCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing variant).expandedNerve.FaceComponent)
    (hstructural : (cellFamily family).Structural
      ((generatedIndexing variant).facePairAt face)) :
    CommonStructuralFaceCoordinate family := by
  have hphase :=
    (generated_face_phase_iff family variant hvariant face).1 hstructural
  have hfirst : structuralSupport D family face.2.1 face.1.1.1.1 :=
    (variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.1.1).1 ⟨face.2.2.1, hphase.1⟩
  have hsecond : structuralSupport D family face.2.1 face.1.1.2.1.1 :=
    (variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.2.1.1).1 ⟨face.2.2.2.1, hphase.2.1⟩
  have hthird : structuralSupport D family face.2.1 face.1.1.2.2.1 :=
    (variantStructuralSupport_iff family variant hvariant
      face.2.1 face.1.1.2.2.1).1 ⟨face.2.2.2.2, hphase.2.2⟩
  let first : (nerveOfStructural D family).Chart :=
    ⟨face.1.1.1.1, ⟨face.2.1, hfirst⟩⟩
  let second : (nerveOfStructural D family).Chart :=
    ⟨face.1.1.2.1.1, ⟨face.2.1, hsecond⟩⟩
  let third : (nerveOfStructural D family).Chart :=
    ⟨face.1.1.2.2.1, ⟨face.2.1, hthird⟩⟩
  exact ⟨⟨(first, second, third),
      ⟨face.2.1, hfirst, hsecond, hthird⟩⟩,
    ⟨face.2.1, hfirst, hsecond, hthird⟩⟩

/-- Common chart coordinates are exactly the structural variant coordinates. -/
noncomputable def commonChartCoordinateEquiv
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    CommonStructuralChartCoordinate family ≃
      {chart : (generatedIndexing variant).expandedNerve.Chart //
        (cellFamily family).Structural
          ((generatedIndexing variant).chartPairAt chart)} where
  toFun chart := ⟨commonChartIntoVariant family variant hvariant chart,
    commonChartIntoVariant_structural family variant hvariant chart⟩
  invFun chart := variantChartToCommon family variant hvariant chart.1 chart.2
  left_inv chart := by
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl
  right_inv chart := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Subtype.ext
      rfl
    · rfl

/-- Common edge coordinates are exactly the structural variant coordinates. -/
noncomputable def commonEdgeCoordinateEquiv
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    CommonStructuralEdgeCoordinate family ≃
      {edge : (generatedIndexing variant).expandedNerve.EdgeComponent //
        (cellFamily family).Structural
          ((generatedIndexing variant).edgePairAt edge)} where
  toFun edge := ⟨commonEdgeIntoVariant family variant hvariant edge,
    commonEdgeIntoVariant_structural family variant hvariant edge⟩
  invFun edge := variantEdgeToCommon family variant hvariant edge.1 edge.2
  left_inv edge := by
    apply Sigma.ext
    · apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    · rfl
  right_inv edge := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext <;> rfl
    · rfl

/-- Common face coordinates are exactly the structural variant coordinates. -/
noncomputable def commonFaceCoordinateEquiv
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    CommonStructuralFaceCoordinate family ≃
      {face : (generatedIndexing variant).expandedNerve.FaceComponent //
        (cellFamily family).Structural
          ((generatedIndexing variant).facePairAt face)} where
  toFun face := ⟨commonFaceIntoVariant family variant hvariant face,
    commonFaceIntoVariant_structural family variant hvariant face⟩
  invFun face := variantFaceToCommon family variant hvariant face.1 face.2
  left_inv face := by
    apply Sigma.ext
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
    · rfl
  right_inv face := by
    apply Subtype.ext
    apply Sigma.ext
    · apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        rfl
      · apply Prod.ext <;> apply Subtype.ext <;> rfl
    · rfl

/-- Common edge inclusion commutes with the left endpoint. -/
@[simp]
theorem commonEdgeIntoVariant_left
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : CommonStructuralEdgeCoordinate family) :
    commonChartIntoVariant family variant hvariant
        (commonStructuralEdgeLeft edge) =
      (generatedIndexing variant).expandedNerve.edgeLeft
        (commonEdgeIntoVariant family variant hvariant edge) := by
  rfl

/-- Common edge inclusion commutes with the right endpoint. -/
@[simp]
theorem commonEdgeIntoVariant_right
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : CommonStructuralEdgeCoordinate family) :
    commonChartIntoVariant family variant hvariant
        (commonStructuralEdgeRight edge) =
      (generatedIndexing variant).expandedNerve.edgeRight
        (commonEdgeIntoVariant family variant hvariant edge) := by
  rfl

/-- Common face inclusion commutes with its first boundary edge. -/
@[simp]
theorem commonFaceIntoVariant_edge0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : CommonStructuralFaceCoordinate family) :
    commonEdgeIntoVariant family variant hvariant
        (commonStructuralFaceEdge0 face) =
      (generatedIndexing variant).expandedNerve.faceEdge0
        (commonFaceIntoVariant family variant hvariant face) := by
  rfl

/-- Common face inclusion commutes with its second boundary edge. -/
@[simp]
theorem commonFaceIntoVariant_edge1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : CommonStructuralFaceCoordinate family) :
    commonEdgeIntoVariant family variant hvariant
        (commonStructuralFaceEdge1 face) =
      (generatedIndexing variant).expandedNerve.faceEdge1
        (commonFaceIntoVariant family variant hvariant face) := by
  rfl

/-- Common face inclusion commutes with its third boundary edge. -/
@[simp]
theorem commonFaceIntoVariant_edge2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : CommonStructuralFaceCoordinate family) :
    commonEdgeIntoVariant family variant hvariant
        (commonStructuralFaceEdge2 face) =
      (generatedIndexing variant).expandedNerve.faceEdge2
        (commonFaceIntoVariant family variant hvariant face) := by
  rfl

/-- Degree-zero structural cochains are canonically common chart functions. -/
noncomputable def structural0EquivCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family variant).structural0 ≃ₗ[ℚ]
      (commonStructuralComplex family).C0 := by
  classical
  let e := commonChartCoordinateEquiv family variant hvariant
  refine {
    toFun := fun cochain chart => cochain.1 (e chart).1
    invFun := fun cochain => ⟨fun chart =>
      if h : (cellFamily family).Structural
          ((generatedIndexing variant).chartPairAt chart) then
        cochain (e.symm ⟨chart, h⟩)
      else 0, by
        change ∀ chart,
          ¬ (cellFamily family).Structural
            ((generatedIndexing variant).chartPairAt chart) →
            (if h : (cellFamily family).Structural
                ((generatedIndexing variant).chartPairAt chart) then
              cochain (e.symm ⟨chart, h⟩)
            else 0) = 0
        intro chart hchart
        simp [hchart]⟩
    left_inv := by
      intro cochain
      apply Subtype.ext
      funext chart
      by_cases hchart : (cellFamily family).Structural
          ((generatedIndexing variant).chartPairAt chart)
      · simp [hchart, e]
      · have hzero :=
          ((generatedCoefficientComplex family variant).mem_structural0_iff
            cochain.1).1 cochain.2 chart hchart
        change cochain.1 chart = 0 at hzero
        simp [hchart, hzero]
    right_inv := by
      intro cochain
      funext chart
      have hchart := (e chart).2
      simp [hchart, e]
    map_add' := by
      intro left right
      funext chart
      rfl
    map_smul' := by
      intro scalar cochain
      funext chart
      rfl }

/-- Degree-one structural cochains are canonically common edge functions. -/
noncomputable def structural1EquivCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family variant).structural1 ≃ₗ[ℚ]
      (commonStructuralComplex family).C1 := by
  classical
  let e := commonEdgeCoordinateEquiv family variant hvariant
  refine {
    toFun := fun cochain edge => cochain.1 (e edge).1
    invFun := fun cochain => ⟨fun edge =>
      if h : (cellFamily family).Structural
          ((generatedIndexing variant).edgePairAt edge) then
        cochain (e.symm ⟨edge, h⟩)
      else 0, by
        change ∀ edge,
          ¬ (cellFamily family).Structural
            ((generatedIndexing variant).edgePairAt edge) →
            (if h : (cellFamily family).Structural
                ((generatedIndexing variant).edgePairAt edge) then
              cochain (e.symm ⟨edge, h⟩)
            else 0) = 0
        intro edge hedge
        simp [hedge]⟩
    left_inv := by
      intro cochain
      apply Subtype.ext
      funext edge
      by_cases hedge : (cellFamily family).Structural
          ((generatedIndexing variant).edgePairAt edge)
      · simp [hedge, e]
      · have hzero :=
          ((generatedCoefficientComplex family variant).mem_structural1_iff
            cochain.1).1 cochain.2 edge hedge
        change cochain.1 edge = 0 at hzero
        simp [hedge, hzero]
    right_inv := by
      intro cochain
      funext edge
      have hedge := (e edge).2
      simp [hedge, e]
    map_add' := by
      intro left right
      funext edge
      rfl
    map_smul' := by
      intro scalar cochain
      funext edge
      rfl }

/-- Degree-two structural cochains are canonically common face functions. -/
noncomputable def structural2EquivCommon
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family variant).structural2 ≃ₗ[ℚ]
      (commonStructuralComplex family).C2 := by
  classical
  let e := commonFaceCoordinateEquiv family variant hvariant
  refine {
    toFun := fun cochain face => cochain.1 (e face).1
    invFun := fun cochain => ⟨fun face =>
      if h : (cellFamily family).Structural
          ((generatedIndexing variant).facePairAt face) then
        cochain (e.symm ⟨face, h⟩)
      else 0, by
        change ∀ face,
          ¬ (cellFamily family).Structural
            ((generatedIndexing variant).facePairAt face) →
            (if h : (cellFamily family).Structural
                ((generatedIndexing variant).facePairAt face) then
              cochain (e.symm ⟨face, h⟩)
            else 0) = 0
        intro face hface
        simp [hface]⟩
    left_inv := by
      intro cochain
      apply Subtype.ext
      funext face
      by_cases hface : (cellFamily family).Structural
          ((generatedIndexing variant).facePairAt face)
      · simp [hface, e]
      · have hzero :=
          ((generatedCoefficientComplex family variant).mem_structural2_iff
            cochain.1).1 cochain.2 face hface
        change cochain.1 face = 0 at hzero
        simp [hface, hzero]
    right_inv := by
      intro cochain
      funext face
      have hface := (e face).2
      simp [hface, e]
    map_add' := by
      intro left right
      funext face
      rfl
    map_smul' := by
      intro scalar cochain
      funext face
      rfl }

/-- The chart/edge equivalences intertwine the structural degree-zero differential. -/
theorem structuralEquivCommon_comm0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (hE : (generatedCoefficientComplex family variant).ConditionE)
    (cochain : (generatedCoefficientComplex family variant).structural0) :
    structural1EquivCommon family variant hvariant
        ((generatedCoefficientComplex family variant).structuralD0 hE cochain) =
      (commonStructuralComplex family).d0
        (structural0EquivCommon family variant hvariant cochain) := by
  rfl

/-- The edge/face equivalences intertwine the structural degree-one differential. -/
theorem structuralEquivCommon_comm1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (hE : (generatedCoefficientComplex family variant).ConditionE)
    (cochain : (generatedCoefficientComplex family variant).structural1) :
    structural2EquivCommon family variant hvariant
        ((generatedCoefficientComplex family variant).structuralD1 hE cochain) =
      (commonStructuralComplex family).d1
        (structural1EquivCommon family variant hvariant cochain) := by
  rfl

/-- Pairwise fixedness in degree zero, factored through the common complex. -/
noncomputable def structuralFixed0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family first).structural0 ≃ₗ[ℚ]
      (generatedCoefficientComplex family second).structural0 :=
  (structural0EquivCommon family first hfirst).trans
    (structural0EquivCommon family second hsecond).symm

/-- Pairwise fixedness in degree one, factored through the common complex. -/
noncomputable def structuralFixed1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family first).structural1 ≃ₗ[ℚ]
      (generatedCoefficientComplex family second).structural1 :=
  (structural1EquivCommon family first hfirst).trans
    (structural1EquivCommon family second hsecond).symm

/-- Pairwise fixedness in degree two, factored through the common complex. -/
noncomputable def structuralFixed2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family first).structural2 ≃ₗ[ℚ]
      (generatedCoefficientComplex family second).structural2 :=
  (structural2EquivCommon family first hfirst).trans
    (structural2EquivCommon family second hsecond).symm

/-- Pairwise degree-zero fixedness respects the generated structural differential. -/
theorem structuralFixed_comm0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (hEfirst : (generatedCoefficientComplex family first).ConditionE)
    (hEsecond : (generatedCoefficientComplex family second).ConditionE)
    (cochain : (generatedCoefficientComplex family first).structural0) :
    structuralFixed1 family first second hfirst hsecond
        ((generatedCoefficientComplex family first).structuralD0 hEfirst cochain) =
      (generatedCoefficientComplex family second).structuralD0 hEsecond
        (structuralFixed0 family first second hfirst hsecond cochain) := by
  apply (structural1EquivCommon family second hsecond).injective
  rw [structuralEquivCommon_comm0 family second hsecond hEsecond]
  simp only [structuralFixed0, structuralFixed1, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact structuralEquivCommon_comm0 family first hfirst hEfirst cochain

/-- Pairwise degree-one fixedness respects the generated structural differential. -/
theorem structuralFixed_comm1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (hEfirst : (generatedCoefficientComplex family first).ConditionE)
    (hEsecond : (generatedCoefficientComplex family second).ConditionE)
    (cochain : (generatedCoefficientComplex family first).structural1) :
    structuralFixed2 family first second hfirst hsecond
        ((generatedCoefficientComplex family first).structuralD1 hEfirst cochain) =
      (generatedCoefficientComplex family second).structuralD1 hEsecond
        (structuralFixed1 family first second hfirst hsecond cochain) := by
  apply (structural2EquivCommon family second hsecond).injective
  rw [structuralEquivCommon_comm1 family second hsecond hEsecond]
  simp only [structuralFixed1, structuralFixed2, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact structuralEquivCommon_comm1 family first hfirst hEfirst cochain

/--
Every two declared variants have the same generated structural complex through
the common base, with both cochain laws.
-/
theorem generatedStructuralComplex_fixed
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    (first second : SemanticVariant D)
    (hfirst : first ∈ family.members) (hsecond : second ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (hEfirst : (generatedCoefficientComplex family first).ConditionE)
    (hEsecond : (generatedCoefficientComplex family second).ConditionE) :
    (∀ cochain,
      structuralFixed1 family first second hfirst hsecond
          ((generatedCoefficientComplex family first).structuralD0
            hEfirst cochain) =
        (generatedCoefficientComplex family second).structuralD0 hEsecond
          (structuralFixed0 family first second hfirst hsecond cochain)) ∧
    (∀ cochain,
      structuralFixed2 family first second hfirst hsecond
          ((generatedCoefficientComplex family first).structuralD1
            hEfirst cochain) =
        (generatedCoefficientComplex family second).structuralD1 hEsecond
          (structuralFixed1 family first second hfirst hsecond cochain)) :=
  ⟨structuralFixed_comm0 family first second hfirst hsecond hEfirst hEsecond,
    structuralFixed_comm1 family first second hfirst hsecond hEfirst hEsecond⟩

end AAT.AG.StructuralCover

#assert_standard_axioms_only AAT.AG.StructuralCover
