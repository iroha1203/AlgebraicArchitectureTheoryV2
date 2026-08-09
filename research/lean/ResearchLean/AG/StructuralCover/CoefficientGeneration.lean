import ResearchLean.AG.StructuralCover.NerveGeneration
import ResearchLean.AG.TwoPhase.CoefficientComplex
import Formal.Util.AssertStandardAxioms

/-!
# Generated coefficients on support nerves

This module handles the I3a construction and phase-representability obligation
of `G-105-aat-structural-cover-invariance`.  For each semantic variant it
constructs the `(cell, source-label)` bases, their label-preserving Čech
differentials over `ℚ`, and the resulting G-102
`AtomIndexedCoefficientComplex` package.

## Implementation notes

G-102 assigns one `ExtractionPair` to each expanded coordinate, whereas G-105
classifies an edge or face label by all incident chart pairs.  Selecting one
endpoint would misclassify mixed-phase cells.  Instead, `cellDoctrine` has a
finite set of original Atoms as its Atom and extracts that cell exactly when
all its original Atoms are extracted.  Its variants and declared family are
functorially generated from the original data.  On a coordinate supported by a
declared variant, its derived `Structural` predicate is proved equivalent to
the conjunction of the original pair predicates.  A phase-selected sentinel
Atom was rejected because it would encode the desired conclusion.

The generated all-phase complex is not an input field chosen for the theorem:
its coordinate spaces and both differentials are constructed below from the
generated label types and tuple incidence.
-/

noncomputable section

namespace AAT.AG.StructuralCover

open Cohomology
open TwoPhase

universe u

/-- A carrier whose Atoms are finite cells of an original Atom carrier. -/
def CellCarrier (U : AtomCarrier.{u}) : AtomCarrier.{u} where
  AtomKind := Finset U.Atom
  Axis := Finset U.Atom
  Subject := Finset U.Atom
  Predicate := Finset U.Atom
  Payload := Finset U.Atom
  Atom := Finset U.Atom
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

/--
The conjunction doctrine on finite cells of original Atoms.

All nonsemantic readings are permissive.  Its extraction relation is generated
from the original doctrine's actual `extracts` predicate.
-/
def cellDoctrine {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    ExtractionDoctrine (CellCarrier U) where
  Source := D.Source
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ source (cell : Finset U.Atom) =>
    ∀ atom, atom ∈ cell → D.extracts source atom
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/-- Cell-doctrine extraction is conjunction of the original extractions. -/
@[simp]
theorem cellDoctrine_extracts_iff {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) (cell : Finset U.Atom) :
    (cellDoctrine D).extracts source cell ↔
      ∀ atom ∈ cell, D.extracts source atom := by
  simp [cellDoctrine, ExtractionDoctrine.extracts]

/-- A semantic variant generated pointwise on finite cells. -/
def cellVariant {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) : SemanticVariant (cellDoctrine D) where
  semanticReading := PUnit.unit
  semanticAllows := fun _ source (cell : Finset U.Atom) =>
    ∀ atom, atom ∈ cell → variant.replaceSemantic.extracts source atom

/-- Generated-cell variant extraction is conjunction of original variant extraction. -/
@[simp]
theorem cellVariant_extracts_iff {U : AtomCarrier.{u}}
    {D : ExtractionDoctrine U} (variant : SemanticVariant D)
    (source : D.Source) (cell : Finset U.Atom) :
    (cellVariant variant).replaceSemantic.extracts source cell ↔
      ∀ atom ∈ cell, variant.replaceSemantic.extracts source atom := by
  simp [cellVariant, SemanticVariant.replaceSemantic, cellDoctrine,
    ExtractionDoctrine.extracts]

/-- Generating cells from the original semantic component gives the cell original. -/
theorem cellVariant_original {U : AtomCarrier.{u}} (D : ExtractionDoctrine U) :
    cellVariant (SemanticVariant.original D) =
      SemanticVariant.original (cellDoctrine D) := by
  rfl

/-- The declared cell family is the direct image of the original family. -/
def cellFamily {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) :
    DeclaredSemanticFamily (cellDoctrine D) where
  members := cellVariant '' family.members
  original_mem :=
    ⟨SemanticVariant.original D, family.original_mem, cellVariant_original D⟩

/-- Every original family member generates a member of the cell family. -/
theorem cellVariant_mem {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members) :
    cellVariant variant ∈ (cellFamily family).members :=
  ⟨variant, hvariant, rfl⟩

/--
On a cell supported by one declared variant, cell structurality is exactly
pointwise structurality of all original pairs in the cell.
-/
theorem cellFamily_structural_iff
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members) (source : D.Source)
    (cell : Finset U.Atom)
    (hcurrent : ∀ atom ∈ cell,
      variant.replaceSemantic.extracts source atom) :
    (cellFamily family).Structural (source, cell) ↔
      ∀ atom ∈ cell, family.Structural (source, atom) := by
  constructor
  · intro hcell atom hatom
    intro other hother
    have hcurrentIff := hcell (cellVariant variant)
      (cellVariant_mem family variant hvariant)
    have hcurrentIff' :
        (∀ a ∈ cell, variant.replaceSemantic.extracts source a) ↔
          ∀ a ∈ cell, D.extracts source a := by
      simpa using hcurrentIff
    have hbase : ∀ a ∈ cell, D.extracts source a :=
      hcurrentIff'.1 hcurrent
    have hotherIff := hcell (cellVariant other)
      (cellVariant_mem family other hother)
    have hotherIff' :
        (∀ a ∈ cell, other.replaceSemantic.extracts source a) ↔
          ∀ a ∈ cell, D.extracts source a := by
      simpa using hotherIff
    have hotherAll :
        ∀ a ∈ cell, other.replaceSemantic.extracts source a :=
      hotherIff'.2 hbase
    exact ⟨fun _ => hbase atom hatom, fun _ => hotherAll atom hatom⟩
  · intro hall generated hgenerated
    rcases hgenerated with ⟨other, hother, rfl⟩
    rw [cellVariant_extracts_iff, cellDoctrine_extracts_iff]
    constructor
    · intro hgenerated atom hatom
      exact (hall atom hatom other hother).1 (hgenerated atom hatom)
    · intro hbase atom hatom
      exact (hall atom hatom other hother).2 (hbase atom hatom)

/-- Source labels present on one generated variant chart. -/
abbrev GeneratedChartLabel {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) (chart : (nerveOfVariantAll variant).Chart) :=
  {source : D.Source //
    variant.replaceSemantic.extracts source chart.1}

/-- Source labels present on the derived intersection of an edge's endpoints. -/
abbrev GeneratedEdgeLabel {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    (edge : (nerveOfVariantAll variant).EdgeComponent) :=
  {source : D.Source //
    variant.replaceSemantic.extracts source edge.1.1.1 ∧
      variant.replaceSemantic.extracts source edge.1.2.1}

/-- Source labels present on the derived intersection of a face's three charts. -/
abbrev GeneratedFaceLabel {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    (face : (nerveOfVariantAll variant).FaceComponent) :=
  {source : D.Source //
    variant.replaceSemantic.extracts source face.1.1.1 ∧
      variant.replaceSemantic.extracts source face.1.2.1.1 ∧
      variant.replaceSemantic.extracts source face.1.2.2.1}

/-- The singleton original-Atom cell represented by a chart coordinate. -/
noncomputable def chartCell {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {variant : SemanticVariant D} (chart : (nerveOfVariantAll variant).Chart) :
    Finset U.Atom := by
  classical
  exact {chart.1}

/-- The two-endpoint original-Atom cell represented by an edge coordinate. -/
noncomputable def edgeCell {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {variant : SemanticVariant D}
    (edge : (nerveOfVariantAll variant).EdgeComponent) : Finset U.Atom := by
  classical
  exact {edge.1.1.1, edge.1.2.1}

/-- The three-chart original-Atom cell represented by a face coordinate. -/
noncomputable def faceCell {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {variant : SemanticVariant D}
    (face : (nerveOfVariantAll variant).FaceComponent) : Finset U.Atom := by
  classical
  exact {face.1.1.1, face.1.2.1.1, face.1.2.2.1}

/--
The G-102 indexing generated from one variant's actual cell supports.

Every label map keeps the same source label while projecting a tuple cell to a
boundary cell; no incidence map is supplied independently.
-/
noncomputable def generatedIndexing
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) [Fintype U.Atom] [Fintype D.Source] :
    AtomIndexedNerveData (cellDoctrine D) (nerveOfVariantAll variant) := by
  classical
  letI : Fintype (nerveOfVariantAll variant).Chart :=
    chartFintype (variantAllSupport variant)
  letI : Fintype (nerveOfVariantAll variant).EdgeComponent :=
    edgeFintype (variantAllSupport variant)
  letI : Fintype (nerveOfVariantAll variant).FaceComponent :=
    faceFintype (variantAllSupport variant)
  exact {
    ChartBasis := GeneratedChartLabel variant
    EdgeBasis := GeneratedEdgeLabel variant
    FaceBasis := GeneratedFaceLabel variant
    chartBasisFintype := fun _ => Fintype.ofFinite _
    edgeBasisFintype := fun _ => Fintype.ofFinite _
    faceBasisFintype := fun _ => Fintype.ofFinite _
    chartPair := fun chart label => (label.1, chartCell chart)
    edgePair := fun edge label => (label.1, edgeCell edge)
    facePair := fun face label => (label.1, faceCell face)
    edgeLeftIndex := fun _edge label => ⟨label.1, label.2.1⟩
    edgeRightIndex := fun _edge label => ⟨label.1, label.2.2⟩
    faceEdge0Index := fun _face label =>
      ⟨label.1, label.2.2.1, label.2.2.2⟩
    faceEdge1Index := fun _face label =>
      ⟨label.1, label.2.1, label.2.2.2⟩
    faceEdge2Index := fun _face label =>
      ⟨label.1, label.2.1, label.2.2.1⟩ }

/-- Label-wise degree-zero Čech differential on a generated expanded nerve. -/
def generatedD0 (N : CoverNerve) :
    (N.Chart → ℚ) →ₗ[ℚ] (N.EdgeComponent → ℚ) where
  toFun cochain edge := cochain (N.edgeRight edge) - cochain (N.edgeLeft edge)
  map_add' left right := by funext edge; simp; abel
  map_smul' scalar cochain := by funext edge; simp [mul_sub]

/-- Label-wise degree-one Čech alternating differential. -/
def generatedD1 (N : CoverNerve) :
    (N.EdgeComponent → ℚ) →ₗ[ℚ] (N.FaceComponent → ℚ) where
  toFun cochain face :=
    cochain (N.faceEdge0 face) - cochain (N.faceEdge1 face) +
      cochain (N.faceEdge2 face)
  map_add' left right := by funext face; simp; abel
  map_smul' scalar cochain := by funext face; simp [mul_sub, mul_add]

/-- The actual generated finite Čech complex for one semantic variant. -/
noncomputable def generatedAllComplex
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) [Fintype U.Atom] [Fintype D.Source] :
    FiniteNerveCochainComplex (generatedIndexing variant).expandedNerve ℚ := by
  let I := generatedIndexing variant
  letI : Fintype I.expandedNerve.Chart := I.chartFintype
  letI : Fintype I.expandedNerve.EdgeComponent := I.edgeFintype
  letI : Fintype I.expandedNerve.FaceComponent := I.faceFintype
  exact {
    C0 := I.expandedNerve.Chart → ℚ
    C1 := I.expandedNerve.EdgeComponent → ℚ
    C2 := I.expandedNerve.FaceComponent → ℚ
    d0 := generatedD0 I.expandedNerve
    d1 := generatedD1 I.expandedNerve
    d1_comp_d0 := by
      intro cochain
      funext face
      rcases face with ⟨face, label⟩
      rcases face with ⟨⟨first, second, third⟩, hface⟩
      simp [generatedD0, generatedD1, I, generatedIndexing,
        AtomIndexedNerveData.expandedNerve, nerveOfVariantAll, nerveOf]
    zeroCochainCoordinates := LinearEquiv.refl ℚ _
    oneCochainCoordinates := LinearEquiv.refl ℚ _
    twoCochainCoordinates := LinearEquiv.refl ℚ _
    d0_eq_edgeIncidence := by intros; rfl
    d1_eq_faceIncidence := by intros; rfl }

/-- The generated coefficient complex packaged through the reviewed G-102 API. -/
noncomputable def generatedCoefficientComplex
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source] :
    AtomIndexedCoefficientComplex (cellDoctrine D) (cellFamily family)
      (nerveOfVariantAll variant) ℚ where
  indexing := generatedIndexing variant
  all := generatedAllComplex variant

/-- G-102 chart phase is exactly the original chart-pair phase. -/
theorem generated_chart_phase_iff
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing variant).expandedNerve.Chart) :
    (cellFamily family).Structural
        ((generatedIndexing variant).chartPairAt chart) ↔
      family.Structural (chart.2.1, chart.1.1) := by
  change (cellFamily family).Structural
      (chart.2.1, chartCell chart.1) ↔
    family.Structural (chart.2.1, chart.1.1)
  rw [cellFamily_structural_iff family variant hvariant]
  · simp [chartCell]
  · intro atom hatom
    have hatom' : atom = chart.1.1 := by
      simpa [chartCell] using hatom
    subst atom
    exact chart.2.2

/-- G-102 edge phase is exactly conjunction over the incident chart pairs. -/
theorem generated_edge_phase_iff
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent) :
    (cellFamily family).Structural
        ((generatedIndexing variant).edgePairAt edge) ↔
      family.Structural (edge.2.1, edge.1.1.1.1) ∧
        family.Structural (edge.2.1, edge.1.1.2.1) := by
  change (cellFamily family).Structural
      (edge.2.1, edgeCell edge.1) ↔
    family.Structural (edge.2.1, edge.1.1.1.1) ∧
      family.Structural (edge.2.1, edge.1.1.2.1)
  rw [cellFamily_structural_iff family variant hvariant]
  · simp [edgeCell]
  · intro atom hatom
    simp only [edgeCell, Finset.mem_insert, Finset.mem_singleton] at hatom
    rcases hatom with rfl | rfl
    · exact edge.2.2.1
    · exact edge.2.2.2

/-- G-102 face phase is exactly conjunction over all three incident charts. -/
theorem generated_face_phase_iff
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    (hvariant : variant ∈ family.members)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing variant).expandedNerve.FaceComponent) :
    (cellFamily family).Structural
        ((generatedIndexing variant).facePairAt face) ↔
      family.Structural (face.2.1, face.1.1.1.1) ∧
        family.Structural (face.2.1, face.1.1.2.1.1) ∧
        family.Structural (face.2.1, face.1.1.2.2.1) := by
  change (cellFamily family).Structural
      (face.2.1, faceCell face.1) ↔
    family.Structural (face.2.1, face.1.1.1.1) ∧
      family.Structural (face.2.1, face.1.1.2.1.1) ∧
      family.Structural (face.2.1, face.1.1.2.2.1)
  rw [cellFamily_structural_iff family variant hvariant]
  · simp [faceCell]
  · intro atom hatom
    simp only [faceCell, Finset.mem_insert, Finset.mem_singleton] at hatom
    rcases hatom with rfl | rfl | rfl
    · exact face.2.2.1
    · exact face.2.2.2.1
    · exact face.2.2.2.2

end AAT.AG.StructuralCover

#assert_standard_axioms_only AAT.AG.StructuralCover
