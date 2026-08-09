import ResearchLean.AG.StructuralCover.CoefficientGeneration
import ResearchLean.AG.TwoPhase.CohomologyComparison
import Formal.Util.AssertStandardAxioms

/-!
# Canonical restriction along actual-support inclusion

This module handles the I3b-1 comparison obligation of
`G-105-aat-structural-cover-invariance`.  An atomwise inclusion of actual
variant supports transports every generated chart, edge, face, and source
label while retaining its Atom tuple and label.  Precomposition with those
coordinate maps gives the large-to-small restriction in degrees zero through
two.

The comparison is constructed before and independently of a cochain.  Both
Cech differential laws follow from the generated tuple incidence.  The final
theorem starts with a raw degree-one cochain and a separate cocycle equation;
it then identifies the reviewed G-102 quotient map with the class of the
restricted raw cochain.  No supplied nerve map, cochain map, kernel element, or
class comparison is an input.
-/

noncomputable section

namespace AAT.AG.StructuralCover

open Cohomology
open TwoPhase

universe u

/-- Atomwise inclusion of one variant's actual extraction support in another's. -/
def ActualSupportIncluded {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (small large : SemanticVariant D) : Prop :=
  ∀ source atom,
    small.replaceSemantic.extracts source atom →
      large.replaceSemantic.extracts source atom

namespace NerveGenerationWitness

open FiniteModel

/-- The original finite fixture support is genuinely included in the expanded support. -/
theorem original_support_included_expanded :
    ActualSupportIncluded (SemanticVariant.original doctrine) expandedVariant := by
  intro source atom horiginal
  have hbase : doctrine.extracts source atom := by
    simpa using horiginal
  exact (expandedVariant_extracts_iff source atom).2
    (Or.inl ((doctrine_extracts_iff source atom).1 hbase))

/-- The expanded finite fixture support is not included back in the original support. -/
theorem expanded_support_not_included_original :
    ¬ ActualSupportIncluded expandedVariant (SemanticVariant.original doctrine) := by
  intro hinclude
  have hexpanded :
      expandedVariant.replaceSemantic.extracts PUnit.unit
        FiniteAtom.componentC :=
    (expandedVariant_extracts_iff PUnit.unit FiniteAtom.componentC).2
      (Or.inr rfl)
  have horiginal := hinclude PUnit.unit FiniteAtom.componentC hexpanded
  have hbase : doctrine.extracts PUnit.unit FiniteAtom.componentC := by
    simpa using horiginal
  have heq :=
    (doctrine_extracts_iff PUnit.unit FiniteAtom.componentC).1 hbase
  exact FiniteAtom.noConfusion heq

end NerveGenerationWitness

/-- A generated small-support chart maps to the same Atom in the large support. -/
def includedChartMap {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    (chart : (nerveOfVariantAll small).Chart) :
    (nerveOfVariantAll large).Chart := by
  refine ⟨chart.1, ?_⟩
  rcases chart.2 with ⟨source, hsource⟩
  exact ⟨source, hinclude source chart.1 hsource⟩

/-- A generated edge maps by its Atom pair and transported common support. -/
def includedEdgeMap {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    (edge : (nerveOfVariantAll small).EdgeComponent) :
    (nerveOfVariantAll large).EdgeComponent := by
  refine ⟨(includedChartMap hinclude edge.1.1,
      includedChartMap hinclude edge.1.2), ?_⟩
  rcases edge.2 with ⟨source, hleft, hright⟩
  exact ⟨source,
    hinclude source edge.1.1.1 hleft,
    hinclude source edge.1.2.1 hright⟩

/-- A generated face maps by its Atom triple and transported common support. -/
def includedFaceMap {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    (face : (nerveOfVariantAll small).FaceComponent) :
    (nerveOfVariantAll large).FaceComponent := by
  refine ⟨(includedChartMap hinclude face.1.1,
      includedChartMap hinclude face.1.2.1,
      includedChartMap hinclude face.1.2.2), ?_⟩
  rcases face.2 with ⟨source, hfirst, hsecond, hthird⟩
  exact ⟨source,
    hinclude source face.1.1.1 hfirst,
    hinclude source face.1.2.1.1 hsecond,
    hinclude source face.1.2.2.1 hthird⟩

/-- The expanded chart map retains both the original Atom and source label. -/
noncomputable def includedGeneratedChartMap
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing small).expandedNerve.Chart) :
    (generatedIndexing large).expandedNerve.Chart :=
  ⟨includedChartMap hinclude chart.1,
    ⟨chart.2.1, hinclude chart.2.1 chart.1.1 chart.2.2⟩⟩

/-- The expanded edge map retains its Atom pair and common source label. -/
noncomputable def includedGeneratedEdgeMap
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing small).expandedNerve.EdgeComponent) :
    (generatedIndexing large).expandedNerve.EdgeComponent :=
  ⟨includedEdgeMap hinclude edge.1,
    ⟨edge.2.1,
      hinclude edge.2.1 edge.1.1.1.1 edge.2.2.1,
      hinclude edge.2.1 edge.1.1.2.1 edge.2.2.2⟩⟩

/-- The expanded face map retains its Atom triple and common source label. -/
noncomputable def includedGeneratedFaceMap
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing small).expandedNerve.FaceComponent) :
    (generatedIndexing large).expandedNerve.FaceComponent :=
  ⟨includedFaceMap hinclude face.1,
    ⟨face.2.1,
      hinclude face.2.1 face.1.1.1.1 face.2.2.1,
      hinclude face.2.1 face.1.1.2.1.1 face.2.2.2.1,
      hinclude face.2.1 face.1.1.2.2.1 face.2.2.2.2⟩⟩

/-- Edge transport commutes with its left endpoint. -/
@[simp]
theorem includedGeneratedEdgeMap_left
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing small).expandedNerve.EdgeComponent) :
    includedGeneratedChartMap hinclude
        ((generatedIndexing small).expandedNerve.edgeLeft edge) =
      (generatedIndexing large).expandedNerve.edgeLeft
        (includedGeneratedEdgeMap hinclude edge) := by
  rfl

/-- Edge transport commutes with its right endpoint. -/
@[simp]
theorem includedGeneratedEdgeMap_right
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing small).expandedNerve.EdgeComponent) :
    includedGeneratedChartMap hinclude
        ((generatedIndexing small).expandedNerve.edgeRight edge) =
      (generatedIndexing large).expandedNerve.edgeRight
        (includedGeneratedEdgeMap hinclude edge) := by
  rfl

/-- Face transport commutes with its first boundary edge. -/
@[simp]
theorem includedGeneratedFaceMap_edge0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing small).expandedNerve.FaceComponent) :
    includedGeneratedEdgeMap hinclude
        ((generatedIndexing small).expandedNerve.faceEdge0 face) =
      (generatedIndexing large).expandedNerve.faceEdge0
        (includedGeneratedFaceMap hinclude face) := by
  rfl

/-- Face transport commutes with its second boundary edge. -/
@[simp]
theorem includedGeneratedFaceMap_edge1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing small).expandedNerve.FaceComponent) :
    includedGeneratedEdgeMap hinclude
        ((generatedIndexing small).expandedNerve.faceEdge1 face) =
      (generatedIndexing large).expandedNerve.faceEdge1
        (includedGeneratedFaceMap hinclude face) := by
  rfl

/-- Face transport commutes with its third boundary edge. -/
@[simp]
theorem includedGeneratedFaceMap_edge2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (face : (generatedIndexing small).expandedNerve.FaceComponent) :
    includedGeneratedEdgeMap hinclude
        ((generatedIndexing small).expandedNerve.faceEdge2 face) =
      (generatedIndexing large).expandedNerve.faceEdge2
        (includedGeneratedFaceMap hinclude face) := by
  rfl

/-- Degree-zero large-to-small restriction is precomposition by chart inclusion. -/
noncomputable def generatedRestriction0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source] :
    ((generatedIndexing large).expandedNerve.Chart → ℚ) →ₗ[ℚ]
      ((generatedIndexing small).expandedNerve.Chart → ℚ) where
  toFun cochain chart := cochain (includedGeneratedChartMap hinclude chart)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree-one large-to-small restriction is precomposition by edge inclusion. -/
noncomputable def generatedRestriction1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source] :
    ((generatedIndexing large).expandedNerve.EdgeComponent → ℚ) →ₗ[ℚ]
      ((generatedIndexing small).expandedNerve.EdgeComponent → ℚ) where
  toFun cochain edge := cochain (includedGeneratedEdgeMap hinclude edge)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Degree-two large-to-small restriction is precomposition by face inclusion. -/
noncomputable def generatedRestriction2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source] :
    ((generatedIndexing large).expandedNerve.FaceComponent → ℚ) →ₗ[ℚ]
      ((generatedIndexing small).expandedNerve.FaceComponent → ℚ) where
  toFun cochain face := cochain (includedGeneratedFaceMap hinclude face)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
The canonical all-phase cochain map generated from actual-support inclusion.
-/
noncomputable def generatedRestrictionHom
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source] :
    ThreeCochainComplex.Hom
      (generatedCoefficientComplex family large).allComplex
      (generatedCoefficientComplex family small).allComplex where
  f0 := generatedRestriction0 hinclude
  f1 := generatedRestriction1 hinclude
  f2 := generatedRestriction2 hinclude
  comm0 cochain := by
    funext edge
    simp [generatedRestriction0, generatedRestriction1,
      AtomIndexedCoefficientComplex.allComplex, generatedCoefficientComplex,
      generatedAllComplex, generatedD0]
  comm1 cochain := by
    funext face
    simp [generatedRestriction1, generatedRestriction2,
      AtomIndexedCoefficientComplex.allComplex, generatedCoefficientComplex,
      generatedAllComplex, generatedD1]

/-- A raw large-support cocycle restricted by the canonical cochain map. -/
noncomputable def generatedRestrictedCocycle
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family large).allComplex.C1)
    (hz : (generatedCoefficientComplex family large).allComplex.d1 z = 0) :
    LinearMap.ker (generatedCoefficientComplex family small).allComplex.d1 :=
  ⟨generatedRestriction1 hinclude z, by
    change (generatedCoefficientComplex family small).allComplex.d1
      ((generatedRestrictionHom family hinclude).f1 z) = 0
    rw [← (generatedRestrictionHom family hinclude).comm1 z, hz]
    exact map_zero (generatedRestrictionHom family hinclude).f2⟩

/--
For every raw cocycle, the induced H1 map is represented by its canonical
label-wise restriction.

The cocycle proof is a separate theorem premise about the raw cochain; no
proof-bearing kernel element is an input.
-/
theorem generatedRestrictionH1_naturality
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    {small large : SemanticVariant D} (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family large).allComplex.C1)
    (hz : (generatedCoefficientComplex family large).allComplex.d1 z = 0) :
    (generatedRestrictionHom family hinclude).h1Map
        ((LinearMap.range
          (generatedCoefficientComplex family large).allComplex.boundaryToCycles).mkQ
            ⟨z, hz⟩) =
      (LinearMap.range
        (generatedCoefficientComplex family small).allComplex.boundaryToCycles).mkQ
          (generatedRestrictedCocycle family hinclude z hz) := by
  rw [ThreeCochainComplex.Hom.h1Map_mk]
  rfl

end AAT.AG.StructuralCover

#assert_standard_axioms_only AAT.AG.StructuralCover
