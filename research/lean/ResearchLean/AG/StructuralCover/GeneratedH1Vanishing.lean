import ResearchLean.AG.StructuralCover.StructuralLocalization
import Formal.Util.AssertStandardAxioms

/-!
# Degree-one vanishing for generated source-labelled coefficients

This module records the route-integrity obstruction discovered at I4 of
`G-105-aat-structural-cover-invariance`.  For one fixed source label, every
supported Atom is a vertex and every ordered supported pair and triple is a
generated edge and face.  Thus each source-labelled summand is a cone.

Given a raw one-cocycle, choose an anchor Atom separately for each nonempty
source support.  Evaluation on the canonical face `(anchor, left, right)`
shows that the cocycle is the coboundary of its anchor-edge primitive.  Hence
every generated all-phase complex has zero `H^1`.  In particular the nonzero
large class required by the fixed I4 firing statement cannot exist.  No
exactness, contraction, kernel element, or vanishing certificate is an input.
-/

noncomputable section

namespace AAT.AG.StructuralCover

open Cohomology
open TwoPhase

universe u

/-- Nonemptiness of the support of the source label carried by a chart coordinate. -/
theorem generatedChart_source_nonempty
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing variant).expandedNerve.Chart) :
    ∃ atom, variant.replaceSemantic.extracts chart.2.1 atom :=
  ⟨chart.1.1, chart.2.2⟩

/-- A source-wise anchor chosen only from its already generated nonempty support. -/
noncomputable def generatedSourceAnchor
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) (source : D.Source)
    (hsupport : ∃ atom, variant.replaceSemantic.extracts source atom) : U.Atom :=
  Classical.choose hsupport

/-- The source-wise anchor belongs to that source support. -/
theorem generatedSourceAnchor_extracts
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D) (source : D.Source)
    (hsupport : ∃ atom, variant.replaceSemantic.extracts source atom) :
    variant.replaceSemantic.extracts source
      (generatedSourceAnchor variant source hsupport) :=
  Classical.choose_spec hsupport

/-- The anchor chart for a generated chart's source label. -/
noncomputable def generatedAnchorChart
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing variant).expandedNerve.Chart) :
    (generatedIndexing variant).expandedNerve.Chart := by
  let hsupport := generatedChart_source_nonempty variant chart
  let anchor := generatedSourceAnchor variant chart.2.1 hsupport
  have hanchor : variant.replaceSemantic.extracts chart.2.1 anchor :=
    generatedSourceAnchor_extracts variant chart.2.1 hsupport
  exact ⟨⟨anchor, ⟨chart.2.1, hanchor⟩⟩,
    ⟨chart.2.1, hanchor⟩⟩

/-- The canonical source-labelled edge from the source anchor to a chart. -/
noncomputable def generatedAnchorEdge
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (chart : (generatedIndexing variant).expandedNerve.Chart) :
    (generatedIndexing variant).expandedNerve.EdgeComponent := by
  let anchor := generatedAnchorChart variant chart
  exact ⟨⟨(anchor.1, chart.1),
      ⟨chart.2.1, anchor.2.2, chart.2.2⟩⟩,
    ⟨chart.2.1, anchor.2.2, chart.2.2⟩⟩

/-- The canonical source-labelled cone face over a generated edge. -/
noncomputable def generatedAnchorFace
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent) :
    (generatedIndexing variant).expandedNerve.FaceComponent := by
  let left := (generatedIndexing variant).expandedNerve.edgeLeft edge
  let anchor := generatedAnchorChart variant left
  exact ⟨⟨(anchor.1, edge.1.1.1, edge.1.1.2),
      ⟨edge.2.1, anchor.2.2, edge.2.2.1, edge.2.2.2⟩⟩,
    ⟨edge.2.1, anchor.2.2, edge.2.2.1, edge.2.2.2⟩⟩

/-- The base of the cone face is the original edge. -/
@[simp]
theorem generatedAnchorFace_edge0
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent) :
    (generatedIndexing variant).expandedNerve.faceEdge0
        (generatedAnchorFace variant edge) = edge := by
  apply Sigma.ext
  · apply Subtype.ext
    rfl
  · rfl

/-- The second cone-face boundary is the anchor edge of the right endpoint. -/
@[simp]
theorem generatedAnchorFace_edge1
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent) :
    (generatedIndexing variant).expandedNerve.faceEdge1
        (generatedAnchorFace variant edge) =
      generatedAnchorEdge variant
        ((generatedIndexing variant).expandedNerve.edgeRight edge) := by
  apply Sigma.ext
  · apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  · rfl

/-- The third cone-face boundary is the anchor edge of the left endpoint. -/
@[simp]
theorem generatedAnchorFace_edge2
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (edge : (generatedIndexing variant).expandedNerve.EdgeComponent) :
    (generatedIndexing variant).expandedNerve.faceEdge2
        (generatedAnchorFace variant edge) =
      generatedAnchorEdge variant
        ((generatedIndexing variant).expandedNerve.edgeLeft edge) := by
  apply Sigma.ext
  · apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  · rfl

/-- The raw degree-zero primitive obtained by evaluating on source-anchor edges. -/
noncomputable def generatedCocyclePrimitive
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family variant).allComplex.C1) :
    (generatedCoefficientComplex family variant).allComplex.C0 :=
  fun chart => z (generatedAnchorEdge variant chart)

/--
The anchor primitive of every raw cocycle has coboundary equal to that
cocycle.

The cocycle equation is a separate premise about the raw cochain.  It is used
at the generated cone face `(anchor(source), left, right, source)`.
-/
theorem generatedD0_cocyclePrimitive
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family variant).allComplex.C1)
    (hz : (generatedCoefficientComplex family variant).allComplex.d1 z = 0) :
    (generatedCoefficientComplex family variant).allComplex.d0
        (generatedCocyclePrimitive family variant z) = z := by
  funext edge
  have hface := congrFun hz (generatedAnchorFace variant edge)
  change
    z ((generatedIndexing variant).expandedNerve.faceEdge0
        (generatedAnchorFace variant edge)) -
      z ((generatedIndexing variant).expandedNerve.faceEdge1
        (generatedAnchorFace variant edge)) +
      z ((generatedIndexing variant).expandedNerve.faceEdge2
        (generatedAnchorFace variant edge)) = 0 at hface
  rw [generatedAnchorFace_edge0, generatedAnchorFace_edge1,
    generatedAnchorFace_edge2] at hface
  change
    z (generatedAnchorEdge variant
        ((generatedIndexing variant).expandedNerve.edgeRight edge)) -
      z (generatedAnchorEdge variant
        ((generatedIndexing variant).expandedNerve.edgeLeft edge)) = z edge
  linarith

/-- Every generated degree-one cocycle lies in the generated boundary range. -/
theorem generatedEveryCocycle_is_boundary
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (z : LinearMap.ker
      (generatedCoefficientComplex family variant).allComplex.d1) :
    z ∈ LinearMap.range
      (generatedCoefficientComplex family variant).allComplex.boundaryToCycles := by
  refine ⟨generatedCocyclePrimitive family variant z.1, ?_⟩
  apply Subtype.ext
  exact generatedD0_cocyclePrimitive family variant z.1 z.2

/-- Every generated all-phase coefficient complex has zero degree-one cohomology. -/
theorem generatedAllComplex_h1Zero
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source] :
    (generatedCoefficientComplex family variant).allComplex.H1Zero := by
  intro obstruction
  obtain ⟨z, rfl⟩ :=
    (LinearMap.range
      (generatedCoefficientComplex family variant).allComplex.boundaryToCycles).mkQ_surjective
        obstruction
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact generatedEveryCocycle_is_boundary family variant z

/-- The class generated from a raw cochain and a separate cocycle equation. -/
noncomputable def generatedRawH1Class
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family variant).allComplex.C1)
    (hz : (generatedCoefficientComplex family variant).allComplex.d1 z = 0) :
    (generatedCoefficientComplex family variant).allComplex.H1 :=
  (LinearMap.range
    (generatedCoefficientComplex family variant).allComplex.boundaryToCycles).mkQ
      ⟨z, hz⟩

/-- Every raw generated cocycle represents the zero generated `H1` class. -/
theorem generatedRawH1Class_eq_zero
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D) (variant : SemanticVariant D)
    [Fintype U.Atom] [Fintype D.Source]
    (z : (generatedCoefficientComplex family variant).allComplex.C1)
    (hz : (generatedCoefficientComplex family variant).allComplex.d1 z = 0) :
    generatedRawH1Class family variant z hz = 0 :=
  generatedAllComplex_h1Zero family variant _

/--
No actual-support inclusion can fire by sending a nonzero generated large
class to zero: the required large class is already zero.
-/
theorem generated_firing_witness_impossible
    {U : AtomCarrier.{u}} {D : ExtractionDoctrine U}
    (family : DeclaredSemanticFamily D)
    {small large : SemanticVariant D}
    (hinclude : ActualSupportIncluded small large)
    [Fintype U.Atom] [Fintype D.Source] :
    ¬ ∃ (z : (generatedCoefficientComplex family large).allComplex.C1)
        (hz : (generatedCoefficientComplex family large).allComplex.d1 z = 0),
      generatedRawH1Class family large z hz ≠ 0 ∧
        (generatedRestrictionHom family hinclude).h1Map
          (generatedRawH1Class family large z hz) = 0 := by
  rintro ⟨z, hz, hnonzero, _hrestricted⟩
  exact hnonzero (generatedRawH1Class_eq_zero family large z hz)

end AAT.AG.StructuralCover

#assert_standard_axioms_only AAT.AG.StructuralCover
