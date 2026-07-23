import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacket
import Formal.AG.SemanticRepair.LawEquationGeneratedPair

/-!
Input adapters from the accepted Research law-equation packet to the native
`Formal.AG` finite-free packet surface.

This file deliberately stops before a conclusion bridge theorem.  It only
translates the material Research binders into the named body inputs consumed
by `lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/

noncomputable section

universe v w r

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
namespace GroundedPacketBridge

open CoverRelativeCechGeneratedSemanticCoefficient

variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {semanticSite : SemanticRepairSite.{r, v} U.Atom}
variable {S : AAT.AG.Site.AATSite A}

/--
The body semantic input retains the complete Research skeleton beside every
projected law atom.  This makes the selected skeleton a material body input
instead of a phantom index on the Research defect source.
-/
def toBodySemanticInput
    (semanticSite : SemanticRepairSite.{r, v} U.Atom)
    {coverGeometry : FinitePosetAtomLawCoverGeometry S}
    {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
    (skeleton :
      SourceSectionFreeSkeleton
        (semanticSite := semanticSite) (S := S)
        (regime := lawEquationRegime coverGeometry G)
        (C := lawEquationStandardComplex coverGeometry G)
        (Ob := G.lawEquationObstructionSheaf)
        (K := lawEquationCechComplex coverGeometry G)) :
    AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationSemanticAtomInputBody.{r, r} U where
  Component := U.Atom ×
    SourceSectionFreeSkeleton
      (semanticSite := semanticSite) (S := S)
      (regime := lawEquationRegime coverGeometry G)
      (C := lawEquationStandardComplex coverGeometry G)
      (Ob := G.lawEquationObstructionSheaf)
      (K := lawEquationCechComplex coverGeometry G)
  project := fun atom => (atom, skeleton)
  sourceTraceToken := semanticSite.sourceTraceToken

/-- Finite graph of the Research chart map, retaining both source and target. -/
def BodyBaseChart
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite) :=
  { entry : semanticCover.CoverChart × semanticSite.Chart //
    entry.2 = semanticCover.chart entry.1 }

/--
Translate the list-enumerated Research semantic cover to the body `Fintype`
surface.  The body base-chart carrier is the finite graph of the Research
chart map, so `semanticCover.chart` is retained as data rather than replaced
by an identity map.  Overlap and triple-overlap fibers are universe-lifted
fieldwise, and the selected comparison data is transported fieldwise.  The
transition carrier indexes `overlapOrder`, which is the Research
representation of the selected finite transitions.
-/
def toBodySemanticCover
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    {coverGeometry : FinitePosetAtomLawCoverGeometry S}
    {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
    (skeleton :
      SourceSectionFreeSkeleton
        (semanticSite := semanticSite) (S := S)
        (regime := lawEquationRegime coverGeometry G)
        (C := lawEquationStandardComplex coverGeometry G)
        (Ob := G.lawEquationObstructionSheaf)
        (K := lawEquationCechComplex coverGeometry G)) :
    AAT.AG.SemanticRepair.SemanticRepairCover.{r, r, max v w, r}
      (toBodySemanticInput semanticSite skeleton).toSemanticAtomProjection where
  baseCover :=
    { Chart := BodyBaseChart semanticCover
      Transition := ULift.{r, 0} (Fin semanticCover.overlapOrder.length)
      chartFinite := by
        classical
        letI : Fintype semanticCover.CoverChart :=
          Fintype.ofList semanticCover.chartOrder semanticCover.chart_complete
        exact Fintype.ofInjective
          (fun chart : BodyBaseChart semanticCover => chart.1.1)
          (by
            intro left right hsource
            apply Subtype.ext
            apply Prod.ext
            · exact hsource
            · calc
                left.1.2 = semanticCover.chart left.1.1 := left.2
                _ = semanticCover.chart right.1.1 := congrArg semanticCover.chart hsource
                _ = right.1.2 := right.2.symm)
      transitionFinite := inferInstance
      holonomySupport := fun component =>
        semanticSite.sourceTraceToken component.1 = true }
  CoverChart := ULift.{max v w, w} semanticCover.CoverChart
  chart := fun chart =>
    ⟨(chart.down, semanticCover.chart chart.down), rfl⟩
  chartInjective := by
    intro left right hchart
    apply ULift.ext
    exact congrArg (fun chart : BodyBaseChart semanticCover => chart.1.1) hchart
  chartFinite := by
    classical
    letI : Fintype semanticCover.CoverChart :=
      Fintype.ofList semanticCover.chartOrder semanticCover.chart_complete
    infer_instance
  Overlap := fun left right =>
    ULift.{max v w, w} (semanticCover.Overlap left.down right.down)
  overlapFinite := fun left right => by
    classical
    letI : Fintype
        (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
          semanticCover.Overlap pair.1 pair.2) :=
      Fintype.ofList semanticCover.overlapOrder (by
        rintro ⟨⟨first, second⟩, overlap⟩
        exact semanticCover.overlap_complete first second overlap)
    let embedding :
        semanticCover.Overlap left.down right.down ↪
          Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
            semanticCover.Overlap pair.1 pair.2 :=
      Function.Embedding.sigmaMk
        (β := fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
          semanticCover.Overlap pair.1 pair.2)
        (left.down, right.down)
    letI : Fintype (semanticCover.Overlap left.down right.down) :=
      Fintype.ofInjective embedding embedding.injective
    infer_instance
  TripleOverlap := fun left middle right =>
    ULift.{max v w, w}
      (semanticCover.TripleOverlap left.down middle.down right.down)
  tripleFinite := fun left middle right => by
    classical
    letI : Fintype
        (Sigma fun triple :
          semanticCover.CoverChart × semanticCover.CoverChart ×
            semanticCover.CoverChart =>
          semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) :=
      Fintype.ofList semanticCover.tripleOrder (by
        rintro ⟨⟨first, second, third⟩, triple⟩
        exact semanticCover.triple_complete first second third triple)
    let embedding :
        semanticCover.TripleOverlap left.down middle.down right.down ↪
          Sigma fun triple :
            semanticCover.CoverChart × semanticCover.CoverChart ×
              semanticCover.CoverChart =>
            semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2 :=
      Function.Embedding.sigmaMk
        (β := fun triple :
          semanticCover.CoverChart × semanticCover.CoverChart ×
            semanticCover.CoverChart =>
          semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2)
        (left.down, middle.down, right.down)
    letI : Fintype
        (semanticCover.TripleOverlap left.down middle.down right.down) :=
      Fintype.ofInjective embedding embedding.injective
    infer_instance
  tripleEdge01 := fun triple => ULift.up (semanticCover.tripleEdge01 triple.down)
  tripleEdge12 := fun triple => ULift.up (semanticCover.tripleEdge12 triple.down)
  tripleEdge02 := fun triple => ULift.up (semanticCover.tripleEdge02 triple.down)
  selectedOverlap := fun left right =>
    ULift.up (semanticCover.selectedOverlap left.down right.down)
  selectedTriple := fun i j k =>
    ULift.up (semanticCover.selectedTriple i.down j.down k.down)
  selectedOverlap_eq_tripleEdge01 := by
    intro i j k
    apply ULift.ext
    exact semanticCover.selectedOverlap_eq_tripleEdge01 i.down j.down k.down
  selectedOverlap_eq_tripleEdge12 := by
    intro i j k
    apply ULift.ext
    exact semanticCover.selectedOverlap_eq_tripleEdge12 i.down j.down k.down
  selectedOverlap_eq_tripleEdge02 := by
    intro i j k
    apply ULift.ext
    exact semanticCover.selectedOverlap_eq_tripleEdge02 i.down j.down k.down

/-- Fieldwise copy of the accepted coefficient-free finite-poset geometry. -/
def toBodyFinitePosetCoverGeometry
    (coverGeometry : FinitePosetAtomLawCoverGeometry S) :
    AAT.AG.Site.FinitePosetCoverGeometry S where
  ContextIndex := coverGeometry.ContextIndex
  finiteContextIndex := coverGeometry.finiteContextIndex
  context := coverGeometry.context
  contextLe := coverGeometry.contextLe
  contextLe_refl := coverGeometry.contextLe_refl
  contextLe_trans := coverGeometry.contextLe_trans
  contextLe_antisymm := coverGeometry.contextLe_antisymm
  contextLe_sound := coverGeometry.contextLe_sound
  contextMeet := coverGeometry.contextMeet
  contextMeet_le_left := coverGeometry.contextMeet_le_left
  contextMeet_le_right := coverGeometry.contextMeet_le_right
  context_le_meet := coverGeometry.context_le_meet
  base := coverGeometry.base
  cover := coverGeometry.cover
  finiteCoverIndex := coverGeometry.finiteCoverIndex
  nerveSimplex := coverGeometry.nerveSimplex
  finiteNerveSimplex := coverGeometry.finiteNerveSimplex
  simplexIndices := coverGeometry.simplexIndices
  simplexOverlap := coverGeometry.simplexOverlap
  simplexOverlap_le_patch := coverGeometry.simplexOverlap_le_patch
  adequacyRequirements := coverGeometry.adequacyRequirements
  coverAdequate := coverGeometry.coverAdequate

/--
Retain the native equation system, displayed atom provenance, and generated
quotient sheaf condition in the body organization.
-/
def toBodyWitnessIdealGeometry
    (G : SemanticLawEquationWitnessIdealGeometry semanticSite S)
    (skeleton :
      SourceSectionFreeSkeleton
        (semanticSite := semanticSite) (S := S)
        (regime := lawEquationRegime coverGeometry G)
        (C := lawEquationStandardComplex coverGeometry G)
        (Ob := G.lawEquationObstructionSheaf)
        (K := lawEquationCechComplex coverGeometry G)) :
    AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.LawEquationWitnessIdealGeometryBody
      (toBodySemanticInput semanticSite skeleton) S where
  equationSystem := G.equationSystem
  supportAtom := G.supportAtom
  supportAtom_traceVisible := G.supportAtom_traceVisible
  quotientIsSheaf := G.quotientIsSheaf

variable {coverGeometry : FinitePosetAtomLawCoverGeometry S}
variable {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
variable {skeleton :
  SourceSectionFreeSkeleton
    (semanticSite := semanticSite) (S := S)
    (regime := lawEquationRegime coverGeometry G)
    (C := lawEquationStandardComplex coverGeometry G)
    (Ob := G.lawEquationObstructionSheaf)
    (K := lawEquationCechComplex coverGeometry G)}

/-- Fieldwise translation of the material Research defect source. -/
def toBodyDefectSource
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton) :
    AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody
      (toBodySemanticInput semanticSite skeleton) (toBodyWitnessIdealGeometry G skeleton)
      (toBodyFinitePosetCoverGeometry coverGeometry) where
  LocalInput := D.LocalInput
  input := D.input
  atomSupport := D.atomSupport
  atomSupport_traceVisible := D.atomSupport_traceVisible
  lawSupport := D.lawSupport
  lawSupport_nonempty := fun i => D.lawSupport_nonempty i (D.input i)
  lawSupport_required := fun i lawIndex hmem =>
    D.lawSupport_required i (D.input i) lawIndex hmem
  objectOfLocalInput := D.objectOfLocalInput
  defect := D.defect
  holds_defect_mem := D.holds_defect_mem

/-- Transport displayed required-law fulfillment to the body defect source. -/
theorem toBodyDisplayedRequiredLawsHoldOn
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (hholds : D.DisplayedRequiredEquationsHoldOn) :
    (toBodyDefectSource D).DisplayedRequiredLawsHoldOn := by
  intro i lawIndex hmem hrequired
  exact hholds i lawIndex hmem hrequired

/-- Degree-zero selected-simplex provenance for the body canonical tuple cover. -/
def toBodyDegreeZeroSimplexMap
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (chartSimplex :
      semanticCover.CoverChart ->
        (AAT.AG.Cohomology.finitePosetCoverRelativeCover
          (lawEquationStandardComplex coverGeometry G)).simplex 0) :
    (toBodySemanticCover semanticCover skeleton).CoverChart ->
      (AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquationCoverRelativeCover
        (E := (toBodyWitnessIdealGeometry G skeleton).equationSystem)
        (toBodyWitnessIdealGeometry G skeleton).quotientIsSheaf
        (toBodyFinitePosetCoverGeometry coverGeometry).canonicalTupleCoverGeometryFromOverlap).simplex 0 :=
  by
    intro chart
    exact chartSimplex chart.down

/-- Degree-one selected-simplex provenance for the body canonical tuple cover. -/
def toBodyDegreeOneSimplexMap
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 1) :
    (Sigma fun pair :
      (toBodySemanticCover semanticCover skeleton).CoverChart ×
        (toBodySemanticCover semanticCover skeleton).CoverChart =>
      (toBodySemanticCover semanticCover skeleton).Overlap pair.1 pair.2) ->
      (AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquationCoverRelativeCover
        (E := (toBodyWitnessIdealGeometry G skeleton).equationSystem)
        (toBodyWitnessIdealGeometry G skeleton).quotientIsSheaf
        (toBodyFinitePosetCoverGeometry coverGeometry).canonicalTupleCoverGeometryFromOverlap).simplex 1 :=
  by
    intro overlap
    exact overlapSimplex
      ⟨(overlap.1.1.down, overlap.1.2.down), overlap.2.down⟩

/-- Degree-two selected-simplex provenance for the body canonical tuple cover. -/
def toBodyDegreeTwoSimplexMap
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (tripleSimplex :
      (Sigma fun triple :
        semanticCover.CoverChart × semanticCover.CoverChart ×
          semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 2) :
    (Sigma fun triple :
      (toBodySemanticCover semanticCover skeleton).CoverChart ×
        (toBodySemanticCover semanticCover skeleton).CoverChart ×
          (toBodySemanticCover semanticCover skeleton).CoverChart =>
      (toBodySemanticCover semanticCover skeleton).TripleOverlap
        triple.1 triple.2.1 triple.2.2) ->
      (AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.lawEquationCoverRelativeCover
        (E := (toBodyWitnessIdealGeometry G skeleton).equationSystem)
        (toBodyWitnessIdealGeometry G skeleton).quotientIsSheaf
        (toBodyFinitePosetCoverGeometry coverGeometry).canonicalTupleCoverGeometryFromOverlap).simplex 2 :=
  by
    intro triple
    exact tripleSimplex
      ⟨(triple.1.1.down, triple.1.2.1.down, triple.1.2.2.down), triple.2.down⟩

/--
Convert body conjunct 1 back to the original Research displayed-interpretation
realization statement.  The proof uses the body realization pointwise; it does
not reconstruct the conclusion from `hholds`.
-/
theorem toResearchDisplayedInterpretationRealization
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (hbody :
      ((toBodyDefectSource D).toLawEquationBodyCechSource
        |>.DisplayedInterpretationRealization)) :
    forall sigma :
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 0,
      D.toCoverRelativeBaseRestrictionSource.toPrimitive sigma =
        G.lawEquationObstructionSheaf.carrier.toPresheaf.map
          (homOfLE
            ((lawEquationRegime coverGeometry G).simplexOverlap_le_patch 0
              sigma 0)).op
          (D.toSupportOnlySemanticAtomLawInputBoundarySource.interpret
            ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)
            (D.toSupportOnlySemanticAtomLawInputBoundarySource.input
              ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0))) := by
  intro sigma
  let bodySigma :
      AAT.AG.Site.FinitePosetCechCanonicalTupleSimplex
        coverGeometry.cover.Index 0 :=
    sigma
  have hinterpret :
      D.toSupportOnlySemanticAtomLawInputBoundarySource.interpret
          ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)
          (D.toSupportOnlySemanticAtomLawInputBoundarySource.input
            ((lawEquationRegime coverGeometry G).simplexIndices 0 sigma 0)) =
        0 := by
    let bodySource :=
      (toBodyDefectSource D).toLawEquationBodyCechSource
    have hrestriction :
        bodySource.restriction bodySigma =
          𝟙 ((toBodyDefectSource D).toLawEquationDefectSource.chart
            (bodySource.chartOf bodySigma)) :=
      Subsingleton.elim _ _
    have hbodyInterpret :
        (toBodyDefectSource D).toLawEquationDefectSource.interpret
            (bodySource.chartOf bodySigma) = 0 := by
      have h := (hbody bodySigma).symm
      simp only [
        AAT.AG.SemanticRepair.LawEquationBodyCechSource.displayedSourceC0,
        AAT.AG.SemanticRepair.LawEquationBodyCechSource.restrictedDisplayedInterpretation]
        at h
      rw [hrestriction] at h
      have hop :
          (𝟙 ((toBodyDefectSource D).toLawEquationDefectSource.chart
            (bodySource.chartOf bodySigma))).op =
            𝟙 (Opposite.op
              ((toBodyDefectSource D).toLawEquationDefectSource.chart
                (bodySource.chartOf bodySigma))) := rfl
      rw [hop, CategoryTheory.Functor.map_id] at h
      simpa [AAT.AG.SemanticRepair.LawEquationBodyCechSource.DisplayedInterpretationRealization,
        AAT.AG.SemanticRepair.LawEquationBodyCechSource.toPrimitive,
        AAT.AG.SemanticRepair.LawEquationBodyCechSource.toBaseRestrictionSource,
        AAT.AG.SemanticRepair.LawEquationBodyCechSource.LawEquationBodyBaseRestrictionSource.toPrimitive,
        CategoryTheory.op_id, CategoryTheory.Functor.map_id,
        CategoryTheory.FunctorToTypes.map_id_apply]
        using h
    simpa [bodySource, bodySigma, toBodyDefectSource,
      AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource,
      AAT.AG.SemanticRepair.StandardFinitePosetGeneratedBoundary.FinitePosetLawEquationDefectSourceBody.toLawEquationDefectSource,
      AAT.AG.LawAlgebra.LawEquationDefectSource.interpret,
      LawEquationDefectSemanticAtomLawInputBoundarySource.toSupportOnlySemanticAtomLawInputBoundarySource,
      SemanticLawEquationWitnessIdealGeometry.toObstructionSection,
      lawEquationRegime,
      FinitePosetAtomLawCanonicalTupleOverlapGeometry.toCanonicalTupleCoverGeometry,
      toBodyWitnessIdealGeometry,
      AAT.AG.ArchitecturalEquationSystem.obstructionIdeal,
      AAT.AG.ArchitecturalEquationSystem.selectedWitnessIdealFamily,
      AAT.AG.ArchitecturalEquationSystem.witnessIdeal]
      using hbodyInterpret
  rw [hinterpret]
  exact
    (G.lawEquationObstructionSheaf.map_zero _).trans
      (G.lawEquationObstructionSheaf.map_zero _).symm

end GroundedPacketBridge
end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
