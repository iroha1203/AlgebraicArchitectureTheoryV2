import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationGroundedPacket
import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationWitnessInstance

/-!
G-06 law-equation layer: degree-zero boundary theorems and the concrete
end-to-end instance.

This file discharges two of the three obligations recorded by the rejected
final review after Cycle 350.

Obligation 3 (degree-zero boundary): the exact contribution of the
law-equation layer to the generated Cech surface is degree-`0` vanishing.
`displayedRequiredLawsHoldOn_constructs_sourceC0_pointwise_zero` proves that
under displayed required-law fulfillment the generated support-only
`0`-cochain is pointwise zero, and
`lawEquation_groundedRoute_isLawIndependent` proves the packet's gate-layer,
realization, comparison, and `H1`-zero conjuncts without any law premise,
fixing as a theorem that those conjuncts are construction-level facts of the
zero-base-section route rather than law-grounded descent content.

Obligation 1 (concrete end-to-end instance): on the Part I/II finite model,
this file constructs a `FinitePosetAtomLawCoverGeometry`, a source-section-free
skeleton, a lawful architecture object for the NoCycle law, a law-equation
defect source, a singleton semantic repair cover with its provenance maps,
proves the displayed required-law fulfillment, and fires
`lawEquation_constructs_groundedComparisonPacket` on the resulting bundle.
The hypothesis class of the end-to-end theorem is therefore inhabited.
-/

noncomputable section

universe u v w x y z r a b

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open Opposite
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1
open SemanticRepairObstructionTower

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis

open CoverRelativeCechGeneratedSemanticCoefficient

variable {U : AAT.AG.AtomCarrier.{r}} {A : AAT.AG.ArchitectureObject U}
variable {semanticSite : SemanticRepairSite.{r, v} U.Atom}
variable {S : AAT.AG.Site.AATSite A}

namespace LawEquationDefectSemanticAtomLawInputBoundarySource

variable {coverGeometry : FinitePosetAtomLawCoverGeometry S}
variable {G : SemanticLawEquationWitnessIdealGeometry semanticSite S}
variable {skeleton :
  SourceSectionFreeSkeleton
    (semanticSite := semanticSite) (S := S)
    (regime := lawEquationRegime coverGeometry G)
    (C := lawEquationStandardComplex coverGeometry G)
    (Ob := G.lawEquationObstructionSheaf)
    (K := lawEquationCechComplex coverGeometry G)}

/--
Degree-zero boundary, positive side: under displayed required-law fulfillment
the generated support-only `0`-cochain of the law-equation source is pointwise
zero.  This is the exact Cech-side content contributed by the law semantics:
it acts at cochain degree `0`, through the Cycle 348 vanishing theorem, and
the generated-Cech `sourceC0CechZero` is its differential shadow.
-/
theorem displayedRequiredLawsHoldOn_constructs_sourceC0_pointwise_zero
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (hholds : D.DisplayedRequiredEquationsHoldOn) :
    forall sigma :
      (AAT.AG.Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex coverGeometry G)).simplex 0,
      atomLawOverlap_sourceSectionFreeSkeleton_sourceC0 coverGeometry
          G.toSemanticAtomLawAdditiveCoefficientGeometry skeleton
          D.toSupportOnlySemanticAtomLawInputBoundarySource sigma = 0 := by
  intro sigma
  show
    G.lawEquationObstructionSheaf.carrier.toPresheaf.map
        (skeleton.zeroSimplexToChart sigma).op
        (D.toSupportOnlySemanticAtomLawInputBoundarySource.interpret
          (skeleton.zeroSimplexChart sigma)
          (D.toSupportOnlySemanticAtomLawInputBoundarySource.input
            (skeleton.zeroSimplexChart sigma))) = 0
  rw [D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds
      (skeleton.zeroSimplexChart sigma)]
  exact G.lawEquationObstructionSheaf.map_zero _

/--
Degree-zero boundary, negative side: the grounded-route conjuncts of the
end-to-end packet — gate layer, degree-wise carrier data and face-restriction
equations, cochain realization, comparison package, residual boundary, and the
semantic / additive `H1` zero readings — hold without any law premise.

This theorem fixes, as a Lean boundary rather than a docstring remark, the
Cycle 350 review finding: on the zero-base-section route those conjuncts are
construction-level facts of the generated boundary coefficient
(`residual := K.d 0 primitive`), so they must not be cited as law-grounded
descent content.  The law-grounded content of the law-equation layer is
exactly the degree-`0` vanishing theorems above.
-/
theorem lawEquation_groundedRoute_isLawIndependent
    (D :
      LawEquationDefectSemanticAtomLawInputBoundarySource coverGeometry G
        skeleton)
    (semanticCover : SemanticRepairCover.{r, v, w} semanticSite)
    (chartSimplex :
      semanticCover.CoverChart ->
        (AAT.AG.Cohomology.finitePosetCoverRelativeCover
          (lawEquationStandardComplex coverGeometry G)).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 1)
    (tripleSimplex :
      (Sigma fun triple :
        semanticCover.CoverChart × semanticCover.CoverChart ×
          semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (AAT.AG.Cohomology.finitePosetCoverRelativeCover
            (lawEquationStandardComplex coverGeometry G)).simplex 2) :
    let surface :=
      lawEquationCurrentG06InputSurface coverGeometry G semanticCover
        chartSimplex overlapSimplex tripleSimplex
    let source := D.toCoverRelativeBaseRestrictionSource
    let restrictionSource :=
      source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let boundarySource :=
      restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
    let geometry :=
      CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
        freeSource
    let boundary :=
      geometry.toBoundaryGeneratedCoefficient
        (K := surface.K) source.c0Order source.c1Order
    let generated := boundary.toGeneratedCoefficient
    let canonical :=
      CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
        (site := semanticSite) generated
    let envelope := canonical.toGeneratedEnvelope
    let realization := envelope.toCochainRealization
    Nonempty
        (SelectedSemanticCoefficientDirectRealizationLayer
          (E := envelope.toEnvelope)
          (additive := envelope.toAdditiveCechH1Data) surface) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquations
        (E := envelope.toEnvelope)
        (additive := envelope.toAdditiveCechH1Data)
        (coverBridge := surface.coverBridge)
        (K := surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeCochainRealization
          envelope.toAdditiveCechH1Data surface.K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      canonical.residualBoundary /\
      SemanticRepairH1Zero envelope.toEnvelope /\
      SemanticRepairAdditiveH1Zero envelope.toAdditiveCechH1Data := by
  dsimp
  have hroute :=
    CoverRelativeCechBaseRestrictionBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource.baseRestriction_constructs_identityC0ReplacementRoute_and_additiveCechBoundaryRoute_withoutCanonicalArgument
      (surface :=
        lawEquationCurrentG06InputSurface coverGeometry G semanticCover
          chartSimplex overlapSimplex tripleSimplex)
      coverGeometry.cover rfl
      D.toCoverRelativeBaseRestrictionSource
  rcases hroute with
    ⟨_hsection, _hsectionToLocal, _hprimitive, _hboundaryPrimitive, _hresidual,
      _hvisible, _hcontinuation, _hsource, hlayer, hface, hrealization,
      _hc0Carrier, hcomparison, _hprimitiveBoundary, hboundary, hsemanticH1,
      hadditiveH1⟩
  exact
    ⟨hlayer, hface, hrealization, hcomparison, hboundary, hsemanticH1,
      hadditiveH1⟩

end LawEquationDefectSemanticAtomLawInputBoundarySource

/-! ## Concrete end-to-end instance on the finite model -/

/--
The finite-poset atom/law cover geometry over the Part I/II finite-model site,
assembled from the existing singleton context, singleton admissible cover, and
adequacy witnesses.
-/
def finiteModelAtomLawCoverGeometry :
    FinitePosetAtomLawCoverGeometry AAT.AG.FiniteModel.site where
  ContextIndex := PUnit
  finiteContextIndex := inferInstance
  context := fun _ => AAT.AG.FiniteModel.siteContext
  contextLe := fun _ _ => True
  contextLe_refl := fun _ => trivial
  contextLe_trans := fun _ _ => trivial
  contextLe_antisymm := by
    intro i j _ _
    cases i
    cases j
    rfl
  contextLe_sound := fun _ => rfl
  contextMeet := fun _ _ => PUnit.unit
  contextMeet_le_left := fun _ _ => trivial
  contextMeet_le_right := fun _ _ => trivial
  context_le_meet := fun _ _ => trivial
  base := AAT.AG.FiniteModel.siteBase
  cover := AAT.AG.FiniteModel.siteSingletonCover
  finiteCoverIndex := by
    change Finite PUnit
    infer_instance
  nerveSimplex := fun _ => PUnit
  finiteNerveSimplex := fun _ => inferInstance
  simplexIndices := fun _ _ _ => PUnit.unit
  simplexOverlap := fun _ _ => AAT.AG.FiniteModel.siteContext
  simplexOverlap_le_patch := fun _ _ _ => rfl
  adequacyRequirements := AAT.AG.FiniteModel.siteAdequacyRequirements
  coverAdequate := AAT.AG.FiniteModel.siteSingletonCover_uAdequate

/--
A lawful finite-model architecture object for the NoCycle law: the selected
configuration carries no relations at all, so the selected dependency cycle is
absent.
-/
def finiteModelLawfulConfiguration :
    AAT.AG.AtomConfiguration AAT.AG.FiniteModel.carrier where
  family := AAT.AG.FiniteModel.allFamily
  relation := fun _ _ => False
  identification := fun _ _ => False

/-- The relation-free finite-model object. -/
def finiteModelLawfulObject :
    AAT.AG.ArchitectureObject AAT.AG.FiniteModel.carrier :=
  AAT.AG.FiniteModel.objectOfConfiguration finiteModelLawfulConfiguration

/-- The selected dependency cycle is absent from the relation-free object. -/
theorem noCycle_holds_finiteModelLawfulObject :
    ¬ AAT.AG.FiniteModel.hasDependencyCycle finiteModelLawfulObject :=
  fun h => h.1

/--
The source-section-free skeleton of the finite-model law-equation stack:
pointwise trace-visible atom and required-law choices on the generated
degree-`0` simplices, with empty selected display orders.
-/
def finiteModelLawEquationSkeleton :
    SourceSectionFreeSkeleton
      (semanticSite := finiteModelSemanticRepairSite)
      (S := AAT.AG.FiniteModel.site)
      (regime :=
        lawEquationRegime finiteModelAtomLawCoverGeometry
          finiteModelLawEquationGeometry)
      (C :=
        lawEquationStandardComplex finiteModelAtomLawCoverGeometry
          finiteModelLawEquationGeometry)
      (Ob := finiteModelLawEquationGeometry.lawEquationObstructionSheaf)
      (K :=
        lawEquationCechComplex finiteModelAtomLawCoverGeometry
          finiteModelLawEquationGeometry) where
  c0Order := []
  c1Order := []
  atom := fun _ => AAT.AG.FiniteModel.FiniteAtom.componentA
  atom_traceVisible := fun _ => rfl
  lawIndex := fun _ => PUnit.unit
  law_required := fun _ =>
    (AAT.AG.FiniteModel.site.equationSystem.toLegacyLawUniverse_required_iff
      PUnit.unit).mpr
      (AAT.AG.FiniteModel.site_equation_required PUnit.unit)

/--
The concrete law-equation defect source on the finite model: singleton local
inputs, the trace-visible atom and required-law supports, the relation-free
lawful object as the displayed reading, and the lawful defect observable `2`
(a violation coordinate of the realized NoCycle equation).
-/
def finiteModelLawEquationDefectSource :
    LawEquationDefectSemanticAtomLawInputBoundarySource
      finiteModelAtomLawCoverGeometry finiteModelLawEquationGeometry
      finiteModelLawEquationSkeleton where
  LocalInput := fun _ => PUnit
  input := fun _ => PUnit.unit
  atomSupport := fun _ _ => [AAT.AG.FiniteModel.FiniteAtom.componentA]
  atomSupport_traceVisible := fun _ _ =>
    ⟨AAT.AG.FiniteModel.FiniteAtom.componentA,
      List.mem_singleton_self _, rfl⟩
  lawSupport := fun _ _ => [PUnit.unit]
  lawSupport_nonempty := fun _ _ => ⟨PUnit.unit, List.mem_singleton_self _⟩
  lawSupport_required := fun _ _ lawIndex _ => by
    exact AAT.AG.FiniteModel.site_equation_required lawIndex
  objectOfLocalInput := fun _ _ => finiteModelLawfulObject
  defect := fun _ _ => 2
  holds_defect_mem := fun _ _ _ _ _ =>
    Ideal.subset_span ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩

/--
Displayed required-law fulfillment holds on the finite-model defect source:
every displayed law is the required NoCycle law and the displayed reading is
the relation-free lawful object.
-/
theorem finiteModelLawEquationDefectSource_displayedRequiredLawsHoldOn :
    finiteModelLawEquationDefectSource.DisplayedRequiredEquationsHoldOn := by
  intro _i equationIndex _hmem _hrequired
  cases equationIndex
  exact
    (AAT.AG.FiniteModel.site_equationHolds_iff_noCycle
      finiteModelLawfulObject).mpr
      noCycle_holds_finiteModelLawfulObject

/-- The singleton semantic repair cover over the finite-model semantic site. -/
def finiteModelSemanticCover :
    SemanticRepairCover.{0, 0, 0} finiteModelSemanticRepairSite where
  CoverChart := PUnit
  chart := fun _ => PUnit.unit
  chartOrder := [PUnit.unit]
  chart_complete := fun chart => by
    cases chart
    exact List.mem_singleton_self _
  Overlap := fun _ _ => PUnit
  overlapOrder := [Sigma.mk (PUnit.unit, PUnit.unit) PUnit.unit]
  overlap_complete := fun left right overlap => by
    cases left
    cases right
    cases overlap
    exact List.mem_singleton_self _
  TripleOverlap := fun _ _ _ => PUnit
  tripleEdge01 := fun _ => PUnit.unit
  tripleEdge12 := fun _ => PUnit.unit
  tripleEdge02 := fun _ => PUnit.unit
  tripleOrder := [Sigma.mk (PUnit.unit, PUnit.unit, PUnit.unit) PUnit.unit]
  triple_complete := fun i j k triple => by
    cases i
    cases j
    cases k
    cases triple
    exact List.mem_singleton_self _

/--
End-to-end instance theorem: the packet hypothesis class is inhabited and the
grounded comparison packet fires on the finite model.

The theorem instantiates `lawEquation_constructs_groundedComparisonPacket` on
the concrete bundle and re-exposes the headline conjuncts: the displayed
required-law restriction evaluator, the generated-Cech `sourceC0CechZero`, the
gate realization layer, the comparison package, and the additive `H1` zero
reading of the generated envelope.
-/
theorem finiteModel_lawEquation_endToEnd_packet_fires :
    let D := finiteModelLawEquationDefectSource
    let surface :=
      lawEquationCurrentG06InputSurface finiteModelAtomLawCoverGeometry
        finiteModelLawEquationGeometry finiteModelSemanticCover
        (fun _ => fun _ => PUnit.unit)
        (fun _ => fun _ => PUnit.unit)
        (fun _ => fun _ => PUnit.unit)
    let source := D.toCoverRelativeBaseRestrictionSource
    let restrictionSource :=
      source.toRestrictionRealizedBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let boundarySource :=
      restrictionSource.toBoundaryPrimitiveFreeSemanticAtomLawInputBoundarySource
    let freeSource := boundarySource.toFreeSemanticAtomLawInputBoundarySource
    let geometry :=
      CoverRelativeCechSemanticAtomLawInputBoundaryGeometry.ofFreeSemanticAtomLawInputBoundarySource
        freeSource
    let boundary :=
      geometry.toBoundaryGeneratedCoefficient
        (K := surface.K) source.c0Order source.c1Order
    let generated := boundary.toGeneratedCoefficient
    let canonical :=
      CoverRelativeCechGeneratedCanonicalH1Envelope.defaultObservationEnvelope
        (site := finiteModelSemanticRepairSite) generated
    let envelope := canonical.toGeneratedEnvelope
    let realization := envelope.toCochainRealization
    D.toSupportOnlySemanticAtomLawInputBoundarySource.displayedRequiredLawRestrictionEvaluator
        D.objectOfLocalInput /\
      atomLawOverlap_sourceSectionFreeSkeleton_sourceC0CechZero
        finiteModelAtomLawCoverGeometry
        finiteModelLawEquationGeometry.toSemanticAtomLawAdditiveCoefficientGeometry
        finiteModelLawEquationSkeleton
        D.toSupportOnlySemanticAtomLawInputBoundarySource /\
      Nonempty
        (SelectedSemanticCoefficientDirectRealizationLayer
          (E := envelope.toEnvelope)
          (additive := envelope.toAdditiveCechH1Data) surface) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      SemanticRepairAdditiveH1Zero envelope.toAdditiveCechH1Data := by
  dsimp
  have hpacket :=
    LawEquationDefectSemanticAtomLawInputBoundarySource.lawEquation_constructs_groundedComparisonPacket
      finiteModelLawEquationDefectSource finiteModelSemanticCover
      (fun _ => fun _ => PUnit.unit)
      (fun _ => fun _ => PUnit.unit)
      (fun _ => fun _ => PUnit.unit)
      finiteModelLawEquationDefectSource_displayedRequiredLawsHoldOn
  rcases hpacket with
    ⟨_hrealizes, hevaluator, hcechZero, hlayer, _hface, _hrealization,
      hcomparison, _hboundary, _hsemanticH1, hadditiveH1⟩
  exact ⟨hevaluator, hcechZero, hlayer, hcomparison, hadditiveH1⟩

end CoverRelativeCechFinitePosetChartProjectionPointwiseAtomLawInputBoundaryBasis
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
