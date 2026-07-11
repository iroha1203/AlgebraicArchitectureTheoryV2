# Part X Semantic Repair statement contract

定理7.5の有限性仮定を持たない経路について、入力と10結論の型を次で固定する。
2つのtarget theoremのsignatureは
`Formal/AG/StatementContractsSemanticRepairPart10.lean` を通常build surfaceから
elaborateして検査する。入力structureと10 fieldのsignatureは、実装との査読突合で固定する。

```lean
structure LawEquationSemanticAtomInputBody (U : AtomCarrier.{x}) where
  Component : Type v
  project : U.Atom -> Component
  sourceTraceToken : U.Atom -> Bool

structure LawEquationWitnessIdealGeometryBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (S : Site.AATSite.{x} Alaw) where
  toCore : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} S
  supportAtom_traceVisible :
    semanticInput.sourceTraceToken toCore.supportAtom = true
  quotientIsSheaf :
    Site.AATSheafCondition S toCore.obstructionQuotientPresheaf

structure FinitePosetLawEquationDefectSourceBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw) where
  LocalInput : geometry.cover.Index -> Type x
  input : (i : geometry.cover.Index) -> LocalInput i
  atomSupport :
    (i : geometry.cover.Index) -> LocalInput i -> List Ulaw.Atom
  atomSupport_traceVisible :
    forall (i : geometry.cover.Index) (localInput : LocalInput i),
      exists atom : Ulaw.Atom,
        atom ∈ atomSupport i localInput /\
          semanticInput.sourceTraceToken atom = true
  lawSupport :
    (i : geometry.cover.Index) -> LocalInput i -> List Slaw.lawUniverse.Index
  lawSupport_nonempty :
    forall i, exists lawIndex : Slaw.lawUniverse.Index,
      lawIndex ∈ lawSupport i (input i)
  lawSupport_required :
    forall i (lawIndex : Slaw.lawUniverse.Index),
      lawIndex ∈ lawSupport i (input i) -> Slaw.lawUniverse.Required lawIndex
  objectOfLocalInput :
    (i : geometry.cover.Index) -> LocalInput i -> ArchitectureObject Ulaw
  defect :
    (i : geometry.cover.Index) -> LocalInput i ->
      G.toCore.Observable
        (Site.ContextCategoryObject.of Slaw.contextPreorder
          (geometry.cover.patch i))
  holds_defect_mem :
    forall i (lawIndex : Slaw.lawUniverse.Index),
      lawIndex ∈ lawSupport i (input i) ->
        Slaw.lawUniverse.Required lawIndex ->
          (Slaw.lawUniverse.law lawIndex).holds
              (objectOfLocalInput i (input i)) ->
            defect i (input i) ∈
              G.toCore.lawWitnessIdeal
                (Site.ContextCategoryObject.of Slaw.contextPreorder
                  (geometry.cover.patch i)) lawIndex
```

10結論 packet は次の field 型を持つ。先頭3 field だけが
`DisplayedRequiredLawsHoldOn` に依存し、残る7 field は law 前提を受けない
補助定理で構成する。

```lean
structure LawEquationGroundedComparisonFiniteFreeConjunctsBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.toCore.obstructionQuotientPresheaf
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
    (source :
      LawEquationBodyCechSource D.toLawEquationDefectSource
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)) where
  displayedInterpretationRealization : source.DisplayedInterpretationRealization
  displayedRequiredLawRestrictionEvaluator :
    source.DisplayedRequiredLawRestrictionEvaluator
  sourceC0CechZero : source.SourceC0CechZero
  selectedRealizationLayer :
    Nonempty
      (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody D source surface
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive))
  degreewiseCarrierFaceEquations :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
      (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
  cochainRealization :
    Nonempty
      (SemanticRepairCoverRelativeCochainRealization
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive)
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
  h1ComparisonPackage :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.
        SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          (coverRelativeGeneratedBoundaryCochainRealization
            (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
              geometry.canonicalTupleCoverGeometryFromOverlap)
            source.toPrimitive).toH1Comparison)
  residualBoundary :
    GeneratedResidualBoundarySurfaceBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  semanticH1Zero :
    GeneratedSemanticH1ZeroBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  additiveH1Zero :
    (coverRelativeGeneratedBoundaryAdditiveH1Surface
      (lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
      source.toPrimitive).H1Zero
```

主定理と law 非依存補助定理の完全な signature は次で固定する。

```lean
theorem lawEquation_constructs_finiteFreeLawIndependentConjuncts
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    let additive := coverRelativeGeneratedBoundaryAdditiveH1Surface K source.toPrimitive
    let realization := coverRelativeGeneratedBoundaryCochainRealization K source.toPrimitive
    Nonempty (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
      D source surface additive) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K /\
      Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.
          SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
            realization.toH1Comparison) /\
      GeneratedResidualBoundarySurfaceBody additive /\
      GeneratedSemanticH1ZeroBody additive /\
      additive.H1Zero

theorem lawEquation_constructs_groundedComparisonPacket_finiteFree
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (G := G.toCore) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    let K := lawEquationCechComplex (G := G.toCore) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    Nonempty (LawEquationGroundedComparisonFiniteFreeConjunctsBody D surface source)
```
