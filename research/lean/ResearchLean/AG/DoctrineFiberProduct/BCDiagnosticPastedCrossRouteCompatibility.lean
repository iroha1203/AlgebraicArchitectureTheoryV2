import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastedIsoSquare
import ResearchLean.AG.DoctrineFiberProduct.BCPastingCoherenceRoutes

/-!
# Pasted diagnostic cross-route compatibility

This module exposes the successive component functors and couples the split
mate square to their generated diagnostic action.  In the horizontal case the
actual three-arrow G-106/G-109 route equality is postcomposed with the
component comparison and a reselected diagnostic path, so the package-level
coherence is proof-used by a pasted diagnostic equation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 2000000

/-! ## Horizontal successive actions -/

noncomputable def horizontalComponentLeftReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation pasting.leftPresentation))

noncomputable def horizontalComponentTopLeftFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcTopPresentation pasting.leftPresentation))

noncomputable def horizontalComponentTopRightFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcTopPresentation pasting.rightPresentation))

noncomputable def horizontalComponentBottomLeftFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcBottomPresentation pasting.leftPresentation))

noncomputable def horizontalComponentBottomRightFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcBottomPresentation pasting.rightPresentation))

noncomputable def horizontalComponentRightReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (bcPastingNormalizedProvenance
      (.horizontal pasting)).rightProvenance.toRealizableHom

/-- The horizontal component-direct diagnostic datum is the genuine
three-stage successive action. -/
theorem horizontalComponentDirect_map_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic) :
    data.map (horizontalPastedComponentDirectFunctor pasting) =
      ((data.map (horizontalComponentLeftReindexFunctor pasting)).map
        (horizontalComponentTopLeftFunctor pasting)).map
          (horizontalComponentTopRightFunctor pasting) := by
  unfold horizontalPastedComponentDirectFunctor
  unfold horizontalComponentLeftReindexFunctor
    horizontalComponentTopLeftFunctor horizontalComponentTopRightFunctor
  rw [fiberwiseAdmissibleTransportData_map_comp,
    fiberwiseAdmissibleTransportData_map_comp]

/-- The horizontal component-via diagnostic datum is the genuine three-stage
successive action. -/
theorem horizontalComponentVia_map_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic) :
    data.map (horizontalPastedComponentViaFunctor pasting) =
      ((data.map (horizontalComponentBottomLeftFunctor pasting)).map
        (horizontalComponentBottomRightFunctor pasting)).map
          (horizontalComponentRightReindexFunctor pasting) := by
  unfold horizontalPastedComponentViaFunctor
  unfold horizontalComponentBottomLeftFunctor
    horizontalComponentBottomRightFunctor horizontalComponentRightReindexFunctor
  rw [fiberwiseAdmissibleTransportData_map_comp,
    fiberwiseAdmissibleTransportData_map_comp]

theorem horizontalComponentDirect_reselection_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    mapEdgeReselection data (horizontalPastedComponentDirectFunctor pasting)
        reselection =
      mapEdgeReselection
        ((data.map (horizontalComponentLeftReindexFunctor pasting)).map
          (horizontalComponentTopLeftFunctor pasting))
        (horizontalComponentTopRightFunctor pasting)
        (mapEdgeReselection
          (data.map (horizontalComponentLeftReindexFunctor pasting))
          (horizontalComponentTopLeftFunctor pasting)
          (mapEdgeReselection data
            (horizontalComponentLeftReindexFunctor pasting) reselection)) := by
  funext i j edge
  change coreFiberFunctorPackageAutHom
      (horizontalPastedComponentDirectFunctor pasting) (data.package j)
        (reselection i j edge) = _
  unfold horizontalPastedComponentDirectFunctor
  rw [coreFiberFunctorPackageAutHom_comp,
    coreFiberFunctorPackageAutHom_comp]
  rfl

theorem horizontalComponentVia_reselection_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    mapEdgeReselection data (horizontalPastedComponentViaFunctor pasting)
        reselection =
      mapEdgeReselection
        ((data.map (horizontalComponentBottomLeftFunctor pasting)).map
          (horizontalComponentBottomRightFunctor pasting))
        (horizontalComponentRightReindexFunctor pasting)
        (mapEdgeReselection
          (data.map (horizontalComponentBottomLeftFunctor pasting))
          (horizontalComponentBottomRightFunctor pasting)
          (mapEdgeReselection data
            (horizontalComponentBottomLeftFunctor pasting) reselection)) := by
  funext i j edge
  change coreFiberFunctorPackageAutHom
      (horizontalPastedComponentViaFunctor pasting) (data.package j)
        (reselection i j edge) = _
  unfold horizontalPastedComponentViaFunctor
  rw [coreFiberFunctorPackageAutHom_comp,
    coreFiberFunctorPackageAutHom_comp]
  rfl

/-! ## Horizontal G-106 proof-used diagnostic path -/

/-- The actual horizontal source alignment is the G-106-justified three-arrow
compositor route followed by the generated northwest reindex alignment. -/
theorem horizontalDataMateSourceAlignment_app_eq_g106Route
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (P : CoreFiber
      pasting.pastePresentation.1.cospan.firstSource.toSemantic) :
    let sigma := pasting.pasteNorthwestIso.inv
    let tau := typedPresentationToSemantic
      (bcTopPresentation pasting.leftPresentation)
    let upsilon := typedPresentationToSemantic
      (bcTopPresentation pasting.rightPresentation)
    let package :=
      (selectedCoreFiberReindexFunctor
        (bcPastingNormalizedProvenance
          (.horizontal pasting)).leftProvenance.toRealizableHom).obj P
    let northwestAlignment :=
      horizontalDataNormalizedNorthwestReindexAlignment pasting
    coreFiberAssociatorCast sigma tau upsilon package ≫
        (horizontalDataMateSourceAlignment pasting).app P =
      coreFiberPentagonLeftRoute sigma tau upsilon package ≫
        (coreFiberTransportFunctor tau ⋙
          coreFiberTransportFunctor upsilon).map
            (northwestAlignment.app P) := by
  dsimp only
  calc
    _ = coreFiberPentagonRightRoute pasting.pasteNorthwestIso.inv
          (typedPresentationToSemantic
            (bcTopPresentation pasting.leftPresentation))
          (typedPresentationToSemantic
            (bcTopPresentation pasting.rightPresentation))
          ((selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.horizontal pasting)).leftProvenance.toRealizableHom).obj P) ≫
        (coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation pasting.leftPresentation)) ⋙
          coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation pasting.rightPresentation))).map
          ((horizontalDataNormalizedNorthwestReindexAlignment pasting).app P) := by
      have hnat := coreFiberCompositor_naturality
        (typedPresentationToSemantic
          (bcTopPresentation pasting.leftPresentation))
        (typedPresentationToSemantic
          (bcTopPresentation pasting.rightPresentation))
        ((horizontalDataNormalizedNorthwestReindexAlignment pasting).app P)
      have hpref := congrArg
        (fun q =>
          (coreFiberAssociatorCast pasting.pasteNorthwestIso.inv
              (typedPresentationToSemantic
                (bcTopPresentation pasting.leftPresentation))
              (typedPresentationToSemantic
                (bcTopPresentation pasting.rightPresentation))
              ((selectedCoreFiberReindexFunctor
                (bcPastingNormalizedProvenance
                  (.horizontal pasting)).leftProvenance.toRealizableHom).obj P) ≫
            (coreFiberCompositorApp pasting.pasteNorthwestIso.inv
              (typedPresentationToSemantic
                  (bcTopPresentation pasting.leftPresentation) ≫
                typedPresentationToSemantic
                  (bcTopPresentation pasting.rightPresentation))
              ((selectedCoreFiberReindexFunctor
                (bcPastingNormalizedProvenance
                  (.horizontal pasting)).leftProvenance.toRealizableHom).obj P)).hom) ≫ q)
        hnat
      simpa [horizontalDataMateSourceAlignment,
        horizontalDataNormalizedTopCompositor,
        horizontalBCPastingNormalizedTopCompositor,
        coreFiberPentagonRightRoute, coreFiberAssociatorCast,
        coreFiberCompositor, Category.assoc] using hpref
    _ = _ := by
      exact congrArg
        (fun route => route ≫
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation pasting.leftPresentation)) ⋙
            coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcTopPresentation pasting.rightPresentation))).map
            ((horizontalDataNormalizedNorthwestReindexAlignment pasting).app P))
        (coreFiberCompositor_assoc_via_g106
          pasting.pasteNorthwestIso.inv
          (typedPresentationToSemantic
            (bcTopPresentation pasting.leftPresentation))
          (typedPresentationToSemantic
            (bcTopPresentation pasting.rightPresentation))
          ((selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.horizontal pasting)).leftProvenance.toRealizableHom).obj P)).symm

/-- G-106 normal form of the actual horizontal four-side package square. -/
def HorizontalPastedPackageSquareViaG106
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation)
    (vertex : (toSemanticBC pasting.pastePresentation).diagnostic.Vertex) : Prop :=
    let data := incidence.toFiberwise
    let sigma := pasting.pasteNorthwestIso.inv
    let tau := typedPresentationToSemantic
      (bcTopPresentation pasting.leftPresentation)
    let upsilon := typedPresentationToSemantic
      (bcTopPresentation pasting.rightPresentation)
    let package :=
      (selectedCoreFiberReindexFunctor
        (bcPastingNormalizedProvenance
          (.horizontal pasting)).leftProvenance.toRealizableHom).obj
        (data.package vertex)
    let northwestAlignment :=
      horizontalDataNormalizedNorthwestReindexAlignment pasting
    coreFiberPentagonLeftRoute sigma tau upsilon package ≫
        (coreFiberTransportFunctor tau ⋙
          coreFiberTransportFunctor upsilon).map
            (northwestAlignment.app (data.package vertex)) ≫
        (horizontalLiteralComponentMate pasting).app
          (data.package vertex) =
      coreFiberAssociatorCast sigma tau upsilon package ≫
        (bcProvenanceCanonicalMate
          (bcPastingNormalizedProvenance (.horizontal pasting))).app
          (data.package vertex) ≫
        (horizontalOuterMateTargetAlignment pasting).app
          (data.package vertex)

/-- The G-106 source-alignment normal form is consumed in the same package
equation as the outer mate and target alignment. -/
theorem horizontalPastedPackageSquare_via_g106
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation)
    (vertex : (toSemanticBC pasting.pastePresentation).diagnostic.Vertex) :
    HorizontalPastedPackageSquareViaG106 pasting interpretation incidence
      vertex := by
  unfold HorizontalPastedPackageSquareViaG106
  dsimp only
  slice_lhs 1 2 =>
    rw [← horizontalDataMateSourceAlignment_app_eq_g106Route]
  slice_lhs 2 3 =>
    change (horizontalDataMateSourceAlignment pasting ≫
      horizontalLiteralComponentMate pasting).app
        (incidence.toFiberwise.package vertex)
    unfold horizontalLiteralComponentMate
    rw [horizontalLiteralComponentMates_eq_outerCanonicalMate]
  simp only [NatTrans.comp_app]

/-! ## Vertical successive actions -/

noncomputable def verticalComponentLeftLowerReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation pasting.lowerPresentation))

noncomputable def verticalComponentLeftUpperReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcLeftPresentation pasting.upperPresentation))

noncomputable def verticalComponentTopFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcTopPresentation pasting.upperPresentation))

noncomputable def verticalComponentBottomFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  coreFiberTransportFunctor
    (typedPresentationToSemantic
      (bcBottomPresentation pasting.lowerPresentation))

noncomputable def verticalComponentRightLowerReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcRightPresentation pasting.lowerPresentation))

noncomputable def verticalComponentRightUpperReindexFunctor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :=
  selectedCoreFiberReindexFunctor
    (typedRealizableHom (bcRightPresentation pasting.upperPresentation))

theorem verticalComponentDirect_map_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic) :
    data.map (verticalPastedComponentDirectFunctor pasting) =
      ((data.map (verticalComponentLeftLowerReindexFunctor pasting)).map
        (verticalComponentLeftUpperReindexFunctor pasting)).map
          (verticalComponentTopFunctor pasting) := by
  unfold verticalPastedComponentDirectFunctor
  unfold verticalComponentLeftLowerReindexFunctor
    verticalComponentLeftUpperReindexFunctor verticalComponentTopFunctor
  rw [fiberwiseAdmissibleTransportData_map_comp,
    fiberwiseAdmissibleTransportData_map_comp]

theorem verticalComponentVia_map_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic) :
    data.map (verticalPastedComponentViaFunctor pasting) =
      ((data.map (verticalComponentBottomFunctor pasting)).map
        (verticalComponentRightLowerReindexFunctor pasting)).map
          (verticalComponentRightUpperReindexFunctor pasting) := by
  unfold verticalPastedComponentViaFunctor
  unfold verticalComponentBottomFunctor verticalComponentRightLowerReindexFunctor
    verticalComponentRightUpperReindexFunctor
  rw [fiberwiseAdmissibleTransportData_map_comp,
    fiberwiseAdmissibleTransportData_map_comp]

theorem verticalComponentDirect_reselection_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    mapEdgeReselection data (verticalPastedComponentDirectFunctor pasting)
        reselection =
      mapEdgeReselection
        ((data.map (verticalComponentLeftLowerReindexFunctor pasting)).map
          (verticalComponentLeftUpperReindexFunctor pasting))
        (verticalComponentTopFunctor pasting)
        (mapEdgeReselection
          (data.map (verticalComponentLeftLowerReindexFunctor pasting))
          (verticalComponentLeftUpperReindexFunctor pasting)
          (mapEdgeReselection data
            (verticalComponentLeftLowerReindexFunctor pasting) reselection)) := by
  funext i j edge
  change coreFiberFunctorPackageAutHom
      (verticalPastedComponentDirectFunctor pasting) (data.package j)
        (reselection i j edge) = _
  unfold verticalPastedComponentDirectFunctor
  rw [coreFiberFunctorPackageAutHom_comp,
    coreFiberFunctorPackageAutHom_comp]
  rfl

theorem verticalComponentVia_reselection_eq_successive
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    {G : FiniteTransportPresentation.{u}}
    (data : FiberwiseAdmissibleTransportData G U
      pasting.pastePresentation.1.cospan.firstSource.toSemantic)
    (reselection : EdgeReselection data.toLiftData) :
    mapEdgeReselection data (verticalPastedComponentViaFunctor pasting)
        reselection =
      mapEdgeReselection
        ((data.map (verticalComponentBottomFunctor pasting)).map
          (verticalComponentRightLowerReindexFunctor pasting))
        (verticalComponentRightUpperReindexFunctor pasting)
        (mapEdgeReselection
          (data.map (verticalComponentBottomFunctor pasting))
          (verticalComponentRightLowerReindexFunctor pasting)
          (mapEdgeReselection data
            (verticalComponentBottomFunctor pasting) reselection)) := by
  funext i j edge
  change coreFiberFunctorPackageAutHom
      (verticalPastedComponentViaFunctor pasting) (data.package j)
        (reselection i j edge) = _
  unfold verticalPastedComponentViaFunctor
  rw [coreFiberFunctorPackageAutHom_comp,
    coreFiberFunctorPackageAutHom_comp]
  rfl

/-- The pullback-side target alignment written directly with the selected
reindex compositor constructed in G-110. -/
noncomputable def verticalSelectedCompositorTargetAlignment
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :
    verticalPastedOuterViaFunctor pasting ⟶
      verticalPastedComponentViaFunctor pasting :=
  Functor.whiskerRight
          (coreFiberTransportEqIso (verticalNormalizedBottom_eq pasting)).hom
          (selectedCoreFiberReindexFunctor
            (bcPastingNormalizedProvenance
              (.vertical pasting)).rightProvenance.toRealizableHom) ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation pasting.lowerPresentation)))
          (selectedCoreFiberReindexCompositor
            (bcRightPresentation pasting.upperPresentation)
            (bcRightPresentation pasting.lowerPresentation)).inv

/-- The pullback-side target alignment is generated by the selected reindex
compositor, with its required inverse orientation. -/
theorem verticalMateTargetAlignmentIso_hom_eq_selectedCompositor_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U) :
    (verticalMateTargetAlignmentIso pasting).hom =
      verticalSelectedCompositorTargetAlignment pasting := by
  change verticalMateTargetAlignment pasting = _
  exact verticalMateTargetAlignment_eq_selectedCompositor_inv pasting

/-- Naturality of a complete reselected diagnostic path through the actual
pullback-side compositor alignment.  Rewriting the target alignment by the
preceding theorem is the proof-use of the compositor construction. -/
theorem verticalPastedDiagnosticTargetPath_via_selectedCompositor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation)
    (reselection : EdgeReselection
      (incidence.toFiberwise.map
        (verticalPastedOuterViaFunctor pasting)).toLiftData)
    {i j : (toSemanticBC pasting.pastePresentation).diagnostic.Vertex}
    (path : (toSemanticBC pasting.pastePresentation).diagnostic.Path i j) :
    fiberReselectedPath
          (incidence.toFiberwise.map (verticalPastedOuterViaFunctor pasting))
          reselection path ≫
        (verticalSelectedCompositorTargetAlignment pasting).app
          (incidence.toFiberwise.package j) =
      (verticalSelectedCompositorTargetAlignment pasting).app
          (incidence.toFiberwise.package i) ≫
        fiberReselectedPath
          (incidence.toFiberwise.map
            (verticalPastedComponentViaFunctor pasting))
          (transportEdgeReselectionAlongNaturalIso incidence.toFiberwise
            (verticalMateTargetAlignmentIso pasting) reselection) path := by
  rw [← verticalMateTargetAlignmentIso_hom_eq_selectedCompositor_inv]
  exact fiberReselectedPath_naturality_iso incidence.toFiberwise
    (verticalMateTargetAlignmentIso pasting) reselection path

/-! ## Direction-specific cross-route packages -/

structure HorizontalPastedBCDiagnosticCrossRouteCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) : Prop where
  outerRouteComposition :
    BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.horizontal pasting)).leftProvenance.toRealizableHom)
        (coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal pasting)).top) ∧
      BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.horizontal pasting)).bottom)
        (selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.horizontal pasting)).rightProvenance.toRealizableHom)
  isoSquare : FiberwiseDiagnosticNaturalIsoSquareCompatibility
    incidence.toFiberwise
    (horizontalDataMateSourceAlignmentIso pasting)
    (horizontalLiteralComponentMateIso pasting)
    (horizontalOuterCanonicalMateIso pasting)
    (horizontalOuterMateTargetAlignmentIso pasting)
  componentDirect_successive :
    incidence.toFiberwise.map (horizontalPastedComponentDirectFunctor pasting) =
      ((incidence.toFiberwise.map
        (horizontalComponentLeftReindexFunctor pasting)).map
        (horizontalComponentTopLeftFunctor pasting)).map
        (horizontalComponentTopRightFunctor pasting)
  componentVia_successive :
    incidence.toFiberwise.map (horizontalPastedComponentViaFunctor pasting) =
      ((incidence.toFiberwise.map
        (horizontalComponentBottomLeftFunctor pasting)).map
        (horizontalComponentBottomRightFunctor pasting)).map
        (horizontalComponentRightReindexFunctor pasting)
  componentDirect_reselection_successive : ∀ reselection,
    mapEdgeReselection incidence.toFiberwise
        (horizontalPastedComponentDirectFunctor pasting) reselection =
      mapEdgeReselection
        ((incidence.toFiberwise.map
          (horizontalComponentLeftReindexFunctor pasting)).map
          (horizontalComponentTopLeftFunctor pasting))
        (horizontalComponentTopRightFunctor pasting)
        (mapEdgeReselection
          (incidence.toFiberwise.map
            (horizontalComponentLeftReindexFunctor pasting))
          (horizontalComponentTopLeftFunctor pasting)
          (mapEdgeReselection incidence.toFiberwise
            (horizontalComponentLeftReindexFunctor pasting) reselection))
  componentVia_reselection_successive : ∀ reselection,
    mapEdgeReselection incidence.toFiberwise
        (horizontalPastedComponentViaFunctor pasting) reselection =
      mapEdgeReselection
        ((incidence.toFiberwise.map
          (horizontalComponentBottomLeftFunctor pasting)).map
          (horizontalComponentBottomRightFunctor pasting))
        (horizontalComponentRightReindexFunctor pasting)
        (mapEdgeReselection
          (incidence.toFiberwise.map
            (horizontalComponentBottomLeftFunctor pasting))
          (horizontalComponentBottomRightFunctor pasting)
          (mapEdgeReselection incidence.toFiberwise
            (horizontalComponentBottomLeftFunctor pasting) reselection))
  packageSquare_via_g106 : ∀ vertex,
    HorizontalPastedPackageSquareViaG106 pasting interpretation incidence vertex

noncomputable def horizontalPastedBCDiagnosticCrossRouteCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : HorizontalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :
    HorizontalPastedBCDiagnosticCrossRouteCompatibility
      pasting interpretation incidence where
  outerRouteComposition :=
    ⟨diagnosticCompositionCompatibility _ _ _,
      diagnosticCompositionCompatibility _ _ _⟩
  isoSquare := horizontalPastedBCDiagnosticIsoSquareCompatibility
    pasting interpretation incidence
  componentDirect_successive :=
    horizontalComponentDirect_map_eq_successive pasting incidence.toFiberwise
  componentVia_successive :=
    horizontalComponentVia_map_eq_successive pasting incidence.toFiberwise
  componentDirect_reselection_successive :=
    horizontalComponentDirect_reselection_eq_successive pasting incidence.toFiberwise
  componentVia_reselection_successive :=
    horizontalComponentVia_reselection_eq_successive pasting incidence.toFiberwise
  packageSquare_via_g106 :=
    horizontalPastedPackageSquare_via_g106 pasting interpretation incidence

structure VerticalPastedBCDiagnosticCrossRouteCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) : Prop where
  outerRouteComposition :
    BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.vertical pasting)).leftProvenance.toRealizableHom)
        (coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical pasting)).top) ∧
      BCDiagnosticCompositionCompatibility incidence.toFiberwise
        (coreFiberTransportFunctor
          (normalizedNestedPasteSquare (.vertical pasting)).bottom)
        (selectedCoreFiberReindexFunctor
          (bcPastingNormalizedProvenance
            (.vertical pasting)).rightProvenance.toRealizableHom)
  isoSquare : FiberwiseDiagnosticNaturalIsoSquareCompatibility
    incidence.toFiberwise
    (verticalMateSourceAlignmentIso pasting)
    (verticalLiteralComponentMateIso pasting)
    (verticalOuterCanonicalMateIso pasting)
    (verticalMateTargetAlignmentIso pasting)
  componentDirect_successive :
    incidence.toFiberwise.map (verticalPastedComponentDirectFunctor pasting) =
      ((incidence.toFiberwise.map
        (verticalComponentLeftLowerReindexFunctor pasting)).map
        (verticalComponentLeftUpperReindexFunctor pasting)).map
        (verticalComponentTopFunctor pasting)
  componentVia_successive :
    incidence.toFiberwise.map (verticalPastedComponentViaFunctor pasting) =
      ((incidence.toFiberwise.map
        (verticalComponentBottomFunctor pasting)).map
        (verticalComponentRightLowerReindexFunctor pasting)).map
        (verticalComponentRightUpperReindexFunctor pasting)
  componentDirect_reselection_successive : ∀ reselection,
    mapEdgeReselection incidence.toFiberwise
        (verticalPastedComponentDirectFunctor pasting) reselection =
      mapEdgeReselection
        ((incidence.toFiberwise.map
          (verticalComponentLeftLowerReindexFunctor pasting)).map
          (verticalComponentLeftUpperReindexFunctor pasting))
        (verticalComponentTopFunctor pasting)
        (mapEdgeReselection
          (incidence.toFiberwise.map
            (verticalComponentLeftLowerReindexFunctor pasting))
          (verticalComponentLeftUpperReindexFunctor pasting)
          (mapEdgeReselection incidence.toFiberwise
            (verticalComponentLeftLowerReindexFunctor pasting) reselection))
  componentVia_reselection_successive : ∀ reselection,
    mapEdgeReselection incidence.toFiberwise
        (verticalPastedComponentViaFunctor pasting) reselection =
      mapEdgeReselection
        ((incidence.toFiberwise.map
          (verticalComponentBottomFunctor pasting)).map
          (verticalComponentRightLowerReindexFunctor pasting))
        (verticalComponentRightUpperReindexFunctor pasting)
        (mapEdgeReselection
          (incidence.toFiberwise.map
            (verticalComponentBottomFunctor pasting))
          (verticalComponentRightLowerReindexFunctor pasting)
          (mapEdgeReselection incidence.toFiberwise
            (verticalComponentBottomFunctor pasting) reselection))
  targetAlignment_selectedCompositor :
    (verticalMateTargetAlignmentIso pasting).hom =
      verticalSelectedCompositorTargetAlignment pasting
  targetDiagnosticPath_selectedCompositor : ∀
    (reselection : EdgeReselection
      (incidence.toFiberwise.map
        (verticalPastedOuterViaFunctor pasting)).toLiftData)
    {i j : (toSemanticBC pasting.pastePresentation).diagnostic.Vertex}
    (path : (toSemanticBC pasting.pastePresentation).diagnostic.Path i j),
      fiberReselectedPath
            (incidence.toFiberwise.map (verticalPastedOuterViaFunctor pasting))
            reselection path ≫
          (verticalSelectedCompositorTargetAlignment pasting).app
            (incidence.toFiberwise.package j) =
        (verticalSelectedCompositorTargetAlignment pasting).app
            (incidence.toFiberwise.package i) ≫
          fiberReselectedPath
            (incidence.toFiberwise.map
              (verticalPastedComponentViaFunctor pasting))
            (transportEdgeReselectionAlongNaturalIso incidence.toFiberwise
              (verticalMateTargetAlignmentIso pasting) reselection) path

noncomputable def verticalPastedBCDiagnosticCrossRouteCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (pasting : VerticalBCPastingData U)
    (interpretation : BCDiagnosticInterpretation U
      (toSemanticBC pasting.pastePresentation))
    (incidence : BCDiagnosticSourceFiberIncidence
      pasting.pastePresentation interpretation) :
    VerticalPastedBCDiagnosticCrossRouteCompatibility
      pasting interpretation incidence where
  outerRouteComposition :=
    ⟨diagnosticCompositionCompatibility _ _ _,
      diagnosticCompositionCompatibility _ _ _⟩
  isoSquare := verticalPastedBCDiagnosticIsoSquareCompatibility
    pasting interpretation incidence
  componentDirect_successive :=
    verticalComponentDirect_map_eq_successive pasting incidence.toFiberwise
  componentVia_successive :=
    verticalComponentVia_map_eq_successive pasting incidence.toFiberwise
  componentDirect_reselection_successive :=
    verticalComponentDirect_reselection_eq_successive pasting incidence.toFiberwise
  componentVia_reselection_successive :=
    verticalComponentVia_reselection_eq_successive pasting incidence.toFiberwise
  targetAlignment_selectedCompositor :=
    verticalMateTargetAlignmentIso_hom_eq_selectedCompositor_inv pasting
  targetDiagnosticPath_selectedCompositor :=
    verticalPastedDiagnosticTargetPath_via_selectedCompositor
      pasting interpretation incidence

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
