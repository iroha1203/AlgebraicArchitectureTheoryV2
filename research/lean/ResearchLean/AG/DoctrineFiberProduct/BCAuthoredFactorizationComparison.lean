import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate
import ResearchLean.AG.TransportCoherence.VanishingCoherence

/-!
# The authored Beck--Chevalley comparison by universal factorization

This module constructs the authored-support comparison without composing an
endomorphism with the already assembled canonical mate.  For each authored
cell, the existing G-106 initial raw defect is first realized as a vertical
map of its southwest support package.  Reindexing sends that map to the
northwest fiber.  The package-specific cocartesian universal property then
generates a new left-leg counit factor from its defining total-morphism
equation.  The Beck--Chevalley component is assembled from the generated
right-leg unit, the producer-derived square comparison, and this independently
generated factor.

No comparison, mate, expected equality, raw defect, or factorization
certificate is accepted from a caller.  In particular the definition below
does not mention `authoredSupportCanonicalMate`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

/-! ## The G-106 defect as a southwest-fiber morphism -/

/-- The total map underlying the existing G-106 initial raw defect. -/
noncomputable def authoredInitialRawDefectTotal
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.hom
    (initialRawDefectCochain input.toTransportData cell)

/-- The initial raw defect lies over the southwest identity. -/
theorem authoredInitialRawDefectTotal_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (authoredInitialRawDefectTotal input cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (authoredInitialRawDefectTotal input cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, authoredInitialRawDefectTotal,
    PackageFiberAut.hom_base_eq]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- The initial raw defect as a vertical southwest-fiber morphism. -/
noncomputable def authoredInitialRawDefectComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨authoredInitialRawDefectTotal input cell,
    authoredInitialRawDefectTotal_isHomLift input cell⟩

/-- The same defect component retagged at the exact decoded southwest fiber. -/
noncomputable def authoredInitialRawDefectDecodedComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredSupportDecodedObject input.context (Discrete.mk cell) ⟶
      authoredSupportDecodedObject input.context (Discrete.mk cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact authoredInitialRawDefectComponent
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
      twoCellBase, authored⟩ cell

/-! ## A new counit factor generated from the authored path equation -/

/--
Generate the left-leg factor by the cocartesian universal property.  Its input
to the universal map is the reindexed G-106 defect, not a completed BC
comparison.
-/
noncomputable def authoredLeftFactor
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcLeftPresentation input.context.square.presentation))).obj
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).obj
          (authoredSupportDecodedObject input.context (Discrete.mk cell))) ⟶
      authoredSupportDecodedObject input.context (Discrete.mk cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  let leftInput := typedRealizableHom (bcLeftPresentation presentation)
  let support := normalizedContext.supportObject cell
  exact reindexToCoreTransportHom leftInput
    ((selectedCoreFiberReindexFunctor leftInput).obj support)
    support
    ((selectedCoreFiberReindexFunctor leftInput).map
      (authoredInitialRawDefectComponent normalizedInput cell))

/--
The generated factor is characterized before any Beck--Chevalley mate is
assembled: the canonical left lift followed by the new factor equals the
reindexed raw-defect map followed by the selected cartesian lift.
-/
theorem authoredLeftFactor_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    coreFiberLift
        (typedPresentationToSemantic
          (bcLeftPresentation input.context.square.presentation))
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).obj
          (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (authoredLeftFactor input cell).1 =
        (((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).map
          (authoredInitialRawDefectDecodedComponent input cell)).1 ≫
        (selectedCoreFiberCartesianLift
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))
          (authoredSupportDecodedObject input.context
            (Discrete.mk cell))).hom) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact reindexToCoreTransportHom_fac
    (typedRealizableHom (bcLeftPresentation presentation))
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).obj
      (AuthoredSupportContext.supportObject
        ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩ cell))
    (AuthoredSupportContext.supportObject
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩ cell)
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).map
      (authoredInitialRawDefectComponent
        ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
          twoCellBase, authored⟩ cell))

/-! ## Identity specialization of the generated factor -/

/-- Identity of the G-106 raw cochain gives the identity support component. -/
theorem authoredInitialRawDefectComponent_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredInitialRawDefectComponent input cell =
      𝟙 (input.context.supportObject cell) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  change PackageFiberAut.hom
      (initialRawDefectCochain input.toTransportData cell) =
    𝟙 (input.context.supportPackage cell)
  rw [congrFun hdefect cell]
  rfl

/-- Identity of the G-106 raw cochain gives the identity decoded component. -/
theorem authoredInitialRawDefectDecodedComponent_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredInitialRawDefectDecodedComponent input cell =
      𝟙 (authoredSupportDecodedObject input.context (Discrete.mk cell)) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  apply CategoryTheory.Functor.Fiber.hom_ext
  change PackageFiberAut.hom
      (initialRawDefectCochain
        (AuthoredBCDatumSquare.toTransportData
          ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
            lift, endpoint_eq⟩, twoCellBase, authored⟩) cell) =
    𝟙 (AuthoredSupportContext.supportPackage
      ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩ cell)
  rw [congrFun hdefect cell]
  rfl

/--
When the G-106 defect is identity, uniqueness identifies the newly generated
factor with the producer-derived left counit.
-/
theorem authoredLeftFactor_eq_counit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredLeftFactor input cell =
      (bcLeftAdjunction input.context.square.presentation).counit.app
        (authoredSupportDecodedObject input.context (Discrete.mk cell)) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let leftInput := typedRealizableHom
    (bcLeftPresentation input.context.square.presentation)
  let support := authoredSupportDecodedObject input.context (Discrete.mk cell)
  let reindexed := (selectedCoreFiberReindexFunctor leftInput).obj support
  letI : (packageProjection U).IsStronglyCocartesian
      leftInput.semantic.hom (coreFiberLift leftInput.semantic.hom reindexed) :=
    coreFiberLift_isStronglyCocartesian leftInput.semantic.hom reindexed
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) leftInput.semantic.hom
    (coreFiberLift leftInput.semantic.hom reindexed)
    (𝟙 leftInput.semantic.target)
  change coreFiberLift leftInput.semantic.hom reindexed ≫
      (authoredLeftFactor input cell).1 =
    coreFiberLift leftInput.semantic.hom reindexed ≫
      ((bcLeftAdjunction input.context.square.presentation).counit.app support).1
  dsimp only [leftInput, reindexed, support]
  change coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (authoredLeftFactor input cell).1 =
    coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      ((bcLeftAdjunction input.context.square.presentation).counit.app
        (authoredSupportDecodedObject input.context (Discrete.mk cell))).1
  rw [authoredLeftFactor_fac]
  rw [show (bcLeftAdjunction input.context.square.presentation).counit =
      coreTransportReindexCounit leftInput by rfl]
  rw [authoredInitialRawDefectDecodedComponent_eq_id input hdefect cell]
  rw [show
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom
        (bcLeftPresentation input.context.square.presentation))).map
        (𝟙 (authoredSupportDecodedObject input.context (Discrete.mk cell))) =
      𝟙 ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) by
    exact CategoryTheory.Functor.map_id _ _]
  simpa only [Category.id_comp] using
    (coreTransportReindexCounit_app_fac leftInput support).symm

/--
Universal uniqueness exposes the exact route class of the generated factor:
it is the canonical counit followed by the initial raw-defect component.
-/
theorem authoredLeftFactor_eq_counit_comp_rawDefect
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredLeftFactor input cell =
      (bcLeftAdjunction input.context.square.presentation).counit.app
          (authoredSupportDecodedObject input.context (Discrete.mk cell)) ≫
        authoredInitialRawDefectDecodedComponent input cell := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let leftInput := typedRealizableHom
    (bcLeftPresentation input.context.square.presentation)
  let support := authoredSupportDecodedObject input.context (Discrete.mk cell)
  let reindexed := (selectedCoreFiberReindexFunctor leftInput).obj support
  letI : (packageProjection U).IsStronglyCocartesian
      leftInput.semantic.hom (coreFiberLift leftInput.semantic.hom reindexed) :=
    coreFiberLift_isStronglyCocartesian leftInput.semantic.hom reindexed
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) leftInput.semantic.hom
    (coreFiberLift leftInput.semantic.hom reindexed)
    (𝟙 leftInput.semantic.target)
  dsimp only [leftInput, support, reindexed]
  change coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (authoredLeftFactor input cell).1 =
    coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (((bcLeftAdjunction input.context.square.presentation).counit.app
        (authoredSupportDecodedObject input.context (Discrete.mk cell))).1 ≫
        (authoredInitialRawDefectDecodedComponent input cell).1)
  rw [authoredLeftFactor_fac]
  rw [← Category.assoc]
  rw [show (bcLeftAdjunction input.context.square.presentation).counit =
      coreTransportReindexCounit
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation)) by rfl]
  have hcounit :
      coreFiberLift
          (typedPresentationToSemantic
            (bcLeftPresentation input.context.square.presentation))
          ((selectedCoreFiberReindexFunctor
            (typedRealizableHom
              (bcLeftPresentation input.context.square.presentation))).obj
            (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
        ((coreTransportReindexCounit
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).app
          (authoredSupportDecodedObject input.context (Discrete.mk cell))).1 =
        (selectedCoreFiberCartesianLift
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))
          (authoredSupportDecodedObject input.context (Discrete.mk cell))).hom := by
    exact coreTransportReindexCounit_app_fac
      (typedRealizableHom
        (bcLeftPresentation input.context.square.presentation))
      (authoredSupportDecodedObject input.context (Discrete.mk cell))
  rw [hcounit]
  exact selectedCoreFiberReindexFunctor_map_fac
    (typedRealizableHom
      (bcLeftPresentation input.context.square.presentation))
    (authoredInitialRawDefectDecodedComponent input cell)

/-! ## Componentwise Beck--Chevalley factorization -/

/--
The authored comparison component assembled from the generated right unit,
the producer-derived covariant square comparison, and `authoredLeftFactor`.
The canonical mate is not an ingredient of this definition.
-/
noncomputable def authoredFactorizationComparisonComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    (authoredSupportDirectRoute input.context).obj cell ⟶
      (authoredSupportViaBaseRoute input.context).obj cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  let support := normalizedContext.supportObject cell.as
  let leftReindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).obj support
  exact
    (bcRightAdjunction presentation).unit.app
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic
            (bcTopPresentation presentation))).obj leftReindexed) ≫
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation))).map
          ((bcCoreTransportSquareIso presentation).hom.app leftReindexed) ≫
      (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            (authoredLeftFactor normalizedInput cell.as))

/-- The via-base image of the same raw defect, retagged at the exact route. -/
noncomputable def authoredViaBaseRawDefectComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    (authoredSupportViaBaseRoute input.context).obj cell ⟶
      (authoredSupportViaBaseRoute input.context).obj cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  exact
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredInitialRawDefectComponent normalizedInput cell.as))

/--
The complete universal-factorization component collapses to the canonical mate
followed by the via-base image of the raw defect.  This theorem is the decisive
anti-wrapper audit for the attempted route.
-/
theorem authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    authoredFactorizationComparisonComponent input cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseRawDefectComponent input cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  let support := normalizedContext.supportObject cell.as
  let leftReindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).obj support
  let raw := authoredInitialRawDefectComponent normalizedInput cell.as
  change
    (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj leftReindexed) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((bcCoreTransportSquareIso presentation).hom.app leftReindexed) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              (authoredLeftFactor normalizedInput cell.as)) =
      (coreBeckChevalleyMate presentation).app support ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map raw)
  rw [authoredLeftFactor_eq_counit_comp_rawDefect normalizedInput cell.as]
  rw [CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.Functor.map_comp]
  rw [coreBeckChevalleyMate_app]
  simp only [Category.assoc]
  rfl

/-- The componentwise universal construction gives the required natural family. -/
noncomputable def authoredFactorizationComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredComparisonOfComponents
    (fun cell => authoredFactorizationComparisonComponent input cell)

/-- The generated component specializes to the canonical mate at identity defect. -/
theorem authoredFactorizationComparisonComponent_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredFactorizationComparisonComponent input cell =
      (authoredSupportCanonicalMate input.context).app cell := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedContext : AuthoredSupportContext U :=
    ⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨normalizedContext, twoCellBase, authored⟩
  let support := normalizedContext.supportObject cell.as
  let leftReindexed :=
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcLeftPresentation presentation))).obj support
  change
    (bcRightAdjunction presentation).unit.app
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation presentation))).obj leftReindexed) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((bcCoreTransportSquareIso presentation).hom.app leftReindexed) ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic
                (bcBottomPresentation presentation))).map
              (authoredLeftFactor normalizedInput cell.as)) =
      (coreBeckChevalleyMate presentation).app support
  rw [authoredLeftFactor_eq_counit
    normalizedInput hdefect cell.as]
  exact (coreBeckChevalleyMate_app presentation support).symm

/-- Identity G-106 defect makes the complete generated family canonical. -/
theorem authoredFactorizationComparison_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    authoredFactorizationComparison input =
      authoredSupportCanonicalMate input.context := by
  apply CategoryTheory.NatTrans.ext
  apply funext
  intro cell
  exact authoredFactorizationComparisonComponent_eq_canonical
    input hdefect cell

/--
The equality relation for the attempted universal-factorization producer.
This is deliberately not the public K2 `MateCoherentRel`: the anti-wrapper
normalization above rejects this producer for that role.
-/
def AttemptedFactorizationMateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  mateCoherentRelEquation authoredFactorizationComparison
    (authoredSupportCanonicalMateFamily U)

/-- Coherent G-106 initial data fires the attempted factorization relation. -/
theorem attemptedFactorizationMateCoherentRel_of_initialRawDefect_eq_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    AttemptedFactorizationMateCoherentRel U input := by
  exact authoredFactorizationComparison_eq_canonical input hdefect

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
