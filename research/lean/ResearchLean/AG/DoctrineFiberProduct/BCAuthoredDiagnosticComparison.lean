import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPairwiseAxisFold

/-!
# The authored diagnostic Beck--Chevalley comparison

This module keeps the actual G-106 raw component at an arbitrary supplied
cochain coordinate and follows it by a diagnostic fold generated at that same
coordinate.  Fold selection is direct-first: a moved axis of the component is
used when available, then the same-boundary pairwise diagnostic is tried, and
identity is the final fallback.

No comparison, endomorphism, fold witness, expected equality, or
noninvertibility certificate is accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

namespace PackageFiberAut

/-- Direct-first availability of a diagnostic fold at one cochain component. -/
def UnifiedAxisFoldAvailableAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (cell : G.TwoCell) : Prop :=
  AxisFoldAvailable (cochain cell) ∨
    PairwiseAxisFoldAvailableAt data cochain cell

/--
Generate the direct component fold when possible, otherwise the same-boundary
pairwise fold, otherwise identity.
-/
noncomputable def generatedUnifiedAxisFoldTotalAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (cell : G.TwoCell) :
    PackageTotalHom (data.lift.package (G.twoTarget cell))
      (data.lift.package (G.twoTarget cell)) := by
  classical
  by_cases direct : AxisFoldAvailable (cochain cell)
  · exact generatedAxisFoldTotal (cochain cell)
  · by_cases pairwise : PairwiseAxisFoldAvailableAt data cochain cell
    · exact generatedPairwiseAxisFoldTotalAt data cochain cell
    · exact PackageTotalHom.id (data.lift.package (G.twoTarget cell))

/-- The unified fold always lies over identity. -/
theorem generatedUnifiedAxisFoldTotalAt_base
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (cell : G.TwoCell) :
    (generatedUnifiedAxisFoldTotalAt data cochain cell).base =
      ExtInstHom.id (packagePoint (data.lift.package (G.twoTarget cell))) := by
  classical
  rw [generatedUnifiedAxisFoldTotalAt]
  split_ifs
  · exact generatedAxisFoldTotal_base (cochain cell)
  · exact generatedPairwiseAxisFoldTotalAt_base data cochain cell
  · rfl

/-- Either available branch makes the selected unified fold noninvertible. -/
theorem generatedUnifiedAxisFoldTotalAt_not_isIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (cell : G.TwoCell)
    (available : UnifiedAxisFoldAvailableAt data cochain cell) :
    ¬ IsIso
      (show data.lift.package (G.twoTarget cell) ⟶
          data.lift.package (G.twoTarget cell) from
        generatedUnifiedAxisFoldTotalAt data cochain cell) := by
  classical
  rcases available with direct | pairwise
  · rw [generatedUnifiedAxisFoldTotalAt, dif_pos direct]
    exact generatedAxisFoldTotal_not_isIso (cochain cell) direct
  · by_cases direct : AxisFoldAvailable (cochain cell)
    · rw [generatedUnifiedAxisFoldTotalAt, dif_pos direct]
      exact generatedAxisFoldTotal_not_isIso (cochain cell) direct
    · rw [generatedUnifiedAxisFoldTotalAt, dif_neg direct, dif_pos pairwise]
      exact generatedPairwiseAxisFoldTotalAt_not_isIso
        data cochain cell pairwise

/-- Failure of both availability tests specializes the unified fold to identity. -/
theorem generatedUnifiedAxisFoldTotalAt_eq_id
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (cell : G.TwoCell)
    (unavailable : ¬ UnifiedAxisFoldAvailableAt data cochain cell) :
    generatedUnifiedAxisFoldTotalAt data cochain cell =
      PackageTotalHom.id (data.lift.package (G.twoTarget cell)) := by
  classical
  have direct : ¬ AxisFoldAvailable (cochain cell) :=
    fun h => unavailable (Or.inl h)
  have pairwise : ¬ PairwiseAxisFoldAvailableAt data cochain cell :=
    fun h => unavailable (Or.inr h)
  rw [generatedUnifiedAxisFoldTotalAt, dif_neg direct, dif_neg pairwise]

end PackageFiberAut

/-! ## The supplied raw cochain as a southwest-fiber morphism -/

/-- The total map underlying the supplied raw-cochain component. -/
noncomputable def authoredRawDefectTotalAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.hom (cochain cell)

/-- The supplied raw component lies over the southwest identity. -/
theorem authoredRawDefectTotalAtCochain_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (authoredRawDefectTotalAtCochain input cochain cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (authoredRawDefectTotalAtCochain input cochain cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, authoredRawDefectTotalAtCochain,
    PackageFiberAut.hom_base_eq]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- The supplied raw component in the southwest core fiber. -/
noncomputable def authoredRawDefectComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨authoredRawDefectTotalAtCochain input cochain cell,
    authoredRawDefectTotalAtCochain_isHomLift input cochain cell⟩

/-- The supplied raw southwest component is an isomorphism. -/
noncomputable def authoredRawDefectComponentIsoAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ≅ input.context.supportObject cell where
  hom := authoredRawDefectComponentAtCochain input cochain cell
  inv := ⟨PackageFiberAut.inv (cochain cell), by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U)
      (𝟙 input.context.square.semantic.square.southwest)
      (PackageFiberAut.inv (cochain cell))
      (input.context.endpoint_eq cell)
      (input.context.endpoint_eq cell)
    rw [packageProjection_map, PackageFiberAut.inv_base_eq]
    rw [Category.comp_id]
    exact Category.id_comp _⟩
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (cochain cell).1.hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (cochain cell).1.inv_hom_id

/-- The same raw component retagged at the exact decoded southwest object. -/
noncomputable def authoredRawDefectDecodedComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredSupportDecodedObject input.context (Discrete.mk cell) ⟶
      authoredSupportDecodedObject input.context (Discrete.mk cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact authoredRawDefectComponentAtCochain
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
      twoCellBase, authored⟩ cochain cell

/-- The decoded raw component retains the supplied cochain value. -/
theorem authoredRawDefectDecodedComponentAtCochain_val_heq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    HEq (authoredRawDefectDecodedComponentAtCochain input cochain cell).1
      (PackageFiberAut.hom (cochain cell)) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  rfl

/-- The decoded supplied raw component is an isomorphism. -/
theorem authoredRawDefectDecodedComponentAtCochain_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    IsIso (authoredRawDefectDecodedComponentAtCochain input cochain cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact (authoredRawDefectComponentIsoAtCochain
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
      twoCellBase, authored⟩ cochain cell).isIso_hom

/-- Generate the left factor from the supplied raw component. -/
noncomputable def authoredRawLeftFactorAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
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
      (authoredRawDefectComponentAtCochain normalizedInput cochain cell))

/-- The universal equation characterizing the supplied raw factor. -/
theorem authoredRawLeftFactorAtCochain_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    coreFiberLift
        (typedPresentationToSemantic
          (bcLeftPresentation input.context.square.presentation))
        ((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).obj
          (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (authoredRawLeftFactorAtCochain input cochain cell).1 =
        (((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).map
          (authoredRawDefectDecodedComponentAtCochain input cochain cell)).1 ≫
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
      (authoredRawDefectComponentAtCochain
        ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
          twoCellBase, authored⟩ cochain cell))

/-- The supplied raw factor is the counit followed by that same raw component. -/
theorem authoredRawLeftFactorAtCochain_eq_counit_comp_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredRawLeftFactorAtCochain input cochain cell =
      (bcLeftAdjunction input.context.square.presentation).counit.app
          (authoredSupportDecodedObject input.context (Discrete.mk cell)) ≫
        authoredRawDefectDecodedComponentAtCochain input cochain cell := by
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
      (authoredRawLeftFactorAtCochain input cochain cell).1 =
    coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (((bcLeftAdjunction input.context.square.presentation).counit.app
        (authoredSupportDecodedObject input.context (Discrete.mk cell))).1 ≫
        (authoredRawDefectDecodedComponentAtCochain input cochain cell).1)
  rw [authoredRawLeftFactorAtCochain_fac]
  rw [← Category.assoc]
  rw [show (bcLeftAdjunction input.context.square.presentation).counit =
      coreTransportReindexCounit leftInput by rfl]
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
    (authoredRawDefectDecodedComponentAtCochain input cochain cell)

/-! ## The raw factorization comparison at the supplied cochain -/

/-- Assemble the Beck--Chevalley component from the supplied raw factor. -/
noncomputable def authoredRawFactorizationComparisonComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
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
            (authoredRawLeftFactorAtCochain normalizedInput cochain cell.as))

/-- The via-base image of the supplied raw component. -/
noncomputable def authoredViaBaseRawDefectComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
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
        (authoredRawDefectComponentAtCochain normalizedInput cochain cell.as))

/-- The via-base image of every raw-cochain component is an isomorphism. -/
theorem authoredViaBaseRawDefectComponentAtCochain_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    IsIso (authoredViaBaseRawDefectComponentAtCochain input cochain cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  let normalizedInput : AuthoredBCDatumSquare U :=
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
      lift, endpoint_eq⟩, twoCellBase, authored⟩
  letI : IsIso (authoredRawDefectComponentAtCochain
      normalizedInput cochain cell.as) :=
    (authoredRawDefectComponentIsoAtCochain
      normalizedInput cochain cell.as).isIso_hom
  change IsIso
    ((selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredRawDefectComponentAtCochain
          normalizedInput cochain cell.as)))
  infer_instance

/-- The generalized Cycle 43 factorization retains the supplied raw component. -/
theorem authoredRawFactorizationComparisonComponentAtCochain_eq_canonical_comp_raw
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredRawFactorizationComparisonComponentAtCochain input cochain cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseRawDefectComponentAtCochain input cochain cell := by
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
  let raw := authoredRawDefectComponentAtCochain
    normalizedInput cochain cell.as
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
              (authoredRawLeftFactorAtCochain normalizedInput cochain cell.as)) =
      (coreBeckChevalleyMate presentation).app support ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map raw)
  rw [authoredRawLeftFactorAtCochain_eq_counit_comp_raw
    normalizedInput cochain cell.as]
  rw [CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.Functor.map_comp]
  rw [coreBeckChevalleyMate_app]
  simp only [Category.assoc]
  rfl

/-! ## The unified direct-first fold in the southwest support -/

/-- The total direct-first/pairwise-fallback fold at a supplied coordinate. -/
noncomputable def authoredUnifiedAxisFoldTotalAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.generatedUnifiedAxisFoldTotalAt
    input.toTransportData cochain cell

/-- The unified fold lies over the southwest identity. -/
theorem authoredUnifiedAxisFoldTotalAtCochain_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (authoredUnifiedAxisFoldTotalAtCochain input cochain cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (authoredUnifiedAxisFoldTotalAtCochain input cochain cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, authoredUnifiedAxisFoldTotalAtCochain,
    PackageFiberAut.generatedUnifiedAxisFoldTotalAt_base]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- The unified fold as a southwest-fiber morphism. -/
noncomputable def authoredUnifiedAxisFoldComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨authoredUnifiedAxisFoldTotalAtCochain input cochain cell,
    authoredUnifiedAxisFoldTotalAtCochain_isHomLift input cochain cell⟩

/-- The unified fold retagged at the exact decoded southwest object. -/
noncomputable def authoredUnifiedAxisFoldDecodedComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredSupportDecodedObject input.context (Discrete.mk cell) ⟶
      authoredSupportDecodedObject input.context (Discrete.mk cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact authoredUnifiedAxisFoldComponentAtCochain
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
      twoCellBase, authored⟩ cochain cell

/-- The decoded unified component retains the internally selected total fold. -/
theorem authoredUnifiedAxisFoldDecodedComponentAtCochain_val_heq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    HEq (authoredUnifiedAxisFoldDecodedComponentAtCochain
        input cochain cell).1
      (PackageFiberAut.generatedUnifiedAxisFoldTotalAt
        input.toTransportData cochain cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  rfl

/-- The via-base image of the unified fold. -/
noncomputable def authoredViaBaseUnifiedAxisFoldComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
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
        (authoredUnifiedAxisFoldComponentAtCochain
          normalizedInput cochain cell.as))

/-- Identity cochain makes the supplied raw southwest component identity. -/
theorem authoredRawDefectComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cochain_eq : cochain = identityDefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredRawDefectComponentAtCochain input cochain cell =
      𝟙 (input.context.supportObject cell) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  change PackageFiberAut.hom (cochain cell) =
    𝟙 (input.context.supportPackage cell)
  rw [congrFun cochain_eq cell]
  rfl

/-- Identity cochain makes the via-base raw component identity. -/
theorem authoredViaBaseRawDefectComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cochain_eq : cochain = identityDefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredViaBaseRawDefectComponentAtCochain input cochain cell =
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  change
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredRawDefectComponentAtCochain
          ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
              lift, endpoint_eq⟩, twoCellBase, authored⟩ cochain cell.as)) = _
  rw [authoredRawDefectComponentAtCochain_eq_id _ cochain cochain_eq]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- Unavailability makes the unified southwest fold identity. -/
theorem authoredUnifiedAxisFoldComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (unavailable : ¬ PackageFiberAut.UnifiedAxisFoldAvailableAt
      input.toTransportData cochain cell) :
    authoredUnifiedAxisFoldComponentAtCochain input cochain cell =
      𝟙 (input.context.supportObject cell) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact PackageFiberAut.generatedUnifiedAxisFoldTotalAt_eq_id
    input.toTransportData cochain cell unavailable

/-- Unavailability makes the via-base unified fold identity. -/
theorem authoredViaBaseUnifiedAxisFoldComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (unavailable : ¬ PackageFiberAut.UnifiedAxisFoldAvailableAt
      input.toTransportData cochain cell.as) :
    authoredViaBaseUnifiedAxisFoldComponentAtCochain input cochain cell =
      𝟙 ((authoredSupportViaBaseRoute input.context).obj cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  change
    (selectedCoreFiberReindexFunctor
      (typedRealizableHom (bcRightPresentation presentation))).map
      ((coreFiberTransportFunctor
        (typedPresentationToSemantic
          (bcBottomPresentation presentation))).map
        (authoredUnifiedAxisFoldComponentAtCochain
          ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
              lift, endpoint_eq⟩, twoCellBase, authored⟩ cochain cell.as)) = _
  rw [authoredUnifiedAxisFoldComponentAtCochain_eq_id
    _ cochain cell.as unavailable]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-! ## The combined authored diagnostic comparison -/

/-- Retain the supplied raw factor and then compose its generated unified fold. -/
noncomputable def authoredDiagnosticComparisonComponentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredSupportDirectRoute input.context).obj cell ⟶
      (authoredSupportViaBaseRoute input.context).obj cell :=
  authoredRawFactorizationComparisonComponentAtCochain input cochain cell ≫
    authoredViaBaseUnifiedAxisFoldComponentAtCochain input cochain cell

/--
The combined component has the fixed order canonical, supplied raw, unified
fold.  In particular the raw factor is not frozen at the initial coordinate.
-/
theorem authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredDiagnosticComparisonComponentAtCochain input cochain cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseRawDefectComponentAtCochain input cochain cell ≫
          authoredViaBaseUnifiedAxisFoldComponentAtCochain input cochain cell := by
  rw [authoredDiagnosticComparisonComponentAtCochain,
    authoredRawFactorizationComparisonComponentAtCochain_eq_canonical_comp_raw]
  exact Category.assoc _ _ _

/-- The complete cochain-indexed authored diagnostic comparison. -/
noncomputable def authoredDiagnosticComparisonAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredComparisonOfComponents
    (fun cell => authoredDiagnosticComparisonComponentAtCochain input cochain cell)

/--
Identity raw data and absence of the pairwise fallback make the same generated
cochain-indexed comparison canonical.
-/
theorem authoredDiagnosticComparisonAtCochain_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cochain_eq : cochain = identityDefectCochain input.toTransportData)
    (pairwiseUnavailable : ∀ cell,
      ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
        input.toTransportData cochain cell) :
    authoredDiagnosticComparisonAtCochain input cochain =
      authoredSupportCanonicalMate input.context := by
  apply CategoryTheory.NatTrans.ext
  apply funext
  intro cell
  have directUnavailable :
      ¬ PackageFiberAut.AxisFoldAvailable (cochain cell.as) := by
    rw [congrFun cochain_eq cell.as]
    exact PackageFiberAut.not_axisFoldAvailable_one
  have unifiedUnavailable :
      ¬ PackageFiberAut.UnifiedAxisFoldAvailableAt
        input.toTransportData cochain cell.as := by
    rintro (direct | pairwise)
    · exact directUnavailable direct
    · exact pairwiseUnavailable cell.as pairwise
  change authoredDiagnosticComparisonComponentAtCochain input cochain cell =
    (authoredSupportCanonicalMate input.context).app cell
  rw [authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold]
  rw [authoredViaBaseRawDefectComponentAtCochain_eq_id
    input cochain cochain_eq cell]
  rw [authoredViaBaseUnifiedAxisFoldComponentAtCochain_eq_id
    input cochain cell unifiedUnavailable]
  simp

/-- The named public producer is the literal initial raw-cochain specialization. -/
noncomputable def authoredDiagnosticComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredDiagnosticComparisonAtCochain input
    (initialRawDefectCochain input.toTransportData)

/-- Relative coherence of the same generated comparison at any supplied cochain. -/
def MateCoherentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) : Prop :=
  AuthoredSupportComparison.Agrees
    (authoredDiagnosticComparisonAtCochain input cochain)
    (authoredSupportCanonicalMate input.context)

/-- The public K2 relation for the named authored and canonical producers. -/
def MateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  mateCoherentRelEquation authoredDiagnosticComparison
    (authoredSupportCanonicalMateFamily U)

/-! ## Application and proof-use APIs -/

/-- The producer application is definitionally the initial cochain specialization. -/
@[simp]
theorem authoredDiagnosticComparison_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredDiagnosticComparison input =
      authoredDiagnosticComparisonAtCochain input
        (initialRawDefectCochain input.toTransportData) := rfl

/-- The public relation exposes exactly the named producer equality. -/
@[simp]
theorem mateCoherentRel_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    MateCoherentRel U input =
      AuthoredSupportComparison.Agrees
        (authoredDiagnosticComparison input)
        (authoredSupportCanonicalMate input.context) := rfl

/--
Proof-use audit: the initial raw factor contains the actual authored comparator
in the fixed noncommutative order against the canonical path comparator.
-/
theorem authoredInitialRawDefectTotal_uses_authoredComparator
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredRawDefectTotalAtCochain input
        (initialRawDefectCochain input.toTransportData) cell =
      (canonicalTwoCellComparator input.toTransportData 1 cell).1.inv.comp
        (PackageFiberAut.hom (input.authored.comparator cell)) := by
  exact rawTwoCellDefect_hom input.toTransportData 1 cell

/-- Application-level normalization of the public producer at one authored cell. -/
theorem authoredDiagnosticComparison_app_eq_canonical_comp_raw_comp_fold
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.Category) :
    (authoredDiagnosticComparison input).app cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseRawDefectComponentAtCochain input
          (initialRawDefectCochain input.toTransportData) cell ≫
          authoredViaBaseUnifiedAxisFoldComponentAtCochain input
            (initialRawDefectCochain input.toTransportData) cell := by
  exact authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold
    input (initialRawDefectCochain input.toTransportData) cell

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
