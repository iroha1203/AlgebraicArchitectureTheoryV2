import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparison

/-!
# Pairwise diagnostic axis folds

A single raw defect need not retain an object-fixing moved axis after edge
reselection.  This module instead compares two raw-cochain components over the
same target package.  The quotient is computed from the cochain itself; no
fold, endomorphism, comparison, or noninvertibility certificate is accepted
from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

namespace PackageFiberAut

/-- Retag a fiber automorphism along equality of the target packages. -/
noncomputable def castTarget
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) {first second : G.TwoCell}
    (package_eq : data.lift.package (G.twoTarget first) =
      data.lift.package (G.twoTarget second))
    (automorphism : PackageFiberAut
      (data.lift.package (G.twoTarget first))) :
    PackageFiberAut (data.lift.package (G.twoTarget second)) :=
  cast (congrArg (fun package : AATCorePackage U => ↥(PackageFiberAut package))
      package_eq)
    automorphism

/-- Retagging along reflexivity is propositionally inert. -/
@[simp]
theorem castTarget_rfl
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cell : G.TwoCell)
    (automorphism : PackageFiberAut
      (data.lift.package (G.twoTarget cell))) :
    castTarget data (first := cell) (second := cell) rfl automorphism =
      automorphism := by
  simp [castTarget]

/--
The relative defect of two cochain components over one endpoint.  The second
component is multiplied by the inverse first component in the fixed
noncommutative order.
-/
noncomputable def pairwiseRawDefect
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (first second : G.TwoCell)
    (package_eq : data.lift.package (G.twoTarget first) =
      data.lift.package (G.twoTarget second)) :
    PackageFiberAut (data.lift.package (G.twoTarget second)) :=
  cochain second * (castTarget data package_eq (cochain first))⁻¹

/-- A common canonical right factor cancels from the pairwise quotient. -/
theorem commonCanonicalPairwiseQuotient_eq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (firstAuthored secondAuthored canonical : PackageFiberAut P) :
    (secondAuthored * canonical⁻¹) *
        (firstAuthored * canonical⁻¹)⁻¹ =
      secondAuthored * firstAuthored⁻¹ := by
  simp [mul_assoc]

/--
Replacing a common canonical comparator cannot change the pairwise quotient.
This is the exact-endpoint presentation-replacement law used by the
double-diamond obstruction: presentation provenance may replace the common
generated comparator, while the authored faces remain fixed.
-/
theorem commonCanonicalPairwiseQuotient_replacement_invariant
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (firstAuthored secondAuthored firstCanonical secondCanonical :
      PackageFiberAut P) :
    (secondAuthored * firstCanonical⁻¹) *
        (firstAuthored * firstCanonical⁻¹)⁻¹ =
      (secondAuthored * secondCanonical⁻¹) *
        (firstAuthored * secondCanonical⁻¹)⁻¹ := by
  rw [commonCanonicalPairwiseQuotient_eq,
    commonCanonicalPairwiseQuotient_eq]

/-- Internal evidence that a pairwise quotient moves an object-fixed axis. -/
structure PairwiseAxisFoldWitnessAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell) where
  /-- The comparison face whose common coordinate will be cancelled. -/
  first : G.TwoCell
  /-- Both faces land in the same endpoint package. -/
  package_eq : data.lift.package (G.twoTarget first) =
    data.lift.package (G.twoTarget second)
  /-- The quotient itself generates the fold; no endomorphism is stored. -/
  fold : AxisFoldWitness
    (pairwiseRawDefect data cochain first second package_eq)

/-- Existence of an internally generated pairwise axis fold at one face. -/
def PairwiseAxisFoldAvailableAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell) : Prop :=
  Nonempty (PairwiseAxisFoldWitnessAt data cochain second)

/-- Select one available pairwise fold witness. -/
noncomputable def chosenPairwiseAxisFoldWitnessAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell) (available : PairwiseAxisFoldAvailableAt data cochain second) :
    PairwiseAxisFoldWitnessAt data cochain second :=
  Classical.choice available

/--
Generate a package endomorphism from the pairwise quotient when a moved-axis
witness exists, and identity otherwise.
-/
noncomputable def generatedPairwiseAxisFoldTotalAt
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell) :
    PackageTotalHom (data.lift.package (G.twoTarget second))
      (data.lift.package (G.twoTarget second)) := by
  classical
  by_cases available : PairwiseAxisFoldAvailableAt data cochain second
  · exact (chosenPairwiseAxisFoldWitnessAt data cochain second available).fold.total
  · exact PackageTotalHom.id (data.lift.package (G.twoTarget second))

/-- The generated pairwise fold lies over identity. -/
theorem generatedPairwiseAxisFoldTotalAt_base
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell) :
    (generatedPairwiseAxisFoldTotalAt data cochain second).base =
      ExtInstHom.id (packagePoint (data.lift.package (G.twoTarget second))) := by
  classical
  rw [generatedPairwiseAxisFoldTotalAt]
  split_ifs with available
  · rfl
  · rfl

/-- Availability forces the generated pairwise fold to be noninvertible. -/
theorem generatedPairwiseAxisFoldTotalAt_not_isIso
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell)
    (available : PairwiseAxisFoldAvailableAt data cochain second) :
    ¬ IsIso
      (show data.lift.package (G.twoTarget second) ⟶
          data.lift.package (G.twoTarget second) from
        generatedPairwiseAxisFoldTotalAt data cochain second) := by
  classical
  rw [generatedPairwiseAxisFoldTotalAt, dif_pos available]
  exact (chosenPairwiseAxisFoldWitnessAt data cochain second available).fold.total_not_isIso

/-- Absence of a pairwise witness specializes the generator to identity. -/
theorem generatedPairwiseAxisFoldTotalAt_eq_id
    {G : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : AdmissibleTransportData G U) (cochain : DefectCochain data)
    (second : G.TwoCell)
    (unavailable : ¬ PairwiseAxisFoldAvailableAt data cochain second) :
    generatedPairwiseAxisFoldTotalAt data cochain second =
      PackageTotalHom.id (data.lift.package (G.twoTarget second)) := by
  classical
  rw [generatedPairwiseAxisFoldTotalAt, dif_neg unavailable]

end PackageFiberAut

/-! ## Authored-support comparison at an arbitrary raw cochain -/

/-- The pairwise fold generated at one authored support component. -/
noncomputable def authoredPairwiseAxisFoldTotal
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.generatedPairwiseAxisFoldTotalAt
    input.toTransportData cochain cell

/-- The pairwise fold lies over the southwest identity. -/
theorem authoredPairwiseAxisFoldTotal_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (authoredPairwiseAxisFoldTotal input cochain cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (authoredPairwiseAxisFoldTotal input cochain cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, authoredPairwiseAxisFoldTotal,
    PackageFiberAut.generatedPairwiseAxisFoldTotalAt_base]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- The pairwise fold as a southwest-fiber morphism. -/
noncomputable def authoredPairwiseAxisFoldComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨authoredPairwiseAxisFoldTotal input cochain cell,
    authoredPairwiseAxisFoldTotal_isHomLift input cochain cell⟩

/-- The pairwise fold retagged at the decoded southwest object. -/
noncomputable def authoredPairwiseAxisFoldDecodedComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredSupportDecodedObject input.context (Discrete.mk cell) ⟶
      authoredSupportDecodedObject input.context (Discrete.mk cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  exact authoredPairwiseAxisFoldComponent
    ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
      twoCellBase, authored⟩ cochain cell

/-- The decoded component's value is the generated pairwise fold. -/
theorem authoredPairwiseAxisFoldDecodedComponent_val_heq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    HEq (authoredPairwiseAxisFoldDecodedComponent input cochain cell).1
      (PackageFiberAut.generatedPairwiseAxisFoldTotalAt
        input.toTransportData cochain cell) := by
  rcases input with ⟨⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩, twoCellBase, authored⟩
  cases realization_eq
  rfl

/-- Generate the left factor from the reindexed pairwise fold. -/
noncomputable def authoredPairwiseAxisFoldLeftFactor
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
      (authoredPairwiseAxisFoldComponent normalizedInput cochain cell))

/-- The universal equation defining the pairwise fold factor. -/
theorem authoredPairwiseAxisFoldLeftFactor_fac
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
      (authoredPairwiseAxisFoldLeftFactor input cochain cell).1 =
        (((selectedCoreFiberReindexFunctor
          (typedRealizableHom
            (bcLeftPresentation input.context.square.presentation))).map
          (authoredPairwiseAxisFoldDecodedComponent input cochain cell)).1 ≫
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
      (authoredPairwiseAxisFoldComponent
        ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩, lift, endpoint_eq⟩,
          twoCellBase, authored⟩ cochain cell))

/-- Universal uniqueness normalizes the factor to counit followed by fold. -/
theorem authoredPairwiseAxisFoldLeftFactor_eq_counit_comp_fold
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    authoredPairwiseAxisFoldLeftFactor input cochain cell =
      (bcLeftAdjunction input.context.square.presentation).counit.app
          (authoredSupportDecodedObject input.context (Discrete.mk cell)) ≫
        authoredPairwiseAxisFoldDecodedComponent input cochain cell := by
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
      (authoredPairwiseAxisFoldLeftFactor input cochain cell).1 =
    coreFiberLift
      (typedPresentationToSemantic
        (bcLeftPresentation input.context.square.presentation))
      ((selectedCoreFiberReindexFunctor
        (typedRealizableHom
          (bcLeftPresentation input.context.square.presentation))).obj
        (authoredSupportDecodedObject input.context (Discrete.mk cell))) ≫
      (((bcLeftAdjunction input.context.square.presentation).counit.app
        (authoredSupportDecodedObject input.context (Discrete.mk cell))).1 ≫
        (authoredPairwiseAxisFoldDecodedComponent input cochain cell).1)
  rw [authoredPairwiseAxisFoldLeftFactor_fac]
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
    (authoredPairwiseAxisFoldDecodedComponent input cochain cell)

/-- The BC component assembled from the pairwise fold factor. -/
noncomputable def authoredPairwiseAxisFoldComparisonComponentAtCochain
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
            (authoredPairwiseAxisFoldLeftFactor normalizedInput cochain cell.as))

/-- The via-base image of the generated pairwise fold. -/
noncomputable def authoredViaBasePairwiseAxisFoldComponentAtCochain
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
        (authoredPairwiseAxisFoldComponent normalizedInput cochain cell.as))

/-- The cochain-indexed component is canonical followed by its generated fold. -/
theorem authoredPairwiseAxisFoldComparisonComponentAtCochain_eq_canonical_comp_fold
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    authoredPairwiseAxisFoldComparisonComponentAtCochain input cochain cell =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBasePairwiseAxisFoldComponentAtCochain input cochain cell := by
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
              (authoredPairwiseAxisFoldLeftFactor normalizedInput cochain cell.as)) =
      (coreBeckChevalleyMate presentation).app support ≫
        (selectedCoreFiberReindexFunctor
          (typedRealizableHom (bcRightPresentation presentation))).map
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation presentation))).map
            (authoredPairwiseAxisFoldComponent normalizedInput cochain cell.as))
  rw [authoredPairwiseAxisFoldLeftFactor_eq_counit_comp_fold
    normalizedInput cochain cell.as]
  rw [CategoryTheory.Functor.map_comp]
  rw [CategoryTheory.Functor.map_comp]
  rw [coreBeckChevalleyMate_app]
  simp only [Category.assoc]
  rfl

/-- The complete pairwise comparison generated at a raw cochain. -/
noncomputable def authoredPairwiseAxisFoldComparisonAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportViaBaseRoute input.context :=
  authoredComparisonOfComponents
    (fun cell =>
      authoredPairwiseAxisFoldComparisonComponentAtCochain input cochain cell)

/-- Relative canonicity of the generated comparison at one orbit coordinate. -/
def PairwiseAxisFoldMateCoherentAtCochain
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData) : Prop :=
  AuthoredSupportComparison.Agrees
    (authoredPairwiseAxisFoldComparisonAtCochain input cochain)
    (authoredSupportCanonicalMate input.context)

/-- The public K2 relation is the initial-cochain specialization. -/
def MateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  fun input => PairwiseAxisFoldMateCoherentAtCochain input
    (initialRawDefectCochain input.toTransportData)

/-- Absence of a pairwise witness makes the southwest component identity. -/
theorem authoredPairwiseAxisFoldComponent_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.square.semantic.diagnostic.TwoCell)
    (unavailable : ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
      input.toTransportData cochain cell) :
    authoredPairwiseAxisFoldComponent input cochain cell =
      𝟙 (input.context.supportObject cell) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact PackageFiberAut.generatedPairwiseAxisFoldTotalAt_eq_id
    input.toTransportData cochain cell unavailable

/-- Absence of a pairwise witness makes its via-base image identity. -/
theorem authoredViaBasePairwiseAxisFoldComponentAtCochain_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category)
    (unavailable : ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
      input.toTransportData cochain cell.as) :
    authoredViaBasePairwiseAxisFoldComponentAtCochain input cochain cell =
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
        (authoredPairwiseAxisFoldComponent
          ⟨⟨⟨toSemanticBC presentation, presentation, rfl⟩,
              lift, endpoint_eq⟩, twoCellBase, authored⟩ cochain cell.as)) = _
  rw [authoredPairwiseAxisFoldComponent_eq_id _ _ _ unavailable]
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-- Pointwise absence makes the cochain-indexed family canonical. -/
theorem authoredPairwiseAxisFoldComparisonAtCochain_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (unavailable : ∀ cell,
      ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
        input.toTransportData cochain cell) :
    authoredPairwiseAxisFoldComparisonAtCochain input cochain =
      authoredSupportCanonicalMate input.context := by
  apply CategoryTheory.NatTrans.ext
  apply funext
  intro cell
  change authoredPairwiseAxisFoldComparisonComponentAtCochain
      input cochain cell =
    (authoredSupportCanonicalMate input.context).app cell
  rw [authoredPairwiseAxisFoldComparisonComponentAtCochain_eq_canonical_comp_fold]
  rw [authoredViaBasePairwiseAxisFoldComponentAtCochain_eq_id
    input cochain cell (unavailable cell.as)]
  exact Category.comp_id _

/-- Pointwise absence fires relative coherence at that cochain. -/
theorem pairwiseAxisFoldMateCoherentAtCochain_of_unavailable
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (unavailable : ∀ cell,
      ¬ PackageFiberAut.PairwiseAxisFoldAvailableAt
        input.toTransportData cochain cell) :
    PairwiseAxisFoldMateCoherentAtCochain input cochain :=
  authoredPairwiseAxisFoldComparisonAtCochain_eq_canonical
    input cochain unavailable

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
