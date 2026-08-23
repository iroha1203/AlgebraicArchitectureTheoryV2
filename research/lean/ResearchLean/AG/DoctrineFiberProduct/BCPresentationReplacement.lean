import ResearchLean.AG.DoctrineFiberProduct.CoreBeckChevalleyMateCleavageIndependence
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationReplacement
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate

/-!
# Beck--Chevalley presentation replacement

This module places two finite Beck--Chevalley presentations over one literal
semantic input.  It extracts realization provenance for all four decoded
edges and uses cartesian uniqueness to compare the two selected reindexing
routes.  Thus replacement is indexed by equality of the complete decoded BC
input, rather than equality of the authored finite endpoint codes.

The final section isolates presentation replacement for the canonical mate.
The covariant square comparison is normalized onto the fixed semantic square;
the remaining comparison separates square provenance from route provenance and
then tracks the generated adjunction data.  No authored comparator or
Beck--Chevalley equality is accepted as data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Realization provenance over one literal BC input -/

/-- A finite BC presentation whose decoder is one fixed literal semantic input. -/
structure BCRealizationProvenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : BCSemanticInput U) where
  /-- The authored finite presentation. -/
  presentation : BCPresentation U
  /-- The presentation decodes to the fixed semantic input. -/
  realization_eq : input = toSemanticBC presentation

namespace BCRealizationProvenance

/-- The first-projection semantic input extracted from the fixed BC square. -/
def leftInput {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northwest
  target := input.square.southwest
  hom := input.square.left

/-- The second-projection semantic input extracted from the fixed BC square. -/
def topInput {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northwest
  target := input.square.northeast
  hom := input.square.top

/-- The first cospan-leg semantic input extracted from the fixed BC square. -/
def bottomInput {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.southwest
  target := input.square.southeast
  hom := input.square.bottom

/-- The second cospan-leg semantic input extracted from the fixed BC square. -/
def rightInput {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) :
    CartSemanticInput U where
  source := input.square.northeast
  target := input.square.southeast
  hom := input.square.right

/-- The generated first projection supplies provenance over the literal left input. -/
def leftProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (leftInput input) where
  presentation := (bcLeftPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The generated second projection supplies provenance over the literal top input. -/
def topProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (topInput input) where
  presentation := (bcTopPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The first cospan leg supplies provenance over the literal bottom input. -/
def bottomProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (bottomInput input) where
  presentation := (bcBottomPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

/-- The second cospan leg supplies provenance over the literal right input. -/
def rightProvenance {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    CartRealizationProvenance (rightInput input) where
  presentation := (bcRightPresentation provenance.presentation).toPresentation
  realization_eq := by
    rcases provenance with ⟨presentation, rfl⟩
    rfl

end BCRealizationProvenance

/-! ## Replacement with authored diagnostic data held fixed -/

/-- Repackage BC realization provenance as a realizable square. -/
def BCRealizationProvenance.toRealizableSquare
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    RealizableSquare U where
  semantic := input
  presentation := provenance.presentation
  realization_eq := provenance.realization_eq.symm

/--
Replace only the finite BC presentation underlying an authored support context.
The semantic square, G-106 lift, and authored endpoint incidence remain literal.
-/
def AuthoredSupportContext.replacePresentation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    AuthoredSupportContext U where
  square := replacement.toRealizableSquare
  lift := context.lift
  endpoint_eq := context.endpoint_eq

/-- Read the existing realizable-square presentation as fixed-input provenance. -/
def AuthoredSupportContext.realizationProvenance
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    BCRealizationProvenance context.square.semantic where
  presentation := context.square.presentation
  realization_eq := context.square.realization_eq.symm

/--
Replace only the finite BC presentation underlying an authored BC datum.  The
diagnostic interpretation and the complete authored comparator table are reused.
-/
def AuthoredBCDatumSquare.replacePresentation
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic) :
    AuthoredBCDatumSquare U where
  context := datum.context.replacePresentation replacement
  twoCellBase := datum.twoCellBase
  authored := datum.authored

/-- Presentation replacement preserves the reviewed G-106 transport datum. -/
@[simp]
theorem AuthoredBCDatumSquare.replacePresentation_toTransportData
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic) :
    (datum.replacePresentation replacement).toTransportData =
      datum.toTransportData := rfl

/-- Presentation replacement preserves every authored comparator entry. -/
@[simp]
theorem AuthoredBCDatumSquare.replacePresentation_authored
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (datum : AuthoredBCDatumSquare U)
    (replacement : BCRealizationProvenance datum.context.square.semantic)
    (cell : datum.context.square.semantic.diagnostic.TwoCell) :
    (datum.replacePresentation replacement).authored.comparator cell =
      datum.authored.comparator cell := rfl

/-! ## Direct and via-base route comparison -/

/-- The direct mate route generated from one realization provenance. -/
noncomputable def bcProvenanceDirectRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :=
  selectedCoreFiberReindexFunctor provenance.leftProvenance.toRealizableHom ⋙
    coreFiberTransportFunctor input.square.top

/-- The via-base mate route generated from one realization provenance. -/
noncomputable def bcProvenanceViaBaseRoute
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :=
  coreFiberTransportFunctor input.square.bottom ⋙
    selectedCoreFiberReindexFunctor provenance.rightProvenance.toRealizableHom

/-- The canonical mate normalized onto the fixed literal semantic BC input. -/
noncomputable def bcProvenanceCanonicalMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    bcProvenanceDirectRoute provenance ⟶
      bcProvenanceViaBaseRoute provenance := by
  rcases provenance with ⟨presentation, rfl⟩
  exact coreBeckChevalleyMate presentation

/--
The canonical covariant square isomorphism normalized onto the fixed literal
semantic BC square.
-/
noncomputable def bcProvenanceCoreTransportSquareIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    coreFiberTransportFunctor input.square.top ⋙
        coreFiberTransportFunctor input.square.right ≅
      coreFiberTransportFunctor input.square.left ⋙
        coreFiberTransportFunctor input.square.bottom := by
  rcases provenance with ⟨presentation, rfl⟩
  exact bcCoreTransportSquareIso presentation

/--
The covariant square isomorphism generated directly from the fixed semantic
square, its commutativity equation, and the two G-109 compositors.
-/
noncomputable def bcSemanticCoreTransportSquareIso
    {U : AtomCarrier.{u}} (input : BCSemanticInput U) :
    coreFiberTransportFunctor input.square.top ⋙
        coreFiberTransportFunctor input.square.right ≅
      coreFiberTransportFunctor input.square.left ⋙
        coreFiberTransportFunctor input.square.bottom := by
  exact (coreFiberCompositor input.square.top input.square.right).symm ≪≫
    eqToIso (congrArg coreFiberTransportFunctor input.square.commutes.symm) ≪≫
    coreFiberCompositor input.square.left input.square.bottom

/--
The generated exact-endpoint transport comparison is the equality-induced
isomorphism of the underlying semantic transport functors.  The proof uses the
strong-cocartesian characterization of the generated comparison component.
-/
theorem coreFiberLift_eqToIso_fac
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (first second : source ⟶ target) (semantic_eq : first = second)
    (sourcePackage : CoreFiber source) :
    coreFiberLift first sourcePackage ≫
        ((eqToIso (congrArg coreFiberTransportFunctor semantic_eq)).hom.app
          sourcePackage).1 =
      coreFiberLift second sourcePackage := by
  cases semantic_eq
  change coreFiberLift first sourcePackage ≫ 𝟙 _ =
    coreFiberLift first sourcePackage
  simp

/-- The generated comparison between equal decoded presentations is equality transport. -/
theorem typedCoreFiberTransportPresentationComparison_eqToIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second) :
    typedCoreFiberTransportPresentationComparison first second semantic_eq =
      eqToIso (congrArg coreFiberTransportFunctor semantic_eq) := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  let firstLift := coreFiberLift
    (typedPresentationToSemantic first) sourcePackage
  letI := coreFiberLift_isStronglyCocartesian
    (typedPresentationToSemantic first) sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (typedPresentationToSemantic first) firstLift
    (𝟙 target.toSemantic)
  change firstLift ≫
      (typedCoreFiberTransportPresentationComparisonApp first second semantic_eq
        sourcePackage).hom.1 = firstLift ≫
      ((eqToIso (congrArg coreFiberTransportFunctor semantic_eq)).hom.app
        sourcePackage).1
  rw [typedCoreFiberTransportPresentationComparisonApp_hom_fac]
  exact (coreFiberLift_eqToIso_fac
    (typedPresentationToSemantic first)
    (typedPresentationToSemantic second) semantic_eq sourcePackage).symm

/-- Expose the equality transport hidden by the typed compositor wrapper. -/
theorem typedCoreFiberTransportCompositor_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    typedCoreFiberTransportCompositor first second =
      eqToIso (congrArg coreFiberTransportFunctor
        (typedPresentationToSemantic_comp first second)) ≪≫
        coreFiberCompositor (typedPresentationToSemantic first)
          (typedPresentationToSemantic second) := by
  rfl

/-- Every presentation-built square comparison is the semantic square comparison. -/
theorem bcProvenanceCoreTransportSquareIso_eq_semantic
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (provenance : BCRealizationProvenance input) :
    bcProvenanceCoreTransportSquareIso provenance =
      bcSemanticCoreTransportSquareIso input := by
  rcases provenance with ⟨presentation, rfl⟩
  change bcCoreTransportSquareIso presentation =
    bcSemanticCoreTransportSquareIso (toSemanticBC presentation)
  rw [show bcCoreTransportSquareIso presentation =
      (typedCoreFiberTransportCompositor
          (bcTopPresentation presentation)
          (bcRightPresentation presentation)).symm ≪≫
        typedCoreFiberTransportPresentationComparison
          (bcTopRightPresentation presentation)
          (bcLeftBottomPresentation presentation)
          (bcCompositePresentations_semantic_eq presentation) ≪≫
        typedCoreFiberTransportCompositor
          (bcLeftPresentation presentation)
          (bcBottomPresentation presentation) by rfl]
  rw [typedCoreFiberTransportPresentationComparison_eqToIso]
  rw [typedCoreFiberTransportCompositor_eq,
    typedCoreFiberTransportCompositor_eq]
  unfold bcSemanticCoreTransportSquareIso
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    eqToIso.hom, eqToIso.inv, NatTrans.comp_app, Category.assoc,
    eqToHom_app, eqToHom_trans_assoc]
  congr 2

/-- The covariant square comparison is independent of finite presentation provenance. -/
theorem bcProvenanceCoreTransportSquareIso_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second : BCRealizationProvenance input) :
    bcProvenanceCoreTransportSquareIso first =
      bcProvenanceCoreTransportSquareIso second :=
  (bcProvenanceCoreTransportSquareIso_eq_semantic first).trans
    (bcProvenanceCoreTransportSquareIso_eq_semantic second).symm

/--
The mate with square provenance and selected-route provenance exposed as
independent inputs over one fixed semantic BC square.
-/
noncomputable def bcSemanticSelectedMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (squareProvenance routeProvenance : BCRealizationProvenance input) :
    bcProvenanceDirectRoute routeProvenance ⟶
      bcProvenanceViaBaseRoute routeProvenance :=
  (mateEquiv
    (coreTransportReindexAdjunction
      routeProvenance.leftProvenance.toRealizableHom)
    (coreTransportReindexAdjunction
      routeProvenance.rightProvenance.toRealizableHom)
    (bcProvenanceCoreTransportSquareIso squareProvenance).hom).natTrans

/-- The selected semantic mate is independent of its square provenance. -/
theorem bcSemanticSelectedMate_reference_independent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second routeProvenance : BCRealizationProvenance input) :
    bcSemanticSelectedMate first routeProvenance =
      bcSemanticSelectedMate second routeProvenance := by
  unfold bcSemanticSelectedMate
  rw [bcProvenanceCoreTransportSquareIso_eq first second]

/-- With one provenance in both roles, the semantic selected mate is canonical. -/
theorem bcSemanticSelectedMate_self
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (provenance : BCRealizationProvenance input) :
    bcSemanticSelectedMate provenance provenance =
      bcProvenanceCanonicalMate provenance := by
  rcases provenance with ⟨presentation, rfl⟩
  rfl

/-- The generated units commute with replacement of realization provenance. -/
theorem coreTransportReindexUnit_provenanceCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : CartSemanticInput U}
    (first second : CartRealizationProvenance input)
    (sourcePackage : CoreFiber input.source) :
    (coreTransportReindexUnit first.toRealizableHom).app sourcePackage ≫
        (cartRealizationProvenanceComparison first second).hom.app
          ((coreFiberTransportFunctor input.hom).obj sourcePackage) =
      (coreTransportReindexUnit second.toRealizableHom).app sourcePackage := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let secondLift := selectedCoreFiberCartesianLift second.toRealizableHom
    ((coreFiberTransportFunctor input.hom).obj sourcePackage)
  letI : (packageProjection U).IsStronglyCartesian input.hom
      secondLift.hom := by
    simpa only [CartRealizationProvenance.toRealizableHom] using
      secondLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom secondLift.hom (𝟙 input.source)
  change (((coreTransportReindexUnit first.toRealizableHom).app
      sourcePackage).1 ≫
        ((cartRealizationProvenanceComparison first second).hom.app
          ((coreFiberTransportFunctor input.hom).obj sourcePackage)).1) ≫
      secondLift.hom =
    ((coreTransportReindexUnit second.toRealizableHom).app sourcePackage).1 ≫
      secondLift.hom
  dsimp [secondLift]
  rw [Category.assoc, show
    ((cartRealizationProvenanceComparison first second).hom.app
        ((coreFiberTransportFunctor input.hom).obj sourcePackage)).1 ≫
      (selectedCoreFiberCartesianLift second.toRealizableHom
        ((coreFiberTransportFunctor input.hom).obj sourcePackage)).hom =
    (selectedCoreFiberCartesianLift first.toRealizableHom
      ((coreFiberTransportFunctor input.hom).obj sourcePackage)).hom by
      exact cartRealizationProvenanceComparisonApp_hom_fac first second _]
  simpa only [CartRealizationProvenance.toRealizableHom] using
    (coreTransportReindexUnit_app_fac first.toRealizableHom sourcePackage).trans
      (coreTransportReindexUnit_app_fac second.toRealizableHom sourcePackage).symm

/-- The generated counits commute with replacement of realization provenance. -/
theorem coreTransportReindexCounit_provenanceCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : CartSemanticInput U}
    (first second : CartRealizationProvenance input)
    (targetPackage : CoreFiber input.target) :
    (coreFiberTransportFunctor input.hom).map
          ((cartRealizationProvenanceComparison first second).hom.app
            targetPackage) ≫
        (coreTransportReindexCounit second.toRealizableHom).app targetPackage =
      (coreTransportReindexCounit first.toRealizableHom).app targetPackage := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI := coreFiberLift_isStronglyCocartesian input.hom
    ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj targetPackage)
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.hom
    (coreFiberLift input.hom
      ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj targetPackage))
    (𝟙 input.target)
  change coreFiberLift input.hom
        ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj
          targetPackage) ≫
      (((coreFiberTransportFunctor input.hom).map
        ((cartRealizationProvenanceComparison first second).hom.app
          targetPackage)).1 ≫
        ((coreTransportReindexCounit second.toRealizableHom).app
          targetPackage).1) =
    coreFiberLift input.hom
        ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj
          targetPackage) ≫
      ((coreTransportReindexCounit first.toRealizableHom).app targetPackage).1
  calc
    _ = (coreFiberLift input.hom
          ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj
            targetPackage) ≫
        ((coreFiberTransportFunctor input.hom).map
          ((cartRealizationProvenanceComparison first second).hom.app
            targetPackage)).1) ≫
        ((coreTransportReindexCounit second.toRealizableHom).app
          targetPackage).1 := (Category.assoc _ _ _).symm
    _ = ((cartRealizationProvenanceComparison first second).hom.app
          targetPackage).1 ≫
        coreFiberLift input.hom
          ((selectedCoreFiberReindexFunctor second.toRealizableHom).obj
            targetPackage) ≫
        ((coreTransportReindexCounit second.toRealizableHom).app
          targetPackage).1 := by
      rw [show coreFiberLift input.hom
            ((selectedCoreFiberReindexFunctor first.toRealizableHom).obj
              targetPackage) ≫
          ((coreFiberTransportFunctor input.hom).map
            ((cartRealizationProvenanceComparison first second).hom.app
              targetPackage)).1 =
        ((cartRealizationProvenanceComparison first second).hom.app
            targetPackage).1 ≫
          coreFiberLift input.hom
            ((selectedCoreFiberReindexFunctor second.toRealizableHom).obj
              targetPackage) by
        exact coreFiberTransportMap_fac input.hom
          ((cartRealizationProvenanceComparison first second).hom.app
            targetPackage)]
      exact Category.assoc _ _ _
    _ = ((cartRealizationProvenanceComparison first second).hom.app
          targetPackage).1 ≫
        (selectedCoreFiberCartesianLift second.toRealizableHom
          targetPackage).hom := by
      rw [show coreFiberLift input.hom
            ((selectedCoreFiberReindexFunctor second.toRealizableHom).obj
              targetPackage) ≫
          ((coreTransportReindexCounit second.toRealizableHom).app
            targetPackage).1 =
        (selectedCoreFiberCartesianLift second.toRealizableHom
          targetPackage).hom by
        simpa only [CartRealizationProvenance.toRealizableHom] using
          coreTransportReindexCounit_app_fac second.toRealizableHom
            targetPackage]
    _ = (selectedCoreFiberCartesianLift first.toRealizableHom
          targetPackage).hom :=
      cartRealizationProvenanceComparisonApp_hom_fac first second targetPackage
    _ = _ := by
      symm
      simpa only [CartRealizationProvenance.toRealizableHom] using
        coreTransportReindexCounit_app_fac first.toRealizableHom targetPackage

/-- The generated hom-set equivalences commute with realization replacement. -/
theorem coreTransportReindexHomEquiv_provenanceCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : CartSemanticInput U}
    (first second : CartRealizationProvenance input)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      targetPackage) :
    (coreTransportReindexAdjunction second.toRealizableHom).homEquiv
        sourcePackage targetPackage hom =
      (coreTransportReindexAdjunction first.toRealizableHom).homEquiv
          sourcePackage targetPackage hom ≫
        (cartRealizationProvenanceComparison first second).hom.app
          targetPackage := by
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  symm
  calc
    _ = (coreTransportReindexAdjunction first.toRealizableHom).unit.app
          sourcePackage ≫
        ((selectedCoreFiberReindexFunctor first.toRealizableHom).map hom ≫
          (cartRealizationProvenanceComparison first second).hom.app
            targetPackage) := Category.assoc _ _ _
    _ = (coreTransportReindexAdjunction first.toRealizableHom).unit.app
          sourcePackage ≫
        ((cartRealizationProvenanceComparison first second).hom.app
            ((coreFiberTransportFunctor input.hom).obj sourcePackage) ≫
          (selectedCoreFiberReindexFunctor second.toRealizableHom).map hom) := by
      rw [show (selectedCoreFiberReindexFunctor first.toRealizableHom).map hom ≫
          (cartRealizationProvenanceComparison first second).hom.app
            targetPackage =
        (cartRealizationProvenanceComparison first second).hom.app
            ((coreFiberTransportFunctor input.hom).obj sourcePackage) ≫
          (selectedCoreFiberReindexFunctor second.toRealizableHom).map hom by
        simpa only [CartRealizationProvenance.toRealizableHom] using
          (cartRealizationProvenanceComparison first second).hom.naturality hom]
    _ = ((coreTransportReindexAdjunction first.toRealizableHom).unit.app
          sourcePackage ≫
        (cartRealizationProvenanceComparison first second).hom.app
          ((coreFiberTransportFunctor input.hom).obj sourcePackage)) ≫
        (selectedCoreFiberReindexFunctor second.toRealizableHom).map hom :=
      (Category.assoc _ _ _).symm
    _ = _ := by
      rw [show (coreTransportReindexAdjunction first.toRealizableHom).unit.app
            sourcePackage ≫
          (cartRealizationProvenanceComparison first second).hom.app
            ((coreFiberTransportFunctor input.hom).obj sourcePackage) =
        (coreTransportReindexAdjunction second.toRealizableHom).unit.app
          sourcePackage by
        simpa only [coreTransportReindexUnit] using
          coreTransportReindexUnit_provenanceCompatibility first second
            sourcePackage]

/-- The semantic selected mate is the generated right transpose of square then counit. -/
theorem bcSemanticSelectedMate_homEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (squareProvenance routeProvenance : BCRealizationProvenance input)
    (sourcePackage : CoreFiber input.square.southwest) :
    (bcSemanticSelectedMate squareProvenance routeProvenance).app sourcePackage =
      (coreTransportReindexAdjunction
        routeProvenance.rightProvenance.toRealizableHom).homEquiv
          ((coreFiberTransportFunctor input.square.top).obj
            ((selectedCoreFiberReindexFunctor
              routeProvenance.leftProvenance.toRealizableHom).obj sourcePackage))
          ((coreFiberTransportFunctor input.square.bottom).obj sourcePackage)
          ((bcProvenanceCoreTransportSquareIso squareProvenance).hom.app
              ((selectedCoreFiberReindexFunctor
                routeProvenance.leftProvenance.toRealizableHom).obj
                  sourcePackage) ≫
            (coreFiberTransportFunctor input.square.bottom).map
              ((coreTransportReindexCounit
                routeProvenance.leftProvenance.toRealizableHom).app
                  sourcePackage)) := by
  simp [bcSemanticSelectedMate, mateEquiv_apply]
  rw [Adjunction.homEquiv_unit, Functor.map_comp]
  rfl

/-- The generated direct routes are canonically isomorphic across provenance. -/
noncomputable def bcProvenanceDirectRouteComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second : BCRealizationProvenance input) :
    bcProvenanceDirectRoute first ≅ bcProvenanceDirectRoute second :=
  Functor.isoWhiskerRight
    (cartRealizationProvenanceComparison first.leftProvenance
      second.leftProvenance)
    (coreFiberTransportFunctor input.square.top)

/-- The generated via-base routes are canonically isomorphic across provenance. -/
noncomputable def bcProvenanceViaBaseRouteComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (first second : BCRealizationProvenance input) :
    bcProvenanceViaBaseRoute first ≅ bcProvenanceViaBaseRoute second :=
  Functor.isoWhiskerLeft
    (coreFiberTransportFunctor input.square.bottom)
    (cartRealizationProvenanceComparison first.rightProvenance
      second.rightProvenance)

/-- The semantic selected mates form the public presentation-replacement square. -/
theorem bcSemanticSelectedMate_replacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    (bcProvenanceDirectRouteComparison reference replacement).hom ≫
        bcSemanticSelectedMate reference replacement =
      bcSemanticSelectedMate reference reference ≫
        (bcProvenanceViaBaseRouteComparison reference replacement).hom := by
  apply NatTrans.ext
  funext sourcePackage
  simp only [NatTrans.comp_app]
  rw [bcSemanticSelectedMate_homEquiv,
    bcSemanticSelectedMate_homEquiv]
  have leftCounitComparison :=
    coreTransportReindexCounit_provenanceCompatibility
      reference.leftProvenance replacement.leftProvenance sourcePackage
  change (coreFiberTransportFunctor input.square.left).map
        ((cartRealizationProvenanceComparison reference.leftProvenance
          replacement.leftProvenance).hom.app sourcePackage) ≫
      (coreTransportReindexCounit
        replacement.leftProvenance.toRealizableHom).app sourcePackage =
    (coreTransportReindexCounit
      reference.leftProvenance.toRealizableHom).app sourcePackage
    at leftCounitComparison
  calc
    (coreFiberTransportFunctor input.square.top).map
          ((cartRealizationProvenanceComparison reference.leftProvenance
            replacement.leftProvenance).hom.app sourcePackage) ≫
        (coreTransportReindexAdjunction
          replacement.rightProvenance.toRealizableHom).homEquiv _ _
            ((bcProvenanceCoreTransportSquareIso reference).hom.app
                ((selectedCoreFiberReindexFunctor
                  replacement.leftProvenance.toRealizableHom).obj
                    sourcePackage) ≫
              (coreFiberTransportFunctor input.square.bottom).map
                ((coreTransportReindexCounit
                  replacement.leftProvenance.toRealizableHom).app
                    sourcePackage)) =
      (coreTransportReindexAdjunction
        replacement.rightProvenance.toRealizableHom).homEquiv _ _
          ((coreFiberTransportFunctor input.square.right).map
              ((coreFiberTransportFunctor input.square.top).map
                ((cartRealizationProvenanceComparison reference.leftProvenance
                  replacement.leftProvenance).hom.app sourcePackage)) ≫
            ((bcProvenanceCoreTransportSquareIso reference).hom.app
                ((selectedCoreFiberReindexFunctor
                  replacement.leftProvenance.toRealizableHom).obj
                    sourcePackage) ≫
              (coreFiberTransportFunctor input.square.bottom).map
                ((coreTransportReindexCounit
                  replacement.leftProvenance.toRealizableHom).app
                    sourcePackage))) := by
        exact ((coreTransportReindexAdjunction
          replacement.rightProvenance.toRealizableHom).homEquiv_naturality_left
            ((coreFiberTransportFunctor input.square.top).map
              ((cartRealizationProvenanceComparison reference.leftProvenance
                replacement.leftProvenance).hom.app sourcePackage))
            _).symm
    _ = (coreTransportReindexAdjunction
        replacement.rightProvenance.toRealizableHom).homEquiv _ _
          ((bcProvenanceCoreTransportSquareIso reference).hom.app
              ((selectedCoreFiberReindexFunctor
                reference.leftProvenance.toRealizableHom).obj sourcePackage) ≫
            (coreFiberTransportFunctor input.square.bottom).map
              ((coreTransportReindexCounit
                reference.leftProvenance.toRealizableHom).app
                  sourcePackage)) := by
      apply congrArg
      calc
        _ = ((coreFiberTransportFunctor input.square.top ⋙
                coreFiberTransportFunctor input.square.right).map
              ((cartRealizationProvenanceComparison reference.leftProvenance
                replacement.leftProvenance).hom.app sourcePackage)) ≫
            ((bcProvenanceCoreTransportSquareIso reference).hom.app
                ((selectedCoreFiberReindexFunctor
                  replacement.leftProvenance.toRealizableHom).obj
                    sourcePackage) ≫
              (coreFiberTransportFunctor input.square.bottom).map
                ((coreTransportReindexCounit
                  replacement.leftProvenance.toRealizableHom).app
                    sourcePackage)) := by rfl
        _ = _ := by
          rw [← Category.assoc]
          rw [(bcProvenanceCoreTransportSquareIso reference).hom.naturality]
          rw [Functor.comp_map]
          rw [Category.assoc, ← Functor.map_comp]
          rw [leftCounitComparison]
    _ = (coreTransportReindexAdjunction
          reference.rightProvenance.toRealizableHom).homEquiv _ _
            ((bcProvenanceCoreTransportSquareIso reference).hom.app
                ((selectedCoreFiberReindexFunctor
                  reference.leftProvenance.toRealizableHom).obj
                    sourcePackage) ≫
              (coreFiberTransportFunctor input.square.bottom).map
                ((coreTransportReindexCounit
                  reference.leftProvenance.toRealizableHom).app
                    sourcePackage)) ≫
        (cartRealizationProvenanceComparison reference.rightProvenance
          replacement.rightProvenance).hom.app
            ((coreFiberTransportFunctor input.square.bottom).obj
              sourcePackage) := by
      exact coreTransportReindexHomEquiv_provenanceCompatibility
        reference.rightProvenance replacement.rightProvenance _ _ _

/-! ## The mate with the reference covariant square held fixed -/

/--
The selected left cleavage generated from `replacement`, rebased over the
literal semantic input of `reference`.  Only realization provenance changes.
-/
noncomputable def bcReplacementLeftCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    CoreFiberCartesianCleavage
      (bcLeftInput reference.presentation).semantic := by
  rcases reference with ⟨presentation, rfl⟩
  exact selectedCoreFiberCartesianCleavage
    replacement.leftProvenance.toRealizableHom

/--
The selected right cleavage generated from `replacement`, rebased over the
literal semantic input of `reference`.
-/
noncomputable def bcReplacementRightCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    CoreFiberCartesianCleavage
      (bcRightInput reference.presentation).semantic := by
  rcases reference with ⟨presentation, rfl⟩
  exact selectedCoreFiberCartesianCleavage
    replacement.rightProvenance.toRealizableHom

/--
The canonical left selected-functor comparison factored through the rebased
replacement cleavage used by the cleavage-independent mate theorem.
-/
noncomputable def bcReplacementLeftSelectedComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    selectedCoreFiberReindexFunctor reference.leftProvenance.toRealizableHom ≅
      selectedCoreFiberReindexFunctor replacement.leftProvenance.toRealizableHom := by
  rcases reference with ⟨reference, rfl⟩
  exact
    (coreFiberCleavageSelectedComparison
      (bcLeftInput reference)
      (bcReplacementLeftCleavage
        ⟨reference, rfl⟩ replacement)).symm ≪≫
      selectedCoreFiberCleavageBridge replacement.leftProvenance.toRealizableHom

/-- Right-hand analogue of `bcReplacementLeftSelectedComparison`. -/
noncomputable def bcReplacementRightSelectedComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    selectedCoreFiberReindexFunctor reference.rightProvenance.toRealizableHom ≅
      selectedCoreFiberReindexFunctor replacement.rightProvenance.toRealizableHom := by
  rcases reference with ⟨reference, rfl⟩
  exact
    (coreFiberCleavageSelectedComparison
      (bcRightInput reference)
      (bcReplacementRightCleavage
        ⟨reference, rfl⟩ replacement)).symm ≪≫
      selectedCoreFiberCleavageBridge replacement.rightProvenance.toRealizableHom

/-- The factored left comparison is the public provenance comparison. -/
theorem bcReplacementLeftSelectedComparison_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    bcReplacementLeftSelectedComparison reference replacement =
      cartRealizationProvenanceComparison reference.leftProvenance
        replacement.leftProvenance := by
  rcases reference with ⟨presentation, rfl⟩
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  let replacementLift := selectedCoreFiberCartesianLift
    replacement.leftProvenance.toRealizableHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian
      (BCRealizationProvenance.leftInput
        (toSemanticBC presentation)).hom replacementLift.hom :=
    replacementLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U)
    (BCRealizationProvenance.leftInput (toSemanticBC presentation)).hom
    replacementLift.hom
    (𝟙 (BCRealizationProvenance.leftInput (toSemanticBC presentation)).source)
  change
    (((coreFiberCleavageSelectedComparisonApp
        (bcLeftInput presentation)
        (bcReplacementLeftCleavage ⟨presentation, rfl⟩ replacement)
        targetPackage).inv.1 ≫
      (selectedCoreFiberCleavageBridgeApp
        replacement.leftProvenance.toRealizableHom targetPackage).hom.1) ≫
        replacementLift.hom) =
      (cartRealizationProvenanceComparisonApp
        (BCRealizationProvenance.leftProvenance ⟨presentation, rfl⟩)
        replacement.leftProvenance targetPackage).hom.1 ≫ replacementLift.hom
  rw [Category.assoc, selectedCoreFiberCleavageBridgeApp_hom_fac]
  change
    (coreFiberCleavageSelectedComparisonApp
        (bcLeftInput presentation)
        (bcReplacementLeftCleavage ⟨presentation, rfl⟩ replacement)
        targetPackage).inv.1 ≫
        ((bcReplacementLeftCleavage ⟨presentation, rfl⟩ replacement).lift
          targetPackage).hom =
      (cartRealizationProvenanceComparisonApp
        (BCRealizationProvenance.leftProvenance ⟨presentation, rfl⟩)
        replacement.leftProvenance targetPackage).hom.1 ≫ replacementLift.hom
  rw [coreFiberCleavageSelectedComparisonApp_inv_fac,
    cartRealizationProvenanceComparisonApp_hom_fac]
  rfl

/-- The factored right comparison is the public provenance comparison. -/
theorem bcReplacementRightSelectedComparison_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    bcReplacementRightSelectedComparison reference replacement =
      cartRealizationProvenanceComparison reference.rightProvenance
        replacement.rightProvenance := by
  rcases reference with ⟨presentation, rfl⟩
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  let replacementLift := selectedCoreFiberCartesianLift
    replacement.rightProvenance.toRealizableHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian
      (BCRealizationProvenance.rightInput
        (toSemanticBC presentation)).hom replacementLift.hom :=
    replacementLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U)
    (BCRealizationProvenance.rightInput (toSemanticBC presentation)).hom
    replacementLift.hom
    (𝟙 (BCRealizationProvenance.rightInput (toSemanticBC presentation)).source)
  change
    (((coreFiberCleavageSelectedComparisonApp
        (bcRightInput presentation)
        (bcReplacementRightCleavage ⟨presentation, rfl⟩ replacement)
        targetPackage).inv.1 ≫
      (selectedCoreFiberCleavageBridgeApp
        replacement.rightProvenance.toRealizableHom targetPackage).hom.1) ≫
        replacementLift.hom) =
      (cartRealizationProvenanceComparisonApp
        (BCRealizationProvenance.rightProvenance ⟨presentation, rfl⟩)
        replacement.rightProvenance targetPackage).hom.1 ≫ replacementLift.hom
  rw [Category.assoc, selectedCoreFiberCleavageBridgeApp_hom_fac]
  change
    (coreFiberCleavageSelectedComparisonApp
        (bcRightInput presentation)
        (bcReplacementRightCleavage ⟨presentation, rfl⟩ replacement)
        targetPackage).inv.1 ≫
        ((bcReplacementRightCleavage ⟨presentation, rfl⟩ replacement).lift
          targetPackage).hom =
      (cartRealizationProvenanceComparisonApp
        (BCRealizationProvenance.rightProvenance ⟨presentation, rfl⟩)
        replacement.rightProvenance targetPackage).hom.1 ≫ replacementLift.hom
  rw [coreFiberCleavageSelectedComparisonApp_inv_fac,
    cartRealizationProvenanceComparisonApp_hom_fac]
  rfl

/--
The replacement mate with the covariant square isomorphism fixed at the
reference presentation.  Both reindexing functors are generated from the
replacement provenance.
-/
noncomputable def bcRebasedReplacementMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :=
  coreBeckChevalleyCleavageMate reference.presentation
    (bcReplacementLeftCleavage reference replacement)
    (bcReplacementRightCleavage reference replacement)

/--
Normalize the rebased replacement mate onto the public selected routes generated
by `replacement`.  The two conjugating isomorphisms are generated by the same
selected cartesian lifts; no route comparison is supplied by a caller.
-/
noncomputable def bcSelectedRebasedReplacementMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    bcProvenanceDirectRoute replacement ⟶
      bcProvenanceViaBaseRoute replacement := by
  rcases reference with ⟨presentation, rfl⟩
  exact
    Functor.whiskerRight
        (selectedCoreFiberCleavageBridge
          replacement.leftProvenance.toRealizableHom).inv
        (coreFiberTransportFunctor
          (toSemanticBC presentation).square.top) ≫
      bcRebasedReplacementMate ⟨presentation, rfl⟩ replacement ≫
      Functor.whiskerLeft
        (coreFiberTransportFunctor
          (toSemanticBC presentation).square.bottom)
        (selectedCoreFiberCleavageBridge
          replacement.rightProvenance.toRealizableHom).hom

/--
Changing both presentation-generated cleavages commutes with the canonical
mate while the reference covariant square isomorphism is held fixed.  This is
the complete adjunction/unit/counit part of BC presentation replacement.
-/
theorem coreBeckChevalleyMate_rebasedReplacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    Functor.whiskerRight
          (coreFiberCleavageSelectedComparison
            (bcLeftInput reference.presentation)
            (bcReplacementLeftCleavage reference replacement)).hom
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation reference.presentation))) ≫
        coreBeckChevalleyMate reference.presentation =
      bcRebasedReplacementMate reference replacement ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation reference.presentation)))
          (coreFiberCleavageSelectedComparison
            (bcRightInput reference.presentation)
            (bcReplacementRightCleavage reference replacement)).hom := by
  exact coreBeckChevalleyCleavageMate_selectedComparison
    reference.presentation
    (bcReplacementLeftCleavage reference replacement)
    (bcReplacementRightCleavage reference replacement)

/--
Inverse form of the cleavage comparison square.  This is the orientation needed
to normalize the rebased mate onto the replacement-selected routes.
-/
theorem coreBeckChevalleyMate_rebasedReplacement_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    Functor.whiskerRight
          (coreFiberCleavageSelectedComparison
            (bcLeftInput reference.presentation)
            (bcReplacementLeftCleavage reference replacement)).inv
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcTopPresentation reference.presentation))) ≫
        bcRebasedReplacementMate reference replacement =
      coreBeckChevalleyMate reference.presentation ≫
        Functor.whiskerLeft
          (coreFiberTransportFunctor
            (typedPresentationToSemantic
              (bcBottomPresentation reference.presentation)))
          (coreFiberCleavageSelectedComparison
            (bcRightInput reference.presentation)
            (bcReplacementRightCleavage reference replacement)).inv := by
  let leftComparison := Functor.isoWhiskerRight
    (coreFiberCleavageSelectedComparison
      (bcLeftInput reference.presentation)
      (bcReplacementLeftCleavage reference replacement))
    (coreFiberTransportFunctor
      (typedPresentationToSemantic (bcTopPresentation reference.presentation)))
  let rightComparison := Functor.isoWhiskerLeft
    (coreFiberTransportFunctor
      (typedPresentationToSemantic
        (bcBottomPresentation reference.presentation)))
    (coreFiberCleavageSelectedComparison
      (bcRightInput reference.presentation)
      (bcReplacementRightCleavage reference replacement))
  have comparisonSquare :=
    coreBeckChevalleyMate_rebasedReplacement reference replacement
  change leftComparison.hom ≫ coreBeckChevalleyMate reference.presentation =
    bcRebasedReplacementMate reference replacement ≫
      rightComparison.hom at comparisonSquare
  change leftComparison.inv ≫ bcRebasedReplacementMate reference replacement =
    coreBeckChevalleyMate reference.presentation ≫ rightComparison.inv
  calc
    _ = leftComparison.inv ≫
          (bcRebasedReplacementMate reference replacement ≫
            rightComparison.hom) ≫ rightComparison.inv := by simp
    _ = leftComparison.inv ≫
          (leftComparison.hom ≫
            coreBeckChevalleyMate reference.presentation) ≫
            rightComparison.inv := by rw [← comparisonSquare]
    _ = _ := by simp

/--
The canonical mate square written entirely with the public presentation-route
comparisons.  Thus the two route isomorphisms and the mate theorem are one
generated construction, rather than unrelated declarations.
-/
theorem bcProvenanceCanonicalMate_rebasedReplacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    (bcProvenanceDirectRouteComparison reference replacement).hom ≫
        bcSelectedRebasedReplacementMate reference replacement =
      bcProvenanceCanonicalMate reference ≫
        (bcProvenanceViaBaseRouteComparison reference replacement).hom := by
  rcases reference with ⟨presentation, rfl⟩
  let leftComparison := Functor.isoWhiskerRight
    (coreFiberCleavageSelectedComparison
      (bcLeftInput presentation)
      (bcReplacementLeftCleavage ⟨presentation, rfl⟩ replacement))
    (coreFiberTransportFunctor (toSemanticBC presentation).square.top)
  let rightComparison := Functor.isoWhiskerLeft
    (coreFiberTransportFunctor (toSemanticBC presentation).square.bottom)
    (coreFiberCleavageSelectedComparison
      (bcRightInput presentation)
      (bcReplacementRightCleavage ⟨presentation, rfl⟩ replacement))
  let leftBridge := Functor.isoWhiskerRight
    (selectedCoreFiberCleavageBridge
      replacement.leftProvenance.toRealizableHom)
    (coreFiberTransportFunctor (toSemanticBC presentation).square.top)
  let rightBridge := Functor.isoWhiskerLeft
    (coreFiberTransportFunctor
      (toSemanticBC presentation).square.bottom)
    (selectedCoreFiberCleavageBridge
      replacement.rightProvenance.toRealizableHom)
  have inverseSquare :=
    coreBeckChevalleyMate_rebasedReplacement_inv
      (⟨presentation, rfl⟩ :
        BCRealizationProvenance (toSemanticBC presentation)) replacement
  change leftComparison.inv ≫
      bcRebasedReplacementMate ⟨presentation, rfl⟩ replacement =
    coreBeckChevalleyMate presentation ≫ rightComparison.inv at inverseSquare
  have postcomposed := congrArg (fun transformation =>
    transformation ≫ rightBridge.hom) inverseSquare
  unfold bcProvenanceDirectRouteComparison
    bcProvenanceViaBaseRouteComparison
  rw [← bcReplacementLeftSelectedComparison_eq
      (⟨presentation, rfl⟩ :
        BCRealizationProvenance (toSemanticBC presentation)) replacement,
    ← bcReplacementRightSelectedComparison_eq
      (⟨presentation, rfl⟩ :
        BCRealizationProvenance (toSemanticBC presentation)) replacement]
  dsimp [bcReplacementLeftSelectedComparison,
    bcReplacementRightSelectedComparison,
    bcSelectedRebasedReplacementMate, bcProvenanceCanonicalMate]
  rw [Functor.whiskerRight_comp]
  change (leftComparison.inv ≫ leftBridge.hom) ≫
      (leftBridge.inv ≫
        bcRebasedReplacementMate ⟨presentation, rfl⟩ replacement ≫
          rightBridge.hom) =
    coreBeckChevalleyMate presentation ≫
      (rightComparison.inv ≫ rightBridge.hom)
  simpa [Category.assoc] using postcomposed

/-- The cleavage-rebased mate is the semantic mate generated from the same square. -/
theorem bcSelectedRebasedReplacementMate_eq_semanticSelectedMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    bcSelectedRebasedReplacementMate reference replacement =
      bcSemanticSelectedMate reference replacement := by
  have semanticSquare :=
    bcSemanticSelectedMate_replacement reference replacement
  rw [bcSemanticSelectedMate_self] at semanticSquare
  exact (cancel_epi
    (bcProvenanceDirectRouteComparison reference replacement).hom).mp
      ((bcProvenanceCanonicalMate_rebasedReplacement reference replacement).trans
        semanticSquare.symm)

/-- The cleavage-rebased mate is the replacement provenance's canonical mate. -/
theorem bcSelectedRebasedReplacementMate_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (reference replacement : BCRealizationProvenance input) :
    bcSelectedRebasedReplacementMate reference replacement =
      bcProvenanceCanonicalMate replacement := by
  calc
    _ = bcSemanticSelectedMate reference replacement :=
      bcSelectedRebasedReplacementMate_eq_semanticSelectedMate
        reference replacement
    _ = bcSemanticSelectedMate replacement replacement :=
      bcSemanticSelectedMate_reference_independent
        reference replacement replacement
    _ = _ := bcSemanticSelectedMate_self replacement

/-- A self-replacement normalizes back to the provenance's canonical mate. -/
theorem bcSelectedRebasedReplacementMate_self
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U}
    (provenance : BCRealizationProvenance input) :
    bcSelectedRebasedReplacementMate provenance provenance =
      bcProvenanceCanonicalMate provenance := by
  have comparison :=
    bcProvenanceCanonicalMate_rebasedReplacement provenance provenance
  unfold bcProvenanceDirectRouteComparison
    bcProvenanceViaBaseRouteComparison at comparison
  rw [cartRealizationProvenanceComparison_refl,
    cartRealizationProvenanceComparison_refl] at comparison
  simpa using comparison

/-! ## Authored-support restriction of presentation replacement -/

/-- Normalize the existing authored direct route to its provenance-indexed form. -/
noncomputable def authoredSupportDirectRouteProvenanceIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    authoredSupportDirectRoute context ≅
      context.supportFunctor ⋙
        bcProvenanceDirectRoute context.realizationProvenance := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Iso.refl _

/-- Normalize the existing authored via-base route to its provenance-indexed form. -/
noncomputable def authoredSupportViaBaseRouteProvenanceIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    authoredSupportViaBaseRoute context ≅
      context.supportFunctor ⋙
        bcProvenanceViaBaseRoute context.realizationProvenance := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Iso.refl _

/-- The public direct-route comparison restricted to fixed authored support. -/
noncomputable def authoredSupportDirectRouteReplacementComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    authoredSupportDirectRoute context ≅
      authoredSupportDirectRoute (context.replacePresentation replacement) :=
  authoredSupportDirectRouteProvenanceIso context ≪≫
    Functor.isoWhiskerLeft context.supportFunctor
      (bcProvenanceDirectRouteComparison context.realizationProvenance
        replacement) ≪≫
    (authoredSupportDirectRouteProvenanceIso
      (context.replacePresentation replacement)).symm

/-- The public via-base comparison restricted to fixed authored support. -/
noncomputable def authoredSupportViaBaseRouteReplacementComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    authoredSupportViaBaseRoute context ≅
      authoredSupportViaBaseRoute (context.replacePresentation replacement) :=
  authoredSupportViaBaseRouteProvenanceIso context ≪≫
    Functor.isoWhiskerLeft context.supportFunctor
      (bcProvenanceViaBaseRouteComparison context.realizationProvenance
        replacement) ≪≫
    (authoredSupportViaBaseRouteProvenanceIso
      (context.replacePresentation replacement)).symm

/-- Restrict the selected rebased replacement mate to the fixed authored support. -/
noncomputable def authoredSupportSelectedRebasedReplacementMate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    authoredSupportDirectRoute (context.replacePresentation replacement) ⟶
      authoredSupportViaBaseRoute
        (context.replacePresentation replacement) :=
  (authoredSupportDirectRouteProvenanceIso
      (context.replacePresentation replacement)).hom ≫
    Functor.whiskerLeft context.supportFunctor
      (bcSelectedRebasedReplacementMate context.realizationProvenance
        replacement) ≫
    (authoredSupportViaBaseRouteProvenanceIso
      (context.replacePresentation replacement)).inv

/-- On fixed authored support, the rebased mate is the normalized replacement canonical mate. -/
theorem authoredSupportSelectedRebasedReplacementMate_eq_canonical
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    authoredSupportSelectedRebasedReplacementMate context replacement =
      (authoredSupportDirectRouteProvenanceIso
          (context.replacePresentation replacement)).hom ≫
        Functor.whiskerLeft context.supportFunctor
          (bcProvenanceCanonicalMate replacement) ≫
        (authoredSupportViaBaseRouteProvenanceIso
          (context.replacePresentation replacement)).inv := by
  unfold authoredSupportSelectedRebasedReplacementMate
  rw [bcSelectedRebasedReplacementMate_eq_canonical]

/--
Presentation replacement commutes with the canonical mate after restriction to
the same authored support.  The context replacement fixes its lift and endpoint
data; the separate datum-level replacement fixes the authored table
definitionally.  This structural theorem consumes only the fixed support.
-/
theorem authoredSupportCanonicalMate_rebasedReplacement
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (replacement : BCRealizationProvenance context.square.semantic) :
    (authoredSupportDirectRouteReplacementComparison
        context replacement).hom ≫
      authoredSupportSelectedRebasedReplacementMate context replacement =
    authoredSupportCanonicalMate context ≫
      (authoredSupportViaBaseRouteReplacementComparison
        context replacement).hom := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  have publicSquare := bcProvenanceCanonicalMate_rebasedReplacement
    (⟨presentation, rfl⟩ :
      BCRealizationProvenance (toSemanticBC presentation)) replacement
  have restrictedSquare := congrArg
    (Functor.whiskerLeft
      (AuthoredSupportContext.supportFunctor
        ⟨⟨toSemanticBC presentation, presentation, rfl⟩,
          lift, endpoint_eq⟩)) publicSquare
  simpa [authoredSupportDirectRouteReplacementComparison,
    authoredSupportViaBaseRouteReplacementComparison,
    authoredSupportSelectedRebasedReplacementMate,
    authoredSupportDirectRouteProvenanceIso,
    authoredSupportViaBaseRouteProvenanceIso,
    authoredSupportCanonicalMate,
    Functor.whiskerLeft_comp, Category.assoc] using restrictedSquare

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
