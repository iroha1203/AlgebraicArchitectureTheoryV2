import Formal.Arch.Extension.SplitExtensionLifting

namespace Formal.Arch

/-
Canonical static skeleton for the coupon feature extension.

The model is intentionally static-only: it records a declared payment port and
a bad direct dependency from the coupon feature into `PaymentAdapter`'s internal
cache.  It does not claim runtime flatness, semantic flatness, or extractor
completeness.
-/
namespace CouponStaticDependencyExample

inductive CoreComponent where
  | paymentApi
  | paymentAdapter
  | internalCache
  deriving DecidableEq, Repr

inductive FeatureComponent where
  | couponService
  deriving DecidableEq, Repr

inductive ExtendedComponent where
  | paymentApi
  | paymentAdapter
  | internalCache
  | couponService
  | declaredPaymentPort
  deriving DecidableEq, Repr

inductive FeatureView where
  | coupon
  deriving DecidableEq, Repr

def coreGraph : ArchGraph CoreComponent where
  edge := fun _ _ => False

def featureGraph : ArchGraph FeatureComponent where
  edge := fun _ _ => False

def coreEmbedding : CoreComponent -> ExtendedComponent
  | .paymentApi => .paymentApi
  | .paymentAdapter => .paymentAdapter
  | .internalCache => .internalCache

def featureEmbedding : FeatureComponent -> ExtendedComponent
  | .couponService => .couponService

def featureView : Observation ExtendedComponent FeatureView where
  observe := fun _ => .coupon

def featureObservation : Observation FeatureComponent FeatureView where
  observe := fun _ => .coupon

def declaredInterface (x : ExtendedComponent) : Prop :=
  x = .declaredPaymentPort

def coreAllowedStaticEdge (_src _dst : CoreComponent) : Prop :=
  True

def extendedAllowedStaticEdge (src dst : ExtendedComponent) : Prop :=
  ¬ (src = .couponService ∧ dst = .internalCache)

inductive GoodStaticEdge : ExtendedComponent -> ExtendedComponent -> Prop where
  | couponToDeclaredPort :
      GoodStaticEdge .couponService .declaredPaymentPort
  | declaredPortToPaymentApi :
      GoodStaticEdge .declaredPaymentPort .paymentApi

inductive BadStaticEdge : ExtendedComponent -> ExtendedComponent -> Prop where
  | couponToDeclaredPort :
      BadStaticEdge .couponService .declaredPaymentPort
  | declaredPortToPaymentApi :
      BadStaticEdge .declaredPaymentPort .paymentApi
  | hiddenCouponToInternalCache :
      BadStaticEdge .couponService .internalCache

inductive RepairedStaticEdge : ExtendedComponent -> ExtendedComponent -> Prop where
  | couponToDeclaredPort :
      RepairedStaticEdge .couponService .declaredPaymentPort
  | declaredPortToPaymentApi :
      RepairedStaticEdge .declaredPaymentPort .paymentApi
  | declaredPortToInternalCache :
      RepairedStaticEdge .declaredPaymentPort .internalCache

def goodGraph : ArchGraph ExtendedComponent where
  edge := GoodStaticEdge

def badGraph : ArchGraph ExtendedComponent where
  edge := BadStaticEdge

def repairedGraph : ArchGraph ExtendedComponent where
  edge := RepairedStaticEdge

def extensionOf (G : ArchGraph ExtendedComponent) :
    FeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView where
  core := coreGraph
  feature := featureGraph
  extended := G
  coreEmbedding := coreEmbedding
  featureEmbedding := featureEmbedding
  featureView := featureView
  preservesRequiredInvariants := True
  interactionFactorsThroughDeclaredInterfaces := True
  coverageAssumptions := True
  proofObligations := True

def goodExtension :
    FeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView :=
  extensionOf goodGraph

def badExtension :
    FeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView :=
  extensionOf badGraph

def repairedExtension :
    FeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView :=
  extensionOf repairedGraph

theorem extensionOf_featureViewSound (G : ArchGraph ExtendedComponent) :
    FeatureViewSound (extensionOf G) featureObservation := by
  intro f
  cases f
  rfl

theorem good_featureObservationCoverage :
    FeatureObservationCoverage goodExtension featureObservation :=
  featureObservationCoverage_of_featureViewSound
    (extensionOf_featureViewSound goodGraph)

theorem no_core_edge {src dst : CoreComponent} :
    ¬ coreGraph.edge src dst := by
  intro hEdge
  exact hEdge

theorem good_edge_not_crosses_boundary {src dst : ExtendedComponent}
    (hEdge : goodGraph.edge src dst) :
    ¬ CrossesFeatureCoreBoundary goodExtension src dst := by
  intro hCross
  cases hEdge with
  | couponToDeclaredPort =>
      rcases hCross with hFeatureCore | hCoreFeature
      · rcases hFeatureCore with ⟨_hFeature, hCore⟩
        rcases hCore with ⟨core, hCoreEq⟩
        cases core <;> cases hCoreEq
      · rcases hCoreFeature with ⟨hCore, _hFeature⟩
        rcases hCore with ⟨core, hCoreEq⟩
        cases core <;> cases hCoreEq
  | declaredPortToPaymentApi =>
      rcases hCross with hFeatureCore | hCoreFeature
      · rcases hFeatureCore with ⟨hFeature, _hCore⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq
      · rcases hCoreFeature with ⟨_hCore, hFeature⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq

theorem repaired_edge_not_crosses_boundary {src dst : ExtendedComponent}
    (hEdge : repairedGraph.edge src dst) :
    ¬ CrossesFeatureCoreBoundary repairedExtension src dst := by
  intro hCross
  cases hEdge with
  | couponToDeclaredPort =>
      rcases hCross with hFeatureCore | hCoreFeature
      · rcases hFeatureCore with ⟨_hFeature, hCore⟩
        rcases hCore with ⟨core, hCoreEq⟩
        cases core <;> cases hCoreEq
      · rcases hCoreFeature with ⟨hCore, _hFeature⟩
        rcases hCore with ⟨core, hCoreEq⟩
        cases core <;> cases hCoreEq
  | declaredPortToPaymentApi =>
      rcases hCross with hFeatureCore | hCoreFeature
      · rcases hFeatureCore with ⟨hFeature, _hCore⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq
      · rcases hCoreFeature with ⟨_hCore, hFeature⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq
  | declaredPortToInternalCache =>
      rcases hCross with hFeatureCore | hCoreFeature
      · rcases hFeatureCore with ⟨hFeature, _hCore⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq
      · rcases hCoreFeature with ⟨_hCore, hFeature⟩
        rcases hFeature with ⟨feature, hFeatureEq⟩
        cases feature
        cases hFeatureEq

theorem good_no_forbidden_static_edge :
    NoNewForbiddenStaticEdge goodExtension.extended extendedAllowedStaticEdge := by
  intro src dst hEdge
  cases hEdge <;> intro hForbidden <;> rcases hForbidden with ⟨hSrc, hDst⟩ <;>
    cases hSrc <;> cases hDst

theorem repaired_no_forbidden_static_edge :
    NoNewForbiddenStaticEdge repairedExtension.extended extendedAllowedStaticEdge := by
  intro src dst hEdge
  cases hEdge <;> intro hForbidden <;> rcases hForbidden with ⟨hSrc, hDst⟩ <;>
    cases hSrc <;> cases hDst

theorem extensionOf_embedding_policy_preserved (G : ArchGraph ExtendedComponent) :
    EmbeddingPolicyPreserved (extensionOf G) coreAllowedStaticEdge
      extendedAllowedStaticEdge := by
  intro src dst _hAllowed hForbidden
  rcases hForbidden with ⟨hSrc, hDst⟩
  cases src <;> cases hSrc

def goodStaticSplitFeatureExtension :
    StaticSplitFeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView where
  extension := goodExtension
  declaredInterface := declaredInterface
  coreAllowedStaticEdge := coreAllowedStaticEdge
  extendedAllowedStaticEdge := extendedAllowedStaticEdge
  coreEdgesPreserved := by
    intro src dst hEdge
    exact False.elim hEdge
  declaredInterfaceFactorization := by
    intro src dst hEdge hCross
    exact False.elim (good_edge_not_crosses_boundary hEdge hCross)
  noNewForbiddenStaticEdge := good_no_forbidden_static_edge
  policyPreserved := extensionOf_embedding_policy_preserved goodGraph

theorem good_selectedStaticSplitFeatureExtension :
    SelectedStaticSplitExtension goodExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  selectedStaticSplitExtension_of_staticSplitFeatureExtension
    goodStaticSplitFeatureExtension

def repairedStaticSplitFeatureExtension :
    StaticSplitFeatureExtension CoreComponent FeatureComponent ExtendedComponent FeatureView where
  extension := repairedExtension
  declaredInterface := declaredInterface
  coreAllowedStaticEdge := coreAllowedStaticEdge
  extendedAllowedStaticEdge := extendedAllowedStaticEdge
  coreEdgesPreserved := by
    intro src dst hEdge
    exact False.elim hEdge
  declaredInterfaceFactorization := by
    intro src dst hEdge hCross
    exact False.elim (repaired_edge_not_crosses_boundary hEdge hCross)
  noNewForbiddenStaticEdge := repaired_no_forbidden_static_edge
  policyPreserved := extensionOf_embedding_policy_preserved repairedGraph

theorem repaired_selectedStaticSplitFeatureExtension :
    SelectedStaticSplitExtension repairedExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  selectedStaticSplitExtension_of_staticSplitFeatureExtension
    repairedStaticSplitFeatureExtension

theorem hidden_dependency_crosses_boundary :
    CrossesFeatureCoreBoundary badExtension .couponService .internalCache := by
  left
  constructor
  · exact FeatureExtension.featureOwned_featureEmbedding badExtension
      FeatureComponent.couponService
  · exact FeatureExtension.coreEmbedded_coreEmbedding badExtension
      CoreComponent.internalCache

theorem hidden_dependency_not_declared_factor :
    ¬ EdgeFactorsThroughDeclaredInterface badExtension.extended declaredInterface
      .couponService .internalCache := by
  intro hFactor
  rcases hFactor with ⟨iface, hDeclared, _hSrcIface, hIfaceDst⟩
  unfold declaredInterface at hDeclared
  cases hDeclared
  cases hIfaceDst

def hiddenDependencyWitness :
    StaticExtensionWitness badExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  StaticExtensionWitness.unfactoredBoundaryEdge .couponService .internalCache
    BadStaticEdge.hiddenCouponToInternalCache
    hidden_dependency_crosses_boundary
    hidden_dependency_not_declared_factor

theorem hiddenDependencyWitnessExists :
    StaticExtensionWitnessExists badExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  ⟨hiddenDependencyWitness⟩

theorem bad_not_selectedStaticSplitFeatureExtension :
    ¬ SelectedStaticSplitExtension badExtension declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  not_selectedStaticSplitExtension_of_staticExtensionWitness hiddenDependencyWitness

end CouponStaticDependencyExample

/-
Small positive example for selected split-extension lifting.

The example proves one chosen feature transition through an observation-relative
section package and a local compatibility package. It intentionally does not
claim strict section equality, unique decomposition of all extended components,
or automatic lifting for all feature steps.
-/
namespace SelectedSplitExtensionLiftingExample

inductive CoreComponent where
  | checkoutApi
  | auditLog
  deriving DecidableEq, Repr

inductive FeatureComponent where
  | couponDraft
  | couponApplied
  deriving DecidableEq, Repr

inductive ExtendedComponent where
  | checkoutApi
  | auditLog
  | couponDraft
  | couponApplied
  | declaredCouponPort
  deriving DecidableEq, Repr

inductive FeatureView where
  | draft
  | applied
  deriving DecidableEq, Repr

inductive CoreView where
  | checkout
  deriving DecidableEq, Repr

def coreGraph : ArchGraph CoreComponent where
  edge := fun _ _ => False

inductive FeatureEdge : FeatureComponent -> FeatureComponent -> Prop where
  | draftToApplied :
      FeatureEdge .couponDraft .couponApplied

inductive ExtendedEdge : ExtendedComponent -> ExtendedComponent -> Prop where
  | draftToApplied :
      ExtendedEdge .couponDraft .couponApplied
  | appliedToDeclaredPort :
      ExtendedEdge .couponApplied .declaredCouponPort

def featureGraph : ArchGraph FeatureComponent where
  edge := FeatureEdge

def extendedGraph : ArchGraph ExtendedComponent where
  edge := ExtendedEdge

def coreEmbedding : CoreComponent -> ExtendedComponent
  | .checkoutApi => .checkoutApi
  | .auditLog => .auditLog

def featureEmbedding : FeatureComponent -> ExtendedComponent
  | .couponDraft => .couponDraft
  | .couponApplied => .couponApplied

def featureView : Observation ExtendedComponent FeatureView where
  observe
    | .couponDraft => .draft
    | .couponApplied => .applied
    | .checkoutApi => .applied
    | .auditLog => .applied
    | .declaredCouponPort => .applied

def featureObservation : Observation FeatureComponent FeatureView where
  observe
    | .couponDraft => .draft
    | .couponApplied => .applied

def coreObservation : Observation CoreComponent CoreView where
  observe := fun _ => .checkout

def coreRetraction : ExtendedComponent -> CoreComponent
  | .checkoutApi => .checkoutApi
  | .auditLog => .auditLog
  | .couponDraft => .checkoutApi
  | .couponApplied => .checkoutApi
  | .declaredCouponPort => .checkoutApi

def extension :
    FeatureExtension CoreComponent FeatureComponent ExtendedComponent
      FeatureView where
  core := coreGraph
  feature := featureGraph
  extended := extendedGraph
  coreEmbedding := coreEmbedding
  featureEmbedding := featureEmbedding
  featureView := featureView
  preservesRequiredInvariants := True
  interactionFactorsThroughDeclaredInterfaces := True
  coverageAssumptions := True
  proofObligations := True

theorem featureViewSound :
    FeatureViewSound extension featureObservation := by
  intro f
  cases f <;> rfl

def featureViewSectionPackage :
    FeatureViewSectionPackage extension featureObservation :=
  featureViewSectionPackage_of_featureViewSound extension featureObservation
    featureViewSound

theorem featureViewSectionPackage_observes (f : FeatureComponent) :
    extension.featureView.observe
        (featureViewSectionPackage.featureSection f) =
      featureObservation.observe f :=
  featureViewSectionPackage.featureSection_observes f

def liftingData :
    SplitExtensionLiftingData CoreComponent FeatureComponent ExtendedComponent
      FeatureView CoreView where
  extension := extension
  featureObservation := featureObservation
  coreObservation := coreObservation
  featureSection := featureEmbedding
  coreRetraction := coreRetraction
  featureSectionLaw := featureViewSound
  observationalCoreRetraction := by
    intro c
    cases c <;> rfl
  interfaceFactorization := trivial
  preservesRequiredInvariants := trivial

def selectedFeatureStep : SelectedFeatureStep FeatureComponent where
  source := .couponDraft
  target := .couponApplied

def featureInvariant (_f : FeatureComponent) : Prop :=
  True

def coreInvariant (c : CoreComponent) : Prop :=
  c = .checkoutApi

theorem lawfulSelectedFeatureStep :
    LawfulFeatureStep featureInvariant selectedFeatureStep := by
  intro _h
  trivial

theorem compatibleWithInterface :
    CompatibleWithInterface liftingData coreInvariant selectedFeatureStep where
  liftedEdge := ExtendedEdge.draftToApplied
  interfaceFactorization := trivial
  coverageAssumptions := trivial
  coreInvariantPreserved := by
    intro _h
    rfl

theorem selectedStepLifts :
    ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      LiftsFeatureStep liftingData selectedFeatureStep liftedStep ∧
        PreservesCoreInvariants liftingData coreInvariant liftedStep :=
  SplitExtensionLifting liftingData selectedFeatureStep
    lawfulSelectedFeatureStep compatibleWithInterface

theorem selectedStepPreservationPackage :
    ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      SplitExtensionLiftingPreservationPackage
        liftingData featureInvariant coreInvariant selectedFeatureStep
        liftedStep :=
  SplitExtensionLifting_preservationPackage liftingData selectedFeatureStep
    lawfulSelectedFeatureStep compatibleWithInterface

theorem selectedStep_coreInvariant_target_of_source :
    ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      coreInvariant (liftingData.coreRetraction liftedStep.source) ->
        coreInvariant (liftingData.coreRetraction liftedStep.target) := by
  rcases selectedStepPreservationPackage with ⟨liftedStep, hPackage⟩
  exact
    ⟨liftedStep,
      SplitExtensionLiftingPreservationPackage.coreInvariant_target_of_source
        hPackage⟩

theorem selectedStep_liftedSource_observes :
    ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      liftingData.extension.featureView.observe liftedStep.source =
        liftingData.featureObservation.observe selectedFeatureStep.source := by
  rcases selectedStepPreservationPackage with ⟨liftedStep, hPackage⟩
  exact
    ⟨liftedStep,
      SplitExtensionLiftingPreservationPackage.liftedFeatureSource_observes
        hPackage⟩

theorem selectedStep_liftedTarget_observes :
    ∃ liftedStep : LiftedExtensionStep ExtendedComponent,
      liftingData.extension.featureView.observe liftedStep.target =
        liftingData.featureObservation.observe selectedFeatureStep.target := by
  rcases selectedStepPreservationPackage with ⟨liftedStep, hPackage⟩
  exact
    ⟨liftedStep,
      SplitExtensionLiftingPreservationPackage.liftedFeatureTarget_observes
        hPackage⟩

end SelectedSplitExtensionLiftingExample

end Formal.Arch
