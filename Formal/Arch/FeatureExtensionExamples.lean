import Formal.Arch.SplitExtensionLifting

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

end Formal.Arch
