import Formal.Arch.Graph
import Formal.Arch.Observation

namespace Formal.Arch

universe u v w q

/--
Feature-extension data for an architecture change.

`featureView` is an observation/quotient map from the extended architecture to
the selected feature view. It is not required to recover implementation detail.
-/
structure FeatureExtension (Core : Type u) (Feature : Type v)
    (Extended : Type w) (FeatureView : Type q) where
  core : ArchGraph Core
  feature : ArchGraph Feature
  extended : ArchGraph Extended
  coreEmbedding : Core -> Extended
  featureEmbedding : Feature -> Extended
  featureView : Observation Extended FeatureView
  preservesRequiredInvariants : Prop
  interactionFactorsThroughDeclaredInterfaces : Prop
  coverageAssumptions : Prop
  proofObligations : Prop

namespace FeatureExtension

variable {Core : Type u} {Feature : Type v} {Extended : Type w}
  {FeatureView : Type q}

/-- Extended components that come from the existing core. -/
def CoreEmbedded (X : FeatureExtension Core Feature Extended FeatureView)
    (x : Extended) : Prop :=
  ∃ c : Core, X.coreEmbedding c = x

/-- Extended components that are owned by the added feature. -/
def FeatureOwned (X : FeatureExtension Core Feature Extended FeatureView)
    (x : Extended) : Prop :=
  ∃ f : Feature, X.featureEmbedding f = x

/-- Every declared feature component has an owner witness in the extension. -/
theorem featureOwned_featureEmbedding
    (X : FeatureExtension Core Feature Extended FeatureView) (f : Feature) :
    FeatureOwned X (X.featureEmbedding f) :=
  ⟨f, rfl⟩

/-- Every declared core component has an embedding witness in the extension. -/
theorem coreEmbedded_coreEmbedding
    (X : FeatureExtension Core Feature Extended FeatureView) (c : Core) :
    CoreEmbedded X (X.coreEmbedding c) :=
  ⟨c, rfl⟩

end FeatureExtension

/-- Existing static edges are preserved by the core embedding. -/
def CoreEdgesPreserved
    (X : FeatureExtension Core Feature Extended FeatureView) : Prop :=
  ∀ {c d : Core}, X.core.edge c d ->
    X.extended.edge (X.coreEmbedding c) (X.coreEmbedding d)

/-- An extended dependency edge factors through a declared interface component. -/
def EdgeFactorsThroughDeclaredInterface (G : ArchGraph Extended)
    (declaredInterface : Extended -> Prop) (src dst : Extended) : Prop :=
  ∃ iface : Extended,
    declaredInterface iface ∧ G.edge src iface ∧ G.edge iface dst

/-- The edge crosses between feature-owned and core-embedded components. -/
def CrossesFeatureCoreBoundary
    (X : FeatureExtension Core Feature Extended FeatureView)
    (src dst : Extended) : Prop :=
  (FeatureExtension.FeatureOwned X src ∧ FeatureExtension.CoreEmbedded X dst) ∨
    (FeatureExtension.CoreEmbedded X src ∧ FeatureExtension.FeatureOwned X dst)

/--
Static feature/core interactions factor through declared interface components.

This is an explicit witness condition, not an edge-count metric.
-/
def DeclaredInterfaceFactorization
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop) : Prop :=
  ∀ {src dst : Extended}, X.extended.edge src dst ->
    CrossesFeatureCoreBoundary X src dst ->
      EdgeFactorsThroughDeclaredInterface X.extended declaredInterface src dst

/-- No extended static edge violates the supplied static edge policy. -/
def NoNewForbiddenStaticEdge (G : ArchGraph Extended)
    (allowedStaticEdge : Extended -> Extended -> Prop) : Prop :=
  ∀ {src dst : Extended}, G.edge src dst -> allowedStaticEdge src dst

/-- Core edge policy is preserved after embedding into the extended graph. -/
def EmbeddingPolicyPreserved
    (X : FeatureExtension Core Feature Extended FeatureView)
    (coreAllowed : Core -> Core -> Prop)
    (extendedAllowed : Extended -> Extended -> Prop) : Prop :=
  ∀ {c d : Core}, coreAllowed c d ->
    extendedAllowed (X.coreEmbedding c) (X.coreEmbedding d)

/--
Static split feature extension.

This is the conservative static kernel: it does not claim runtime or semantic
split soundness, and it keeps coverage/proof obligations as explicit fields of
the underlying `FeatureExtension`.
-/
structure StaticSplitFeatureExtension (Core : Type u) (Feature : Type v)
    (Extended : Type w) (FeatureView : Type q) where
  extension : FeatureExtension Core Feature Extended FeatureView
  declaredInterface : Extended -> Prop
  coreAllowedStaticEdge : Core -> Core -> Prop
  extendedAllowedStaticEdge : Extended -> Extended -> Prop
  coreEdgesPreserved : CoreEdgesPreserved extension
  declaredInterfaceFactorization :
    DeclaredInterfaceFactorization extension declaredInterface
  noNewForbiddenStaticEdge :
    NoNewForbiddenStaticEdge extension.extended extendedAllowedStaticEdge
  policyPreserved :
    EmbeddingPolicyPreserved extension coreAllowedStaticEdge extendedAllowedStaticEdge

/-- Short name used by the extension-preservation roadmap. -/
abbrev StaticSplitExtension :=
  StaticSplitFeatureExtension

end Formal.Arch
