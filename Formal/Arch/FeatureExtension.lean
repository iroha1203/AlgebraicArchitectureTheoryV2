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

/--
Selected static split condition for a fixed feature extension and fixed policy
parameters.

This predicate is the unbundled form of `StaticSplitFeatureExtension`: it is
useful when diagnostic theorems need to talk about failure of one selected
static split package without claiming runtime, semantic, or extractor
completeness.
-/
structure SelectedStaticSplitExtension
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop) : Prop where
  coreEdgesPreserved : CoreEdgesPreserved X
  declaredInterfaceFactorization :
    DeclaredInterfaceFactorization X declaredInterface
  noNewForbiddenStaticEdge :
    NoNewForbiddenStaticEdge X.extended extendedAllowedStaticEdge
  policyPreserved :
    EmbeddingPolicyPreserved X coreAllowedStaticEdge extendedAllowedStaticEdge

/-- The bundled static split schema supplies the selected static split predicate. -/
theorem selectedStaticSplitExtension_of_staticSplitFeatureExtension
    (S : StaticSplitFeatureExtension Core Feature Extended FeatureView) :
    SelectedStaticSplitExtension S.extension S.declaredInterface
      S.coreAllowedStaticEdge S.extendedAllowedStaticEdge :=
  ⟨S.coreEdgesPreserved, S.declaredInterfaceFactorization,
    S.noNewForbiddenStaticEdge, S.policyPreserved⟩

/-- A selected static split predicate can be bundled back into the existing schema. -/
def staticSplitFeatureExtension_of_selectedStaticSplitExtension
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop)
    (hSplit :
      SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge) :
    StaticSplitFeatureExtension Core Feature Extended FeatureView where
  extension := X
  declaredInterface := declaredInterface
  coreAllowedStaticEdge := coreAllowedStaticEdge
  extendedAllowedStaticEdge := extendedAllowedStaticEdge
  coreEdgesPreserved := hSplit.coreEdgesPreserved
  declaredInterfaceFactorization := hSplit.declaredInterfaceFactorization
  noNewForbiddenStaticEdge := hSplit.noNewForbiddenStaticEdge
  policyPreserved := hSplit.policyPreserved

/--
Selected diagnostic witnesses for failure of the static split package.

The constructors mirror the current Lean static split kernel: core edge
preservation, declared interface factorization, no-new-forbidden-edge, and
embedding policy preservation. They are intentionally static-only.
-/
inductive StaticExtensionWitness
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop) where
  | missingCoreEdge (src dst : Core)
      (coreEdge : X.core.edge src dst)
      (missingExtendedEdge :
        ¬ X.extended.edge (X.coreEmbedding src) (X.coreEmbedding dst))
  | unfactoredBoundaryEdge (src dst : Extended)
      (extendedEdge : X.extended.edge src dst)
      (crossesBoundary : CrossesFeatureCoreBoundary X src dst)
      (missingDeclaredFactor :
        ¬ EdgeFactorsThroughDeclaredInterface X.extended declaredInterface src dst)
  | forbiddenStaticEdge (src dst : Extended)
      (extendedEdge : X.extended.edge src dst)
      (forbidden : ¬ extendedAllowedStaticEdge src dst)
  | embeddingPolicyBroken (src dst : Core)
      (coreAllowed : coreAllowedStaticEdge src dst)
      (extendedForbidden :
        ¬ extendedAllowedStaticEdge (X.coreEmbedding src) (X.coreEmbedding dst))

/-- Selected static witness existence, kept separate from any global universe. -/
def StaticExtensionWitnessExists
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop) : Prop :=
  Nonempty
    (StaticExtensionWitness X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge)

/--
Coverage/exactness premise for the selected static diagnostic universe.

This is a bounded assumption: it states that the selected static witness family
covers failures of the selected static split predicate. It does not assert that
all runtime, semantic, or extractor-level failures are represented.
-/
def StaticSplitFailureCoverage
    (X : FeatureExtension Core Feature Extended FeatureView)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop) : Prop :=
  ¬ SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge ->
    StaticExtensionWitnessExists X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge

/--
A selected static witness is sound: it refutes the corresponding selected
static split predicate.
-/
theorem not_selectedStaticSplitExtension_of_staticExtensionWitness
    {X : FeatureExtension Core Feature Extended FeatureView}
    {declaredInterface : Extended -> Prop}
    {coreAllowedStaticEdge : Core -> Core -> Prop}
    {extendedAllowedStaticEdge : Extended -> Extended -> Prop}
    (witness :
      StaticExtensionWitness X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge) :
    ¬ SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge := by
  intro hSplit
  cases witness with
  | missingCoreEdge src dst coreEdge missingExtendedEdge =>
      exact missingExtendedEdge (hSplit.coreEdgesPreserved coreEdge)
  | unfactoredBoundaryEdge src dst extendedEdge crossesBoundary missingDeclaredFactor =>
      exact missingDeclaredFactor
        (hSplit.declaredInterfaceFactorization extendedEdge crossesBoundary)
  | forbiddenStaticEdge src dst extendedEdge forbidden =>
      exact forbidden (hSplit.noNewForbiddenStaticEdge extendedEdge)
  | embeddingPolicyBroken src dst coreAllowed extendedForbidden =>
      exact extendedForbidden (hSplit.policyPreserved coreAllowed)

/-- Soundness-only form for selected static witness existence. -/
theorem not_selectedStaticSplitExtension_of_staticExtensionWitnessExists
    {X : FeatureExtension Core Feature Extended FeatureView}
    {declaredInterface : Extended -> Prop}
    {coreAllowedStaticEdge : Core -> Core -> Prop}
    {extendedAllowedStaticEdge : Extended -> Extended -> Prop}
    (hWitness :
      StaticExtensionWitnessExists X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge) :
    ¬ SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge := by
  rcases hWitness with ⟨witness⟩
  exact not_selectedStaticSplitExtension_of_staticExtensionWitness witness

/--
Bounded completeness: under the selected coverage/exactness premise, a failure
of the selected static split predicate has a selected static witness.
-/
theorem staticExtensionWitnessExists_of_not_selectedStaticSplitExtension
    {X : FeatureExtension Core Feature Extended FeatureView}
    {declaredInterface : Extended -> Prop}
    {coreAllowedStaticEdge : Core -> Core -> Prop}
    {extendedAllowedStaticEdge : Extended -> Extended -> Prop}
    (hCoverage :
      StaticSplitFailureCoverage X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge)
    (hNonSplit :
      ¬ SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge) :
    StaticExtensionWitnessExists X declaredInterface coreAllowedStaticEdge
      extendedAllowedStaticEdge :=
  hCoverage hNonSplit

/--
Soundness plus bounded completeness for the selected static witness universe.

The equivalence is relative to `StaticSplitFailureCoverage`; it is not a global
claim about unmeasured runtime edges, semantic diagrams, or extractor
completeness.
-/
theorem staticExtensionWitnessExists_iff_not_selectedStaticSplitExtension
    {X : FeatureExtension Core Feature Extended FeatureView}
    {declaredInterface : Extended -> Prop}
    {coreAllowedStaticEdge : Core -> Core -> Prop}
    {extendedAllowedStaticEdge : Extended -> Extended -> Prop}
    (hCoverage :
      StaticSplitFailureCoverage X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge) :
    StaticExtensionWitnessExists X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge ↔
      ¬ SelectedStaticSplitExtension X declaredInterface coreAllowedStaticEdge
        extendedAllowedStaticEdge := by
  constructor
  · exact not_selectedStaticSplitExtension_of_staticExtensionWitnessExists
  · exact staticExtensionWitnessExists_of_not_selectedStaticSplitExtension hCoverage

end Formal.Arch
