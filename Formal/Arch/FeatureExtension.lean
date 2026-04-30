import Formal.Arch.Graph
import Formal.Arch.Observation

namespace Formal.Arch

universe u v w q r s

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
Identity feature extension: no new feature components are introduced, and the
extended graph is definitionally the original core graph.
-/
def identityFeatureExtension (G : ArchGraph Core) :
    FeatureExtension Core PEmpty Core Core where
  core := G
  feature := { edge := fun _ _ => False }
  extended := G
  coreEmbedding := id
  featureEmbedding := PEmpty.elim
  featureView := { observe := id }
  preservesRequiredInvariants := True
  interactionFactorsThroughDeclaredInterfaces := True
  coverageAssumptions := True
  proofObligations := True

/-- Identity extensions preserve core edges by reflexivity. -/
theorem identityFeatureExtension_coreEdgesPreserved
    (G : ArchGraph Core) :
    CoreEdgesPreserved (identityFeatureExtension G) := by
  intro _src _dst hEdge
  exact hEdge

/-- With no feature components, an identity extension has no feature/core boundary. -/
theorem identityFeatureExtension_not_crossesFeatureCoreBoundary
    (G : ArchGraph Core) (src dst : Core) :
    ¬ CrossesFeatureCoreBoundary (identityFeatureExtension G) src dst := by
  intro hCross
  rcases hCross with hFeatureCore | hCoreFeature
  · rcases hFeatureCore with ⟨hFeature, _hCore⟩
    rcases hFeature with ⟨feature, _hFeatureEq⟩
    cases feature
  · rcases hCoreFeature with ⟨_hCore, hFeature⟩
    rcases hFeature with ⟨feature, _hFeatureEq⟩
    cases feature

/--
Identity static split package.

The only substantive premise is that the existing graph already satisfies the
selected static-edge policy; runtime and semantic flatness remain out of scope.
-/
def identityStaticSplitFeatureExtension
    (G : ArchGraph Core)
    (allowedStaticEdge : Core -> Core -> Prop)
    (hAllowed : ∀ {src dst : Core}, G.edge src dst -> allowedStaticEdge src dst) :
    StaticSplitFeatureExtension Core PEmpty Core Core where
  extension := identityFeatureExtension G
  declaredInterface := fun _ => False
  coreAllowedStaticEdge := allowedStaticEdge
  extendedAllowedStaticEdge := allowedStaticEdge
  coreEdgesPreserved := identityFeatureExtension_coreEdgesPreserved G
  declaredInterfaceFactorization := by
    intro src dst _hEdge hCross
    exact False.elim
      (identityFeatureExtension_not_crossesFeatureCoreBoundary G src dst hCross)
  noNewForbiddenStaticEdge := by
    intro _src _dst hEdge
    exact hAllowed hEdge
  policyPreserved := by
    intro _src _dst hPolicy
    exact hPolicy

/-- Selected form of the identity static split package. -/
theorem selectedStaticSplitExtension_identity
    (G : ArchGraph Core)
    (allowedStaticEdge : Core -> Core -> Prop)
    (hAllowed : ∀ {src dst : Core}, G.edge src dst -> allowedStaticEdge src dst) :
    SelectedStaticSplitExtension (identityFeatureExtension G) (fun _ => False)
      allowedStaticEdge allowedStaticEdge :=
  selectedStaticSplitExtension_of_staticSplitFeatureExtension
    (identityStaticSplitFeatureExtension G allowedStaticEdge hAllowed)

/--
Composition of two feature extensions.

The first extension is read as part of the core of the second extension. Feature
components from the first stage are embedded through the second core embedding,
while second-stage feature components keep their own embedding.
-/
def composeFeatureExtension
    {Middle : Type r} {Feature₂ : Type s} {FeatureView₂ : Type q}
    {FeatureView₁ : Type w}
    (left : FeatureExtension Core Feature Middle FeatureView₁)
    (right : FeatureExtension Middle Feature₂ Extended FeatureView₂) :
    FeatureExtension Core (Sum Feature Feature₂) Extended
      (Sum FeatureView₁ FeatureView₂) where
  core := left.core
  feature := {
    edge := fun src dst =>
      match src, dst with
      | Sum.inl src₁, Sum.inl dst₁ => left.feature.edge src₁ dst₁
      | Sum.inr src₂, Sum.inr dst₂ => right.feature.edge src₂ dst₂
      | _, _ => False
  }
  extended := right.extended
  coreEmbedding := fun c => right.coreEmbedding (left.coreEmbedding c)
  featureEmbedding := fun
    | Sum.inl f => right.coreEmbedding (left.featureEmbedding f)
    | Sum.inr f => right.featureEmbedding f
  featureView := { observe := fun x => Sum.inr (right.featureView.observe x) }
  preservesRequiredInvariants :=
    left.preservesRequiredInvariants ∧ right.preservesRequiredInvariants
  interactionFactorsThroughDeclaredInterfaces :=
    left.interactionFactorsThroughDeclaredInterfaces ∧
      right.interactionFactorsThroughDeclaredInterfaces
  coverageAssumptions := left.coverageAssumptions ∧ right.coverageAssumptions
  proofObligations := left.proofObligations ∧ right.proofObligations

/--
Explicit assumptions needed to compose two static split packages.

The theorem intentionally keeps graph compatibility, interface factorization,
and policy transport as premises. This avoids claiming an unconditional global
composition law for runtime, semantic, or extractor behavior.
-/
structure StaticSplitCompositionAssumptions
    {Middle : Type r} {Feature₂ : Type s} {FeatureView₁ : Type w}
    {FeatureView₂ : Type q}
    (left : StaticSplitExtension Core Feature Middle FeatureView₁)
    (right : StaticSplitExtension Middle Feature₂ Extended FeatureView₂)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop) : Prop where
  coreGraphCompatible :
    ∀ {src dst : Middle}, left.extension.extended.edge src dst ->
      right.extension.core.edge src dst
  declaredInterfaceFactorization :
    DeclaredInterfaceFactorization
      (composeFeatureExtension left.extension right.extension) declaredInterface
  corePolicyToLeft :
    ∀ {src dst : Core}, coreAllowedStaticEdge src dst ->
      left.coreAllowedStaticEdge src dst
  leftPolicyEmbeddedByRight :
    ∀ {src dst : Middle}, left.extendedAllowedStaticEdge src dst ->
      right.extendedAllowedStaticEdge
        (right.extension.coreEmbedding src) (right.extension.coreEmbedding dst)
  rightPolicyToComposed :
    ∀ {src dst : Extended}, right.extendedAllowedStaticEdge src dst ->
      extendedAllowedStaticEdge src dst

/--
Interface-compatible composition of static split extensions.

This constructs the bundled composed static split extension under explicit
compatibility premises. It does not assert semantic flatness, runtime flatness,
or unconditional global composition.
-/
def staticSplitFeatureExtension_compose
    {Middle : Type r} {Feature₂ : Type s} {FeatureView₁ : Type w}
    {FeatureView₂ : Type q}
    (left : StaticSplitExtension Core Feature Middle FeatureView₁)
    (right : StaticSplitExtension Middle Feature₂ Extended FeatureView₂)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop)
    (hCompat :
      StaticSplitCompositionAssumptions left right declaredInterface
        coreAllowedStaticEdge extendedAllowedStaticEdge) :
    StaticSplitFeatureExtension Core (Sum Feature Feature₂) Extended
      (Sum FeatureView₁ FeatureView₂) where
  extension := composeFeatureExtension left.extension right.extension
  declaredInterface := declaredInterface
  coreAllowedStaticEdge := coreAllowedStaticEdge
  extendedAllowedStaticEdge := extendedAllowedStaticEdge
  coreEdgesPreserved := by
    intro src dst hEdge
    exact right.coreEdgesPreserved
      (hCompat.coreGraphCompatible (left.coreEdgesPreserved hEdge))
  declaredInterfaceFactorization := hCompat.declaredInterfaceFactorization
  noNewForbiddenStaticEdge := by
    intro src dst hEdge
    exact hCompat.rightPolicyToComposed
      (right.noNewForbiddenStaticEdge hEdge)
  policyPreserved := by
    intro src dst hCoreAllowed
    exact hCompat.rightPolicyToComposed
      (hCompat.leftPolicyEmbeddedByRight
        (left.policyPreserved
          (hCompat.corePolicyToLeft hCoreAllowed)))

/-- Selected predicate form of static split composition. -/
theorem selectedStaticSplitExtension_compose
    {Middle : Type r} {Feature₂ : Type s} {FeatureView₁ : Type w}
    {FeatureView₂ : Type q}
    (left : StaticSplitExtension Core Feature Middle FeatureView₁)
    (right : StaticSplitExtension Middle Feature₂ Extended FeatureView₂)
    (declaredInterface : Extended -> Prop)
    (coreAllowedStaticEdge : Core -> Core -> Prop)
    (extendedAllowedStaticEdge : Extended -> Extended -> Prop)
    (hCompat :
      StaticSplitCompositionAssumptions left right declaredInterface
        coreAllowedStaticEdge extendedAllowedStaticEdge) :
    SelectedStaticSplitExtension
      (composeFeatureExtension left.extension right.extension)
      declaredInterface coreAllowedStaticEdge extendedAllowedStaticEdge :=
  selectedStaticSplitExtension_of_staticSplitFeatureExtension
    (staticSplitFeatureExtension_compose left right declaredInterface
      coreAllowedStaticEdge extendedAllowedStaticEdge hCompat)

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
