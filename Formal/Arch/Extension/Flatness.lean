import Formal.Arch.Extension.FeatureExtension
import Formal.Arch.Signature.SignatureLawfulness
import Formal.Arch.Law.StateEffect

namespace Formal.Arch

universe u v w q r

/--
Three-layer flatness data for one architecture.

The static layer reuses the existing Signature-integrated law model. Runtime
and semantic layers are kept explicit so that unmeasured axes cannot be treated
as zero without a coverage premise.
-/
structure ArchitectureFlatnessModel (C : Type u) (A : Type v)
    (StaticObs : Type w) (SemanticExpr : Type q)
    (SemanticObs : Type r) where
  static : StaticDependencyGraph C
  runtime : RuntimeDependencyGraph C
  projection : InterfaceProjection C A
  abstractStatic : AbstractGraph A
  staticObservation : Observation C StaticObs
  boundaryAllowed : C -> C -> Prop
  abstractionAllowed : C -> C -> Prop
  runtimeAllowed : C -> C -> Prop
  semantic : Semantics SemanticExpr SemanticObs
  requiredSemantic : RequiredDiagram SemanticExpr -> Prop
  measuredSemantic : List (RequiredDiagram SemanticExpr)

namespace ArchitectureFlatnessModel

variable {C : Type u} {A : Type v} {StaticObs : Type w}
  {SemanticExpr : Type q} {SemanticObs : Type r}

/-- The static-law view of a flatness model relative to a finite universe. -/
def staticLawModel
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) :
    ArchitectureSignature.ArchitectureLawModel C A StaticObs where
  G := X.static
  π := X.projection
  GA := X.abstractStatic
  O := X.staticObservation
  U := U
  boundaryAllowed := X.boundaryAllowed
  abstractionAllowed := X.abstractionAllowed
  lspPairClosed := by
    intro x y _hSameAbstraction
    exact ⟨U.covers x, U.covers y⟩

end ArchitectureFlatnessModel

/-- The supplied universe covers the static dependency evidence used by flatness. -/
def StaticCoverageComplete
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  ∀ {c d : C}, X.static.edge c d -> c ∈ U.components ∧ d ∈ U.components

/-- `ComponentUniverse` already carries static edge closure. -/
theorem staticCoverageComplete_of_componentUniverse
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) :
    StaticCoverageComplete X U := by
  intro c d hEdge
  exact U.edgeClosed hEdge

/-- Static flatness within a finite universe is the existing static lawfulness package. -/
def StaticFlatWithin
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  ArchitectureSignature.ArchitectureLawful
    (ArchitectureFlatnessModel.staticLawModel X U)

/-- Runtime dependency evidence is covered by the supplied component universe. -/
def RuntimeCoverageComplete
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  ∀ {c d : C}, X.runtime.edge c d -> c ∈ U.components ∧ d ∈ U.components

/--
Runtime flatness is policy soundness for runtime edges whose endpoints are in
the measured universe.
-/
def RuntimeFlatWithin
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  ∀ {c d : C}, c ∈ U.components -> d ∈ U.components ->
    X.runtime.edge c d -> X.runtimeAllowed c d

/-- The measured semantic diagram list covers every required semantic diagram. -/
def SemanticCoverageComplete
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  CoversRequired X.requiredSemantic X.measuredSemantic

/-- Semantic flatness within the measured semantic diagram universe. -/
def SemanticFlatWithin
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  DiagramLawfulByList X.semantic X.measuredSemantic

/--
Selected runtime interaction protection.

This is the bounded runtime split premise: every measured runtime interaction
that appears in the selected universe satisfies the target runtime policy. It
does not assert telemetry completeness outside `U`.
-/
def RuntimeInteractionProtected
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  ∀ {src dst : C}, X.runtime.edge src dst ->
    src ∈ U.components -> dst ∈ U.components -> X.runtimeAllowed src dst

/--
Runtime interaction protection discharges bounded runtime flatness once the
selected runtime universe is the one used by the flatness model.
-/
theorem runtimeFlatWithin_of_runtimeInteractionProtected
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (_hCoverage : RuntimeCoverageComplete X U)
    (hProtected : RuntimeInteractionProtected X U) :
    RuntimeFlatWithin X U := by
  intro src dst hSrc hDst hEdge
  exact hProtected hEdge hSrc hDst

/-- Bounded runtime flatness can be read as selected runtime protection. -/
theorem runtimeInteractionProtected_of_runtimeFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (hFlat : RuntimeFlatWithin X U) :
    RuntimeInteractionProtected X U := by
  intro src dst hEdge hSrc hDst
  exact hFlat hSrc hDst hEdge

/-- Runtime protection and bounded runtime flatness are equivalent on `U`. -/
theorem runtimeInteractionProtected_iff_runtimeFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (hCoverage : RuntimeCoverageComplete X U) :
    RuntimeInteractionProtected X U ↔ RuntimeFlatWithin X U := by
  constructor
  · exact runtimeFlatWithin_of_runtimeInteractionProtected hCoverage
  · exact runtimeInteractionProtected_of_runtimeFlatWithin

/--
Selected semantic diagram preservation for a feature extension.

The predicate is intentionally measured-list relative: it says that every
selected semantic diagram commutes, without claiming that the list is globally
complete.
-/
def FeatureDiagramsCommute
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  ∀ d, d ∈ X.measuredSemantic -> DiagramCommutes X.semantic d

/--
Selected semantic diagram preservation discharges bounded semantic flatness
under the semantic coverage package used by full architecture flatness.
-/
theorem semanticFlatWithin_of_featureDiagramsCommute
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (_hCoverage : SemanticCoverageComplete X)
    (hCommute : FeatureDiagramsCommute X) :
    SemanticFlatWithin X := by
  intro d hMeasured
  exact hCommute d hMeasured

/-- Bounded semantic flatness can be read as selected diagram commutation. -/
theorem featureDiagramsCommute_of_semanticFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (hFlat : SemanticFlatWithin X) :
    FeatureDiagramsCommute X := by
  intro d hMeasured
  exact hFlat d hMeasured

/-- Semantic diagram commutation and bounded semantic flatness coincide. -/
theorem featureDiagramsCommute_iff_semanticFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (hCoverage : SemanticCoverageComplete X) :
    FeatureDiagramsCommute X ↔ SemanticFlatWithin X := by
  constructor
  · exact semanticFlatWithin_of_featureDiagramsCommute hCoverage
  · exact featureDiagramsCommute_of_semanticFlatWithin

/--
Runtime / semantic split preservation evidence for one bounded flatness model.

Static split evidence remains in `StaticSplitExtension`; this package only
bundles the runtime and semantic premises that discharge the non-static layers.
-/
structure RuntimeSemanticSplitPreservation
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop where
  runtimeInteractionProtected : RuntimeInteractionProtected X U
  featureDiagramsCommute : FeatureDiagramsCommute X

/--
All required axes have evidence in the supplied bounded universes.

This is intentionally separate from zero/flatness predicates: missing runtime
edges or semantic diagrams are coverage gaps, not zero obstructions.
-/
def NoUnmeasuredRequiredAxis
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  StaticCoverageComplete X U ∧
  RuntimeCoverageComplete X U ∧
  SemanticCoverageComplete X

/--
Architecture flatness within a bounded, coverage-aware universe.

The conclusion is only relative to `U` and `measuredSemantic`; it does not claim
global extractor, telemetry, or semantic-diagram completeness.
-/
def ArchitectureFlatWithin
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  NoUnmeasuredRequiredAxis X U ∧
  StaticFlatWithin X U ∧
  RuntimeFlatWithin X U ∧
  SemanticFlatWithin X

/-- The static component of bounded architecture flatness. -/
theorem staticFlatWithin_of_architectureFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} :
    ArchitectureFlatWithin X U -> StaticFlatWithin X U := by
  intro hFlat
  exact hFlat.2.1

/-- The runtime component of bounded architecture flatness. -/
theorem runtimeFlatWithin_of_architectureFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} :
    ArchitectureFlatWithin X U -> RuntimeFlatWithin X U := by
  intro hFlat
  exact hFlat.2.2.1

/-- The semantic component of bounded architecture flatness. -/
theorem semanticFlatWithin_of_architectureFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} :
    ArchitectureFlatWithin X U -> SemanticFlatWithin X := by
  intro hFlat
  exact hFlat.2.2.2

/-- The coverage component of bounded architecture flatness. -/
theorem noUnmeasuredRequiredAxis_of_architectureFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static} :
    ArchitectureFlatWithin X U -> NoUnmeasuredRequiredAxis X U := by
  intro hFlat
  exact hFlat.1

/--
Exhaustive coverage premise for completing bounded architecture flatness.

This is named separately from `ArchitectureFlatWithin` so that global
completion corollaries expose the coverage assumption instead of hiding it in a
primary theorem.
-/
def ExhaustiveFlatnessCoverage
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  NoUnmeasuredRequiredAxis X U

/--
Exact observation premise for completing the selected static / runtime /
semantic flatness evidence into bounded architecture flatness.

The premise is still relative to `U` and the measured semantic list. It is a
bridge assumption, not a claim of extractor or telemetry completeness.
-/
def ExactFlatnessObservation
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs)
    (U : ComponentUniverse X.static) : Prop :=
  StaticFlatWithin X U ->
  RuntimeFlatWithin X U ->
  SemanticFlatWithin X ->
  ArchitectureFlatWithin X U

/-- Coverage discharges the exact-observation bridge for the existing layers. -/
theorem exactFlatnessObservation_of_exhaustiveCoverage
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (hCoverage : ExhaustiveFlatnessCoverage X U) :
    ExactFlatnessObservation X U := by
  intro hStatic hRuntime hSemantic
  exact ⟨hCoverage, hStatic, hRuntime, hSemantic⟩

/--
Certificate for reading bounded flatness as completed global flatness.

The certificate keeps the bounded theorem package primary: `flatWithin` is the
proved architecture flatness statement, while `exhaustiveCoverage`,
`exactObservation`, and `recordsNonConclusions` record the extra assumptions
that justify exposing a global predicate.
-/
structure GlobalFlatCertificate
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) where
  completionUniverse : ComponentUniverse X.static
  flatWithin : ArchitectureFlatWithin X completionUniverse
  exhaustiveCoverage : ExhaustiveFlatnessCoverage X completionUniverse
  exactObservation : ExactFlatnessObservation X completionUniverse
  nonConclusions : Prop
  recordsNonConclusions : nonConclusions

/--
Global architecture flatness is a completion predicate backed by an explicit
certificate. It is not the primary theorem package.
-/
def ArchitectureFlat
    (X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs) :
    Prop :=
  Nonempty (GlobalFlatCertificate X)

namespace GlobalFlatCertificate

/-- A global-flat certificate carries the underlying bounded flatness theorem. -/
theorem architectureFlatWithin
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (certificate : GlobalFlatCertificate X) :
    ArchitectureFlatWithin X certificate.completionUniverse :=
  certificate.flatWithin

/-- A global-flat certificate exposes exhaustive coverage explicitly. -/
theorem exhaustiveFlatnessCoverage
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (certificate : GlobalFlatCertificate X) :
    ExhaustiveFlatnessCoverage X certificate.completionUniverse :=
  certificate.exhaustiveCoverage

/-- A global-flat certificate exposes exact observation explicitly. -/
theorem exactFlatnessObservation
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (certificate : GlobalFlatCertificate X) :
    ExactFlatnessObservation X certificate.completionUniverse :=
  certificate.exactObservation

/-- A global-flat certificate records the non-conclusions it does not prove. -/
theorem nonConclusions_recorded
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    (certificate : GlobalFlatCertificate X) :
    certificate.nonConclusions :=
  certificate.recordsNonConclusions

end GlobalFlatCertificate

/--
Completion corollary from bounded flatness to global flatness.

The theorem deliberately requires exhaustive coverage, exact observation, and
recorded non-conclusions as visible inputs; without those, the bounded
`ArchitectureFlatWithin` theorem is not promoted.
-/
theorem globalFlat_of_within_exhaustive
    {X : ArchitectureFlatnessModel C A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (hWithin : ArchitectureFlatWithin X U)
    (hCoverage : ExhaustiveFlatnessCoverage X U)
    (hExact : ExactFlatnessObservation X U)
    {nonConclusions : Prop}
    (hNonConclusions : nonConclusions) :
    ArchitectureFlat X :=
  ⟨{
    completionUniverse := U
    flatWithin := hWithin
    exhaustiveCoverage := hCoverage
    exactObservation := hExact
    nonConclusions := nonConclusions
    recordsNonConclusions := hNonConclusions
  }⟩

/--
Coverage for a feature extension relative to the extended architecture universe.

This packages the minimum assumptions needed by later preservation theorems:
core embeddings, feature embeddings, extended static edges, and the extension's
own declared coverage assumptions are all explicit.
-/
def ExtensionCoverageComplete
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended) : Prop :=
  (∀ c : Core, X.coreEmbedding c ∈ U.components) ∧
  (∀ f : Feature, X.featureEmbedding f ∈ U.components) ∧
  (∀ {src dst : Extended}, X.extended.edge src dst ->
    src ∈ U.components ∧ dst ∈ U.components) ∧
  X.coverageAssumptions

/--
Selected witnesses for failure of `ExtensionCoverageComplete`.

These witnesses are coverage-only diagnostics: they record missing measured
components, uncovered extended edge endpoints, or failure of the declared
coverage assumptions. They are intentionally separate from
`StaticExtensionWitness`, which diagnoses static split law failures.
-/
inductive ExtensionCoverageWitness
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended) where
  | missingCoreEmbedding (c : Core)
      (missing : X.coreEmbedding c ∉ U.components)
  | missingFeatureEmbedding (f : Feature)
      (missing : X.featureEmbedding f ∉ U.components)
  | uncoveredExtendedEdge (src dst : Extended)
      (extendedEdge : X.extended.edge src dst)
      (missingEndpoint : src ∉ U.components ∨ dst ∉ U.components)
  | coverageAssumptionsFailure
      (missingCoverageAssumptions : ¬ X.coverageAssumptions)

/-- Selected coverage witness existence, separate from static split diagnostics. -/
def ExtensionCoverageWitnessExists
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended) : Prop :=
  Nonempty (ExtensionCoverageWitness X U)

/--
Coverage/exactness premise for the selected extension-coverage diagnostic
universe.

This is bounded to the supplied `ComponentUniverse`. It does not claim extractor
completeness, global split completeness, or runtime / semantic flatness.
-/
def ExtensionCoverageFailureCoverage
    (X : FeatureExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse X.extended) : Prop :=
  ¬ ExtensionCoverageComplete X U -> ExtensionCoverageWitnessExists X U

/--
A selected coverage witness is sound: it refutes the corresponding complete
extension coverage package.
-/
theorem not_extensionCoverageComplete_of_extensionCoverageWitness
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (witness : ExtensionCoverageWitness X U) :
    ¬ ExtensionCoverageComplete X U := by
  intro hCoverage
  cases witness with
  | missingCoreEmbedding c missing =>
      exact missing (hCoverage.1 c)
  | missingFeatureEmbedding f missing =>
      exact missing (hCoverage.2.1 f)
  | uncoveredExtendedEdge src dst extendedEdge missingEndpoint =>
      have hEndpoints := hCoverage.2.2.1 extendedEdge
      cases missingEndpoint with
      | inl missingSrc =>
          exact missingSrc hEndpoints.1
      | inr missingDst =>
          exact missingDst hEndpoints.2
  | coverageAssumptionsFailure missingCoverageAssumptions =>
      exact missingCoverageAssumptions hCoverage.2.2.2

/-- Soundness-only form for selected extension-coverage witness existence. -/
theorem not_extensionCoverageComplete_of_extensionCoverageWitnessExists
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hWitness : ExtensionCoverageWitnessExists X U) :
    ¬ ExtensionCoverageComplete X U := by
  rcases hWitness with ⟨witness⟩
  exact not_extensionCoverageComplete_of_extensionCoverageWitness witness

/--
Bounded completeness: under the selected coverage/exactness premise, a failure
of `ExtensionCoverageComplete` has a selected coverage witness.
-/
theorem extensionCoverageWitnessExists_of_not_extensionCoverageComplete
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hFailureCoverage : ExtensionCoverageFailureCoverage X U)
    (hNonCoverage : ¬ ExtensionCoverageComplete X U) :
    ExtensionCoverageWitnessExists X U :=
  hFailureCoverage hNonCoverage

/--
Soundness plus bounded completeness for the selected extension-coverage witness
universe.
-/
theorem extensionCoverageWitnessExists_iff_not_extensionCoverageComplete
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hFailureCoverage : ExtensionCoverageFailureCoverage X U) :
    ExtensionCoverageWitnessExists X U ↔ ¬ ExtensionCoverageComplete X U := by
  constructor
  · exact not_extensionCoverageComplete_of_extensionCoverageWitnessExists
  · exact extensionCoverageWitnessExists_of_not_extensionCoverageComplete
      hFailureCoverage

/-- Coverage for the static split-extension wrapper. -/
def StaticSplitExtensionCoverageComplete
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    (U : ComponentUniverse S.extension.extended) : Prop :=
  ExtensionCoverageComplete S.extension U

/-- Core embeddings are covered under complete extension coverage. -/
theorem coreEmbedding_mem_of_extensionCoverageComplete
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hCoverage : ExtensionCoverageComplete X U) (c : Core) :
    X.coreEmbedding c ∈ U.components :=
  hCoverage.1 c

/-- Feature embeddings are covered under complete extension coverage. -/
theorem featureEmbedding_mem_of_extensionCoverageComplete
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hCoverage : ExtensionCoverageComplete X U) (f : Feature) :
    X.featureEmbedding f ∈ U.components :=
  hCoverage.2.1 f

/-- Extended static edges are covered under complete extension coverage. -/
theorem extended_edge_mem_of_extensionCoverageComplete
    {X : FeatureExtension Core Feature Extended FeatureView}
    {U : ComponentUniverse X.extended}
    (hCoverage : ExtensionCoverageComplete X U)
    {src dst : Extended} (hEdge : X.extended.edge src dst) :
    src ∈ U.components ∧ dst ∈ U.components :=
  hCoverage.2.2.1 hEdge

/--
Static split-extension policy soundness for a compatible static graph.

The split extension supplies only the static edge-policy part. Other static
laws, such as acyclicity, projection soundness, and LSP compatibility, remain
separate assumptions of the flatness theorem below.
-/
theorem policySound_of_staticSplitExtension
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {G : ArchGraph Extended} {allowed : Extended -> Extended -> Prop}
    (hEdges :
      ∀ {src dst : Extended}, G.edge src dst ->
        S.extension.extended.edge src dst)
    (hAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        allowed src dst) :
    ArchitectureSignature.PolicySound G allowed := by
  intro src dst hEdge
  exact hAllowed (S.noNewForbiddenStaticEdge (hEdges hEdge))

/--
Boundary-policy soundness supplied by a static split extension.

This is only the boundary-policy component. It does not infer acyclicity,
projection soundness, LSP compatibility, runtime flatness, or semantic
flatness.
-/
theorem boundaryPolicySound_of_staticSplitExtension
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {G : ArchGraph Extended} {boundaryAllowed : Extended -> Extended -> Prop}
    (hEdges :
      ∀ {src dst : Extended}, G.edge src dst ->
        S.extension.extended.edge src dst)
    (hBoundaryAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        boundaryAllowed src dst) :
    ArchitectureSignature.PolicySound G boundaryAllowed :=
  policySound_of_staticSplitExtension S hEdges hBoundaryAllowed

/--
Abstraction-policy soundness supplied by a static split extension.

This is only the abstraction-policy component. Projection soundness itself
remains a separate premise, because static split policy soundness does not
identify abstract graph edges.
-/
theorem abstractionPolicySound_of_staticSplitExtension
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {G : ArchGraph Extended} {abstractionAllowed : Extended -> Extended -> Prop}
    (hEdges :
      ∀ {src dst : Extended}, G.edge src dst ->
        S.extension.extended.edge src dst)
    (hAbstractionAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        abstractionAllowed src dst) :
    ArchitectureSignature.PolicySound G abstractionAllowed :=
  policySound_of_staticSplitExtension S hEdges hAbstractionAllowed

/--
Static-split-friendly LSP bridge from observation factorization.

The static split package is a context marker here: the LSP conclusion comes
from the explicit `ObservationFactorsThrough` premise, not from static split
evidence alone.
-/
theorem lspCompatible_of_staticSplitObservationFactorsThrough
    (_S : StaticSplitExtension Core Feature Extended FeatureView)
    {projection : InterfaceProjection Extended A}
    {staticObservation : Observation Extended StaticObs}
    (hFactors : ObservationFactorsThrough projection staticObservation) :
    LSPCompatible projection staticObservation :=
  lspCompatible_of_observationFactorsThrough hFactors

/--
Exact projection gives projection soundness for the extended static graph of a
static split extension.

This theorem is intentionally bounded by the supplied exactness premise; a
`StaticSplitExtension` alone does not determine the abstract graph.
-/
theorem projectionSound_of_staticSplitProjectionExact
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    (hExact : ProjectionExact S.extension.extended projection abstractStatic) :
    ProjectionSound S.extension.extended projection abstractStatic :=
  projectionSound_of_projectionExact hExact

/--
Projection soundness transfers to a compatible static graph whose edges
decompose through the static split extension's extended graph.

The edge-decomposition premise is explicit, so this theorem does not claim
that every graph over `Extended` is covered by the static split extension.
-/
theorem projectionSound_of_staticSplitEdgeDecomposition
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {G : ArchGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    (hEdges :
      ∀ {src dst : Extended}, G.edge src dst ->
        S.extension.extended.edge src dst)
    (hProjectionSound :
      ProjectionSound S.extension.extended projection abstractStatic) :
    ProjectionSound G projection abstractStatic := by
  intro src dst hEdge
  exact hProjectionSound (hEdges hEdge)

/--
Static split extensions preserve coverage-aware static flatness.

This theorem is deliberately static-only: it concludes `StaticFlatWithin`, not
runtime, semantic, or full `ArchitectureFlatWithin`. The non-policy static laws
are explicit premises because the static split-extension schema only controls
new forbidden static edges.
-/
theorem staticFlatWithin_of_staticSplitExtension
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {X : ArchitectureFlatnessModel Extended A StaticObs SemanticExpr SemanticObs}
    {U : ComponentUniverse X.static}
    (hCoverage : StaticCoverageComplete X U)
    (hEdges :
      ∀ {src dst : Extended}, X.static.edge src dst ->
        S.extension.extended.edge src dst)
    (hBoundaryAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        X.boundaryAllowed src dst)
    (hAbstractionAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        X.abstractionAllowed src dst)
    (hWalkAcyclic : WalkAcyclic X.static)
    (hProjectionSound : ProjectionSound X.static X.projection X.abstractStatic)
    (hLSP : LSPCompatible X.projection X.staticObservation) :
    StaticFlatWithin X U := by
  have _hStaticCoverage : StaticCoverageComplete X U := hCoverage
  refine ⟨hWalkAcyclic, hProjectionSound, hLSP, ?_, ?_⟩
  · exact boundaryPolicySound_of_staticSplitExtension S hEdges hBoundaryAllowed
  · exact abstractionPolicySound_of_staticSplitExtension S hEdges hAbstractionAllowed

/--
Flatness model induced by a static split extension and explicit runtime /
semantic evidence.

The static graph is exactly the extended graph of the split extension. Runtime
and semantic layers remain supplied evidence rather than inferred telemetry or
global semantic completeness.
-/
def LawfulExtensionFlatnessModel
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    (runtime : RuntimeDependencyGraph Extended)
    (projection : InterfaceProjection Extended A)
    (abstractStatic : AbstractGraph A)
    (staticObservation : Observation Extended StaticObs)
    (boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop)
    (semantic : Semantics SemanticExpr SemanticObs)
    (requiredSemantic : RequiredDiagram SemanticExpr -> Prop)
    (measuredSemantic : List (RequiredDiagram SemanticExpr)) :
    ArchitectureFlatnessModel Extended A StaticObs SemanticExpr SemanticObs where
  static := S.extension.extended
  runtime := runtime
  projection := projection
  abstractStatic := abstractStatic
  staticObservation := staticObservation
  boundaryAllowed := boundaryAllowed
  abstractionAllowed := abstractionAllowed
  runtimeAllowed := runtimeAllowed
  semantic := semantic
  requiredSemantic := requiredSemantic
  measuredSemantic := measuredSemantic

/--
Recorded non-conclusions for the public split feature extension package.

This marker keeps the bounded package from being read as global flatness,
extractor completeness, or automatic runtime / semantic completeness.
-/
def SplitFeatureExtensionWithinNonConclusions
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    (_U : ComponentUniverse S.extension.extended) : Prop :=
  True

/--
Public bounded package for a split feature extension within a selected
component universe.

The package is intentionally a thin wrapper around existing static split,
coverage, and runtime / semantic evidence. It records all assumptions needed
to conclude `ArchitectureFlatWithin` for the induced flatness model, while
leaving global `ArchitectureFlat`, extractor completeness, and unmeasured
runtime / semantic axes outside the conclusion.
-/
structure SplitFeatureExtensionWithin
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    (runtime : RuntimeDependencyGraph Extended)
    (projection : InterfaceProjection Extended A)
    (abstractStatic : AbstractGraph A)
    (staticObservation : Observation Extended StaticObs)
    (boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop)
    (semantic : Semantics SemanticExpr SemanticObs)
    (requiredSemantic : RequiredDiagram SemanticExpr -> Prop)
    (measuredSemantic : List (RequiredDiagram SemanticExpr))
    (U : ComponentUniverse S.extension.extended) : Prop where
  extensionCoverage : StaticSplitExtensionCoverageComplete S U
  boundaryPolicyCompatible :
    ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
      boundaryAllowed src dst
  abstractionPolicyCompatible :
    ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
      abstractionAllowed src dst
  walkAcyclic : WalkAcyclic S.extension.extended
  projectionSound : ProjectionSound S.extension.extended projection abstractStatic
  lspCompatible : LSPCompatible projection staticObservation
  runtimeCoverage :
    RuntimeCoverageComplete
      (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
        measuredSemantic)
      U
  semanticCoverage : CoversRequired requiredSemantic measuredSemantic
  runtimeSemanticPreservation :
    RuntimeSemanticSplitPreservation
      (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
        measuredSemantic)
      U
  recordsNonConclusions : SplitFeatureExtensionWithinNonConclusions S U

/-- Constructor-style entrypoint for the public bounded split package. -/
def splitFeatureExtensionWithin_of_runtimeSemanticSplitPreservation
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {runtime : RuntimeDependencyGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    {staticObservation : Observation Extended StaticObs}
    {boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop}
    {semantic : Semantics SemanticExpr SemanticObs}
    {requiredSemantic : RequiredDiagram SemanticExpr -> Prop}
    {measuredSemantic : List (RequiredDiagram SemanticExpr)}
    (U : ComponentUniverse S.extension.extended)
    (hExtensionCoverage : StaticSplitExtensionCoverageComplete S U)
    (hBoundaryAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        boundaryAllowed src dst)
    (hAbstractionAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        abstractionAllowed src dst)
    (hWalkAcyclic : WalkAcyclic S.extension.extended)
    (hProjectionSound : ProjectionSound S.extension.extended projection abstractStatic)
    (hLSP : LSPCompatible projection staticObservation)
    (hRuntimeCoverage :
      RuntimeCoverageComplete
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U)
    (hSemanticCoverage : CoversRequired requiredSemantic measuredSemantic)
    (hRuntimeSemantic :
      RuntimeSemanticSplitPreservation
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U) :
    SplitFeatureExtensionWithin S runtime projection abstractStatic staticObservation
      boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic
      U where
  extensionCoverage := hExtensionCoverage
  boundaryPolicyCompatible := hBoundaryAllowed
  abstractionPolicyCompatible := hAbstractionAllowed
  walkAcyclic := hWalkAcyclic
  projectionSound := hProjectionSound
  lspCompatible := hLSP
  runtimeCoverage := hRuntimeCoverage
  semanticCoverage := hSemanticCoverage
  runtimeSemanticPreservation := hRuntimeSemantic
  recordsNonConclusions := trivial

/-- The public bounded split package records its non-conclusions explicitly. -/
theorem splitFeatureExtensionWithin_recordsNonConclusions
    {S : StaticSplitExtension Core Feature Extended FeatureView}
    {runtime : RuntimeDependencyGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    {staticObservation : Observation Extended StaticObs}
    {boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop}
    {semantic : Semantics SemanticExpr SemanticObs}
    {requiredSemantic : RequiredDiagram SemanticExpr -> Prop}
    {measuredSemantic : List (RequiredDiagram SemanticExpr)}
    {U : ComponentUniverse S.extension.extended}
    (hSplit :
      SplitFeatureExtensionWithin S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic
        U) :
    SplitFeatureExtensionWithinNonConclusions S U :=
  hSplit.recordsNonConclusions

/--
Bounded flatness preservation for a lawful static split extension.

This corollary is deliberately coverage-aware: extension coverage, runtime
coverage, and semantic coverage are explicit premises. It does not assume global
extractor completeness, telemetry completeness, or semantic universe
completeness outside the supplied bounded evidence.
-/
theorem LawfulExtensionPreservesFlatness
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {runtime : RuntimeDependencyGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    {staticObservation : Observation Extended StaticObs}
    {boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop}
    {semantic : Semantics SemanticExpr SemanticObs}
    {requiredSemantic : RequiredDiagram SemanticExpr -> Prop}
    {measuredSemantic : List (RequiredDiagram SemanticExpr)}
    (U : ComponentUniverse S.extension.extended)
    (_hExtensionCoverage : StaticSplitExtensionCoverageComplete S U)
    (hBoundaryAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        boundaryAllowed src dst)
    (hAbstractionAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        abstractionAllowed src dst)
    (hWalkAcyclic : WalkAcyclic S.extension.extended)
    (hProjectionSound : ProjectionSound S.extension.extended projection abstractStatic)
    (hLSP : LSPCompatible projection staticObservation)
    (hRuntimeCoverage :
      RuntimeCoverageComplete
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U)
    (hRuntimeFlat :
      RuntimeFlatWithin
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U)
    (hSemanticCoverage : CoversRequired requiredSemantic measuredSemantic)
    (hSemanticFlat : DiagramLawfulByList semantic measuredSemantic) :
    ArchitectureFlatWithin
      (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic)
      U := by
  let X :=
    LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
      boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic
  have hStaticCoverage : StaticCoverageComplete X U :=
    staticCoverageComplete_of_componentUniverse X U
  have hStaticFlat : StaticFlatWithin X U :=
    staticFlatWithin_of_staticSplitExtension
      (S := S)
      (X := X)
      (U := U)
      hStaticCoverage
      (fun hEdge => hEdge)
      hBoundaryAllowed
      hAbstractionAllowed
      hWalkAcyclic
      hProjectionSound
      hLSP
  exact ⟨⟨hStaticCoverage, hRuntimeCoverage, hSemanticCoverage⟩,
    hStaticFlat, hRuntimeFlat, hSemanticFlat⟩

/--
Bounded flatness preservation with runtime / semantic split evidence.

This corollary connects the selected runtime protection and selected semantic
diagram commutation predicates to `LawfulExtensionPreservesFlatness`. Runtime
coverage and semantic coverage remain explicit bounded assumptions.
-/
theorem LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation
    (S : StaticSplitExtension Core Feature Extended FeatureView)
    {runtime : RuntimeDependencyGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    {staticObservation : Observation Extended StaticObs}
    {boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop}
    {semantic : Semantics SemanticExpr SemanticObs}
    {requiredSemantic : RequiredDiagram SemanticExpr -> Prop}
    {measuredSemantic : List (RequiredDiagram SemanticExpr)}
    (U : ComponentUniverse S.extension.extended)
    (hExtensionCoverage : StaticSplitExtensionCoverageComplete S U)
    (hBoundaryAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        boundaryAllowed src dst)
    (hAbstractionAllowed :
      ∀ {src dst : Extended}, S.extendedAllowedStaticEdge src dst ->
        abstractionAllowed src dst)
    (hWalkAcyclic : WalkAcyclic S.extension.extended)
    (hProjectionSound : ProjectionSound S.extension.extended projection abstractStatic)
    (hLSP : LSPCompatible projection staticObservation)
    (hRuntimeCoverage :
      RuntimeCoverageComplete
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U)
    (hSemanticCoverage : CoversRequired requiredSemantic measuredSemantic)
    (hRuntimeSemantic :
      RuntimeSemanticSplitPreservation
        (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
          boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic
          measuredSemantic)
        U) :
    ArchitectureFlatWithin
      (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic)
      U := by
  let X :=
    LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
      boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic
  exact LawfulExtensionPreservesFlatness
    (S := S)
    (runtime := runtime)
    (projection := projection)
    (abstractStatic := abstractStatic)
    (staticObservation := staticObservation)
    (boundaryAllowed := boundaryAllowed)
    (abstractionAllowed := abstractionAllowed)
    (runtimeAllowed := runtimeAllowed)
    (semantic := semantic)
    (requiredSemantic := requiredSemantic)
    (measuredSemantic := measuredSemantic)
    U
    hExtensionCoverage
    hBoundaryAllowed
    hAbstractionAllowed
    hWalkAcyclic
    hProjectionSound
    hLSP
    hRuntimeCoverage
    (runtimeFlatWithin_of_runtimeInteractionProtected
      (X := X) (U := U) hRuntimeCoverage
      hRuntimeSemantic.runtimeInteractionProtected)
    hSemanticCoverage
    (semanticFlatWithin_of_featureDiagramsCommute
      (X := X) hSemanticCoverage hRuntimeSemantic.featureDiagramsCommute)

/--
Public bounded preservation theorem for `SplitFeatureExtensionWithin`.

This is an alias-style theorem package: it reuses
`LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation` and
therefore does not add new global completeness assumptions.
-/
theorem architectureFlatWithin_of_splitFeatureExtensionWithin
    {S : StaticSplitExtension Core Feature Extended FeatureView}
    {runtime : RuntimeDependencyGraph Extended}
    {projection : InterfaceProjection Extended A}
    {abstractStatic : AbstractGraph A}
    {staticObservation : Observation Extended StaticObs}
    {boundaryAllowed abstractionAllowed runtimeAllowed : Extended -> Extended -> Prop}
    {semantic : Semantics SemanticExpr SemanticObs}
    {requiredSemantic : RequiredDiagram SemanticExpr -> Prop}
    {measuredSemantic : List (RequiredDiagram SemanticExpr)}
    {U : ComponentUniverse S.extension.extended}
    (hSplit :
      SplitFeatureExtensionWithin S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic
        U) :
    ArchitectureFlatWithin
      (LawfulExtensionFlatnessModel S runtime projection abstractStatic staticObservation
        boundaryAllowed abstractionAllowed runtimeAllowed semantic requiredSemantic measuredSemantic)
      U :=
  LawfulExtensionPreservesFlatness_of_runtimeSemanticSplitPreservation
    (S := S)
    (runtime := runtime)
    (projection := projection)
    (abstractStatic := abstractStatic)
    (staticObservation := staticObservation)
    (boundaryAllowed := boundaryAllowed)
    (abstractionAllowed := abstractionAllowed)
    (runtimeAllowed := runtimeAllowed)
    (semantic := semantic)
    (requiredSemantic := requiredSemantic)
    (measuredSemantic := measuredSemantic)
    U
    hSplit.extensionCoverage
    hSplit.boundaryPolicyCompatible
    hSplit.abstractionPolicyCompatible
    hSplit.walkAcyclic
    hSplit.projectionSound
    hSplit.lspCompatible
    hSplit.runtimeCoverage
    hSplit.semanticCoverage
    hSplit.runtimeSemanticPreservation

end Formal.Arch
