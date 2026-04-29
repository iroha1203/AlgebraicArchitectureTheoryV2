import Formal.Arch.FeatureExtension
import Formal.Arch.SignatureLawfulness
import Formal.Arch.StateEffect

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
  · exact policySound_of_staticSplitExtension S hEdges hBoundaryAllowed
  · exact policySound_of_staticSplitExtension S hEdges hAbstractionAllowed

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

end Formal.Arch
