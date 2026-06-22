import Formal.AG.Research.QualitySurface.SemanticResidualAliasClassification

/-!
Cycle 85 evidence for `G-aat-quality-surface-01`.

This file moves the semantic-residual obstruction from component projection to
transport.  A semantic support transported from a source vocabulary preserves
target semantic repair closure only when every target residual has a supported
source residual lift.  Component-preserving transport alone is not enough: the
selected obligation-to-surface alias map preserves protected components, but it
forgets the repair-frontier obligation residual.

The result remains finite and semantic-support-level.  It does not assert
source extraction completeness, ArchMap correctness, runtime repair synthesis,
canonical global semantic ontology, general sheaf gluing, global sheaf
completeness, or whole-codebase quality.
-/

universe u v

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualTransportNaturality

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualAliasNonfaithfulness
open SemanticResidualComponentFaithfulness
open SemanticResidualAliasClassification

/-! ## Generic residual transport kernel -/

/--
The target support is exactly the image of a source support under a semantic
atom transport map.
-/
def TransportedSemanticSupportExact
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (sourceSupport : Source -> Prop)
    (targetSupport : Target -> Prop) : Prop :=
  forall target,
    targetSupport target <->
      exists source, sourceSupport source /\ transport source = target

/--
A transport is residual-surjective when every target residual is the image of a
source residual.
-/
def TargetResidualLiftedBySourceResidual
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (sourceProjection : Source -> BridgeComponent)
    (sourceCover : HandoffCechCover)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover) : Prop :=
  forall targetResidual,
    SemanticProjectedResidual targetProjection targetCover targetResidual ->
      exists sourceResidual,
        SemanticProjectedResidual sourceProjection sourceCover sourceResidual /\
          transport sourceResidual = targetResidual

/--
Every target residual has a supported source lift.  This is the exact
transport-side invariant needed by target semantic repair closure.
-/
def TargetResidualSupportedBySource
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop) : Prop :=
  forall targetResidual,
    SemanticProjectedResidual targetProjection targetCover targetResidual ->
      exists source,
        sourceSupport source /\ transport source = targetResidual

/--
A target residual is missed by the transported support when no supported source
atom maps to it.
-/
def MissedTargetResidualTransport
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop) : Prop :=
  exists targetResidual,
    SemanticProjectedResidual targetProjection targetCover targetResidual /\
      forall source, sourceSupport source -> transport source ≠ targetResidual

/-- A semantic transport preserves the protected component of every source atom. -/
def ComponentPreservingSemanticTransport
    {Source : Type u}
    {Target : Type v}
    (sourceProjection : Source -> BridgeComponent)
    (targetProjection : Target -> BridgeComponent)
    (transport : Source -> Target) : Prop :=
  forall source, targetProjection (transport source) = sourceProjection source

/--
A residual support transport carries source residuals to target residuals,
covers every target residual, and preserves support truth on residual atoms.
-/
structure ResidualSupportTransport
    {Source : Type u}
    {Target : Type v}
    (sourceProjection : Source -> BridgeComponent)
    (sourceCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (targetSupport : Target -> Prop) where
  map : Source -> Target
  residual_map :
    forall sourceResidual,
      SemanticProjectedResidual sourceProjection sourceCover sourceResidual ->
        SemanticProjectedResidual targetProjection targetCover
          (map sourceResidual)
  residual_surj :
    forall targetResidual,
      SemanticProjectedResidual targetProjection targetCover targetResidual ->
        exists sourceResidual,
          SemanticProjectedResidual sourceProjection sourceCover sourceResidual /\
            map sourceResidual = targetResidual
  support_on_residuals :
    forall sourceResidual,
      SemanticProjectedResidual sourceProjection sourceCover sourceResidual ->
        (sourceSupport sourceResidual <->
          targetSupport (map sourceResidual))

/-- Exact transported support contains the image of every supported source atom. -/
theorem transportedSupportExact_supports_image
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {sourceSupport : Source -> Prop}
    {targetSupport : Target -> Prop}
    (hexact :
      TransportedSemanticSupportExact transport sourceSupport targetSupport)
    {source : Source}
    (hsource : sourceSupport source) :
    targetSupport (transport source) := by
  exact (hexact (transport source)).mpr ⟨source, hsource, rfl⟩

/--
A residual support transport is exactly the data needed to reflect semantic
repair closure across two residual vocabularies.
-/
theorem residualSupportTransport_semanticRepairClosed_iff
    {Source : Type u}
    {Target : Type v}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {targetSupport : Target -> Prop}
    (transport :
      ResidualSupportTransport
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport) :
    SemanticRepairClosed sourceProjection sourceCover sourceSupport <->
      SemanticRepairClosed targetProjection targetCover targetSupport := by
  constructor
  · intro hsourceClosed targetResidual htargetResidual
    rcases transport.residual_surj targetResidual htargetResidual with
      ⟨sourceResidual, hsourceResidual, hmap⟩
    have hsourceSupport : sourceSupport sourceResidual :=
      hsourceClosed sourceResidual hsourceResidual
    have htargetSupport : targetSupport (transport.map sourceResidual) :=
      (transport.support_on_residuals
        sourceResidual hsourceResidual).mp hsourceSupport
    simpa [hmap] using htargetSupport
  · intro htargetClosed sourceResidual hsourceResidual
    have htargetResidual :
        SemanticProjectedResidual targetProjection targetCover
          (transport.map sourceResidual) :=
      transport.residual_map sourceResidual hsourceResidual
    have htargetSupport : targetSupport (transport.map sourceResidual) :=
      htargetClosed (transport.map sourceResidual) htargetResidual
    exact
      (transport.support_on_residuals
        sourceResidual hsourceResidual).mpr htargetSupport

/--
Residual support transports provide residual-surjective maps after forgetting
support preservation.
-/
theorem targetResidualLiftedBySourceResidual_of_residualSupportTransport
    {Source : Type u}
    {Target : Type v}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {targetSupport : Target -> Prop}
    (transport :
      ResidualSupportTransport
        sourceProjection sourceCover sourceSupport
        targetProjection targetCover targetSupport) :
    TargetResidualLiftedBySourceResidual
      transport.map sourceProjection sourceCover targetProjection targetCover := by
  intro targetResidual htargetResidual
  exact transport.residual_surj targetResidual htargetResidual

/--
For an exact transported support, semantic repair closure is equivalent to
having a supported source lift for every target residual.
-/
theorem semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetSupport : Target -> Prop}
    (hexact :
      TransportedSemanticSupportExact transport sourceSupport targetSupport) :
    SemanticRepairClosed targetProjection targetCover targetSupport <->
      TargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport := by
  constructor
  · intro htargetClosed targetResidual htargetResidual
    exact (hexact targetResidual).mp
      (htargetClosed targetResidual htargetResidual)
  · intro hsupported targetResidual htargetResidual
    rcases hsupported targetResidual htargetResidual with
      ⟨source, hsourceSupport, htransport⟩
    have htargetSupport : targetSupport (transport source) :=
      transportedSupportExact_supports_image hexact hsourceSupport
    simpa [htransport] using htargetSupport

/--
Residual-surjective transport from a closed source support supplies supported
lifts for every target residual.
-/
theorem targetResidualSupported_of_residualLiftedTransport_of_sourceClosed
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    (hlift :
      TargetResidualLiftedBySourceResidual
        transport sourceProjection sourceCover targetProjection targetCover)
    (hsourceClosed :
      SemanticRepairClosed sourceProjection sourceCover sourceSupport) :
    TargetResidualSupportedBySource
      transport targetProjection targetCover sourceSupport := by
  intro targetResidual htargetResidual
  rcases hlift targetResidual htargetResidual with
    ⟨sourceResidual, hsourceResidual, htransport⟩
  exact ⟨sourceResidual, hsourceClosed sourceResidual hsourceResidual, htransport⟩

/--
If target residuals lift to source residuals and the target support is exactly
the transported source support, then semantic repair closure transports.
-/
theorem semanticRepairClosed_of_residualLiftedTransport_of_exactSupport
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetSupport : Target -> Prop}
    (hexact :
      TransportedSemanticSupportExact transport sourceSupport targetSupport)
    (hlift :
      TargetResidualLiftedBySourceResidual
        transport sourceProjection sourceCover targetProjection targetCover)
    (hsourceClosed :
      SemanticRepairClosed sourceProjection sourceCover sourceSupport) :
    SemanticRepairClosed targetProjection targetCover targetSupport := by
  exact
    (semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport
      hexact).mpr
      (targetResidualSupported_of_residualLiftedTransport_of_sourceClosed
        hlift hsourceClosed)

/--
A missed target residual obstructs semantic repair closure for any exact image
support.
-/
theorem missedTargetResidualTransport_obstructs_semanticRepairClosed
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    {targetSupport : Target -> Prop}
    (hexact :
      TransportedSemanticSupportExact transport sourceSupport targetSupport)
    (hmissed :
      MissedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) :
    Not (SemanticRepairClosed targetProjection targetCover targetSupport) := by
  intro htargetClosed
  rcases hmissed with ⟨targetResidual, htargetResidual, hnoLift⟩
  have htargetSupport : targetSupport targetResidual :=
    htargetClosed targetResidual htargetResidual
  rcases (hexact targetResidual).mp htargetSupport with
    ⟨source, hsourceSupport, htransport⟩
  exact hnoLift source hsourceSupport htransport

/-- A missed target residual is an explicit obstruction to the supported-lift criterion. -/
theorem missedTargetResidualTransport_obstructs_supportedResidualTransport
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    (hmissed :
      MissedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) :
    Not
      (TargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport) := by
  intro hsupported
  rcases hmissed with ⟨targetResidual, htargetResidual, hnoLift⟩
  rcases hsupported targetResidual htargetResidual with
    ⟨source, hsourceSupport, htransport⟩
  exact hnoLift source hsourceSupport htransport

/--
Residual-surjective transport from a closed source support rules out missed
target residuals.
-/
theorem residualLiftedTransport_rules_out_missedTargetResidual
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    (hlift :
      TargetResidualLiftedBySourceResidual
        transport sourceProjection sourceCover targetProjection targetCover)
    (hsourceClosed :
      SemanticRepairClosed sourceProjection sourceCover sourceSupport) :
    Not
      (MissedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) := by
  intro hmissed
  rcases hmissed with ⟨targetResidual, htargetResidual, hnoLift⟩
  rcases hlift targetResidual htargetResidual with
    ⟨sourceResidual, hsourceResidual, htransport⟩
  have hsourceSupport : sourceSupport sourceResidual :=
    hsourceClosed sourceResidual hsourceResidual
  exact hnoLift sourceResidual hsourceSupport htransport

/--
For a closed source support, a missed target residual refutes residual
surjectivity of the transport.
-/
theorem missedTargetResidualTransport_obstructs_residualLiftedTransport_of_sourceClosed
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {sourceProjection : Source -> BridgeComponent}
    {sourceCover : HandoffCechCover}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    (hsourceClosed :
      SemanticRepairClosed sourceProjection sourceCover sourceSupport)
    (hmissed :
      MissedTargetResidualTransport
        transport targetProjection targetCover sourceSupport) :
    Not
      (TargetResidualLiftedBySourceResidual
        transport sourceProjection sourceCover targetProjection targetCover) := by
  intro hlift
  exact
    residualLiftedTransport_rules_out_missedTargetResidual
      hlift hsourceClosed hmissed

/-! ## Selected obligation-alias transport -/

open RefinedSemanticRepairAtom

/--
The selected transport collapses the protected repair-frontier obligation to
the visible repair-frontier surface atom.
-/
def obligationAliasTransport :
    RefinedSemanticRepairAtom -> RefinedSemanticRepairAtom
  | traceContract => traceContract
  | repairFrontierSurface => repairFrontierSurface
  | repairFrontierObligation => repairFrontierSurface

/-- The selected alias transport preserves protected bridge components. -/
theorem obligationAliasTransport_componentPreserving :
    ComponentPreservingSemanticTransport
      refinedSemanticComponent refinedSemanticComponent
      obligationAliasTransport := by
  intro source
  cases source <;> rfl

/--
The surface-reading support is exactly the image of complete support under the
obligation-alias transport.
-/
theorem surfaceRepairSupport_is_obligationAliasTransport_image :
    TransportedSemanticSupportExact
      obligationAliasTransport
      completeRepairSupport
      surfaceRepairSupport := by
  intro target
  constructor
  · intro htarget
    cases target
    · exact ⟨traceContract, trivial, rfl⟩
    · exact ⟨repairFrontierSurface, trivial, rfl⟩
    · exact False.elim htarget
  · intro himage
    rcases himage with ⟨source, _hsource, htransport⟩
    subst target
    cases source <;> trivial

/--
The selected component-preserving transport misses the protected obligation
residual as a target atom.
-/
theorem selected_obligationAliasTransport_misses_obligationResidual :
    MissedTargetResidualTransport
      obligationAliasTransport
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport := by
  refine
    ⟨repairFrontierObligation,
      ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl),
      ?_⟩
  intro source _hsource htransport
  cases source <;> cases htransport

/--
The selected component-preserving transport is not residual-surjective for the
selected repair-frontier cover.
-/
theorem selected_obligationAliasTransport_not_residualLifted :
    Not
      (TargetResidualLiftedBySourceResidual
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        refinedSemanticComponent
        repairFrontierOverlapBasisCover) := by
  exact
    missedTargetResidualTransport_obstructs_residualLiftedTransport_of_sourceClosed
      completeRepairSupport_semanticRepairClosed
      selected_obligationAliasTransport_misses_obligationResidual

/--
The selected exact transport image does not preserve semantic repair closure,
even though the atom transport preserves protected components.
-/
theorem selected_componentPreserving_transport_not_semanticRepairClosed :
    ComponentPreservingSemanticTransport
        refinedSemanticComponent refinedSemanticComponent
        obligationAliasTransport /\
      TransportedSemanticSupportExact
        obligationAliasTransport
        completeRepairSupport
        surfaceRepairSupport /\
      Not
        (TargetResidualSupportedBySource
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport) /\
      MissedTargetResidualTransport
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (TargetResidualLiftedBySourceResidual
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          refinedSemanticComponent
          repairFrontierOverlapBasisCover) /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) := by
  exact
    ⟨obligationAliasTransport_componentPreserving,
      surfaceRepairSupport_is_obligationAliasTransport_image,
      missedTargetResidualTransport_obstructs_supportedResidualTransport
        selected_obligationAliasTransport_misses_obligationResidual,
      selected_obligationAliasTransport_misses_obligationResidual,
      selected_obligationAliasTransport_not_residualLifted,
      missedTargetResidualTransport_obstructs_semanticRepairClosed
        surfaceRepairSupport_is_obligationAliasTransport_image
        selected_obligationAliasTransport_misses_obligationResidual⟩

/--
The selected component-preserving alias map cannot be upgraded to a residual
support transport between complete and surface semantic supports.
-/
theorem selected_no_residualSupportTransport_for_obligationAlias :
    Not
      (exists transport :
        ResidualSupportTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport,
        transport.map = obligationAliasTransport) := by
  intro htransport
  rcases htransport with ⟨transport, hmap⟩
  have hlift :
      TargetResidualLiftedBySourceResidual
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        refinedSemanticComponent
        repairFrontierOverlapBasisCover := by
    intro targetResidual htargetResidual
    rcases transport.residual_surj targetResidual htargetResidual with
      ⟨sourceResidual, hsourceResidual, htransportMap⟩
    exact ⟨sourceResidual, hsourceResidual, by simpa [hmap] using htransportMap⟩
  exact selected_obligationAliasTransport_not_residualLifted hlift

/-! ## Theorem package -/

/--
Cycle-85 theorem package: exact support transport preserves semantic repair
closure precisely through target residual lifts, and the selected
component-preserving alias transport misses the obligation residual.
-/
theorem semanticResidualTransportNaturality_package :
    (forall {Source : Type u}
      {Target : Type v}
      {sourceProjection : Source -> BridgeComponent}
      {sourceCover : HandoffCechCover}
      {targetProjection : Target -> BridgeComponent}
      {targetCover : HandoffCechCover}
      {sourceSupport : Source -> Prop}
      {targetSupport : Target -> Prop},
      ResidualSupportTransport
          sourceProjection sourceCover sourceSupport
          targetProjection targetCover targetSupport ->
        (SemanticRepairClosed sourceProjection sourceCover sourceSupport <->
          SemanticRepairClosed targetProjection targetCover targetSupport)) /\
      (forall {Source : Type u}
      {Target : Type v}
      {transport : Source -> Target}
      {targetProjection : Target -> BridgeComponent}
      {targetCover : HandoffCechCover}
      {sourceSupport : Source -> Prop}
      {targetSupport : Target -> Prop},
      TransportedSemanticSupportExact transport sourceSupport targetSupport ->
        (SemanticRepairClosed targetProjection targetCover targetSupport <->
          TargetResidualSupportedBySource
            transport targetProjection targetCover sourceSupport)) /\
      (forall {Source : Type u}
      {Target : Type v}
      {transport : Source -> Target}
      {sourceProjection : Source -> BridgeComponent}
      {sourceCover : HandoffCechCover}
      {targetProjection : Target -> BridgeComponent}
      {targetCover : HandoffCechCover}
      {sourceSupport : Source -> Prop}
      {targetSupport : Target -> Prop},
      TransportedSemanticSupportExact transport sourceSupport targetSupport ->
        TargetResidualLiftedBySourceResidual
          transport sourceProjection sourceCover targetProjection targetCover ->
          SemanticRepairClosed sourceProjection sourceCover sourceSupport ->
            SemanticRepairClosed targetProjection targetCover targetSupport) /\
      (forall {Source : Type u}
        {Target : Type v}
        {transport : Source -> Target}
        {targetProjection : Target -> BridgeComponent}
        {targetCover : HandoffCechCover}
        {sourceSupport : Source -> Prop}
        {targetSupport : Target -> Prop},
        TransportedSemanticSupportExact transport sourceSupport targetSupport ->
          MissedTargetResidualTransport
            transport targetProjection targetCover sourceSupport ->
            Not
              (SemanticRepairClosed
                targetProjection targetCover targetSupport)) /\
      ComponentPreservingSemanticTransport
        refinedSemanticComponent refinedSemanticComponent
        obligationAliasTransport /\
      TransportedSemanticSupportExact
        obligationAliasTransport
        completeRepairSupport
        surfaceRepairSupport /\
      Not
        (TargetResidualSupportedBySource
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport) /\
      MissedTargetResidualTransport
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (TargetResidualLiftedBySourceResidual
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          refinedSemanticComponent
          repairFrontierOverlapBasisCover) /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (exists transport :
          ResidualSupportTransport
            refinedSemanticComponent
            repairFrontierOverlapBasisCover
            completeRepairSupport
            refinedSemanticComponent
            repairFrontierOverlapBasisCover
            surfaceRepairSupport,
          transport.map = obligationAliasTransport) := by
  exact
    ⟨fun {Source} {Target} {sourceProjection} {sourceCover}
        {targetProjection} {targetCover} {sourceSupport} {targetSupport} =>
        residualSupportTransport_semanticRepairClosed_iff,
      fun {Source} {Target} {transport} {targetProjection} {targetCover}
        {sourceSupport} {targetSupport} =>
        semanticRepairClosed_iff_targetResidualSupportedTransport_of_exactSupport,
      fun {Source} {Target} {transport} {sourceProjection} {sourceCover}
        {targetProjection} {targetCover} {sourceSupport} {targetSupport} =>
        semanticRepairClosed_of_residualLiftedTransport_of_exactSupport,
      fun {Source} {Target} {transport} {targetProjection} {targetCover}
        {sourceSupport} {targetSupport} =>
        missedTargetResidualTransport_obstructs_semanticRepairClosed,
      obligationAliasTransport_componentPreserving,
      surfaceRepairSupport_is_obligationAliasTransport_image,
      selected_componentPreserving_transport_not_semanticRepairClosed.2.2.1,
      selected_obligationAliasTransport_misses_obligationResidual,
      selected_obligationAliasTransport_not_residualLifted,
      selected_componentPreserving_transport_not_semanticRepairClosed.2.2.2.2.2,
      selected_no_residualSupportTransport_for_obligationAlias⟩

end SemanticResidualTransportNaturality
end QualitySurface
end Formal.AG.Research
