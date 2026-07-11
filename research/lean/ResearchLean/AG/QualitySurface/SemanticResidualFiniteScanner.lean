import ResearchLean.AG.QualitySurface.SemanticResidualTransportNaturality

/-!
Cycle 86 evidence for `G-aat-quality-surface-01`.

This file makes the Cycle 84 missed-residual normal form executable under an
explicit finite scan order.  A finite list is allowed to extract a missed
semantic residual only when it covers the source-supported residuals of the
chosen projection and cover.  Under that completeness hypothesis and a closed
source support, `none` from the scanner is equivalent to target semantic repair
closure.

The result remains finite, list-relative, and semantic-support-level.  It does
not extract witnesses from a bare negated closure statement without a complete
finite scan order, does not assert a canonical global residual order, and does
not assert source extraction completeness, ArchMap correctness, runtime repair
synthesis, canonical global semantic ontology, general sheaf gluing, global
sheaf completeness, or whole-codebase quality.
-/

universe u v

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualFiniteScanner

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open HandoffRepairTransversalTheorem
open SemanticSupportProjectionKernel
open SemanticResidualAliasNonfaithfulness
open SemanticResidualAliasClassification
open SemanticResidualTransportNaturality

/-! ## Generic finite scanner -/

/-- The list contains every source-supported semantic residual. -/
def ListedSourceSemanticResidualsComplete
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport : Atom -> Prop)
    (atoms : List Atom) : Prop :=
  forall residual,
    SemanticProjectedResidual projection cover residual ->
      sourceSupport residual ->
        residual ∈ atoms

/-- Every listed source-supported residual is already target-supported. -/
def ListedSourceSemanticResidualsClosed
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop)
    (atoms : List Atom) : Prop :=
  forall residual,
    residual ∈ atoms ->
      SemanticProjectedResidual projection cover residual ->
        sourceSupport residual ->
          targetSupport residual

/-- The first listed semantic residual carried by source support and missed by target support. -/
def firstMissedSemanticResidual?
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop)
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport] :
    List Atom -> Option Atom
  | [] => none
  | atom :: rest =>
      if SemanticProjectedResidual projection cover atom /\
          sourceSupport atom /\ Not (targetSupport atom) then
        some atom
      else
        firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport rest

/-- A returned residual is a member of the supplied scan order. -/
theorem firstMissedSemanticResidual?_some_mem
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop)
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport] :
    forall {atoms : List Atom} {residual : Atom},
      firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport atoms =
        some residual ->
        residual ∈ atoms
  | [], _residual, hsome => by
      cases hsome
  | head :: rest, residual, hsome => by
      by_cases hmissed :
        SemanticProjectedResidual projection cover head /\
          sourceSupport head /\ Not (targetSupport head)
      · have hresidual : residual = head := by
          simpa [firstMissedSemanticResidual?, hmissed] using hsome.symm
        subst residual
        simp
      · have htail :
          firstMissedSemanticResidual?
              projection cover sourceSupport targetSupport rest =
            some residual := by
          simpa [firstMissedSemanticResidual?, hmissed] using hsome
        exact List.mem_cons_of_mem head
          (firstMissedSemanticResidual?_some_mem
            projection cover sourceSupport targetSupport htail)

/-- A returned residual is an actual missed semantic residual. -/
theorem firstMissedSemanticResidual?_some_missed
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop)
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport] :
    forall {atoms : List Atom} {residual : Atom},
      firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport atoms =
        some residual ->
        SemanticProjectedResidual projection cover residual /\
          sourceSupport residual /\
          Not (targetSupport residual)
  | [], _residual, hsome => by
      cases hsome
  | head :: rest, residual, hsome => by
      by_cases hmissed :
        SemanticProjectedResidual projection cover head /\
          sourceSupport head /\ Not (targetSupport head)
      · have hresidual : residual = head := by
          simpa [firstMissedSemanticResidual?, hmissed] using hsome.symm
        subst residual
        exact hmissed
      · have htail :
          firstMissedSemanticResidual?
              projection cover sourceSupport targetSupport rest =
            some residual := by
          simpa [firstMissedSemanticResidual?, hmissed] using hsome
        exact
          firstMissedSemanticResidual?_some_missed
            projection cover sourceSupport targetSupport htail

/-- A returned residual gives the Cycle 84 missed-residual witness. -/
theorem firstMissedSemanticResidual?_some_missedSemanticResidual
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport]
    {atoms : List Atom}
    {residual : Atom}
    (hscan :
      firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport atoms =
        some residual) :
    MissedSemanticResidual projection cover sourceSupport targetSupport := by
  rcases
      firstMissedSemanticResidual?_some_missed
        projection cover sourceSupport targetSupport hscan with
    ⟨hresidual, hsource, htargetMiss⟩
  exact ⟨residual, hresidual, hsource, htargetMiss⟩

/-- The scanner returns none exactly when every listed source-supported residual is closed. -/
theorem firstMissedSemanticResidual?_none_iff_listedClosed
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop)
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport] :
    forall atoms,
      firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport atoms = none <->
        ListedSourceSemanticResidualsClosed
          projection cover sourceSupport targetSupport atoms
  | [] => by
      constructor
      · intro _ residual hmem _hresidual _hsource
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone residual hmem hresidual hsource
        by_cases hmissed :
          SemanticProjectedResidual projection cover head /\
            sourceSupport head /\ Not (targetSupport head)
        · have hsome :
            firstMissedSemanticResidual?
                projection cover sourceSupport targetSupport (head :: rest) =
              some head := by
            simp [firstMissedSemanticResidual?, hmissed]
          rw [hsome] at hnone
          cases hnone
        · have htail :
            firstMissedSemanticResidual?
                projection cover sourceSupport targetSupport rest = none := by
            simpa [firstMissedSemanticResidual?, hmissed] using hnone
          cases hmem with
          | head =>
              by_contra htargetMiss
              exact hmissed ⟨hresidual, hsource, htargetMiss⟩
          | tail _ hlisted =>
              exact
                ((firstMissedSemanticResidual?_none_iff_listedClosed
                  projection cover sourceSupport targetSupport rest).mp
                  htail) residual hlisted hresidual hsource
      · intro hclosed
        by_cases hmissed :
          SemanticProjectedResidual projection cover head /\
            sourceSupport head /\ Not (targetSupport head)
        · have htarget : targetSupport head :=
            hclosed head (by simp) hmissed.1 hmissed.2.1
          exact False.elim (hmissed.2.2 htarget)
        · have htailClosed :
            ListedSourceSemanticResidualsClosed
              projection cover sourceSupport targetSupport rest := by
            intro residual hmem hresidual hsource
            exact hclosed residual (by simp [hmem]) hresidual hsource
          have htailNone :
            firstMissedSemanticResidual?
                projection cover sourceSupport targetSupport rest = none :=
            (firstMissedSemanticResidual?_none_iff_listedClosed
              projection cover sourceSupport targetSupport rest).mpr
              htailClosed
          simp [firstMissedSemanticResidual?, hmissed, htailNone]

/--
If the source is closed and the scan order covers the source-supported
residuals, no missed residual is equivalent to target semantic repair closure.
-/
theorem firstMissedSemanticResidual?_none_iff_target_semanticRepairClosed
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport]
    {atoms : List Atom}
    (hcomplete :
      ListedSourceSemanticResidualsComplete
        projection cover sourceSupport atoms)
    (hsourceClosed :
      SemanticRepairClosed projection cover sourceSupport) :
    firstMissedSemanticResidual?
        projection cover sourceSupport targetSupport atoms = none <->
      SemanticRepairClosed projection cover targetSupport := by
  constructor
  · intro hnone residual hresidual
    have hsource : sourceSupport residual :=
      hsourceClosed residual hresidual
    have hlisted : residual ∈ atoms :=
      hcomplete residual hresidual hsource
    exact
      ((firstMissedSemanticResidual?_none_iff_listedClosed
        projection cover sourceSupport targetSupport atoms).mp
        hnone) residual hlisted hresidual hsource
  · intro htargetClosed
    apply
      (firstMissedSemanticResidual?_none_iff_listedClosed
        projection cover sourceSupport targetSupport atoms).mpr
    intro residual _hlisted hresidual _hsource
    exact htargetClosed residual hresidual

/--
Under the same component projection, a returned scanner witness determines a
residual alias gap.
-/
theorem firstMissedSemanticResidual?_some_aliasGap_of_sameComponentProjection
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    [DecidablePred (fun atom => SemanticProjectedResidual projection cover atom)]
    [DecidablePred sourceSupport]
    [DecidablePred targetSupport]
    {atoms : List Atom}
    {residual : Atom}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hscan :
      firstMissedSemanticResidual?
          projection cover sourceSupport targetSupport atoms =
        some residual) :
    ResidualAliasGap projection cover sourceSupport targetSupport := by
  exact
    residualAliasGap_of_missedSemanticResidual_of_sameComponentProjection
      hsame
      (firstMissedSemanticResidual?_some_missedSemanticResidual hscan)

/-! ## Transport residual scanner -/

/-- A target atom has a supported source preimage under a semantic transport. -/
def TransportSupportedTarget
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (sourceSupport : Source -> Prop)
    (target : Target) : Prop :=
  exists source, sourceSupport source /\ transport source = target

/-- The list contains every target semantic residual. -/
def ListedTargetSemanticResidualsComplete
    {Target : Type v}
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (targets : List Target) : Prop :=
  forall target,
    SemanticProjectedResidual targetProjection targetCover target ->
      target ∈ targets

/-- Every listed target residual has a supported source preimage. -/
def ListedTargetResidualsSupported
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    (targets : List Target) : Prop :=
  forall target,
    target ∈ targets ->
      SemanticProjectedResidual targetProjection targetCover target ->
        TransportSupportedTarget transport sourceSupport target

/-- First listed target residual without a supported source preimage. -/
def firstUnsupportedTargetResidual?
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)] :
    List Target -> Option Target
  | [] => none
  | target :: rest =>
      if SemanticProjectedResidual targetProjection targetCover target /\
          Not (TransportSupportedTarget transport sourceSupport target) then
        some target
      else
        firstUnsupportedTargetResidual?
          transport targetProjection targetCover sourceSupport rest

/-- A returned target is a member of the supplied transport scan order. -/
theorem firstUnsupportedTargetResidual?_some_mem
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)] :
    forall {targets : List Target} {targetResidual : Target},
      firstUnsupportedTargetResidual?
          transport targetProjection targetCover sourceSupport targets =
        some targetResidual ->
        targetResidual ∈ targets
  | [], _targetResidual, hsome => by
      cases hsome
  | head :: rest, targetResidual, hsome => by
      by_cases hmissed :
        SemanticProjectedResidual targetProjection targetCover head /\
          Not (TransportSupportedTarget transport sourceSupport head)
      · have htarget : targetResidual = head := by
          simpa [firstUnsupportedTargetResidual?, hmissed] using hsome.symm
        subst targetResidual
        simp
      · have htail :
          firstUnsupportedTargetResidual?
              transport targetProjection targetCover sourceSupport rest =
            some targetResidual := by
          simpa [firstUnsupportedTargetResidual?, hmissed] using hsome
        exact List.mem_cons_of_mem head
          (firstUnsupportedTargetResidual?_some_mem
            transport targetProjection targetCover sourceSupport htail)

/-- A returned target residual is genuinely unsupported by the source support. -/
theorem firstUnsupportedTargetResidual?_some_missed
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)] :
    forall {targets : List Target} {targetResidual : Target},
      firstUnsupportedTargetResidual?
          transport targetProjection targetCover sourceSupport targets =
        some targetResidual ->
        SemanticProjectedResidual targetProjection targetCover targetResidual /\
          Not (TransportSupportedTarget transport sourceSupport targetResidual)
  | [], _targetResidual, hsome => by
      cases hsome
  | head :: rest, targetResidual, hsome => by
      by_cases hmissed :
        SemanticProjectedResidual targetProjection targetCover head /\
          Not (TransportSupportedTarget transport sourceSupport head)
      · have htarget : targetResidual = head := by
          simpa [firstUnsupportedTargetResidual?, hmissed] using hsome.symm
        subst targetResidual
        exact hmissed
      · have htail :
          firstUnsupportedTargetResidual?
              transport targetProjection targetCover sourceSupport rest =
            some targetResidual := by
          simpa [firstUnsupportedTargetResidual?, hmissed] using hsome
        exact
          firstUnsupportedTargetResidual?_some_missed
            transport targetProjection targetCover sourceSupport htail

/-- A returned target residual gives the Cycle 85 missed-transport witness. -/
theorem firstUnsupportedTargetResidual?_some_missedTargetResidualTransport
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)]
    {targets : List Target}
    {targetResidual : Target}
    (hscan :
      firstUnsupportedTargetResidual?
          transport targetProjection targetCover sourceSupport targets =
        some targetResidual) :
    MissedTargetResidualTransport
      transport targetProjection targetCover sourceSupport := by
  rcases
      firstUnsupportedTargetResidual?_some_missed
        transport targetProjection targetCover sourceSupport hscan with
    ⟨htargetResidual, hunsupported⟩
  exact
    ⟨targetResidual, htargetResidual,
      by
        intro source hsource htransport
        exact hunsupported ⟨source, hsource, htransport⟩⟩

/--
The transport scanner returns none exactly when every listed target residual
has a supported source preimage.
-/
theorem firstUnsupportedTargetResidual?_none_iff_listedSupported
    {Source : Type u}
    {Target : Type v}
    (transport : Source -> Target)
    (targetProjection : Target -> BridgeComponent)
    (targetCover : HandoffCechCover)
    (sourceSupport : Source -> Prop)
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)] :
    forall targets,
      firstUnsupportedTargetResidual?
          transport targetProjection targetCover sourceSupport targets = none <->
        ListedTargetResidualsSupported
          transport targetProjection targetCover sourceSupport targets
  | [] => by
      constructor
      · intro _ target hmem _htargetResidual
        cases hmem
      · intro _
        rfl
  | head :: rest => by
      constructor
      · intro hnone target hmem htargetResidual
        by_cases hmissed :
          SemanticProjectedResidual targetProjection targetCover head /\
            Not (TransportSupportedTarget transport sourceSupport head)
        · have hsome :
            firstUnsupportedTargetResidual?
                transport targetProjection targetCover sourceSupport
                (head :: rest) =
              some head := by
            simp [firstUnsupportedTargetResidual?, hmissed]
          rw [hsome] at hnone
          cases hnone
        · have htail :
            firstUnsupportedTargetResidual?
                transport targetProjection targetCover sourceSupport
                rest = none := by
            simpa [firstUnsupportedTargetResidual?, hmissed] using hnone
          cases hmem with
          | head =>
              by_contra hunsupported
              exact hmissed ⟨htargetResidual, hunsupported⟩
          | tail _ hlisted =>
              exact
                ((firstUnsupportedTargetResidual?_none_iff_listedSupported
                  transport targetProjection targetCover sourceSupport rest).mp
                  htail) target hlisted htargetResidual
      · intro hsupported
        by_cases hmissed :
          SemanticProjectedResidual targetProjection targetCover head /\
            Not (TransportSupportedTarget transport sourceSupport head)
        · have hsupp : TransportSupportedTarget transport sourceSupport head :=
            hsupported head (by simp) hmissed.1
          exact False.elim (hmissed.2 hsupp)
        · have htailSupported :
            ListedTargetResidualsSupported
              transport targetProjection targetCover sourceSupport rest := by
            intro target hmem htargetResidual
            exact hsupported target (by simp [hmem]) htargetResidual
          have htailNone :
            firstUnsupportedTargetResidual?
                transport targetProjection targetCover sourceSupport rest =
              none :=
            (firstUnsupportedTargetResidual?_none_iff_listedSupported
              transport targetProjection targetCover sourceSupport rest).mpr
              htailSupported
          simp [firstUnsupportedTargetResidual?, hmissed, htailNone]

/--
When the supplied target order covers every target residual, no unsupported
target residual is equivalent to the Cycle 85 supported-lift criterion.
-/
theorem firstUnsupportedTargetResidual?_none_iff_targetResidualSupported
    {Source : Type u}
    {Target : Type v}
    {transport : Source -> Target}
    {targetProjection : Target -> BridgeComponent}
    {targetCover : HandoffCechCover}
    {sourceSupport : Source -> Prop}
    [DecidablePred (fun target =>
      SemanticProjectedResidual targetProjection targetCover target)]
    [DecidablePred
      (TransportSupportedTarget transport sourceSupport)]
    {targets : List Target}
    (hcomplete :
      ListedTargetSemanticResidualsComplete
        targetProjection targetCover targets) :
    firstUnsupportedTargetResidual?
        transport targetProjection targetCover sourceSupport targets = none <->
      TargetResidualSupportedBySource
        transport targetProjection targetCover sourceSupport := by
  constructor
  · intro hnone targetResidual htargetResidual
    have hlisted : targetResidual ∈ targets :=
      hcomplete targetResidual htargetResidual
    exact
      ((firstUnsupportedTargetResidual?_none_iff_listedSupported
        transport targetProjection targetCover sourceSupport targets).mp
        hnone) targetResidual hlisted htargetResidual
  · intro hsupported
    apply
      (firstUnsupportedTargetResidual?_none_iff_listedSupported
        transport targetProjection targetCover sourceSupport targets).mpr
    intro target _hlisted htargetResidual
    exact hsupported target htargetResidual

/-! ## Selected refined semantic scanner -/

open RefinedSemanticRepairAtom

/-- Selected finite scan order for the repair-frontier refined residual fiber. -/
def selectedSemanticResidualScanOrder : List RefinedSemanticRepairAtom :=
  [repairFrontierSurface, repairFrontierObligation]

instance selected_semanticProjectedResidual_decidable :
    DecidablePred
      (fun atom =>
        SemanticProjectedResidual
          refinedSemanticComponent repairFrontierOverlapBasisCover atom) := by
  intro atom
  cases atom
  · exact isFalse (by
      intro hresidual
      have hcomponent :
          BridgeComponent.trace = BridgeComponent.repairFrontier :=
        (repairFrontierLawDeletion_componentSupport_iff
          BridgeComponent.trace).mp
          (by
            simpa [SemanticProjectedResidual, refinedSemanticComponent,
              repairFrontierOverlapBasisCover, HandoffCechOverlapSupport]
              using hresidual)
      cases hcomponent)
  · exact isTrue
      ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)
  · exact isTrue
      ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)

instance completeRepairSupport_decidable :
    DecidablePred completeRepairSupport := by
  intro atom
  cases atom <;> exact isTrue trivial

instance surfaceRepairSupport_decidable :
    DecidablePred surfaceRepairSupport := by
  intro atom
  cases atom
  · exact isTrue trivial
  · exact isTrue trivial
  · exact isFalse id

/-- The selected finite list covers every complete-support semantic residual. -/
theorem selectedSemanticResidualScanOrder_complete :
    ListedSourceSemanticResidualsComplete
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      selectedSemanticResidualScanOrder := by
  intro residual hresidual _hsource
  have hcomponent :
      refinedSemanticComponent residual = BridgeComponent.repairFrontier :=
    (repairFrontierLawDeletion_componentSupport_iff
      (refinedSemanticComponent residual)).mp
      (by
        simpa [SemanticProjectedResidual, repairFrontierOverlapBasisCover,
          HandoffCechOverlapSupport] using hresidual)
  cases residual <;>
    simp [selectedSemanticResidualScanOrder, refinedSemanticComponent]
      at hcomponent ⊢

/-- The selected finite list covers every target semantic residual. -/
theorem selectedSemanticTargetResidualScanOrder_complete :
    ListedTargetSemanticResidualsComplete
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      selectedSemanticResidualScanOrder := by
  intro residual hresidual
  have hcomponent :
      refinedSemanticComponent residual = BridgeComponent.repairFrontier :=
    (repairFrontierLawDeletion_componentSupport_iff
      (refinedSemanticComponent residual)).mp
      (by
        simpa [SemanticProjectedResidual, repairFrontierOverlapBasisCover,
          HandoffCechOverlapSupport] using hresidual)
  cases residual <;>
    simp [selectedSemanticResidualScanOrder, refinedSemanticComponent]
      at hcomponent ⊢

instance obligationAliasTransport_supported_decidable :
    DecidablePred
      (TransportSupportedTarget
        obligationAliasTransport completeRepairSupport) := by
  intro target
  cases target
  · exact isTrue ⟨traceContract, trivial, rfl⟩
  · exact isTrue ⟨repairFrontierSurface, trivial, rfl⟩
  · exact isFalse (by
      intro hsupported
      rcases hsupported with ⟨source, _hsource, htransport⟩
      cases source <;> cases htransport)

/-- The selected scanner returns the obligation residual as the first miss. -/
theorem selected_firstMissedSemanticResidual :
    firstMissedSemanticResidual?
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport
        selectedSemanticResidualScanOrder =
      some repairFrontierObligation := by
  have hobligation :
      SemanticProjectedResidual
        refinedSemanticComponent repairFrontierOverlapBasisCover
        repairFrontierObligation :=
    ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)
  simp [selectedSemanticResidualScanOrder, firstMissedSemanticResidual?,
    completeRepairSupport, surfaceRepairSupport, hobligation]

/--
The selected scanner result is exactly the selected missed repair-frontier
residual from Cycle 84.
-/
theorem selected_firstMissedSemanticResidual_witness :
    MissedSemanticResidual
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      surfaceRepairSupport :=
  firstMissedSemanticResidual?_some_missedSemanticResidual
    selected_firstMissedSemanticResidual

/-- The selected scanner has no miss exactly when the surface support is semantically closed. -/
theorem selected_firstMissedSemanticResidual_none_iff_surfaceClosure :
    firstMissedSemanticResidual?
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport
        selectedSemanticResidualScanOrder = none <->
      SemanticRepairClosed
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport := by
  exact
    firstMissedSemanticResidual?_none_iff_target_semanticRepairClosed
      selectedSemanticResidualScanOrder_complete
      completeRepairSupport_semanticRepairClosed

/-- The selected scanner reconstructs the selected residual alias gap. -/
theorem selected_firstMissedSemanticResidual_aliasGap :
    ResidualAliasGap
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      surfaceRepairSupport := by
  exact
    firstMissedSemanticResidual?_some_aliasGap_of_sameComponentProjection
      complete_and_surface_same_semanticComponentProjection
      selected_firstMissedSemanticResidual

/-- The selected transport scanner returns the unsupported obligation residual. -/
theorem selected_firstUnsupportedTargetResidual :
    firstUnsupportedTargetResidual?
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        selectedSemanticResidualScanOrder =
      some repairFrontierObligation := by
  have hsurfaceResidual :
      SemanticProjectedResidual
        refinedSemanticComponent repairFrontierOverlapBasisCover
        repairFrontierSurface :=
    ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)
  have hobligationResidual :
      SemanticProjectedResidual
        refinedSemanticComponent repairFrontierOverlapBasisCover
        repairFrontierObligation :=
    ((repairFrontierOverlapBasis).1 BridgeComponent.repairFrontier rfl)
  have hsurfaceSupported :
      TransportSupportedTarget
        obligationAliasTransport completeRepairSupport
        repairFrontierSurface :=
    ⟨repairFrontierSurface, trivial, rfl⟩
  have hobligationUnsupported :
      Not
        (TransportSupportedTarget
          obligationAliasTransport completeRepairSupport
          repairFrontierObligation) := by
    intro hsupported
    rcases hsupported with ⟨source, _hsource, htransport⟩
    cases source <;> cases htransport
  simp [selectedSemanticResidualScanOrder, firstUnsupportedTargetResidual?,
    hsurfaceResidual, hsurfaceSupported, hobligationResidual,
    hobligationUnsupported]

/-- The selected transport scanner gives the Cycle 85 missed target residual. -/
theorem selected_firstUnsupportedTargetResidual_missedTransport :
    MissedTargetResidualTransport
      obligationAliasTransport
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport :=
  firstUnsupportedTargetResidual?_some_missedTargetResidualTransport
    selected_firstUnsupportedTargetResidual

/--
The selected transport scanner has no unsupported target residual exactly when
the Cycle 85 supported-lift criterion holds.
-/
theorem selected_firstUnsupportedTargetResidual_none_iff_supportedLift :
    firstUnsupportedTargetResidual?
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        selectedSemanticResidualScanOrder = none <->
      TargetResidualSupportedBySource
        obligationAliasTransport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport := by
  exact
    firstUnsupportedTargetResidual?_none_iff_targetResidualSupported
      selectedSemanticTargetResidualScanOrder_complete

/-- The selected transport scanner certificate obstructs surface semantic closure. -/
theorem selected_firstUnsupportedTargetResidual_obstructs_surfaceClosure :
    Not
      (SemanticRepairClosed
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport) := by
  exact
    missedTargetResidualTransport_obstructs_semanticRepairClosed
      surfaceRepairSupport_is_obligationAliasTransport_image
      selected_firstUnsupportedTargetResidual_missedTransport

/-! ## Theorem package -/

/--
Cycle-86 theorem package: under a complete finite residual list, the scanner
classifies target semantic closure and returns missed residual / alias-gap
witnesses.
-/
theorem semanticResidualFiniteScanner_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop}
      [DecidablePred (fun atom =>
        SemanticProjectedResidual projection cover atom)]
      [DecidablePred sourceSupport]
      [DecidablePred targetSupport]
      {atoms : List Atom},
      ListedSourceSemanticResidualsComplete
          projection cover sourceSupport atoms ->
        SemanticRepairClosed projection cover sourceSupport ->
          (firstMissedSemanticResidual?
              projection cover sourceSupport targetSupport atoms = none <->
            SemanticRepairClosed projection cover targetSupport)) /\
      (forall {Atom : Type u}
        {projection : Atom -> BridgeComponent}
        {cover : HandoffCechCover}
        {sourceSupport targetSupport : Atom -> Prop}
        [DecidablePred (fun atom =>
          SemanticProjectedResidual projection cover atom)]
        [DecidablePred sourceSupport]
        [DecidablePred targetSupport]
        {atoms : List Atom}
        {residual : Atom},
        firstMissedSemanticResidual?
            projection cover sourceSupport targetSupport atoms =
          some residual ->
          MissedSemanticResidual
            projection cover sourceSupport targetSupport) /\
      (forall {Atom : Type u}
        {projection : Atom -> BridgeComponent}
        {cover : HandoffCechCover}
        {sourceSupport targetSupport : Atom -> Prop}
        [DecidablePred (fun atom =>
          SemanticProjectedResidual projection cover atom)]
        [DecidablePred sourceSupport]
        [DecidablePred targetSupport]
        {atoms : List Atom}
        {residual : Atom},
        SameSemanticComponentProjection projection sourceSupport targetSupport ->
          firstMissedSemanticResidual?
              projection cover sourceSupport targetSupport atoms =
            some residual ->
            ResidualAliasGap projection cover sourceSupport targetSupport) /\
      (forall {Source : Type u}
        {Target : Type v}
        {transport : Source -> Target}
        {targetProjection : Target -> BridgeComponent}
        {targetCover : HandoffCechCover}
        {sourceSupport : Source -> Prop}
        [DecidablePred (fun target =>
          SemanticProjectedResidual targetProjection targetCover target)]
        [DecidablePred
          (TransportSupportedTarget transport sourceSupport)]
        {targets : List Target},
        ListedTargetSemanticResidualsComplete
            targetProjection targetCover targets ->
          (firstUnsupportedTargetResidual?
              transport targetProjection targetCover sourceSupport targets =
            none <->
            TargetResidualSupportedBySource
              transport targetProjection targetCover sourceSupport)) /\
      (forall {Source : Type u}
        {Target : Type v}
        {transport : Source -> Target}
        {targetProjection : Target -> BridgeComponent}
        {targetCover : HandoffCechCover}
        {sourceSupport : Source -> Prop}
        [DecidablePred (fun target =>
          SemanticProjectedResidual targetProjection targetCover target)]
        [DecidablePred
          (TransportSupportedTarget transport sourceSupport)]
        {targets : List Target}
        {targetResidual : Target},
        firstUnsupportedTargetResidual?
            transport targetProjection targetCover sourceSupport targets =
          some targetResidual ->
          MissedTargetResidualTransport
            transport targetProjection targetCover sourceSupport) /\
      firstMissedSemanticResidual?
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          surfaceRepairSupport
          selectedSemanticResidualScanOrder =
        some repairFrontierObligation /\
      (firstMissedSemanticResidual?
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          surfaceRepairSupport
          selectedSemanticResidualScanOrder = none <->
        SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      MissedSemanticResidual
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport /\
      ResidualAliasGap
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport /\
      firstUnsupportedTargetResidual?
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          selectedSemanticResidualScanOrder =
        some repairFrontierObligation /\
      (firstUnsupportedTargetResidual?
          obligationAliasTransport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          selectedSemanticResidualScanOrder = none <->
        TargetResidualSupportedBySource
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
        (SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport}
        {atoms} =>
        firstMissedSemanticResidual?_none_iff_target_semanticRepairClosed,
      fun {Atom} {projection} {cover} {sourceSupport} {targetSupport}
        {atoms} {residual} =>
        firstMissedSemanticResidual?_some_missedSemanticResidual,
      fun {Atom} {projection} {cover} {sourceSupport} {targetSupport}
        {atoms} {residual} =>
        firstMissedSemanticResidual?_some_aliasGap_of_sameComponentProjection,
      fun {Source} {Target} {transport} {targetProjection} {targetCover}
        {sourceSupport} {targets} =>
        firstUnsupportedTargetResidual?_none_iff_targetResidualSupported,
      fun {Source} {Target} {transport} {targetProjection} {targetCover}
        {sourceSupport} {targets} {targetResidual} =>
        firstUnsupportedTargetResidual?_some_missedTargetResidualTransport,
      selected_firstMissedSemanticResidual,
      selected_firstMissedSemanticResidual_none_iff_surfaceClosure,
      selected_firstMissedSemanticResidual_witness,
      selected_firstMissedSemanticResidual_aliasGap,
      selected_firstUnsupportedTargetResidual,
      selected_firstUnsupportedTargetResidual_none_iff_supportedLift,
      selected_firstUnsupportedTargetResidual_missedTransport,
      selected_firstUnsupportedTargetResidual_obstructs_surfaceClosure⟩

end SemanticResidualFiniteScanner
end QualitySurface
end ResearchLean.AG
