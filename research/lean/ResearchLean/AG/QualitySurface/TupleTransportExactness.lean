import ResearchLean.AG.QualitySurface.ProfileTupleIntegration

/-!
Cycle 14 evidence for `G-aat-quality-surface-01`.

This file treats transport of profile-typed certificate tuples as a
non-definitional comparison map between profile fibers. Exactness results are
relative to explicitly supplied component transport laws; no canonical global
transport, source extraction completeness, or whole-codebase quality claim is
asserted.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace TupleTransportExactness

open TraceLocus

abbrev TupleProfile :=
  ProfileTupleIntegration.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Non-definitional tuple transports -/

/-- A comparison map between two profile-typed tuple fibers. -/
structure TupleTransport (p q : TupleProfile) where
  map : TupleCertificateAt p -> TupleCertificateAt q

/-- Transport preserves the selected tuple support. -/
def PreservesTupleSupport {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, c.selectedSupport atom -> (τ.map c).selectedSupport atom

/-- Transport reflects the selected tuple support. -/
def ReflectsTupleSupport {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, (τ.map c).selectedSupport atom -> c.selectedSupport atom

/-- Transport preserves missing trace values. -/
def PreservesTupleTraceNone {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, c.traceField atom = none -> (τ.map c).traceField atom = none

/-- Transport reflects missing trace values. -/
def ReflectsTupleTraceNone {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, (τ.map c).traceField atom = none -> c.traceField atom = none

/-- Transport preserves repair-frontier membership. -/
def PreservesTupleRepairFrontier {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, c.repairFrontier atom -> (τ.map c).repairFrontier atom

/-- Transport reflects repair-frontier membership. -/
def ReflectsTupleRepairFrontier {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom, (τ.map c).repairFrontier atom -> c.repairFrontier atom

/-- Transport preserves tuple missing loci. -/
def PreservesTupleTraceMissingLocus {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom,
    ProfileTupleIntegration.TupleTraceMissingLocus c atom ->
      ProfileTupleIntegration.TupleTraceMissingLocus (τ.map c) atom

/-- Transport reflects tuple missing loci. -/
def ReflectsTupleTraceMissingLocus {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c atom,
    ProfileTupleIntegration.TupleTraceMissingLocus (τ.map c) atom ->
      ProfileTupleIntegration.TupleTraceMissingLocus c atom

/--
Support preservation plus trace-none preservation is enough to preserve the
tuple missing locus.
-/
theorem tupleTransport_preserves_traceMissingLocus
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hsupport : PreservesTupleSupport τ)
    (htrace : PreservesTupleTraceNone τ) :
    PreservesTupleTraceMissingLocus τ := by
  intro c atom hmissing
  exact ⟨hsupport c atom hmissing.1, htrace c atom hmissing.2⟩

/--
Support reflection plus trace-none reflection is enough to reflect the tuple
missing locus.
-/
theorem tupleTransport_reflects_traceMissingLocus
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hsupport : ReflectsTupleSupport τ)
    (htrace : ReflectsTupleTraceNone τ) :
    ReflectsTupleTraceMissingLocus τ := by
  intro c atom hmissing
  exact ⟨hsupport c atom hmissing.1, htrace c atom hmissing.2⟩

/-- Bundled bidirectional component laws for tuple repair exactness. -/
structure BidirectionalTupleTransport {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop where
  preservesSupport : PreservesTupleSupport τ
  reflectsSupport : ReflectsTupleSupport τ
  preservesTraceNone : PreservesTupleTraceNone τ
  reflectsTraceNone : ReflectsTupleTraceNone τ
  preservesRepairFrontier : PreservesTupleRepairFrontier τ
  reflectsRepairFrontier : ReflectsTupleRepairFrontier τ

/-- Bidirectional component laws give bidirectional missing-locus transport. -/
theorem bidirectional_transport_missingLocus
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ) :
    PreservesTupleTraceMissingLocus τ ∧
      ReflectsTupleTraceMissingLocus τ := by
  exact ⟨tupleTransport_preserves_traceMissingLocus τ
      hlaws.preservesSupport hlaws.preservesTraceNone,
    tupleTransport_reflects_traceMissingLocus τ
      hlaws.reflectsSupport hlaws.reflectsTraceNone⟩

/-- Bidirectional component laws make missing-locus membership invariant. -/
theorem tupleTransport_traceMissingLocus_iff
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ)
    (c : TupleCertificateAt p) (atom : LocusAtom) :
    ProfileTupleIntegration.TupleTraceMissingLocus (τ.map c) atom ↔
      ProfileTupleIntegration.TupleTraceMissingLocus c atom := by
  constructor
  · intro hmissing
    exact tupleTransport_reflects_traceMissingLocus τ
      hlaws.reflectsSupport hlaws.reflectsTraceNone c atom hmissing
  · intro hmissing
    exact tupleTransport_preserves_traceMissingLocus τ
      hlaws.preservesSupport hlaws.preservesTraceNone c atom hmissing

/-- Bidirectional component laws make repair-frontier membership invariant. -/
theorem tupleTransport_repairFrontier_iff
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ)
    (c : TupleCertificateAt p) (atom : LocusAtom) :
    (τ.map c).repairFrontier atom ↔ c.repairFrontier atom := by
  constructor
  · intro hrepair
    exact hlaws.reflectsRepairFrontier c atom hrepair
  · intro hrepair
    exact hlaws.preservesRepairFrontier c atom hrepair

/--
Exact repair frontier is preserved by a bidirectional tuple transport.

Both directions of the component laws are needed: target repair is pulled back
to source repair, source exactness gives source missing, and source missing is
pushed forward again; the converse implication uses the dual path.
-/
theorem tupleTransport_preserves_repairFrontierExact
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ)
    {c : TupleCertificateAt p}
    (hexact : ProfileTupleIntegration.TupleRepairFrontierExact c) :
    ProfileTupleIntegration.TupleRepairFrontierExact (τ.map c) := by
  have hmissingPreserves :=
    tupleTransport_preserves_traceMissingLocus τ
      hlaws.preservesSupport hlaws.preservesTraceNone
  have hmissingReflects :=
    tupleTransport_reflects_traceMissingLocus τ
      hlaws.reflectsSupport hlaws.reflectsTraceNone
  intro atom
  constructor
  · intro hrepairTarget
    have hrepairSource :
        c.repairFrontier atom :=
      hlaws.reflectsRepairFrontier c atom hrepairTarget
    have hmissingSource :
        ProfileTupleIntegration.TupleTraceMissingLocus c atom :=
      (hexact atom).mp hrepairSource
    exact hmissingPreserves c atom hmissingSource
  · intro hmissingTarget
    have hmissingSource :
        ProfileTupleIntegration.TupleTraceMissingLocus c atom :=
      hmissingReflects c atom hmissingTarget
    have hrepairSource : c.repairFrontier atom :=
      (hexact atom).mpr hmissingSource
    exact hlaws.preservesRepairFrontier c atom hrepairSource

/-- Exact repair frontier reflects back through a bidirectional tuple transport. -/
theorem tupleTransport_reflects_repairFrontierExact
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ)
    {c : TupleCertificateAt p}
    (hexact : ProfileTupleIntegration.TupleRepairFrontierExact (τ.map c)) :
    ProfileTupleIntegration.TupleRepairFrontierExact c := by
  have hmissingPreserves :=
    tupleTransport_preserves_traceMissingLocus τ
      hlaws.preservesSupport hlaws.preservesTraceNone
  have hmissingReflects :=
    tupleTransport_reflects_traceMissingLocus τ
      hlaws.reflectsSupport hlaws.reflectsTraceNone
  intro atom
  constructor
  · intro hrepairSource
    have hrepairTarget :
        (τ.map c).repairFrontier atom :=
      hlaws.preservesRepairFrontier c atom hrepairSource
    have hmissingTarget :
        ProfileTupleIntegration.TupleTraceMissingLocus (τ.map c) atom :=
      (hexact atom).mp hrepairTarget
    exact hmissingReflects c atom hmissingTarget
  · intro hmissingSource
    have hmissingTarget :
        ProfileTupleIntegration.TupleTraceMissingLocus (τ.map c) atom :=
      hmissingPreserves c atom hmissingSource
    have hrepairTarget : (τ.map c).repairFrontier atom :=
      (hexact atom).mpr hmissingTarget
    exact hlaws.reflectsRepairFrontier c atom hrepairTarget

/-- Bidirectional tuple transport preserves exact repair frontier exactly. -/
theorem tupleTransport_exactRepair_iff_of_bidirectional
    {p q : TupleProfile} (τ : TupleTransport p q)
    (hlaws : BidirectionalTupleTransport τ)
    (c : TupleCertificateAt p) :
    ProfileTupleIntegration.TupleRepairFrontierExact (τ.map c) ↔
      ProfileTupleIntegration.TupleRepairFrontierExact c := by
  constructor
  · intro hexactTarget
    exact tupleTransport_reflects_repairFrontierExact
      τ hlaws hexactTarget
  · intro hexactSource
    exact tupleTransport_preserves_repairFrontierExact
      τ hlaws hexactSource

/-! ## Trace projection and protected-data boundary -/

/-- Transport commutes with trace-locus projection, stated pointwise. -/
def TupleTraceProjectionCommutes {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c : TupleCertificateAt p,
    (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).visibleScalarReading =
        (ProfileTupleIntegration.toTraceLocusCertificate c).visibleScalarReading ∧
      (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).verdict =
        (ProfileTupleIntegration.toTraceLocusCertificate c).verdict ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).selectedSupport atom ↔
          (ProfileTupleIntegration.toTraceLocusCertificate c).selectedSupport atom) ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).repairFrontier atom ↔
          (ProfileTupleIntegration.toTraceLocusCertificate c).repairFrontier atom) ∧
      (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).obligation =
        (ProfileTupleIntegration.toTraceLocusCertificate c).obligation ∧
      (∀ atom,
        (ProfileTupleIntegration.toTraceLocusCertificate (τ.map c)).traceField atom =
          (ProfileTupleIntegration.toTraceLocusCertificate c).traceField atom)

/-- Cross-profile equality of tuple protected data `(omega, R, T)`. -/
def SameTupleProtectedDataAcross {p q : TupleProfile}
    (source : TupleCertificateAt p) (target : TupleCertificateAt q) : Prop :=
  source.omega = target.omega ∧
    (∀ atom, source.repairFrontier atom ↔ target.repairFrontier atom) ∧
    (∀ atom, source.traceField atom = target.traceField atom)

/-- A transport preserves each tuple's protected data across profile fibers. -/
def PreservesTupleProtectedDataAcross {p q : TupleProfile}
    (τ : TupleTransport p q) : Prop :=
  ∀ c : TupleCertificateAt p, SameTupleProtectedDataAcross c (τ.map c)

/--
If one transported tuple visibly exhibits protected-data divergence from its
source, the transport is not protected-data preserving.
-/
theorem protectedDataDivergence_obstructs_losslessTupleTransport
    {p q : TupleProfile} (τ : TupleTransport p q)
    {c : TupleCertificateAt p}
    (hdivergence : ¬ SameTupleProtectedDataAcross c (τ.map c)) :
    ¬ PreservesTupleProtectedDataAcross τ := by
  intro hp
  exact hdivergence (hp c)

/-! ## Profile-changing grid-map transports -/

/--
A profile-changing transport induced by a supplied map between grid
certificates. The tuple's protected data is carried pointwise; only the profile
fiber changes through `gridMap`.
-/
def tupleTransportOfGridMap {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q) :
    TupleTransport p q where
  map := fun c =>
    { gridCertificate := gridMap c.gridCertificate
      sigma := c.sigma
      omega := c.omega
      selectedSupport := c.selectedSupport
      repairFrontier := c.repairFrontier
      nu := c.nu
      traceField := c.traceField }

/-- Grid-map transports satisfy all bidirectional component laws. -/
theorem tupleTransportOfGridMap_bidirectional
    {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q) :
    BidirectionalTupleTransport (tupleTransportOfGridMap gridMap) := by
  constructor
  · intro c atom hsupport
    exact hsupport
  · intro c atom hsupport
    exact hsupport
  · intro c atom htrace
    exact htrace
  · intro c atom htrace
    exact htrace
  · intro c atom hrepair
    exact hrepair
  · intro c atom hrepair
    exact hrepair

/-- Grid-map transports commute with trace-locus projection pointwise. -/
theorem tupleTransportOfGridMap_traceProjection_commutes
    {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q) :
    TupleTraceProjectionCommutes (tupleTransportOfGridMap gridMap) := by
  intro c
  exact ⟨rfl, rfl, by
    intro atom
    rfl,
    by
      intro atom
      rfl,
    rfl,
    by
      intro atom
      rfl⟩

/-- Grid-map transports preserve protected tuple data across profile fibers. -/
theorem tupleTransportOfGridMap_preserves_protectedDataAcross
    {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q) :
    PreservesTupleProtectedDataAcross (tupleTransportOfGridMap gridMap) := by
  intro c
  exact ⟨rfl, by
    intro atom
    rfl,
    by
      intro atom
      rfl⟩

/-- Exact repair is invariant under a supplied profile-changing grid map. -/
theorem tupleTransportOfGridMap_exactRepair_iff
    {p q : TupleProfile}
    (gridMap :
      ProfileGridHolonomy.CertificateAt p ->
        ProfileGridHolonomy.CertificateAt q)
    (c : TupleCertificateAt p) :
    ProfileTupleIntegration.TupleRepairFrontierExact
        ((tupleTransportOfGridMap gridMap).map c) ↔
      ProfileTupleIntegration.TupleRepairFrontierExact c :=
  tupleTransport_exactRepair_iff_of_bidirectional
    (tupleTransportOfGridMap gridMap)
    (tupleTransportOfGridMap_bidirectional gridMap)
    c

/-- The law-first grid path gives a concrete profile-changing tuple transport. -/
def lowCoarseToHighFineLawFirstTupleTransport :
    TupleTransport ProfileGridHolonomy.lowCoarse ProfileGridHolonomy.highFine :=
  tupleTransportOfGridMap ProfileGridHolonomy.lawFirstPath

/-- Exact repair is invariant along the law-first low-coarse to high-fine path. -/
theorem lawFirstTupleTransport_exactRepair_iff
    (c : TupleCertificateAt ProfileGridHolonomy.lowCoarse) :
    ProfileTupleIntegration.TupleRepairFrontierExact
        (lowCoarseToHighFineLawFirstTupleTransport.map c) ↔
      ProfileTupleIntegration.TupleRepairFrontierExact c :=
  tupleTransportOfGridMap_exactRepair_iff
    ProfileGridHolonomy.lawFirstPath c

/--
Cycle-14 theorem package: a tuple transport with bidirectional component laws
preserves and reflects missing loci, and exact repair is invariant. A supplied
grid-certificate map gives a concrete profile-changing instance.
-/
theorem tupleTransport_exactness_package :
    (∀ {p q : TupleProfile} (τ : TupleTransport p q),
      BidirectionalTupleTransport τ ->
        PreservesTupleTraceMissingLocus τ ∧
          ReflectsTupleTraceMissingLocus τ) ∧
      (∀ {p q : TupleProfile} (τ : TupleTransport p q),
        BidirectionalTupleTransport τ ->
          ∀ c : TupleCertificateAt p,
            (ProfileTupleIntegration.TupleRepairFrontierExact
                (τ.map c) ↔
              ProfileTupleIntegration.TupleRepairFrontierExact c)) ∧
      (∀ c : TupleCertificateAt ProfileGridHolonomy.lowCoarse,
        ProfileTupleIntegration.TupleRepairFrontierExact
            (lowCoarseToHighFineLawFirstTupleTransport.map c) ↔
      ProfileTupleIntegration.TupleRepairFrontierExact c) := by
  exact ⟨by
    intro p q τ hlaws
    exact bidirectional_transport_missingLocus τ hlaws,
    by
      intro p q τ hlaws c
      exact tupleTransport_exactRepair_iff_of_bidirectional τ hlaws c,
    lawFirstTupleTransport_exactRepair_iff⟩

/--
Cycle-14 boundary theorem: the law-first grid-map transport is lossless for
trace projection, exact repair, and protected tuple data. Therefore any
transported protected-data divergence would obstruct lossless tuple transport.
-/
theorem lawFirstTupleTransport_lossless_boundary :
    TupleTraceProjectionCommutes lowCoarseToHighFineLawFirstTupleTransport ∧
      PreservesTupleProtectedDataAcross
        lowCoarseToHighFineLawFirstTupleTransport ∧
      (∀ c : TupleCertificateAt ProfileGridHolonomy.lowCoarse,
        ProfileTupleIntegration.TupleRepairFrontierExact
            (lowCoarseToHighFineLawFirstTupleTransport.map c) ↔
          ProfileTupleIntegration.TupleRepairFrontierExact c) ∧
      (∀ c : TupleCertificateAt ProfileGridHolonomy.lowCoarse,
        ¬ SameTupleProtectedDataAcross c
            (lowCoarseToHighFineLawFirstTupleTransport.map c) ->
          ¬ PreservesTupleProtectedDataAcross
            lowCoarseToHighFineLawFirstTupleTransport) := by
  exact ⟨tupleTransportOfGridMap_traceProjection_commutes
      ProfileGridHolonomy.lawFirstPath,
    tupleTransportOfGridMap_preserves_protectedDataAcross
      ProfileGridHolonomy.lawFirstPath,
    lawFirstTupleTransport_exactRepair_iff,
    by
      intro c hdivergence
      exact protectedDataDivergence_obstructs_losslessTupleTransport
        lowCoarseToHighFineLawFirstTupleTransport hdivergence⟩

end TupleTransportExactness
end QualitySurface
end ResearchLean.AG
