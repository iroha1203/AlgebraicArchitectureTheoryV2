import Formal.Arch.LSP

namespace Formal.Arch

universe u v w

/--
Local implementation replacement contract.

The contract keeps the projection bridge and observation bridge as independent
axes sharing the same interface projection.
-/
def LocalReplacementContract {C : Type u} {A : Type v} {Obs : Type w}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    (O : Observation C Obs) : Prop :=
  DIPCompatible G π GA ∧ ObservationFactorsThrough π O

/-- A local replacement contract includes projection soundness. -/
theorem projectionSound_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : LocalReplacementContract G π GA O) : ProjectionSound G π GA :=
  h.1.1

/-- A local replacement contract includes observation factorization. -/
theorem observationFactorsThrough_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : LocalReplacementContract G π GA O) : ObservationFactorsThrough π O :=
  h.2

/-- A local replacement contract gives observation preservation on each abstraction fiber. -/
theorem lspCompatible_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : LocalReplacementContract G π GA O) : LSPCompatible π O :=
  lspCompatible_of_observationFactorsThrough
    (observationFactorsThrough_of_localReplacementContract h)

/--
A local replacement contract preserves selected observations between
implementations exposed through the same interface.
-/
theorem observationallyEquivalent_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs} {x y : C}
    (h : LocalReplacementContract G π GA O)
    (hInterface : π.expose x = π.expose y) :
    ObservationallyEquivalent O x y :=
  lspCompatible_of_localReplacementContract h hInterface

/--
Unfolding a local replacement contract through projection-obstruction
exactness keeps the representative-stability and observation-factorization
axes explicit.
-/
theorem localReplacementContract_iff_noProjectionObstruction_and_representativeStable_and_observationFactorsThrough
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs} :
    LocalReplacementContract G π GA O ↔
      NoProjectionObstruction G π GA ∧ RepresentativeStable G π ∧
        ObservationFactorsThrough π O := by
  constructor
  · intro h
    exact ⟨projectionSound_iff_noProjectionObstruction.mp h.1.1, h.1.2, h.2⟩
  · rintro ⟨hNoProjection, hStable, hObservation⟩
    exact ⟨⟨projectionSound_iff_noProjectionObstruction.mpr hNoProjection,
      hStable⟩, hObservation⟩

/--
A local replacement contract eliminates projection obstruction witnesses and
LSP obstruction witnesses simultaneously.
-/
theorem noProjectionObstruction_and_noLSPObstruction_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    (h : LocalReplacementContract G π GA O) :
    NoProjectionObstruction G π GA ∧ NoLSPObstruction π O :=
  ⟨projectionSound_iff_noProjectionObstruction.mp
      (projectionSound_of_localReplacementContract h),
    lspCompatible_iff_noLSPObstruction.mp
      (lspCompatible_of_observationFactorsThrough
        (observationFactorsThrough_of_localReplacementContract h))⟩

/--
A local replacement contract simultaneously zeroes the measured projection and
LSP violation counts.
-/
theorem violationCounts_eq_zero_of_localReplacementContract
    {C : Type u} {A : Type v} {Obs : Type w}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    {O : Observation C Obs}
    [DecidableRel G.edge] [DecidableRel GA.edge] [DecidableEq A] [DecidableEq Obs]
    (components implementations : List C)
    (h : LocalReplacementContract G π GA O) :
    projectionSoundnessViolation G π GA components = 0 ∧
      lspViolationCount π O implementations = 0 :=
  ⟨projectionSoundnessViolation_eq_zero_of_projectionSound components
      (projectionSound_of_localReplacementContract h),
    lspViolationCount_eq_zero_of_observationFactorsThrough implementations
      (observationFactorsThrough_of_localReplacementContract h)⟩

end Formal.Arch
