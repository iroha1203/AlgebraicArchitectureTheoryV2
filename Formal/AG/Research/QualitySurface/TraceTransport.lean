import Formal.AG.Research.QualitySurface.ProfileCurvature

/-!
Cycle 4 evidence for `G-aat-quality-surface-01`.

The file separates support transport from trace-token transport. Trace
naturality preserves trace availability along transported support, while a
finite witness shows that support can be transported and still leave a
trace-missing target atom when naturality fails.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace TraceTransport

universe u v w x

/-- The support obtained by transporting a source support along an atom map. -/
def TransportedSupport {Source : Type u} {Target : Type v}
    (atomMap : Source -> Target) (sourceSupport : Set Source) : Set Target :=
  fun target => ∃ source, sourceSupport source ∧ atomMap source = target

/-- A partial trace field is available on every atom in a selected support. -/
def TraceAvailableOn {Atom : Type u} {TraceToken : Type v}
    (support : Set Atom) (traceField : Atom -> Option TraceToken) : Prop :=
  ∀ atom, support atom -> ∃ token, traceField atom = some token

/-- A selected support has at least one atom whose trace token is missing. -/
def TraceMissingOn {Atom : Type u} {TraceToken : Type v}
    (support : Set Atom) (traceField : Atom -> Option TraceToken) : Prop :=
  ∃ atom, support atom ∧ traceField atom = none

/--
Trace naturality for one profile change.

On selected source support, reading the target trace after atom transport agrees
with transporting the source trace token.
-/
def TraceNatural {Source : Type u} {Target : Type v}
    {SourceTrace : Type w} {TargetTrace : Type x}
    (sourceSupport : Set Source) (atomMap : Source -> Target)
    (traceMap : SourceTrace -> TargetTrace)
    (sourceTraceField : Source -> Option SourceTrace)
    (targetTraceField : Target -> Option TargetTrace) : Prop :=
  ∀ source, sourceSupport source ->
    targetTraceField (atomMap source) =
      Option.map traceMap (sourceTraceField source)

/--
Trace naturality preserves trace availability along transported support.

This is the positive bridge theorem: if the source support is traced and the
profile change respects trace tokens, then every transported target support atom
is traced.
-/
theorem traceAvailableOn_transport_of_traceNatural
    {Source : Type u} {Target : Type v}
    {SourceTrace : Type w} {TargetTrace : Type x}
    {sourceSupport : Set Source} {atomMap : Source -> Target}
    {traceMap : SourceTrace -> TargetTrace}
    {sourceTraceField : Source -> Option SourceTrace}
    {targetTraceField : Target -> Option TargetTrace}
    (hsource : TraceAvailableOn sourceSupport sourceTraceField)
    (hnatural :
      TraceNatural sourceSupport atomMap traceMap sourceTraceField
        targetTraceField) :
    TraceAvailableOn (TransportedSupport atomMap sourceSupport)
      targetTraceField := by
  intro target htarget
  rcases htarget with ⟨source, hsourceSupport, hmap⟩
  rcases hsource source hsourceSupport with ⟨token, htoken⟩
  refine ⟨traceMap token, ?_⟩
  rw [← hmap]
  rw [hnatural source hsourceSupport, htoken]
  rfl

/-! ## A finite support-transport / trace-missing witness -/

/-- Source atoms before the profile change. -/
inductive SourceAtom where
  | a
  | b
  deriving DecidableEq, Fintype

/-- Target atoms after the profile change. -/
inductive TargetAtom where
  | aPrime
  | bPrime
  deriving DecidableEq, Fintype

/-- Trace tokens available on the source certificate. -/
inductive SourceTraceToken where
  | refA
  | refB
  deriving DecidableEq

/-- Trace tokens available on the target certificate. -/
inductive TargetTraceToken where
  | refA
  | refB
  deriving DecidableEq

open SourceAtom TargetAtom

/-- Both source atoms belong to the selected support. -/
def sourceSupport : Set SourceAtom :=
  fun _ => True

/-- The profile change transports each source atom to its target atom. -/
def atomTransport : SourceAtom -> TargetAtom
  | a => aPrime
  | b => bPrime

/-- Source trace tokens are renamed along the profile change. -/
def traceTokenTransport : SourceTraceToken -> TargetTraceToken
  | SourceTraceToken.refA => TargetTraceToken.refA
  | SourceTraceToken.refB => TargetTraceToken.refB

/-- The source trace field is available on both selected support atoms. -/
def sourceTraceField : SourceAtom -> Option SourceTraceToken
  | a => some SourceTraceToken.refA
  | b => some SourceTraceToken.refB

/-- A target trace field that preserves trace tokens naturally. -/
def targetTraceFieldNatural : TargetAtom -> Option TargetTraceToken
  | aPrime => some TargetTraceToken.refA
  | bPrime => some TargetTraceToken.refB

/-- A target trace field where the transported `b` atom has no available token. -/
def targetTraceFieldMissing : TargetAtom -> Option TargetTraceToken
  | aPrime => some TargetTraceToken.refA
  | bPrime => none

/-- The transported target support. -/
def targetSupport : Set TargetAtom :=
  TransportedSupport atomTransport sourceSupport

/-- The source support is fully traced. -/
theorem sourceTraceAvailable :
    TraceAvailableOn sourceSupport sourceTraceField := by
  intro atom _hatom
  cases atom with
  | a => exact ⟨SourceTraceToken.refA, rfl⟩
  | b => exact ⟨SourceTraceToken.refB, rfl⟩

/-- The natural target trace field satisfies trace naturality. -/
theorem targetTraceNatural :
    TraceNatural sourceSupport atomTransport traceTokenTransport
      sourceTraceField targetTraceFieldNatural := by
  intro source _hsource
  cases source <;> rfl

/-- Natural trace transport preserves target trace availability. -/
theorem targetTraceAvailable_of_traceNatural :
    TraceAvailableOn targetSupport targetTraceFieldNatural :=
  traceAvailableOn_transport_of_traceNatural sourceTraceAvailable
    targetTraceNatural

/-- The transported support contains `bPrime`. -/
theorem bPrime_mem_targetSupport : targetSupport bPrime := by
  exact ⟨SourceAtom.b, trivial, rfl⟩

/-- The missing target trace field has no token at `bPrime`. -/
theorem targetTraceMissing_bPrime :
    targetTraceFieldMissing bPrime = none :=
  rfl

/-- Support transport can hold while the transported support has a missing trace. -/
theorem supportTransported_but_traceMissing :
    targetSupport bPrime ∧ targetTraceFieldMissing bPrime = none :=
  And.intro bPrime_mem_targetSupport targetTraceMissing_bPrime

/-- The missing target trace field is not trace-natural. -/
theorem targetTraceMissing_not_traceNatural :
    ¬ TraceNatural sourceSupport atomTransport traceTokenTransport
      sourceTraceField targetTraceFieldMissing := by
  intro hnatural
  have hb := hnatural SourceAtom.b trivial
  change (none : Option TargetTraceToken) =
    some TargetTraceToken.refB at hb
  cases hb

/-- The finite missing-trace witness on transported support. -/
theorem missingTraceOn_targetSupport :
    TraceMissingOn targetSupport targetTraceFieldMissing :=
  ⟨bPrime, bPrime_mem_targetSupport, targetTraceMissing_bPrime⟩

/--
The cycle-4 finite bridge witness: support transport alone does not transport
traceability. The target support contains `bPrime`, its trace token is missing,
and the missing trace field fails trace naturality.
-/
theorem support_transport_without_trace_naturality_has_missing_trace :
    targetSupport bPrime ∧
      targetTraceFieldMissing bPrime = none ∧
        ¬ TraceNatural sourceSupport atomTransport traceTokenTransport
          sourceTraceField targetTraceFieldMissing := by
  exact And.intro bPrime_mem_targetSupport
    (And.intro targetTraceMissing_bPrime targetTraceMissing_not_traceNatural)

end TraceTransport
end QualitySurface
end Formal.AG.Research
