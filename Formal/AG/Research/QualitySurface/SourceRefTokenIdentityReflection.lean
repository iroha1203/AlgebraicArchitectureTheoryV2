import Formal.AG.Research.QualitySurface.SourceRefTupleBridge

/-!
Cycle 16 evidence for `G-aat-quality-surface-01`.

This file strengthens the source-ref packet to tuple bridge from missing-locus
and repair-frontier exactness to source-ref token identity reflection. The
claim is relative to the finite supplied source-ref vocabulary and aligned
profile tuples; it does not assert source extraction completeness, ArchMap
correctness, or a global source-reference namespace.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SourceRefTokenIdentityReflection

open TraceLocus

abbrev TupleProfile :=
  SourceRefTupleBridge.TupleProfile

abbrev TupleCertificateAt :=
  ProfileTupleIntegration.TupleCertificateAt

/-! ## Token-level losslessness -/

/-- The finite source-ref to trace-token projection does not alias tokens. -/
theorem sourceRefToTraceToken_injective :
    Function.Injective CodebaseTracePacket.sourceRefToTraceToken := by
  intro token₁ token₂ htoken
  cases token₁ <;> cases token₂ <;> cases htoken <;> rfl

/--
Equality after mapping optional source-ref tokens to trace tokens reflects
equality before the projection.
-/
theorem sourceRefOptionMap_eq_iff
    (left right : Option CodebaseTracePacket.SourceRefToken) :
    Option.map CodebaseTracePacket.sourceRefToTraceToken left =
        Option.map CodebaseTracePacket.sourceRefToTraceToken right ↔
      left = right := by
  constructor
  · intro hmap
    cases left with
    | none =>
        cases right with
        | none => rfl
        | some token => cases hmap
    | some leftToken =>
        cases right with
        | none => cases hmap
        | some rightToken =>
            cases leftToken <;> cases rightToken <;> cases hmap <;> rfl
  · intro heq
    cases heq
    rfl

/-! ## Packet-level reflection -/

/--
Projected trace-field equality is equivalent to equality of the supplied
source-ref tables.
-/
theorem projectedTraceField_eq_iff_sourceRefTable
    (packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket) :
    (∀ atom,
      CodebaseTracePacket.projectedTraceField packet₁ atom =
        CodebaseTracePacket.projectedTraceField packet₂ atom) ↔
      ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom := by
  constructor
  · intro htrace codeAtom
    have hprojected :=
      htrace (CodebaseTracePacket.toLocusAtom codeAtom)
    have hsource :=
      (sourceRefOptionMap_eq_iff
        (packet₁.sourceRefTable
          (CodebaseTracePacket.fromLocusAtom
            (CodebaseTracePacket.toLocusAtom codeAtom)))
        (packet₂.sourceRefTable
          (CodebaseTracePacket.fromLocusAtom
            (CodebaseTracePacket.toLocusAtom codeAtom)))).mp
        hprojected
    simpa [SourceRefTupleBridge.from_to_locusAtom] using hsource
  · intro hsource atom
    change
      Option.map CodebaseTracePacket.sourceRefToTraceToken
          (packet₁.sourceRefTable
            (CodebaseTracePacket.fromLocusAtom atom)) =
        Option.map CodebaseTracePacket.sourceRefToTraceToken
          (packet₂.sourceRefTable
            (CodebaseTracePacket.fromLocusAtom atom))
    rw [hsource (CodebaseTracePacket.fromLocusAtom atom)]

/-- Projected trace-field equality reflects source-ref table equality. -/
theorem projectedTraceField_reflects_sourceRefTable
    (packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket)
    (htrace :
      ∀ atom,
        CodebaseTracePacket.projectedTraceField packet₁ atom =
          CodebaseTracePacket.projectedTraceField packet₂ atom) :
    ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom :=
  (projectedTraceField_eq_iff_sourceRefTable packet₁ packet₂).mp htrace

/-- Source-ref table equality preserves projected trace-field equality. -/
theorem sourceRefTable_preserves_projectedTraceField
    (packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket)
    (hsource :
      ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom) :
    ∀ atom,
      CodebaseTracePacket.projectedTraceField packet₁ atom =
        CodebaseTracePacket.projectedTraceField packet₂ atom :=
  (projectedTraceField_eq_iff_sourceRefTable packet₁ packet₂).mpr hsource

/-! ## Aligned tuple-level reflection -/

/--
For two aligned packet/tuple pairs, tuple trace-field equality is equivalent to
equality of the supplied source-ref tables.
-/
theorem aligned_tupleTraceField_eq_iff_sourceRefTable
    {profile₁ profile₂ : TupleProfile}
    {packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket}
    {tuple₁ : TupleCertificateAt profile₁}
    {tuple₂ : TupleCertificateAt profile₂}
    (haligned₁ : SourceRefTupleBridge.PacketTupleAligned packet₁ tuple₁)
    (haligned₂ : SourceRefTupleBridge.PacketTupleAligned packet₂ tuple₂) :
    (∀ atom, tuple₁.traceField atom = tuple₂.traceField atom) ↔
      ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom := by
  rcases haligned₁ with
    ⟨_hsigma₁, _homega₁, _hsupport₁, _hrepair₁, _hnu₁, htrace₁⟩
  rcases haligned₂ with
    ⟨_hsigma₂, _homega₂, _hsupport₂, _hrepair₂, _hnu₂, htrace₂⟩
  constructor
  · intro htuple
    apply projectedTraceField_reflects_sourceRefTable packet₁ packet₂
    intro atom
    calc
      CodebaseTracePacket.projectedTraceField packet₁ atom =
          tuple₁.traceField atom := (htrace₁ atom).symm
      _ = tuple₂.traceField atom := htuple atom
      _ = CodebaseTracePacket.projectedTraceField packet₂ atom := htrace₂ atom
  · intro hsource atom
    calc
      tuple₁.traceField atom =
          CodebaseTracePacket.projectedTraceField packet₁ atom := htrace₁ atom
      _ = CodebaseTracePacket.projectedTraceField packet₂ atom := by
        exact sourceRefTable_preserves_projectedTraceField
          packet₁ packet₂ hsource atom
      _ = tuple₂.traceField atom := (htrace₂ atom).symm

/--
Aligned tuple trace-field equality reflects identity of the supplied
source-ref token table.
-/
theorem aligned_tupleTraceField_reflects_sourceRefTokens
    {profile₁ profile₂ : TupleProfile}
    {packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket}
    {tuple₁ : TupleCertificateAt profile₁}
    {tuple₂ : TupleCertificateAt profile₂}
    (haligned₁ : SourceRefTupleBridge.PacketTupleAligned packet₁ tuple₁)
    (haligned₂ : SourceRefTupleBridge.PacketTupleAligned packet₂ tuple₂)
    (htrace : ∀ atom, tuple₁.traceField atom = tuple₂.traceField atom) :
    ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom :=
  (aligned_tupleTraceField_eq_iff_sourceRefTable
    haligned₁ haligned₂).mp htrace

/--
Cycle-16 theorem package: the finite source-ref to trace-token coordinate is
injective, optional projection equality reflects source-ref token equality,
packet projected trace-field equality reflects source-ref table equality, and
the same reflection holds across two aligned profile tuples.
-/
theorem sourceRefTokenIdentity_reflection_package
    {profile₁ profile₂ : TupleProfile}
    {packet₁ packet₂ : CodebaseTracePacket.SourceRefPacket}
    {tuple₁ : TupleCertificateAt profile₁}
    {tuple₂ : TupleCertificateAt profile₂}
    (haligned₁ : SourceRefTupleBridge.PacketTupleAligned packet₁ tuple₁)
    (haligned₂ : SourceRefTupleBridge.PacketTupleAligned packet₂ tuple₂) :
    Function.Injective CodebaseTracePacket.sourceRefToTraceToken ∧
      (∀ left right : Option CodebaseTracePacket.SourceRefToken,
        Option.map CodebaseTracePacket.sourceRefToTraceToken left =
            Option.map CodebaseTracePacket.sourceRefToTraceToken right ↔
          left = right) ∧
      ((∀ atom,
        CodebaseTracePacket.projectedTraceField packet₁ atom =
          CodebaseTracePacket.projectedTraceField packet₂ atom) ↔
        ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom) ∧
      ((∀ atom, tuple₁.traceField atom = tuple₂.traceField atom) ↔
        ∀ atom, packet₁.sourceRefTable atom = packet₂.sourceRefTable atom) := by
  exact ⟨sourceRefToTraceToken_injective,
    by
      intro left right
      exact sourceRefOptionMap_eq_iff left right,
    projectedTraceField_eq_iff_sourceRefTable packet₁ packet₂,
    aligned_tupleTraceField_eq_iff_sourceRefTable haligned₁ haligned₂⟩

end SourceRefTokenIdentityReflection
end QualitySurface
end Formal.AG.Research
