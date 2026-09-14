import ResearchLean.AG.RealizationReconstruction.KaroubiArrowReconstruction
import ResearchLean.AG.RealizationReconstruction.LensFinitePresentation
import ResearchLean.AG.RealizationReconstruction.ProtocolFinitePresentation
import ResearchLean.AG.RealizationReconstruction.ProtocolIdempotents

/-!
# Karoubi reconstruction for the two independent CS models

This module applies the common G-123(B1) reconstruction theorem to both CS
models constructed in the preceding modules.  Each application passes four
named proofs produced from the fixed model input: decoder fullness, decoder
faithfulness, semantic idempotent completeness by fixed points, and explicit
retract generation by finite enumeration.  It does not use either model's
already available direct equivalence as a shortcut.

The accompanying arrow equivalences retain arbitrary natural transformations,
including non-invertible lens and protocol changes.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open CategoryTheory.Idempotents

universe u

namespace LensRealization

variable {V : Type u} {v₀ : V}

/-- G-123(B), property 4 premise discharge for lenses, constructed by the finite-fiber
normal form rather than assumed as an application certificate. -/
theorem lensRetractGeneratedBy :
    RetractGeneratedBy (lensDecoder V v₀) :=
  exists_decoder_retract

/-- G-123(B1,E) for lenses.  All four hypotheses are the named constructions
from the fixed n1015 lens input, and the direct presentation equivalence is not
used in this definition. -/
noncomputable def lensKaroubiReconstructionEquivalence :
    Karoubi LensPresentation ≌ LensRealization V v₀ :=
  karoubiReconstructionEquivalence (lensDecoder V v₀)
    lensDecoder_full lensDecoder_faithful
    lensRealization_isIdempotentComplete lensRetractGeneratedBy

/-- The reconstructed lens functor restricts to the original finite decoder. -/
noncomputable def lensKaroubiReconstructionRestrictionIso :
    toKaroubi LensPresentation ⋙ lensKaroubiReconstructionEquivalence.functor ≅
      lensDecoder V v₀ :=
  karoubiReconstructionRestrictionIso (lensDecoder V v₀)
    lensDecoder_full lensDecoder_faithful
    lensRealization_isIdempotentComplete lensRetractGeneratedBy

/-- Arrow-level lens reconstruction preserves arbitrary, possibly
non-invertible, get/put-preserving state changes. -/
noncomputable def lensKaroubiArrowReconstructionEquivalence :
    Karoubi (Arrow LensPresentation) ≌ Arrow (LensRealization V v₀) :=
  karoubiArrowReconstructionEquivalence (lensDecoder V v₀)
    lensDecoder_full lensDecoder_faithful
    lensRealization_isIdempotentComplete lensRetractGeneratedBy

end LensRealization

namespace ProtocolPresentation

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}

/-- G-123(B), property 4 premise discharge for protocols, constructed vertexwise from the
finite-carrier enumeration and its explicit normal-form isomorphism. -/
theorem protocolRetractGeneratedBy :
    RetractGeneratedBy (decoder S O) :=
  exists_decoder_retract

/-- G-123(B1,E) for protocols.  The four hypotheses are discharged by the
independent schema semantics, generator reconstruction, finite enumeration,
and fixed-point splitting developed for this same `S,O`. -/
noncomputable def protocolKaroubiReconstructionEquivalence :
    Karoubi (ProtocolPresentation S O) ≌ ProtocolRealization S O :=
  karoubiReconstructionEquivalence (decoder S O)
    decoder_full decoder_faithful
    ProtocolRealization.protocolRealization_isIdempotentComplete
    protocolRetractGeneratedBy

/-- The reconstructed protocol functor restricts to the finite decoder that
executes the fixed named operations and quotient relations. -/
noncomputable def protocolKaroubiReconstructionRestrictionIso :
    toKaroubi (ProtocolPresentation S O) ⋙
        protocolKaroubiReconstructionEquivalence.functor ≅ decoder S O :=
  karoubiReconstructionRestrictionIso (decoder S O)
    decoder_full decoder_faithful
    ProtocolRealization.protocolRealization_isIdempotentComplete
    protocolRetractGeneratedBy

/-- Arrow-level protocol reconstruction preserves all observation-compatible
natural transformations, including non-invertible adapters. -/
noncomputable def protocolKaroubiArrowReconstructionEquivalence :
    Karoubi (Arrow (ProtocolPresentation S O)) ≌
      Arrow (ProtocolRealization S O) :=
  karoubiArrowReconstructionEquivalence (decoder S O)
    decoder_full decoder_faithful
    ProtocolRealization.protocolRealization_isIdempotentComplete
    protocolRetractGeneratedBy

end ProtocolPresentation

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
