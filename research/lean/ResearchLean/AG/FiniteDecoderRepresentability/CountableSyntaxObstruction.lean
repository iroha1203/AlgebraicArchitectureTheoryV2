import ResearchLean.AG.FiniteDecoderRepresentability.NatSubsetSwaps
import Mathlib.Data.Countable.Basic
import Mathlib.Logic.Equiv.List
import Mathlib.Logic.Function.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Countable syntax cannot enumerate the fixed semantic automorphisms

The subset-indexed family from G-121(E) embeds `Set Nat` into the
automorphisms of the fixed all-true semantic object.  Cantor's diagonal
argument therefore makes that automorphism type uncountable.  Consequently
no decoder from a countable type is surjective.

The last part records two exact syntax specializations from the target: finite
lists over a countable alphabet, and the sum of countably many presentation
object names with countable morphism syntax for every ordered pair.  Only
countability is assumed; no computability data is requested.

## Implementation notes

`CountablePresentationSyntax` bundles the object and typed-morphism families
with their countability proofs so one value fixes the complete syntax boundary
used by the decoder corollary.  Passing all four ingredients separately would
prove the same cardinal fact but would not package the target's combined
presentation-syntax regime as a reusable input.

`CombinedSyntax` is an object-code sum with a nested dependent sum over source
and target.  A plain nondependent union of morphism expressions was rejected
because it would erase their endpoint types; using only the nested sigma was
also rejected because the target explicitly combines presentation-object names
with morphism syntax.  The bundle carries propositions of countability, not
chosen encoders, so it adds no computability assumption.
-/

namespace AAT.AG.FiniteDecoderRepresentability

open CategoryTheory AtomFoundation DoctrineFiberProduct

/-- The type of subsets of `Nat` is uncountable, directly by Cantor's theorem. -/
theorem setNat_uncountable : Uncountable (Set Nat) := by
  rw [uncountable_iff_not_countable]
  intro hcountable
  letI : Countable (Set Nat) := hcountable
  obtain ⟨encode, hencode⟩ := exists_injective_nat (Set Nat)
  exact Function.cantor_injective encode hencode

/-- G-121(E): the fixed semantic object has uncountably many automorphisms. -/
theorem natSemanticAut_uncountable :
    Uncountable (natSwapCode.toSemantic ≅ natSwapCode.toSemantic) := by
  letI : Uncountable (Set Nat) := setNat_uncountable
  exact natSubsetSemanticAut_injective.uncountable

/-- G-121(E): a decoder from any countable syntax type misses an automorphism. -/
theorem countableDecoder_not_surjective {T : Type*} [Countable T]
    (decode : T → (natSwapCode.toSemantic ≅ natSwapCode.toSemantic)) :
    ¬ Function.Surjective decode := by
  letI : Uncountable (natSwapCode.toSemantic ≅ natSwapCode.toSemantic) :=
    natSemanticAut_uncountable
  exact not_surjective_countable_uncountable decode

/-- Finite strings over a countable alphabet cannot enumerate all automorphisms. -/
theorem finiteListDecoder_not_surjective {Alphabet : Type*} [Countable Alphabet]
    (decode : List Alphabet → (natSwapCode.toSemantic ≅ natSwapCode.toSemantic)) :
    ¬ Function.Surjective decode :=
  countableDecoder_not_surjective decode

/--
Countable presentation syntax: countably many object names and a countable
type of morphism expressions for every ordered pair of object names.
-/
structure CountablePresentationSyntax where
  ObjectCode : Type*
  HomSyntax : ObjectCode → ObjectCode → Type*
  objectCode_countable : Countable ObjectCode
  homSyntax_countable : ∀ source target, Countable (HomSyntax source target)

namespace CountablePresentationSyntax

/-- The combined syntax contains both object names and typed morphism expressions. -/
abbrev CombinedSyntax (presentation : CountablePresentationSyntax) :=
  presentation.ObjectCode ⊕
    Σ source, Σ target, presentation.HomSyntax source target

/-- The combined object-and-morphism syntax is countable. -/
theorem combinedSyntax_countable (presentation : CountablePresentationSyntax) :
    Countable presentation.CombinedSyntax := by
  letI : Countable presentation.ObjectCode := presentation.objectCode_countable
  letI (source target : presentation.ObjectCode) :
      Countable (presentation.HomSyntax source target) :=
    presentation.homSyntax_countable source target
  infer_instance

/--
G-121(E)'s presentation-syntax specialization: no interpretation of the
combined countable syntax can enumerate every automorphism of `X_*`.
-/
theorem combinedSyntaxDecoder_not_surjective (presentation : CountablePresentationSyntax)
    (decode : presentation.CombinedSyntax →
      (natSwapCode.toSemantic ≅ natSwapCode.toSemantic)) :
    ¬ Function.Surjective decode := by
  letI : Countable presentation.CombinedSyntax := presentation.combinedSyntax_countable
  exact countableDecoder_not_surjective decode

end CountablePresentationSyntax

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
