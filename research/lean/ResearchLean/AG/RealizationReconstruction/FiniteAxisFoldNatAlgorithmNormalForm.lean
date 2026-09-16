import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNatAlgorithmParity
import Mathlib.GroupTheory.Perm.Support
import Formal.Util.AssertStandardAxioms

/-!
# Faithful Nat normal forms for the finite-support/adjacent image

Cycle 104 proved unique outer parity but left the finite-support component as
a semantic condition.  Here that component is represented by an exact finite
support and explicit finite forward/backward lookup tables.  Every table entry
must move, so fixed-point padding is impossible.  Extending the table by the
identity is therefore injective and covers exactly the finite-support Nat
permutations.

Combining this canonical finite component with the Cycle 104 parity gives a
faithful source-owned normal form for the Cycle 102 generated Nat subgroup.
No completed permutation of `Nat` or actual residual-kernel element is stored
in the syntax.  Uniform primitive parameters and full residual-kernel coverage
remain separate obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- Independent finite data for a Nat permutation.  The finite lookup table is
fixed-point-free, making `support` the exact moved set rather than a padded
ambient bound. -/
structure FiniteAxisFoldNatFiniteSupportCode where
  support : Finset Nat
  table : FiniteAxisFoldExtensionPermutationCode support
  table_moves : ∀ atom, table.forward atom ≠ atom

namespace FiniteAxisFoldNatFiniteSupportCode

/-- Extend the explicit finite table by the identity on the rest of `Nat`. -/
def evaluate (code : FiniteAxisFoldNatFiniteSupportCode) : Equiv.Perm Nat :=
  Equiv.Perm.ofSubtype code.table.toPerm

/-- The authored finite set is exactly the moved set of the evaluation. -/
theorem evaluate_ne_iff_mem (code : FiniteAxisFoldNatFiniteSupportCode)
    (atom : Nat) :
    code.evaluate atom ≠ atom ↔ atom ∈ code.support := by
  constructor
  · intro moved
    by_contra outside
    exact moved
      (Equiv.Perm.ofSubtype_apply_of_not_mem code.table.toPerm outside)
  · intro inside fixed
    apply code.table_moves ⟨atom, inside⟩
    apply Subtype.ext
    change (↑(code.table.toPerm ⟨atom, inside⟩) : Nat) = atom
    rw [← Equiv.Perm.ofSubtype_apply_of_mem code.table.toPerm inside]
    exact fixed

/-- Evaluation has finite support, derived from the finite code rather than
received as a syntax field. -/
theorem evaluate_finite (code : FiniteAxisFoldNatFiniteSupportCode) :
    (fixedBy Nat code.evaluate)ᶜ.Finite := by
  have moved_eq : (fixedBy Nat code.evaluate)ᶜ =
      (code.support : Set Nat) := by
    ext atom
    simp only [Set.mem_compl_iff, mem_fixedBy, Finset.mem_coe]
    exact code.evaluate_ne_iff_mem atom
  rw [moved_eq]
  exact code.support.finite_toSet

/-- Evaluation lands in the independently characterized finite-support
subgroup. -/
def decode (code : FiniteAxisFoldNatFiniteSupportCode) :
    finiteAxisFoldFiniteSupportPermutationSubgroup Nat :=
  ⟨code.evaluate,
    (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2
      code.evaluate_finite⟩

/-- Equality of evaluated permutations recovers the entire exact-support
finite code. -/
theorem evaluate_injective : Function.Injective evaluate := by
  intro first second equality
  have supportEquality : first.support = second.support := by
    ext atom
    rw [← first.evaluate_ne_iff_mem, ← second.evaluate_ne_iff_mem, equality]
  cases first with
  | mk firstSupport firstTable firstMoves =>
      cases second with
      | mk secondSupport secondTable secondMoves =>
          dsimp only at supportEquality
          subst secondSupport
          congr
          apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
          apply Equiv.Perm.ofSubtype_injective
          exact equality

/-- Membership in the moved set is invariant under a permutation. -/
private theorem moved_invariant (permutation : Equiv.Perm Nat) (atom : Nat) :
    permutation (permutation atom) ≠ permutation atom ↔
      permutation atom ≠ atom := by
  rw [permutation.injective.ne_iff]

/-- The exact finite moved set of a member of the finite-support subgroup. -/
private noncomputable def exactSupport
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup Nat) :
    Finset Nat :=
  ((finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff permutation.1).1
    permutation.2).toFinset

private theorem mem_exactSupport_iff
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)
    (atom : Nat) :
    atom ∈ exactSupport permutation ↔ permutation.1 atom ≠ atom := by
  rw [exactSupport, Set.Finite.mem_toFinset]
  simp [fixedBy]

private theorem exactSupport_invariant
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup Nat)
    (atom : Nat) :
    permutation.1 atom ∈ exactSupport permutation ↔
      atom ∈ exactSupport permutation := by
  rw [mem_exactSupport_iff, mem_exactSupport_iff]
  exact moved_invariant permutation.1 atom

/-- Extract the exact finite moved set and its finite forward/backward table.
The finiteness proof enumerates an already defined source moved set; it is not
stored in the resulting syntax. -/
noncomputable def encode
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup Nat) :
    FiniteAxisFoldNatFiniteSupportCode :=
    { support := exactSupport permutation
      table := FiniteAxisFoldExtensionPermutationCode.ofPerm
        (permutation.1.subtypePerm (exactSupport_invariant permutation))
      table_moves := fun atom fixed => by
        have movedAtom : permutation.1 atom.1 ≠ atom.1 := by
          exact (mem_exactSupport_iff permutation atom.1).1 atom.2
        apply movedAtom
        exact congrArg Subtype.val fixed }

/-- Decoding the extracted finite table returns the original permutation. -/
theorem decode_encode
    (permutation : finiteAxisFoldFiniteSupportPermutationSubgroup Nat) :
    (encode permutation).decode = permutation := by
  apply Subtype.ext
  apply Equiv.Perm.ofSubtype_subtypePerm
    (exactSupport_invariant permutation)
  intro atom moved
  exact (mem_exactSupport_iff permutation atom).2 moved

/-- Exact-support extraction is a left inverse: there is no support-padding
ambiguity in the finite syntax. -/
theorem encode_decode (code : FiniteAxisFoldNatFiniteSupportCode) :
    encode code.decode = code := by
  apply evaluate_injective
  change (encode code.decode).decode.1 = code.decode.1
  exact congrArg Subtype.val (decode_encode code.decode)

/-- Canonical equivalence between exact finite source data and the semantic
finite-support subgroup. -/
noncomputable def equivFiniteSupport :
    FiniteAxisFoldNatFiniteSupportCode ≃
      finiteAxisFoldFiniteSupportPermutationSubgroup Nat where
  toFun := decode
  invFun := encode
  left_inv := encode_decode
  right_inv := decode_encode

end FiniteAxisFoldNatFiniteSupportCode

/-- Faithful outer-parity normal form.  `false` is the finite-support branch;
`true` is its left translate by the fixed adjacent algorithm. -/
structure FiniteAxisFoldNatAlgorithmNormalForm where
  adjacent : Bool
  finite : FiniteAxisFoldNatFiniteSupportCode

namespace FiniteAxisFoldNatAlgorithmNormalForm

/-- Evaluate the independent normal form on the primitive Nat carrier. -/
def evaluate (normal : FiniteAxisFoldNatAlgorithmNormalForm) : Equiv.Perm Nat :=
  if normal.adjacent then
    finiteAxisFoldNatAdjacentSwap * normal.finite.evaluate
  else
    normal.finite.evaluate

/-- Every normal-form evaluation belongs to the Cycle 102 generated source
subgroup. -/
theorem evaluate_mem (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    normal.evaluate ∈ finiteAxisFoldNatAlgorithmPermutationSubgroup := by
  rw [finiteAxisFoldNatAlgorithmPermutationSubgroup_mem_iff_coset]
  cases adjacent : normal.adjacent with
  | false =>
      left
      simpa [evaluate, adjacent] using normal.finite.evaluate_finite
  | true =>
      right
      simpa [evaluate, adjacent, ← mul_assoc] using
        normal.finite.evaluate_finite

/-- The outer parity and the exact finite table are both recovered from the
evaluated source permutation. -/
theorem evaluate_injective : Function.Injective evaluate := by
  intro first second equality
  cases first with
  | mk firstAdjacent firstFinite =>
      cases second with
      | mk secondAdjacent secondFinite =>
          cases firstAdjacent <;> cases secondAdjacent
          · congr
            apply FiniteAxisFoldNatFiniteSupportCode.evaluate_injective
            simpa [evaluate] using equality
          · exfalso
            apply finiteAxisFoldNatAlgorithmCoset_branches_disjoint
              firstFinite.evaluate
            constructor
            · exact firstFinite.decode.2
            · have evaluatedEquality :
                  firstFinite.evaluate =
                    finiteAxisFoldNatAdjacentSwap * secondFinite.evaluate := by
                simpa [evaluate] using equality
              have reduced :
                  finiteAxisFoldNatAdjacentSwap * firstFinite.evaluate =
                    secondFinite.evaluate := by
                rw [evaluatedEquality, ← mul_assoc,
                  finiteAxisFoldNatAdjacent_mul_self, one_mul]
              rw [reduced]
              exact secondFinite.decode.2
          · exfalso
            apply finiteAxisFoldNatAlgorithmCoset_branches_disjoint
              secondFinite.evaluate
            constructor
            · exact secondFinite.decode.2
            · have evaluatedEquality :
                  finiteAxisFoldNatAdjacentSwap * firstFinite.evaluate =
                    secondFinite.evaluate := by
                simpa [evaluate] using equality
              rw [← evaluatedEquality, ← mul_assoc,
                finiteAxisFoldNatAdjacent_mul_self, one_mul]
              exact firstFinite.decode.2
          · congr
            apply FiniteAxisFoldNatFiniteSupportCode.evaluate_injective
            have evaluatedEquality :
                finiteAxisFoldNatAdjacentSwap * firstFinite.evaluate =
                  finiteAxisFoldNatAdjacentSwap * secondFinite.evaluate := by
              simpa [evaluate] using equality
            have cancelled := congrArg
              (fun permutation : Equiv.Perm Nat =>
                finiteAxisFoldNatAdjacentSwap⁻¹ * permutation)
              evaluatedEquality
            simpa [mul_assoc] using cancelled

/-- Every generated Nat source permutation has an independent faithful normal
form. -/
theorem evaluate_surjective
    (permutation : finiteAxisFoldNatAlgorithmPermutationSubgroup) :
    ∃ normal : FiniteAxisFoldNatAlgorithmNormalForm,
      normal.evaluate = permutation.1 := by
  have classified :=
    (finiteAxisFoldNatAlgorithmPermutationSubgroup_mem_iff_coset
      permutation.1).1 permutation.2
  rcases classified with finite | adjacentFinite
  · let finitePermutation :
        finiteAxisFoldFiniteSupportPermutationSubgroup Nat :=
      ⟨permutation.1,
        (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2 finite⟩
    refine ⟨⟨false,
      FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation⟩, ?_⟩
    have decoded := congrArg Subtype.val
      (FiniteAxisFoldNatFiniteSupportCode.decode_encode finitePermutation)
    change (FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation).evaluate =
      permutation.1 at decoded
    simpa [evaluate] using decoded
  · let finitePermutation :
        finiteAxisFoldFiniteSupportPermutationSubgroup Nat :=
      ⟨finiteAxisFoldNatAdjacentSwap * permutation.1,
        (finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff _).2
          adjacentFinite⟩
    refine ⟨⟨true,
      FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation⟩, ?_⟩
    have decoded := congrArg Subtype.val
      (FiniteAxisFoldNatFiniteSupportCode.decode_encode finitePermutation)
    change (FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation).evaluate =
      finiteAxisFoldNatAdjacentSwap * permutation.1 at decoded
    change finiteAxisFoldNatAdjacentSwap *
        (FiniteAxisFoldNatFiniteSupportCode.encode finitePermutation).evaluate =
      permutation.1
    rw [decoded, ← mul_assoc,
      finiteAxisFoldNatAdjacent_mul_self, one_mul]

/-- Explicit equivalence with the generated source subgroup.  It is obtained
from the independently defined finite syntax and proved evaluation
bijectivity, not by quotienting syntax by decoder equality. -/
noncomputable def equivPermutationSubgroup :
    FiniteAxisFoldNatAlgorithmNormalForm ≃
      finiteAxisFoldNatAlgorithmPermutationSubgroup :=
  Equiv.ofBijective
    (fun normal => ⟨normal.evaluate, normal.evaluate_mem⟩)
    ⟨fun first second equality => evaluate_injective
        (congrArg Subtype.val equality),
      fun permutation => by
        obtain ⟨normal, equality⟩ := evaluate_surjective permutation
        exact ⟨normal, Subtype.ext equality⟩⟩

/-- Evaluate the faithful source normal form through the same fixed actual
local-fiber-kernel section used by the algorithm-word decoder. -/
noncomputable def actualEvaluate
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    FiniteAxisFoldResidualLocalFiberKernel :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom Nat
    normal.evaluate

/-- The actual projection of a normal form is the independently defined
expected backward action of its source evaluation. -/
theorem actualEvaluate_backwardProjection
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection
        normal.actualEvaluate =
      finiteAxisFoldArbitraryCarrierBackwardAction Nat normal.evaluate :=
  finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom_backwardProjection
    normal.evaluate

/-- The faithful normal-form evaluator lands in the decoder-independent
actual intrinsic image. -/
noncomputable def intrinsicDecode
    (normal : FiniteAxisFoldNatAlgorithmNormalForm) :
    FiniteAxisFoldNatAlgorithmWordIntrinsicImage :=
  ⟨normal.actualEvaluate, by
    rw [finiteAxisFoldNatAlgorithmWordIntrinsicImage_mem_iff]
    exact ⟨normal.evaluate, normal.evaluate_mem,
      normal.actualEvaluate_backwardProjection⟩⟩

/-- Actual decoding remains faithful: equality in the displayed residual
kernel reads back through the complete backward action to source normal-form
equality. -/
theorem intrinsicDecode_injective : Function.Injective intrinsicDecode := by
  intro first second equality
  apply evaluate_injective
  apply finiteAxisFoldNatArbitraryCarrierBackwardAction_injective
  rw [← first.actualEvaluate_backwardProjection,
    ← second.actualEvaluate_backwardProjection]
  exact congrArg finiteAxisFoldResidualLocalFiberKernelBackwardProjection
    (congrArg Subtype.val equality)

/-- Every actual intrinsic member has a faithful exact-support/parity normal
form, not merely a redundant algorithm word. -/
theorem intrinsicDecode_surjective : Function.Surjective intrinsicDecode := by
  intro remainder
  obtain ⟨permutation, membership, actionEquality⟩ :=
    (finiteAxisFoldNatAlgorithmWordIntrinsicImage_mem_iff remainder.1).mp
      remainder.2
  let source : finiteAxisFoldNatAlgorithmPermutationSubgroup :=
    ⟨permutation, membership⟩
  obtain ⟨normal, evaluationEquality⟩ := evaluate_surjective source
  refine ⟨normal, ?_⟩
  apply Subtype.ext
  apply finiteAxisFoldResidualLocalFiberKernelBackwardProjection_injective
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      normal.actualEvaluate =
    finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder.1
  rw [actualEvaluate_backwardProjection, evaluationEquality]
  exact actionEquality.symm

/-- Exact recovery equivalence on the actual intrinsic image. -/
noncomputable def equivIntrinsicImage :
    FiniteAxisFoldNatAlgorithmNormalForm ≃
      FiniteAxisFoldNatAlgorithmWordIntrinsicImage :=
  Equiv.ofBijective intrinsicDecode
    ⟨intrinsicDecode_injective, intrinsicDecode_surjective⟩

end FiniteAxisFoldNatAlgorithmNormalForm

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
