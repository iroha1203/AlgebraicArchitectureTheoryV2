import ResearchLean.AG.FiniteDecoderRepresentability.ArrowCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Finite-support classification for Atom permutation codes

This module proves the Atom-permutation sub-obligation of G-121(C).  A semantic
permutation is represented by the existing `AtomPermutationCode` exactly when
its actual moved-point set is finite.  The reverse direction constructs the
finite table with `AtomPermutationCode.ofPerm` and proves exact decoding.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/-- G-121(C) moved-point support of an arbitrary semantic Atom permutation. -/
def atomPermutationSupport (equiv : Equiv.Perm U.Atom) : Set U.Atom :=
  {atom | equiv atom ≠ atom}

/--
G-121(C) necessity: the moved-point support of a decoded finite Atom table is
contained in its authored Finset and is therefore finite.  `DecidableEq` is
inherited from the existing permutation decoder.
-/
theorem atomPermutationSupport_finite_of_code [DecidableEq U.Atom]
    (code : AtomPermutationCode U) :
    (atomPermutationSupport code.toEquiv).Finite := by
  apply code.support.finite_toSet.subset
  intro atom hmove
  by_contra hnot
  exact hmove (code.toEquiv_apply_not_mem atom hnot)

/--
G-121(C) sufficiency: finite actual support constructs an existing finite Atom
table whose decoded permutation is exactly the supplied semantic permutation.
The support Finset is derived from `hfinite`, not supplied as extra data.
-/
noncomputable def atomPermutationCodeOfFiniteSupport [DecidableEq U.Atom]
    (equiv : Equiv.Perm U.Atom)
    (hfinite : (atomPermutationSupport equiv).Finite) :
    AtomPermutationCode U :=
  AtomPermutationCode.ofPerm hfinite.toFinset equiv
    (by
      intro atom
      simp only [Set.Finite.mem_toFinset, atomPermutationSupport, Set.mem_setOf_eq]
      exact not_congr equiv.injective.eq_iff)
    (by
      intro atom hnot
      simp only [Set.Finite.mem_toFinset, atomPermutationSupport,
        Set.mem_setOf_eq, not_not] at hnot
      exact hnot)

/-- The finite-support constructor decodes to the original permutation. -/
@[simp]
theorem atomPermutationCodeOfFiniteSupport_toEquiv [DecidableEq U.Atom]
    (equiv : Equiv.Perm U.Atom)
    (hfinite : (atomPermutationSupport equiv).Finite) :
    (atomPermutationCodeOfFiniteSupport equiv hfinite).toEquiv = equiv := by
  apply AtomPermutationCode.toEquiv_ofPerm

/--
G-121(C) Atom-component classification: an existing finite Atom table decodes
to `equiv` exactly when the actual moved-point support of `equiv` is finite.
-/
theorem exists_atomPermutationCode_toEquiv_iff [DecidableEq U.Atom]
    (equiv : Equiv.Perm U.Atom) :
    (∃ code : AtomPermutationCode U, code.toEquiv = equiv) ↔
      (atomPermutationSupport equiv).Finite := by
  constructor
  · rintro ⟨code, rfl⟩
    exact atomPermutationSupport_finite_of_code code
  · intro hfinite
    exact ⟨atomPermutationCodeOfFiniteSupport equiv hfinite,
      atomPermutationCodeOfFiniteSupport_toEquiv equiv hfinite⟩

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
