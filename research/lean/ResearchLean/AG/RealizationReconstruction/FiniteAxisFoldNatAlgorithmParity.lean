import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNatAlgorithmCoset
import Formal.Util.AssertStandardAxioms

/-!
# Unique outer parity of the Nat algorithm image

Cycle 103 expressed the generated Nat subgroup as the union of the
finite-support subgroup and its adjacent left coset.  Here those two branches
are proved disjoint.  The fixed adjacent algorithm moves every natural number,
so it is not finite-support; if a permutation belonged to both branches, group
cancellation would put the adjacent algorithm in the finite-support subgroup.

Consequently every generated source permutation, and every actual intrinsic
member through its source witness, has a unique outer parity.  This proves the
outer part of a normal form.  It does not provide a canonical finite code for
the finite-support component.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization
open MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1200000

/-- The fixed adjacent algorithm is not finite-support because every natural
number is moved. -/
theorem finiteAxisFoldNatAdjacent_not_mem_finiteSupport :
    finiteAxisFoldNatAdjacentSwap ∉
      finiteAxisFoldFiniteSupportPermutationSubgroup Nat := by
  rw [finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff]
  intro finiteSupport
  have moved_eq_univ :
      (fixedBy Nat finiteAxisFoldNatAdjacentSwap)ᶜ = Set.univ := by
    ext atom
    simp only [Set.mem_compl_iff, mem_fixedBy, Set.mem_univ, iff_true]
    exact finiteAxisFoldNatAdjacentSwap_ne atom
  have univFinite : (Set.univ : Set Nat).Finite := by
    rw [← moved_eq_univ]
    exact finiteSupport
  exact Set.infinite_univ univFinite

/-- The finite-support branch and adjacent left-coset branch are disjoint. -/
theorem finiteAxisFoldNatAlgorithmCoset_branches_disjoint
    (permutation : Equiv.Perm Nat) :
    ¬ (permutation ∈ finiteAxisFoldFiniteSupportPermutationSubgroup Nat ∧
      finiteAxisFoldNatAdjacentSwap * permutation ∈
        finiteAxisFoldFiniteSupportPermutationSubgroup Nat) := by
  rintro ⟨finite, adjacentFinite⟩
  apply finiteAxisFoldNatAdjacent_not_mem_finiteSupport
  have productFinite :=
    (finiteAxisFoldFiniteSupportPermutationSubgroup Nat).mul_mem
      adjacentFinite
      ((finiteAxisFoldFiniteSupportPermutationSubgroup Nat).inv_mem finite)
  simpa [mul_assoc] using productFinite

/-- Every generated primitive permutation lies in exactly one displayed
branch.  The conjunction records existence and disjointness without choosing a
semantic representative as new syntax. -/
theorem finiteAxisFoldNatAlgorithmPermutationSubgroup_unique_parity
    (permutation : Equiv.Perm Nat) :
    permutation ∈ finiteAxisFoldNatAlgorithmPermutationSubgroup ↔
      ((permutation ∈ finiteAxisFoldFiniteSupportPermutationSubgroup Nat ∨
        finiteAxisFoldNatAdjacentSwap * permutation ∈
          finiteAxisFoldFiniteSupportPermutationSubgroup Nat) ∧
       ¬ (permutation ∈ finiteAxisFoldFiniteSupportPermutationSubgroup Nat ∧
        finiteAxisFoldNatAdjacentSwap * permutation ∈
          finiteAxisFoldFiniteSupportPermutationSubgroup Nat)) := by
  rw [finiteAxisFoldNatAlgorithmPermutationSubgroup_eq_cosetSubgroup]
  constructor
  · intro membership
    exact ⟨membership,
      finiteAxisFoldNatAlgorithmCoset_branches_disjoint permutation⟩
  · exact fun membership => membership.1

/-- Finite-moved-set formulation of the unique outer parity theorem. -/
theorem finiteAxisFoldNatAlgorithmPermutationSubgroup_unique_parity_finite
    (permutation : Equiv.Perm Nat) :
    permutation ∈ finiteAxisFoldNatAlgorithmPermutationSubgroup ↔
      (((fixedBy Nat permutation)ᶜ.Finite ∨
        (fixedBy Nat
          (finiteAxisFoldNatAdjacentSwap * permutation))ᶜ.Finite) ∧
       ¬ ((fixedBy Nat permutation)ᶜ.Finite ∧
        (fixedBy Nat
          (finiteAxisFoldNatAdjacentSwap * permutation))ᶜ.Finite)) := by
  rw [finiteAxisFoldNatAlgorithmPermutationSubgroup_unique_parity]
  rw [finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff,
    finiteAxisFoldFiniteSupportPermutationSubgroup_mem_iff]

/-- Actual intrinsic membership retains the unique source parity and the same
expected-action equality. -/
theorem finiteAxisFoldNatAlgorithmWordIntrinsicImage_mem_iff_uniqueParity
    (remainder : FiniteAxisFoldResidualLocalFiberKernel) :
    remainder ∈ FiniteAxisFoldNatAlgorithmWordIntrinsicImage ↔
      ∃ permutation : Equiv.Perm Nat,
        ((((fixedBy Nat permutation)ᶜ.Finite ∨
          (fixedBy Nat
            (finiteAxisFoldNatAdjacentSwap * permutation))ᶜ.Finite) ∧
         ¬ ((fixedBy Nat permutation)ᶜ.Finite ∧
          (fixedBy Nat
            (finiteAxisFoldNatAdjacentSwap * permutation))ᶜ.Finite)) ∧
        finiteAxisFoldResidualLocalFiberKernelBackwardProjection remainder =
          finiteAxisFoldArbitraryCarrierBackwardAction Nat permutation) := by
  rw [finiteAxisFoldNatAlgorithmWordIntrinsicImage_mem_iff]
  constructor
  · rintro ⟨permutation, membership, actionEquality⟩
    exact ⟨permutation,
      (finiteAxisFoldNatAlgorithmPermutationSubgroup_unique_parity_finite
        permutation).1 membership,
      actionEquality⟩
  · rintro ⟨permutation, parity, actionEquality⟩
    exact ⟨permutation,
      (finiteAxisFoldNatAlgorithmPermutationSubgroup_unique_parity_finite
        permutation).2 parity,
      actionEquality⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
