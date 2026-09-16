import ResearchLean.AG.RealizationReconstruction.FixedFPointedSplitExactSequenceAndTorsor
import Mathlib.Data.Finite.Perm
import Mathlib.SetTheory.Cardinal.Finite
import Formal.Util.AssertStandardAxioms

/-!
# Finite cardinalities of the fixed-graph following-change fibers

When the vertex and hidden carriers are finite, every visible automorphism has
exactly one hidden permutation per generated undirected component.  Hence its
full following-change fiber has cardinality
`(|K|!) ^ |pi₀(F)|`.

For a selected hidden basepoint, the pointed fiber uses the literal point
stabilizer in every component.  We identify this stabilizer with permutations
of the complement of the basepoint and obtain
`((|K| - 1)!) ^ |pi₀(F)|`.

No finiteness of the visible subgroup `H` is assumed: both theorems count one
fixed projection fiber over an arbitrary `u : H`.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFFiberCardinality

open FixedFSplitExactSequenceAndTorsor
open FixedFPointedSplitExactSequenceAndTorsor

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- A point stabilizer is the same finite type as permutations of the
complement of the selected point. -/
def pointedPermutationEquivFixedOutside [DecidableEq K] (basepoint : K) :
    PointedPermutation basepoint ≃
      { permutation : Equiv.Perm K //
        ∀ hidden, ¬ hidden ≠ basepoint → permutation hidden = hidden } where
  toFun permutation :=
    ⟨permutation.1, by
      intro hidden notAway
      have equality : hidden = basepoint := not_ne_iff.mp notAway
      subst hidden
      exact permutation.2⟩
  invFun permutation :=
    ⟨permutation.1, permutation.2 basepoint (by simp)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Remove the fixed basepoint and restrict a pointed permutation to the
remaining hidden values. -/
def pointedPermutationEquivComplement [DecidableEq K] (basepoint : K) :
    PointedPermutation basepoint ≃
      Equiv.Perm { hidden : K // hidden ≠ basepoint } :=
  (pointedPermutationEquivFixedOutside basepoint).trans
    (Equiv.Perm.subtypeEquivSubtypePerm
      (fun hidden : K => hidden ≠ basepoint)).symm

/-- A finite hidden point stabilizer has `( |K| - 1 )!` elements. -/
theorem natCard_pointedPermutation [Finite K] (basepoint : K) :
    Nat.card (PointedPermutation basepoint) =
      Nat.factorial (Nat.card K - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  calc
    Nat.card (PointedPermutation basepoint) =
        Nat.card (Equiv.Perm { hidden : K // hidden ≠ basepoint }) :=
      Nat.card_congr (pointedPermutationEquivComplement basepoint)
    _ = Nat.factorial (Nat.card { hidden : K // hidden ≠ basepoint }) :=
      Nat.card_perm
    _ = Nat.factorial (Nat.card K - 1) := by
      congr 1
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
        Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- The component-indexed full hidden permutation group has one factorial
factor for every generated component. -/
theorem natCard_componentGroup [Finite F.Vertex] [Finite K] :
    Nat.card
        (FixedFRestrictedKernelIdentification.ComponentGroup (F := F) (K := K)) =
      Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) := by
  change Nat.card (FixedFComponent F → Equiv.Perm K) =
    Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F)
  rw [Nat.card_fun, Nat.card_perm]

/-- Every full following-change fiber over a fixed visible automorphism has
the cardinality required by G-123(F1). -/
theorem natCard_projectionFiber
    [Finite F.Vertex] [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    Nat.card (ProjectionFiber (K := K) H automorphism) =
      Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) := by
  calc
    Nat.card (ProjectionFiber (K := K) H automorphism) =
        Nat.card
          (FixedFRestrictedKernelIdentification.ComponentGroup
            (F := F) (K := K)) :=
      Nat.card_congr
        (componentGroupEquivProjectionFiber (K := K) H automorphism).symm
    _ = Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) :=
      natCard_componentGroup

/-- The component-indexed pointed hidden permutation group has one
`(|K|-1)!` factor for every generated component. -/
theorem natCard_pointedComponentGroup
    [Finite F.Vertex] [Finite K] (basepoint : K) :
    Nat.card (PointedComponentGroup F K basepoint) =
      Nat.factorial (Nat.card K - 1) ^ Nat.card (FixedFComponent F) := by
  change Nat.card (FixedFComponent F → PointedPermutation basepoint) =
    Nat.factorial (Nat.card K - 1) ^ Nat.card (FixedFComponent F)
  rw [Nat.card_fun, natCard_pointedPermutation]

/-- Every basepoint-preserving following-change fiber over a fixed visible
automorphism has one point-stabilizer choice per generated component. -/
theorem natCard_pointedProjectionFiber
    [Finite F.Vertex] [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :
    Nat.card (PointedProjectionFiber H basepoint automorphism) =
      Nat.factorial (Nat.card K - 1) ^ Nat.card (FixedFComponent F) := by
  calc
    Nat.card (PointedProjectionFiber H basepoint automorphism) =
        Nat.card (PointedComponentGroup F K basepoint) :=
      Nat.card_congr
        (pointedComponentGroupEquivProjectionFiber
          H basepoint automorphism).symm
    _ = Nat.factorial (Nat.card K - 1) ^ Nat.card (FixedFComponent F) :=
      natCard_pointedComponentGroup basepoint

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFFiberCardinality

end AAT.AG.RealizationReconstruction
