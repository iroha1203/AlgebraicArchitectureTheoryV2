import ResearchLean.AG.RealizationReconstruction.FixedFFiniteExamples
import ResearchLean.AG.RealizationReconstruction.LensSemantics
import Mathlib.Data.Finite.Perm
import Formal.Util.AssertStandardAxioms

/-!
# Product-lens changes and the fixed-graph classification

The lens-side condition in n1015 (L5) is defined here directly from the
independent `LensRealization` operations: the same state equivalence and the
same visible equivalence must commute with both `get` and `put`.  For the
product realization, this condition is proved equivalent in both directions
to the actual named-operation preservation condition of the fixed complete
update graph.

The resulting normal form constructs the unique hidden permutation in (L6).
Neither the completed state map nor its hidden permutation is accepted as a
presentation certificate.
-/

namespace AAT.AG.RealizationReconstruction

universe u

namespace FixedFLensConnection

open FixedFFiniteExamples

/-- The independent CS-side invertible change condition of n1015 (L5).
The equations use one common `h` and one common `u` for both semantic
operations. -/
@[ext]
structure LensInvertibleChange {V : Type u} {reference : V}
    (L M : LensRealization V reference) (visible : Equiv.Perm V) where
  h : L.Carrier ≃ M.Carrier
  get_naturality : ∀ state,
    M.get (h state) = visible (L.get state)
  put_naturality : ∀ state requested,
    h (L.put state requested) =
      M.put (h state) (visible requested)

namespace LensInvertibleChange

variable {V K : Type u} {reference : V} [Finite K]
  {visible : Equiv.Perm V}

/-- Forgetting the lens vocabulary produces the actual following change over
the complete update graph.  Get preservation supplies exactly the observation
law. -/
def toFollowingStateChange
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible) :
    FixedFFollowingStateChange (completeUpdateGraph V) K
      (completeUpdateAutomorphism visible) where
  h := change.h
  observation vertex hidden := change.get_naturality (vertex, hidden)

/-- The lens `put` square is exactly the actual named-operation execution
square for every complete-update edge. -/
theorem toFollowingStateChange_preserves
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible) :
    change.toFollowingStateChange.PreservesNamedOperations := by
  intro namedEdge hidden
  rcases namedEdge with ⟨source, target⟩
  exact change.put_naturality (source, hidden) target

/-- Conversely, an actual following change on the complete update graph is a
CS-side lens change precisely when its named operations are preserved. -/
def ofFollowingStateChange
    (change :
      { actual : FixedFFollowingStateChange (completeUpdateGraph V) K
          (completeUpdateAutomorphism visible) //
        actual.PreservesNamedOperations }) :
    LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible where
  h := change.1.h
  get_naturality state := by
    rcases state with ⟨vertex, hidden⟩
    exact change.1.observation vertex hidden
  put_naturality state requested := by
    rcases state with ⟨source, hidden⟩
    exact change.2 (source, requested) hidden

/-- Bidirectional identification of independent lens (L5) changes with the
actual operation-preserving fixed-graph changes. -/
def equivPreservingFollowingChanges :
    LensInvertibleChange
        (LensRealization.product V K reference)
        (LensRealization.product V K reference) visible ≃
      { actual : FixedFFollowingStateChange (completeUpdateGraph V) K
          (completeUpdateAutomorphism visible) //
        actual.PreservesNamedOperations } where
  toFun change := ⟨change.toFollowingStateChange,
    change.toFollowingStateChange_preserves⟩
  invFun := ofFollowingStateChange
  left_inv change := by
    apply LensInvertibleChange.ext
    rfl
  right_inv change := by
    apply Subtype.ext
    apply FixedFFollowingStateChange.ext
    rfl

/-- The hidden permutation is constructed by evaluating the actual state
change in the reference visible fiber. -/
def hiddenPermutation
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible) :
    Equiv.Perm K :=
  change.toFollowingStateChange.fiberPerm reference

/-- The constructed fiber permutation is independent of the visible state,
because every ordered pair is a named update operation. -/
theorem fiberPerm_eq_hiddenPermutation
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (vertex : V) :
    change.toFollowingStateChange.fiberPerm vertex =
      change.hiddenPermutation := by
  have edgeConstancy :=
    (FixedFFollowingStateChange.preservesNamedOperations_iff
      change.toFollowingStateChange).1
      change.toFollowingStateChange_preserves
      (reference, vertex)
  exact edgeConstancy.symm

/-- Constructive (L6): every product-lens (L5) change has one global hidden
permutation, and the original complete state equivalence is recovered from it
at every state. -/
theorem normalForm
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (vertex : V) (hidden : K) :
    change.h (vertex, hidden) =
      (visible vertex, change.hiddenPermutation hidden) := by
  calc
    change.h (vertex, hidden) =
        (visible vertex,
          change.toFollowingStateChange.fiberPerm vertex hidden) :=
      change.toFollowingStateChange.factorization vertex hidden
    _ = (visible vertex, change.hiddenPermutation hidden) := by
      rw [change.fiberPerm_eq_hiddenPermutation vertex]

/-- The hidden permutation in (L6) is unique; it is not an additional input
or a quotient of completed state maps. -/
theorem hiddenPermutation_unique
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (permutation : Equiv.Perm K)
    (factorization : ∀ vertex hidden,
      change.h (vertex, hidden) =
        (visible vertex, permutation hidden)) :
    permutation = change.hiddenPermutation := by
  apply Equiv.ext
  intro hidden
  exact (congrArg Prod.snd
    (factorization reference hidden)).symm

/-- Build the complete CS-side lens change from a visible permutation and a
finite-complement permutation, as prescribed by (L6). -/
def ofHiddenPermutation (permutation : Equiv.Perm K) :
    LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible where
  h := Equiv.prodCongr visible permutation
  get_naturality _ := rfl
  put_naturality _ _ := rfl

/-- Product-lens (L5) changes over any fixed visible permutation are exactly
the full hidden permutation group. -/
def equivHiddenPermutations :
    LensInvertibleChange
        (LensRealization.product V K reference)
        (LensRealization.product V K reference) visible ≃
      Equiv.Perm K where
  toFun := hiddenPermutation
  invFun := ofHiddenPermutation
  left_inv change := by
    apply LensInvertibleChange.ext
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (change.normalForm vertex hidden).symm
  right_inv permutation := by
    apply Equiv.ext
    intro hidden
    rfl

/-- The independent lens-side fiber count agrees with the fixed-F
classification for every visible permutation. -/
theorem natCard_productLensChanges :
    Nat.card
        (LensInvertibleChange
          (LensRealization.product V K reference)
          (LensRealization.product V K reference) visible) =
      Nat.factorial (Nat.card K) := by
  calc
    Nat.card
        (LensInvertibleChange
          (LensRealization.product V K reference)
          (LensRealization.product V K reference) visible) =
        Nat.card (Equiv.Perm K) :=
      Nat.card_congr equivHiddenPermutations
    _ = Nat.factorial (Nat.card K) := Nat.card_perm

/-- The selected section of a product lens. -/
def productSection (basepoint : K) (vertex : V) :
    (LensRealization.product V K reference).Carrier :=
  (vertex, basepoint)

/-- The section-preservation equation is exactly the point-stabilizer
condition on every fixed-F hidden fiber. -/
theorem preservesSection_iff
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (basepoint : K) :
    (∀ vertex,
      change.h (productSection basepoint vertex) =
        productSection basepoint (visible vertex)) ↔
      ∀ vertex,
        change.toFollowingStateChange.fiberPerm vertex basepoint =
          basepoint := by
  constructor
  · intro preserves vertex
    change (change.h (vertex, basepoint)).2 = basepoint
    exact congrArg Prod.snd (preserves vertex)
  · intro fixes vertex
    calc
      change.h (productSection basepoint vertex) =
          (visible vertex,
            change.toFollowingStateChange.fiberPerm vertex basepoint) :=
        change.toFollowingStateChange.factorization vertex basepoint
      _ = productSection basepoint (visible vertex) := by
        rw [fixes vertex]
        rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end LensInvertibleChange

end FixedFLensConnection

end AAT.AG.RealizationReconstruction
