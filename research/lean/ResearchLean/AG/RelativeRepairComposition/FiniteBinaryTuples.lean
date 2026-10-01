import Formal.Util.AssertStandardAxioms
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Sum

/-!
# Finite binary tuples and complete leaf coordinates

## Implementation notes

A finite binary tree records the actual product parentheses. Leaves keep their
individual input types. The flatten/unflatten algorithms are recursive tuple
operations and retain every leaf value, including zero or nontrivial freedoms.
-/
namespace AAT.AG.RelativeRepairComposition
namespace FiniteBinary

/-- Finite binary assembly parentheses, including the empty family and one original leaf at each tip. -/
inductive Tree where
  | empty
  | leaf
  | branch (left right : Tree)
  deriving DecidableEq

/-- Every original leaf is retained in the recursively indexed disjoint union. -/
def Leaves : Tree → Type
  | .empty => Empty
  | .leaf => Unit
  | .branch l r => Leaves l ⊕ Leaves r

/-- The finite leaf list is generated from the binary assembly shape. -/
instance leafFintype : (t : Tree) → Fintype (Leaves t)
  | .empty => inferInstanceAs (Fintype Empty)
  | .leaf => inferInstanceAs (Fintype Unit)
  | .branch l r =>
    letI : Fintype (Leaves l) := leafFintype l
    letI : Fintype (Leaves r) := leafFintype r
    inferInstanceAs (Fintype (Leaves l ⊕ Leaves r))

/-- The recursive original leaf names have decidable equality. -/
instance leafEquality : (t : Tree) → DecidableEq (Leaves t)
  | .empty => inferInstanceAs (DecidableEq Empty)
  | .leaf => inferInstanceAs (DecidableEq Unit)
  | .branch l r =>
    letI : DecidableEq (Leaves l) := leafEquality l
    letI : DecidableEq (Leaves r) := leafEquality r
    inferInstanceAs (DecidableEq (Leaves l ⊕ Leaves r))

universe uA
/-- Nested products retain exactly the original input object at each leaf. -/
def Tuple : (t : Tree) → (Leaves t → Type uA) → Type uA
  | .empty,_ => PUnit
  | .leaf,A => A ()
  | .branch l r,A => Tuple l (fun i => A (.inl i)) × Tuple r (fun j => A (.inr j))

/-- Flatten or reconstruct every leaf using only recursive projections and product assembly. -/
def tupleEquiv : (t : Tree) → (A : Leaves t → Type uA) → Tuple t A ≃ (∀ i, A i)
  | .empty,_ => {
      toFun := fun _ i => i.elim
      invFun := fun _ => PUnit.unit
      left_inv := fun a => by cases a; rfl
      right_inv := fun a => by funext i; cases i }
  | .leaf,A => {
      toFun := fun a i => by cases i; exact a
      invFun := fun a => a ()
      left_inv := fun _ => rfl
      right_inv := fun a => by funext i; cases i; rfl }
  | .branch l r,A => {
      toFun := fun a i => match i with
        | .inl i => tupleEquiv l _ a.1 i
        | .inr j => tupleEquiv r _ a.2 j
      invFun := fun a => ((tupleEquiv l _).symm (fun i => a (.inl i)),
        (tupleEquiv r _).symm (fun j => a (.inr j)))
      left_inv := fun a => Prod.ext ((tupleEquiv l _).symm_apply_apply a.1)
        ((tupleEquiv r _).symm_apply_apply a.2)
      right_inv := fun a => by
        funext i
        cases i with
        | inl i => exact congrFun ((tupleEquiv l _).apply_symm_apply (fun j => a (.inl j))) i
        | inr i => exact congrFun ((tupleEquiv r _).apply_symm_apply (fun j => a (.inr j))) i }

/-- Every finite bracket change preserves all original leaf values in both directions. -/
theorem tuple_restore (t : Tree) (A : Leaves t → Type uA) (a : Tuple t A) :
    (tupleEquiv t A).symm (tupleEquiv t A a) = a :=
  (tupleEquiv t A).symm_apply_apply a

/-- Reconstructing and flattening returns every complete original leaf family. -/
theorem tuple_read (t : Tree) (A : Leaves t → Type uA) (a : ∀ i, A i) :
    tupleEquiv t A ((tupleEquiv t A).symm a) = a :=
  (tupleEquiv t A).apply_symm_apply a

/-- A binary step retains every original left child object. -/
theorem tuple_left (l r : Tree) (A : Leaves (.branch l r) → Type uA)
    (a : Tuple (.branch l r) A) (i : Leaves l) :
    tupleEquiv (.branch l r) A a (.inl i) = tupleEquiv l (fun i => A (.inl i)) a.1 i := rfl

/-- A binary step retains every original right child object. -/
theorem tuple_right (l r : Tree) (A : Leaves (.branch l r) → Type uA)
    (a : Tuple (.branch l r) A) (i : Leaves r) :
    tupleEquiv (.branch l r) A a (.inr i) = tupleEquiv r (fun i => A (.inr i)) a.2 i := rfl

end FiniteBinary
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
