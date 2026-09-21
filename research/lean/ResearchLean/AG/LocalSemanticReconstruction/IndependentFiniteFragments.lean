import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.EquivFin
import Formal.Util.AssertStandardAxioms

/-!
# Dependent finite fragments

This module records a query-independent finite-fragment construction for a
dependent table `q ↦ Value q`.  A compatible family is glued from singleton
fragments, and restriction and gluing are inverse.  No finiteness assumption
is placed on the whole query type.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFiniteFragments

noncomputable section

universe u v

variable {Q : Type u} {Value : Q → Type v}

/-- A dependent table assigns a value of the prescribed type to every query. -/
abbrev Table (Q : Type u) (Value : Q → Type v) := (q : Q) → Value q

/-- A fragment assigns correctly typed values on one finite query set. -/
abbrev Fragment (Value : Q → Type v) (D : Finset Q) := (q : D) → Value q.val

/-- A fragment family supplies one dependent fragment for every finite query set. -/
abbrev FragmentFamily (Value : Q → Type v) :=
  (D : Finset Q) → Fragment Value D

/-- Every fragment address type is finite. -/
theorem fragment_finite (D : Finset Q) : Finite D := Finite.of_fintype D

/-- Restrict a dependent table to every finite query set. -/
def fragments (table : Table Q Value) : FragmentFamily Value :=
  fun _ query => table query.val

/-- A family is compatible when restriction along every inclusion preserves values. -/
def Compatible (family : FragmentFamily Value) : Prop :=
  ∀ (D E : Finset Q) (inclusion : D ⊆ E) (query : D),
    family D query = family E ⟨query.val, inclusion query.property⟩

/-- Construct a dependent table from the singleton cells of a fragment family. -/
def glue (family : FragmentFamily Value) : Table Q Value := by
  classical
  exact fun query => family {query} ⟨query, by simp⟩

/-- Restrictions of every dependent table form a compatible family. -/
theorem fragments_compatible (table : Table Q Value) : Compatible (fragments table) :=
  fun _ _ _ _ => rfl

/-- Gluing the restrictions of a dependent table recovers the table. -/
theorem glue_fragments (table : Table Q Value) : glue (fragments table) = table := rfl

/-- A compatible family is recovered from the singleton cells of its glued table. -/
theorem fragments_glue (family : FragmentFamily Value) (compatible : Compatible family) :
    fragments (glue family) = family := by
  classical
  funext D query
  exact compatible {query.val} D
    (Finset.singleton_subset_iff.mpr query.property) ⟨query.val, by simp⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentFiniteFragments

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFiniteFragments
