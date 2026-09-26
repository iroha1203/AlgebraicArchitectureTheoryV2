import Mathlib.Data.Finset.Defs
import Formal.Util.AssertStandardAxioms

/-! Common finite reading predicates.  The coherence predicate is supplied by
each application independently of the existence of a global extension. -/

namespace AAT.AG.LocalSemanticReconstruction.FiniteReading

/-- The table obtained by reading an element only at the finite index set
`S`. -/
def restrict {A Index Value : Type*} (read : A → Index → Value)
    (S : Finset Index) (a : A) : {index // index ∈ S} → Value :=
  fun index => read a index.1

/-- A finite reading separates the selected global elements when its table
map is injective. -/
def Separates {A Index Value : Type*} (read : A → Index → Value)
    (S : Finset Index) : Prop :=
  Function.Injective (restrict read S)

/-- A finite reading extends every table satisfying a separately supplied
coherence predicate. -/
def Extends {A Index Value : Type*} (read : A → Index → Value)
    (S : Finset Index)
    (Coherent : ({index // index ∈ S} → Value) → Prop) : Prop :=
  ∀ table, Coherent table → ∃ a, restrict read S a = table

/-- A determining set has both separation and extension. -/
def Determining {A Index Value : Type*} (read : A → Index → Value)
    (S : Finset Index)
    (Coherent : ({index // index ∈ S} → Value) → Prop) : Prop :=
  Separates read S ∧ Extends read S Coherent

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteReading

end AAT.AG.LocalSemanticReconstruction.FiniteReading
