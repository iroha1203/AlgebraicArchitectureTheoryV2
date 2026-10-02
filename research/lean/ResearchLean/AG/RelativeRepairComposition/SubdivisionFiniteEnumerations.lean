import ResearchLean.AG.RelativeRepairComposition.FiniteCoordinateEnumerations
import ResearchLean.AG.RelativeRepairComposition.SubdivisionFiniteIncidence

/-!
# Complete finite subdivision inputs from the original named-cell lists

## Implementation notes

The new edge enumeration retains each complete old name except the selected
one and adds the two actual factor names. It is computed from the original
list, rather than supplying a new list or selecting generated output. The
actual edge-name equivalence supplies both completeness and decidable equality.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration
universe u v
variable {A : Type u} {B : Type v}

/-- Mapping a complete input list through a full equivalence retains every target element. -/
def mapEquiv (E : FiniteElimination.Enumeration A) (e : A ≃ B) :
    FiniteElimination.Enumeration B where
  values := E.values.map e
  complete b := List.mem_map.mpr ⟨e.symm b,E.complete (e.symm b),e.apply_symm_apply b⟩

/-- The mapped list evaluates the same input values through its specified full equivalence. -/
theorem mapEquiv_values (E : FiniteElimination.Enumeration A) (e : A ≃ B) :
    (mapEquiv E e).values = E.values.map e := rfl

/-- Independent universe levels retain both complete input lists in their disjoint sum. -/
def sum (E : FiniteElimination.Enumeration A) (F : FiniteElimination.Enumeration B) :
    FiniteElimination.Enumeration (A ⊕ B) where
  values := E.values.map Sum.inl ++ F.values.map Sum.inr
  complete a := by cases a <;> simp [E.complete,F.complete]

end AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration

namespace AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))
variable [DecidableEq (EdgeName (K := K))]

/-- Both actual factor tags have a literal complete input enumeration. -/
def factorEnumeration : FiniteElimination.Enumeration Bool :=
  ⟨[false,true],by intro b; cases b <;> simp⟩

/-- Actual complete new edge names have equality decided by their old name or factor tag. -/
instance edgeDecidableEq : DecidableEq (EdgeName (K := presentation K chosen)) :=
  (edgeNameEquiv K chosen).decidableEq

/-- The entire new edge list is generated from all retained old names and both factor tags. -/
def edgeEnumeration (E : FiniteElimination.Enumeration (EdgeName (K := K))) :
    FiniteElimination.Enumeration (EdgeName (K := presentation K chosen)) :=
  ((E.subtype (· ≠ chosen)).sum factorEnumeration).mapEquiv
    (edgeNameEquiv K chosen).symm

/-- The computed new list contains each actual retained or factor name. -/
theorem edgeEnumeration_complete (E : FiniteElimination.Enumeration (EdgeName (K := K)))
    (e : EdgeName (K := presentation K chosen)) :
    e ∈ (edgeEnumeration K chosen E).values := (edgeEnumeration K chosen E).complete e

/-- The complete computed list supplies the same actual finite edge carrier. -/
def edgeFintype (E : FiniteElimination.Enumeration (EdgeName (K := K))) :
    Fintype (EdgeName (K := presentation K chosen)) := (edgeEnumeration K chosen E).fintype

end AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.FiniteElimination.Enumeration
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.FiniteEnumerations
