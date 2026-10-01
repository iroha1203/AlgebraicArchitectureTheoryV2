import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FiniteFamilyCoordinates
import ResearchLean.AG.RelativeRepairComposition.FiniteElimination
import Mathlib.Data.List.FinRange

/-!
# Explicit enumeration of every original coefficient coordinate

## Implementation notes

Lists are generated from the original cell enumeration and the complete basis
indices. No quotient-to-list or noncomputable index choice is used.
-/
namespace AAT.AG.RelativeRepairComposition
namespace FiniteElimination.Enumeration
universe u
variable {A : Type u}

/-- Build the finite carrier instance from its actual executable input list. -/
def fintype (E : FiniteElimination.Enumeration A) [DecidableEq A] : Fintype A :=
  ⟨E.values.toFinset,by intro a; exact List.mem_toFinset.mpr (E.complete a)⟩

/-- Enumerate a decidable subset while keeping every original included element. -/
def subtype (E : FiniteElimination.Enumeration A) (p : A → Prop) [DecidablePred p] :
    FiniteElimination.Enumeration {a // p a} where
  values := E.values.filterMap (fun a => if ha : p a then some ⟨a,ha⟩ else none)
  complete a := by
    apply List.mem_filterMap.mpr
    refine ⟨a.1,E.complete a.1,?_⟩
    simp only [dif_pos a.2]

end FiniteElimination.Enumeration
namespace FiniteFamily
universe uk ui ua
variable {k : Type uk} [Field k]
variable {I : Type ui} (A : I → Type ua)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]
variable (B : Bases (k := k) A) (s p : Set I)
variable [DecidablePred (· ∈ s)] [DecidablePred (· ∈ p)]

/-- Enumerate every nonfixed original cell and every complete kernel basis coordinate. -/
def indexEnumeration (E : FiniteElimination.Enumeration I) :
    FiniteElimination.Enumeration (Index A B s p) where
  values := E.values.flatMap (fun i => if hi : i ∈ s ∧ i ∉ p then
    (List.finRange (B.dimension i)).map (fun j => ⟨⟨i,hi⟩,j⟩) else [])
  complete j := by
    rcases j with ⟨⟨i,hi⟩,a⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,E.complete i,?_⟩
    simp only [dif_pos hi]
    exact List.mem_map.mpr ⟨a,by simp,rfl⟩

end FiniteFamily
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
