import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import ResearchLean.AG.RealizationReconstruction.MandatoryCFiniteReferenceObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Pointwise tag changes from all finite readings

This module proves the function-level core of G-124(E1b).  A local value is a
`Bool` table on one finite subset of the architecture-object index.  A coherent
family contains one such table for every finite subset and only restriction
equalities between them.  Singleton readings assemble the unique global
pointwise tag change, and the two read/assemble laws are proved separately.

The same local-reading definition also exhibits the finite-determination
obstruction: when the index is infinite, every finite reading misses a
nontrivial pointwise tag change.
-/

namespace AAT.AG.LocalSemanticReconstruction.TagChange

open AtomFoundation DoctrineFiberProduct RealizationReconstruction

universe u

variable {Ω : Type u}

/-- A pointwise tag change on the whole index type. -/
abbrev GlobalTagChange (Ω : Type u) := Ω → Bool

/-- A local tag table contains one bit at each member of a finite subset. -/
abbrev LocalTagTable (S : Finset Ω) := {x // x ∈ S} → Bool

namespace LocalTagTable

/-- Restrict a finite tag table along inclusion of finite subsets. -/
def restrict {S T : Finset Ω} (h : S ⊆ T) (table : LocalTagTable T) :
    LocalTagTable S :=
  fun x => table ⟨x.1, h x.2⟩

/-- Read a global pointwise tag change on one finite subset. -/
def read (change : GlobalTagChange Ω) (S : Finset Ω) : LocalTagTable S :=
  fun x => change x.1

/-- Each local tag table is a finite value type. -/
theorem finite_value_type (S : Finset Ω) : Finite (LocalTagTable S) := by
  classical
  letI : Fintype {x // x ∈ S} := Finset.fintypeCoeSort S
  letI : Fintype (LocalTagTable S) := inferInstance
  infer_instance

end LocalTagTable

/-- An inverse-limit element of finite tag tables.  Its only compatibility data
are restriction equalities; no global tag change or extension witness is stored. -/
structure CoherentFamily (Ω : Type u) where
  /-- One local table on every finite subset. -/
  value : ∀ S : Finset Ω, LocalTagTable S
  /-- Values agree under every inclusion of finite subsets. -/
  coherent : ∀ (S T : Finset Ω) (h : S ⊆ T),
    LocalTagTable.restrict h (value T) = value S

namespace CoherentFamily

/-- Coherent families are determined by all their finite tables. -/
@[ext]
theorem ext {a b : CoherentFamily Ω} (h : ∀ S, a.value S = b.value S) : a = b := by
  cases a with
  | mk av ac =>
    cases b with
    | mk bv bc =>
      have hv : av = bv := by
        funext S
        exact h S
      subst bv
      rfl

end CoherentFamily

/-- Read a global tag change on every finite subset. -/
def read (change : GlobalTagChange Ω) : CoherentFamily Ω where
  value S := LocalTagTable.read change S
  coherent := by
    intro S T h
    rfl

/-- Assemble a global tag change from singleton finite readings. -/
noncomputable def assemble (family : CoherentFamily Ω) : GlobalTagChange Ω :=
  fun x => family.value {x} ⟨x, by simp⟩

/-- Singleton assembly after reading recovers the original global change. -/
@[simp]
theorem assemble_read (change : GlobalTagChange Ω) :
    assemble (read change) = change := by
  funext x
  rfl

/-- Reading a singleton-assembled change recovers every finite local table. -/
@[simp]
theorem read_assemble (family : CoherentFamily Ω) :
    read (assemble family) = family := by
  apply CoherentFamily.ext
  intro S
  funext x
  have hsubset : ({x.1} : Finset Ω) ⊆ S :=
    Finset.singleton_subset_iff.mpr x.2
  have hcoherent := family.coherent {x.1} S hsubset
  have hat := congrFun hcoherent ⟨x.1, by simp⟩
  simpa only [read, assemble, LocalTagTable.read, LocalTagTable.restrict] using hat.symm

/-- Pointwise tag changes are exactly coherent families of all finite readings. -/
noncomputable def globalTagChangeEquivCoherentFamily :
    GlobalTagChange Ω ≃ CoherentFamily Ω where
  toFun := read
  invFun := assemble
  left_inv := assemble_read
  right_inv := read_assemble

/-- The concrete index type of the accepted tagged-operation source-choice family. -/
abbrev TaggedArchitectureIndex := ArchitectureObject FiniteModel.carrier

/-- G-124(E1b)'s function-level inverse-limit equivalence on the actual
mandatory tagged-operation index. -/
noncomputable def taggedSourceChoiceEquivCoherentFamily :
    (TaggedArchitectureIndex → Bool) ≃ CoherentFamily TaggedArchitectureIndex :=
  globalTagChangeEquivCoherentFamily

/-- Assemble a coherent finite-reading family into the accepted ambient tagged
package endomorphism constructed by the G-123 source-choice family. -/
noncomputable def assembleTaggedSourceChoiceTotal
    (family : CoherentFamily TaggedArchitectureIndex) :
    PackageTotalHom taggedOperationPackage taggedOperationPackage :=
  taggedSourceChoiceTotal (assemble family)

/-- Reading the assembled tagged package endomorphism recovers the same global
pointwise choice obtained by singleton assembly. -/
@[simp]
theorem readTaggedSourceChoice_assembleTaggedSourceChoiceTotal
    (family : CoherentFamily TaggedArchitectureIndex) :
    readTaggedSourceChoice (assembleTaggedSourceChoiceTotal family) = assemble family := by
  exact readTaggedSourceChoice_taggedSourceChoiceTotal (assemble family)

/-- Consequently every finite local table of the assembled ambient
endomorphism is exactly the table supplied by the coherent family. -/
theorem read_assembleTaggedSourceChoiceTotal_on_finite
    (family : CoherentFamily TaggedArchitectureIndex) (S : Finset TaggedArchitectureIndex) :
    LocalTagTable.read
        (readTaggedSourceChoice (assembleTaggedSourceChoiceTotal family)) S =
      family.value S := by
  rw [readTaggedSourceChoice_assembleTaggedSourceChoiceTotal]
  have hfamily := congrArg CoherentFamily.value (read_assemble family)
  exact congrFun hfamily S

/-- On an infinite index type, every finite reading misses a nontrivial
pointwise tag change.  The witness flips exactly one point outside the reading. -/
theorem finite_reading_not_separating [Infinite Ω] (S : Finset Ω) :
    ∃ change : GlobalTagChange Ω,
      change ≠ (fun _ => false) ∧ ∀ x ∈ S, change x = false := by
  classical
  obtain ⟨outside, houtside⟩ := Infinite.exists_notMem_finset S
  let change : GlobalTagChange Ω := fun x => if x = outside then true else false
  refine ⟨change, ?_, ?_⟩
  · intro hchange
    have hat := congrFun hchange outside
    simp [change] at hat
  · intro x hx
    have hne : x ≠ outside := by
      intro h
      subst x
      exact houtside hx
    simp [change, hne]

/-- The actual mandatory tagged-operation index is infinite, so no finite
source reading separates all pointwise tag changes. -/
theorem taggedSourceChoice_finite_reading_not_separating
    (S : Finset TaggedArchitectureIndex) :
    ∃ choice : TaggedArchitectureIndex → Bool,
      choice ≠ (fun _ => false) ∧ ∀ x ∈ S, choice x = false :=
  finite_reading_not_separating S

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChange

end AAT.AG.LocalSemanticReconstruction.TagChange
