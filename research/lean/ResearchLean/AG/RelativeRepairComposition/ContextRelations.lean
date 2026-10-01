import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Set.Image

/-!
# Strict shared values and the two directions of contextual existence

This is the set-theoretic step of the proof. The singleton hypothesis here is a
direction condition; the affine application must construct its actual test from
primitive operations and discharge this condition for the allowed environment
family. It is not a definition of an actual affine environment or repair.
-/
namespace AAT.AG.RelativeRepairComposition.ContextRelations
universe uX uL uR uE
variable {X : Type uX} {L : Type uL} {R : Type uR}

/-- All independent left and right objects whose full shared values literally agree. -/
def StrictJoin (left : L → X) (right : R → X) :=
  {p : L × R // left p.1 = right p.2}

/-- Strict agreement exists exactly when the two independently realized shared ranges intersect. -/
theorem strict_join_nonempty (left : L → X) (right : R → X) :
    Nonempty (StrictJoin left right) ↔ (Set.range left ∩ Set.range right).Nonempty := by
  constructor
  · rintro ⟨⟨⟨l,r⟩,h⟩⟩
    exact ⟨left l,⟨⟨l,rfl⟩,⟨r,h.symm⟩⟩⟩
  · rintro ⟨x,⟨⟨l,hl⟩,⟨r,hr⟩⟩⟩
    exact ⟨⟨(l,r),hl.trans hr.symm⟩⟩

/-- Equal boundary relations have equal existence outcomes for every external relation. -/
theorem equal_relations_context (C D : Set X) (h : C = D) (V : Set X) :
    (C ∩ V).Nonempty ↔ (D ∩ V).Nonempty := by rw [h]

/-- Testing every realizable singleton detects both differences, using all external environments. -/
theorem contextual_iff_equal {Env : Type uE} (C D : Set X) (external : Env → Set X)
    (test : ∀ t ∈ C ∪ D, ∃ env : Env, external env = {t}) :
    (∀ env : Env, (C ∩ external env).Nonempty ↔ (D ∩ external env).Nonempty) ↔ C = D := by
  constructor
  · intro h
    ext t
    constructor
    · intro ht
      obtain ⟨env,he⟩ := test t (Or.inl ht)
      obtain ⟨u,huD,huV⟩ := (h env).mp ⟨t,ht,by rw [he]; exact Set.mem_singleton t⟩
      rw [he] at huV
      exact (Set.mem_singleton_iff.mp huV) ▸ huD
    · intro ht
      obtain ⟨env,he⟩ := test t (Or.inr ht)
      obtain ⟨u,huC,huV⟩ := (h env).mpr ⟨t,ht,by rw [he]; exact Set.mem_singleton t⟩
      rw [he] at huV
      exact (Set.mem_singleton_iff.mp huV) ▸ huC
  · intro h env
    exact equal_relations_context C D h (external env)

/-- The same conclusion applies to whole independent objects before any coordinate quotient. -/
theorem contextual_ranges {L' : Type uL} {Env : Type uE} (left : L → X) (other : L' → X)
    (objects : Env → Type uR) (boundary : ∀ env, objects env → X)
    (test : ∀ t ∈ Set.range left ∪ Set.range other,
      ∃ env, Set.range (boundary env) = {t}) :
    (∀ env, Nonempty (StrictJoin left (boundary env)) ↔
      Nonempty (StrictJoin other (boundary env))) ↔ Set.range left = Set.range other := by
  simpa only [strict_join_nonempty] using
    contextual_iff_equal (Set.range left) (Set.range other) (fun env => Set.range (boundary env)) test

end AAT.AG.RelativeRepairComposition.ContextRelations
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.ContextRelations
