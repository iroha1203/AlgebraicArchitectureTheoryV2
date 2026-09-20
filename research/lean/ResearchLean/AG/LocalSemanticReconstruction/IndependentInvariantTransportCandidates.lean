import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import ResearchLean.AG.RealizationReconstruction.MandatoryCFiniteReferenceObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Invariant transport candidates: exactness and two failed simplifications

This is evidence for an unresolved Part I design question, outside the numbered
research cycles. It is not an implementation of the accepted local Hom laws.

The native function-invariant condition hides a value equivalence in `Prop`.
Separate finite evaluation constraints do not imply that condition: finite
rotations approximate successor, which is not surjective. Retaining a chosen
value equivalence as Hom data also fails: two permutations fixing zero give
different witnesses for the same constant invariant.

The `InfiniteWitness` candidate is exactly equivalent to native transport and
erases witness choices. However, its existential quantifies a whole coherent
family. It has not met the approved restriction to primitive values or finite
existence witnesses, and is not imported by the object or Hom assemblers.

## Implementation notes

These results rule out the two specified shortcuts, not every possible local
presentation and not the fixed G-124 target. The surjective architecture reading
is constructed using the accepted natural-number architecture-object injection;
its existence is not an additional assumption. No native invariant or Hom
meaning is changed.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentInvariantTransportCandidates.FiniteApproximation

noncomputable section

/-- Rotate the first `n + 1` natural numbers and fix all larger values. -/
def prefixCycle : ℕ → Equiv.Perm ℕ
  | 0 => Equiv.refl ℕ
  | n + 1 => (prefixCycle n).trans (Equiv.swap 0 (n + 1))

/-- The finite rotation agrees with successor below its last point. -/
theorem prefixCycle_properties (n : ℕ) :
    prefixCycle n n = 0 ∧
      (∀ x, x < n → prefixCycle n x = x + 1) ∧
      (∀ x, n < x → prefixCycle n x = x) := by
  induction n with
  | zero => simp [prefixCycle]
  | succ n ih =>
      refine ⟨?_, ?_, ?_⟩
      · simp only [prefixCycle, Equiv.trans_apply, ih.2.2 (n + 1) (by omega)]
        exact Equiv.swap_apply_right _ _
      · intro x hx
        simp only [prefixCycle, Equiv.trans_apply]
        by_cases h : x = n
        · subst x
          rw [ih.1, Equiv.swap_apply_left]
        · rw [ih.2.1 x (by omega)]
          exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
      · intro x hx
        simp only [prefixCycle, Equiv.trans_apply]
        rw [ih.2.2 x (by omega)]
        exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)

/-- Every finite set of successor constraints extends to a genuine permutation. -/
theorem finite_successor_constraints (S : Finset ℕ) :
    ∃ e : Equiv.Perm ℕ, ∀ n ∈ S, e n = n + 1 := by
  refine ⟨prefixCycle (S.sup id + 1), ?_⟩
  intro n hn
  apply (prefixCycle_properties _).2.1
  have h : n ≤ S.sup id := Finset.le_sup (f := id) hn
  omega

/-- No permutation can meet the same constraints at every natural number. -/
theorem no_global_successor_permutation :
    ¬ ∃ e : Equiv.Perm ℕ, ∀ n, e n = n + 1 := by
  rintro ⟨e, he⟩
  obtain ⟨n, hn⟩ := e.surjective 0
  have := he n
  omega

variable {U : AtomCarrier.{0}}

/-- Any natural-valued architecture reading has witnesses on each finite list. -/
theorem finite_evaluation_constraints (f : ArchitectureObject U → ℕ)
    (S : Finset (ArchitectureObject U)) :
    ∃ e : Equiv.Perm ℕ, ∀ A ∈ S, e (f A) = f A + 1 := by
  classical
  obtain ⟨e, he⟩ := finite_successor_constraints (S.image f)
  exact ⟨e, fun A hA => he _ (Finset.mem_image.mpr ⟨A, hA, rfl⟩)⟩

/-- Surjectivity makes the original native invariant transport impossible. -/
theorem successor_not_transported (f : ArchitectureObject U → ℕ)
    (hf : Function.Surjective f) :
    ¬ Invariant.TransportedAlong
      (.function ⟨ℕ, f⟩) (.function ⟨ℕ, fun A => f A + 1⟩) id id := by
  rintro ⟨e, he⟩
  apply no_global_successor_permutation
  refine ⟨e, ?_⟩
  intro n
  obtain ⟨A, hA⟩ := hf n
  simpa only [id_eq, hA] using he A

/-- The accepted natural-number architecture objects give a surjective reading. -/
def naturalReading : ArchitectureObject FiniteModel.carrier → ℕ :=
  Function.invFun RealizationReconstruction.naturalArchitectureObject

/-- Surjectivity is discharged by the accepted architecture-object injection. -/
theorem naturalReading_surjective : Function.Surjective naturalReading :=
  Function.invFun_surjective RealizationReconstruction.naturalArchitectureObject_injective

/-- Actual native function invariants have all finite witnesses but no transport.
This refutes the separate-finite-extension candidate, not every local presentation. -/
theorem native_finite_constraints_do_not_imply_transport :
    (∀ S : Finset (ArchitectureObject FiniteModel.carrier),
      ∃ e : Equiv.Perm ℕ, ∀ A ∈ S, e (naturalReading A) = naturalReading A + 1) ∧
    ¬ Invariant.TransportedAlong
      (.function ⟨ℕ, naturalReading⟩)
      (.function ⟨ℕ, fun A => naturalReading A + 1⟩) id id :=
  ⟨finite_evaluation_constraints naturalReading,
    successor_not_transported naturalReading naturalReading_surjective⟩

/-- Two different equivalence witnesses preserve the same constant invariant. -/
theorem distinct_constant_witnesses :
    ∃ e₁ e₂ : Equiv.Perm (Fin 3), e₁ ≠ e₂ ∧ e₁ 0 = 0 ∧ e₂ 0 = 0 := by
  refine ⟨Equiv.refl _, Equiv.swap 1 2, ?_, rfl, ?_⟩
  · intro h
    have hh := congrArg (fun e : Equiv.Perm (Fin 3) => e 1) h
    have hn : (1 : Fin 3) ≠ 2 := by decide
    simp only [Equiv.refl_apply, Equiv.swap_apply_left] at hh
    exact hn hh
  · exact Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)

/-- Forgetting a chosen constant-value witness is not faithful to its data.
The two choices cannot be retained as distinct local Hom data. -/
theorem chosen_constant_witness_forget_not_injective :
    ¬ Function.Injective (fun (_ : {e : Equiv.Perm (Fin 3) // e 0 = 0}) => ()) := by
  intro h
  obtain ⟨e₁, e₂, hne, h₁, h₂⟩ := distinct_constant_witnesses
  exact hne (congrArg Subtype.val (h (a₁ := ⟨e₁, h₁⟩) (a₂ := ⟨e₂, h₂⟩) rfl))

end

end AAT.AG.LocalSemanticReconstruction.IndependentInvariantTransportCandidates.FiniteApproximation


namespace AAT.AG.LocalSemanticReconstruction.IndependentInvariantTransportCandidates.InfiniteWitness

noncomputable section

universe u w

variable {U : AtomCarrier.{u}} {ι : Type w}

/-- Every value is a finite Boolean table; the family ranges over all finite sets. -/
abbrev WitnessFamily := TagChange.CoherentFamily IndependentInverseGraph.Query.{u, u}

/-- Only graph points, inverse laws, and evaluation-preserving point pairs are tested. -/
def PointLaws (I J : FunctionInvariant U) (source target : ι → ArchitectureObject U)
    (m : WitnessFamily.{u}) : Prop :=
  IndependentInverseGraph.IsLawful I.Value J.Value (TagChange.assemble m) ∧
    ∀ a, TagChange.assemble m (.forward (.edge I.Value J.Value
      (I.evaluate (source a)) (J.evaluate (target a)))) = true

/-- Existential erasure retains no selected auxiliary inverse graph as Hom data.
This quantifies an entire coherent family, not a single finite witness. -/
def HasWitness (I J : FunctionInvariant U) (source target : ι → ArchitectureObject U) : Prop :=
  ∃ m : WitnessFamily.{u}, PointLaws I J source target m

/-- The exploratory infinite-family condition is exactly the original native existential. -/
theorem hasWitness_iff_transported (I J : FunctionInvariant U)
    (source target : ι → ArchitectureObject U) :
    HasWitness I J source target ↔
      Invariant.TransportedAlong (.function I) (.function J) source target := by
  constructor
  · rintro ⟨m, hm, he⟩
    refine ⟨IndependentInverseGraph.assemble I.Value J.Value (TagChange.assemble m) hm, ?_⟩
    intro a
    exact IndependentCarrierGraph.assemble_eq_of_edge I.Value J.Value
      (IndependentInverseGraph.forward (TagChange.assemble m)) hm.forward (he a)
  · rintro ⟨e, he⟩
    refine ⟨TagChange.read (IndependentInverseGraph.read I.Value J.Value e), ?_, ?_⟩
    · rw [TagChange.assemble_read]
      exact IndependentInverseGraph.read_isLawful I.Value J.Value e
    · intro a
      rw [TagChange.assemble_read]
      exact (IndependentCarrierGraph.read_edge I.Value J.Value e _ _).2 (he a)

/-- Erasing the witness keeps each directed object map only once. -/
def transportEquiv (I J : FunctionInvariant U) (source : ι → ArchitectureObject U) :
    {target : ι → ArchitectureObject U // HasWitness I J source target} ≃
      {target : ι → ArchitectureObject U //
        Invariant.TransportedAlong (.function I) (.function J) source target} where
  toFun t := ⟨t.val, (hasWitness_iff_transported I J source t.val).1 t.property⟩
  invFun t := ⟨t.val, (hasWitness_iff_transported I J source t.val).2 t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentInvariantTransportCandidates.InfiniteWitness

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentInvariantTransportCandidates
