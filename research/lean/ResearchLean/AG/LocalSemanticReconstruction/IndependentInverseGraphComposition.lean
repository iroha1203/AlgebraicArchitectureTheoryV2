import ResearchLean.AG.LocalSemanticReconstruction.IndependentInverseGraphReadings
import Formal.Util.AssertStandardAxioms

/-!
# Composition of primitive inverse graphs

The forward point follows the two forward rows. The backward point follows
the two backward rows in reverse order. Each output uses a finite intermediate
point, as in directed carrier-graph composition. Native equivalences are used
only to verify this point construction.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph

noncomputable section

universe u v w

/-- Compose primitive rows in forward order and reverse the order for backward rows. -/
def compose (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    Table.{u, w}
  | .forward q => IndependentCarrierGraph.compose α β γ (forward t) ht.forward (forward s) q
  | .backward q => IndependentCarrierGraph.compose γ β α (backward s) hs.backward (backward t) q

/-- The direct point construction agrees with the composite of reconstructed equivalences. -/
theorem compose_eq_read (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    compose α β γ t ht s hs = read α γ ((assemble α β t ht).trans (assemble β γ s hs)) := by
  funext q
  cases q with
  | forward q =>
    have h := IndependentCarrierGraph.read_assemble α γ
      (IndependentCarrierGraph.compose α β γ (forward t) ht.forward (forward s))
      (IndependentCarrierGraph.compose_isLawful α β γ (forward t) ht.forward (forward s) hs.forward)
    rw [IndependentCarrierGraph.assemble_compose] at h
    exact congrFun h.symm q
  | backward q =>
    have h := IndependentCarrierGraph.read_assemble γ α
      (IndependentCarrierGraph.compose γ β α (backward s) hs.backward (backward t))
      (IndependentCarrierGraph.compose_isLawful γ β α (backward s) hs.backward (backward t) ht.backward)
    rw [IndependentCarrierGraph.assemble_compose] at h
    exact congrFun h.symm q

/-- Point composition preserves exact-one rows and both inverse equations. -/
theorem compose_isLawful (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    IsLawful α γ (compose α β γ t ht s hs) := by
  rw [compose_eq_read]
  exact read_isLawful _ _ _

/-- Assembly respects primitive inverse-graph composition. -/
theorem assemble_compose (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s) :
    assemble α γ (compose α β γ t ht s hs) (compose_isLawful α β γ t ht s hs) =
      (assemble α β t ht).trans (assemble β γ s hs) := by
  apply Equiv.ext
  intro x
  exact congrFun (IndependentCarrierGraph.assemble_compose α β γ
    (forward t) ht.forward (forward s) hs.forward) x

/-- A forward output uses one first-row point and one second-row point. -/
theorem compose_forward_support (α : Type u) (β : Type v) (γ : Type w)
    (t t' : Table.{u, v}) (ht : IsLawful α β t) (ht' : IsLawful α β t')
    (s s' : Table.{v, w}) (hs : IsLawful β γ s) (hs' : IsLawful β γ s')
    (x : α) (z : γ)
    (h1 : t (.forward (.edge α β x (assemble α β t ht x))) =
      t' (.forward (.edge α β x (assemble α β t ht x))))
    (h2 : s (.forward (.edge β γ (assemble α β t ht x) z)) =
      s' (.forward (.edge β γ (assemble α β t ht x) z))) :
    compose α β γ t ht s hs (.forward (.edge α γ x z)) =
      compose α β γ t' ht' s' hs' (.forward (.edge α γ x z)) :=
  IndependentCarrierGraph.compose_point_finite_support α β γ
    (forward t) (forward t') ht.forward ht'.forward (forward s) (forward s') x z h1 h2

/-- A backward output uses the second backward row before the first backward row. -/
theorem compose_backward_support (α : Type u) (β : Type v) (γ : Type w)
    (t t' : Table.{u, v}) (ht : IsLawful α β t) (ht' : IsLawful α β t')
    (s s' : Table.{v, w}) (hs : IsLawful β γ s) (hs' : IsLawful β γ s')
    (z : γ) (x : α)
    (h1 : s (.backward (.edge γ β z ((assemble β γ s hs).symm z))) =
      s' (.backward (.edge γ β z ((assemble β γ s hs).symm z))))
    (h2 : t (.backward (.edge β α ((assemble β γ s hs).symm z) x)) =
      t' (.backward (.edge β α ((assemble β γ s hs).symm z) x))) :
    compose α β γ t ht s hs (.backward (.edge γ α z x)) =
      compose α β γ t' ht' s' hs' (.backward (.edge γ α z x)) :=
  IndependentCarrierGraph.compose_point_finite_support γ β α
    (backward s) (backward s') hs.backward hs'.backward (backward t) (backward t') z x h1 h2

/-- Inactive candidate carriers remain false in both directions of a composite. -/
theorem compose_inactive (α : Type u) (β : Type v) (γ : Type w)
    (t : Table.{u, v}) (ht : IsLawful α β t) (s : Table.{v, w}) (hs : IsLawful β γ s)
    (S : Type u) (T : Type w) (x : S) (z : T) (hn : S ≠ α ∨ T ≠ γ) :
    compose α β γ t ht s hs (.forward (.edge S T x z)) = false ∧
      compose α β γ t ht s hs (.backward (.edge T S z x)) = false :=
  ⟨(compose_isLawful α β γ t ht s hs).forward.1 _ _ _ _ hn,
    (compose_isLawful α β γ t ht s hs).backward.1 _ _ _ _ hn.symm⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentInverseGraph
