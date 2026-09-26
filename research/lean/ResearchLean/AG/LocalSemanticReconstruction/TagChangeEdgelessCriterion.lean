import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Logic.Equiv.Bool
import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence
import Formal.Util.AssertStandardAxioms

/-! Specialize the general D criterion to the fixed edgeless tag index. -/

namespace AAT.AG.LocalSemanticReconstruction

open RealizationReconstruction

namespace TagChangeEdgelessCriterion

/-- The two hidden Bool permutations are the two xor translations. -/
noncomputable def boolPerm (bit : Bool) : Equiv.Perm Bool :=
  if bit then Equiv.boolNot else 1

private theorem perm_apply_eq_xor (permutation : Equiv.Perm Bool) (bit : Bool) :
    permutation bit = Bool.xor (permutation false) bit := by
  cases bit with
  | false => simp
  | true =>
    have hne : permutation false ≠ permutation true := by
      intro equality
      have h := permutation.injective equality
      cases h
    cases h : permutation false <;> cases h' : permutation true <;>
      simp [h, h'] at hne ⊢

private theorem boolPerm_false (bit : Bool) : boolPerm bit false = bit := by
  cases bit <;> rfl

/-- Evaluation at false identifies the permutation group of Bool with the
same xor group used by global tagged source choices. -/
noncomputable def boolPermMulEquiv : Equiv.Perm Bool ≃* Multiplicative Bool where
  toFun permutation := Multiplicative.ofAdd (permutation false)
  invFun bit := boolPerm bit.toAdd
  left_inv permutation := by
    apply Equiv.ext
    intro bit
    rw [perm_apply_eq_xor permutation bit]
    cases bit <;> cases h : permutation false <;> simp [boolPerm, h]
  right_inv bit := by
    apply Multiplicative.ext
    exact boolPerm_false bit.toAdd
  map_mul' first second := by
    apply Multiplicative.ext
    change (first * second) false = Bool.xor (first false) (second false)
    rw [Equiv.Perm.mul_apply, perm_apply_eq_xor]

/-- The tagged source objects form a named graph with no operations between
distinct vertices. -/
def graph : FixedFDirectedMultigraph where
  Vertex := TagChange.TaggedArchitectureIndex
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

def identity : FixedFGraphAutomorphism graph where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  source_rename := by intro e; exact e.elim
  target_rename := by intro e; exact e.elim

theorem reachable_iff_eq (first second : graph.Vertex) :
    FixedFUndirectedReachable graph first second ↔ first = second := by
  constructor
  · intro reachable
    induction reachable with
    | rel first second step =>
        obtain ⟨edge, _, _⟩ := step
        exact edge.elim
    | refl vertex => rfl
    | symm first second _ ih => exact ih.symm
    | trans first second third _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · intro h
    subst second
    exact Relation.EqvGen.refl _

/-- Components of the edgeless tagged graph are exactly its source objects. -/
noncomputable def componentEquiv :
    FixedFComponent graph ≃ TagChange.TaggedArchitectureIndex where
  toFun := Quotient.lift id (by
    intro first second h
    exact (reachable_iff_eq first second).1 h)
  invFun := fixedFComponentMk graph
  left_inv := by
    intro component
    refine Quotient.inductionOn component ?_
    intro source
    rfl
  right_inv := by intro source; rfl

theorem component_finite_iff :
    Finite (FixedFComponent graph) ↔
      Finite TagChange.TaggedArchitectureIndex := by
  constructor
  · intro h
    letI := h
    exact Finite.of_injective componentEquiv.symm componentEquiv.symm.injective
  · intro h
    letI := h
    exact Finite.of_injective componentEquiv componentEquiv.injective

/-- The same common finite-reading D criterion says that a determining
finite tag selection exists precisely when the actual source index is finite. -/
theorem finite_determining_iff :
    (∃ S : Finset graph.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt graph Bool identity) S
        (FinitePermutationReadingCriteria.EdgeCoherent graph Bool S)) ↔
      Finite TagChange.TaggedArchitectureIndex := by
  exact (FinitePermutationReadingCriteria.exists_finite_determining_iff
    graph Bool identity).trans component_finite_iff

/-- The actual architecture-object index is infinite, so the same D
predicate admits no finite determining reading on the tagged graph. -/
theorem no_finite_determining :
    ¬ ∃ S : Finset graph.Vertex,
      FiniteReading.Determining
        (FinitePermutationReadingCriteria.readAt graph Bool identity) S
        (FinitePermutationReadingCriteria.EdgeCoherent graph Bool S) := by
  intro h
  letI : Finite TagChange.TaggedArchitectureIndex :=
    finite_determining_iff.mp h
  exact not_finite TagChange.TaggedArchitectureIndex

/-- A source-choice function gives the actual preserving change whose Bool
permutation at each edgeless component is the corresponding xor translation. -/
noncomputable def edgelessChangeOfChoice
    (choice : TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex) :
    PermutationRestriction.PreservingChange graph Bool identity :=
  FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies.symm
    (fun component => boolPerm (choice (componentEquiv component)))

theorem edgeless_readAt_false
    (choice : TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) :
    (FinitePermutationReadingCriteria.readAt graph Bool identity
      (edgelessChangeOfChoice choice) source) false = choice source := by
  change (FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
    (edgelessChangeOfChoice choice) (fixedFComponentMk graph source)) false = _
  simp [edgelessChangeOfChoice, boolPerm_false, componentEquiv, fixedFComponentMk]

theorem edgeless_readAt_code
    (choice : TagChange.GlobalTagChange TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) :
    boolPermMulEquiv
      (FinitePermutationReadingCriteria.readAt graph Bool identity
        (edgelessChangeOfChoice choice) source) =
      Multiplicative.ofAdd (choice source) := by
  apply Multiplicative.ext
  exact edgeless_readAt_false choice source

/-- The edgeless D reading is the same pointwise source choice classified by
the existing ambient tagged subgroup. -/
theorem edgeless_readAt_actual_source_choice
    (choice : Multiplicative TagChangeKaroubiReconstruction.Choice)
    (source : TagChange.TaggedArchitectureIndex) :
    (FinitePermutationReadingCriteria.readAt graph Bool identity
      (edgelessChangeOfChoice choice.toAdd) source) false =
      TagChangeAmbientLocalEquivalence.readAmbientSourceChoiceAt
        (TagChangeAmbientCategory.sourceChoiceGroupEquiv choice) source := by
  rw [edgeless_readAt_false,
    TagChangeAmbientLocalEquivalence.readAmbientSourceChoiceAt_eq]
  simp

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeEdgelessCriterion

end TagChangeEdgelessCriterion

end AAT.AG.LocalSemanticReconstruction
