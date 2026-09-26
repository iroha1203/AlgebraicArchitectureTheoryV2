import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationReadingCriteria
import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality
import Formal.Util.AssertStandardAxioms

/-! The executable finite graph program acts on the same actual changes and
point reading as the unrestricted component criteria.  Enumeration and
decidable equality occur only in the executable specialization. -/

namespace AAT.AG.LocalSemanticReconstruction.FinitePermutationReadingEffectiveness

open RealizationReconstruction
open FinitePermutationReadingCriteria

universe u v w

variable (F : FixedFDirectedMultigraph.{u, v}) (K : Type w)
  (visible : FixedFGraphAutomorphism F)

/-- The graph criteria and the executable program evaluate the identical
actual preserving change at each vertex. -/
theorem readAt_eq_finiteEffectiveness :
    readAt F K visible = FiniteEffectiveness.readPreservingChangeAt F K visible :=
  rfl

/-- An explicitly enumerated vertex type turns an arbitrary finite selection
into the existing program's retained-vertex input without changing it. -/
theorem retainedVertices_mem [Fintype F.Vertex] [DecidableEq F.Vertex]
    (S : Finset F.Vertex) :
    FiniteEffectiveness.retainedVertices F (fun vertex => vertex ∈ S) = S := by
  ext vertex
  simp [FiniteEffectiveness.retainedVertices]

/-- Reindex a raw Finset table onto the executable program's selected-vertex
subtype; the actual vertices and values are unchanged. -/
def toProgramTable [Fintype F.Vertex] [DecidableEq F.Vertex]
    (S : Finset F.Vertex)
    (table : {vertex // vertex ∈ S} → Equiv.Perm K) :
    {vertex // vertex ∈ FiniteEffectiveness.retainedVertices F
      (fun vertex => vertex ∈ S)} → Equiv.Perm K :=
  fun vertex => table ⟨vertex.1, by simpa only [retainedVertices_mem F S] using vertex.2⟩

/-- Both forms of finite coherence inspect exactly the named edges whose
endpoints lie in the selected Finset. -/
theorem coherent_iff [Fintype F.Vertex] [DecidableEq F.Vertex]
    (S : Finset F.Vertex)
    (table : {vertex // vertex ∈ S} → Equiv.Perm K) :
    EdgeCoherent F K S table ↔
      FiniteEffectiveness.PermutationTableCoherent F
        (fun vertex => vertex ∈ S) K (toProgramTable F K S table) := by
  constructor <;> intro h edge
  · simpa [FiniteEffectiveness.PermutationTableCoherent,
      FiniteEffectiveness.toPermutationVertexTable, toProgramTable] using h edge
  · simpa [FiniteEffectiveness.PermutationTableCoherent,
      FiniteEffectiveness.toPermutationVertexTable, toProgramTable] using h edge

/-- The accepted executable algorithm, expressed on the general criterion's
exact Finset and independently coherent raw table. -/
def effectivenessProgram
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    [Fintype K] [DecidableEq K]
    (S : Finset F.Vertex)
    (retains : InducedComponent.RetainsFullConnectivity F
      (fun vertex => vertex ∈ S)) :
    FiniteReading.EffectivenessProgram (readAt F K visible) S
      (EdgeCoherent F K S) := by
  letI : DecidablePred (fun vertex : F.Vertex => vertex ∈ S) :=
    inferInstance
  let old := FiniteEffectiveness.permutationEffectivenessProgram
    F (fun vertex => vertex ∈ S) K visible retains
  refine {
    coherenceTest := fun table => old.coherenceTest (toProgramTable F K S table)
    coherenceTest_eq_true_iff := ?_
    extend? := fun table => old.extend? (toProgramTable F K S table)
    extend_eq_none_iff := ?_
    restrict_eq_of_extend_eq_some := ?_
  }
  · intro table
    exact (old.coherenceTest_eq_true_iff (toProgramTable F K S table)).trans
      (coherent_iff F K S table).symm
  · intro table
    exact (old.extend_eq_none_iff (toProgramTable F K S table)).trans
      (not_congr (coherent_iff F K S table).symm)
  · intro table change success
    have h := old.restrict_eq_of_extend_eq_some
      (toProgramTable F K S table) change success
    funext vertex
    have point := congrFun h
      ⟨vertex.1, by simpa only [retainedVertices_mem F S] using vertex.2⟩
    simpa [FiniteReading.restrict, toProgramTable] using point
/-- Once the general raw-table extension property is known for a finite
selection, the accepted executable program applies to the same actual
preserving changes.  It decides the original retained-edge predicate,
rejects exactly incoherent tables, and reads successful results back. -/
theorem effective_of_extends
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    [Fintype K] [DecidableEq K] [Nontrivial K]
    (S : Finset F.Vertex)
    (hExtends : FiniteReading.Extends (readAt F K visible) S
      (EdgeCoherent F K S)) :
    FiniteReading.Effective (readAt F K visible) S
      (EdgeCoherent F K S) := by
  have retains := (extends_iff F K visible S).1 hExtends
  exact ⟨effectivenessProgram F K visible S retains⟩

/-- In an enumerated finite graph, one finite selection both determines every
actual preserving change and supports the executable coherence/extension
program.  The selected vertices come from the general component criterion. -/
theorem exists_effective_determining
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    [Fintype K] [DecidableEq K] [Nontrivial K]
    [Finite (FixedFComponent F)] :
    ∃ S : Finset F.Vertex,
      FiniteReading.Determining (readAt F K visible) S
        (EdgeCoherent F K S) ∧
      FiniteReading.Effective (readAt F K visible) S
        (EdgeCoherent F K S) := by
  obtain ⟨S, hS⟩ := (exists_finite_determining_iff F K visible).2 inferInstance
  exact ⟨S, hS, effective_of_extends F K visible S hS.2⟩

/-- The accepted factorial-per-component count measures the actual output
fiber of the same effective finite reading, for every finite graph and
hidden carrier satisfying the nontriviality condition. -/
theorem finite_effective_fiber_count
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    [Fintype K] [DecidableEq K] [Nontrivial K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    ∃ S : Finset F.Vertex,
      FiniteReading.Determining (readAt F K visible.1) S
        (EdgeCoherent F K S) ∧
      FiniteReading.Effective (readAt F K visible.1) S
        (EdgeCoherent F K S) ∧
      Nat.card (PermutationRestriction.PreservingChange F K visible.1) =
        Nat.factorial (Nat.card K) ^ Nat.card (FixedFComponent F) := by
  obtain ⟨S, determining, effective⟩ :=
    exists_effective_determining F K visible.1
  exact ⟨S, determining, effective,
    FinitePermutationExampleCardinality.natCard_preservingChange H visible⟩

open RealizationReconstruction.FixedFFiniteExamples

section BoolLensExample

local instance : Fintype BoolLensGraph.Vertex := by
  change Fintype Bool
  infer_instance

local instance : DecidableEq BoolLensGraph.Vertex := by
  change DecidableEq Bool
  infer_instance

local instance : Fintype BoolLensGraph.Edge := by
  change Fintype (Bool × Bool)
  infer_instance

/-- The accepted Bool-lens identity fiber count belongs to the actual output
type of a finite effective determining reading. -/
theorem boolLens_identity_effective_count :
    ∃ S : Finset BoolLensGraph.Vertex,
      FiniteReading.Determining
        (readAt BoolLensGraph Bool boolLensIdentityAutomorphism) S
        (EdgeCoherent BoolLensGraph Bool S) ∧
      FiniteReading.Effective
        (readAt BoolLensGraph Bool boolLensIdentityAutomorphism) S
        (EdgeCoherent BoolLensGraph Bool S) ∧
      Nat.card (PermutationRestriction.PreservingChange BoolLensGraph Bool
        boolLensIdentityAutomorphism) = 2 := by
  obtain ⟨S, determining, effective⟩ :=
    exists_effective_determining BoolLensGraph Bool boolLensIdentityAutomorphism
  exact ⟨S, determining, effective,
    FinitePermutationExampleCardinality.boolLens_preservingChange_count_identity⟩

/-- The nonidentity visible Bool-lens change has the same exact finite
reading and the accepted two-element output fiber. -/
theorem boolLens_flip_effective_count :
    ∃ S : Finset BoolLensGraph.Vertex,
      FiniteReading.Determining
        (readAt BoolLensGraph Bool boolLensFlipAutomorphism) S
        (EdgeCoherent BoolLensGraph Bool S) ∧
      FiniteReading.Effective
        (readAt BoolLensGraph Bool boolLensFlipAutomorphism) S
        (EdgeCoherent BoolLensGraph Bool S) ∧
      Nat.card (PermutationRestriction.PreservingChange BoolLensGraph Bool
        boolLensFlipAutomorphism) = 2 := by
  obtain ⟨S, determining, effective⟩ :=
    exists_effective_determining BoolLensGraph Bool boolLensFlipAutomorphism
  exact ⟨S, determining, effective,
    FinitePermutationExampleCardinality.boolLens_preservingChange_count_flip⟩

end BoolLensExample

section ProtocolExample

local instance : Fintype protocolGraph.Vertex := by
  change Fintype (Fin 4)
  infer_instance

local instance : DecidableEq protocolGraph.Vertex := by
  change DecidableEq (Fin 4)
  infer_instance

local instance : Fintype protocolGraph.Edge := by
  change Fintype Bool
  infer_instance

/-- The fixed two-session protocol has the accepted four-element actual
output fiber together with one executable determining reading. -/
theorem protocol_identity_effective_count :
    ∃ S : Finset protocolGraph.Vertex,
      FiniteReading.Determining
        (readAt protocolGraph Bool protocolIdentityAutomorphism) S
        (EdgeCoherent protocolGraph Bool S) ∧
      FiniteReading.Effective
        (readAt protocolGraph Bool protocolIdentityAutomorphism) S
        (EdgeCoherent protocolGraph Bool S) ∧
      Nat.card (PermutationRestriction.PreservingChange protocolGraph Bool
        protocolIdentityAutomorphism) = 4 := by
  obtain ⟨S, determining, effective⟩ :=
    exists_effective_determining protocolGraph Bool protocolIdentityAutomorphism
  exact ⟨S, determining, effective,
    FinitePermutationExampleCardinality.protocol_preservingChange_count_identity⟩

/-- The named session swap also has an effective determining reading whose
actual output fiber has the accepted four elements. -/
theorem protocol_sessionSwap_effective_count :
    ∃ S : Finset protocolGraph.Vertex,
      FiniteReading.Determining
        (readAt protocolGraph Bool protocolSessionSwapAutomorphism) S
        (EdgeCoherent protocolGraph Bool S) ∧
      FiniteReading.Effective
        (readAt protocolGraph Bool protocolSessionSwapAutomorphism) S
        (EdgeCoherent protocolGraph Bool S) ∧
      Nat.card (PermutationRestriction.PreservingChange protocolGraph Bool
        protocolSessionSwapAutomorphism) = 4 := by
  obtain ⟨S, determining, effective⟩ :=
    exists_effective_determining protocolGraph Bool protocolSessionSwapAutomorphism
  exact ⟨S, determining, effective,
    FinitePermutationExampleCardinality.protocol_preservingChange_count_sessionSwap⟩

end ProtocolExample

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationReadingEffectiveness

end AAT.AG.LocalSemanticReconstruction.FinitePermutationReadingEffectiveness
