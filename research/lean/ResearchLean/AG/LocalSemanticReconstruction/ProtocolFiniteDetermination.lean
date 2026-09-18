import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolConnection
import Formal.Util.AssertStandardAxioms

/-!
# Finite determination of protocol invertible changes

For the protocol realization carried by a fixed directed multigraph, an
invertible change has one actual hidden-state permutation at every vertex and
the generator squares make that family constant along every named edge.  A
finite retained vertex set therefore reads the protocol change by its actual
`stateEquiv` components.

This module connects that reading to the common `FiniteReading` surface.  The
separation criterion is exactly that the retained vertices meet every full
component; extension of every edge-coherent raw table is exactly preservation
of full connectivity inside the induced graph.  Effectiveness is kept
separate and transports the existing executable preserving-change algorithm
back to the actual `ProtocolInvertibleChange` type.

Implementation notes:

* Coherence is equality along the actual retained named edges.  Defining it by
  existence of a global protocol change was rejected as circular.
* The output of the executable path is converted through the accepted
  protocol/fixed-graph equivalence; returning only a fixed-graph change was
  rejected because the G-124(E2) conclusion is about protocol changes.
* Vertex tables are not identified with component families.  The two exact
  graph criteria and the quotient component maps mediate between them.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFProtocolConnection

universe u

namespace ProtocolFiniteDetermination

variable {F : FixedFDirectedMultigraph.{u, u}}
  [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
  {K : Type u} [Fintype K] [DecidableEq K]
  {automorphism : FixedFGraphAutomorphism F}

/-- Read an actual protocol invertible change at one control vertex. -/
def readProtocolChangeAt
    (change : ProtocolInvertibleChange F K automorphism)
    (vertex : F.Vertex) : Equiv.Perm K :=
  change.stateEquiv vertex

omit [DecidableEq F.Vertex] [DecidableEq K] in
/-- Forgetting protocol vocabulary sends the point reading to the accepted
fixed-graph component-permutation reading at the same vertex. -/
@[simp] theorem readProtocolChangeAt_eq_preservingReading
    (change : ProtocolInvertibleChange F K automorphism)
    (vertex : F.Vertex) :
    readProtocolChangeAt change vertex =
      FiniteEffectiveness.readPreservingChangeAt F K automorphism
        (ProtocolInvertibleChange.equivPreservingFollowingChanges change)
        vertex := by
  change change.stateEquiv vertex =
    change.toFollowingStateChange.fiberPerm vertex
  exact congrFun
    (FixedFFollowingStateChange.fiberPerm_ofFamily
      change.hiddenPermutation) vertex |>.symm

/-- The explicit finite reading set supplied by a retained vertex predicate. -/
abbrev readingVertices (F : FixedFDirectedMultigraph)
    [Fintype F.Vertex] (S : F.Vertex → Prop) [DecidablePred S] :
    Finset F.Vertex :=
  FiniteEffectiveness.retainedVertices F S

/-- Local protocol-table coherence is the existing actual named-edge
coherence predicate on the retained graph. -/
abbrev TableCoherent
    (F : FixedFDirectedMultigraph) [Fintype F.Vertex]
    (S : F.Vertex → Prop) [DecidablePred S]
    (K : Type*)
    (table : {vertex // vertex ∈ readingVertices F S} → Equiv.Perm K) : Prop :=
  FiniteEffectiveness.PermutationTableCoherent F S K table

/-! ### Nonvacuity of retained-edge coherence -/

/-- A single named edge between two Boolean vertices, used only to expose
both outcomes of the local coherence predicate. -/
def coherenceWitnessGraph : FixedFDirectedMultigraph where
  Vertex := Bool
  Edge := Unit
  source := fun _ => false
  target := fun _ => true

/-- The witness graph has the finite Boolean vertex enumeration. -/
instance : Fintype coherenceWitnessGraph.Vertex := by
  change Fintype Bool
  infer_instance

/-- Vertex equality on the witness graph is the Boolean equality decision. -/
instance : DecidableEq coherenceWitnessGraph.Vertex := by
  change DecidableEq Bool
  infer_instance

/-- The constant identity table is coherent across the witness edge. -/
def coherentIdentityTable :
    {vertex // vertex ∈ readingVertices coherenceWitnessGraph (fun _ => True)} →
      Equiv.Perm Bool :=
  fun _ => 1

/-- The constant identity table supplies a positive coherence instance. -/
theorem coherentIdentityTable_coherent :
    TableCoherent coherenceWitnessGraph (fun _ => True) Bool
      coherentIdentityTable := by
  intro edge
  rfl

/-- Assign identity at the source and negation at the target of the witness
edge.  This is an independently incoherent raw table. -/
def incoherentSplitTable :
    {vertex // vertex ∈ readingVertices coherenceWitnessGraph (fun _ => True)} →
      Equiv.Perm Bool :=
  fun vertex => if vertex.1 = true then Equiv.swap false true else 1

/-- The split source/target table supplies a negative coherence instance. -/
theorem incoherentSplitTable_not_coherent :
    ¬ TableCoherent coherenceWitnessGraph (fun _ => True) Bool
      incoherentSplitTable := by
  intro coherent
  have edgeEquality := coherent
    (⟨(), ⟨True.intro, True.intro⟩⟩ :
      (InducedComponent.graph coherenceWitnessGraph (fun _ => True)).Edge)
  have valueEquality := Equiv.congr_fun edgeEquality false
  simp [FiniteEffectiveness.toPermutationVertexTable,
    incoherentSplitTable, InducedComponent.graph, coherenceWitnessGraph]
    at valueEquality

omit [DecidableEq F.Vertex] [DecidableEq K] in
/-- G-124(D/E2), constructive separation direction: the retained protocol
point readings separate actual protocol changes when the supplied graph
predicate meets every full component.  Unlike the converse below, this API
does not require a nontrivial hidden carrier. -/
theorem separates_of_meetsEveryFullComponent
    (S : F.Vertex → Prop) [DecidablePred S]
    (meets : InducedComponent.MeetsEveryFullComponent F S) :
    FiniteReading.Separates
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F S) := by
  intro first second tableEquality
  apply ProtocolInvertibleChange.equivPreservingFollowingChanges.injective
  apply FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies.injective
  funext component
  refine Quotient.inductionOn component ?_
  intro vertex
  obtain ⟨retained, reachable⟩ := meets vertex
  have componentEquality :
      fixedFComponentMk F retained.1 = fixedFComponentMk F vertex :=
    (fixedFComponentMk_eq_iff F retained.1 vertex).mpr reachable
  change
    FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
        (ProtocolInvertibleChange.equivPreservingFollowingChanges first)
        (fixedFComponentMk F vertex) =
      FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies
        (ProtocolInvertibleChange.equivPreservingFollowingChanges second)
        (fixedFComponentMk F vertex)
  rw [← componentEquality]
  have pointEquality := congrFun tableEquality
    ⟨retained.1,
      (FiniteEffectiveness.mem_retainedVertices F S retained.1).2 retained.2⟩
  simpa only [FiniteReading.restrict,
    readProtocolChangeAt_eq_preservingReading] using pointEquality

omit [DecidableEq F.Vertex] [DecidableEq K] in
/-- G-124(D/E2), exact separation criterion.  For the target's `|K| ≥ 2`
boundary, represented here by `[Nontrivial K]`, separation of the actual
protocol readings is equivalent to meeting every full component. -/
theorem separates_iff_meetsEveryFullComponent
    [Nontrivial K]
    (S : F.Vertex → Prop) [DecidablePred S] :
    FiniteReading.Separates
        (readProtocolChangeAt (F := F) (K := K)
          (automorphism := automorphism))
        (readingVertices F S) ↔
      InducedComponent.MeetsEveryFullComponent F S := by
  constructor
  · intro separates
    apply (PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent
      (K := K) F S automorphism).mp
    intro first second familyEquality
    let firstProtocol :=
      ProtocolInvertibleChange.equivPreservingFollowingChanges.symm first
    let secondProtocol :=
      ProtocolInvertibleChange.equivPreservingFollowingChanges.symm second
    have tableEquality :
        FiniteReading.restrict
            (readProtocolChangeAt (F := F) (K := K)
              (automorphism := automorphism))
            (readingVertices F S) firstProtocol =
          FiniteReading.restrict
            (readProtocolChangeAt (F := F) (K := K)
              (automorphism := automorphism))
            (readingVertices F S) secondProtocol := by
      funext vertex
      have atComponent := congrFun familyEquality
        (fixedFComponentMk (InducedComponent.graph F S)
          ⟨vertex.1,
            (FiniteEffectiveness.mem_retainedVertices F S vertex.1).1 vertex.2⟩)
      simpa [PermutationRestriction.restrictPreservingChange,
        PermutationRestriction.restrict, ComponentRestriction.precompose,
        FiniteReading.restrict, firstProtocol, secondProtocol] using atComponent
    have protocolEquality := separates tableEquality
    exact ProtocolInvertibleChange.equivPreservingFollowingChanges.symm.injective
      protocolEquality
  · exact separates_of_meetsEveryFullComponent S

/-- G-124(D/E2), constructive extension direction: every table coherent on
the actual retained named edges extends to an actual protocol change when the
supplied graph predicate retains full connectivity. -/
theorem extends_of_retainsFullConnectivity
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.Extends
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F S)
      (TableCoherent F S K) := by
  intro table coherent
  let vertexTable :=
    FiniteEffectiveness.toPermutationVertexTable F S K table
  let preserving :=
    FinitePermutationExtension.extendPreservingChange F S K automorphism
      ⟨vertexTable, coherent⟩
  let protocol :=
    ProtocolInvertibleChange.equivPreservingFollowingChanges.symm preserving
  refine ⟨protocol, ?_⟩
  funext vertex
  have readback :=
    FinitePermutationExtension.extendPreservingChange_classification_mk
      F S K automorphism ⟨vertexTable, coherent⟩ retains
        ⟨vertex.1,
          (FiniteEffectiveness.mem_retainedVertices F S vertex.1).1 vertex.2⟩
  simpa [FiniteReading.restrict, protocol, preserving, vertexTable] using readback

/-- G-124(D/E2), exact extension criterion.  For `[Nontrivial K]`, extension
of every independently edge-coherent raw table is equivalent to retention of
full connectivity by the induced graph. -/
theorem extends_iff_retainsFullConnectivity
    [Nontrivial K]
    (S : F.Vertex → Prop) [DecidablePred S] :
    FiniteReading.Extends
        (readProtocolChangeAt (F := F) (K := K)
          (automorphism := automorphism))
        (readingVertices F S)
        (TableCoherent F S K) ↔
      InducedComponent.RetainsFullConnectivity F S := by
  constructor
  · intro hextends
    apply (PermutationRestriction.restrictPreservingChange_surjective_iff_retainsFullConnectivity
      (K := K) F S automorphism).mp
    intro family
    let table : {vertex // vertex ∈ readingVertices F S} → Equiv.Perm K :=
      fun vertex => family
        (fixedFComponentMk (InducedComponent.graph F S)
          ⟨vertex.1,
            (FiniteEffectiveness.mem_retainedVertices F S vertex.1).1 vertex.2⟩)
    have coherent : TableCoherent F S K table := by
      intro edge
      exact congrArg family
        (fixedFComponent_source_eq_target
          (InducedComponent.graph F S) edge)
    obtain ⟨protocol, readback⟩ := hextends table coherent
    refine ⟨ProtocolInvertibleChange.equivPreservingFollowingChanges protocol, ?_⟩
    funext component
    refine Quotient.inductionOn component ?_
    intro vertex
    have atVertex := congrFun readback
      ⟨vertex.1,
        (FiniteEffectiveness.mem_retainedVertices F S vertex.1).2 vertex.2⟩
    simpa [PermutationRestriction.restrictPreservingChange,
      PermutationRestriction.restrict, ComponentRestriction.precompose,
      FiniteReading.restrict, table] using atVertex
  · exact extends_of_retainsFullConnectivity S

/-- G-124(D/E2), determining-set API: the separately supplied component
meeting and induced-connectivity premises combine the already independent
separation and extension results for actual protocol invertible changes. -/
theorem determining_of_componentCriteria
    (S : F.Vertex → Prop) [DecidablePred S]
    (meets : InducedComponent.MeetsEveryFullComponent F S)
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.Determining
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F S)
      (TableCoherent F S K) :=
  ⟨separates_of_meetsEveryFullComponent S meets,
    extends_of_retainsFullConnectivity S retains⟩

/-- Choosing one representative vertex from every full component gives an
actual protocol determining set.  The decidability input only presents that
chosen predicate as the explicit finite `Finset` required by `FiniteReading`;
the two graph criteria are supplied by the representative construction. -/
theorem representativeVertices_determining
    [DecidablePred (InducedComponent.RepresentativeVertex F)] :
    FiniteReading.Determining
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F (InducedComponent.RepresentativeVertex F))
      (TableCoherent F (InducedComponent.RepresentativeVertex F) K) :=
  determining_of_componentCriteria
    (InducedComponent.RepresentativeVertex F)
    (InducedComponent.representativeVertex_meetsEveryFullComponent F)
    (InducedComponent.representativeVertex_retainsFullConnectivity F)

/-- G-124(D/E2), effectiveness API under the supplied retained-connectivity
premise: decide actual retained-edge coherence, reject exactly incoherent
tables, and return the corresponding actual protocol change with exact
pointwise readback. -/
def effectivenessProgram
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.EffectivenessProgram
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F S)
      (TableCoherent F S K) := by
  let base := FiniteEffectiveness.permutationEffectivenessProgram
    F S K automorphism retains
  exact
    { coherenceTest := base.coherenceTest
      coherenceTest_eq_true_iff := base.coherenceTest_eq_true_iff
      extend? := fun table =>
        Option.map
          ProtocolInvertibleChange.equivPreservingFollowingChanges.symm
          (base.extend? table)
      extend_eq_none_iff := by
        intro table
        cases result : base.extend? table with
        | none =>
            simpa [result] using base.extend_eq_none_iff table
        | some preserving =>
            have coherent : TableCoherent F S K table := by
              by_contra notCoherent
              have impossible : (none : Option _) = some preserving :=
                ((base.extend_eq_none_iff table).2 notCoherent |>.symm.trans result)
              cases impossible
            simp [coherent]
      restrict_eq_of_extend_eq_some := by
        intro table protocol success
        cases result : base.extend? table with
        | none => simp [result] at success
        | some preserving =>
            simp only [result, Option.map_some, Option.some.injEq] at success
            subst protocol
            have readback := base.restrict_eq_of_extend_eq_some
              table preserving result
            funext vertex
            simpa only [FiniteReading.restrict,
              readProtocolChangeAt_eq_preservingReading,
              Equiv.apply_symm_apply] using congrFun readback vertex }

/-- The executable protocol program supplies the third common finite-reading
property independently of separation and extension. -/
theorem effective_of_retainsFullConnectivity
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S) :
    FiniteReading.Effective
      (readProtocolChangeAt (F := F) (K := K)
        (automorphism := automorphism))
      (readingVertices F S)
      (TableCoherent F S K) :=
  ⟨effectivenessProgram S retains⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination

end ProtocolFiniteDetermination

end AAT.AG.LocalSemanticReconstruction
