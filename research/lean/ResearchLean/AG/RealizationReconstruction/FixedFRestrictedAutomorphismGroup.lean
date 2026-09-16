import ResearchLean.AG.RealizationReconstruction.FixedFAllAutomorphismGroup
import Mathlib.Algebra.Group.Subgroup.Map
import Formal.Util.AssertStandardAxioms

/-!
# Restriction to an independently supplied graph-automorphism subgroup

For an arbitrary independently supplied subgroup `H` of the full fixed-graph
automorphism group, the actual preserving-pair group is restricted by taking
the literal preimage of `H` under the visible projection.  The restricted
projection and the canonical visible-renaming section are then constructed
as group homomorphisms, and the section proves surjectivity.

The full graph-automorphism group also acts on the generated undirected
component quotient.  This action is descended from the actual vertex action:
edge reachability preservation is proved before quotienting, and multiplication
orientation is checked on quotient representatives.  Restriction to `H` is
obtained by composing with the subgroup inclusion.

The subgroup is never defined by existence of a presentation, and no kernel
exactness or torsor claim is made here.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFRestrictedAutomorphism

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Actual preserving pairs whose independently projected visible
automorphism belongs to the supplied subgroup `H`. -/
def FollowingGroup (H : Subgroup (FixedFGraphAutomorphism F)) :
    Subgroup (FixedFPreservingFollowingPair F K) :=
  H.comap FixedFPreservingFollowingPair.automorphismProjection

/-- Restrict the visible projection to the supplied subgroup. -/
def projection (H : Subgroup (FixedFGraphAutomorphism F)) :
    FollowingGroup (K := K) H →* H where
  toFun pair :=
    ⟨FixedFPreservingFollowingPair.automorphismProjection pair.1, pair.2⟩
  map_one' := Subtype.ext (map_one
    FixedFPreservingFollowingPair.automorphismProjection)
  map_mul' first second := Subtype.ext (map_mul
    FixedFPreservingFollowingPair.automorphismProjection first.1 second.1)

/-- The canonical visible-renaming section restricted to `H`. -/
def canonicalSection (H : Subgroup (FixedFGraphAutomorphism F)) :
    H →* FollowingGroup (K := K) H where
  toFun automorphism :=
    ⟨FixedFPreservingFollowingPair.visibleRenameSection automorphism.1, by
      change FixedFPreservingFollowingPair.automorphismProjection
          (FixedFPreservingFollowingPair.visibleRenameSection automorphism.1) ∈ H
      rw [FixedFPreservingFollowingPair.automorphismProjection_visibleRenameSection
        (K := K)]
      exact automorphism.2⟩
  map_one' := Subtype.ext (map_one
    FixedFPreservingFollowingPair.visibleRenameSection)
  map_mul' first second := Subtype.ext (map_mul
    FixedFPreservingFollowingPair.visibleRenameSection first.1 second.1)

/-- The restricted section is a right inverse of the restricted projection. -/
theorem projection_section
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    projection (K := K) H
      (canonicalSection (K := K) H automorphism) = automorphism := by
  apply Subtype.ext
  rfl

/-- Every supplied visible automorphism has its canonical identity-hidden
actual lift. -/
theorem projection_surjective
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.Surjective (projection (K := K) H) := by
  intro automorphism
  exact ⟨canonicalSection (K := K) H automorphism,
    projection_section (K := K) H automorphism⟩

end FixedFRestrictedAutomorphism

namespace FixedFGraphAutomorphism

variable {F : FixedFDirectedMultigraph}

/-- One directed edge step remains an edge step after the actual vertex and
edge renaming. -/
theorem map_directedEdgeStep
    (automorphism : FixedFGraphAutomorphism F)
    {first second : F.Vertex}
    (step : fixedFDirectedEdgeStep F first second) :
    fixedFDirectedEdgeStep F
      (automorphism.vertex first) (automorphism.vertex second) := by
  obtain ⟨namedEdge, sourceEquality, targetEquality⟩ := step
  refine ⟨automorphism.edge namedEdge, ?_, ?_⟩
  · rw [automorphism.source_rename, sourceEquality]
  · rw [automorphism.target_rename, targetEquality]

/-- The actual vertex action preserves all generated undirected
reachability. -/
theorem map_undirectedReachable
    (automorphism : FixedFGraphAutomorphism F)
    {first second : F.Vertex}
    (reachable : FixedFUndirectedReachable F first second) :
    FixedFUndirectedReachable F
      (automorphism.vertex first) (automorphism.vertex second) := by
  induction reachable with
  | rel first second step =>
      exact Relation.EqvGen.rel _ _
        (automorphism.map_directedEdgeStep step)
  | refl vertex =>
      exact Relation.EqvGen.refl _
  | symm first second relation inductionHypothesis =>
      exact Relation.EqvGen.symm _ _ inductionHypothesis
  | trans first second third firstRelation secondRelation
      firstInduction secondInduction =>
      exact Relation.EqvGen.trans _ _ _ firstInduction secondInduction

/-- Descend the actual vertex action to the generated component quotient. -/
def componentMap (automorphism : FixedFGraphAutomorphism F) :
    FixedFComponent F → FixedFComponent F :=
  Quotient.map automorphism.vertex
    (fun _ _ reachable =>
      automorphism.map_undirectedReachable reachable)

/-- The descended component map of one graph automorphism is a permutation. -/
def componentPerm (automorphism : FixedFGraphAutomorphism F) :
    Equiv.Perm (FixedFComponent F) where
  toFun := automorphism.componentMap
  invFun := (automorphism⁻¹).componentMap
  left_inv component := by
    refine Quotient.inductionOn component ?_
    intro vertex
    change fixedFComponentMk F
        (automorphism.vertex.symm (automorphism.vertex vertex)) =
      fixedFComponentMk F vertex
    rw [automorphism.vertex.symm_apply_apply]
  right_inv component := by
    refine Quotient.inductionOn component ?_
    intro vertex
    change fixedFComponentMk F
        (automorphism.vertex (automorphism.vertex.symm vertex)) =
      fixedFComponentMk F vertex
    rw [automorphism.vertex.apply_symm_apply]

/-- Component permutation evaluates on a represented source vertex by the
actual vertex action. -/
theorem componentPerm_mk
    (automorphism : FixedFGraphAutomorphism F) (vertex : F.Vertex) :
    automorphism.componentPerm (fixedFComponentMk F vertex) =
      fixedFComponentMk F (automorphism.vertex vertex) :=
  rfl

/-- The full graph-automorphism group acts on generated components with the
same multiplication orientation as its vertex action. -/
def componentAction :
    FixedFGraphAutomorphism F →* Equiv.Perm (FixedFComponent F) where
  toFun := componentPerm
  map_one' := by
    apply Equiv.ext
    intro component
    refine Quotient.inductionOn component ?_
    intro vertex
    rfl
  map_mul' first second := by
    apply Equiv.ext
    intro component
    refine Quotient.inductionOn component ?_
    intro vertex
    rfl

/-- Restrict the component action to any independently supplied visible
automorphism subgroup. -/
def restrictedComponentAction
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    H →* Equiv.Perm (FixedFComponent F) :=
  componentAction.comp H.subtype

end FixedFGraphAutomorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
