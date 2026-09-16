import ResearchLean.AG.RealizationReconstruction.FixedFProtocolConnection
import ResearchLean.AG.RealizationReconstruction.FixedFSplitExactSequenceAndTorsor
import Formal.Util.AssertStandardAxioms

/-!
# The all-H independent protocol change group

For an arbitrary independently supplied subgroup `H` of the automorphisms of
a fixed directed multigraph, this file assembles all independently defined
protocol changes above every `u : H`.  Multiplication and inversion are
constructed on the protocol state equivalences and their actual named-edge
squares.  The visible projection has the identity-hidden protocol change as
a homomorphic section.

The resulting group is genuinely equivalent to the fixed-F preserving
following group.  The equivalence retains the original operation rename and
state adapter, commutes with projection and section, and restricts to literal
kernels and every literal projection fiber.  The protocol fibers carry their
own free and transitive right-kernel action before any transport.
-/

namespace AAT.AG.RealizationReconstruction

universe u

namespace FixedFProtocolGroupConnection

open CategoryTheory
open FixedFProtocolConnection

variable {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
  {K : Type u} [Finite K]

/-- The independent CS-side carrier over every visible automorphism in `H`.
Its fields are precisely the semantic state equivalences and the squares for
every original typed operation name; no fixed-F change is stored as input. -/
@[ext]
structure ProtocolChangeGroup
    (H : Subgroup (FixedFGraphAutomorphism F)) where
  visible : H
  stateEquiv : F.Vertex → Equiv.Perm K
  edge_naturality : ∀ {source target : F.Vertex}
      (edge : (schema F).Edge source target)
      (state : (realization F K).State source),
    stateEquiv target ((realization F K).edgeAction edge state) =
      (realization F K).edgeAction (renameTypedEdge visible.1 edge)
        (stateEquiv source state)
  observation_naturality : ∀ vertex state,
    (realization F K).observe (visible.1.vertex vertex)
        (stateEquiv vertex state) =
      (realization F K).observe vertex state

namespace ProtocolChangeGroup

variable {H : Subgroup (FixedFGraphAutomorphism F)}

/-- Recover the independently defined fixed-automorphism protocol change. -/
def toProtocolInvertibleChange (change : ProtocolChangeGroup (K := K) H) :
    ProtocolInvertibleChange F K change.visible.1 where
  stateEquiv := change.stateEquiv
  edge_naturality := change.edge_naturality
  observation_naturality := change.observation_naturality

/-- The authored generator square says exactly that hidden permutations are
constant along every original named edge. -/
theorem stateEquiv_edge_constant
    (change : ProtocolChangeGroup (K := K) H)
    {source target : F.Vertex}
    (edge : (schema F).Edge source target) :
    change.stateEquiv target = change.stateEquiv source := by
  apply Equiv.ext
  intro state
  simpa only [realization_edgeAction, id_eq] using
    change.edge_naturality edge state

instance : One (ProtocolChangeGroup (K := K) H) where
  one :=
    { visible := 1
      stateEquiv := fun _ => 1
      edge_naturality := fun _ _ => rfl
      observation_naturality := fun _ _ => rfl }

instance : Mul (ProtocolChangeGroup (K := K) H) where
  mul first second :=
    { visible := first.visible * second.visible
      stateEquiv := fun vertex =>
        first.stateEquiv (second.visible.1.vertex vertex) *
          second.stateEquiv vertex
      edge_naturality := by
        intro source target edge state
        change first.stateEquiv (second.visible.1.vertex target)
              (second.stateEquiv target state) =
          first.stateEquiv (second.visible.1.vertex source)
              (second.stateEquiv source state)
        rw [second.stateEquiv_edge_constant edge,
          first.stateEquiv_edge_constant
            (renameTypedEdge second.visible.1 edge)]
      observation_naturality := fun _ _ => Subsingleton.elim _ _ }

instance : Inv (ProtocolChangeGroup (K := K) H) where
  inv change :=
    { visible := change.visible⁻¹
      stateEquiv := fun vertex =>
        (change.stateEquiv (change.visible.1.vertex.symm vertex)).symm
      edge_naturality := by
        intro source target edge state
        have constant :
            change.stateEquiv (change.visible.1.vertex.symm target) =
              change.stateEquiv (change.visible.1.vertex.symm source) := by
          simpa using change.stateEquiv_edge_constant
            (renameTypedEdge change.visible.1⁻¹ edge)
        exact congrFun
          (congrArg (fun permutation : Equiv.Perm K => permutation.symm)
            constant) state
      observation_naturality := fun _ _ => Subsingleton.elim _ _ }

instance : Group (ProtocolChangeGroup (K := K) H) where
  mul_assoc first second third := by
    apply ProtocolChangeGroup.ext
    · exact mul_assoc _ _ _
    · funext vertex
      exact mul_assoc _ _ _
  one_mul change := by
    apply ProtocolChangeGroup.ext
    · exact one_mul _
    · funext vertex
      exact one_mul _
  mul_one change := by
    apply ProtocolChangeGroup.ext
    · exact mul_one _
    · funext vertex
      exact mul_one _
  inv_mul_cancel change := by
    apply ProtocolChangeGroup.ext
    · exact inv_mul_cancel _
    · funext vertex
      change (change.stateEquiv
          (change.visible.1.vertex.symm
            (change.visible.1.vertex vertex))).symm *
          change.stateEquiv vertex = 1
      rw [change.visible.1.vertex.symm_apply_apply]
      exact inv_mul_cancel _

/-- Projection to the complete independently supplied visible subgroup. -/
def projection : ProtocolChangeGroup (K := K) H →* H where
  toFun := visible
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The identity-hidden protocol change over every allowed visible
automorphism, including its actual operation-name rename. -/
def canonicalSection : H →* ProtocolChangeGroup (K := K) H where
  toFun visible :=
    { visible := visible
      stateEquiv := fun _ => 1
      edge_naturality := fun _ _ => rfl
      observation_naturality := fun _ _ => rfl }
  map_one' := by
    apply ProtocolChangeGroup.ext <;> rfl
  map_mul' first second := by
    apply ProtocolChangeGroup.ext
    · rfl
    · funext vertex
      simp

theorem projection_section (visible : H) :
    projection (K := K) (canonicalSection (K := K) visible) = visible :=
  rfl

/-- Assemble an independent protocol change into the actual preserving
fixed-F pair while retaining its complete state map and every original
operation name. -/
def toFollowingGroup :
    ProtocolChangeGroup (K := K) H →*
      FixedFRestrictedAutomorphism.FollowingGroup (K := K) H where
  toFun change :=
    ⟨{ automorphism := change.visible.1
       h := change.toProtocolInvertibleChange.toFollowingStateChange.h
       observation := change.toProtocolInvertibleChange.toFollowingStateChange.observation
       preserves := change.toProtocolInvertibleChange.toFollowingStateChange_preserves },
      change.visible.2⟩
  map_one' := by
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨vertex, hidden⟩
      rfl
  map_mul' first second := by
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext
    · rfl
    · apply Equiv.ext
      rintro ⟨vertex, hidden⟩
      rfl

theorem toFollowingGroup_injective :
    Function.Injective (toFollowingGroup (K := K) (H := H)) := by
  intro first second equality
  have pairEquality :
      (toFollowingGroup (K := K) first).1 =
        (toFollowingGroup (K := K) second).1 :=
    congrArg Subtype.val equality
  apply ProtocolChangeGroup.ext
  · apply Subtype.ext
    exact congrArg FixedFPreservingFollowingPair.automorphism pairEquality
  · funext vertex
    apply Equiv.ext
    intro hidden
    have stateEquality := congrArg FixedFPreservingFollowingPair.h pairEquality
    exact congrArg Prod.snd
      (congrArg (fun stateMap : (F.Vertex × K) ≃ (F.Vertex × K) =>
        stateMap (vertex, hidden)) stateEquality)

theorem toFollowingGroup_surjective :
    Function.Surjective (toFollowingGroup (K := K) (H := H)) := by
  intro actual
  let protocol : ProtocolInvertibleChange F K actual.1.automorphism :=
    ProtocolInvertibleChange.ofFollowingStateChange
      ⟨actual.1.change, actual.1.change_preserves⟩
  let independent : ProtocolChangeGroup (K := K) H :=
    { visible := ⟨actual.1.automorphism, actual.2⟩
      stateEquiv := protocol.stateEquiv
      edge_naturality := protocol.edge_naturality
      observation_naturality := protocol.observation_naturality }
  refine ⟨independent, ?_⟩
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · rfl
  · change protocol.toFollowingStateChange.h = actual.1.h
    apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    exact (actual.1.change.factorization vertex hidden).symm

/-- Group-level equivalence between the independently defined protocol group
and the actual fixed-F preserving following group over all of `H`. -/
noncomputable def mulEquivFollowingGroup :
    ProtocolChangeGroup (K := K) H ≃*
      FixedFRestrictedAutomorphism.FollowingGroup (K := K) H :=
  MulEquiv.ofBijective (toFollowingGroup (K := K) (H := H))
    ⟨toFollowingGroup_injective, toFollowingGroup_surjective⟩

/-- The group equivalence commutes literally with visible projection. -/
theorem projection_compatibility (change : ProtocolChangeGroup (K := K) H) :
    FixedFRestrictedAutomorphism.projection (K := K) H
        (mulEquivFollowingGroup change) = projection change := by
  apply Subtype.ext
  rfl

/-- The group equivalence carries the protocol identity-hidden section to
the fixed-F canonical section. -/
theorem section_compatibility (visible : H) :
    mulEquivFollowingGroup (K := K)
        (canonicalSection (K := K) visible) =
      FixedFRestrictedAutomorphism.canonicalSection (K := K) H visible := by
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · rfl
  · apply Equiv.ext
    rintro ⟨vertex, hidden⟩
    rfl

/-- The same equivalence restricts to the literal projection kernels. -/
noncomputable def kernelMulEquiv :
    MonoidHom.ker (projection (K := K) (H := H)) ≃*
      MonoidHom.ker
        (FixedFRestrictedAutomorphism.projection (K := K) H) where
  toFun kernelElement :=
    ⟨mulEquivFollowingGroup kernelElement.1, by
      rw [MonoidHom.mem_ker, projection_compatibility,
        MonoidHom.mem_ker.mp kernelElement.property]⟩
  invFun kernelElement :=
    ⟨mulEquivFollowingGroup.symm kernelElement.1, by
      rw [MonoidHom.mem_ker]
      calc
        projection (mulEquivFollowingGroup.symm kernelElement.1) =
            FixedFRestrictedAutomorphism.projection (K := K) H
              (mulEquivFollowingGroup
                (mulEquivFollowingGroup.symm kernelElement.1)) :=
          (projection_compatibility
            (mulEquivFollowingGroup.symm kernelElement.1)).symm
        _ = FixedFRestrictedAutomorphism.projection (K := K) H
              kernelElement.1 := by
          rw [mulEquivFollowingGroup.apply_symm_apply]
        _ = 1 := MonoidHom.mem_ker.mp kernelElement.property⟩
  left_inv kernelElement := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.symm_apply_apply kernelElement.1
  right_inv kernelElement := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.apply_symm_apply kernelElement.1
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul mulEquivFollowingGroup first.1 second.1

/-- Literal protocol projection fiber over one visible automorphism. -/
abbrev ProjectionFiber (visible : H) :=
  { change : ProtocolChangeGroup (K := K) H // projection change = visible }

/-- Right multiplication by the literal protocol projection kernel. -/
instance projectionFiberSMul (visible : H) :
    SMul (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ
      (ProjectionFiber (K := K) visible) where
  smul kernelElement change :=
    ⟨change.1 * (MulOpposite.unop kernelElement).1, by
      rw [map_mul, change.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelElement).property,
        mul_one]⟩

/-- The literal protocol-kernel action obeys the group action laws. -/
instance projectionFiberMulAction (visible : H) :
    MulAction (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ
      (ProjectionFiber (K := K) visible) where
  one_smul change := by
    apply Subtype.ext
    exact mul_one change.1
  mul_smul first second change := by
    apply Subtype.ext
    exact (mul_assoc change.1
      (MulOpposite.unop second).1 (MulOpposite.unop first).1).symm

/-- The literal kernel action on every independent protocol fiber is free. -/
theorem projectionFiber_action_free (visible : H)
    (change : ProjectionFiber (K := K) visible) :
    Function.Injective
      (fun kernelElement :
          (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ =>
        kernelElement • change) := by
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have values := congrArg
    (fun point : ProjectionFiber (K := K) visible => point.1) equality
  exact mul_left_cancel values

/-- The literal kernel action on every independent protocol fiber is
transitive. -/
theorem projectionFiber_action_transitive (visible : H)
    (first second : ProjectionFiber (K := K) visible) :
    ∃ kernelElement :
        (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ,
      kernelElement • first = second := by
  let displacement : ProtocolChangeGroup (K := K) H :=
    first.1⁻¹ * second.1
  have displacement_mem : displacement ∈
      MonoidHom.ker (projection (K := K) (H := H)) := by
    rw [MonoidHom.mem_ker]
    change projection (K := K) (first.1⁻¹ * second.1) = 1
    rw [map_mul, map_inv, first.property, second.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, displacement_mem⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Between two protocol changes over the same visible automorphism there is
a unique literal kernel displacement. -/
theorem projectionFiber_existsUnique_smul_eq (visible : H)
    (first second : ProjectionFiber (K := K) visible) :
    ∃! kernelElement :
        (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ,
      kernelElement • first = second := by
  rcases projectionFiber_action_transitive visible first second with
    ⟨kernelElement, equality⟩
  refine ⟨kernelElement, equality, ?_⟩
  intro other otherEquality
  exact projectionFiber_action_free visible first
    (otherEquality.trans equality.symm)

/-- Every literal protocol projection fiber is identified with the same
fixed-F preserving-change fiber by the group equivalence. -/
noncomputable def projectionFiberEquiv (visible : H) :
    ProjectionFiber (K := K) visible ≃
      FixedFSplitExactSequenceAndTorsor.ProjectionFiber
        (K := K) H visible where
  toFun change :=
    ⟨mulEquivFollowingGroup change.1, by
      rw [projection_compatibility, change.2]⟩
  invFun actual :=
    ⟨mulEquivFollowingGroup.symm actual.1, by
      calc
        projection (mulEquivFollowingGroup.symm actual.1) =
            FixedFRestrictedAutomorphism.projection (K := K) H
              (mulEquivFollowingGroup
                (mulEquivFollowingGroup.symm actual.1)) :=
          (projection_compatibility
            (mulEquivFollowingGroup.symm actual.1)).symm
        _ = FixedFRestrictedAutomorphism.projection (K := K) H actual.1 := by
          rw [mulEquivFollowingGroup.apply_symm_apply]
        _ = visible := actual.2⟩
  left_inv change := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.symm_apply_apply change.1
  right_inv actual := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.apply_symm_apply actual.1

/-- Every protocol fiber is classified directly by the component-indexed
hidden permutation group, using the same construction as the fixed-F fiber. -/
noncomputable def componentGroupEquivProjectionFiber (visible : H) :
    FixedFSplitExactSequenceAndTorsor.ComponentGroup (F := F) (K := K) ≃
      ProjectionFiber (K := K) visible :=
  (FixedFSplitExactSequenceAndTorsor.componentGroupEquivProjectionFiber
    (K := K) H visible).trans (projectionFiberEquiv visible).symm

/-- The fiber equivalence intertwines the two literal right-kernel actions. -/
theorem projectionFiberEquiv_smul (visible : H)
    (kernelElement :
      (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ)
    (change : ProjectionFiber (K := K) visible) :
    projectionFiberEquiv visible (kernelElement • change) =
      MulOpposite.op
          (kernelMulEquiv (MulOpposite.unop kernelElement)) •
        projectionFiberEquiv visible change := by
  apply Subtype.ext
  change mulEquivFollowingGroup
      (change.1 * (MulOpposite.unop kernelElement).1) =
    mulEquivFollowingGroup change.1 *
      mulEquivFollowingGroup (MulOpposite.unop kernelElement).1
  exact map_mul mulEquivFollowingGroup change.1
    (MulOpposite.unop kernelElement).1

/-- The protocol group map retains every original operation name and hidden
state adapter, rather than merely identifying abstract group elements. -/
theorem operationMap_compatibility
    (change : ProtocolChangeGroup (K := K) H)
    (namedEdge : F.Edge) (hidden : K) :
    ((renameTypedEdge change.visible.1 (typedEdge F namedEdge)).1,
      change.stateEquiv (F.source namedEdge) hidden) =
      (mulEquivFollowingGroup change).1.change.operationMap
        (namedEdge, hidden) := by
  apply Prod.ext <;> rfl

/-- Each all-H group element preserves every finite named execution path,
with every original operation name renamed by its visible automorphism. -/
theorem path_naturality
    (change : ProtocolChangeGroup (K := K) H)
    {source target : F.Vertex} (path : Quiver.Path source target)
    (state : (realization F K).State source) :
    change.stateEquiv target ((realization F K).pathAction path state) =
      (realization F K).pathAction
        (renamePath change.visible.1 path)
        (change.stateEquiv source state) :=
  change.toProtocolInvertibleChange.path_naturality path state

/-- Generator preservation for an all-H group element descends to every
morphism of the quotient execution category. -/
theorem execution_naturality
    (change : ProtocolChangeGroup (K := K) H)
    {source target : (schema F).ExecutionCategory}
    (execution : source ⟶ target)
    (state : (realization F K).toFunctor.obj source) :
    change.stateEquiv target.as
        ((realization F K).toFunctor.map execution state) =
      (realization F K).toFunctor.map
          ((renameExecutionFunctor change.visible.1).map execution)
        (change.stateEquiv source.as state) :=
  change.toProtocolInvertibleChange.execution_naturality execution state

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end ProtocolChangeGroup

end FixedFProtocolGroupConnection

end AAT.AG.RealizationReconstruction
