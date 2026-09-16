import ResearchLean.AG.RealizationReconstruction.FixedFRestrictedAutomorphismGroup
import Mathlib.Algebra.Group.Subgroup.Ker
import Formal.Util.AssertStandardAxioms

/-!
# Kernel identification for a restricted fixed-graph action

For an independently supplied visible subgroup `H`, a component-indexed
hidden permutation family constructs an actual operation-preserving following
pair with identity visible automorphism.  This construction is a group
homomorphism into the restricted actual group.

Conversely, an actual restricted pair with identity visible projection has a
fiber family constant on edges.  The already constructed quotient descent
recovers a component family, and factorization of the original state
equivalence proves that reconstructing from this family returns the original
pair.  Hence the literal range of the component-family homomorphism is exactly
the kernel of the independently defined restricted projection.

The kernel is not defined as a range, and no component family is stored in an
actual pair.  No torsor or further exact-sequence claim is made here.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFRestrictedKernelIdentification

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Component-indexed hidden permutation group. -/
abbrev ComponentGroup := FixedFComponentPermutationFamily F K

/-- Identity-visible actual pair constructed from one component-indexed
hidden permutation family. -/
def identityVisiblePair (family : ComponentGroup (F := F) (K := K)) :
    FixedFPreservingFollowingPair F K where
  automorphism := 1
  h :=
    { toFun := fun state =>
        (state.1, family (fixedFComponentMk F state.1) state.2)
      invFun := fun state =>
        (state.1, (family (fixedFComponentMk F state.1)).symm state.2)
      left_inv := by
        rintro ⟨vertex, hidden⟩
        simp
      right_inv := by
        rintro ⟨vertex, hidden⟩
        simp }
  observation _ _ := rfl
  preserves namedEdge hidden := by
    apply Prod.ext
    · rfl
    · exact congrArg
        (fun component : FixedFComponent F => family component hidden)
        (fixedFComponent_source_eq_target F namedEdge).symm

/-- Package the identity-visible pair in the preimage of any independently
supplied visible subgroup. -/
def restrictedIdentityVisiblePair
    (H : Subgroup (FixedFGraphAutomorphism F))
    (family : ComponentGroup (F := F) (K := K)) :
    FixedFRestrictedAutomorphism.FollowingGroup (K := K) H :=
  ⟨identityVisiblePair family, by
    change (1 : FixedFGraphAutomorphism F) ∈ H
    exact H.one_mem⟩

/-- Component families map homomorphically into the actual restricted group. -/
def componentKernelHom
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    ComponentGroup (F := F) (K := K) →*
      FixedFRestrictedAutomorphism.FollowingGroup (K := K) H where
  toFun := restrictedIdentityVisiblePair H
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

/-- Evaluation of the component construction exposes the authored family at
every represented vertex. -/
theorem componentKernelHom_fiberPerm
    (H : Subgroup (FixedFGraphAutomorphism F))
    (family : ComponentGroup (F := F) (K := K))
    (vertex : F.Vertex) :
    ((componentKernelHom (K := K) H family).1.fiberPerm vertex) =
      family (fixedFComponentMk F vertex) := by
  apply Equiv.ext
  intro hidden
  rfl

/-- The component-family homomorphism is faithful. -/
theorem componentKernelHom_injective
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.Injective (componentKernelHom (K := K) H) := by
  intro first second equality
  funext component
  refine Quotient.inductionOn component ?_
  intro vertex
  apply Equiv.ext
  intro hidden
  have evaluated := congrArg
    (fun pair : FixedFRestrictedAutomorphism.FollowingGroup (K := K) H =>
      (pair.1.h (vertex, hidden)).2)
    equality
  exact evaluated

/-- Every constructed component-family element has identity visible
projection. -/
theorem projection_componentKernelHom
    (H : Subgroup (FixedFGraphAutomorphism F))
    (family : ComponentGroup (F := F) (K := K)) :
    FixedFRestrictedAutomorphism.projection (K := K) H
        (componentKernelHom (K := K) H family) = 1 := by
  apply Subtype.ext
  rfl

/-- Read the component family of an actual preserving pair by descending its
constructed edge-constant fiber family. -/
def componentFamilyOfPair (pair : FixedFPreservingFollowingPair F K) :
    ComponentGroup (F := F) (K := K) :=
  FixedFEdgeConstantPermutationFamily.descendToComponents
    { perm := pair.fiberPerm
      edge_constant :=
        (pair.change.preservesNamedOperations_iff).1 pair.change_preserves }

/-- On a represented component, extraction returns the actual constructed
fiber permutation. -/
theorem componentFamilyOfPair_mk
    (pair : FixedFPreservingFollowingPair F K) (vertex : F.Vertex) :
    componentFamilyOfPair pair (fixedFComponentMk F vertex) =
      pair.fiberPerm vertex :=
  rfl

/-- The actual range of component families is exactly the kernel of the
restricted visible projection. -/
theorem range_componentKernelHom_eq_ker_projection
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    MonoidHom.range (componentKernelHom (K := K) H) =
      MonoidHom.ker (FixedFRestrictedAutomorphism.projection (K := K) H) := by
  apply le_antisymm
  · rintro actual ⟨family, rfl⟩
    rw [MonoidHom.mem_ker]
    exact projection_componentKernelHom (K := K) H family
  · intro actual kernelMembership
    rw [MonoidHom.mem_ker] at kernelMembership
    have automorphismEquality : actual.1.automorphism = 1 := by
      exact congrArg Subtype.val kernelMembership
    let family : ComponentGroup (F := F) (K := K) :=
      componentFamilyOfPair actual.1
    refine ⟨family, ?_⟩
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext
    · exact automorphismEquality.symm
    · apply Equiv.ext
      rintro ⟨vertex, hidden⟩
      change (vertex, family (fixedFComponentMk F vertex) hidden) =
        actual.1.h (vertex, hidden)
      symm
      calc
        actual.1.h (vertex, hidden) =
            (actual.1.automorphism.vertex vertex,
              actual.1.fiberPerm vertex hidden) :=
          actual.1.change.factorization vertex hidden
        _ = (vertex, family (fixedFComponentMk F vertex) hidden) := by
          rw [automorphismEquality]
          rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFRestrictedKernelIdentification

end AAT.AG.RealizationReconstruction
