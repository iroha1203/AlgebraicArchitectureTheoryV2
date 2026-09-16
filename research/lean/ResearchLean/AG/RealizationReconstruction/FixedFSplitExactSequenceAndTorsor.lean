import ResearchLean.AG.RealizationReconstruction.FixedFRestrictedKernelIdentification
import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction
import Formal.Util.AssertStandardAxioms

/-!
# The split exact sequence and its explicit following-change fibers

For an arbitrary independently supplied visible subgroup `H`, the concrete
component-family homomorphism, the actual preserving-pair group, and the
visible projection form the short exact sequence in G-123(F1).  The already
constructed identity-hidden visible renaming is a homomorphic section.

For every `u : H`, the full fiber of the actual projection is explicitly
equivalent to the component-indexed hidden permutation group.  The forward
map multiplies a hidden component family by the canonical lift of `u`; the
inverse removes that lift and reads the resulting actual kernel element back
on the generated component quotient.  Thus neither existence of a following
change nor a chosen lift is included in the input subgroup or fiber.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFSplitExactSequenceAndTorsor

open AAT.AG.ComparisonInformationLoss

variable {F : FixedFDirectedMultigraph} {K : Type w}

abbrev ComponentGroup :=
  FixedFRestrictedKernelIdentification.ComponentGroup (F := F) (K := K)

abbrev FollowingGroup (H : Subgroup (FixedFGraphAutomorphism F)) :=
  FixedFRestrictedAutomorphism.FollowingGroup (K := K) H

/-- The actual fiber over one independently supplied visible automorphism. -/
def ProjectionFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :=
  { actual : FollowingGroup (K := K) H //
      FixedFRestrictedAutomorphism.projection (K := K) H actual = automorphism }

/-- Right multiplication by the literal actual projection kernel, represented
as a left action of its opposite group. -/
instance projectionFiberSMul
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    SMul (MonoidHom.ker
        (FixedFRestrictedAutomorphism.projection (K := K) H))ᵐᵒᵖ
      (ProjectionFiber (K := K) H automorphism) where
  smul kernelElement actual :=
    ⟨actual.1 * (MulOpposite.unop kernelElement).1, by
      rw [map_mul, actual.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelElement).property,
        mul_one]⟩

/-- The literal right-kernel action satisfies the group action laws. -/
instance projectionFiberMulAction
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    MulAction (MonoidHom.ker
        (FixedFRestrictedAutomorphism.projection (K := K) H))ᵐᵒᵖ
      (ProjectionFiber (K := K) H automorphism) where
  one_smul actual := by
    apply Subtype.ext
    change actual.1 * (1 : FollowingGroup (K := K) H) = actual.1
    simp
  mul_smul first second actual := by
    apply Subtype.ext
    change actual.1 *
        (((MulOpposite.unop second :
            MonoidHom.ker
              (FixedFRestrictedAutomorphism.projection (K := K) H)) :
            FollowingGroup (K := K) H) *
          ((MulOpposite.unop first :
            MonoidHom.ker
              (FixedFRestrictedAutomorphism.projection (K := K) H)) :
            FollowingGroup (K := K) H)) =
      (actual.1 *
          ((MulOpposite.unop second :
            MonoidHom.ker
              (FixedFRestrictedAutomorphism.projection (K := K) H)) :
            FollowingGroup (K := K) H)) *
        ((MulOpposite.unop first :
          MonoidHom.ker
            (FixedFRestrictedAutomorphism.projection (K := K) H)) :
          FollowingGroup (K := K) H)
    simp [mul_assoc]

/-- The actual right-kernel action on each projection fiber is free. -/
theorem projectionFiber_action_free
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (actual : ProjectionFiber (K := K) H automorphism) :
    Function.Injective
      (fun kernelElement :
          (MonoidHom.ker
            (FixedFRestrictedAutomorphism.projection (K := K) H))ᵐᵒᵖ =>
        kernelElement • actual) := by
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have values := congrArg
    (fun point : ProjectionFiber (K := K) H automorphism => point.1) equality
  exact mul_left_cancel values

/-- The actual right-kernel action on each projection fiber is transitive. -/
theorem projectionFiber_action_transitive
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (first second : ProjectionFiber (K := K) H automorphism) :
    ∃ kernelElement :
        (MonoidHom.ker
          (FixedFRestrictedAutomorphism.projection (K := K) H))ᵐᵒᵖ,
      kernelElement • first = second := by
  let displacement : FollowingGroup (K := K) H := first.1⁻¹ * second.1
  have displacement_mem : displacement ∈
      MonoidHom.ker
        (FixedFRestrictedAutomorphism.projection (K := K) H) := by
    rw [MonoidHom.mem_ker]
    change FixedFRestrictedAutomorphism.projection (K := K) H
        (first.1⁻¹ * second.1) = 1
    rw [map_mul, map_inv,
      first.property, second.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, displacement_mem⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Between two following changes above the same visible automorphism there
is a unique literal kernel displacement. -/
theorem projectionFiber_existsUnique_smul_eq
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (first second : ProjectionFiber (K := K) H automorphism) :
    ∃! kernelElement :
        (MonoidHom.ker
          (FixedFRestrictedAutomorphism.projection (K := K) H))ᵐᵒᵖ,
      kernelElement • first = second := by
  rcases projectionFiber_action_transitive H automorphism first second with
    ⟨kernelElement, equality⟩
  refine ⟨kernelElement, equality, ?_⟩
  intro other otherEquality
  exact projectionFiber_action_free H automorphism first
    (otherEquality.trans equality.symm)

/-- The concrete G-123(F1) sequence is short exact. -/
theorem isGroupShortExact
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    IsGroupShortExact
      (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H)
      (FixedFRestrictedAutomorphism.projection (K := K) H) := by
  refine ⟨FixedFRestrictedKernelIdentification.componentKernelHom_injective
      (K := K) H, ?_,
    FixedFRestrictedAutomorphism.projection_surjective (K := K) H⟩
  rw [MonoidHom.mulExact_iff]
  exact (FixedFRestrictedKernelIdentification.range_componentKernelHom_eq_ker_projection
    (K := K) H).symm

/-- The section in G-123(F1) is a homomorphic right inverse of the concrete
visible projection. -/
theorem canonicalSection_rightInverse
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.RightInverse
      (FixedFRestrictedAutomorphism.canonicalSection (K := K) H)
      (FixedFRestrictedAutomorphism.projection (K := K) H) :=
  FixedFRestrictedAutomorphism.projection_section (K := K) H

/-- Reading components reconstructs every actual element whose visible
projection is identity. -/
theorem componentKernelHom_componentFamilyOfPair_of_projection_eq_one
    (H : Subgroup (FixedFGraphAutomorphism F))
    (actual : FollowingGroup (K := K) H)
    (projection_eq_one :
      FixedFRestrictedAutomorphism.projection (K := K) H actual = 1) :
    FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H
        (FixedFRestrictedKernelIdentification.componentFamilyOfPair actual.1) =
      actual := by
  have kernelMembership : actual ∈
      MonoidHom.ker (FixedFRestrictedAutomorphism.projection (K := K) H) := by
    exact (MonoidHom.mem_ker).2 projection_eq_one
  rw [← FixedFRestrictedKernelIdentification.range_componentKernelHom_eq_ker_projection
    (K := K) H] at kernelMembership
  rcases kernelMembership with ⟨family, family_eq⟩
  rw [← family_eq]
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · rfl
  apply Equiv.ext
  rintro ⟨vertex, hidden⟩
  rfl

/-- Remove the canonical visible lift from a point of one projection fiber. -/
def normalizedKernelElement
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (actual : ProjectionFiber (K := K) H automorphism) :
    FollowingGroup (K := K) H :=
  actual.1 *
    (FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism)⁻¹

/-- Removing the canonical lift lands in the literal kernel. -/
theorem normalizedKernelElement_projection
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (actual : ProjectionFiber (K := K) H automorphism) :
    FixedFRestrictedAutomorphism.projection (K := K) H
        (normalizedKernelElement (K := K) H automorphism actual) = 1 := by
  rw [normalizedKernelElement, map_mul, map_inv, actual.property,
    FixedFRestrictedAutomorphism.projection_section]
  exact mul_inv_cancel automorphism

/-- Construct the actual following change over `u` represented by a hidden
component family. -/
def componentFamilyToFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (family : ComponentGroup (F := F) (K := K)) :
    ProjectionFiber (K := K) H automorphism :=
  ⟨FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H family *
      FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism,
    by
      rw [map_mul,
        FixedFRestrictedKernelIdentification.projection_componentKernelHom,
        FixedFRestrictedAutomorphism.projection_section, one_mul]⟩

/-- Read the unique hidden component family of an actual following change
after its canonical visible lift has been removed. -/
def componentFamilyOfFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (actual : ProjectionFiber (K := K) H automorphism) :
    ComponentGroup (F := F) (K := K) :=
  FixedFRestrictedKernelIdentification.componentFamilyOfPair
    (normalizedKernelElement (K := K) H automorphism actual).1

/-- Construction followed by reading returns the authored component family. -/
theorem componentFamilyOfFiber_componentFamilyToFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (family : ComponentGroup (F := F) (K := K)) :
    componentFamilyOfFiber (K := K) H automorphism
        (componentFamilyToFiber (K := K) H automorphism family) = family := by
  apply FixedFRestrictedKernelIdentification.componentKernelHom_injective (K := K) H
  rw [componentFamilyOfFiber]
  have reconstruction :=
    componentKernelHom_componentFamilyOfPair_of_projection_eq_one
      (K := K) H
      (normalizedKernelElement (K := K) H automorphism
        (componentFamilyToFiber (K := K) H automorphism family))
      (normalizedKernelElement_projection (K := K) H automorphism
        (componentFamilyToFiber (K := K) H automorphism family))
  rw [reconstruction]
  simp [normalizedKernelElement, componentFamilyToFiber]

/-- Reading followed by construction returns the original actual following
change, including its state equivalence and all operation-preservation data. -/
theorem componentFamilyToFiber_componentFamilyOfFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H)
    (actual : ProjectionFiber (K := K) H automorphism) :
    componentFamilyToFiber (K := K) H automorphism
        (componentFamilyOfFiber (K := K) H automorphism actual) = actual := by
  apply Subtype.ext
  change
    FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H
          (componentFamilyOfFiber (K := K) H automorphism actual) *
        FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism =
      actual.1
  have reconstruction :=
    componentKernelHom_componentFamilyOfPair_of_projection_eq_one
      (K := K) H
      (normalizedKernelElement (K := K) H automorphism actual)
      (normalizedKernelElement_projection (K := K) H automorphism actual)
  calc
    FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H
          (componentFamilyOfFiber (K := K) H automorphism actual) *
        FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism =
        normalizedKernelElement (K := K) H automorphism actual *
          FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism := by
            rw [componentFamilyOfFiber, reconstruction]
    _ = actual.1 := by simp [normalizedKernelElement]

/-- Every visible automorphism has exactly the component-indexed family of
following changes prescribed by G-123(F1). -/
def componentGroupEquivProjectionFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (automorphism : H) :
    ComponentGroup (F := F) (K := K) ≃
      ProjectionFiber (K := K) H automorphism where
  toFun := componentFamilyToFiber H automorphism
  invFun := componentFamilyOfFiber H automorphism
  left_inv := componentFamilyOfFiber_componentFamilyToFiber H automorphism
  right_inv := componentFamilyToFiber_componentFamilyOfFiber H automorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFSplitExactSequenceAndTorsor

end AAT.AG.RealizationReconstruction
