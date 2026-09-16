import ResearchLean.AG.RealizationReconstruction.FixedFSplitExactSequenceAndTorsor
import Formal.Util.AssertStandardAxioms

/-!
# The basepoint-preserving fixed-graph split sequence

Fix a hidden value `k₀ : K`.  The actual following pairs whose hidden
fiber permutation fixes `k₀` at every vertex form a subgroup of the full
restricted actual group.  Its kernel is constructed from one copy of the
point stabilizer in `Sym(K)` for every generated undirected component.

The visible identity-hidden section lands in this subgroup.  The resulting
sequence is split short exact, and every pointed projection fiber is
explicitly equivalent to the component-indexed point-stabilizer group.  The
basepoint law is proved from the actual fiber maps; it is not supplied as a
lift, exactness, or reconstruction certificate.
-/

namespace AAT.AG.RealizationReconstruction

universe u v w

namespace FixedFPointedSplitExactSequenceAndTorsor

open AAT.AG.ComparisonInformationLoss
open AAT.AG.RealizationReconstruction.FixedFSplitExactSequenceAndTorsor

variable {F : FixedFDirectedMultigraph} {K : Type w}

/-- Hidden permutations that fix the selected basepoint. -/
abbrev PointedPermutation (basepoint : K) :=
  MulAction.stabilizer (Equiv.Perm K) basepoint

/-- One basepoint-fixing hidden permutation for every generated component. -/
abbrev PointedComponentGroup (F : FixedFDirectedMultigraph)
    (K : Type w) (basepoint : K) :=
  FixedFComponent F → PointedPermutation basepoint

/-- Actual restricted following pairs that preserve the selected hidden
basepoint in every vertex fiber. -/
def PointedFollowingGroup
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Subgroup (FixedFRestrictedAutomorphism.FollowingGroup (K := K) H) where
  carrier := { actual | ∀ vertex, actual.1.fiberPerm vertex basepoint = basepoint }
  one_mem' := by
    intro vertex
    rfl
  mul_mem' := by
    intro first second firstFixes secondFixes vertex
    change (first.1 * second.1).fiberPerm vertex basepoint = basepoint
    rw [FixedFPreservingFollowingPair.mul_fiberPerm]
    change first.1.fiberPerm (second.1.automorphism.vertex vertex)
        (second.1.fiberPerm vertex basepoint) = basepoint
    rw [secondFixes vertex, firstFixes]
  inv_mem' := by
    intro actual actualFixes vertex
    change actual.1.change.inverse.fiberPerm vertex basepoint = basepoint
    rw [FixedFFollowingStateChange.inverse_fiberPerm]
    exact (actual.1.fiberPerm
      (actual.1.automorphism.vertex.symm vertex)).symm_apply_eq.mpr
        (actualFixes _).symm

/-- The pointwise fiber condition is exactly preservation of the selected
basepoint section in the actual state equivalence. -/
theorem mem_pointedFollowingGroup_iff_state
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (actual : FixedFRestrictedAutomorphism.FollowingGroup (K := K) H) :
    actual ∈ PointedFollowingGroup H basepoint ↔
      ∀ vertex,
        actual.1.h (vertex, basepoint) =
          (actual.1.automorphism.vertex vertex, basepoint) := by
  constructor
  · intro fixes vertex
    calc
      actual.1.h (vertex, basepoint) =
          (actual.1.automorphism.vertex vertex,
            actual.1.fiberPerm vertex basepoint) :=
        actual.1.change.factorization vertex basepoint
      _ = (actual.1.automorphism.vertex vertex, basepoint) := by
        rw [fixes vertex]
  · intro preserves vertex
    change (actual.1.h (vertex, basepoint)).2 = basepoint
    exact congrArg Prod.snd (preserves vertex)

/-- Restrict the visible projection to the basepoint-preserving actual
subgroup. -/
def pointedProjection
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    PointedFollowingGroup H basepoint →* H :=
  (FixedFRestrictedAutomorphism.projection (K := K) H).comp
    (PointedFollowingGroup H basepoint).subtype

/-- The canonical identity-hidden lift preserves every selected basepoint. -/
def pointedCanonicalSection
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    H →* PointedFollowingGroup H basepoint where
  toFun automorphism :=
    ⟨FixedFRestrictedAutomorphism.canonicalSection (K := K) H automorphism,
      by
        intro vertex
        rfl⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (FixedFRestrictedAutomorphism.canonicalSection (K := K) H)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (FixedFRestrictedAutomorphism.canonicalSection (K := K) H)
      first second

/-- The pointed section is a right inverse of the pointed projection. -/
theorem pointedProjection_section
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :
    pointedProjection H basepoint
        (pointedCanonicalSection H basepoint automorphism) = automorphism :=
  FixedFRestrictedAutomorphism.projection_section (K := K) H automorphism

/-- Every visible automorphism has an actual basepoint-preserving lift. -/
theorem pointedProjection_surjective
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.Surjective (pointedProjection H basepoint) := by
  intro automorphism
  exact ⟨pointedCanonicalSection H basepoint automorphism,
    pointedProjection_section H basepoint automorphism⟩

/-- Forget only the point-stabilizer subtype of a component family. -/
def forgetPointedComponentGroup (basepoint : K) :
    PointedComponentGroup F K basepoint →*
      FixedFRestrictedKernelIdentification.ComponentGroup (F := F) (K := K) where
  toFun family component := (family component).1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Forgetting point-stabilizer proofs is injective. -/
theorem forgetPointedComponentGroup_injective (basepoint : K) :
    Function.Injective
      (forgetPointedComponentGroup (F := F) (K := K) basepoint) := by
  intro first second equality
  funext component
  apply Subtype.ext
  exact congrFun equality component

/-- Construct an actual basepoint-preserving kernel element from one pointed
hidden permutation per generated component. -/
def pointedComponentKernelHom
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    PointedComponentGroup F K basepoint →*
      PointedFollowingGroup H basepoint where
  toFun family :=
    ⟨FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H
        (forgetPointedComponentGroup basepoint family),
      by
        intro vertex
        rw [FixedFRestrictedKernelIdentification.componentKernelHom_fiberPerm]
        exact (family (fixedFComponentMk F vertex)).2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one
      (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul
      (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H)
      (forgetPointedComponentGroup basepoint first)
      (forgetPointedComponentGroup basepoint second)

/-- The pointed component-family construction is faithful. -/
theorem pointedComponentKernelHom_injective
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.Injective (pointedComponentKernelHom H basepoint) := by
  intro first second equality
  apply forgetPointedComponentGroup_injective basepoint
  apply FixedFRestrictedKernelIdentification.componentKernelHom_injective (K := K) H
  exact congrArg Subtype.val equality

/-- Every pointed component family has identity visible projection. -/
theorem pointedProjection_pointedComponentKernelHom
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (family : PointedComponentGroup F K basepoint) :
    pointedProjection H basepoint
        (pointedComponentKernelHom H basepoint family) = 1 :=
  FixedFRestrictedKernelIdentification.projection_componentKernelHom (K := K) H
    (forgetPointedComponentGroup basepoint family)

/-- Read a pointed component family from an actual pointed pair. -/
def pointedComponentFamilyOfPair
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (actual : PointedFollowingGroup H basepoint) :
    PointedComponentGroup F K basepoint :=
  fun component =>
    ⟨FixedFRestrictedKernelIdentification.componentFamilyOfPair actual.1.1 component,
      by
        refine Quotient.inductionOn component ?_
        intro vertex
        exact actual.2 vertex⟩

/-- Extraction reconstructs every pointed element with identity visible
projection. -/
theorem pointedComponentKernelHom_pointedComponentFamilyOfPair
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (actual : PointedFollowingGroup H basepoint)
    (projection_eq_one : pointedProjection H basepoint actual = 1) :
    pointedComponentKernelHom H basepoint
        (pointedComponentFamilyOfPair H basepoint actual) = actual := by
  apply Subtype.ext
  exact componentKernelHom_componentFamilyOfPair_of_projection_eq_one
    (K := K) H actual.1 projection_eq_one

/-- The pointed component-family range is the literal kernel of the pointed
visible projection. -/
theorem range_pointedComponentKernelHom_eq_ker_pointedProjection
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    MonoidHom.range (pointedComponentKernelHom H basepoint) =
      MonoidHom.ker (pointedProjection H basepoint) := by
  apply le_antisymm
  · rintro actual ⟨family, rfl⟩
    rw [MonoidHom.mem_ker]
    exact pointedProjection_pointedComponentKernelHom H basepoint family
  · intro actual kernelMembership
    rw [MonoidHom.mem_ker] at kernelMembership
    exact ⟨pointedComponentFamilyOfPair H basepoint actual,
      pointedComponentKernelHom_pointedComponentFamilyOfPair
        H basepoint actual kernelMembership⟩

/-- The basepoint-preserving fixed-F sequence is short exact. -/
theorem isGroupShortExact
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    IsGroupShortExact (pointedComponentKernelHom H basepoint)
      (pointedProjection H basepoint) := by
  refine ⟨pointedComponentKernelHom_injective H basepoint, ?_,
    pointedProjection_surjective H basepoint⟩
  rw [MonoidHom.mulExact_iff]
  exact (range_pointedComponentKernelHom_eq_ker_pointedProjection
    H basepoint).symm

/-- The basepoint-preserving sequence is split by the constructed
identity-hidden section. -/
theorem pointedCanonicalSection_rightInverse
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K) :
    Function.RightInverse (pointedCanonicalSection H basepoint)
      (pointedProjection H basepoint) :=
  pointedProjection_section H basepoint

/-- The full pointed projection fiber over one visible automorphism. -/
def PointedProjectionFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :=
  { actual : PointedFollowingGroup H basepoint //
      pointedProjection H basepoint actual = automorphism }

/-- Right multiplication by the literal pointed projection kernel. -/
instance pointedProjectionFiberSMul
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :
    SMul (MonoidHom.ker (pointedProjection H basepoint))ᵐᵒᵖ
      (PointedProjectionFiber H basepoint automorphism) where
  smul kernelElement actual :=
    ⟨actual.1 * (MulOpposite.unop kernelElement).1, by
      rw [map_mul, actual.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelElement).property,
        mul_one]⟩

/-- The literal pointed right-kernel action satisfies the group action laws. -/
instance pointedProjectionFiberMulAction
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :
    MulAction (MonoidHom.ker (pointedProjection H basepoint))ᵐᵒᵖ
      (PointedProjectionFiber H basepoint automorphism) where
  one_smul actual := by
    apply Subtype.ext
    change actual.1 * (1 : PointedFollowingGroup H basepoint) = actual.1
    simp
  mul_smul first second actual := by
    apply Subtype.ext
    change actual.1 *
        (((MulOpposite.unop second :
            MonoidHom.ker (pointedProjection H basepoint)) :
            PointedFollowingGroup H basepoint) *
          ((MulOpposite.unop first :
            MonoidHom.ker (pointedProjection H basepoint)) :
            PointedFollowingGroup H basepoint)) =
      (actual.1 *
          ((MulOpposite.unop second :
            MonoidHom.ker (pointedProjection H basepoint)) :
            PointedFollowingGroup H basepoint)) *
        ((MulOpposite.unop first :
          MonoidHom.ker (pointedProjection H basepoint)) :
          PointedFollowingGroup H basepoint)
    simp [mul_assoc]

/-- The literal pointed kernel action is free. -/
theorem pointedProjectionFiber_action_free
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (actual : PointedProjectionFiber H basepoint automorphism) :
    Function.Injective
      (fun kernelElement :
          (MonoidHom.ker (pointedProjection H basepoint))ᵐᵒᵖ =>
        kernelElement • actual) := by
  intro first second equality
  apply MulOpposite.unop_injective
  apply Subtype.ext
  have values := congrArg
    (fun point : PointedProjectionFiber H basepoint automorphism => point.1)
    equality
  exact mul_left_cancel values

/-- The literal pointed kernel action is transitive on every pointed fiber. -/
theorem pointedProjectionFiber_action_transitive
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (first second : PointedProjectionFiber H basepoint automorphism) :
    ∃ kernelElement :
        (MonoidHom.ker (pointedProjection H basepoint))ᵐᵒᵖ,
      kernelElement • first = second := by
  let displacement : PointedFollowingGroup H basepoint := first.1⁻¹ * second.1
  have displacement_mem : displacement ∈
      MonoidHom.ker (pointedProjection H basepoint) := by
    rw [MonoidHom.mem_ker]
    change pointedProjection H basepoint (first.1⁻¹ * second.1) = 1
    rw [map_mul, map_inv, first.property, second.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, displacement_mem⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- There is a unique literal pointed-kernel displacement between two
pointed following changes over the same visible automorphism. -/
theorem pointedProjectionFiber_existsUnique_smul_eq
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (first second : PointedProjectionFiber H basepoint automorphism) :
    ∃! kernelElement :
        (MonoidHom.ker (pointedProjection H basepoint))ᵐᵒᵖ,
      kernelElement • first = second := by
  rcases pointedProjectionFiber_action_transitive
      H basepoint automorphism first second with ⟨kernelElement, equality⟩
  refine ⟨kernelElement, equality, ?_⟩
  intro other otherEquality
  exact pointedProjectionFiber_action_free H basepoint automorphism first
    (otherEquality.trans equality.symm)

/-- Remove the pointed canonical lift from an actual pointed fiber element. -/
def normalizedPointedKernelElement
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (actual : PointedProjectionFiber H basepoint automorphism) :
    PointedFollowingGroup H basepoint :=
  actual.1 * (pointedCanonicalSection H basepoint automorphism)⁻¹

/-- Removing the pointed canonical lift lands in the pointed projection
kernel. -/
theorem normalizedPointedKernelElement_projection
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (actual : PointedProjectionFiber H basepoint automorphism) :
    pointedProjection H basepoint
        (normalizedPointedKernelElement H basepoint automorphism actual) = 1 := by
  rw [normalizedPointedKernelElement, map_mul, map_inv, actual.property,
    pointedProjection_section]
  exact mul_inv_cancel automorphism

/-- Construct every pointed following change from a pointed component
family and the canonical visible lift. -/
def pointedComponentFamilyToFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) (family : PointedComponentGroup F K basepoint) :
    PointedProjectionFiber H basepoint automorphism :=
  ⟨pointedComponentKernelHom H basepoint family *
      pointedCanonicalSection H basepoint automorphism,
    by
      rw [map_mul, pointedProjection_pointedComponentKernelHom,
        pointedProjection_section, one_mul]⟩

/-- Read the unique pointed component family after removing the canonical
visible lift. -/
def pointedComponentFamilyOfFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (actual : PointedProjectionFiber H basepoint automorphism) :
    PointedComponentGroup F K basepoint :=
  pointedComponentFamilyOfPair H basepoint
    (normalizedPointedKernelElement H basepoint automorphism actual)

/-- Pointed construction followed by reading is identity. -/
theorem pointedComponentFamilyOfFiber_pointedComponentFamilyToFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) (family : PointedComponentGroup F K basepoint) :
    pointedComponentFamilyOfFiber H basepoint automorphism
        (pointedComponentFamilyToFiber H basepoint automorphism family) =
      family := by
  apply pointedComponentKernelHom_injective H basepoint
  rw [pointedComponentFamilyOfFiber]
  have reconstruction :=
    pointedComponentKernelHom_pointedComponentFamilyOfPair
      H basepoint
      (normalizedPointedKernelElement H basepoint automorphism
        (pointedComponentFamilyToFiber H basepoint automorphism family))
      (normalizedPointedKernelElement_projection H basepoint automorphism
        (pointedComponentFamilyToFiber H basepoint automorphism family))
  rw [reconstruction]
  simp [normalizedPointedKernelElement, pointedComponentFamilyToFiber]

/-- Reading followed by pointed construction returns the complete original
actual following pair. -/
theorem pointedComponentFamilyToFiber_pointedComponentFamilyOfFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H)
    (actual : PointedProjectionFiber H basepoint automorphism) :
    pointedComponentFamilyToFiber H basepoint automorphism
        (pointedComponentFamilyOfFiber H basepoint automorphism actual) =
      actual := by
  apply Subtype.ext
  change pointedComponentKernelHom H basepoint
        (pointedComponentFamilyOfFiber H basepoint automorphism actual) *
      pointedCanonicalSection H basepoint automorphism = actual.1
  have reconstruction :=
    pointedComponentKernelHom_pointedComponentFamilyOfPair
      H basepoint
      (normalizedPointedKernelElement H basepoint automorphism actual)
      (normalizedPointedKernelElement_projection H basepoint automorphism actual)
  calc
    pointedComponentKernelHom H basepoint
          (pointedComponentFamilyOfFiber H basepoint automorphism actual) *
        pointedCanonicalSection H basepoint automorphism =
        normalizedPointedKernelElement H basepoint automorphism actual *
          pointedCanonicalSection H basepoint automorphism := by
            rw [pointedComponentFamilyOfFiber, reconstruction]
    _ = actual.1 := by simp [normalizedPointedKernelElement]

/-- Pointed following changes above every visible automorphism are exactly
component-indexed basepoint stabilizers. -/
def pointedComponentGroupEquivProjectionFiber
    (H : Subgroup (FixedFGraphAutomorphism F)) (basepoint : K)
    (automorphism : H) :
    PointedComponentGroup F K basepoint ≃
      PointedProjectionFiber H basepoint automorphism where
  toFun := pointedComponentFamilyToFiber H basepoint automorphism
  invFun := pointedComponentFamilyOfFiber H basepoint automorphism
  left_inv :=
    pointedComponentFamilyOfFiber_pointedComponentFamilyToFiber
      H basepoint automorphism
  right_inv :=
    pointedComponentFamilyToFiber_pointedComponentFamilyOfFiber
      H basepoint automorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end FixedFPointedSplitExactSequenceAndTorsor

end AAT.AG.RealizationReconstruction
