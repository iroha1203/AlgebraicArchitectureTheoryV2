import ResearchLean.AG.RealizationReconstruction.FixedFLensConnection
import ResearchLean.AG.RealizationReconstruction.FixedFSplitExactSequenceAndTorsor
import Formal.Util.AssertStandardAxioms

/-!
# The all-H product-lens change group

For an arbitrary independently supplied `H ≤ Perm V`, this file assembles the
fixed-visible lens changes of Cycle 120 into the actual group of all pairs
`(u,h)` satisfying the independent get/put equations.  It constructs the
visible projection and its identity-hidden section, then identifies this group
with the fixed-F following group over the image of `H` in complete-update graph
automorphisms.

Thus multiplication, projection, section, kernels, and literal projection
fibers are transported by a genuine group equivalence rather than inferred
from the cardinality of each fixed-visible fiber.
-/

namespace AAT.AG.RealizationReconstruction

universe u

namespace FixedFLensGroupConnection

open FixedFFiniteExamples
open FixedFLensConnection
open FixedFRestrictedAutomorphism
open FixedFSplitExactSequenceAndTorsor

variable {V K : Type u} {reference : V}

/-- Visible permutations act on the complete update graph by simultaneously
renaming both endpoints of every named put operation. -/
def completeUpdateAutomorphismHom :
    Equiv.Perm V →* FixedFGraphAutomorphism (completeUpdateGraph V) where
  toFun := completeUpdateAutomorphism
  map_one' := by
    apply FixedFGraphAutomorphism.ext <;> rfl
  map_mul' first second := by
    apply FixedFGraphAutomorphism.ext <;> rfl

theorem completeUpdateAutomorphismHom_injective :
    Function.Injective (completeUpdateAutomorphismHom (V := V)) := by
  intro first second equality
  apply Equiv.ext
  intro vertex
  exact congrArg
    (fun automorphism : FixedFGraphAutomorphism (completeUpdateGraph V) =>
      automorphism.vertex vertex) equality

/-- Image of an independently supplied visible subgroup in actual graph
automorphisms. -/
def completeUpdateGraphSubgroup (H : Subgroup (Equiv.Perm V)) :
    Subgroup (FixedFGraphAutomorphism (completeUpdateGraph V)) :=
  H.map (completeUpdateAutomorphismHom (V := V))

/-- The independent CS-side group carrier: all visible changes in `H` and all
state equivalences satisfying both product-lens equations with the same
visible change. -/
@[ext]
structure LensChangeGroup (H : Subgroup (Equiv.Perm V)) where
  visible : H
  h : (V × K) ≃ (V × K)
  get_naturality : ∀ state,
    (h state).1 = visible.1 state.1
  put_naturality : ∀ state requested,
    h (requested, state.2) =
      (visible.1 requested, (h state).2)

namespace LensChangeGroup

variable {H : Subgroup (Equiv.Perm V)}

/-- Recover the Cycle 120 independent fixed-visible lens change. -/
def toLensInvertibleChange [Finite K]
    (change : LensChangeGroup (K := K) H) :
    LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) change.visible.1 where
  h := change.h
  get_naturality := change.get_naturality
  put_naturality state requested := by
    change change.h (requested, state.2) =
      (change.visible.1 requested, (change.h state).2)
    exact change.put_naturality state requested

instance : One (LensChangeGroup (K := K) H) where
  one :=
    { visible := 1
      h := 1
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }

instance : Mul (LensChangeGroup (K := K) H) where
  mul first second :=
    { visible := first.visible * second.visible
      h := first.h * second.h
      get_naturality := fun state => by
        change (first.h (second.h state)).1 =
          first.visible.1 (second.visible.1 state.1)
        rw [first.get_naturality, second.get_naturality]
      put_naturality := fun state requested => by
        change first.h (second.h (requested, state.2)) =
          (first.visible.1 (second.visible.1 requested),
            (first.h (second.h state)).2)
        rw [second.put_naturality state requested]
        exact first.put_naturality (second.h state)
          (second.visible.1 requested) }

instance : Inv (LensChangeGroup (K := K) H) where
  inv change :=
    { visible := change.visible⁻¹
      h := change.h⁻¹
      get_naturality := fun state => by
        have observed :
            change.visible.1 ((change.h.symm state).1) = state.1 := by
          calc
            change.visible.1 ((change.h.symm state).1) =
                (change.h (change.h.symm state)).1 :=
              (change.get_naturality (change.h.symm state)).symm
            _ = state.1 := by rw [change.h.apply_symm_apply]
        simpa using congrArg change.visible.1.symm observed
      put_naturality := fun state requested => by
        apply change.h.injective
        calc
          change.h (change.h.symm (requested, state.2)) =
              (requested, state.2) := change.h.apply_symm_apply _
          _ =
              (change.visible.1
                (change.visible.1.symm requested),
                (change.h (change.h.symm state)).2) := by simp
          _ = change.h
              (change.visible.1.symm requested,
                (change.h.symm state).2) :=
            (change.put_naturality (change.h.symm state)
              (change.visible.1.symm requested)).symm }

instance : Group (LensChangeGroup (K := K) H) where
  mul_assoc first second third := by
    apply LensChangeGroup.ext
    · exact mul_assoc _ _ _
    · exact mul_assoc _ _ _
  one_mul change := by
    apply LensChangeGroup.ext
    · exact one_mul _
    · exact one_mul _
  mul_one change := by
    apply LensChangeGroup.ext
    · exact mul_one _
    · exact mul_one _
  inv_mul_cancel change := by
    apply LensChangeGroup.ext
    · exact inv_mul_cancel _
    · exact inv_mul_cancel _

/-- Projection to the independently supplied visible subgroup. -/
def projection : LensChangeGroup (K := K) H →* H where
  toFun := visible
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The identity-hidden product-lens change over every allowed visible
permutation. -/
def canonicalSection : H →* LensChangeGroup (K := K) H where
  toFun visible :=
    { visible := visible
      h := Equiv.prodCongr visible.1 1
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }
  map_one' := by
    apply LensChangeGroup.ext <;> rfl
  map_mul' first second := by
    apply LensChangeGroup.ext <;> rfl

theorem projection_section (visible : H) :
    projection (K := K) (canonicalSection (K := K) visible) = visible :=
  rfl

/-- Map an independent lens change into the actual fixed-F following group. -/
def toFollowingGroup :
    LensChangeGroup (K := K) H →*
      FixedFRestrictedAutomorphism.FollowingGroup (K := K)
        (completeUpdateGraphSubgroup H) where
  toFun change :=
    ⟨{ automorphism := completeUpdateAutomorphism change.visible.1
       h := change.h
       observation := fun vertex hidden =>
         change.get_naturality (vertex, hidden)
       preserves := fun namedEdge hidden => by
         rcases namedEdge with ⟨source, target⟩
         exact change.put_naturality (source, hidden) target },
      ⟨change.visible.1, change.visible.2, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext <;> rfl
  map_mul' first second := by
    apply Subtype.ext
    apply FixedFPreservingFollowingPair.ext <;> rfl

theorem toFollowingGroup_injective :
    Function.Injective (toFollowingGroup (K := K) (H := H)) := by
  intro first second equality
  have pairEquality :
      (toFollowingGroup (K := K) first).1 =
        (toFollowingGroup (K := K) second).1 :=
    congrArg Subtype.val equality
  apply LensChangeGroup.ext
  · apply Subtype.ext
    apply completeUpdateAutomorphismHom_injective (V := V)
    exact congrArg FixedFPreservingFollowingPair.automorphism pairEquality
  · exact congrArg FixedFPreservingFollowingPair.h pairEquality

theorem toFollowingGroup_surjective :
    Function.Surjective (toFollowingGroup (K := K) (H := H)) := by
  intro actual
  rcases actual.2 with ⟨visible, visibleMem, automorphismEquality⟩
  let allowedVisible : H := ⟨visible, visibleMem⟩
  have autoEq : actual.1.automorphism =
      completeUpdateAutomorphism allowedVisible.1 :=
    automorphismEquality.symm
  let lensChange : LensChangeGroup (K := K) H :=
    { visible := allowedVisible
      h := actual.1.h
      get_naturality := fun state => by
        rcases state with ⟨vertex, hidden⟩
        calc
          (actual.1.h (vertex, hidden)).1 =
              actual.1.automorphism.vertex vertex :=
            actual.1.observation vertex hidden
          _ = allowedVisible.1 vertex := by
            rw [autoEq]
            rfl
      put_naturality := fun state requested => by
        rcases state with ⟨source, hidden⟩
        have execution := actual.1.preserves (source, requested) hidden
        simpa [autoEq, completeUpdateAutomorphism,
          completeUpdateGraph] using execution }
  refine ⟨lensChange, ?_⟩
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · exact autoEq.symm
  · rfl

/-- Group-level equivalence, not merely a collection of fixed-visible fiber
bijections. -/
noncomputable def mulEquivFollowingGroup :
    LensChangeGroup (K := K) H ≃*
      FixedFRestrictedAutomorphism.FollowingGroup (K := K)
        (completeUpdateGraphSubgroup H) :=
  MulEquiv.ofBijective (toFollowingGroup (K := K) (H := H))
    ⟨toFollowingGroup_injective, toFollowingGroup_surjective⟩

/-- The visible subgroup itself is faithfully identified with its graph image. -/
noncomputable def visibleMulEquivGraphSubgroup :
    H ≃* completeUpdateGraphSubgroup H :=
  let hom : H →* completeUpdateGraphSubgroup H :=
    { toFun := fun visible =>
        ⟨completeUpdateAutomorphism visible.1,
          ⟨visible.1, visible.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one
        (completeUpdateAutomorphismHom (V := V)))
      map_mul' := fun first second => Subtype.ext (map_mul
        (completeUpdateAutomorphismHom (V := V)) first.1 second.1) }
  MulEquiv.ofBijective hom ⟨by
      intro first second equality
      apply Subtype.ext
      apply completeUpdateAutomorphismHom_injective (V := V)
      exact congrArg Subtype.val equality,
    by
      intro graphVisible
      rcases graphVisible.2 with ⟨visible, visibleMem, equality⟩
      exact ⟨⟨visible, visibleMem⟩, Subtype.ext equality⟩⟩

/-- The group equivalence commutes with visible projection. -/
theorem projection_compatibility (change : LensChangeGroup (K := K) H) :
    FixedFRestrictedAutomorphism.projection
        (K := K) (completeUpdateGraphSubgroup H)
        (mulEquivFollowingGroup change) =
      visibleMulEquivGraphSubgroup (projection change) :=
by
  apply Subtype.ext
  rfl

/-- The group equivalence carries the independent lens section to the fixed-F
canonical section. -/
theorem section_compatibility (visible : H) :
    mulEquivFollowingGroup (K := K)
        (canonicalSection (K := K) visible) =
      FixedFRestrictedAutomorphism.canonicalSection
        (K := K) (completeUpdateGraphSubgroup H)
        (visibleMulEquivGraphSubgroup visible) := by
  apply Subtype.ext
  apply FixedFPreservingFollowingPair.ext
  · rfl
  · rfl

/-- The same group equivalence restricts to the literal projection kernels;
kernel membership is proved from the commuting projection square rather than
added to either carrier. -/
noncomputable def kernelMulEquiv :
    MonoidHom.ker (projection (K := K) (H := H)) ≃*
      MonoidHom.ker
        (FixedFRestrictedAutomorphism.projection
          (K := K) (completeUpdateGraphSubgroup H)) where
  toFun kernelElement :=
    ⟨mulEquivFollowingGroup kernelElement.1, by
      rw [MonoidHom.mem_ker]
      rw [projection_compatibility]
      rw [MonoidHom.mem_ker.mp kernelElement.property]
      exact map_one (visibleMulEquivGraphSubgroup (V := V) (H := H))⟩
  invFun kernelElement :=
    ⟨mulEquivFollowingGroup.symm kernelElement.1, by
      rw [MonoidHom.mem_ker]
      apply visibleMulEquivGraphSubgroup.injective
      calc
        visibleMulEquivGraphSubgroup
            (projection (mulEquivFollowingGroup.symm kernelElement.1)) =
            FixedFRestrictedAutomorphism.projection
              (K := K) (completeUpdateGraphSubgroup H) kernelElement.1 := by
          rw [← projection_compatibility,
            mulEquivFollowingGroup.apply_symm_apply]
        _ = 1 := MonoidHom.mem_ker.mp kernelElement.property
        _ = visibleMulEquivGraphSubgroup 1 :=
          (map_one (visibleMulEquivGraphSubgroup
            (V := V) (H := H))).symm⟩
  left_inv kernelElement := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.symm_apply_apply kernelElement.1
  right_inv kernelElement := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.apply_symm_apply kernelElement.1
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul mulEquivFollowingGroup first.1 second.1

/-- Literal lens projection fiber over one visible change. -/
abbrev ProjectionFiber (visible : H) :=
  { change : LensChangeGroup (K := K) H //
    projection change = visible }

/-- Right multiplication by the literal kernel of the independent lens
projection.  This is defined on the lens group itself, before transporting
anything to the fixed-F presentation. -/
instance projectionFiberSMul (visible : H) :
    SMul (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ
      (ProjectionFiber (K := K) visible) where
  smul kernelElement change :=
    ⟨change.1 * (MulOpposite.unop kernelElement).1, by
      rw [map_mul, change.property,
        MonoidHom.mem_ker.mp (MulOpposite.unop kernelElement).property,
        mul_one]⟩

/-- The literal lens-kernel action obeys the group action laws. -/
instance projectionFiberMulAction (visible : H) :
    MulAction (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ
      (ProjectionFiber (K := K) visible) where
  one_smul change := by
    apply Subtype.ext
    change change.1 * (1 : LensChangeGroup (K := K) H) = change.1
    exact mul_one _
  mul_smul first second change := by
    apply Subtype.ext
    change change.1 *
        (((MulOpposite.unop second :
            MonoidHom.ker (projection (K := K) (H := H))) :
          LensChangeGroup (K := K) H) *
         ((MulOpposite.unop first :
            MonoidHom.ker (projection (K := K) (H := H))) :
          LensChangeGroup (K := K) H)) =
      (change.1 *
          ((MulOpposite.unop second :
            MonoidHom.ker (projection (K := K) (H := H))) :
            LensChangeGroup (K := K) H)) *
        ((MulOpposite.unop first :
          MonoidHom.ker (projection (K := K) (H := H))) :
          LensChangeGroup (K := K) H)
    exact (mul_assoc _ _ _).symm

/-- The literal kernel action on every independent lens fiber is free. -/
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

/-- The literal kernel action on every independent lens fiber is transitive. -/
theorem projectionFiber_action_transitive (visible : H)
    (first second : ProjectionFiber (K := K) visible) :
    ∃ kernelElement :
        (MonoidHom.ker (projection (K := K) (H := H)))ᵐᵒᵖ,
      kernelElement • first = second := by
  let displacement : LensChangeGroup (K := K) H := first.1⁻¹ * second.1
  have displacement_mem : displacement ∈
      MonoidHom.ker (projection (K := K) (H := H)) := by
    rw [MonoidHom.mem_ker]
    change projection (K := K) (first.1⁻¹ * second.1) = 1
    rw [map_mul, map_inv, first.property, second.property, inv_mul_cancel]
  refine ⟨MulOpposite.op ⟨displacement, displacement_mem⟩, ?_⟩
  apply Subtype.ext
  change first.1 * displacement = second.1
  simp [displacement]

/-- Between two independent lens changes above the same visible change there
is a unique literal kernel displacement. -/
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

/-- Every literal lens projection fiber is identified with the corresponding
literal fixed-F projection fiber by the same group equivalence. -/
noncomputable def projectionFiberEquiv (visible : H) :
    ProjectionFiber (K := K) visible ≃
      FixedFSplitExactSequenceAndTorsor.ProjectionFiber
        (K := K) (completeUpdateGraphSubgroup H)
        (visibleMulEquivGraphSubgroup visible) where
  toFun change :=
    ⟨mulEquivFollowingGroup change.1, by
      rw [projection_compatibility, change.2]⟩
  invFun actual :=
    ⟨mulEquivFollowingGroup.symm actual.1, by
      apply visibleMulEquivGraphSubgroup.injective
      calc
        visibleMulEquivGraphSubgroup
            (projection (mulEquivFollowingGroup.symm actual.1)) =
            FixedFRestrictedAutomorphism.projection
              (K := K) (completeUpdateGraphSubgroup H)
              (mulEquivFollowingGroup
                (mulEquivFollowingGroup.symm actual.1)) :=
          (projection_compatibility
            (mulEquivFollowingGroup.symm actual.1)).symm
        _ = FixedFRestrictedAutomorphism.projection
              (K := K) (completeUpdateGraphSubgroup H) actual.1 := by
          rw [mulEquivFollowingGroup.apply_symm_apply]
        _ = visibleMulEquivGraphSubgroup visible := actual.2⟩
  left_inv change := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.symm_apply_apply change.1
  right_inv actual := by
    apply Subtype.ext
    exact mulEquivFollowingGroup.apply_symm_apply actual.1

/-- The fiber equivalence intertwines the two literal right-kernel actions.
Thus the lens torsor is the same torsor as the fixed-F preserving-change
fiber, not merely an equipotent set. -/
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

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end LensChangeGroup

end FixedFLensGroupConnection

end AAT.AG.RealizationReconstruction
