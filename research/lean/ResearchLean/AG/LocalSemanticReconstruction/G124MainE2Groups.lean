import ResearchLean.AG.LocalSemanticReconstruction.CSComponentLocalGroup
import Formal.Util.AssertStandardAxioms

/-! IV-4/E2: the fixed-F change groups, their literal component kernels,
sections, visible coordinates and all lift fibers in the one main reader. -/
namespace AAT.AG.LocalSemanticReconstruction.G124MainTheorem
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
universe u

/-- For each original protocol visible subgroup H, the same component group
is the literal projection kernel and the main-local automorphism group. Its
semidirect action retains the original visible coordinate, canonical section,
and every lift fiber. -/
theorem protocol_local_change_group_recovery
    {F : FixedFDirectedMultigraph.{u,u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    Function.Bijective (CSComponentLocalGroup.componentKernelMulEquiv (K := K) H) ∧
    Function.Bijective (CSComponentLocalGroup.protocolComponentLocalAutMulEquiv (K := K) H) ∧
    Function.Bijective (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv (K := K) H) ∧
    (∀ change : FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K) H,
      (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv H change).right =
        change.visible) ∧
    (∀ visible : H,
      CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv (K := K) H
        (FixedFProtocolGroupConnection.ProtocolChangeGroup.canonicalSection
          (K := K) visible) = SemidirectProduct.inr visible) ∧
    (∀ visible : H,
      Function.Bijective
        (CSComponentLocalGroup.protocolProjectionFiberLocalEquiv (K := K) H visible)) ∧
    (∀ (visible : H) (family : FixedFSemidirectProduct.ComponentGroup F K),
      (CSComponentLocalGroup.protocolLocalComponentAction (K := K) H visible)
        (CSComponentLocalGroup.protocolComponentLocalAutMulEquiv H family) =
      CSComponentLocalGroup.protocolComponentLocalAutMulEquiv H
        ((FixedFSemidirectProduct.componentAction (K := K) H visible) family)) := by
  exact ⟨(CSComponentLocalGroup.componentKernelMulEquiv (K := K) H).bijective,
    (CSComponentLocalGroup.protocolComponentLocalAutMulEquiv (K := K) H).bijective,
    (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv (K := K) H).bijective,
    CSComponentLocalGroup.protocolChangeLocal_visible H,
    CSComponentLocalGroup.protocolChangeLocal_section H,
    fun visible => (CSComponentLocalGroup.protocolProjectionFiberLocalEquiv
      (K := K) H visible).bijective,
    by
      intro visible family
      change (((CSComponentLocalGroup.protocolComponentLocalAutMulEquiv (K := K) H).symm.trans
        ((FixedFSemidirectProduct.componentAction (K := K) H) visible)).trans
        (CSComponentLocalGroup.protocolComponentLocalAutMulEquiv (K := K) H))
          ((CSComponentLocalGroup.protocolComponentLocalAutMulEquiv (K := K) H) family) = _
      simp⟩

/-- The same all-H recovery for the product lens uses its complete-update
graph component group, main-local automorphisms and visibly reindexed fibers. -/
theorem lens_local_change_group_recovery
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) :
    Function.Bijective
      (CSComponentLocalGroup.componentKernelMulEquiv (K := K)
        (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)) ∧
    Function.Bijective
      (CSComponentLocalGroup.lensComponentLocalAutMulEquiv (K := K) reference H) ∧
    Function.Bijective
      (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv (K := K) reference H) ∧
    (∀ change : FixedFLensGroupConnection.LensChangeGroup (K := K) H,
      (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv reference H change).right =
        FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
          (H := H) change.visible) ∧
    (∀ visible : H,
      CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv (K := K) reference H
        (FixedFLensGroupConnection.LensChangeGroup.canonicalSection
          (K := K) visible) =
        SemidirectProduct.inr
          (FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
            (H := H) visible)) ∧
    (∀ visible : H,
      Function.Bijective
        (CSComponentLocalGroup.lensProjectionFiberLocalEquiv (K := K)
          reference H visible)) ∧
    (∀ (visible : FixedFLensGroupConnection.completeUpdateGraphSubgroup H)
        (family : FixedFSemidirectProduct.ComponentGroup
          (FixedFFiniteExamples.completeUpdateGraph V) K),
      (CSComponentLocalGroup.lensLocalComponentAction (K := K) reference H visible)
        (CSComponentLocalGroup.lensComponentLocalAutMulEquiv reference H family) =
      CSComponentLocalGroup.lensComponentLocalAutMulEquiv reference H
        ((FixedFSemidirectProduct.componentAction (K := K)
          (FixedFLensGroupConnection.completeUpdateGraphSubgroup H) visible) family)) := by
  exact ⟨(CSComponentLocalGroup.componentKernelMulEquiv (K := K)
      (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)).bijective,
    (CSComponentLocalGroup.lensComponentLocalAutMulEquiv (K := K) reference H).bijective,
    (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv (K := K) reference H).bijective,
    CSComponentLocalGroup.lensChangeLocal_visible reference H,
    CSComponentLocalGroup.lensChangeLocal_section reference H,
    fun visible => (CSComponentLocalGroup.lensProjectionFiberLocalEquiv
      (K := K) reference H visible).bijective,
    by
      intro visible family
      change (((CSComponentLocalGroup.lensComponentLocalAutMulEquiv (K := K) reference H).symm.trans
        ((FixedFSemidirectProduct.componentAction (K := K)
          (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)) visible)).trans
        (CSComponentLocalGroup.lensComponentLocalAutMulEquiv (K := K) reference H))
          ((CSComponentLocalGroup.lensComponentLocalAutMulEquiv (K := K) reference H) family) = _
      simp⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
