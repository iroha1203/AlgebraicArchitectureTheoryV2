import ResearchLean.AG.LocalSemanticReconstruction.CSLensKernelLocal
import ResearchLean.AG.LocalSemanticReconstruction.CSProtocolKernelLocal
import ResearchLean.AG.RealizationReconstruction.FixedFSemidirectProduct
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the same fixed-F component groups and all-H semidirect
coordinates are transported through actual independent lens/protocol change
groups to automorphisms of the common main local Hom. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
namespace CSComponentLocalGroup
universe u v
variable {F : FixedFDirectedMultigraph.{u, v}} {K : Type u}

/-- The accepted component family is exactly the literal visible kernel. -/
noncomputable def componentKernelMulEquiv
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    FixedFSemidirectProduct.ComponentGroup F K ≃*
      MonoidHom.ker (FixedFRestrictedAutomorphism.projection (K := K) H) := by
  let hom : FixedFSemidirectProduct.ComponentGroup F K →*
      MonoidHom.ker (FixedFRestrictedAutomorphism.projection (K := K) H) := {
    toFun := fun family =>
      ⟨FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H family,
        FixedFRestrictedKernelIdentification.projection_componentKernelHom (K := K) H family⟩
    map_one' := by
      apply Subtype.ext
      exact map_one (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H)
    map_mul' := by
      intro first second
      apply Subtype.ext
      exact map_mul (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H)
        first second
  }
  apply MulEquiv.ofBijective hom
  constructor
  · intro first second equality
    apply FixedFRestrictedKernelIdentification.componentKernelHom_injective (K := K) H
    exact congrArg Subtype.val equality
  · intro kernel
    have hmem : kernel.1 ∈
        MonoidHom.range (FixedFRestrictedKernelIdentification.componentKernelHom (K := K) H) := by
      rw [FixedFRestrictedKernelIdentification.range_componentKernelHom_eq_ker_projection]
      exact kernel.property
    obtain ⟨family, heq⟩ := hmem
    refine ⟨family, ?_⟩
    apply Subtype.ext
    exact heq

/-- The component-indexed hidden permutations act as automorphisms in the
same main protocol local Hom as the independent all-H change group. -/
noncomputable def protocolComponentLocalAutMulEquiv
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    FixedFSemidirectProduct.ComponentGroup F K ≃*
      Aut ((reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).obj
        (ULiftHom.objUp (FixedFProtocolConnection.realization F K))) :=
  ((componentKernelMulEquiv (K := K) H).trans
    (FixedFProtocolGroupConnection.ProtocolChangeGroup.kernelMulEquiv (K := K) (H := H)).symm).trans
      (CSProtocolKernelLocal.kernelLocalAutMulEquiv (K := K) H)

/-- The complete-update graph has one component, and its component group is
the kernel automorphism group of the fixed product lens in the main reader. -/
noncomputable def lensComponentLocalAutMulEquiv
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) :
    FixedFSemidirectProduct.ComponentGroup
      (FixedFFiniteExamples.completeUpdateGraph V) K ≃*
      Aut ((reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).obj
        (ULiftHom.objUp (LensRealization.product V K reference))) :=
  ((componentKernelMulEquiv (K := K)
      (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)).trans
    (FixedFLensGroupConnection.LensChangeGroup.kernelMulEquiv
      (K := K) (H := H)).symm).trans
      (CSLensKernelLocal.kernelLocalAutMulEquiv
        (input := ⟨V, reference⟩) (K := K) H)


/-- The independent protocol all-H change group uses the accepted
destination-indexed semidirect coordinate and its full visible subgroup. -/
noncomputable def protocolChangeSemidirectMulEquiv
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K) H ≃*
      FixedFSemidirectProduct.Semidirect (K := K) H :=
  (FixedFProtocolGroupConnection.ProtocolChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H)).trans
      (FixedFSemidirectProduct.actualEquivSemidirect (K := K) H)

/-- The independent product-lens all-H change group has the same accepted
semidirect coordinate on its complete update operation graph. -/
noncomputable def lensChangeSemidirectMulEquiv
    {V K : Type u} [Finite K]
    (H : Subgroup (Equiv.Perm V)) :
    FixedFLensGroupConnection.LensChangeGroup (K := K) H ≃*
      FixedFSemidirectProduct.Semidirect (K := K)
        (FixedFLensGroupConnection.completeUpdateGraphSubgroup H) :=
  (FixedFLensGroupConnection.LensChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H)).trans
      (FixedFSemidirectProduct.actualEquivSemidirect (K := K)
        (FixedFLensGroupConnection.completeUpdateGraphSubgroup H))


/-- Transport a genuine group action along a constructed group equivalence. -/
private def transportAction {G A B : Type*} [Group G] [Group A] [Group B]
    (e : A ≃* B) (action : G →* MulAut A) : G →* MulAut B where
  toFun visible := (e.symm.trans (action visible)).trans e
  map_one' := by
    apply MulEquiv.ext
    intro value
    simp
  map_mul' first second := by
    apply MulEquiv.ext
    intro value
    simp [MulEquiv.trans_apply, map_mul]

/-- The fixed-F component reindexing action, now acting on automorphisms of
the main local protocol Hom. -/
noncomputable def protocolLocalComponentAction
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    H →* MulAut
      (Aut ((reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).obj
          (ULiftHom.objUp (FixedFProtocolConnection.realization F K)))) :=
  transportAction (protocolComponentLocalAutMulEquiv (K := K) H)
    (FixedFSemidirectProduct.componentAction (K := K) H)

/-- The complete-update component action, transported to automorphisms of
the same main local product-lens Hom. -/
noncomputable def lensLocalComponentAction
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) :
    FixedFLensGroupConnection.completeUpdateGraphSubgroup H →* MulAut
      (Aut ((reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).obj
        (ULiftHom.objUp (LensRealization.product V K reference)))) :=
  transportAction (lensComponentLocalAutMulEquiv (K := K) reference H)
    (FixedFSemidirectProduct.componentAction (K := K)
      (FixedFLensGroupConnection.completeUpdateGraphSubgroup H))


/-- The full independent protocol change group is the semidirect product of
main-local automorphisms and the original full visible subgroup. -/
noncomputable def protocolChangeLocalSemidirectMulEquiv
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K) H ≃*
      (Aut ((reading (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
        Parameter.{u, u})).obj
          (ULiftHom.objUp (FixedFProtocolConnection.realization F K)))
        ⋊[protocolLocalComponentAction (K := K) H] H) :=
  (protocolChangeSemidirectMulEquiv (K := K) H).trans
    (SemidirectProduct.congr
      (protocolComponentLocalAutMulEquiv (K := K) H) (MulEquiv.refl H)
      (by
        intro visible
        apply MulEquiv.ext
        intro family
        simp [protocolLocalComponentAction, transportAction]))

/-- The full independent product-lens change group has the matching
main-local automorphism and visible-coordinate semidirect form. -/
noncomputable def lensChangeLocalSemidirectMulEquiv
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) :
    FixedFLensGroupConnection.LensChangeGroup (K := K) H ≃*
      (Aut ((reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).obj
        (ULiftHom.objUp (LensRealization.product V K reference)))
        ⋊[lensLocalComponentAction (K := K) reference H]
          (FixedFLensGroupConnection.completeUpdateGraphSubgroup H)) :=
  (lensChangeSemidirectMulEquiv (K := K) H).trans
    (SemidirectProduct.congr
      (lensComponentLocalAutMulEquiv (K := K) reference H)
      (MulEquiv.refl (FixedFLensGroupConnection.completeUpdateGraphSubgroup H))
      (by
        intro visible
        apply MulEquiv.ext
        intro family
        simp [lensLocalComponentAction, transportAction]))


/-- Component families evaluate at their original protocol vertex through the
main local Hom, with the full visible subgroup still present. -/
theorem protocolComponentLocal_point
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F))
    (family : FixedFSemidirectProduct.ComponentGroup F K)
    (vertex : F.Vertex) (state output : K) :
    FiniteApplicationHomDecoders.decodeProtocolPoint
      (CSProtocolKernelLocal.fixedProtocolInput F)
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      vertex state output
      (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
        (protocolComponentLocalAutMulEquiv H family).hom) = true ↔
      family (fixedFComponentMk F vertex) state = output := by
  let kernel := (FixedFProtocolGroupConnection.ProtocolChangeGroup.kernelMulEquiv
    (K := K) (H := H)).symm ((componentKernelMulEquiv (K := K) H) family)
  change FiniteApplicationHomDecoders.decodeProtocolPoint
      (CSProtocolKernelLocal.fixedProtocolInput F)
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      vertex state output
      (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
        (CSProtocolKernelLocal.kernelLocalAutMulEquiv H kernel).hom) = true ↔ _
  rw [CSProtocolKernelLocal.kernelLocalAut_point H kernel vertex state output]
  have hgroup :=
    (FixedFProtocolGroupConnection.ProtocolChangeGroup.kernelMulEquiv
      (K := K) (H := H)).apply_symm_apply
        ((componentKernelMulEquiv (K := K) H) family)
  have hactual := congrArg
    (fun member : MonoidHom.ker
      (FixedFRestrictedAutomorphism.projection (K := K) H) =>
        member.1.1.fiberPerm vertex) hgroup
  have hcode :
      (FixedFProtocolGroupConnection.ProtocolChangeGroup.kernelMulEquiv
        (K := K) (H := H) kernel).1.1.fiberPerm vertex =
      kernel.1.stateEquiv vertex := by
    apply Equiv.ext
    intro state
    rfl
  have hfamily := FixedFRestrictedKernelIdentification.componentKernelHom_fiberPerm
    (K := K) H family vertex
  have hperm : kernel.1.stateEquiv vertex = family (fixedFComponentMk F vertex) := by
    exact hcode.symm.trans (hactual.trans hfamily)
  rw [hperm]


/-- The protocol semidirect coordinate keeps the actual visible change. -/
theorem protocolChangeLocal_visible
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F))
    (change : FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K) H) :
    (protocolChangeLocalSemidirectMulEquiv H change).right = change.visible := by
  let actual := FixedFProtocolGroupConnection.ProtocolChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H) change
  let entry := FixedFSemidirectProduct.actualEquivSemidirect (K := K) H actual
  have hinverse :=
    (FixedFSemidirectProduct.actualEquivSemidirect (K := K) H).symm_apply_apply actual
  have hp := congrArg (FixedFRestrictedAutomorphism.projection (K := K) H) hinverse
  change entry.right = FixedFRestrictedAutomorphism.projection (K := K) H actual at hp
  rw [FixedFProtocolGroupConnection.ProtocolChangeGroup.projection_compatibility] at hp
  exact hp


/-- The product-lens semidirect coordinate keeps the original visible
change through its faithful complete-update graph image. -/
theorem lensChangeLocal_visible
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V))
    (change : FixedFLensGroupConnection.LensChangeGroup (K := K) H) :
    (lensChangeLocalSemidirectMulEquiv (K := K) reference H change).right =
      FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
        (H := H) change.visible := by
  let actual := FixedFLensGroupConnection.LensChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H) change
  let graphH := FixedFLensGroupConnection.completeUpdateGraphSubgroup H
  let entry := FixedFSemidirectProduct.actualEquivSemidirect (K := K) graphH actual
  have hinverse :=
    (FixedFSemidirectProduct.actualEquivSemidirect (K := K) graphH).symm_apply_apply actual
  have hp := congrArg (FixedFRestrictedAutomorphism.projection (K := K) graphH) hinverse
  change entry.right = FixedFRestrictedAutomorphism.projection (K := K) graphH actual at hp
  rw [FixedFLensGroupConnection.LensChangeGroup.projection_compatibility] at hp
  exact hp


private theorem actualEquivSemidirect_section
    (H : Subgroup (FixedFGraphAutomorphism F))
    (visible : H) :
    FixedFSemidirectProduct.actualEquivSemidirect (K := K) H
      (FixedFRestrictedAutomorphism.canonicalSection (K := K) H visible) =
        SemidirectProduct.inr visible := by
  apply (FixedFSemidirectProduct.actualEquivSemidirect (K := K) H).symm.injective
  rw [(FixedFSemidirectProduct.actualEquivSemidirect (K := K) H).symm_apply_apply]
  change FixedFRestrictedAutomorphism.canonicalSection (K := K) H visible =
    FixedFSemidirectProduct.realize (K := K) H (SemidirectProduct.inr visible)
  simp [FixedFSemidirectProduct.realize]

/-- The protocol canonical section is the pure visible coordinate in the
same local semidirect representation. -/
theorem protocolChangeLocal_section
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    protocolChangeLocalSemidirectMulEquiv (K := K) H
      (FixedFProtocolGroupConnection.ProtocolChangeGroup.canonicalSection
        (K := K) visible) = SemidirectProduct.inr visible := by
  simp only [protocolChangeLocalSemidirectMulEquiv,
    protocolChangeSemidirectMulEquiv, MulEquiv.trans_apply]
  rw [FixedFProtocolGroupConnection.ProtocolChangeGroup.section_compatibility,
    actualEquivSemidirect_section]
  simp [SemidirectProduct.congr]


/-- The product-lens canonical section is the pure visible coordinate in
the same local semidirect representation. -/
theorem lensChangeLocal_section
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) (visible : H) :
    lensChangeLocalSemidirectMulEquiv (K := K) reference H
      (FixedFLensGroupConnection.LensChangeGroup.canonicalSection
        (K := K) visible) =
      SemidirectProduct.inr
        (FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
          (H := H) visible) := by
  simp only [lensChangeLocalSemidirectMulEquiv,
    lensChangeSemidirectMulEquiv, MulEquiv.trans_apply]
  rw [FixedFLensGroupConnection.LensChangeGroup.section_compatibility,
    actualEquivSemidirect_section]
  simp [SemidirectProduct.congr]


/-- Every literal protocol lift fiber is the matching fiber in the main-local
automorphism semidirect product. -/
noncomputable def protocolProjectionFiberLocalEquiv
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) (visible : H) :
    FixedFProtocolGroupConnection.ProtocolChangeGroup.ProjectionFiber
      (K := K) visible ≃
      {entry : Aut ((reading
          (Parameter.protocol (CSProtocolKernelLocal.fixedProtocolInput F) :
            Parameter.{u, u})).obj
            (ULiftHom.objUp (FixedFProtocolConnection.realization F K)))
          ⋊[protocolLocalComponentAction (K := K) H] H // entry.right = visible} where
  toFun change := ⟨protocolChangeLocalSemidirectMulEquiv H change.1, by
    rw [protocolChangeLocal_visible]
    exact change.2⟩
  invFun entry := ⟨(protocolChangeLocalSemidirectMulEquiv H).symm entry.1, by
    have h := protocolChangeLocal_visible (K := K) H
      ((protocolChangeLocalSemidirectMulEquiv H).symm entry.1)
    rw [(protocolChangeLocalSemidirectMulEquiv H).apply_symm_apply] at h
    exact h.symm.trans entry.2⟩
  left_inv change := by
    apply Subtype.ext
    exact (protocolChangeLocalSemidirectMulEquiv H).symm_apply_apply change.1
  right_inv entry := by
    apply Subtype.ext
    exact (protocolChangeLocalSemidirectMulEquiv H).apply_symm_apply entry.1


/-- Every literal product-lens lift fiber is the matching fiber in the
main-local automorphism semidirect product. -/
noncomputable def lensProjectionFiberLocalEquiv
    {V K : Type u} [Finite K] (reference : V)
    (H : Subgroup (Equiv.Perm V)) (visible : H) :
    FixedFLensGroupConnection.LensChangeGroup.ProjectionFiber
      (K := K) visible ≃
      {entry : Aut ((reading (Parameter.lens ⟨V, reference⟩ : Parameter.{u, u})).obj
          (ULiftHom.objUp (LensRealization.product V K reference)))
          ⋊[lensLocalComponentAction (K := K) reference H]
            (FixedFLensGroupConnection.completeUpdateGraphSubgroup H) //
        entry.right =
          FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
            (H := H) visible} where
  toFun change := ⟨lensChangeLocalSemidirectMulEquiv reference H change.1, by
    rw [lensChangeLocal_visible]
    exact congrArg
      (FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
        (H := H)) change.2⟩
  invFun entry := ⟨(lensChangeLocalSemidirectMulEquiv reference H).symm entry.1, by
    apply (FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
      (H := H)).injective
    have h := lensChangeLocal_visible (K := K) reference H
      ((lensChangeLocalSemidirectMulEquiv reference H).symm entry.1)
    rw [(lensChangeLocalSemidirectMulEquiv reference H).apply_symm_apply] at h
    exact h.symm.trans entry.2⟩
  left_inv change := by
    apply Subtype.ext
    exact (lensChangeLocalSemidirectMulEquiv reference H).symm_apply_apply change.1
  right_inv entry := by
    apply Subtype.ext
    exact (lensChangeLocalSemidirectMulEquiv reference H).apply_symm_apply entry.1


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSComponentLocalGroup

end CSComponentLocalGroup
end AAT.AG.LocalSemanticReconstruction
