import ResearchLean.AG.LocalSemanticReconstruction.CSComponentLocalGroup
import ResearchLean.AG.LocalSemanticReconstruction.LensFiniteDetermination
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: finite program outputs in both reversible CS change
families are read through the all-visible semidirect coordinate as actual
points of the common main local Hom, with source/destination reindexing. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
namespace CSProgramLocal
universe u

theorem protocol_change_local_point
    {F : FixedFDirectedMultigraph.{u,u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F))
    (change : FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K) H)
    (vertex : F.Vertex) (state output : K) :
    FiniteApplicationHomDecoders.decodeProtocolPoint
      (CSProtocolKernelLocal.fixedProtocolInput F)
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (change.visible.1.vertex vertex) state output
      (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
        (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv H change).left.hom) = true ↔
      change.stateEquiv vertex state = output := by
  let original := CSComponentLocalGroup.protocolChangeSemidirectMulEquiv H change
  change FiniteApplicationHomDecoders.decodeProtocolPoint
      (CSProtocolKernelLocal.fixedProtocolInput F)
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (change.visible.1.vertex vertex) state output
      (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
        (CSComponentLocalGroup.protocolComponentLocalAutMulEquiv H original.left).hom) = true ↔ _
  rw [CSComponentLocalGroup.protocolComponentLocal_point]
  let actual := FixedFProtocolGroupConnection.ProtocolChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H) change
  have hActual := (FixedFSemidirectProduct.actualEquivSemidirect (K := K) H).symm_apply_apply actual
  change FixedFSemidirectProduct.realize H original = actual at hActual
  have hperm := congrArg (fun x : FixedFRestrictedAutomorphism.FollowingGroup (K := K) H =>
    x.1.fiberPerm vertex) hActual
  change (FixedFSemidirectProduct.realize H original).1.fiberPerm vertex =
    actual.1.fiberPerm vertex at hperm
  rw [FixedFSemidirectProduct.realize_fiberPerm] at hperm
  have hright : original.right = change.visible := by
    have h := CSComponentLocalGroup.protocolChangeLocal_visible H change
    exact h
  rw [hright] at hperm
  rw [FixedFGraphAutomorphism.componentPerm_mk] at hperm
  have hcode : actual.1.fiberPerm vertex = change.stateEquiv vertex := by
    apply Equiv.ext
    intro state
    rfl
  rw [hcode] at hperm
  rw [hperm]


theorem lens_component_local_point
    {V K : Type u} [Finite K]
    (reference : V) (H : Subgroup (Equiv.Perm V))
    (family : FixedFSemidirectProduct.ComponentGroup
      (FixedFFiniteExamples.completeUpdateGraph V) K)
    (vertex : V) (state output : K) :
    FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
      (ULiftHom.objUp (LensRealization.product V K reference))
      (ULiftHom.objUp (LensRealization.product V K reference))
      (vertex,state) (vertex,output)
      (localHomTable (.lens ⟨V,reference⟩)
        (CSComponentLocalGroup.lensComponentLocalAutMulEquiv reference H family).hom) = true ↔
      family (fixedFComponentMk (FixedFFiniteExamples.completeUpdateGraph V) vertex)
        state = output := by
  let graphH := FixedFLensGroupConnection.completeUpdateGraphSubgroup H
  let kernel := (FixedFLensGroupConnection.LensChangeGroup.kernelMulEquiv
    (K := K) (H := H)).symm ((CSComponentLocalGroup.componentKernelMulEquiv
      (K := K) graphH) family)
  change FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
      (ULiftHom.objUp (LensRealization.product V K reference))
      (ULiftHom.objUp (LensRealization.product V K reference))
      (vertex,state) (vertex,output)
      (localHomTable (.lens ⟨V,reference⟩)
        (CSLensKernelLocal.kernelLocalAutMulEquiv ⟨V,reference⟩ H kernel).hom) = true ↔ _
  rw [CSLensKernelLocal.kernelLocalAut_point]
  have hgroup := (FixedFLensGroupConnection.LensChangeGroup.kernelMulEquiv
    (K := K) (H := H)).apply_symm_apply
      ((CSComponentLocalGroup.componentKernelMulEquiv (K := K) graphH) family)
  have hstate := congrArg
    (fun member : MonoidHom.ker
      (FixedFRestrictedAutomorphism.projection (K := K) graphH) =>
        member.1.1.h (vertex,state)) hgroup
  have hfamily := FixedFRestrictedKernelIdentification.componentKernelHom_fiberPerm
    (K := K) graphH family vertex
  have hhidden : (kernel.1.h (vertex,state)).2 =
      family (fixedFComponentMk (FixedFFiniteExamples.completeUpdateGraph V) vertex)
        state := by
    exact congrArg Prod.snd hstate |>.trans (congrArg (fun e : Equiv.Perm K => e state) hfamily)
  have hvisible : kernel.1.visible = 1 := by
    exact MonoidHom.mem_ker.mp kernel.property
  have hfirst : (kernel.1.h (vertex,state)).1 = vertex := by
    simpa [hvisible] using kernel.1.get_naturality (vertex,state)
  constructor
  · intro h
    have := congrArg Prod.snd h
    simpa [hhidden] using this
  · intro h
    apply Prod.ext
    · exact hfirst
    · exact hhidden.trans h


theorem lens_change_local_point
    {V K : Type u} [Finite K]
    (reference : V) (H : Subgroup (Equiv.Perm V))
    (change : FixedFLensGroupConnection.LensChangeGroup (K := K) H)
    (vertex : V) (state output : K) :
    FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
      (ULiftHom.objUp (LensRealization.product V K reference))
      (ULiftHom.objUp (LensRealization.product V K reference))
      (change.visible.1 vertex,state) (change.visible.1 vertex,output)
      (localHomTable (.lens ⟨V,reference⟩)
        (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv reference H change).left.hom) =
        true ↔ (change.h (vertex,state)).2 = output := by
  let graphH := FixedFLensGroupConnection.completeUpdateGraphSubgroup H
  let original := CSComponentLocalGroup.lensChangeSemidirectMulEquiv (K := K) H change
  change FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
      (ULiftHom.objUp (LensRealization.product V K reference))
      (ULiftHom.objUp (LensRealization.product V K reference))
      (change.visible.1 vertex,state) (change.visible.1 vertex,output)
      (localHomTable (.lens ⟨V,reference⟩)
        (CSComponentLocalGroup.lensComponentLocalAutMulEquiv reference H original.left).hom) =
        true ↔ _
  rw [lens_component_local_point]
  let actual := FixedFLensGroupConnection.LensChangeGroup.mulEquivFollowingGroup
    (K := K) (H := H) change
  have hActual := (FixedFSemidirectProduct.actualEquivSemidirect (K := K) graphH).symm_apply_apply actual
  change FixedFSemidirectProduct.realize graphH original = actual at hActual
  have hperm := congrArg (fun x : FixedFRestrictedAutomorphism.FollowingGroup (K := K) graphH =>
    x.1.fiberPerm vertex) hActual
  change (FixedFSemidirectProduct.realize graphH original).1.fiberPerm vertex =
    actual.1.fiberPerm vertex at hperm
  rw [FixedFSemidirectProduct.realize_fiberPerm] at hperm
  have hright : original.right =
      FixedFLensGroupConnection.LensChangeGroup.visibleMulEquivGraphSubgroup
        (H := H) change.visible := by
    exact CSComponentLocalGroup.lensChangeLocal_visible reference H change
  rw [hright, FixedFGraphAutomorphism.componentPerm_mk] at hperm
  have hcode : (actual.1.fiberPerm vertex) state = (change.h (vertex,state)).2 := rfl
  have h := (congrArg (fun e : Equiv.Perm K => e state) hperm).trans hcode
  change original.left (fixedFComponentMk
      (FixedFFiniteExamples.completeUpdateGraph V) (change.visible.1 vertex)) state =
      (change.h (vertex,state)).2 at h
  rw [h]


/-- Place an actual fixed-visible product-lens program output in the full
visible group without narrowing to the identity-visible kernel. -/
def lensChangeToFullGroup
    {V K : Type u} (reference : V) [Finite K]
    {visible : Equiv.Perm V}
    (change : FixedFLensConnection.LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible) :
    FixedFLensGroupConnection.LensChangeGroup (K := K) (⊤ : Subgroup (Equiv.Perm V)) where
  visible := ⟨visible, Subgroup.mem_top _⟩
  h := change.h
  get_naturality := change.get_naturality
  put_naturality := change.put_naturality

/-- Place an actual fixed-visible protocol program output in the full
visible group without narrowing to its kernel. -/
def protocolChangeToFullGroup
    {F : FixedFDirectedMultigraph.{u,u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    {visible : FixedFGraphAutomorphism F}
    (change : FixedFProtocolConnection.ProtocolInvertibleChange F K visible) :
    FixedFProtocolGroupConnection.ProtocolChangeGroup (K := K)
      (⊤ : Subgroup (FixedFGraphAutomorphism F)) where
  visible := ⟨visible, Subgroup.mem_top _⟩
  stateEquiv := change.stateEquiv
  edge_naturality := change.edge_naturality
  observation_naturality := change.observation_naturality



/-- Every successful finite product-lens change program output is read at
its visible-renamed reference point in the common main local Hom. -/
theorem lens_effectivenessProgram_main_point
    {V K : Type u} (reference : V) [Fintype K] [DecidableEq K]
    {visible : Equiv.Perm V}
    (table : {hidden // hidden ∈ LensFiniteDetermination.fullReferenceFiber (K := K)} → K)
    (change : FixedFLensConnection.LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (success : (LensFiniteDetermination.effectivenessProgram
      (V := V) (K := K) (reference := reference) (visible := visible)).extend? table =
        some change)
    (state output : K) :
    FiniteApplicationHomDecoders.decodeLensPoint ⟨V,reference⟩
      (ULiftHom.objUp (LensRealization.product V K reference))
      (ULiftHom.objUp (LensRealization.product V K reference))
      (visible reference,state) (visible reference,output)
      (localHomTable (.lens ⟨V,reference⟩)
        (CSComponentLocalGroup.lensChangeLocalSemidirectMulEquiv reference
          (⊤ : Subgroup (Equiv.Perm V))
          (lensChangeToFullGroup reference change)).left.hom) = true ↔
      table ⟨state, Finset.mem_univ _⟩ = output := by
  have hpoint := lens_change_local_point reference
    (⊤ : Subgroup (Equiv.Perm V)) (lensChangeToFullGroup reference change)
    reference state output
  have h := (LensFiniteDetermination.effectivenessProgram
    (V := V) (K := K) (reference := reference) (visible := visible )).restrict_eq_of_extend_eq_some
      table change success
  have hstate := congrFun h ⟨state, Finset.mem_univ _⟩
  have hvalue : (change.h (reference,state)).2 = table ⟨state, Finset.mem_univ _⟩ := by
    simpa [FiniteReading.restrict, LensFiniteDetermination.readProductLensChangeAt] using
      hstate
  have hvalue' : ((lensChangeToFullGroup reference change).h (reference,state)).2 =
      table ⟨state, Finset.mem_univ _⟩ := hvalue
  exact hpoint.trans (by rw [hvalue'])


/-- Every successful finite protocol change program output is read at its
visibly reindexed vertex in the common main local Hom. -/
theorem protocol_effectivenessProgram_main_point
    {F : FixedFDirectedMultigraph.{u,u}}
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    {K : Type u} [Fintype K] [DecidableEq K]
    {visible : FixedFGraphAutomorphism F}
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (table : {vertex // vertex ∈ ProtocolFiniteDetermination.readingVertices F S} →
      Equiv.Perm K)
    (change : FixedFProtocolConnection.ProtocolInvertibleChange F K visible)
    (success : (ProtocolFiniteDetermination.effectivenessProgram
      (F := F) (K := K) (automorphism := visible) S retains).extend? table =
        some change)
    (vertex : F.Vertex)
    (selected : vertex ∈ ProtocolFiniteDetermination.readingVertices F S)
    (state output : K) :
    FiniteApplicationHomDecoders.decodeProtocolPoint
      (CSProtocolKernelLocal.fixedProtocolInput F)
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (ULiftHom.objUp (FixedFProtocolConnection.realization F K))
      (visible.vertex vertex) state output
      (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
        (CSComponentLocalGroup.protocolChangeLocalSemidirectMulEquiv
          (⊤ : Subgroup (FixedFGraphAutomorphism F))
          (protocolChangeToFullGroup change)).left.hom) = true ↔
      (table ⟨vertex,selected⟩) state = output := by
  have hpoint := protocol_change_local_point
    (⊤ : Subgroup (FixedFGraphAutomorphism F))
    (protocolChangeToFullGroup change) vertex state output
  have h := (ProtocolFiniteDetermination.effectivenessProgram
    (F := F) (K := K) (automorphism := visible) S retains).restrict_eq_of_extend_eq_some
      table change success
  have hvertex := congrFun h ⟨vertex,selected⟩
  have hvalue : change.stateEquiv vertex state = (table ⟨vertex,selected⟩) state := by
    simpa [FiniteReading.restrict, ProtocolFiniteDetermination.readProtocolChangeAt]
      using congrArg (fun e : Equiv.Perm K => e state) hvertex
  have hvalue' : (protocolChangeToFullGroup change).stateEquiv vertex state =
      (table ⟨vertex,selected⟩) state := hvalue
  exact hpoint.trans (by rw [hvalue'])


/-- The finite product-lens change program rejects exactly non-bijective
hidden tables. -/
theorem lens_effectivenessProgram_reject_iff
    {V K : Type u} (reference : V) [Fintype K] [DecidableEq K]
    {visible : Equiv.Perm V}
    (table : {hidden // hidden ∈ LensFiniteDetermination.fullReferenceFiber (K := K)} → K) :
    (LensFiniteDetermination.effectivenessProgram
      (V := V) (K := K) (reference := reference) (visible := visible)).extend? table =
      none ↔ ¬ LensFiniteDetermination.TableCoherent table :=
  (LensFiniteDetermination.effectivenessProgram
    (V := V) (K := K) (reference := reference) (visible := visible)).extend_eq_none_iff table

/-- The finite protocol change program rejects exactly tables violating its
retained named-edge coherence. -/
theorem protocol_effectivenessProgram_reject_iff
    {F : FixedFDirectedMultigraph.{u,u}}
    [Fintype F.Vertex] [DecidableEq F.Vertex] [Fintype F.Edge]
    {K : Type u} [Fintype K] [DecidableEq K]
    {visible : FixedFGraphAutomorphism F}
    (S : F.Vertex → Prop) [DecidablePred S]
    (retains : InducedComponent.RetainsFullConnectivity F S)
    (table : {vertex // vertex ∈ ProtocolFiniteDetermination.readingVertices F S} →
      Equiv.Perm K) :
    (ProtocolFiniteDetermination.effectivenessProgram
      (F := F) (K := K) (automorphism := visible) S retains).extend? table = none ↔
      ¬ ProtocolFiniteDetermination.TableCoherent F S K table :=
  (ProtocolFiniteDetermination.effectivenessProgram
    (F := F) (K := K) (automorphism := visible) S retains).extend_eq_none_iff table
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSProgramLocal

end CSProgramLocal
end AAT.AG.LocalSemanticReconstruction
