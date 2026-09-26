import ResearchLean.AG.RealizationReconstruction.FixedFProtocolGroupConnection
import ResearchLean.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: identify the literal all-H protocol visible kernel
with automorphisms of the fixed semantic protocol realization, transport it
through the common main reader, and evaluate original vertex state maps.
Generator squares are extended over all quotient executions by the accepted
protocol reconstruction rather than installed as complete naturality fields. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open FixedFProtocolConnection
attribute [local instance] uliftCategory
universe u
namespace CSProtocolKernelLocal
local instance fixedFProtocolQuiver (F : FixedFDirectedMultigraph.{u, u}) :
    Quiver F.Vertex where
  Hom := TypedEdge F
variable {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
  {K : Type u} [Finite K]
  (H : Subgroup (FixedFGraphAutomorphism F))
private abbrev ProtocolKernel := MonoidHom.ker
  (FixedFProtocolGroupConnection.ProtocolChangeGroup.projection (K := K) (H := H))

/-- A visible-identity protocol change gives a semantic automorphism via
all-path extension of its generated vertex maps. -/
noncomputable def kernelToAut (element : ProtocolKernel (K := K) H) :
    Aut (FixedFProtocolConnection.realization F K) := by
  let change := element.1
  let forward : FixedFProtocolConnection.realization F K ⟶
      FixedFProtocolConnection.realization F K :=
    ProtocolRealization.ext {
      component := fun vertex => change.stateEquiv vertex
      edge_naturality := by
        intro source target edge
        funext state
        exact congrArg (fun permutation : Equiv.Perm K => permutation state)
          (change.stateEquiv_edge_constant edge)
      observation_naturality := by
        intro vertex
        funext state
        exact Subsingleton.elim _ _
    }
  let backward : FixedFProtocolConnection.realization F K ⟶
      FixedFProtocolConnection.realization F K :=
    ProtocolRealization.ext {
      component := fun vertex => (change.stateEquiv vertex).symm
      edge_naturality := by
        intro source target edge
        funext state
        exact congrArg (fun permutation : Equiv.Perm K => permutation.symm state)
          (change.stateEquiv_edge_constant edge)
      observation_naturality := by
        intro vertex
        funext state
        exact Subsingleton.elim _ _
    }
  exact {
    hom := forward
    inv := backward
    hom_inv_id := by
      apply ProtocolRealization.Hom.ext
      ext vertex state
      exact (change.stateEquiv vertex.as).symm_apply_apply state
    inv_hom_id := by
      apply ProtocolRealization.Hom.ext
      ext vertex state
      exact (change.stateEquiv vertex.as).apply_symm_apply state
  }

/-- A semantic protocol automorphism restricts to the independent
visible-identity change and its original named-edge squares. -/
noncomputable def autToKernel
    (aut : Aut (realization F K)) : ProtocolKernel (K := K) H := by
  let componentEquiv : F.Vertex → Equiv.Perm K := fun vertex => {
    toFun := (ProtocolRealization.res aut.hom).component vertex
    invFun := (ProtocolRealization.res aut.inv).component vertex
    left_inv := by
      intro state
      have h := congrArg
        (fun morphism : realization F K ⟶ realization F K =>
          ProtocolRealization.app morphism ((schema F).vertexObject vertex) state)
        aut.hom_inv_id
      exact h
    right_inv := by
      intro state
      have h := congrArg
        (fun morphism : realization F K ⟶ realization F K =>
          ProtocolRealization.app morphism ((schema F).vertexObject vertex) state)
        aut.inv_hom_id
      exact h
  }
  refine ⟨{
    visible := 1
    stateEquiv := componentEquiv
    edge_naturality := by
      intro source target edge state
      have h := congrFun ((ProtocolRealization.res aut.hom).edge_naturality edge) state
      simpa [componentEquiv, realization_edgeAction] using h
    observation_naturality := by
      intro vertex state
      exact Subsingleton.elim _ _
  }, ?_⟩
  rfl


/-- The literal visible-identity protocol kernel is the automorphism group
of the fixed semantic protocol realization. -/
noncomputable def kernelAutMulEquiv :
    ProtocolKernel (K := K) H ≃* Aut (realization F K) where
  toFun := kernelToAut H
  invFun := autToKernel H
  left_inv element := by
    apply Subtype.ext
    apply FixedFProtocolGroupConnection.ProtocolChangeGroup.ext
    · exact (MonoidHom.mem_ker.mp element.property).symm
    · funext vertex
      apply Equiv.ext
      intro state
      rfl
  right_inv aut := by
    apply Aut.ext
    apply ProtocolRealization.Hom.ext
    ext vertex state
    rfl
  map_mul' first second := by
    apply Aut.ext
    apply ProtocolRealization.Hom.ext
    ext vertex state
    have hv : second.1.visible = 1 := MonoidHom.mem_ker.mp second.property
    change first.1.stateEquiv (second.1.visible.1.vertex vertex.as)
        (second.1.stateEquiv vertex.as state) =
      first.1.stateEquiv vertex.as (second.1.stateEquiv vertex.as state)
    rw [hv]
    rfl


/-- The independently fixed protocol family parameter for the same operation
graph and terminal observation that define the change group. -/
def fixedProtocolInput (F : FixedFDirectedMultigraph.{u, u})
    [Finite F.Vertex] [Finite F.Edge] : ProtocolFamilyInput.{u} :=
  ⟨schema F, observationFunctor F⟩

/-- Transport the literal protocol kernel through the common main local
reader while retaining its complete automorphism Hom and inverse. -/
noncomputable def kernelLocalAutMulEquiv
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F)) :
    MonoidHom.ker
      (FixedFProtocolGroupConnection.ProtocolChangeGroup.projection (K := K) (H := H)) ≃*
      Aut ((reading (Parameter.protocol (fixedProtocolInput F) : Parameter.{u, u})).obj
        (ULiftHom.objUp (realization F K))) := by
  let upEquiv := CategoryTheory.ULiftHom.equiv
    (C := ProtocolRealization (schema F) (observationFunctor F))
  let mainEquiv := equivalence
    (Parameter.protocol (fixedProtocolInput F) : Parameter.{u, u})
  exact (kernelAutMulEquiv (K := K) H).trans
    ((upEquiv.fullyFaithfulFunctor.autMulEquivOfFullyFaithful
      (realization F K)).trans
      (mainEquiv.fullyFaithfulFunctor.autMulEquivOfFullyFaithful
        (ULiftHom.objUp (realization F K))))


/-- A kernel automorphism at the main local protocol Hom evaluates to its
original vertex-indexed hidden-state permutation. -/
theorem kernelLocalAut_point
    {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
    {K : Type u} [Finite K]
    (H : Subgroup (FixedFGraphAutomorphism F))
    (element : MonoidHom.ker
      (FixedFProtocolGroupConnection.ProtocolChangeGroup.projection (K := K) (H := H)))
    (vertex : F.Vertex) (state output : K) :
    FiniteApplicationHomDecoders.decodeProtocolPoint (fixedProtocolInput F)
      (ULiftHom.objUp (realization F K))
      (ULiftHom.objUp (realization F K)) vertex state output
      (localHomTable (.protocol (fixedProtocolInput F))
        (kernelLocalAutMulEquiv H element).hom) = true ↔
      element.1.stateEquiv vertex state = output := by
  change FiniteApplicationHomDecoders.decodeProtocolPoint (fixedProtocolInput F)
      (ULiftHom.objUp (realization F K))
      (ULiftHom.objUp (realization F K)) vertex state output
      (localHomTable (.protocol (fixedProtocolInput F))
        ((reading (.protocol (fixedProtocolInput F))).map
          (ULift.up ((kernelToAut (K := K) H element).hom)))) = true ↔ _
  exact FiniteApplicationHomDecoders.protocolPoint_decode (fixedProtocolInput F)
    (ULift.up ((kernelToAut (K := K) H element).hom)) vertex state output


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSProtocolKernelLocal

end CSProtocolKernelLocal
end AAT.AG.LocalSemanticReconstruction
