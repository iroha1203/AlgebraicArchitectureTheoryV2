import ResearchLean.AG.LocalSemanticReconstruction.CSProtocolKernelLocal
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolConnection
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the original visible protocol adapter square, including its
vertex reindexing, is read as an equivalence of point graph queries of the
one common main local Hom. The adapters remain arbitrary semantic morphisms. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open FiniteApplicationHomDecoders
namespace CSProtocolAdapterLocal
universe u
variable {F : FixedFDirectedMultigraph.{u, u}} [Finite F.Vertex] [Finite F.Edge]
  {KX KY : Type u} [Finite KX] [Finite KY]
  {automorphism : FixedFGraphAutomorphism F}
/-- The original adapter square is equivalent to its correctly reindexed
family of main local primitive point-query equivalences. -/
theorem adapter_square_iff_main_points
    (q q' : FixedFProtocolConnection.realization F KX ⟶
      FixedFProtocolConnection.realization F KY)
    (a : FixedFProtocolConnection.ProtocolInvertibleChange F KX automorphism)
    (b : FixedFProtocolConnection.ProtocolInvertibleChange F KY automorphism) :
    FixedFProtocolConnection.ProtocolChangeAdapterSquare q q' a b ↔
      ∀ vertex state output,
        (decodeProtocolPoint (CSProtocolKernelLocal.fixedProtocolInput F)
          (ULiftHom.objUp (FixedFProtocolConnection.realization F KX))
          (ULiftHom.objUp (FixedFProtocolConnection.realization F KY))
          vertex state output
          (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
            ((reading (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))).map
              (ULift.up q))) = true ↔
        decodeProtocolPoint (CSProtocolKernelLocal.fixedProtocolInput F)
          (ULiftHom.objUp (FixedFProtocolConnection.realization F KX))
          (ULiftHom.objUp (FixedFProtocolConnection.realization F KY))
          (automorphism.vertex vertex) (a.stateEquiv vertex state)
          (b.stateEquiv vertex output)
          (localHomTable (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))
            ((reading (.protocol (CSProtocolKernelLocal.fixedProtocolInput F))).map
              (ULift.up q'))) = true) := by
  rw [FixedFProtocolConnection.protocolChangeAdapterSquare_iff_vertices]
  simp_rw [protocolPoint_decode]
  constructor
  · intro hs vertex state output
    constructor
    · intro h
      simpa [← h] using (hs vertex state).symm
    · intro h
      apply (b.stateEquiv vertex).injective
      calc
        b.stateEquiv vertex
            (ProtocolRealization.app q ((FixedFProtocolConnection.schema F).vertexObject vertex) state) =
          ProtocolRealization.app q'
            ((FixedFProtocolConnection.schema F).vertexObject (automorphism.vertex vertex))
            (a.stateEquiv vertex state) := hs vertex state
        _ = b.stateEquiv vertex output := h
  · intro hs vertex state
    exact (hs vertex state
      (ProtocolRealization.app q ((FixedFProtocolConnection.schema F).vertexObject vertex) state)).1 rfl |>.symm

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSProtocolAdapterLocal

end CSProtocolAdapterLocal
end AAT.AG.LocalSemanticReconstruction
