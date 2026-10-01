import ResearchLean.AG.RelativeRepairComposition.AffineContextInput

/-!
# Every full shared edge coordinate retains its original name

The shared edge subtype and the original W edge names are bijective. In
particular pulling back a full vector loses neither a parallel edge name nor a
translation direction.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG

namespace FinitePresentationEmbedding
variable {G H : FiniteTransportPresentation.{uG}}
/-- Distinct typed original edge names remain distinct, including their endpoints. -/
theorem edge_name_injective (m : FinitePresentationEmbedding G H) :
    Function.Injective m.edgeName := by
  rintro ⟨i,j,e⟩ ⟨a,b,f⟩ h
  have hi := m.vertex_injective (congrArg Sigma.fst h)
  have hj : m.vertex j = m.vertex b := by
    cases hi
    exact congrArg (fun q => q.2.1) h
  have hj' := m.vertex_injective hj
  cases hi
  cases hj'
  have he : m.edge e = m.edge f := by
    exact eq_of_heq (Sigma.mk.inj_iff.mp (eq_of_heq (Sigma.mk.inj_iff.mp h).2)).2
  exact congrArg (fun q : G.Edge i j => (⟨i,j,q⟩ : EdgeName (K := G)))
    (m.edge_injective i j he)
end FinitePresentationEmbedding

namespace NativeAffine.AffineContextInput
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {W : FiniteTransportPresentation.{uG}}
variable {LW RW : ∀ {i j : W.Vertex}, W.Edge i j → Operations k A}
variable {cW : W.TwoCell → A} {PW : ClosedRegion W} {CW : Set (EdgeName (K := W))}
variable (I : AffineContextInput W LW RW cW PW CW)

/-- The full named shared edge image is a coordinate bijection with the original W. -/
noncomputable def sharedEdgeEquiv : EdgeName (K := W) ≃ I.shared.edges :=
  Equiv.ofBijective
    (fun e => ⟨I.embedding.edgeName e, by rw [I.shared_edges]; exact ⟨e,rfl⟩⟩)
    ⟨fun a b h => I.embedding.edge_name_injective (congrArg Subtype.val h), by
      rintro ⟨e,he⟩
      rw [I.shared_edges] at he
      obtain ⟨a,ha⟩ := he
      exact ⟨a,Subtype.ext ha⟩⟩

/-- Pullback reads every full actual translation vector at its same original edge name. -/
noncomputable def pullShared (v : I.shared.edges → A) : EdgeName (K := W) → A :=
  fun e => v (I.sharedEdgeEquiv e)

/-- The shared-coordinate pullback is bijective on whole translation vector families. -/
theorem pull_shared_bijective : Function.Bijective I.pullShared := by
  constructor
  · intro u v h
    funext e
    have he := congrFun h (I.sharedEdgeEquiv.symm e)
    simpa only [pullShared,Equiv.apply_symm_apply] using he
  · intro u
    refine ⟨fun e => u (I.sharedEdgeEquiv.symm e), ?_⟩
    funext e
    exact congrArg u (I.sharedEdgeEquiv.symm_apply_apply e)

end NativeAffine.AffineContextInput
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
