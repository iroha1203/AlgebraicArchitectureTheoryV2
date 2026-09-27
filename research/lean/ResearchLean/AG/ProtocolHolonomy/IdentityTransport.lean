import ResearchLean.AG.ProtocolHolonomy.HolonomyGenerators
import Formal.Util.AssertStandardAxioms

/-!
# Identity operations in the original reversible protocol input

For arbitrary named edges and a common state type, every forward and reverse
named operation is the identity. Hence every signed path and every original
named-edge holonomy generator acts by the identity on that same state type.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- The identity-operation instance of the original A-side primitive data. -/
def identityReversibleData
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w) :
    ReversibleData.{u, v, w} Q where
  Fiber := fun _ => K
  edgeEquiv := fun _ => Equiv.refl K

/-- Both orientations of every original named edge act trivially. -/
theorem identity_signedEdgeEquiv
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    (identityReversibleData Q K).signedEdgeEquiv e = Equiv.refl K := by
  cases e with
  | inl f =>
      rcases f with ⟨edge, hs, ht⟩
      cases hs
      cases ht
      rfl
  | inr f =>
      rcases f with ⟨edge, hs, ht⟩
      cases hs
      cases ht
      rfl

/-- Every signed named path, including reverse passages, acts trivially. -/
theorem identity_transport
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    {s t : Q.Vertex} (p : SignedPath Q s t) :
    (identityReversibleData Q K).transport p = Equiv.refl K := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) :=
    Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => rfl
  | cons p e ih =>
      change ((identityReversibleData Q K).transport p).trans
        ((identityReversibleData Q K).signedEdgeEquiv e) = Equiv.refl K
      rw [ih, identity_signedEdgeEquiv Q K e]
      rfl

/-- Every B1 edge-table monodromy is the identity permutation. -/
theorem identity_edgeMonodromyAt
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (R : RootedPaths Q) (j : FixedFComponent Q)
    (e : Q.Edge) (he : fixedFComponentMk Q (Q.source e) = j) :
    (identityReversibleData Q K).edgeMonodromyAt R j e he = 1 := by
  rw [← (identityReversibleData Q K).transport_edgeLoopAt R j e he,
    identity_transport]
  rfl

/-- Holonomy is trivial at every component for every choice of root paths. -/
theorem identity_holonomy
    (Q : FixedFDirectedMultigraph.{u, v}) (K : Type w)
    (R : RootedPaths Q) (j : FixedFComponent Q) :
    (identityReversibleData Q K).holonomy R j = ⊥ := by
  rw [(identityReversibleData Q K).holonomy_eq_rootedLoopTransportGroup R j]
  ext m
  constructor
  · rintro ⟨p, rfl⟩
    rw [identity_transport]
    exact Subgroup.one_mem _
  · intro hm
    have h : m = 1 := by simpa using hm
    subst m
    exact ⟨signedNil Q (R.root j), rfl⟩

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.identityReversibleData
#print axioms AAT.AG.ProtocolHolonomy.identity_signedEdgeEquiv
#print axioms AAT.AG.ProtocolHolonomy.identity_transport
#print axioms AAT.AG.ProtocolHolonomy.identity_edgeMonodromyAt
#print axioms AAT.AG.ProtocolHolonomy.identity_holonomy
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
