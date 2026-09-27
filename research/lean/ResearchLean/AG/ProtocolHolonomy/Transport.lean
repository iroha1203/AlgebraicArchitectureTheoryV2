import ResearchLean.AG.ProtocolHolonomy.Basic
import Mathlib.Combinatorics.Quiver.Symmetric
import Formal.Util.AssertStandardAxioms

/-!
# Transport along named operations in both directions

The original edge name and its endpoint equalities form the typed quiver.
Mathlib's symmetrification supplies the reverse edge; its action is the
inverse of the original reversible operation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- An original named edge with explicit endpoints. -/
abbrev TypedEdge (Q : FixedFDirectedMultigraph.{u, v})
    (s t : Q.Vertex) :=
  {e : Q.Edge // Q.source e = s ∧ Q.target e = t}

def typedQuiver (Q : FixedFDirectedMultigraph.{u, v}) : Quiver Q.Vertex where
  Hom := TypedEdge Q

/-- A path in the actual Mathlib symmetrification of the named graph. -/
abbrev SignedPath (Q : FixedFDirectedMultigraph.{u, v})
    (s t : Q.Vertex) :=
  @Quiver.Path (Quiver.Symmetrify Q.Vertex)
    (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)) s t

def signedNil (Q : FixedFDirectedMultigraph.{u, v}) (s : Q.Vertex) :
    SignedPath Q s s := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  exact Quiver.Path.nil

def signedCons (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : SignedPath Q s t)
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom t z) :
    SignedPath Q s z := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  exact p.cons e

def signedComp (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : SignedPath Q s t) (q : SignedPath Q t z) :
    SignedPath Q s z := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  exact p.comp q

def signedReverse (Q : FixedFDirectedMultigraph.{u, v})
    {s t : Q.Vertex} (p : SignedPath Q s t) : SignedPath Q t s := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  exact p.reverse

def signedToPath (Q : FixedFDirectedMultigraph.{u, v})
    {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    SignedPath Q s t := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  exact e.toPath

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}} (D : ReversibleData.{u, v, w} Q)

/-- The original edge action with its typed endpoint equalities. -/
def typedEdgeEquiv {s t : Q.Vertex} (e : TypedEdge Q s t) :
    D.Fiber s ≃ D.Fiber t :=
  (Equiv.cast (congrArg D.Fiber e.2.1.symm)).trans
    ((D.edgeEquiv e.1).trans (Equiv.cast (congrArg D.Fiber e.2.2)))

/-- A positive passage uses the edge action; a negative passage uses its
inverse. -/
def signedEdgeEquiv {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    D.Fiber s ≃ D.Fiber t :=
  match e with
  | Sum.inl f => D.typedEdgeEquiv f
  | Sum.inr f => (D.typedEdgeEquiv f).symm

@[simp] theorem signedEdgeEquiv_swap {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    D.signedEdgeEquiv e.swap = (D.signedEdgeEquiv e).symm := by
  cases e <;> rfl

/-- Compose the reversible action along a signed named path. -/
def transport {s t : Q.Vertex} (p : SignedPath Q s t) :
    D.Fiber s ≃ D.Fiber t :=
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  match p with
  | .nil => Equiv.refl _
  | .cons p e => (transport p).trans (D.signedEdgeEquiv e)

@[simp] theorem transport_nil (s : Q.Vertex) :
    D.transport (signedNil Q s) = Equiv.refl _ := rfl

@[simp] theorem transport_cons {s t z : Q.Vertex}
    (p : SignedPath Q s t)
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom t z) :
    D.transport (signedCons Q p e) =
      (D.transport p).trans (D.signedEdgeEquiv e) := rfl

@[simp] theorem transport_toPath {s t : Q.Vertex}
    (e : (@Quiver.symmetrifyQuiver Q.Vertex (typedQuiver Q)).Hom s t) :
    D.transport (signedToPath Q e) = D.signedEdgeEquiv e := by
  change (Equiv.refl _).trans (D.signedEdgeEquiv e) = _
  rfl

@[simp] theorem transport_positive {s t : Q.Vertex} (e : TypedEdge Q s t) :
    D.transport (signedToPath Q (Sum.inl e)) = D.typedEdgeEquiv e := rfl

@[simp] theorem transport_negative {s t : Q.Vertex} (e : TypedEdge Q s t) :
    D.transport (signedToPath Q (Sum.inr e)) = (D.typedEdgeEquiv e).symm := rfl

/-- Transport respects concatenation of signed paths. -/
theorem transport_comp {s t z : Q.Vertex}
    (p : SignedPath Q s t) (q : SignedPath Q t z) :
    D.transport (signedComp Q p q) = (D.transport p).trans (D.transport q) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction q with
  | nil => simp [signedComp, transport]
  | cons q e ih =>
    change D.transport (signedCons Q (signedComp Q p q) e) =
      (D.transport p).trans (D.transport (signedCons Q q e))
    rw [transport_cons, transport_cons, ih]
    exact (Equiv.trans_assoc _ _ _).symm

/-- Reversing a signed path inverts its transport. -/
theorem transport_reverse {s t : Q.Vertex} (p : SignedPath Q s t) :
    D.transport (signedReverse Q p) = (D.transport p).symm := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => rfl
  | cons p e ih =>
    change D.transport (signedComp Q (signedToPath Q e.swap) (signedReverse Q p)) =
      (D.transport (signedCons Q p e)).symm
    rw [transport_comp, transport_toPath, signedEdgeEquiv_swap, ih, transport_cons]
    rfl

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.transport_comp
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.transport_reverse
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy

end ReversibleData
end AAT.AG.ProtocolHolonomy
