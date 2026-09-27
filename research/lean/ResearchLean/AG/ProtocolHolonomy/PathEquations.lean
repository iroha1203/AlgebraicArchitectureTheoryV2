import ResearchLean.AG.ProtocolHolonomy.Transport
import Mathlib.Combinatorics.Quiver.Prefunctor
import Mathlib.Data.Finite.Card
import Mathlib.Algebra.Group.Subgroup.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Finite named path equations for reversible protocols

The equation family is finite, while its generated path congruence need not be.
Each equation is between directed paths in the original named graph.  The
signed quiver remains a separate transport construction.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Directed paths on the original named graph. -/
abbrev PositivePath (Q : FixedFDirectedMultigraph.{u, v})
    (s t : Q.Vertex) := @Quiver.Path Q.Vertex (typedQuiver Q) s t

def positiveNil (Q : FixedFDirectedMultigraph.{u, v}) (s : Q.Vertex) :
    PositivePath Q s s := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact Quiver.Path.nil

def positiveCons (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : PositivePath Q s t)
    (e : TypedEdge Q t z) : PositivePath Q s z := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact p.cons e

def positiveComp (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : PositivePath Q s t)
    (q : PositivePath Q t z) : PositivePath Q s z := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact p.comp q

/-- Include an original directed execution in the signed transport graph. -/
def positiveToSigned (Q : FixedFDirectedMultigraph.{u, v})
    {s t : Q.Vertex} (p : PositivePath Q s t) : SignedPath Q s t := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction p with
  | nil => exact signedNil Q _
  | cons p e ih => exact signedCons Q ih (Sum.inl e)

theorem positiveToSigned_comp (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : PositivePath Q s t) (q : PositivePath Q t z) :
    positiveToSigned Q (positiveComp Q p q) =
      signedComp Q (positiveToSigned Q p) (positiveToSigned Q q) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
  induction q with
  | nil => rfl
  | cons q e ih =>
    change signedCons Q (positiveToSigned Q (positiveComp Q p q)) (Sum.inl e) =
      signedComp Q (positiveToSigned Q p)
        (signedCons Q (positiveToSigned Q q) (Sum.inl e))
    rw [ih]
    rfl

/-- Rename an original edge using both endpoint laws of a graph automorphism. -/
def renameTypedEdge {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (e : TypedEdge Q s t) : TypedEdge Q (g.vertex s) (g.vertex t) :=
  ⟨g.edge e.1,
    by rw [g.source_rename, e.2.1],
    by rw [g.target_rename, e.2.2]⟩

/-- Rename every original edge of a directed execution. -/
def renamePositive {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t : Q.Vertex}
    (p : PositivePath Q s t) :
    PositivePath Q (g.vertex s) (g.vertex t) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  induction p with
  | nil => exact positiveNil Q _
  | cons p e ih => exact positiveCons Q ih (renameTypedEdge g e)

theorem renamePositive_comp {Q : FixedFDirectedMultigraph.{u, v}}
    (g : FixedFGraphAutomorphism Q) {s t z : Q.Vertex}
    (p : PositivePath Q s t) (q : PositivePath Q t z) :
    renamePositive g (positiveComp Q p q) =
      positiveComp Q (renamePositive g p) (renamePositive g q) := by
  letI : Quiver Q.Vertex := typedQuiver Q
  induction q with
  | nil => rfl
  | cons q e ih =>
    change positiveCons Q (renamePositive g (positiveComp Q p q))
        (renameTypedEdge g e) =
      positiveComp Q (renamePositive g p)
        (positiveCons Q (renamePositive g q) (renameTypedEdge g e))
    rw [ih]
    rfl

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}} (D : ReversibleData.{u, v, w} Q)

/-- Evaluation of a directed path uses the already constructed signed
transport, with only original forward edges. -/
def positiveTransport {s t : Q.Vertex} (p : PositivePath Q s t) :
    D.Fiber s ≃ D.Fiber t := D.transport (positiveToSigned Q p)

@[simp] theorem positiveTransport_nil (s : Q.Vertex) :
    D.positiveTransport (positiveNil Q s) = Equiv.refl _ := rfl

@[simp] theorem positiveTransport_cons {s t z : Q.Vertex}
    (p : PositivePath Q s t) (e : TypedEdge Q t z) :
    D.positiveTransport (positiveCons Q p e) =
      (D.positiveTransport p).trans (D.typedEdgeEquiv e) := rfl

theorem positiveTransport_comp {s t z : Q.Vertex}
    (p : PositivePath Q s t) (q : PositivePath Q t z) :
    D.positiveTransport (positiveComp Q p q) =
      (D.positiveTransport p).trans (D.positiveTransport q) := by
  change D.transport (positiveToSigned Q (positiveComp Q p q)) = _
  rw [positiveToSigned_comp, D.transport_comp]
  rfl

end ReversibleData

/-- A finite family of parallel equations among original directed paths. -/
structure PathEquations (Q : FixedFDirectedMultigraph.{u, v}) where
  Index : Type (max u v)
  finiteIndex : Finite Index
  source : Index → Q.Vertex
  target : Index → Q.Vertex
  left : (r : Index) → PositivePath Q (source r) (target r)
  right : (r : Index) → PositivePath Q (source r) (target r)

namespace PathEquations

variable {Q : FixedFDirectedMultigraph.{u, v}} (eqs : PathEquations Q)

instance : Finite eqs.Index := eqs.finiteIndex

/-- The least path congruence generated by the specified finite equations. -/
inductive Congruent : {s t : Q.Vertex} →
    PositivePath Q s t → PositivePath Q s t → Prop where
  | equation (r : eqs.Index) : Congruent (eqs.left r) (eqs.right r)
  | refl {s t : Q.Vertex} (p : PositivePath Q s t) : Congruent p p
  | symm {s t : Q.Vertex} {p q : PositivePath Q s t} :
      Congruent p q → Congruent q p
  | trans {s t : Q.Vertex} {p q r : PositivePath Q s t} :
      Congruent p q → Congruent q r → Congruent p r
  | comp {s t z : Q.Vertex}
      {p p' : PositivePath Q s t} {q q' : PositivePath Q t z} :
      Congruent p p' → Congruent q q' →
        Congruent (positiveComp Q p q) (positiveComp Q p' q')

/-- The finite generator criterion for preserving the generated congruence. -/
def PreservesGenerators (g : FixedFGraphAutomorphism Q) : Prop :=
  ∀ r : eqs.Index,
    eqs.Congruent (renamePositive g (eqs.left r))
      (renamePositive g (eqs.right r))

/-- Preservation of every consequence of the path equations. -/
def PreservesCongruence (g : FixedFGraphAutomorphism Q) : Prop :=
  ∀ {s t : Q.Vertex} {p q : PositivePath Q s t},
    eqs.Congruent p q →
      eqs.Congruent (renamePositive g p) (renamePositive g q)

theorem preservesCongruence_iff_generators (g : FixedFGraphAutomorphism Q) :
    eqs.PreservesCongruence g ↔ eqs.PreservesGenerators g := by
  constructor
  · intro h r
    exact h (.equation r)
  · intro h s t p q hp
    induction hp with
    | equation r => exact h r
    | refl p => exact .refl _
    | symm _ ih => exact .symm ih
    | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
    | comp h₁ h₂ ih₁ ih₂ =>
        rw [renamePositive_comp, renamePositive_comp]
        exact .comp ih₁ ih₂

end PathEquations

/-- Finite primitive data, including the required truth of every authored
path equation under the edge actions. -/
structure FiniteProtocolInput (Q : FixedFDirectedMultigraph.{u, v}) where
  data : ReversibleData.{u, v, w} Q
  finiteVertex : Finite Q.Vertex
  finiteEdge : Finite Q.Edge
  finiteFiber : ∀ x, Finite (data.Fiber x)
  equations : PathEquations Q
  satisfies : ∀ r : equations.Index,
    data.positiveTransport (equations.left r) =
      data.positiveTransport (equations.right r)
  H : Subgroup (FixedFGraphAutomorphism Q)
  renaming_preserves : ∀ g, g ∈ H → equations.PreservesGenerators g

namespace FiniteProtocolInput

variable {Q : FixedFDirectedMultigraph.{u, v}} (P : FiniteProtocolInput.{u, v, w} Q)

instance : Finite Q.Vertex := P.finiteVertex
instance : Finite Q.Edge := P.finiteEdge
instance (x : Q.Vertex) : Finite (P.data.Fiber x) := P.finiteFiber x

/-- The primitive equation condition extends to the full generated path
congruence by the actual path action. -/
theorem preserves_congruence {s t : Q.Vertex}
    {p q : PositivePath Q s t} (h : P.equations.Congruent p q) :
    P.data.positiveTransport p = P.data.positiveTransport q := by
  induction h with
  | equation r => exact P.satisfies r
  | refl p => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp h₁ h₂ ih₁ ih₂ =>
      rw [P.data.positiveTransport_comp, P.data.positiveTransport_comp,
        ih₁, ih₂]

/-- Every selected visible change preserves the full generated congruence,
not merely the displayed finite list. -/
theorem visible_preserves_congruence (g : FixedFGraphAutomorphism Q)
    (hg : g ∈ P.H) : P.equations.PreservesCongruence g :=
  (P.equations.preservesCongruence_iff_generators g).2
    (P.renaming_preserves g hg)

end FiniteProtocolInput

#print axioms AAT.AG.ProtocolHolonomy.PathEquations.Congruent
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.positiveTransport_comp
#print axioms AAT.AG.ProtocolHolonomy.PathEquations.preservesCongruence_iff_generators
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.preserves_congruence
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.visible_preserves_congruence
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
end AAT.AG.ProtocolHolonomy
