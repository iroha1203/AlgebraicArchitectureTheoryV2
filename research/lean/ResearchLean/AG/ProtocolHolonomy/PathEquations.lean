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

## Implementation notes

The authored equations use only original directed paths.  Using the signed
transport quiver as the equation syntax would add formal inverse operations
to the input language.  The inductive congruence is the contextual closure
needed before the later comparison with the independent quotient execution
category; it does not assume equality of realized actions.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

/-- Directed paths on the original named graph. -/
abbrev PositivePath (Q : FixedFDirectedMultigraph.{u, v})
    (s t : Q.Vertex) := @Quiver.Path Q.Vertex (typedQuiver Q) s t

/-- The empty original execution. -/
def positiveNil (Q : FixedFDirectedMultigraph.{u, v}) (s : Q.Vertex) :
    PositivePath Q s s := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact Quiver.Path.nil

/-- Append one original named operation to a directed execution. -/
def positiveCons (Q : FixedFDirectedMultigraph.{u, v})
    {s t z : Q.Vertex} (p : PositivePath Q s t)
    (e : TypedEdge Q t z) : PositivePath Q s z := by
  letI : Quiver Q.Vertex := typedQuiver Q
  exact p.cons e

/-- Concatenate two original directed executions. -/
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

/-- The positive-to-signed API respects concatenation. -/
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

/-- Renaming original operations respects execution concatenation. -/
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

/-- Normalize the empty execution's action to the identity equivalence. -/
@[simp] theorem positiveTransport_nil (s : Q.Vertex) :
    D.positiveTransport (positiveNil Q s) = Equiv.refl _ := rfl

/-- Normalize appended-edge transport to the earlier action followed by the
actual edge equivalence. -/
@[simp] theorem positiveTransport_cons {s t z : Q.Vertex}
    (p : PositivePath Q s t) (e : TypedEdge Q t z) :
    D.positiveTransport (positiveCons Q p e) =
      (D.positiveTransport p).trans (D.typedEdgeEquiv e) := rfl

/-- The directed-path action respects concatenation. -/
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

/-- Expose finiteness of the authored equation indices. -/
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

/-- A graph rename sends every authored equation into its generated path
congruence, without requiring permutation of the displayed list. -/
def PreservesGenerators (g : FixedFGraphAutomorphism Q) : Prop :=
  ∀ r : eqs.Index,
    eqs.Congruent (renamePositive g (eqs.left r))
      (renamePositive g (eqs.right r))

/-- A graph rename preserves all paths related by the generated congruence. -/
def PreservesCongruence (g : FixedFGraphAutomorphism Q) : Prop :=
  ∀ {s t : Q.Vertex} {p q : PositivePath Q s t},
    eqs.Congruent p q →
      eqs.Congruent (renamePositive g p) (renamePositive g q)

/-- API characterization: the finite generator test is equivalent to
preserving every consequence of the equations. -/
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

/-- Expose the finite control points of the A-side input. -/
instance : Finite Q.Vertex := P.finiteVertex
/-- Expose the finite original operation names of the A-side input. -/
instance : Finite Q.Edge := P.finiteEdge
/-- Expose finite states at each control point. -/
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

/-! ## Nonvacuity examples for the new path predicates -/

/-- Two distinct named loops at one control point for nonvacuity checks. -/
private def witnessGraph : FixedFDirectedMultigraph where
  Vertex := PUnit
  Edge := Bool
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit

/-- Retain the chosen loop name in the typed edge. -/
private def witnessEdge (e : Bool) :
    TypedEdge witnessGraph PUnit.unit PUnit.unit := ⟨e, rfl, rfl⟩

/-- The one-step execution of either named loop. -/
private def witnessPath (e : Bool) :
    PositivePath witnessGraph PUnit.unit PUnit.unit :=
  positiveCons witnessGraph (positiveNil witnessGraph PUnit.unit) (witnessEdge e)

/-- A nonempty equation family identifying only the first loop with id. -/
private def witnessEquations : PathEquations witnessGraph where
  Index := PUnit
  finiteIndex := inferInstance
  source := fun _ => PUnit.unit
  target := fun _ => PUnit.unit
  left := fun _ => witnessPath false
  right := fun _ => positiveNil witnessGraph PUnit.unit

/-- A separating action: the first loop acts identically, the second swaps
the two states. -/
private def witnessData : ReversibleData witnessGraph where
  Fiber := fun _ => Bool
  edgeEquiv := fun e =>
    match e with
    | false => Equiv.refl Bool
    | true => Equiv.swap false true

/-- The authored equation gives a positive congruence instance. -/
example : witnessEquations.Congruent (witnessPath false)
    (positiveNil witnessGraph PUnit.unit) :=
  .equation PUnit.unit

/-- The other named loop is not identified with the empty path by the
equation on the first loop. -/
private theorem witness_not_congruent :
    ¬ witnessEquations.Congruent (witnessPath true)
      (positiveNil witnessGraph PUnit.unit) := by
  intro h
  have actionEq : ∀ {s t : witnessGraph.Vertex}
      {p q : PositivePath witnessGraph s t},
      witnessEquations.Congruent p q →
        witnessData.positiveTransport p = witnessData.positiveTransport q := by
    intro s t p q hp
    induction hp with
    | equation r =>
        cases r
        apply Equiv.ext
        intro x
        cases x <;> rfl
    | refl p => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | comp h₁ h₂ ih₁ ih₂ =>
        rw [witnessData.positiveTransport_comp,
          witnessData.positiveTransport_comp, ih₁, ih₂]
  have hfalse := congrArg
    (fun f : Bool ≃ Bool => f false) (actionEq h)
  change true = false at hfalse
  cases hfalse

/-- A congruence instance that does not hold. -/
example : ¬ witnessEquations.Congruent (witnessPath true)
    (positiveNil witnessGraph PUnit.unit) := witness_not_congruent

/-- The graph automorphism that exchanges the two original operation names. -/
private noncomputable def witnessSwap : FixedFGraphAutomorphism witnessGraph where
  vertex := Equiv.refl PUnit
  edge := by classical exact Equiv.swap false true
  source_rename := by intro e; rfl
  target_rename := by intro e; rfl

/-- The identity visible change preserves a nonempty equation family. -/
example : witnessEquations.PreservesGenerators (1 : FixedFGraphAutomorphism witnessGraph) := by
  intro r
  cases r
  exact .equation PUnit.unit

/-- Swapping the two distinct loop names fails the generator criterion. -/
private theorem witness_swap_not_preserves_generators :
    ¬ witnessEquations.PreservesGenerators witnessSwap := by
  intro h
  have hleft : renamePositive witnessSwap (witnessPath false) =
      witnessPath true := by
    simp [witnessPath, renamePositive, positiveCons, positiveNil,
      witnessSwap, renameTypedEdge, witnessEdge]
  have hright : renamePositive witnessSwap
      (positiveNil witnessGraph PUnit.unit) =
      positiveNil witnessGraph PUnit.unit := rfl
  have hr := h PUnit.unit
  change witnessEquations.Congruent
    (renamePositive witnessSwap (witnessPath false))
    (renamePositive witnessSwap (positiveNil witnessGraph PUnit.unit)) at hr
  rw [hleft, hright] at hr
  exact witness_not_congruent hr

/-- Negative generator-preservation instance, using the separating action. -/
example : ¬ witnessEquations.PreservesGenerators witnessSwap :=
  witness_swap_not_preserves_generators

/-- The identity change also preserves every consequence of the equation. -/
example : witnessEquations.PreservesCongruence (1 : FixedFGraphAutomorphism witnessGraph) :=
  (witnessEquations.preservesCongruence_iff_generators _).2 (by
    intro r
    cases r
    exact .equation PUnit.unit)

/-- The same name swap fails preservation of the full congruence. -/
example : ¬ witnessEquations.PreservesCongruence witnessSwap := by
  intro h
  exact witness_swap_not_preserves_generators
    ((witnessEquations.preservesCongruence_iff_generators _).1 h)

#print axioms AAT.AG.ProtocolHolonomy.PathEquations.Congruent
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.positiveTransport_comp
#print axioms AAT.AG.ProtocolHolonomy.PathEquations.preservesCongruence_iff_generators
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.preserves_congruence
#print axioms AAT.AG.ProtocolHolonomy.FiniteProtocolInput.visible_preserves_congruence
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
end AAT.AG.ProtocolHolonomy
