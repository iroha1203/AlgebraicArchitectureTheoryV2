import ResearchLean.AG.ProtocolHolonomy.PathEquations
import ResearchLean.AG.RealizationReconstruction.FixedFComponentClassification
import Formal.Util.AssertStandardAxioms

/-!
# Reachability and root paths for reversible named protocols

The existing undirected component quotient is matched with existence of a
signed named path. A root and paths to every vertex are then constructed for
each component, with the root path forced to be empty.

## Implementation notes

The component quotient is inherited from the original graph rather than
redefined from signed paths. This keeps its existing API and original edge
names. The selected paths use choice for the structural B calculation; E
still requires an independent terminating finite-table forest algorithm.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Existence of a path using original named edges in either direction. -/
def SignedReachable (Q : FixedFDirectedMultigraph.{u, v})
    (s t : Q.Vertex) : Prop := Nonempty (SignedPath Q s t)

/-- Signed path existence is exactly the existing undirected edge closure. -/
theorem signedReachable_iff_undirected
    (Q : FixedFDirectedMultigraph.{u, v}) (s t : Q.Vertex) :
    SignedReachable Q s t ↔ FixedFUndirectedReachable Q s t := by
  constructor
  · rintro ⟨p⟩
    letI : Quiver Q.Vertex := typedQuiver Q
    letI : Quiver (Quiver.Symmetrify Q.Vertex) := Quiver.symmetrifyQuiver Q.Vertex
    induction p with
    | nil => exact Relation.EqvGen.refl _
    | cons p e ih =>
        apply Relation.EqvGen.trans _ _ _ ih
        cases e with
        | inl f =>
            exact Relation.EqvGen.rel _ _ ⟨f.1, f.2.1, f.2.2⟩
        | inr f =>
            apply Relation.EqvGen.symm
            exact Relation.EqvGen.rel _ _ ⟨f.1, f.2.1, f.2.2⟩
  · intro h
    induction h with
    | rel a b hab =>
        obtain ⟨e, hs, ht⟩ := hab
        exact ⟨signedToPath Q (Sum.inl ⟨e, hs, ht⟩)⟩
    | refl a => exact ⟨signedNil Q a⟩
    | symm a b hab ih =>
        obtain ⟨p⟩ := ih
        exact ⟨signedReverse Q p⟩
    | trans a b c hab hbc ih₁ ih₂ =>
        obtain ⟨p⟩ := ih₁
        obtain ⟨q⟩ := ih₂
        exact ⟨signedComp Q p q⟩

/-- Two vertices share the original graph component exactly when a signed
named path connects them. -/
theorem component_eq_iff_signedReachable
    (Q : FixedFDirectedMultigraph.{u, v}) (s t : Q.Vertex) :
    fixedFComponentMk Q s = fixedFComponentMk Q t ↔
      SignedReachable Q s t := by
  rw [fixedFComponentMk_eq_iff]
  exact (signedReachable_iff_undirected Q s t).symm

/-- A root and paths from it to each vertex of its component. The chosen
path at the root is the empty path. -/
structure RootedPaths (Q : FixedFDirectedMultigraph.{u, v}) where
  root : FixedFComponent Q → Q.Vertex
  root_component : ∀ j, fixedFComponentMk Q (root j) = j
  path : ∀ (j : FixedFComponent Q) (x : Q.Vertex),
    fixedFComponentMk Q x = j → SignedPath Q (root j) x
  path_root : ∀ j, path j (root j) (root_component j) = signedNil Q (root j)

/-- Choose a path from a specified root to any vertex of its component,
normalizing the root case to the empty path. -/
noncomputable def pathFromRoot
    (Q : FixedFDirectedMultigraph.{u, v})
    (root : FixedFComponent Q → Q.Vertex)
    (hroot : ∀ j, fixedFComponentMk Q (root j) = j)
    (j : FixedFComponent Q) (x : Q.Vertex)
    (hx : fixedFComponentMk Q x = j) : SignedPath Q (root j) x := by
  classical
  by_cases h : x = root j
  · subst x
    exact signedNil Q (root j)
  · have hsame : fixedFComponentMk Q (root j) = fixedFComponentMk Q x :=
      (hroot j).trans hx.symm
    have hpath : SignedReachable Q (root j) x :=
      (component_eq_iff_signedReachable Q _ _).mp hsame
    exact Classical.choice hpath

/-- The selected root-to-root path equals the empty execution. -/
theorem pathFromRoot_self
    (Q : FixedFDirectedMultigraph.{u, v})
    (root : FixedFComponent Q → Q.Vertex)
    (hroot : ∀ j, fixedFComponentMk Q (root j) = j)
    (j : FixedFComponent Q) :
    pathFromRoot Q root hroot j (root j) (hroot j) =
      signedNil Q (root j) := by
  unfold pathFromRoot
  simp

/-- For any chosen root in each component, construct the required path
family from the original reachability relation. -/
noncomputable def rootedPathsOfRoots
    (Q : FixedFDirectedMultigraph.{u, v})
    (root : FixedFComponent Q → Q.Vertex)
    (hroot : ∀ j, fixedFComponentMk Q (root j) = j) : RootedPaths Q where
  root := root
  root_component := hroot
  path := pathFromRoot Q root hroot
  path_root := by
    intro j
    exact pathFromRoot_self Q root hroot j

/-- A choice of roots is available even for empty/disconnected
graphs. Finite spanning-tree construction remains an E obligation. -/
noncomputable def chooseRootedPaths
    (Q : FixedFDirectedMultigraph.{u, v}) : RootedPaths Q :=
  rootedPathsOfRoots Q Quotient.out (fun j => Quotient.out_eq j)

/-! SignedReachable has both positive and negative instances. RootedPaths
itself always has an instance by `chooseRootedPaths`, so a negative instance
of that certificate is mathematically impossible. -/

/-- Two isolated control points, with no named operation between them. -/
private def disconnectedGraph : FixedFDirectedMultigraph where
  Vertex := Bool
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

/-- A zero-length signed path witnesses reflexive reachability. -/
example : SignedReachable disconnectedGraph false false :=
  ⟨signedNil disconnectedGraph false⟩

/-- Distinct isolated vertices are not connected by a signed named path. -/
example : ¬ SignedReachable disconnectedGraph false true := by
  intro h
  have hd : FixedFUndirectedReachable disconnectedGraph false true :=
    (signedReachable_iff_undirected _ _ _).mp h
  have equal_of_reachable : ∀ {a b : disconnectedGraph.Vertex},
      FixedFUndirectedReachable disconnectedGraph a b → a = b := by
    intro a b hab
    induction hab with
    | rel a b step =>
        obtain ⟨e, _, _⟩ := step
        exact Empty.elim e
    | refl a => rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih₁ ih₂ => exact ih₁.trans ih₂
  exact Bool.false_ne_true (equal_of_reachable hd)

#print axioms AAT.AG.ProtocolHolonomy.signedReachable_iff_undirected
#print axioms AAT.AG.ProtocolHolonomy.component_eq_iff_signedReachable
#print axioms AAT.AG.ProtocolHolonomy.pathFromRoot_self
#print axioms AAT.AG.ProtocolHolonomy.rootedPathsOfRoots
#print axioms AAT.AG.ProtocolHolonomy.chooseRootedPaths
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
end AAT.AG.ProtocolHolonomy
