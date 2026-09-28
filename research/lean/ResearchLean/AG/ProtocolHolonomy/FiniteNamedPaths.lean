import ResearchLean.AG.ProtocolHolonomy.FiniteNamedWalks
import Formal.Util.AssertStandardAxioms

/-!
# Select original named paths from finite reachability

Enumerate finite graph walks by length using the explicit vertex list. A
reachable pair has a simple walk shorter than the vertex count, so the
bounded list contains a walk between that pair. Select its first entry and
resolve every step against the original named edge list. This computes an
original `SignedPath` from finite input tables and an existing component
equality. Choosing component roots and a consistent spanning forest remains
an E obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- All walks of exactly `n` steps from `a` to `b`, generated from the
explicit vertex list and decidable adjacency. -/
def finiteWalksExact (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) : (n : Nat) →
    List ((finiteReachabilityGraph Q).Walk a b)
  | 0 =>
      if h : a = b then [h ▸ SimpleGraph.Walk.nil] else []
  | n + 1 => by
      letI : DecidableRel (finiteReachabilityGraph Q).Adj :=
        finiteAdjDecidable Q edges
      exact vertices.values.flatMap fun y =>
        if h : (finiteReachabilityGraph Q).Adj a y then
          (finiteWalksExact Q vertices edges y b n).map
            (SimpleGraph.Walk.cons h)
        else []

/-- Every concrete walk occurs in the list at its own length. -/
theorem mem_finiteWalksExact (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    {a b : Q.Vertex} (p : (finiteReachabilityGraph Q).Walk a b) :
    p ∈ finiteWalksExact Q vertices edges a b p.length := by
  induction p with
  | nil => simp [finiteWalksExact]
  | cons h p ih =>
      rename_i x y z
      letI : DecidableRel (finiteReachabilityGraph Q).Adj :=
        finiteAdjDecidable Q edges
      simp only [SimpleGraph.Walk.length_cons]
      unfold finiteWalksExact
      apply List.mem_flatMap.mpr
      refine ⟨y, vertices.complete y, ?_⟩
      simp [h, ih]

/-- All walks with length below the finite vertex count. -/
def finiteBoundedWalks (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) :
    List ((finiteReachabilityGraph Q).Walk a b) := by
  letI : Fintype Q.Vertex := vertices.toFintype
  exact (List.range (Fintype.card Q.Vertex)).flatMap
    (finiteWalksExact Q vertices edges a b)

/-- Complete original finite tables turn a component-equality proof into an
executable original named signed path. The proof only eliminates the empty
finite path list; the selected path is the list head. -/
def finiteNamedPathOfReachable (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    {a b : Q.Vertex} (h : FixedFUndirectedReachable Q a b) :
    SignedPath Q a b := by
  letI : Fintype Q.Vertex := vertices.toFintype
  letI : DecidableRel (finiteReachabilityGraph Q).Adj :=
    finiteAdjDecidable Q edges
  let G := finiteReachabilityGraph Q
  let paths : List (G.Walk a b) := finiteBoundedWalks Q vertices edges a b
  have hne : paths ≠ [] := by
    intro hempty
    have hr : G.Reachable a b := (finiteReachable_iff_original Q a b).mpr h
    have hp : Nonempty (G.Path a b) := hr.elim_path (fun p => ⟨p⟩)
    obtain ⟨p⟩ := hp
    have hmem : p.1 ∈ paths := by
      unfold paths finiteBoundedWalks
      apply List.mem_flatMap.mpr
      refine ⟨p.1.length, List.mem_range.mpr p.2.length_lt, ?_⟩
      exact mem_finiteWalksExact Q vertices edges p.1
    simp [hempty] at hmem
  exact signedPathOfFiniteWalk Q edges (paths.head hne)

/-- Decide pairwise original-component reachability from finite tables and
return an actual original signed named path exactly when it holds. -/
def findFiniteNamedPath (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) : Option (SignedPath Q a b) := by
  letI : DecidableEq (FixedFComponent Q) :=
    finiteComponentDecidableEq Q vertices edges
  if hc : fixedFComponentMk Q a = fixedFComponentMk Q b then
    exact some (finiteNamedPathOfReachable Q vertices edges
      ((fixedFComponentMk_eq_iff Q a b).mp hc))
  else exact none

theorem findFiniteNamedPath_isSome_iff
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (a b : Q.Vertex) :
    (findFiniteNamedPath Q vertices edges a b).isSome = true ↔
      fixedFComponentMk Q a = fixedFComponentMk Q b := by
  letI : DecidableEq (FixedFComponent Q) :=
    finiteComponentDecidableEq Q vertices edges
  unfold findFiniteNamedPath
  split_ifs with hc <;> simp [hc]

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.finiteWalksExact
#print axioms AAT.AG.ProtocolHolonomy.mem_finiteWalksExact
#print axioms AAT.AG.ProtocolHolonomy.finiteBoundedWalks
#print axioms AAT.AG.ProtocolHolonomy.finiteNamedPathOfReachable
#print axioms AAT.AG.ProtocolHolonomy.findFiniteNamedPath
#print axioms AAT.AG.ProtocolHolonomy.findFiniteNamedPath_isSome_iff

private def smokeQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := PUnit
  source := fun _ => false
  target := fun _ => true

private def smokeVertices : AAT.AG.ProtocolHolonomy.ExplicitEnumeration smokeQ.Vertex where
  values := [false, true]
  complete := by intro x; cases x <;> simp

private def smokeEdges : AAT.AG.ProtocolHolonomy.ExplicitEnumeration smokeQ.Edge where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  let h : AAT.AG.RealizationReconstruction.FixedFUndirectedReachable
      smokeQ false true := Relation.EqvGen.rel _ _ ⟨PUnit.unit, rfl, rfl⟩
  (AAT.AG.ProtocolHolonomy.finiteNamedPathOfReachable
    smokeQ smokeVertices smokeEdges h).length)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  (AAT.AG.ProtocolHolonomy.findFiniteNamedPath
    smokeQ smokeVertices smokeEdges false true).isSome)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  (AAT.AG.ProtocolHolonomy.findFiniteNamedPath
    smokeQ smokeVertices smokeEdges false true).map Quiver.Path.length)

private def disconnectedQ : AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := Empty
  source := Empty.elim
  target := Empty.elim

private def disconnectedEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration disconnectedQ.Edge where
  values := []
  complete := by intro x; exact Empty.elim x

#eval (letI : DecidableEq disconnectedQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq disconnectedQ.Edge := inferInstanceAs (DecidableEq Empty)
  (AAT.AG.ProtocolHolonomy.findFiniteNamedPath
    disconnectedQ smokeVertices disconnectedEdges false true).isSome)

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
