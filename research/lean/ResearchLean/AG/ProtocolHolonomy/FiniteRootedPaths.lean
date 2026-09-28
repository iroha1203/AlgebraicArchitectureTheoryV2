import ResearchLean.AG.ProtocolHolonomy.FiniteNamedPaths
import ResearchLean.AG.ProtocolHolonomy.FiniteRootDecision
import Formal.Util.AssertStandardAxioms

/-!
# Executable roots and original named paths from finite graph tables

For each original component, scan the complete vertex list and select its
first representative. For every vertex in that component, the bounded path
search constructs an original named signed path from that root. The root path
is normalized to the empty path. This supplies `RootedPaths` to B/C/E from
finite input tables; proving that the paths form one named spanning forest
remains a separate obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v
universe w

/-- Select the first original vertex listed in a component. The quotient
representative is used only to prove that the filtered list is nonempty. -/
def finiteRootForComponent (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q) :
    {r : Q.Vertex // fixedFComponentMk Q r = j} := by
  letI : DecidableEq (FixedFComponent Q) :=
    finiteComponentDecidableEq Q vertices edges
  let candidates := vertices.values.filter (fun x => fixedFComponentMk Q x = j)
  have hne : candidates ≠ [] := by
    intro hempty
    let x : Q.Vertex := Quotient.out j
    have hx : fixedFComponentMk Q x = j := Quotient.out_eq j
    have hmem : x ∈ candidates := by
      simp [candidates, vertices.complete x, hx]
    simp [hempty] at hmem
  have hhead : candidates.head hne ∈ candidates := List.head_mem hne
  refine ⟨candidates.head hne, ?_⟩
  have hh := (List.mem_filter.mp hhead).2
  simpa only [decide_eq_true_eq] using hh

/-- Compute one original named root path, using the empty path at the root. -/
def finitePathFromRoot (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q)
    (r : {x : Q.Vertex // fixedFComponentMk Q x = j})
    (x : Q.Vertex) (hx : fixedFComponentMk Q x = j) :
    SignedPath Q r.1 x := by
  by_cases h : x = r.1
  · subst x
    exact signedNil Q r.1
  · exact finiteNamedPathOfReachable Q vertices edges
      ((fixedFComponentMk_eq_iff Q r.1 x).mp (r.2.trans hx.symm))

theorem finitePathFromRoot_self (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q)
    (r : {x : Q.Vertex // fixedFComponentMk Q x = j}) :
    finitePathFromRoot Q vertices edges j r r.1 r.2 = signedNil Q r.1 := by
  unfold finitePathFromRoot
  simp

/-- The exact B/C rooted-path input, generated from the original finite
vertex and named-edge tables, with no supplied roots or paths. -/
def finiteRootedPaths (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) : RootedPaths Q where
  root j := (finiteRootForComponent Q vertices edges j).1
  root_component j := (finiteRootForComponent Q vertices edges j).2
  path j x hx :=
    finitePathFromRoot Q vertices edges j
      (finiteRootForComponent Q vertices edges j) x hx
  path_root := by
    intro j
    exact finitePathFromRoot_self Q vertices edges j
      (finiteRootForComponent Q vertices edges j)

namespace ReversibleData

/-- Run the simultaneous C1 search using roots and original named paths
constructed from the same finite graph input tables. -/
def findFiniteRootLift {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    Option (D.Lift g) :=
  D.findRootLift (finiteRootedPaths Q vertices edges) g vertices edges fibers

/-- Input-generated root paths make the C1 decision exact for the original
A1 lift fiber, including the negative answer. -/
theorem findFiniteRootLift_isSome_iff
    {Q : FixedFDirectedMultigraph.{u, v}}
    (D : ReversibleData.{u, v, w} Q)
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    [∀ x : Q.Vertex, DecidableEq (D.Fiber x)]
    (g : FixedFGraphAutomorphism Q)
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (fibers : ∀ x, ExplicitEnumeration (D.Fiber x)) :
    (D.findFiniteRootLift g vertices edges fibers).isSome = true ↔
      Nonempty (D.Lift g) :=
  D.findRootLift_isSome_iff (finiteRootedPaths Q vertices edges)
    g vertices edges fibers

end ReversibleData

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.finiteRootForComponent
#print axioms AAT.AG.ProtocolHolonomy.finitePathFromRoot
#print axioms AAT.AG.ProtocolHolonomy.finitePathFromRoot_self
#print axioms AAT.AG.ProtocolHolonomy.finiteRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findFiniteRootLift
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.findFiniteRootLift_isSome_iff

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

private def smokeD : AAT.AG.ProtocolHolonomy.ReversibleData.{0, 0, 0} smokeQ where
  Fiber := fun _ => Bool
  edgeEquiv := fun _ => Equiv.refl Bool

private def smokeFibers :
    ∀ x : smokeQ.Vertex,
      AAT.AG.ProtocolHolonomy.ExplicitEnumeration (smokeD.Fiber x) := by
  intro x
  exact { values := [false, true], complete := by intro y; cases y <;> simp }

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  let R := AAT.AG.ProtocolHolonomy.finiteRootedPaths
    smokeQ smokeVertices smokeEdges
  R.root (AAT.AG.RealizationReconstruction.fixedFComponentMk smokeQ false))

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : Quiver smokeQ.Vertex := AAT.AG.ProtocolHolonomy.typedQuiver smokeQ
  letI : Quiver (Quiver.Symmetrify smokeQ.Vertex) :=
    Quiver.symmetrifyQuiver smokeQ.Vertex
  let R := AAT.AG.ProtocolHolonomy.finiteRootedPaths
    smokeQ smokeVertices smokeEdges
  let j := AAT.AG.RealizationReconstruction.fixedFComponentMk smokeQ false
  let hx : AAT.AG.RealizationReconstruction.fixedFComponentMk smokeQ true = j :=
    (AAT.AG.RealizationReconstruction.fixedFComponent_source_eq_target
      smokeQ PUnit.unit).symm
  (R.path j true hx).length)

#eval (letI : DecidableEq smokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq smokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : ∀ x : smokeQ.Vertex, DecidableEq (smokeD.Fiber x) :=
    fun _ => inferInstanceAs (DecidableEq Bool)
  (smokeD.findFiniteRootLift (1 : AAT.AG.RealizationReconstruction.FixedFGraphAutomorphism smokeQ)
    smokeVertices smokeEdges smokeFibers).isSome)

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
