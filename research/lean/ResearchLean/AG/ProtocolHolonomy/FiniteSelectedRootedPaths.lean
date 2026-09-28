import ResearchLean.AG.ProtocolHolonomy.FiniteSelectedPaths
import ResearchLean.AG.ProtocolHolonomy.FiniteRootedPaths
import Formal.Util.AssertStandardAxioms

/-!
# Compute normalized root paths inside the generated named forest

Choose the first original vertex of each component from the finite table.
For every vertex of that component, the bounded selected path search returns
an actual original named path in its selected tree. At the root the path is
the empty path, as required by B and C.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v

/-- Compute a root path carrying only the input-generated tree names of this
original component, normalized to the empty path at the root. -/
def finiteSelectedPathFromRoot
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q)
    (r : {x : Q.Vertex // fixedFComponentMk Q x = j})
    (x : Q.Vertex) (hx : fixedFComponentMk Q x = j) :
    {p : SignedPath Q r.1 x //
      UsesNamedEdges
        (fun e => e ∈ finiteSpanningEdgeSelection Q vertices edges ∧
          fixedFComponentMk Q (Q.source e) = j) p} := by
  by_cases h : x = r.1
  · subst x
    exact ⟨signedNil Q r.1, UsesNamedEdges.nil r.1⟩
  · have horig : FixedFUndirectedReachable Q r.1 x :=
      (fixedFComponentMk_eq_iff Q r.1 x).mp (r.2.trans hx.symm)
    have hselected : SelectedNamedReachable Q
        (finiteSpanningEdgeSelection Q vertices edges) r.1 x :=
      finiteSpanningEdgeSelection_originalReachable Q vertices edges
        r.1 x horig
    let p := finiteSelectedNamedPathOfReachable Q vertices edges
      (finiteSpanningEdgeSelection Q vertices edges) hselected
    exact ⟨p.1, usesNamedEdges_restrictComponent Q _ j p.1 r.2 p.2⟩

theorem finiteSelectedPathFromRoot_self
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q)
    (r : {x : Q.Vertex // fixedFComponentMk Q x = j}) :
    (finiteSelectedPathFromRoot Q vertices edges j r r.1 r.2).1 =
      signedNil Q r.1 := by
  unfold finiteSelectedPathFromRoot
  simp

/-- A terminating original named `RootedPaths` input for B and C, computed
within the same finite-table-generated forest used in E. -/
def finiteSelectedRootedPaths
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge) : RootedPaths Q where
  root j := (finiteRootForComponent Q vertices edges j).1
  root_component j := (finiteRootForComponent Q vertices edges j).2
  path j x hx :=
    (finiteSelectedPathFromRoot Q vertices edges j
      (finiteRootForComponent Q vertices edges j) x hx).1
  path_root := by
    intro j
    exact finiteSelectedPathFromRoot_self Q vertices edges j
      (finiteRootForComponent Q vertices edges j)

/-- Every computed root path stays in the selected original named tree of
its component, including the normalized empty root path. -/
theorem finiteSelectedRootedPaths_path_usesForest
    (Q : FixedFDirectedMultigraph.{u, v})
    [DecidableEq Q.Vertex] [DecidableEq Q.Edge]
    (vertices : ExplicitEnumeration Q.Vertex)
    (edges : ExplicitEnumeration Q.Edge)
    (j : FixedFComponent Q) (x : Q.Vertex)
    (hx : fixedFComponentMk Q x = j) :
    UsesNamedEdges
      ((finiteNamedSpanningForest Q vertices edges).tree j).selected
      ((finiteSelectedRootedPaths Q vertices edges).path j x hx) :=
  (finiteSelectedPathFromRoot Q vertices edges j
    (finiteRootForComponent Q vertices edges j) x hx).2

end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.finiteSelectedPathFromRoot
#print axioms AAT.AG.ProtocolHolonomy.finiteSelectedPathFromRoot_self
#print axioms AAT.AG.ProtocolHolonomy.finiteSelectedRootedPaths
#print axioms AAT.AG.ProtocolHolonomy.finiteSelectedRootedPaths_path_usesForest

private def selectedRootSmokeQ :
    AAT.AG.RealizationReconstruction.FixedFDirectedMultigraph.{0, 0} where
  Vertex := Bool
  Edge := PUnit
  source := fun _ => false
  target := fun _ => true

private def selectedRootSmokeVertices :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration selectedRootSmokeQ.Vertex where
  values := [false, true]
  complete := by intro x; cases x <;> simp

private def selectedRootSmokeEdges :
    AAT.AG.ProtocolHolonomy.ExplicitEnumeration selectedRootSmokeQ.Edge where
  values := [PUnit.unit]
  complete := by intro x; cases x; simp

#eval (letI : DecidableEq selectedRootSmokeQ.Vertex := inferInstanceAs (DecidableEq Bool)
  letI : DecidableEq selectedRootSmokeQ.Edge := inferInstanceAs (DecidableEq PUnit)
  letI : Quiver selectedRootSmokeQ.Vertex :=
    AAT.AG.ProtocolHolonomy.typedQuiver selectedRootSmokeQ
  letI : Quiver (Quiver.Symmetrify selectedRootSmokeQ.Vertex) :=
    Quiver.symmetrifyQuiver selectedRootSmokeQ.Vertex
  let j := AAT.AG.RealizationReconstruction.fixedFComponentMk selectedRootSmokeQ false
  let hx : AAT.AG.RealizationReconstruction.fixedFComponentMk
      selectedRootSmokeQ true = j :=
    ((AAT.AG.RealizationReconstruction.fixedFComponentMk_eq_iff
      selectedRootSmokeQ false true).mpr
      (Relation.EqvGen.rel _ _ ⟨PUnit.unit, rfl, rfl⟩)).symm
  ((AAT.AG.ProtocolHolonomy.finiteSelectedRootedPaths
    selectedRootSmokeQ selectedRootSmokeVertices selectedRootSmokeEdges).path
      j true hx).length)

#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
