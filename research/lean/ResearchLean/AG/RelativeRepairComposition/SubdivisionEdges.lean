import ResearchLean.AG.RelativeRepairComposition.ClosedRegions

/-!
# Named finite edges for one original internal-edge subdivision

All original endpoint-indexed edge names except the selected name remain.
Two new names join its old endpoints through a distinct new vertex.

## Implementation notes

The edge type is the finite subtype of names with the specified source and
target. Keeping the complete old Sigma name avoids identifying parallel edges
or forgetting their endpoints. A fresh indexed inductive edge family was
rejected: finite named incidence directly supplies every indexed finite type
and the total-name equivalence needed by the full cochain coordinates.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence AbelianLiftingObstruction
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))

/-- All original vertices and one separately named intermediate vertex. -/
abbrev Vertex := K.Vertex ⊕ Unit

/-- Every remaining original complete edge name and the two distinct factor names. -/
abbrev Name := {e : EdgeName (K := K) // e ≠ chosen} ⊕ Bool

/-- The source of an old name or its first/second actual factor. -/
def source : Name K chosen → Vertex K
  | .inl e => .inl e.1.1
  | .inr false => .inl chosen.1
  | .inr true => .inr ()

/-- The target of an old name or its first/second actual factor. -/
def target : Name K chosen → Vertex K
  | .inl e => .inl e.1.2.1
  | .inr false => .inr ()
  | .inr true => .inl chosen.2.1

/-- A named edge at precisely its original or factor endpoints. -/
abbrev Edge (i j : Vertex K) := {n : Name K chosen // source K chosen n = i ∧ target K chosen n = j}

/-- Each indexed edge type is finite from the complete finite named incidence. -/
noncomputable instance edgeFintype (i j : Vertex K) : Fintype (Edge K chosen i j) := by
  classical
  exact inferInstance

/-- A remaining original edge keeps its complete original endpoint indices and name. -/
def oldEdge (e : EdgeName (K := K)) (he : e ≠ chosen) : Edge K chosen (.inl e.1) (.inl e.2.1) :=
  ⟨.inl ⟨e,he⟩,rfl,rfl⟩

/-- The first factor has the selected old source and the new intermediate target. -/
def firstEdge : Edge K chosen (.inl chosen.1) (.inr ()) := ⟨.inr false,rfl,rfl⟩

/-- The second factor has the new intermediate source and selected old target. -/
def secondEdge : Edge K chosen (.inr ()) (.inl chosen.2.1) := ⟨.inr true,rfl,rfl⟩

/-- The two factor names are distinct even when the original edge is a loop. -/
theorem first_ne_second :
    (firstEdge K chosen).1 ≠ (secondEdge K chosen).1 := by
  intro h
  exact Bool.false_ne_true (Sum.inr.inj h)

/-- The actual ordered two-factor path has the selected original bookends. -/
def factorPath : PresentedPath (Edge K chosen) (.inl chosen.1) (.inl chosen.2.1) :=
  .cons (firstEdge K chosen) (.cons (secondEdge K chosen) (.nil (Sum.inl chosen.2.1)))

/-- Replace the complete selected name by the two factors and every other name by itself. -/
noncomputable def edgeWord (e : EdgeName (K := K)) :
    PresentedPath (Edge K chosen) (.inl e.1) (.inl e.2.1) := by
  classical
  exact if h : e = chosen then h.symm ▸ factorPath K chosen
    else .cons (oldEdge K chosen e h) (.nil (Sum.inl e.2.1))

/-- The selected complete original name is replaced by both factors in their original order. -/
theorem edgeWord_chosen : edgeWord K chosen chosen = factorPath K chosen := by
  classical
  simp [edgeWord]

/-- Every other complete original name stays at its original endpoints. -/
theorem edgeWord_old (e : EdgeName (K := K)) (he : e ≠ chosen) :
    edgeWord K chosen e = .cons (oldEdge K chosen e he) (.nil (Sum.inl e.2.1)) := by
  classical
  simp only [edgeWord,dif_neg he]

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
