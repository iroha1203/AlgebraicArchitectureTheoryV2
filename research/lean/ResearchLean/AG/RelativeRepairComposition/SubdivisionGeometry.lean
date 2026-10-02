import ResearchLean.AG.RelativeRepairComposition.SubdivisionEdges

/-!
# Complete typed geometry after subdivision of one original edge

The substitution is computed on every old word and every whiskered rewrite.
Original face and three-cell names, orientation and both ordered routes remain.

## Implementation notes

A word substitution sends one edge to two edges, so a single-edge embedding
would be the wrong geometric map. Recursion by concatenating edgeWord keeps all
occurrences; its append law supplies the exact before/after step equations.
Copying only face endpoints was rejected because original three-cell routes
also retain their complete incoming/outgoing words and their ordered steps.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG}) (chosen : EdgeName (K := K))

/-- Substitute every original edge occurrence and preserve both original endpoints. -/
noncomputable def substitutePath {i j : K.Vertex} :
    K.Path i j → PresentedPath (Edge K chosen) (Sum.inl i) (Sum.inl j)
  | .nil i => .nil (Sum.inl i)
  | .cons e w => (edgeWord K chosen ⟨_,_,e⟩).append (substitutePath w)

/-- Full ordered substitution preserves every concatenation. -/
theorem substitute_append {i j l : K.Vertex} (w : K.Path i j) (z : K.Path j l) :
    substitutePath K chosen (w.append z) =
      (substitutePath K chosen w).append (substitutePath K chosen z) := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    simp only [PresentedPath.append,substitutePath,ih,PresentedPath.append_assoc]

/-- Both original face words are substituted and their names are kept exactly. -/
noncomputable def skeleton : FiniteTransportTwoPresentation.{uG} where
  Vertex := Vertex K
  vertexFintype := inferInstance
  Edge := Edge K chosen
  edgeFintype _ _ := inferInstance
  TwoCell := K.TwoCell
  twoCellFintype := K.twoCellFintype
  twoSource f := .inl (K.twoSource f)
  twoTarget f := .inl (K.twoTarget f)
  twoLeft f := substitutePath K chosen (K.twoLeft f)
  twoRight f := substitutePath K chosen (K.twoRight f)

/-- Every original oriented face occurrence keeps its full substituted prefix and suffix. -/
noncomputable def substituteFace {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    WhiskeredFace (skeleton K chosen) (Sum.inl i) (Sum.inl j) where
  cell := f.cell
  incoming := substitutePath K chosen f.incoming
  outgoing := substitutePath K chosen f.outgoing
  orientation := f.orientation

/-- The chosen orientation keeps the complete incoming local word. -/
theorem substitute_local_before {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (substituteFace K chosen f).localBefore = substitutePath K chosen f.localBefore := by
  cases h : f.orientation <;> simp only [WhiskeredFace.localBefore,substituteFace,h,skeleton]

/-- The chosen orientation keeps the complete outgoing local word. -/
theorem substitute_local_after {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (substituteFace K chosen f).localAfter = substitutePath K chosen f.localAfter := by
  cases h : f.orientation <;> simp only [WhiskeredFace.localAfter,substituteFace,h,skeleton]

/-- The full path before each rewrite has every selected occurrence replaced. -/
theorem substitute_before {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (substituteFace K chosen f).before = substitutePath K chosen f.before := by
  rw [WhiskeredFace.before,substitute_local_before]
  change (substitutePath K chosen f.incoming).append
    ((substitutePath K chosen f.localBefore).append (substitutePath K chosen f.outgoing)) = _
  simp only [WhiskeredFace.before,substitute_append]

/-- The full path after each rewrite has every selected occurrence replaced. -/
theorem substitute_after {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (substituteFace K chosen f).after = substitutePath K chosen f.after := by
  rw [WhiskeredFace.after,substitute_local_after]
  change (substitutePath K chosen f.incoming).append
    ((substitutePath K chosen f.localAfter).append (substitutePath K chosen f.outgoing)) = _
  simp only [WhiskeredFace.after,substitute_append]

/-- Original step equations generate the actual substituted typed step equations. -/
noncomputable def substituteStep {i j : K.Vertex} {w z : K.Path i j}
    (s : RewriteStep K.toFiniteTransportTwoPresentation w z) :
    RewriteStep (skeleton K chosen) (substitutePath K chosen w) (substitutePath K chosen z) where
  face := substituteFace K chosen s.face
  before_eq := (congrArg (substitutePath K chosen) s.before_eq).trans (substitute_before K chosen s.face).symm
  after_eq := (congrArg (substitutePath K chosen) s.after_eq).trans (substitute_after K chosen s.face).symm

/-- Every original route keeps all oriented steps and both complete substituted bookends. -/
noncomputable def substitutePasting {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z →
      RewritePasting (skeleton K chosen) (substitutePath K chosen w) (substitutePath K chosen z)
  | .nil w => @RewritePasting.nil (skeleton K chosen) (Sum.inl i) (Sum.inl j) (substitutePath K chosen w)
  | .cons s t => .cons (substituteStep K chosen s) (substitutePasting t)

/-- Complete original finite geometry with one internal edge replaced and no new Laws. -/
noncomputable def presentation : FiniteTransportPresentation.{uG} where
  toFiniteTransportTwoPresentation := skeleton K chosen
  ThreeCell := K.ThreeCell
  threeCellFintype := K.threeCellFintype
  threeSource f := .inl (K.threeSource f)
  threeTarget f := .inl (K.threeTarget f)
  threeStart f := substitutePath K chosen (K.threeStart f)
  threeFinish f := substitutePath K chosen (K.threeFinish f)
  threeLeft f := substitutePasting K chosen (K.threeLeft f)
  threeRight f := substitutePasting K chosen (K.threeRight f)

/-- Total names of the subdivided indexed graph are exactly its named old edges and two factors. -/
def edgeNameEquiv : EdgeName (K := presentation K chosen) ≃ Name K chosen where
  toFun e := e.2.2.1
  invFun n := ⟨source K chosen n,target K chosen n,⟨n,rfl,rfl⟩⟩
  left_inv e := by
    rcases e with ⟨i,j,n,hs,ht⟩
    cases hs; cases ht
    rfl
  right_inv _ := rfl

/-- A nonselected original edge retains its full name in the subdivided presentation. -/
def oldEdgeName (e : EdgeName (K := K)) (he : e ≠ chosen) : EdgeName (K := presentation K chosen) :=
  ⟨.inl e.1,.inl e.2.1,oldEdge K chosen e he⟩

/-- The full name of the first actual factor includes its original source and fresh target. -/
def firstEdgeName : EdgeName (K := presentation K chosen) :=
  ⟨.inl chosen.1,.inr (),firstEdge K chosen⟩

/-- The full name of the second actual factor includes its fresh source and original target. -/
def secondEdgeName : EdgeName (K := presentation K chosen) :=
  ⟨.inr (),.inl chosen.2.1,secondEdge K chosen⟩

/-- The fresh intermediate vertex differs from every original vertex. -/
theorem new_vertex_ne_old (v : K.Vertex) : (Sum.inr () : (presentation K chosen).Vertex) ≠ .inl v := by
  intro h
  cases h

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
