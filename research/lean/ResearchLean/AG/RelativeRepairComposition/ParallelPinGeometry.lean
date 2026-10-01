import ResearchLean.AG.RelativeRepairComposition.ClosedRegions

/-!
# Parallel forbidden candidates over the complete shared geometry

Every old path and every oriented face occurrence in an authored three-cell is
copied. The added parallel edges have one identity-comparison face each; there
are no new vertices or three-cells. Affine operations are supplied separately.
-/
namespace AAT.AG.RelativeRepairComposition.ParallelPinGeometry
open TransportCoherence
universe uG
variable (K : FiniteTransportPresentation.{uG})

/-- Old edges and their separately named parallel pins have the same endpoints. -/
abbrev Edge (i j : K.Vertex) := K.Edge i j ⊕ K.Edge i j

/-- Inclusion keeps the complete ordered old path and all its endpoints. -/
def includePath {i j : K.Vertex} : K.Path i j → PresentedPath (Edge K) i j
  | .nil i => .nil i
  | .cons e w => .cons (.inl e) (includePath w)

/-- Inclusion preserves typed path concatenation. -/
theorem include_append {i j l : K.Vertex} (w : K.Path i j) (z : K.Path j l) :
    includePath K (w.append z) = (includePath K w).append (includePath K z) := by
  induction w with
  | nil _ => rfl
  | cons e w ih => simp only [PresentedPath.append, includePath, ih]

/-- All old faces remain, with a distinct pin face for every original edge name. -/
noncomputable def skeleton : FiniteTransportTwoPresentation.{uG} where
  Vertex := K.Vertex
  vertexFintype := K.vertexFintype
  Edge := Edge K
  edgeFintype _ _ := inferInstance
  TwoCell := K.TwoCell ⊕ EdgeName (K := K)
  twoCellFintype := inferInstance
  twoSource := fun f => match f with | .inl f => K.twoSource f | .inr e => e.1
  twoTarget := fun f => match f with | .inl f => K.twoTarget f | .inr e => e.2.1
  twoLeft := fun f => match f with
    | .inl f => includePath K (K.twoLeft f)
    | .inr e => .cons (.inl e.2.2) (.nil e.2.1)
  twoRight := fun f => match f with
    | .inl f => includePath K (K.twoRight f)
    | .inr e => .cons (.inr e.2.2) (.nil e.2.1)

/-- Every old whiskered rewrite retains both full contextual paths and orientation. -/
noncomputable def includeFace {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    WhiskeredFace (skeleton K) i j where
  cell := .inl f.cell
  incoming := includePath K f.incoming
  outgoing := includePath K f.outgoing
  orientation := f.orientation

/-- The copied local incoming path is the old path with old edge names included. -/
theorem include_local_before {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (includeFace K f).localBefore = includePath K f.localBefore := by
  cases h : f.orientation <;> simp only [WhiskeredFace.localBefore, includeFace, h, skeleton]

/-- The copied local outgoing path is the old path with old edge names included. -/
theorem include_local_after {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (includeFace K f).localAfter = includePath K f.localAfter := by
  cases h : f.orientation <;> simp only [WhiskeredFace.localAfter, includeFace, h, skeleton]

/-- The entire pre-rewrite path, including prefix and suffix, is preserved. -/
theorem include_before {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (includeFace K f).before = includePath K f.before := by
  rw [WhiskeredFace.before, include_local_before]
  change (includePath K f.incoming).append ((includePath K f.localBefore).append (includePath K f.outgoing)) = _
  simp only [WhiskeredFace.before, include_append]

/-- The entire post-rewrite path, including prefix and suffix, is preserved. -/
theorem include_after {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    (includeFace K f).after = includePath K f.after := by
  rw [WhiskeredFace.after, include_local_after]
  change (includePath K f.incoming).append ((includePath K f.localAfter).append (includePath K f.outgoing)) = _
  simp only [WhiskeredFace.after, include_append]

/-- The old typed rewrite equations generate the copied step equations. -/
noncomputable def includeStep {i j : K.Vertex} {w z : K.Path i j}
    (s : RewriteStep K.toFiniteTransportTwoPresentation w z) :
    RewriteStep (skeleton K) (includePath K w) (includePath K z) where
  face := includeFace K s.face
  before_eq := (congrArg (includePath K) s.before_eq).trans (include_before K s.face).symm
  after_eq := (congrArg (includePath K) s.after_eq).trans (include_after K s.face).symm

/-- Every old composable sequence is included with the exact original bookends. -/
noncomputable def includePasting {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z →
      RewritePasting (skeleton K) (includePath K w) (includePath K z)
  | .nil w => @RewritePasting.nil (skeleton K) i j (includePath K w)
  | .cons s t => .cons (includeStep K s) (includePasting t)

/-- Full shared geometry with pins: the original three-cells and both complete routes remain. -/
noncomputable def presentation : FiniteTransportPresentation.{uG} where
  toFiniteTransportTwoPresentation := skeleton K
  ThreeCell := K.ThreeCell
  threeCellFintype := K.threeCellFintype
  threeSource := K.threeSource
  threeTarget := K.threeTarget
  threeStart f := includePath K (K.threeStart f)
  threeFinish f := includePath K (K.threeFinish f)
  threeLeft f := includePasting K (K.threeLeft f)
  threeRight f := includePasting K (K.threeRight f)

/-- The embedded old edge keeps the same original endpoint indices and name. -/
def oldEdgeName (e : EdgeName (K := K)) : EdgeName (K := presentation K) :=
  ⟨e.1, e.2.1, .inl e.2.2⟩

/-- A pin is a new named edge at exactly the original endpoint indices. -/
def pinEdgeName (e : EdgeName (K := K)) : EdgeName (K := presentation K) :=
  ⟨e.1, e.2.1, .inr e.2.2⟩

/-- Old and pin names never collide, including loops and parallel original edges. -/
theorem old_ne_pin (e f : EdgeName (K := K)) : oldEdgeName K e ≠ pinEdgeName K f := by
  intro h
  cases e with | mk i e =>
    cases e with | mk j e =>
      cases f with | mk a f =>
        cases f with | mk b f =>
          cases h

end AAT.AG.RelativeRepairComposition.ParallelPinGeometry
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.ParallelPinGeometry
