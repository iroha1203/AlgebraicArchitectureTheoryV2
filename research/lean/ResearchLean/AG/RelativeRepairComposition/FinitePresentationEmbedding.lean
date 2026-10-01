import ResearchLean.AG.RelativeRepairComposition.ParallelPinGeometry

/-!
# Typed embeddings of a common finite presentation

Sharing a presentation means sharing its actual cells, words and both complete
three-cell routes. The data below are geometric incidence maps and their exact
compatibilities; they contain no repair, coherence or existence conclusion.

## Implementation notes

The path/step/route fields retain their native dependent endpoint types and all
contexts; nil/cons and HEq laws identify them with the computed geometric map.
Storing only vertex/edge images was rejected: faces and both authored routes
also need endpoint/bookend transports, and a computed path alone does not keep
those native typed data definitionally aligned. These are incidence fields,
so the record supplies no repair or contextual-equivalence certificate.
-/
namespace AAT.AG.RelativeRepairComposition
open TransportCoherence
universe uG

/-- Map each original path by its vertex and single-edge maps, preserving every occurrence and order. -/
def embeddedPath {G H : FiniteTransportPresentation.{uG}} (v : G.Vertex → H.Vertex)
    (e : ∀ {i j : G.Vertex}, G.Edge i j → H.Edge (v i) (v j))
    {i j : G.Vertex} : G.Path i j → H.Path (v i) (v j)
  | .nil i => .nil (v i)
  | .cons a w => .cons (e a) (embeddedPath v e w)

/-- A full common-presentation embedding retaining exact typed contexts and cell names. -/
structure FinitePresentationEmbedding (G H : FiniteTransportPresentation.{uG}) where
  /-- Every shared original vertex has its named image. -/
  vertex : G.Vertex → H.Vertex
  /-- Shared vertices remain distinct. -/
  vertex_injective : Function.Injective vertex
  /-- Every shared original edge has its named image at the same mapped endpoints. -/
  edge : ∀ {i j : G.Vertex}, G.Edge i j → H.Edge (vertex i) (vertex j)
  /-- Original parallel edge names remain distinct. -/
  edge_injective : ∀ i j, Function.Injective (@edge i j)
  /-- The full typed word map follows the named edge and vertex maps. -/
  path : ∀ {i j : G.Vertex}, G.Path i j → H.Path (vertex i) (vertex j)
  /-- An empty original word remains empty at its named vertex. -/
  path_nil : ∀ i : G.Vertex, path (.nil i) = .nil (vertex i)
  /-- Every original edge occurrence stays in its original temporal order. -/
  path_cons : ∀ {i j l : G.Vertex} (a : G.Edge i j) (w : G.Path j l),
    path (.cons a w) = .cons (edge a) (path w)
  /-- Every shared original authored face has its named image. -/
  face : G.TwoCell → H.TwoCell
  /-- Shared authored faces remain distinct. -/
  face_injective : Function.Injective face
  /-- Each mapped authored face retains its actual initial vertex. -/
  face_source : ∀ f, H.twoSource (face f) = vertex (G.twoSource f)
  /-- Each mapped authored face retains its actual terminal vertex. -/
  face_target : ∀ f, H.twoTarget (face f) = vertex (G.twoTarget f)
  /-- Every occurrence in the left authored word is the mapped old occurrence. -/
  face_left : ∀ f, HEq (path (G.twoLeft f)) (H.twoLeft (face f))
  /-- Every occurrence in the right authored word is the mapped old occurrence. -/
  face_right : ∀ f, HEq (path (G.twoRight f)) (H.twoRight (face f))
  /-- The actual typed step at mapped complete paths. -/
  step : ∀ {i j : G.Vertex} {w z : G.Path i j},
    RewriteStep G.toFiniteTransportTwoPresentation w z →
      RewriteStep H.toFiniteTransportTwoPresentation (path w) (path z)
  /-- Every mapped step uses exactly the same named shared face. -/
  step_face : ∀ {i j : G.Vertex} {w z : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z), (step s).face.cell = face s.face.cell
  /-- Every mapped step retains its complete original prefix. -/
  step_incoming : ∀ {i j : G.Vertex} {w z : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z),
    HEq (path s.face.incoming) (step s).face.incoming
  /-- Every mapped step retains its complete original suffix. -/
  step_outgoing : ∀ {i j : G.Vertex} {w z : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z),
    HEq (path s.face.outgoing) (step s).face.outgoing
  /-- Every mapped step retains its original orientation. -/
  step_orientation : ∀ {i j : G.Vertex} {w z : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z), (step s).face.orientation = s.face.orientation
  /-- The full route at mapped bookends, including every original step. -/
  route : ∀ {i j : G.Vertex} {w z : G.Path i j},
    RewritePasting G.toFiniteTransportTwoPresentation w z →
      RewritePasting H.toFiniteTransportTwoPresentation (path w) (path z)
  /-- Empty routes remain empty at their actual complete path. -/
  route_nil : ∀ {i j : G.Vertex} (w : G.Path i j), route (.nil w) = .nil (path w)
  /-- Every original temporal route step is retained in the same order. -/
  route_cons : ∀ {i j : G.Vertex} {w z u : G.Path i j}
    (s : RewriteStep G.toFiniteTransportTwoPresentation w z)
    (p : RewritePasting G.toFiniteTransportTwoPresentation z u), route (.cons s p) = .cons (step s) (route p)
  /-- Every shared original three-cell has its named image. -/
  triple : G.ThreeCell → H.ThreeCell
  /-- Shared original three-cells remain distinct. -/
  triple_injective : Function.Injective triple
  /-- The mapped three-cell retains its original initial vertex. -/
  triple_source : ∀ f, H.threeSource (triple f) = vertex (G.threeSource f)
  /-- The mapped three-cell retains its original terminal vertex. -/
  triple_target : ∀ f, H.threeTarget (triple f) = vertex (G.threeTarget f)
  /-- The mapped three-cell retains its exact complete starting word. -/
  triple_start : ∀ f, HEq (path (G.threeStart f)) (H.threeStart (triple f))
  /-- The mapped three-cell retains its exact complete finishing word. -/
  triple_finish : ∀ f, HEq (path (G.threeFinish f)) (H.threeFinish (triple f))
  /-- Every face, context and bookend of the left route is retained. -/
  triple_left : ∀ f, HEq (route (G.threeLeft f)) (H.threeLeft (triple f))
  /-- Every face, context and bookend of the right route is retained. -/
  triple_right : ∀ f, HEq (route (G.threeRight f)) (H.threeRight (triple f))

namespace FinitePresentationEmbedding
variable {G H : FiniteTransportPresentation.{uG}}

/-- The induced complete original edge name retains both typed endpoint names. -/
def edgeName (m : FinitePresentationEmbedding G H) (e : EdgeName (K := G)) : EdgeName (K := H) :=
  ⟨m.vertex e.1,m.vertex e.2.1,m.edge e.2.2⟩

/-- The geometric word-map laws determine the computed full original mapped word. -/
theorem path_computed (m : FinitePresentationEmbedding G H)
    {i j : G.Vertex} (w : G.Path i j) :
    m.path w = embeddedPath m.vertex m.edge w := by
  induction w with
  | nil _ => exact m.path_nil _
  | cons e w ih => rw [m.path_cons,embeddedPath,ih]

/-- Every original affine word is evaluated after mapping precisely its original operations. -/
theorem path_map_append (m : FinitePresentationEmbedding G H)
    {i j l : G.Vertex} (w : G.Path i j) (z : G.Path j l) :
    m.path (w.append z) = (m.path w).append (m.path z) := by
  induction w with
  | nil _ => simp only [PresentedPath.append,m.path_nil]
  | cons e w ih => simp only [PresentedPath.append,m.path_cons,ih]

end FinitePresentationEmbedding
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
