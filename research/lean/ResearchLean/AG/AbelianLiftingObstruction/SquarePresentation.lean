import ResearchLean.AG.AbelianLiftingObstruction.TowerPresentation

/-!
# The shared one-loop square presentation

G-129 completion criteria 2–4 use the same presentation: one vertex, one
loop `e`, a face `e² ⇒ ∅`, and a 3-cell comparing deletion of the first and
last `e²` in `e³`. The two typed pastings remain distinct input syntax.
-/

namespace AAT.AG.AbelianLiftingObstruction

open TransportCoherence

/-- The unique edge occurrence in the shared one-vertex graph. -/
def squareEdge : PresentedPath (fun (_ _ : Unit) => Unit) () () :=
  .cons () (.nil ())

/-- The repeated edge path `e²`; both occurrences are retained. -/
def squareTwo : PresentedPath (fun (_ _ : Unit) => Unit) () () :=
  .cons () squareEdge

/-- The repeated edge path `e³`. -/
def squareThree : PresentedPath (fun (_ _ : Unit) => Unit) () () :=
  .cons () squareTwo

/-- The two-dimensional skeleton with `e² ⇒ ∅`. -/
def squareTwoPresentation : FiniteTransportTwoPresentation where
  Vertex := Unit
  vertexFintype := inferInstance
  Edge := fun _ _ => Unit
  edgeFintype := fun _ _ => inferInstance
  TwoCell := Unit
  twoCellFintype := inferInstance
  twoSource := fun _ => ()
  twoTarget := fun _ => ()
  twoLeft := fun _ => squareTwo
  twoRight := fun _ => .nil ()

/-- Delete the first two edges of `e³`, retaining the final edge as suffix. -/
def squareFirstFace : WhiskeredFace squareTwoPresentation () () where
  cell := ()
  incoming := .nil ()
  outgoing := squareEdge
  orientation := .forward

/-- Delete the last two edges of `e³`, retaining the first edge as prefix. -/
def squareLastFace : WhiskeredFace squareTwoPresentation () () where
  cell := ()
  incoming := squareEdge
  outgoing := .nil ()
  orientation := .forward

/-- The first deletion is a typed rewrite from `e³` to `e`. -/
def squareFirstStep : RewriteStep squareTwoPresentation squareThree squareEdge where
  face := squareFirstFace
  before_eq := rfl
  after_eq := rfl

/-- The last deletion is a typed rewrite from `e³` to `e`. -/
def squareLastStep : RewriteStep squareTwoPresentation squareThree squareEdge where
  face := squareLastFace
  before_eq := rfl
  after_eq := rfl

/-- The common finite 0–3 presentation used by all three specified examples. -/
def squarePresentation : FiniteTransportPresentation where
  toFiniteTransportTwoPresentation := squareTwoPresentation
  ThreeCell := Unit
  threeCellFintype := inferInstance
  threeSource := fun _ => ()
  threeTarget := fun _ => ()
  threeStart := fun _ => squareThree
  threeFinish := fun _ => squareEdge
  threeLeft := fun _ => by
    change RewritePasting squareTwoPresentation squareThree squareEdge
    exact .cons squareFirstStep
      (@RewritePasting.nil squareTwoPresentation () () squareEdge)
  threeRight := fun _ => by
    change RewritePasting squareTwoPresentation squareThree squareEdge
    exact .cons squareLastStep
      (@RewritePasting.nil squareTwoPresentation () () squareEdge)

/-- G-129 A3: the square's vertex differential is `1 - ρ`. -/
theorem square_d0 (M : LocalCoefficients squarePresentation)
    (b : C0 M) :
    d0 M b ⟨(), (), ()⟩ = b () - M.edge () (b ()) := rfl

/-- G-129 A3: the square's face differential is `ρ + 1`, counting both edges. -/
theorem square_d1 (M : LocalCoefficients squarePresentation)
    (h : C1 M) :
    d1 M h () = M.edge () (h ⟨(), (), ()⟩) + h ⟨(), (), ()⟩ := by
  simp [d1, squarePresentation, squareTwoPresentation, squareTwo,
    squareEdge, pathCorrection, EdgeCoefficients.pathTransport,
    LocalCoefficients.pathTransport]

/-- G-129 A3: the square's 3-cell differential is `ρ - 1`. -/
theorem square_d2 (M : LocalCoefficients squarePresentation)
    (c : C2 M) :
    d2 M c () = M.edge () (c ()) - c () := by
  simp [d2, squarePresentation, squareTwoPresentation, squareFirstStep,
    squareLastStep, squareFirstFace, squareLastFace, squareEdge,
    faceCorrection, pastingCorrection, EdgeCoefficients.pathTransport,
    LocalCoefficients.pathTransport]

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
