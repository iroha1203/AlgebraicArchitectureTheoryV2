import ResearchLean.AG.RelativeRepairComposition.NativeAffineEvaluation
import ResearchLean.AG.RelativeRepairComposition.SupportedRepairs

/-! # Original typed differentials evaluated in real translation vectors -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))

/-- Transport along every original word evaluates its full reference linear component. -/
theorem path_coefficient {i j : K.Vertex} (w : K.Path i j) (x : (M).A i) :
    coefficient K L R c hfaces j ((M).pathTransport w x) =
      (GroupExtension.pathValue K R w).linear (coefficient K L R c hfaces i x) := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change coefficient K L R c hfaces _ ((M).pathTransport w ((M).edge e x)) = _
    rw [ih, edge_coefficient]
    rfl

/-- Each original edge occurrence contributes its terminal vector transported by the remaining real word. -/
def vectorPath (h : EdgeName (K := K) → A) : ∀ {i j : K.Vertex}, K.Path i j → A
  | _, _, .nil _ => 0
  | _, _, .cons e w => (GroupExtension.pathValue K R w).linear (h ⟨_, _, e⟩) + vectorPath h w

/-- Native full path corrections evaluate the occurrence-counting real vector expression. -/
theorem path_correction_value (h : C1 (M)) {i j : K.Vertex} (w : K.Path i j) :
    coefficient K L R c hfaces j (pathCorrection (M) h w) =
      vectorPath K R (fun e => coefficient K L R c hfaces e.2.1 (h e)) w := by
  induction w with
  | nil v => exact (coefficient K L R c hfaces v).map_zero
  | cons e w ih =>
    change coefficient K L R c hfaces _
      ((M).pathTransport w (h ⟨_, _, e⟩) + pathCorrection (M) h w) = _
    rw [map_add, path_coefficient, ih]
    rfl

/-- The original vertex differential is the target vector minus transported source vector. -/
theorem d0_value (b : C0 (M)) (e : EdgeName (K := K)) :
    coefficient K L R c hfaces e.2.1 (d0 (M) b e) =
      coefficient K L R c hfaces e.2.1 (b e.2.1) -
        (R e.2.2).linear (coefficient K L R c hfaces e.1 (b e.1)) := by
  change coefficient K L R c hfaces e.2.1 (b e.2.1 - (M).edge e.2.2 (b e.1)) = _
  rw [map_sub, edge_coefficient]

/-- The original face differential retains both authored temporal words and every occurrence. -/
theorem d1_value (h : C1 (M)) (f : K.TwoCell) :
    coefficient K L R c hfaces (K.twoTarget f) (d1 (M) h f) =
      vectorPath K R (fun e => coefficient K L R c hfaces e.2.1 (h e)) (K.twoLeft f) -
        vectorPath K R (fun e => coefficient K L R c hfaces e.2.1 (h e)) (K.twoRight f) := by
  change coefficient K L R c hfaces _
    (pathCorrection (M) h (K.twoLeft f) - pathCorrection (M) h (K.twoRight f)) = _
  rw [map_sub, path_correction_value, path_correction_value]

/-- Each typed whiskered face contributes its signed real outgoing linear transport. -/
def vectorFace (a : K.TwoCell → A) {s t : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) : A :=
  match f.orientation with
  | .forward => (GroupExtension.pathValue K R f.outgoing).linear (a f.cell)
  | .backward => -(GroupExtension.pathValue K R f.outgoing).linear (a f.cell)

/-- The vector comparison counts every signed typed face occurrence in the original pasting. -/
def vectorPasting (a : K.TwoCell → A) {s t : K.Vertex} {w z : K.Path s t} :
    RewritePasting K.toFiniteTransportTwoPresentation w z → A
  | .nil _ => 0
  | .cons step tail => vectorFace K R a step.face + vectorPasting a tail

/-- Native signed face corrections evaluate the real outgoing transport and specified orientation. -/
theorem face_correction_value (a : C2 (M)) {s t : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) :
    coefficient K L R c hfaces t (faceCorrection (M) a f) =
      vectorFace K R (fun g => coefficient K L R c hfaces (K.twoTarget g) (a g)) f := by
  cases ho : f.orientation <;>
    simp only [faceCorrection, vectorFace, ho, map_neg, path_coefficient]

/-- Native full pasting corrections evaluate every original signed real face occurrence. -/
theorem pasting_correction_value (a : C2 (M)) {s t : K.Vertex} {w z : K.Path s t}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    coefficient K L R c hfaces t (pastingCorrection (M) a p) =
      vectorPasting K R (fun g => coefficient K L R c hfaces (K.twoTarget g) (a g)) p := by
  induction p with
  | nil _ => exact (coefficient K L R c hfaces t).map_zero
  | cons step tail ih =>
    change coefficient K L R c hfaces t
      (faceCorrection (M) a step.face + pastingCorrection (M) a tail) = _
    rw [map_add, face_correction_value, ih]
    rfl

/-- The original degree-two differential evaluates both complete authored typed three-cell pastings. -/
theorem d2_value (a : C2 (M)) (s : K.ThreeCell) :
    coefficient K L R c hfaces (K.threeTarget s) (d2 (M) a s) =
      vectorPasting K R (fun g => coefficient K L R c hfaces (K.twoTarget g) (a g)) (K.threeLeft s) -
        vectorPasting K R (fun g => coefficient K L R c hfaces (K.twoTarget g) (a g)) (K.threeRight s) := by
  change coefficient K L R c hfaces _
    (pastingCorrection (M) a (K.threeLeft s) - pastingCorrection (M) a (K.threeRight s)) = _
  rw [map_sub, pasting_correction_value, pasting_correction_value]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
