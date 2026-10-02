import ResearchLean.AG.RelativeRepairComposition.SubdivisionThreeLaws
import ResearchLean.AG.RelativeRepairComposition.SubdivisionVertexLabels

/-!
# Full original coefficient words and differentials under actual subdivision

Every original path occurrence is replaced by the same two actual factors.
Actual whiskering identifies the entire kernel transport, and the correction
sum then identifies both face words and every signed authored three-cell route.

## Implementation notes

The coefficient maps are generated from actual full kernels and actual selected
arrows. Whiskering and its inclusion API prove path transport equality without
assuming a constant coefficient group or a new comparison certificate. Word
induction counts all occurrences; checking only generator edges would not prove
the face and complete three-cell differential equations.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)

/-- The actual entire kernel transport agrees on every complete substituted old word. -/
theorem kernel_path_substitute {i j : K.Vertex} (w : K.Path i j)
    (a : Kernel p q (T.original.object i)) :
    (originalTower T chosen F).toTower.pathKernelTransportHom (substitutePath K chosen w) a =
      T.toTower.pathKernelTransportHom w a := by
  apply kernelInclusion_injective p q _
  have hn := (originalTower T chosen F).toTower.whisker_kernel (substitutePath K chosen w) a
  have ho := T.toTower.whisker_kernel w a
  exact hn.symm.trans ((whisker_substitute T chosen F (kernelInclusion p q _ a) w).trans ho)

/-- Full additive coefficient transport keeps every original word and every original kernel value. -/
theorem coefficient_path_substitute {i j : K.Vertex} (w : K.Path i j)
    (a : T.toTower.localCoefficients.A i) :
    (originalTower T chosen F).toTower.localCoefficients.pathTransport
        (substitutePath K chosen w) a = T.toTower.localCoefficients.pathTransport w a := by
  calc
    _ = Additive.ofMul ((originalTower T chosen F).toTower.pathKernelTransportHom
        (substitutePath K chosen w) (Additive.toMul a)) :=
      (originalTower T chosen F).toTower.edgeCoefficients_pathTransport _ _
    _ = Additive.ofMul (T.toTower.pathKernelTransportHom w (Additive.toMul a)) :=
      congrArg (fun b : Kernel p q (T.original.object j) => Additive.ofMul b)
        (kernel_path_substitute T chosen F w (Additive.toMul a))
    _ = _ := (T.toTower.edgeCoefficients_pathTransport w (Additive.toMul a)).symm

/-- Each replaced edge word has exactly its collapsed full correction. -/
theorem correction_edge_word
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    (e : EdgeName (K := K)) :
    pathCorrection (originalTower T chosen F).toTower.localCoefficients h (edgeWord K chosen e) =
      collapseCorrection T chosen F h e := by
  classical
  by_cases he : e = chosen
  · subst e
    rw [edgeWord_chosen, collapseCorrection_chosen]
    let hf : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) :=
      h (firstEdgeName K chosen)
    let hs : T.toTower.localCoefficients.A chosen.2.1 := h (secondEdgeName K chosen)
    let rt : T.toTower.localCoefficients.A chosen.2.1 :=
      (originalTower T chosen F).toTower.localCoefficients.edge (secondEdge K chosen) hf
    let r : T.toTower.localCoefficients.A chosen.2.1 := rho2Add T chosen F hf
    change rt + (hs + 0) = hs + r
    have hr : rt = r := by
      change (originalTower T chosen F).toTower.localCoefficients.edge (secondEdge K chosen) hf =
        rho2Add T chosen F hf
      rw [coefficient_edge_second]
      rfl
    rw [hr, add_zero]
    exact add_comm _ _
  · rw [edgeWord_old K chosen e he, collapseCorrection_old T chosen F h e he]
    change h (oldEdgeName K chosen e he) + 0 = h (oldEdgeName K chosen e he)
    exact add_zero _

/-- All occurrences in an arbitrary full old typed word use the same collapsed correction. -/
theorem pathCorrection_substitute
    (h : C1 (originalTower T chosen F).toTower.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    pathCorrection (originalTower T chosen F).toTower.localCoefficients h
        (substitutePath K chosen w) =
      pathCorrection T.toTower.localCoefficients (collapseCorrection T chosen F h) w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change pathCorrection (originalTower T chosen F).toTower.localCoefficients h
      ((edgeWord K chosen ⟨_,_,e⟩).append (substitutePath K chosen w)) = _
    rw [pathCorrection_append, correction_edge_word, coefficient_path_substitute, ih]
    rfl

/-- The full original face differential is preserved by the same actual correction collapse. -/
theorem d1_collapse
    (h : C1 (originalTower T chosen F).toTower.localCoefficients) :
    d1 (originalTower T chosen F).toTower.localCoefficients h =
      d1 T.toTower.localCoefficients (collapseCorrection T chosen F h) := by
  funext f
  change pathCorrection (originalTower T chosen F).toTower.localCoefficients h
        (substitutePath K chosen (K.twoLeft f)) -
      pathCorrection (originalTower T chosen F).toTower.localCoefficients h
        (substitutePath K chosen (K.twoRight f)) = _
  rw [pathCorrection_substitute, pathCorrection_substitute]
  rfl

/-- Every oriented face occurrence keeps its signed full coefficient value in its full outgoing word. -/
theorem faceCorrection_substitute (c : C2 T.toTower.localCoefficients)
    {i j : K.Vertex} (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    faceCorrection (originalTower T chosen F).toTower.localCoefficients c
        (substituteFace K chosen f) = faceCorrection T.toTower.localCoefficients c f := by
  rcases f with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation with
  | forward =>
    change (originalTower T chosen F).toTower.localCoefficients.pathTransport
      (substitutePath K chosen outgoing) (c cell) =
      T.toTower.localCoefficients.pathTransport outgoing (c cell)
    exact coefficient_path_substitute T chosen F outgoing (c cell)
  | backward =>
    change -((originalTower T chosen F).toTower.localCoefficients.pathTransport
      (substitutePath K chosen outgoing) (c cell)) =
      -(T.toTower.localCoefficients.pathTransport outgoing (c cell))
    exact congrArg (fun a : T.toTower.localCoefficients.A j => -a)
      (coefficient_path_substitute T chosen F outgoing (c cell))

/-- Every step of a complete authored old route has the same full signed correction after subdivision. -/
theorem pastingCorrection_substitute (c : C2 T.toTower.localCoefficients)
    {i j : K.Vertex} {w z : K.Path i j}
    (t : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingCorrection (originalTower T chosen F).toTower.localCoefficients c
        (substitutePasting K chosen t) = pastingCorrection T.toTower.localCoefficients c t := by
  induction t with
  | nil _ => rfl
  | cons s t ih =>
    change faceCorrection (originalTower T chosen F).toTower.localCoefficients c
        (substituteFace K chosen s.face) +
      pastingCorrection (originalTower T chosen F).toTower.localCoefficients c
        (substitutePasting K chosen t) = _
    rw [faceCorrection_substitute, ih]
    rfl

/-- Both complete authored routes of every original three-cell retain the same full differential. -/
theorem d2_substitute (c : C2 T.toTower.localCoefficients) :
    d2 (originalTower T chosen F).toTower.localCoefficients c = d2 T.toTower.localCoefficients c := by
  funext s
  change pastingCorrection (originalTower T chosen F).toTower.localCoefficients c
      (substitutePasting K chosen (K.threeLeft s)) -
    pastingCorrection (originalTower T chosen F).toTower.localCoefficients c
      (substitutePasting K chosen (K.threeRight s)) = _
  rw [pastingCorrection_substitute, pastingCorrection_substitute]
  rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
