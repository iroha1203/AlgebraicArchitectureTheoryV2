import ResearchLean.AG.RelativeRepairComposition.NativeAffineCoefficients

/-! # Original affine word evaluation and authored three-cell comparisons -/
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
local notation "π" => projection (k := k) (A := A)

/-- The actual selected tower path is the same original reference word. -/
theorem tower_path_value {i j : K.Vertex} (w : K.Path i j) :
    (tower K L R c hfaces).toTower.upper.pathLift w = GroupExtension.pathValue K R w :=
  selected_path_value K L R w

/-- A primitive whiskered comparison is its actual affine conjugation through the outgoing word. -/
def faceOperation {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) : Operations k A :=
  let word := GroupExtension.pathValue K R f.outgoing
  let op := match f.orientation with
    | .forward => translation (k := k) (c f.cell)
    | .backward => (translation (k := k) (c f.cell))⁻¹
  word * op * word⁻¹

/-- A primitive authored route evaluates every original oriented face in temporal order. -/
def pastingOperation {i j : K.Vertex} {w z : K.Path i j} :
    RewritePasting K.toFiniteTransportTwoPresentation w z → Operations k A
  | .nil _ => 1
  | .cons step tail => pastingOperation tail * faceOperation K R c step.face

/-- Strong factorization gives real affine conjugation for every original transported automorphism. -/
theorem whisker_value {i j : K.Vertex}
    (a : FiberAut (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
      ((tower K L R c hfaces).original.object i)) (w : K.Path i j) :
    FiberAut.hom (Arbitrary.whiskerFiberAut (tower K L R c hfaces).toTower.upper 1 a w) =
      GroupExtension.pathValue K R w * FiberAut.hom a * (GroupExtension.pathValue K R w)⁻¹ := by
  have hf := Arbitrary.whiskerFiberAut_fac (tower K L R c hfaces).toTower.upper 1 a w
  rw [Arbitrary.reselectedPathLift_one] at hf
  unfold Arbitrary.fiberAutThenPath at hf
  rw [Arbitrary.reselectedPathLift_one, tower_path_value] at hf
  change (show Operations k A from FiberAut.hom
    (Arbitrary.whiskerFiberAut (tower K L R c hfaces).toTower.upper 1 a w)) *
    GroupExtension.pathValue K R w = GroupExtension.pathValue K R w *
      (show Operations k A from FiberAut.hom a) at hf
  change (show Operations k A from FiberAut.hom
    (Arbitrary.whiskerFiberAut (tower K L R c hfaces).toTower.upper 1 a w)) = _
  exact (eq_mul_inv_iff_mul_eq).mpr hf

/-- The native authored oriented face retains the same real primitive affine comparison. -/
theorem authored_face_value {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    FiberAut.hom (Arbitrary.orientedFaceAuthoredComparator
      (tower K L R c hfaces).toTower.toTransportData 1 f) = faceOperation K R c f := by
  unfold Arbitrary.orientedFaceAuthoredComparator Arbitrary.orientedFaceComparator
    Arbitrary.authoredComparatorFamily
  cases hor : f.orientation with
  | forward =>
    simpa only [faceOperation, hor] using
      whisker_value K L R c hfaces ((tower K L R c hfaces).comparator f.cell) f.outgoing
  | backward =>
    have h := whisker_value K L R c hfaces ((tower K L R c hfaces).comparator f.cell)⁻¹ f.outgoing
    simpa only [faceOperation, hor] using h

/-- All native authored route comparisons preserve the full primitive affine operation. -/
theorem authored_pasting_value {i j : K.Vertex} {w z : K.Path i j}
    (P : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    FiberAut.hom (Arbitrary.authoredPastingComparator
      (tower K L R c hfaces).toTower.toTransportData 1 P) = pastingOperation K R c P := by
  induction P with
  | nil _ => rfl
  | cons step tail ih =>
    change FiberAut.hom
      (Arbitrary.authoredPastingComparator (tower K L R c hfaces).toTower.toTransportData 1 tail *
        Arbitrary.orientedFaceAuthoredComparator (tower K L R c hfaces).toTower.toTransportData 1 step.face) = _
    change (show Operations k A from FiberAut.hom
      (Arbitrary.authoredPastingComparator (tower K L R c hfaces).toTower.toTransportData 1 tail)) *
      (show Operations k A from FiberAut.hom
        (Arbitrary.orientedFaceAuthoredComparator (tower K L R c hfaces).toTower.toTransportData 1 step.face)) = _
    rw [ih, authored_face_value]
    rfl

/-- Real equality of primitive three-cell route operations generates A's authored syzygy. -/
theorem authored_syzygy
    (hthree : ∀ s : K.ThreeCell,
      pastingOperation K R c (K.threeLeft s) = pastingOperation K R c (K.threeRight s)) :
    ∀ s : K.ThreeCell, AuthoredSyzygy (tower K L R c hfaces).toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s) := by
  intro s
  unfold AuthoredSyzygy
  apply Subtype.ext
  apply Iso.ext
  exact (authored_pasting_value K L R c hfaces _).trans
    ((hthree s).trans (authored_pasting_value K L R c hfaces _).symm)

/-- The generated canonical face comparison is the right reference word times inverse left word. -/
theorem canonical_face_value (f : K.TwoCell) :
    FiberAut.hom ((tower K L R c hfaces).toTower.canonicalFace f) =
      GroupExtension.pathValue K R (K.twoRight f) *
        (GroupExtension.pathValue K R (K.twoLeft f))⁻¹ := by
  have h := Arbitrary.canonicalFiberComparator_fac
    (GroupExtension.projection π ⋙ GroupExtension.terminal (A ≃ₗ[k] A))
    ((tower K L R c hfaces).toTower.upper.pathBase (K.twoLeft f))
    ((tower K L R c hfaces).toTower.upper.pathLift (K.twoLeft f))
    ((tower K L R c hfaces).toTower.upper.pathLift (K.twoRight f))
    ((tower K L R c hfaces).toTower.upper.pathLift_isStronglyCocartesian (K.twoLeft f))
    (by rw [(tower K L R c hfaces).toTower.faceBase f]
        exact (tower K L R c hfaces).toTower.upper.pathLift_isStronglyCocartesian (K.twoRight f))
  change (tower K L R c hfaces).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((tower K L R c hfaces).toTower.canonicalFace f) =
      (tower K L R c hfaces).toTower.upper.pathLift (K.twoRight f) at h
  rw [tower_path_value, tower_path_value] at h
  change (show Operations k A from FiberAut.hom
    ((tower K L R c hfaces).toTower.canonicalFace f)) *
      GroupExtension.pathValue K R (K.twoLeft f) = GroupExtension.pathValue K R (K.twoRight f) at h
  change (show Operations k A from FiberAut.hom
    ((tower K L R c hfaces).toTower.canonicalFace f)) = _
  exact (eq_mul_inv_iff_mul_eq).mpr h

/-- The actual original face defect evaluates the same authored translation and original words. -/
theorem defect_value (f : K.TwoCell) :
    coefficient K L R c hfaces (K.twoTarget f) ((tower K L R c hfaces).toTower.defect f) =
      (translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) *
        (GroupExtension.pathValue K R (K.twoRight f))⁻¹) 0 := by
  have h := congrArg (GroupExtension.upperEquiv π).symm
    ((tower K L R c hfaces).toTower.faceDefect_inclusion f)
  rw [map_mul, map_inv] at h
  change FiberAut.hom (kernelInclusion (GroupExtension.projection π)
    (GroupExtension.terminal (A ≃ₗ[k] A)) ((tower K L R c hfaces).original.object (K.twoTarget f))
    (Additive.toMul ((tower K L R c hfaces).toTower.defect f))) =
      translation (k := k) (c f) *
        (show Operations k A from FiberAut.hom ((tower K L R c hfaces).toTower.canonicalFace f))⁻¹ at h
  rw [coefficient_inclusion, canonical_face_value, mul_inv_rev, inv_inv, ← mul_assoc] at h
  have hh := congrArg (fun g : Operations k A => g 0) h
  simpa using hh

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
