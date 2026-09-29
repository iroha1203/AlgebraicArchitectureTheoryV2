import ResearchLean.AG.AbelianLiftingObstruction.Correction

/-!
# The obstruction class for the original fixed core selection

Every alternative lift of the same fixed core value is compared with the
original lift by an element of the actual projection kernel. This comparison
is made on the original arrows before passing to the cohomology class.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

namespace TowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)

/-- The actual B1 defect as a cycle of its own finite presentation complex. -/
noncomputable def obstructionCocycle
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    Z2 T.localCoefficients :=
  ⟨T.defect, T.defect_cocycle hsyzygy⟩

/-- The degree-two obstruction class of the original selected arrows. -/
noncomputable def obstructionClass
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    H2 T.localCoefficients :=
  QuotientAddGroup.mk (T.obstructionCocycle hsyzygy)

/-- Every actually corrected defect is a cycle in the same complex. -/
noncomputable def correctedObstructionCocycle
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (h : C1 T.localCoefficients) : Z2 T.localCoefficients :=
  ⟨T.correctedDefect h, by
    change d2 T.localCoefficients (T.correctedDefect h) = 0
    rw [T.correctedDefect_eq h, d2_add, T.defect_cocycle hsyzygy, d2_d1]
    simp⟩

/-- B2 makes the class of every actual kernel correction equal to the original class. -/
theorem correctedObstructionClass_eq
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (h : C1 T.localCoefficients) :
    (QuotientAddGroup.mk (T.correctedObstructionCocycle hsyzygy h) :
      H2 T.localCoefficients) = T.obstructionClass hsyzygy := by
  rw [obstructionClass, QuotientAddGroup.eq_iff_sub_mem]
  rw [AddMonoidHom.mem_range]
  refine ⟨h, ?_⟩
  apply Subtype.ext
  change d1 T.localCoefficients h = T.correctedDefect h - T.defect
  rw [T.correctedDefect_eq h]
  abel

end TowerPresentation

namespace OriginalTowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The unique actual-kernel difference between any other lift and the supplied one. -/
noncomputable def alternativeCorrection
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    C1 T.toTower.localCoefficients :=
  fun ⟨_, j, e⟩ => Additive.ofMul
    (liftDifference p q (T.original.object j) (other e) (T.lift e)
      ((hother e).trans (T.lift_core e).symm))

/-- The alternative actual selected edge is the corrected original selected edge. -/
theorem alternativeEdge_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (e : K.Edge i j) :
    reselectedEdgeLift T.toTower.upper
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) e =
      (selectedUpper K p q T.original other).edgeLift e := by
  let d := liftDifference p q (T.original.object j) (other e) (T.lift e)
    ((hother e).trans (T.lift_core e).symm)
  change (T.original.edgeLift e ≫ FiberAut.hom (T.lift e)) ≫
      FiberAut.hom (kernelInclusion p q _ d) =
    T.original.edgeLift e ≫ FiberAut.hom (other e)
  calc
    _ = T.original.edgeLift e ≫
        (FiberAut.hom (T.lift e) ≫ FiberAut.hom (kernelInclusion p q _ d)) :=
          Category.assoc _ _ _
    _ = T.original.edgeLift e ≫
        FiberAut.hom (kernelInclusion p q _ d * T.lift e) := rfl
    _ = _ := by rw [liftDifference_mul p q _ (other e) (T.lift e)
      ((hother e).trans (T.lift_core e).symm)]

/-- The equality of actual selected arrows extends to every typed original path. -/
theorem alternativePath_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (w : K.Path i j) :
    reselectedPathLift T.toTower.upper
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) w =
      (selectedUpper K p q T.original other).pathLift w := by
  induction w with
  | nil v => rfl
  | cons e tail ih =>
      change reselectedEdgeLift T.toTower.upper
          (T.toTower.correctionReselection (T.alternativeCorrection other hother)) e ≫
            reselectedPathLift T.toTower.upper
              (T.toTower.correctionReselection (T.alternativeCorrection other hother)) tail =
        (selectedUpper K p q T.original other).edgeLift e ≫
          (selectedUpper K p q T.original other).pathLift tail
      rw [T.alternativeEdge_eq other hother e, ih]

/-- The original presentation with the alternative actual edge lifts and unchanged authored comparisons. -/
def alternativeTransportData
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j)) :
    TransportData K.toFiniteTransportTwoPresentation (p ⋙ q) where
  lift := selectedUpper K p q T.original other
  faceBase := by
    intro f
    rw [selectedUpper_pathBase, selectedUpper_pathBase]
    exact T.faceBase f
  comparator := T.comparator

/-- The canonical comparator from alternative original arrows equals the corrected comparator. -/
theorem alternativeCanonical_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (f : K.TwoCell) :
    canonicalFaceComparator (T.alternativeTransportData other) 1 f =
      canonicalFaceComparator T.toTower.toTransportData
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) f := by
  let h := T.alternativeCorrection other hother
  have hl := T.alternativePath_eq other hother (K.twoLeft f)
  have hr := T.alternativePath_eq other hother (K.twoRight f)
  apply FiberAut.ext_of_strong_fac
    (reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h)
      (K.twoLeft f))
    (reselectedPathLift_isStronglyCocartesian T.toTower.upper
      (T.toTower.correctionReselection h) (K.twoLeft f))
  have hleft : reselectedPathLift (T.alternativeTransportData other).lift 1
      (K.twoLeft f) =
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h)
        (K.twoLeft f) := by
    rw [Arbitrary.reselectedPathLift_one]
    exact hl.symm
  have hright : reselectedPathLift (T.alternativeTransportData other).lift 1
      (K.twoRight f) =
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h)
        (K.twoRight f) := by
    rw [Arbitrary.reselectedPathLift_one]
    exact hr.symm
  have ha := canonicalFaceComparator_fac (T.alternativeTransportData other) 1 f
  have hb := canonicalFaceComparator_fac T.toTower.toTransportData
    (T.toTower.correctionReselection h) f
  rw [hleft, hright] at ha
  exact ha.trans hb.symm

/-- The existing raw defect of the alternative original lift is the actual corrected raw defect. -/
theorem alternativeRawDefect_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (f : K.TwoCell) :
    rawFaceDefect (T.alternativeTransportData other) 1 f =
      kernelInclusion p q _
        (T.toTower.correctedFaceDefect (T.alternativeCorrection other hother) f) := by
  rw [T.toTower.correctedFaceDefect_eq_raw
    (T.alternativeCorrection other hother) f]
  unfold rawFaceDefect
  rw [T.alternativeCanonical_eq other hother f]
  rfl

/-- Whiskering by alternative original arrows is the same as whiskering by their correction. -/
theorem alternativeWhisker_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (u : FiberAut (p ⋙ q) (T.original.object i))
    (w : K.Path i j) :
    whiskerFiberAut (T.alternativeTransportData other).lift 1 u w =
      whiskerFiberAut T.toTower.upper
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) u w := by
  let h := T.alternativeCorrection other hother
  have hp : reselectedPathLift (T.alternativeTransportData other).lift 1 w =
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) w := by
    rw [Arbitrary.reselectedPathLift_one]
    exact (T.alternativePath_eq other hother w).symm
  apply FiberAut.ext_of_strong_fac
    (reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) w)
    (reselectedPathLift_isStronglyCocartesian T.toTower.upper
      (T.toTower.correctionReselection h) w)
  calc
    _ = reselectedPathLift (T.alternativeTransportData other).lift 1 w ≫
        FiberAut.hom
          (whiskerFiberAut (T.alternativeTransportData other).lift 1 u w) := by
            rw [hp]
    _ = FiberAut.hom u ≫
        reselectedPathLift (T.alternativeTransportData other).lift 1 w :=
          Arbitrary.whiskerFiberAut_fac
            (T.alternativeTransportData other).lift 1 u w
    _ = FiberAut.hom u ≫
        reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) w := by
          rw [hp]
    _ = _ := (Arbitrary.whiskerFiberAut_fac T.toTower.upper
      (T.toTower.correctionReselection h) u w).symm

/-- Alternative actual arrows retain every oriented authored face comparator. -/
theorem alternativeOrientedAuthored_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) :
    orientedFaceAuthoredComparator (T.alternativeTransportData other) 1 f =
      orientedFaceAuthoredComparator T.toTower.toTransportData
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) f := by
  rcases f with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation with
  | forward =>
      change whiskerFiberAut (T.alternativeTransportData other).lift 1
          (T.comparator cell) outgoing =
        whiskerFiberAut T.toTower.upper
          (T.toTower.correctionReselection (T.alternativeCorrection other hother))
          (T.comparator cell) outgoing
      exact T.alternativeWhisker_eq other hother (T.comparator cell) outgoing
  | backward =>
      change whiskerFiberAut (T.alternativeTransportData other).lift 1
          (T.comparator cell)⁻¹ outgoing =
        whiskerFiberAut T.toTower.upper
          (T.toTower.correctionReselection (T.alternativeCorrection other hother))
          (T.comparator cell)⁻¹ outgoing
      exact T.alternativeWhisker_eq other hother (T.comparator cell)⁻¹ outgoing

/-- Alternative original arrows give the same authored comparison on every typed pasting. -/
theorem alternativeAuthoredPasting_eq
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {source target : K.Vertex} {before after : K.Path source target}
    (P : RewritePasting K.toFiniteTransportTwoPresentation before after) :
    authoredPastingComparator (T.alternativeTransportData other) 1 P =
      authoredPastingComparator T.toTower.toTransportData
        (T.toTower.correctionReselection (T.alternativeCorrection other hother)) P := by
  induction P with
  | nil _ => rfl
  | cons step tail ih =>
      change authoredPastingComparator (T.alternativeTransportData other) 1 tail *
          orientedFaceAuthoredComparator (T.alternativeTransportData other) 1 step.face =
        authoredPastingComparator T.toTower.toTransportData
            (T.toTower.correctionReselection (T.alternativeCorrection other hother)) tail *
          orientedFaceAuthoredComparator T.toTower.toTransportData
            (T.toTower.correctionReselection (T.alternativeCorrection other hother)) step.face
      rw [ih, T.alternativeOrientedAuthored_eq other hother step.face]

/-- The original designated 3-cell syzygy holds for every other lift of the same core. -/
theorem alternativeAuthoredSyzygy
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (s : K.ThreeCell) :
    AuthoredSyzygy (T.alternativeTransportData other) 1
      (K.threeLeft s) (K.threeRight s) := by
  unfold AuthoredSyzygy
  rw [T.alternativeAuthoredPasting_eq other hother (K.threeLeft s),
    T.alternativeAuthoredPasting_eq other hother (K.threeRight s)]
  exact T.toTower.authoredSyzygy_correction_invariant
    (T.alternativeCorrection other hother) hsyzygy s

/-- The face cochain reconstructed from alternative original arrows in the same actual kernel. -/
noncomputable def alternativeDefect
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    C2 T.toTower.localCoefficients :=
  T.toTower.correctedDefect (T.alternativeCorrection other hother)

/-- The alternative cochain includes to the raw defect of the actual alternative arrows. -/
theorem alternativeDefect_eq_raw
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (f : K.TwoCell) :
    kernelInclusion p q _ (Additive.toMul (T.alternativeDefect other hother f)) =
      rawFaceDefect (T.alternativeTransportData other) 1 f := by
  exact (T.alternativeRawDefect_eq other hother f).symm

/-- The H² class computed from every alternative lift of the same fixed core. -/
noncomputable def alternativeObstructionClass
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    H2 T.toTower.localCoefficients :=
  QuotientAddGroup.mk
    (T.toTower.correctedObstructionCocycle hsyzygy
      (T.alternativeCorrection other hother))

/-- G-129 B: the obstruction class is independent of all lifts of the same core selection. -/
theorem alternativeObstructionClass_eq
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    T.alternativeObstructionClass hsyzygy other hother =
      T.toTower.obstructionClass hsyzygy :=
  T.toTower.correctedObstructionClass_eq hsyzygy
    (T.alternativeCorrection other hother)

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
