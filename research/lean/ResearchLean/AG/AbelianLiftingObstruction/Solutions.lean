import ResearchLean.AG.AbelianLiftingObstruction.ObstructionClass

/-!
# Actual coherent lifts and vanishing of the obstruction

`Solution` is defined directly from the original edge arrows, the fixed core
values, and the authored equations on every face. The correction equation and
cohomology class enter only in theorems relating this independent solution set
to the obstruction.
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

/-- A corrected actual face defect vanishes exactly when its original authored face commutes. -/
theorem correctedDefect_eq_zero_iff_coherent (h : C1 T.localCoefficients) :
    T.correctedDefect h = 0 ↔
      CoherentAt T.toTransportData (T.correctionReselection h) := by
  constructor
  · intro hzero f
    have hcoord := congrFun hzero f
    have hker : T.correctedFaceDefect h f = 1 := by
      apply Additive.ofMul.injective
      simpa only [correctedDefect, Pi.zero_apply] using hcoord
    apply (rawFaceDefect_eq_one_iff_coherent T.toTransportData
      (T.correctionReselection h) f).mp
    rw [← T.correctedFaceDefect_eq_raw h f, hker]
    simp
  · intro hcoherent
    funext f
    have hraw := (rawFaceDefect_eq_one_iff_coherent T.toTransportData
      (T.correctionReselection h) f).mpr (hcoherent f)
    have hker : T.correctedFaceDefect h f = 1 := by
      apply kernelInclusion_injective p q _
      rw [T.correctedFaceDefect_eq_raw h f, hraw]
      simp
    change Additive.ofMul (T.correctedFaceDefect h f) = 0
    rw [hker]
    rfl

/-- B3's correction equation is exactly the zero-defect condition of actual reselected arrows. -/
theorem correctedDefect_eq_zero_iff_d1 (h : C1 T.localCoefficients) :
    T.correctedDefect h = 0 ↔
      d1 T.localCoefficients h = -T.defect := by
  rw [T.correctedDefect_eq h]
  rw [add_comm]
  exact add_eq_zero_iff_eq_neg

end TowerPresentation

/-- A genuine coherent lift of the fixed core selection, specified by original
edge arrows and all authored face equations. The reference lift is absent from
these fields. -/
structure Solution {K : FiniteTransportPresentation.{uG}}
    {E : Type uE} {B : Type uB} {D : Type uD}
    [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
    {p : E ⥤ B} {q : B ⥤ D}
    (T : OriginalTowerPresentation K p q) where
  choice : ∀ {i j : K.Vertex} (_ : K.Edge i j),
    FiberAut (p ⋙ q) (T.original.object j)
  choice_core : ∀ {i j : K.Vertex} (e : K.Edge i j),
    fiberPushforward p q (T.original.object j) (choice e) = T.core e
  face : ∀ f : K.TwoCell,
    (selectedUpper K p q T.original choice).pathLift (K.twoLeft f) ≫
      FiberAut.hom (T.comparator f) =
    (selectedUpper K p q T.original choice).pathLift (K.twoRight f)

namespace Solution

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable {T : OriginalTowerPresentation K p q}

theorem ext {S R : Solution T}
    (h : ∀ {i j : K.Vertex} (e : K.Edge i j), S.choice e = R.choice e) :
    S = R := by
  cases S with
  | mk c hc hf =>
    cases R with
    | mk d hd hg =>
      have hchoice : @c = @d := by
        funext i j e
        exact h e
      cases hchoice
      rfl

end Solution

namespace OriginalTowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- Apply an arbitrary actual-kernel cochain to the reference lifts of the fixed core. -/
noncomputable def correctionChoice (h : C1 T.toTower.localCoefficients) :
    ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j) :=
  fun {i j} e => kernelInclusion p q (T.original.object j)
    (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j)) * T.lift e

theorem correctionChoice_core (h : C1 T.toTower.localCoefficients)
    {i j : K.Vertex} (e : K.Edge i j) :
    fiberPushforward p q (T.original.object j) (T.correctionChoice h e) = T.core e := by
  let a : Kernel p q (T.original.object j) := Additive.toMul (h ⟨i, j, e⟩)
  have ha : fiberPushforward p q (T.original.object j)
      (kernelInclusion p q (T.original.object j) a) = 1 := a.property
  change fiberPushforward p q (T.original.object j)
      (kernelInclusion p q (T.original.object j) a * T.lift e) = T.core e
  rw [map_mul, ha, one_mul, T.lift_core e]

/-- Correcting the reference choice gives exactly the existing corrected edge arrow. -/
theorem correctionChoice_edge (h : C1 T.toTower.localCoefficients)
    {i j : K.Vertex} (e : K.Edge i j) :
    (selectedUpper K p q T.original (T.correctionChoice h)).edgeLift e =
      reselectedEdgeLift T.toTower.upper (T.toTower.correctionReselection h) e := by
  change T.original.edgeLift e ≫ FiberAut.hom
      (kernelInclusion p q (T.original.object j)
        (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j)) * T.lift e) =
    (T.original.edgeLift e ≫ FiberAut.hom (T.lift e)) ≫
      FiberAut.hom (kernelInclusion p q (T.original.object j)
        (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j)))
  exact (Category.assoc _ _ _).symm

/-- The equality extends to every actual path of the finite presentation. -/
theorem correctionChoice_path (h : C1 T.toTower.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K p q T.original (T.correctionChoice h)).pathLift w =
      reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) w := by
  induction w with
  | nil v => rfl
  | cons e tail ih =>
      change (selectedUpper K p q T.original (T.correctionChoice h)).edgeLift e ≫
          (selectedUpper K p q T.original (T.correctionChoice h)).pathLift tail =
        reselectedEdgeLift T.toTower.upper (T.toTower.correctionReselection h) e ≫
          reselectedPathLift T.toTower.upper (T.toTower.correctionReselection h) tail
      rw [T.correctionChoice_edge h e, ih]

/-- A solution of the correction equation produces an actual coherent lift. -/
noncomputable def solutionOfCorrection (h : C1 T.toTower.localCoefficients)
    (hh : d1 T.toTower.localCoefficients h = -T.toTower.defect) : Solution T where
  choice := T.correctionChoice h
  choice_core := T.correctionChoice_core h
  face := by
    intro f
    have hc := (T.toTower.correctedDefect_eq_zero_iff_coherent h).mp
      ((T.toTower.correctedDefect_eq_zero_iff_d1 h).mpr hh)
    simpa only [T.correctionChoice_path h (K.twoLeft f),
      T.correctionChoice_path h (K.twoRight f)] using hc f

/-- Each independent actual solution determines its unique actual-kernel correction. -/
noncomputable def solutionCorrection (S : Solution T) :
    C1 T.toTower.localCoefficients :=
  T.alternativeCorrection S.choice S.choice_core

/-- The actual face equations force the corrected defect to vanish. -/
theorem solutionCorrection_zero (S : Solution T) :
    T.toTower.correctedDefect (T.solutionCorrection S) = 0 := by
  funext f
  have hraw : rawFaceDefect (T.alternativeTransportData S.choice) 1 f = 1 :=
    (rawFaceDefect_eq_one_iff_coherent
      (T.alternativeTransportData S.choice) 1 f).mpr (by
        simpa only [Arbitrary.reselectedPathLift_one] using S.face f)
  have hker : T.toTower.correctedFaceDefect (T.solutionCorrection S) f = 1 := by
    apply kernelInclusion_injective p q _
    exact (T.alternativeRawDefect_eq S.choice S.choice_core f).symm.trans hraw
  change Additive.ofMul (T.toTower.correctedFaceDefect (T.solutionCorrection S) f) = 0
  rw [hker]
  rfl

/-- Every actual solution supplies a correction solving the fixed B3 equation. -/
theorem solutionCorrection_d1 (S : Solution T) :
    d1 T.toTower.localCoefficients (T.solutionCorrection S) =
      -T.toTower.defect :=
  (T.toTower.correctedDefect_eq_zero_iff_d1 (T.solutionCorrection S)).mp
    (T.solutionCorrection_zero S)

/-- Taking the actual kernel difference after a correction recovers that cochain. -/
theorem solutionCorrection_correctionChoice
    (h : C1 T.toTower.localCoefficients) :
    T.alternativeCorrection (T.correctionChoice h) (T.correctionChoice_core h) = h := by
  funext edge
  rcases edge with ⟨i, j, e⟩
  change Additive.ofMul
      (liftDifference p q (T.original.object j) (T.correctionChoice h e) (T.lift e)
        ((T.correctionChoice_core h e).trans (T.lift_core e).symm)) = h ⟨i, j, e⟩
  apply Additive.toMul.injective
  change liftDifference p q (T.original.object j) (T.correctionChoice h e) (T.lift e)
      ((T.correctionChoice_core h e).trans (T.lift_core e).symm) =
    (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j))
  apply kernelInclusion_injective p q (T.original.object j)
  change T.correctionChoice h e * (T.lift e)⁻¹ =
    kernelInclusion p q (T.original.object j)
      (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j))
  change (kernelInclusion p q (T.original.object j)
      (Additive.toMul (h ⟨i, j, e⟩) : Kernel p q (T.original.object j)) * T.lift e) *
        (T.lift e)⁻¹ = _
  exact mul_inv_cancel_right _ _

/-- Applying the recovered correction restores every original edge choice. -/
theorem correctionChoice_solutionCorrection (S : Solution T)
    {i j : K.Vertex} (e : K.Edge i j) :
    T.correctionChoice (T.solutionCorrection S) e = S.choice e := by
  change kernelInclusion p q (T.original.object j)
      (liftDifference p q (T.original.object j) (S.choice e) (T.lift e)
        ((S.choice_core e).trans (T.lift_core e).symm)) * T.lift e = S.choice e
  exact liftDifference_mul p q (T.original.object j) (S.choice e) (T.lift e)
    ((S.choice_core e).trans (T.lift_core e).symm)

/-- The two constructions compose to the identity on correction solutions. -/
theorem solutionCorrection_solutionOfCorrection
    (h : C1 T.toTower.localCoefficients)
    (hh : d1 T.toTower.localCoefficients h = -T.toTower.defect) :
    T.solutionCorrection (T.solutionOfCorrection h hh) = h :=
  T.solutionCorrection_correctionChoice h

/-- The two constructions compose to the identity on actual coherent lifts. -/
theorem solutionOfCorrection_solutionCorrection (S : Solution T) :
    T.solutionOfCorrection (T.solutionCorrection S) (T.solutionCorrection_d1 S) = S := by
  apply Solution.ext
  intro i j e
  exact T.correctionChoice_solutionCorrection S e

/-- B3: actual coherent lifts exist exactly when the fixed correction equation is solvable. -/
theorem solution_nonempty_iff_correction :
    Nonempty (Solution T) ↔
      ∃ h : C1 T.toTower.localCoefficients,
        d1 T.toTower.localCoefficients h = -T.toTower.defect := by
  constructor
  · rintro ⟨S⟩
    exact ⟨T.solutionCorrection S, T.solutionCorrection_d1 S⟩
  · rintro ⟨h, hh⟩
    exact ⟨T.solutionOfCorrection h hh⟩

/-- The zero class is exactly the solvability of the actual correction equation. -/
theorem obstructionClass_eq_zero_iff_correction
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    T.toTower.obstructionClass hsyzygy = 0 ↔
      ∃ h : C1 T.toTower.localCoefficients,
        d1 T.toTower.localCoefficients h = -T.toTower.defect := by
  let M := T.toTower.localCoefficients
  change (QuotientAddGroup.mk (T.toTower.obstructionCocycle hsyzygy) : H2 M) = 0 ↔ _
  rw [h2_eq_zero_iff]
  constructor
  · rintro ⟨x, hx⟩
    have heq : d1 M x = T.toTower.defect := congrArg Subtype.val hx
    refine ⟨-x, ?_⟩
    change (d1Hom M) (-x) = -T.toTower.defect
    change (d1Hom M) x = T.toTower.defect at heq
    rw [map_neg, heq]
  · rintro ⟨h, hh⟩
    refine ⟨-h, ?_⟩
    apply Subtype.ext
    change (d1Hom M) (-h) = T.toTower.defect
    change (d1Hom M) h = -T.toTower.defect at hh
    rw [map_neg, hh, neg_neg]

/-- G-129 B3: the genuine coherent lift space is nonempty exactly when the H² obstruction vanishes. -/
theorem obstructionClass_eq_zero_iff_solution
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1 (K.threeLeft s) (K.threeRight s)) :
    T.toTower.obstructionClass hsyzygy = 0 ↔ Nonempty (Solution T) := by
  exact (T.obstructionClass_eq_zero_iff_correction hsyzygy).trans
    T.solution_nonempty_iff_correction.symm

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
