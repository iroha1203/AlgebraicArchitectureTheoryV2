import ResearchLean.AG.AbelianLiftingObstruction.H1Classification

/-!
# Independence of the reference edge lifts

An alternative lift of the same fixed core selection reconstructs the same
actual solution space. Its local coefficients use the same kernel transports,
so the vertex-orbit classification remains the same.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

namespace OriginalTowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

private theorem localCoefficients_eq_of_edge
    (M N : LocalCoefficients K)
    (h : M.toEdgeCoefficients = N.toEdgeCoefficients) : M = N := by
  cases M with
  | mk m hm =>
    cases N with
    | mk n hn =>
      cases h
      rfl

private noncomputable def cocycleEquivOfEq {M N : LocalCoefficients K}
    (h : M = N) : Z1 M ≃+ Z1 N := by
  cases h
  exact AddEquiv.refl _

private theorem cocycleEquivOfEq_val {M N : LocalCoefficients K}
    (h : M = N) (z : Z1 M) :
    HEq z.1 (cocycleEquivOfEq h z).1 := by
  cases h
  rfl

private theorem d0_heq_of_eq {M N : LocalCoefficients K}
    (h : M = N) (b : C0 M) (c : C0 N) (hb : HEq b c) :
    HEq (d0 M b) (d0 N c) := by
  cases h
  cases hb
  rfl

private noncomputable def h1EquivOfEq {M N : LocalCoefficients K}
    (h : M = N) : H1 M ≃+ H1 N := by
  cases h
  exact AddEquiv.refl _

private theorem h1EquivOfEq_mk {M N : LocalCoefficients K}
    (h : M = N) (z : Z1 M) :
    h1EquivOfEq h (QuotientAddGroup.mk z : H1 M) =
      QuotientAddGroup.mk (cocycleEquivOfEq h z) := by
  cases h
  rfl

private noncomputable def h2EquivOfEq {M N : LocalCoefficients K}
    (h : M = N) : H2 M ≃+ H2 N := by
  cases h
  exact AddEquiv.refl _

private noncomputable def z2EquivOfEq {M N : LocalCoefficients K}
    (h : M = N) : Z2 M ≃+ Z2 N := by
  cases h
  exact AddEquiv.refl _

private theorem z2EquivOfEq_val {M N : LocalCoefficients K}
    (h : M = N) (z : Z2 M) :
    HEq z.1 (z2EquivOfEq h z).1 := by
  cases h
  rfl

private theorem h2EquivOfEq_mk {M N : LocalCoefficients K}
    (h : M = N) (z : Z2 M) :
    h2EquivOfEq h (QuotientAddGroup.mk z : H2 M) =
      QuotientAddGroup.mk (z2EquivOfEq h z) := by
  cases h
  rfl

/-- Every other lift of the fixed core selection satisfies the same original
tower hypotheses; none of its material conditions are newly assumed. -/
noncomputable def withAlternativeLift
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    OriginalTowerPresentation K p q where
  original := T.original
  originalLowerStrong := T.originalLowerStrong
  core := T.core
  lift := other
  lift_core := hother
  faceBase := T.faceBase
  comparator := T.comparator
  coreAlignment := by
    intro f
    rw [← T.alternativePath_eq other hother (K.twoLeft f),
      ← T.alternativePath_eq other hother (K.twoRight f)]
    exact T.toTower.correctedCoreAlignment (T.alternativeCorrection other hother) f
  kernelComm := T.kernelComm
  edgeBijective := by
    intro i j e
    rw [← T.edgeTransport_independent_lift other hother e]
    exact T.edgeBijective e
  comparatorCentralizes := T.comparatorCentralizes

/-- The independent type of coherent original-edge solutions does not depend
on which lift was chosen as reference. -/
noncomputable def solutionChangeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    Solution T ≃ Solution (T.withAlternativeLift other hother) where
  toFun S := ⟨S.choice, S.choice_core, S.face⟩
  invFun R := ⟨R.choice, R.choice_core, R.face⟩
  left_inv := by intro S; cases S; rfl
  right_inv := by intro R; cases R; rfl

/-- The two reference choices produce the same local coefficient system, with
edge maps equal as actual kernel transports. -/
  theorem localCoefficients_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    T.toTower.localCoefficients =
      (T.withAlternativeLift other hother).toTower.localCoefficients := by
  have hedge : T.toTower.edgeCoefficients =
      (T.withAlternativeLift other hother).toTower.edgeCoefficients := by
    unfold TowerPresentation.edgeCoefficients
    congr 1
    funext i j e
    apply AddEquiv.ext
    intro a
    exact congrArg (fun h => Additive.ofMul (h (Additive.toMul a)))
      (T.edgeTransport_independent_lift other hother e)
  exact localCoefficients_eq_of_edge _ _ hedge

/-- The correspondence leaves every original edge choice literally unchanged. -/
theorem solutionChangeReference_choice
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (S : Solution T) {i j : K.Vertex} (e : K.Edge i j) :
    (T.solutionChangeReference other hother S).choice e = S.choice e := rfl

/-- The first cocycle group is transported by equality of the actually
constructed local coefficient systems. -/
noncomputable def cocycleChangeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    Z1 T.toTower.localCoefficients ≃+
      Z1 (T.withAlternativeLift other hother).toTower.localCoefficients := by
  let hM := T.localCoefficients_changeReference other hother
  exact cocycleEquivOfEq hM

theorem cocycleChangeReference_val
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (z : Z1 T.toTower.localCoefficients) :
    HEq z.1 (T.cocycleChangeReference other hother z).1 :=
  cocycleEquivOfEq_val (T.localCoefficients_changeReference other hother) z

/-- The cocycle action on actual edge choices is unchanged by the reference
lift, after identifying the equal local coefficient systems. -/
theorem solutionAction_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (z : Z1 T.toTower.localCoefficients) (S : Solution T) :
    T.solutionChangeReference other hother (T.solutionAction z S) =
      (T.withAlternativeLift other hother).solutionAction
        (T.cocycleChangeReference other hother z)
        (T.solutionChangeReference other hother S) := by
  apply Solution.ext
  intro i j e
  rw [T.solutionChangeReference_choice,
    T.solutionAction_edge,
    (T.withAlternativeLift other hother).solutionAction_edge,
    T.solutionChangeReference_choice]
  have hval := T.cocycleChangeReference_val other hother z
  have hcochain : z.1 = (T.cocycleChangeReference other hother z).1 :=
    eq_of_heq hval
  rw [← hcochain]
  rfl

/-- The actual vertex coboundary is the same for both reference lifts. -/
theorem d0ToZ1_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (b : C0 T.toTower.localCoefficients) :
    T.cocycleChangeReference other hother
      (d0ToZ1 T.toTower.localCoefficients b) =
        d0ToZ1 (T.withAlternativeLift other hother).toTower.localCoefficients b := by
  apply Subtype.ext
  have hval := T.cocycleChangeReference_val other hother
    (d0ToZ1 T.toTower.localCoefficients b)
  have hcochain : (d0ToZ1 T.toTower.localCoefficients b).1 =
      (T.cocycleChangeReference other hother
        (d0ToZ1 T.toTower.localCoefficients b)).1 := eq_of_heq hval
  rw [← hcochain]
  change d0 T.toTower.localCoefficients b =
    d0 (T.withAlternativeLift other hother).toTower.localCoefficients b
  exact eq_of_heq (d0_heq_of_eq
    (T.localCoefficients_changeReference other hother) b b HEq.rfl)

/-- The same original-edge solution correspondence commutes with vertex
reidentification, not merely with abstract cochains. -/
theorem vertexGauge_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (b : C0 T.toTower.localCoefficients) (S : Solution T) :
    T.solutionChangeReference other hother (T.vertexGauge b S) =
      (T.withAlternativeLift other hother).vertexGauge b
        (T.solutionChangeReference other hother S) := by
  change T.solutionChangeReference other hother
    (T.solutionAction (d0ToZ1 T.toTower.localCoefficients b) S) =
      (T.withAlternativeLift other hother).solutionAction
        (d0ToZ1 (T.withAlternativeLift other hother).toTower.localCoefficients b)
        (T.solutionChangeReference other hother S)
  rw [T.solutionAction_changeReference,
    T.d0ToZ1_changeReference]

/-- Vertex-orbit classes correspond by keeping every actual original-edge
solution fixed. -/
noncomputable def solutionOrbitChangeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    SolutionOrbit T ≃ SolutionOrbit (T.withAlternativeLift other hother) := by
  let e := T.solutionChangeReference other hother
  apply Quotient.congr e
  intro S R
  rw [T.solution_orbit_rel_iff,
    (T.withAlternativeLift other hother).solution_orbit_rel_iff]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [← T.vertexGauge_changeReference]
    exact congrArg e hb
  · rintro ⟨b, hb⟩
    refine ⟨b, e.injective ?_⟩
    rw [T.vertexGauge_changeReference]
    exact hb

/-- The orbit equivalence maps a class to the class of the same actual choice. -/
theorem solutionOrbitChangeReference_mk
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (S : Solution T) :
    T.solutionOrbitChangeReference other hother (⟦S⟧ : SolutionOrbit T) =
      (⟦T.solutionChangeReference other hother S⟧ :
        SolutionOrbit (T.withAlternativeLift other hother)) := rfl

/-- The first cohomology groups are identified by equality of the actual
local coefficient systems, not by a new or constant coefficient system. -/
noncomputable def h1ChangeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    H1 T.toTower.localCoefficients ≃+
      H1 (T.withAlternativeLift other hother).toTower.localCoefficients :=
  h1EquivOfEq (T.localCoefficients_changeReference other hother)

theorem h1ChangeReference_mk
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (z : Z1 T.toTower.localCoefficients) :
    T.h1ChangeReference other hother
      (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) =
        QuotientAddGroup.mk (T.cocycleChangeReference other hother z) :=
  h1EquivOfEq_mk (T.localCoefficients_changeReference other hother) z

/-- A genuine solution for one reference is a genuine solution for the other. -/
noncomputable def solutionChangeReference_nonempty [Nonempty (Solution T)]
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    Nonempty (Solution (T.withAlternativeLift other hother)) :=
  ⟨T.solutionChangeReference other hother (Classical.choice inferInstance)⟩

/-- The same actual orbit map intertwines the `H¹` actions from both choices
of reference edge lift. -/
theorem solutionOrbitChangeReference_vadd [Nonempty (Solution T)]
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (c : H1 T.toTower.localCoefficients) (Q : SolutionOrbit T) :
    letI : Nonempty (Solution (T.withAlternativeLift other hother)) :=
      T.solutionChangeReference_nonempty other hother
    T.solutionOrbitChangeReference other hother (c +ᵥ Q) =
      (T.h1ChangeReference other hother c) +ᵥ
        (T.solutionOrbitChangeReference other hother Q) := by
  letI : Nonempty (Solution (T.withAlternativeLift other hother)) :=
    T.solutionChangeReference_nonempty other hother
  induction c using Quotient.inductionOn' with
  | _ z =>
    induction Q using Quotient.inductionOn' with
    | _ S =>
      change T.solutionOrbitChangeReference other hother
          ((QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +ᵥ
            (⟦S⟧ : SolutionOrbit T)) =
        (T.h1ChangeReference other hother (QuotientAddGroup.mk z)) +ᵥ
          (T.solutionOrbitChangeReference other hother (⟦S⟧ : SolutionOrbit T))
      rw [T.solutionOrbit_vadd_mk,
        T.solutionOrbitChangeReference_mk,
        T.h1ChangeReference_mk,
        T.solutionOrbitChangeReference_mk,
        (T.withAlternativeLift other hother).solutionOrbit_vadd_mk,
        T.solutionAction_changeReference]

/-- Differences of two actual solutions use the same kernel values after
changing the reference choice. -/
theorem solutionDifference_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (S R : Solution T) :
    T.cocycleChangeReference other hother (T.solutionDifference S R) =
      (T.withAlternativeLift other hother).solutionDifference
        (T.solutionChangeReference other hother S)
        (T.solutionChangeReference other hother R) := by
  have h := congrArg (T.solutionChangeReference other hother)
    (T.solutionDifference_action S R)
  rw [T.solutionAction_changeReference] at h
  have h' := congrArg
    (fun X => (T.withAlternativeLift other hother).solutionDifference X
      (T.solutionChangeReference other hother R)) h
  dsimp only at h'
  rw [(T.withAlternativeLift other hother).solutionDifference_solutionAction] at h'
  exact h'

/-- The quotient torsor difference also agrees after changing the reference. -/
theorem solutionOrbitChangeReference_vsub [Nonempty (Solution T)]
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e)
        = T.core e)
    (Q R : SolutionOrbit T) :
    letI : Nonempty (Solution (T.withAlternativeLift other hother)) :=
      T.solutionChangeReference_nonempty other hother
    T.h1ChangeReference other hother (Q -ᵥ R) =
      (T.solutionOrbitChangeReference other hother Q) -ᵥ
        (T.solutionOrbitChangeReference other hother R) := by
  letI : Nonempty (Solution (T.withAlternativeLift other hother)) :=
    T.solutionChangeReference_nonempty other hother
  induction Q using Quotient.inductionOn' with
  | _ S =>
    induction R using Quotient.inductionOn' with
    | _ U =>
      rw [T.solutionOrbit_vsub_mk,
        T.h1ChangeReference_mk,
        T.solutionOrbitChangeReference_mk,
        T.solutionOrbitChangeReference_mk,
        (T.withAlternativeLift other hother).solutionOrbit_vsub_mk,
        T.solutionDifference_changeReference]

/-- The defect reconstructed from the alternative original arrows is exactly
the defect of the alternative presentation, coordinate by coordinate. -/
theorem defect_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    (T.withAlternativeLift other hother).toTower.defect =
      T.alternativeDefect other hother := by
  funext f
  apply Additive.ofMul.injective
  apply kernelInclusion_injective p q (T.original.object (K.twoTarget f))
  change kernelInclusion p q _
      ((T.withAlternativeLift other hother).toTower.faceDefect f) =
    kernelInclusion p q _
      (Additive.toMul (T.alternativeDefect other hother f))
  rw [(T.withAlternativeLift other hother).toTower.faceDefect_eq_raw]
  exact (T.alternativeDefect_eq_raw other hother f).symm

/-- The original designated 3-cell law remains valid for the actual
alternative edge lifts. -/
theorem syzygy_changeReference
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1
        (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    ∀ s : K.ThreeCell,
      AuthoredSyzygy (T.withAlternativeLift other hother).toTower.toTransportData 1
        (K.threeLeft s) (K.threeRight s) :=
  T.alternativeAuthoredSyzygy hsyzygy other hother

/-- The degree-two cohomology groups are identified by the same coefficient
equality used for first cohomology. -/
noncomputable def h2ChangeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    H2 T.toTower.localCoefficients ≃+
      H2 (T.withAlternativeLift other hother).toTower.localCoefficients :=
  h2EquivOfEq (T.localCoefficients_changeReference other hother)

/-- The obstruction class of the alternative actual reference lifts is the
same class under the constructed equality of coefficient systems. -/
theorem obstructionClass_changeReference
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1
        (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    T.h2ChangeReference other hother (T.toTower.obstructionClass hsyzygy) =
      (T.withAlternativeLift other hother).toTower.obstructionClass
        (T.syzygy_changeReference hsyzygy other hother) := by
  let hM := T.localCoefficients_changeReference other hother
  have hcorr : T.h2ChangeReference other hother
      (T.alternativeObstructionClass hsyzygy other hother) =
        (T.withAlternativeLift other hother).toTower.obstructionClass
          (T.syzygy_changeReference hsyzygy other hother) := by
    change h2EquivOfEq hM
        (QuotientAddGroup.mk (T.toTower.correctedObstructionCocycle hsyzygy
          (T.alternativeCorrection other hother))) =
      QuotientAddGroup.mk
        ((T.withAlternativeLift other hother).toTower.obstructionCocycle
          (T.syzygy_changeReference hsyzygy other hother))
    rw [h2EquivOfEq_mk]
    congr 1
    apply Subtype.ext
    have hval := z2EquivOfEq_val hM
      (T.toTower.correctedObstructionCocycle hsyzygy
        (T.alternativeCorrection other hother))
    have hcochain :
        (T.toTower.correctedObstructionCocycle hsyzygy
          (T.alternativeCorrection other hother)).1 =
          (z2EquivOfEq hM (T.toTower.correctedObstructionCocycle hsyzygy
            (T.alternativeCorrection other hother))).1 := eq_of_heq hval
    rw [← hcochain]
    change T.alternativeDefect other hother =
      (T.withAlternativeLift other hother).toTower.defect
    exact (T.defect_changeReference other hother).symm
  calc
    T.h2ChangeReference other hother (T.toTower.obstructionClass hsyzygy) =
        T.h2ChangeReference other hother
          (T.alternativeObstructionClass hsyzygy other hother) := by
            rw [T.alternativeObstructionClass_eq]
    _ = _ := hcorr

/-- Vanishing of the degree-two obstruction is reference independent on the
same original core selection. -/
theorem obstructionClass_zero_changeReference
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTower.toTransportData 1
        (K.threeLeft s) (K.threeRight s))
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e) :
    T.toTower.obstructionClass hsyzygy = 0 ↔
      (T.withAlternativeLift other hother).toTower.obstructionClass
        (T.syzygy_changeReference hsyzygy other hother) = 0 := by
  rw [← T.obstructionClass_changeReference hsyzygy other hother]
  exact (T.h2ChangeReference other hother).map_eq_zero_iff.symm

/-- The base-solution parametrization by `H¹` is natural under the actual
reference-lift change. -/
theorem solutionOrbitEquivH1_changeReference
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    (base : Solution T) (c : H1 T.toTower.localCoefficients) :
    T.solutionOrbitChangeReference other hother
        (T.solutionOrbitEquivH1 base c) =
      (T.withAlternativeLift other hother).solutionOrbitEquivH1
        (T.solutionChangeReference other hother base)
        (T.h1ChangeReference other hother c) := by
  induction c using Quotient.inductionOn' with
  | _ z =>
      change T.solutionOrbitChangeReference other hother
          (T.solutionOrbitFromH1 base (QuotientAddGroup.mk z)) =
        (T.withAlternativeLift other hother).solutionOrbitFromH1
          (T.solutionChangeReference other hother base)
          (T.h1ChangeReference other hother (QuotientAddGroup.mk z))
      rw [T.h1ChangeReference_mk]
      change T.solutionOrbitChangeReference other hother
          (⟦T.solutionAction z base⟧ : SolutionOrbit T) =
        (⟦(T.withAlternativeLift other hother).solutionAction
          (T.cocycleChangeReference other hother z)
          (T.solutionChangeReference other hother base)⟧ :
            SolutionOrbit (T.withAlternativeLift other hother))
      rw [T.solutionOrbitChangeReference_mk,
        T.solutionAction_changeReference]

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
