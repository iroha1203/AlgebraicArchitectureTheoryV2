import ResearchLean.AG.AbelianLiftingObstruction.VertexGauge
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# First cohomology classifies actual coherent lifts up to vertex reidentification

The quotient points are orbits of the vertex action on the original `Solution`.
The action of `H¹` and its difference descend from the `Z¹` torsor of those
same actual edge choices.
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

/-- The vertex action on genuine coherent original-edge choices. -/
noncomputable instance vertexAddAction :
    AddAction (C0 T.toTower.localCoefficients) (Solution T) where
  vadd := T.vertexGauge
  zero_vadd := T.vertexGauge_zero
  add_vadd := T.vertexGauge_add

/-- Actual solutions identified by changes at vertices. -/
abbrev SolutionOrbit : Type _ :=
  Quotient (AddAction.orbitRel (C0 T.toTower.localCoefficients) (Solution T))

/-- The two actual solutions are in the same orbit exactly when a vertex
cochain changes the second one into the first one. -/
theorem solution_orbit_rel_iff (S R : Solution T) :
    AddAction.orbitRel (C0 T.toTower.localCoefficients) (Solution T) S R ↔
      ∃ b : C0 T.toTower.localCoefficients, T.vertexGauge b R = S := by
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  rfl

/-- Equality of classes means an actual vertex reidentification of solutions. -/
theorem solutionOrbit_mk_eq_iff (S R : Solution T) :
    (⟦S⟧ : SolutionOrbit T) = ⟦R⟧ ↔
      ∃ b : C0 T.toTower.localCoefficients, T.vertexGauge b R = S := by
  rw [Quotient.eq'']
  exact T.solution_orbit_rel_iff S R

/-- The orbit relation is exactly vanishing of the difference in the same `H¹`. -/
theorem solutionOrbit_mk_eq_iff_difference_zero (S R : Solution T) :
    (⟦S⟧ : SolutionOrbit T) = ⟦R⟧ ↔
      (QuotientAddGroup.mk (T.solutionDifference S R) : H1 T.toTower.localCoefficients) = 0 := by
  rw [T.solutionOrbit_mk_eq_iff,
    h1_eq_zero_iff T.toTower.localCoefficients]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [← hb]
    exact (T.solutionDifference_solutionAction
      (d0ToZ1 T.toTower.localCoefficients b) R).symm
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    change T.solutionAction (d0ToZ1 T.toTower.localCoefficients b) R = S
    rw [hb]
    exact T.solutionDifference_action S R

/-- Differences of actual solutions obey the torsor subtraction identity. -/
theorem solutionDifference_sub (S R U : Solution T) :
    T.solutionDifference S R =
      T.solutionDifference S U - T.solutionDifference R U := by
  apply Subtype.ext
  change T.solutionCorrection S - T.solutionCorrection R =
    (T.solutionCorrection S - T.solutionCorrection U) -
      (T.solutionCorrection R - T.solutionCorrection U)
  abel

/-- Equality of orbit classes is equality of their difference classes relative
to any chosen actual solution. -/
theorem solutionOrbit_mk_eq_iff_coord (base S R : Solution T) :
    (⟦S⟧ : SolutionOrbit T) = ⟦R⟧ ↔
      (QuotientAddGroup.mk (T.solutionDifference S base) : H1 T.toTower.localCoefficients) =
        QuotientAddGroup.mk (T.solutionDifference R base) := by
  rw [T.solutionOrbit_mk_eq_iff_difference_zero]
  have hmap :
      (QuotientAddGroup.mk
        (T.solutionDifference S base - T.solutionDifference R base) :
          H1 T.toTower.localCoefficients) =
        QuotientAddGroup.mk (T.solutionDifference S base) -
          QuotientAddGroup.mk (T.solutionDifference R base) :=
    (QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range).map_sub _ _
  rw [T.solutionDifference_sub S R base, hmap, sub_eq_zero]

/-- Coordinates of an orbit relative to an actual coherent lift, in the same `H¹`. -/
noncomputable def solutionOrbitCoord (base : Solution T) :
    SolutionOrbit T → H1 T.toTower.localCoefficients :=
  fun Q => Quotient.liftOn' Q
    (fun S => QuotientAddGroup.mk (T.solutionDifference S base))
    (by
      intro S R h
      exact (T.solutionOrbit_mk_eq_iff_coord base S R).mp (Quotient.sound h))

/-- A first cohomology class acts on the orbit of a chosen actual lift. -/
noncomputable def solutionOrbitFromH1 (base : Solution T) :
    H1 T.toTower.localCoefficients → SolutionOrbit T :=
  fun c => Quotient.liftOn' c (fun z => (⟦T.solutionAction z base⟧ : SolutionOrbit T))
    (by
      intro z w h
      apply (T.solutionOrbit_mk_eq_iff_coord base _ _).mpr
      simpa only [T.solutionDifference_solutionAction] using (Quotient.sound h :
        (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) =
          QuotientAddGroup.mk w))

/-- An actual base lift identifies its vertex-orbit quotient with first cohomology. -/
noncomputable def solutionOrbitEquivH1 (base : Solution T) :
    H1 T.toTower.localCoefficients ≃ SolutionOrbit T where
  toFun := T.solutionOrbitFromH1 base
  invFun := T.solutionOrbitCoord base
  left_inv := by
    intro c
    induction c using Quotient.inductionOn' with
    | _ z =>
        change (QuotientAddGroup.mk
          (T.solutionDifference (T.solutionAction z base) base) :
            H1 T.toTower.localCoefficients) = QuotientAddGroup.mk z
        rw [T.solutionDifference_solutionAction]
  right_inv := by
    intro Q
    induction Q using Quotient.inductionOn' with
    | _ S =>
        change (⟦T.solutionAction (T.solutionDifference S base) base⟧ :
          SolutionOrbit T) = ⟦S⟧
        rw [T.solutionDifference_action]

/-- A chosen actual point used internally to transport the standard torsor
structure; the formulas below prove the result is independent of this choice. -/
private noncomputable def solutionOrbitBase [Nonempty (Solution T)] : Solution T :=
  Classical.choice inferInstance

/-- The vertex-orbit quotient of actual coherent lifts is an `H¹` torsor. -/
noncomputable instance solutionOrbitAddTorsor [Nonempty (Solution T)] :
    AddTorsor (H1 T.toTower.localCoefficients) (SolutionOrbit T) := by
  let e := T.solutionOrbitEquivH1 (T.solutionOrbitBase)
  exact {
    vadd := fun c Q => e (c + e.symm Q)
    zero_vadd := by
      intro Q
      change e (0 + e.symm Q) = Q
      rw [zero_add, e.apply_symm_apply]
    add_vadd := by
      intro c d Q
      change e ((c + d) + e.symm Q) = e (c + e.symm (e (d + e.symm Q)))
      rw [e.symm_apply_apply]
      congr 1
      exact add_assoc c d (e.symm Q)
    vsub := fun Q R => e.symm Q - e.symm R
    nonempty := ⟨e 0⟩
    vsub_vadd' := by
      intro Q R
      change e ((e.symm Q - e.symm R) + e.symm R) = Q
      rw [sub_add_cancel, e.apply_symm_apply]
    vadd_vsub' := by
      intro c Q
      change e.symm (e (c + e.symm Q)) - e.symm Q = c
      rw [e.symm_apply_apply, add_sub_cancel_right] }

/-- Adding a cocycle to an actual solution changes its coordinate by that cocycle. -/
theorem solutionDifference_action_base (z : Z1 T.toTower.localCoefficients)
    (S base : Solution T) :
    T.solutionDifference (T.solutionAction z S) base =
      z + T.solutionDifference S base := by
  apply Subtype.ext
  change T.solutionCorrection (T.solutionAction z S) - T.solutionCorrection base =
    z.1 + (T.solutionCorrection S - T.solutionCorrection base)
  rw [T.solutionAction_correction]
  abel

/-- The transported `H¹` action is literally the cocycle action on each
actual original-edge solution, modulo vertex reidentification. -/
theorem solutionOrbit_vadd_mk [Nonempty (Solution T)]
    (z : Z1 T.toTower.localCoefficients) (S : Solution T) :
    (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +ᵥ
      (⟦S⟧ : SolutionOrbit T) = ⟦T.solutionAction z S⟧ := by
  let base := T.solutionOrbitBase
  let e := T.solutionOrbitEquivH1 base
  have hv :
      (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +ᵥ
        (⟦S⟧ : SolutionOrbit T) =
          e ((QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +
            e.symm (⟦S⟧ : SolutionOrbit T)) := rfl
  rw [hv]
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +
    e.symm (⟦S⟧ : SolutionOrbit T) = e.symm ⟦T.solutionAction z S⟧
  change (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) +
    QuotientAddGroup.mk (T.solutionDifference S base) =
      QuotientAddGroup.mk (T.solutionDifference (T.solutionAction z S) base)
  rw [T.solutionDifference_action_base]
  exact ((QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range).map_add
    z (T.solutionDifference S base)).symm

/-- The torsor difference of two vertex classes is their actual solution
difference mapped into the same `H¹`. -/
theorem solutionOrbit_vsub_mk [Nonempty (Solution T)]
    (S R : Solution T) :
    ((⟦S⟧ : SolutionOrbit T) -ᵥ (⟦R⟧ : SolutionOrbit T) :
      H1 T.toTower.localCoefficients) =
        QuotientAddGroup.mk (T.solutionDifference S R) := by
  let base := T.solutionOrbitBase
  change QuotientAddGroup.mk (T.solutionDifference S base) -
    QuotientAddGroup.mk (T.solutionDifference R base) =
      QuotientAddGroup.mk (T.solutionDifference S R)
  have hmap := (QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range).map_sub
    (T.solutionDifference S base) (T.solutionDifference R base)
  change (QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range)
      (T.solutionDifference S base) -
    (QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range)
      (T.solutionDifference R base) =
    (QuotientAddGroup.mk' (d0ToZ1 T.toTower.localCoefficients).range)
      (T.solutionDifference S R)
  rw [← hmap, ← T.solutionDifference_sub S R base]

/-- Both choices of cocycle and actual representative can change without
changing the descended action. -/
theorem solutionOrbit_action_well_defined [Nonempty (Solution T)]
    (z w : Z1 T.toTower.localCoefficients) (S R : Solution T)
    (hz : (QuotientAddGroup.mk z : H1 T.toTower.localCoefficients) =
      QuotientAddGroup.mk w)
    (hS : (⟦S⟧ : SolutionOrbit T) = ⟦R⟧) :
    (⟦T.solutionAction z S⟧ : SolutionOrbit T) =
      ⟦T.solutionAction w R⟧ := by
  rw [← T.solutionOrbit_vadd_mk, ← T.solutionOrbit_vadd_mk, hz, hS]

/-- The class of the difference is independent of both actual representatives. -/
theorem solutionOrbit_difference_well_defined [Nonempty (Solution T)]
    (S S' R R' : Solution T)
    (hS : (⟦S⟧ : SolutionOrbit T) = ⟦S'⟧)
    (hR : (⟦R⟧ : SolutionOrbit T) = ⟦R'⟧) :
    (QuotientAddGroup.mk (T.solutionDifference S R) :
      H1 T.toTower.localCoefficients) =
        QuotientAddGroup.mk (T.solutionDifference S' R') := by
  rw [← T.solutionOrbit_vsub_mk, ← T.solutionOrbit_vsub_mk, hS, hR]

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
