import ResearchLean.AG.AbelianLiftingObstruction.Solutions
import Mathlib.Algebra.AddTorsor.Defs

/-!
# First cocycles acting on genuine coherent lifts

The action and difference use the actual kernel correction of each original
edge choice. The underlying points remain `Solution T`, whose face equations
are those of the original paths.
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

/-- A first cocycle changes every original edge choice by its actual kernel value. -/
noncomputable def solutionAction (z : Z1 T.toTower.localCoefficients)
    (S : Solution T) : Solution T :=
  T.solutionOfCorrection (T.solutionCorrection S + z.1) (by
    change (d1Hom T.toTower.localCoefficients)
      (T.solutionCorrection S + z.1) = -T.toTower.defect
    rw [map_add]
    have hz : (d1Hom T.toTower.localCoefficients) z.1 = 0 := z.2
    have hcor := T.solutionCorrection_d1 S
    change (d1Hom T.toTower.localCoefficients) (T.solutionCorrection S) =
      -T.toTower.defect at hcor
    rw [hcor, hz, add_zero])

/-- Its kernel cochain is exactly the original correction plus the cocycle. -/
theorem solutionAction_correction (z : Z1 T.toTower.localCoefficients)
    (S : Solution T) :
    T.solutionCorrection (T.solutionAction z S) = T.solutionCorrection S + z.1 :=
  T.solutionCorrection_solutionOfCorrection _ _

/-- On each original edge the action is literal multiplication by the included kernel value. -/
theorem solutionAction_edge (z : Z1 T.toTower.localCoefficients)
    (S : Solution T) {i j : K.Vertex} (e : K.Edge i j) :
    (T.solutionAction z S).choice e =
      kernelInclusion p q (T.original.object j)
        (Additive.toMul (z.1 ⟨i, j, e⟩) : Kernel p q (T.original.object j)) * S.choice e := by
  let a : Kernel p q (T.original.object j) :=
    Additive.toMul (T.solutionCorrection S ⟨i, j, e⟩)
  let b : Kernel p q (T.original.object j) := Additive.toMul (z.1 ⟨i, j, e⟩)
  rw [← T.correctionChoice_solutionCorrection S e]
  change kernelInclusion p q (T.original.object j) (a * b) * T.lift e =
    kernelInclusion p q (T.original.object j) b *
      (kernelInclusion p q (T.original.object j) a * T.lift e)
  rw [T.kernelComm j a b, map_mul]
  exact mul_assoc _ _ _

/-- The unique candidate difference of two actual solutions lies in `Z¹`. -/
noncomputable def solutionDifference (S R : Solution T) :
    Z1 T.toTower.localCoefficients :=
  ⟨T.solutionCorrection S - T.solutionCorrection R, by
    change (d1Hom T.toTower.localCoefficients)
      (T.solutionCorrection S - T.solutionCorrection R) = 0
    rw [map_sub]
    change d1 T.toTower.localCoefficients (T.solutionCorrection S) -
      d1 T.toTower.localCoefficients (T.solutionCorrection R) = 0
    rw [T.solutionCorrection_d1 S, T.solutionCorrection_d1 R, sub_self]⟩

/-- The extracted difference sends the second actual solution to the first. -/
theorem solutionDifference_action (S R : Solution T) :
    T.solutionAction (T.solutionDifference S R) R = S := by
  apply Solution.ext
  intro i j e
  have hcochain : T.solutionCorrection (T.solutionAction (T.solutionDifference S R) R) =
      T.solutionCorrection S := by
    rw [T.solutionAction_correction]
    change T.solutionCorrection R +
      (T.solutionCorrection S - T.solutionCorrection R) = T.solutionCorrection S
    abel
  have hchoice := congrArg (fun h => T.correctionChoice h e) hcochain
  simpa only [T.correctionChoice_solutionCorrection] using hchoice

/-- An applied first cocycle is recovered as the unique difference. -/
theorem solutionDifference_solutionAction
    (z : Z1 T.toTower.localCoefficients) (S : Solution T) :
    T.solutionDifference (T.solutionAction z S) S = z := by
  apply Subtype.ext
  change T.solutionCorrection (T.solutionAction z S) - T.solutionCorrection S = z.1
  rw [T.solutionAction_correction]
  abel

/-- The zero cocycle acts trivially on the actual solution space. -/
theorem solutionAction_zero (S : Solution T) :
    T.solutionAction 0 S = S := by
  change T.solutionOfCorrection (T.solutionCorrection S + 0) _ = S
  simpa only [add_zero] using T.solutionOfCorrection_solutionCorrection S

/-- The actual action respects addition in the first-cocycle group. -/
theorem solutionAction_add (z w : Z1 T.toTower.localCoefficients)
    (S : Solution T) :
    T.solutionAction (z + w) S = T.solutionAction z (T.solutionAction w S) := by
  apply Solution.ext
  intro i j e
  have hleft := T.solutionAction_correction (z + w) S
  have hright := T.solutionAction_correction z (T.solutionAction w S)
  rw [T.solutionAction_correction w S] at hright
  have hcochain : T.solutionCorrection (T.solutionAction (z + w) S) =
      T.solutionCorrection (T.solutionAction z (T.solutionAction w S)) := by
    rw [hleft, hright]
    change T.solutionCorrection S + (z.1 + w.1) =
      (T.solutionCorrection S + w.1) + z.1
    abel
  have hchoice := congrArg (fun h => T.correctionChoice h e) hcochain
  simpa only [T.correctionChoice_solutionCorrection] using hchoice

/-- When actual solutions exist, they form a torsor under the first cocycles. -/
noncomputable instance solutionAddTorsor [Nonempty (Solution T)] :
    AddTorsor (Z1 T.toTower.localCoefficients) (Solution T) where
  vadd := T.solutionAction
  zero_vadd := T.solutionAction_zero
  add_vadd := T.solutionAction_add
  nonempty := inferInstance
  vsub := T.solutionDifference
  vsub_vadd' := T.solutionDifference_action
  vadd_vsub' := T.solutionDifference_solutionAction

/-- The difference of any two actual solutions is the unique first cocycle joining them. -/
theorem solutionAction_existsUnique
    (base target : Solution T) :
    ∃! z : Z1 T.toTower.localCoefficients, T.solutionAction z base = target := by
  refine ⟨T.solutionDifference target base, T.solutionDifference_action target base, ?_⟩
  intro z hz
  rw [← hz, T.solutionDifference_solutionAction]

/-- A chosen actual solution identifies all first cocycles with all actual solutions. -/
noncomputable def solutionEquivZ1 (origin : Solution T) :
    Z1 T.toTower.localCoefficients ≃ Solution T := by
  letI : Nonempty (Solution T) := ⟨origin⟩
  exact Equiv.vaddConst origin

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
