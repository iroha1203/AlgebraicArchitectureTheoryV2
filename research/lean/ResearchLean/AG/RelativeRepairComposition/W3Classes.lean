import ResearchLean.AG.RelativeRepairComposition.W3LoopIsomorphisms

/-! # W3's full actual isomorphism quotients

Both inverse maps use actual repairs on the original two edges. The quotient
is Mathlib's whole isomorphism setoid, rather than a selected orbit family.
-/
namespace AAT.AG.RelativeRepairComposition.W3Classes
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels W3ActualArrows W3LoopIsomorphisms
attribute [local instance] actualAction

/-- Each complete loop vector has an actual repair with original e correction zero. -/
def normalObject (sheared : Bool) (w : A) : ActualCategory sheared candidates :=
  (unrestrictedParametersEquiv sheared).symm (0,w)

/-- The constructed object's actual original loop is the entire chosen vector. -/
theorem loop_normal (sheared : Bool) (w : A) : loopCoordinate (normalObject sheared w) = w := by
  have hp : parameters ((unrestrictedParametersEquiv sheared).symm (0,w)) = (0,w) :=
    (unrestrictedParametersEquiv sheared).apply_symm_apply (0,w)
  change loopValue sheared (parameters ((unrestrictedParametersEquiv sheared).symm (0,w))).1
    (parameters ((unrestrictedParametersEquiv sheared).symm (0,w))).2 = w
  rw [hp]
  simp [loopValue]

/-- Each shear class is realized by an actual full-vector repair on both original edges. -/
def shearObject (a : ZMod 3) : ActualCategory true candidates :=
  normalObject true (fun i => if i = 0 then 0 else a)

/-- Its invariant is the original full loop's second coordinate. -/
theorem shear_object (a : ZMod 3) : shearInvariant (shearObject a) = a := by
  unfold shearInvariant shearObject
  rw [loop_normal]
  rfl

/-- The entire original shear repair isomorphism quotient has both inverse F3 coordinates. -/
noncomputable def shearClassEquiv :
    Quotient (isIsomorphicSetoid (ActualCategory true candidates)) ≃ ZMod 3 where
  toFun := Quotient.lift shearInvariant (fun R Q h => (shear_isomorphic_iff R Q).mp h)
  invFun a := Quotient.mk _ (shearObject a)
  left_inv q := Quotient.inductionOn q (fun R => Quotient.sound
    ((shear_isomorphic_iff (shearObject (shearInvariant R)) R).mpr (shear_object _)))
  right_inv := shear_object

/-- The entire original identity repair isomorphism quotient has both inverse A coordinates. -/
noncomputable def identityClassEquiv :
    Quotient (isIsomorphicSetoid (ActualCategory false candidates)) ≃ A where
  toFun := Quotient.lift loopCoordinate (fun R Q h => (identity_isomorphic_iff R Q).mp h)
  invFun w := Quotient.mk _ (normalObject false w)
  left_inv q := Quotient.inductionOn q (fun R => Quotient.sound
    ((identity_isomorphic_iff (normalObject false (loopCoordinate R)) R).mpr (loop_normal _ _)))
  right_inv := loop_normal false

/-- The whole original shear actual groupoid has exactly three isomorphism classes. -/
theorem shear_class_card :
    Nat.card (Quotient (isIsomorphicSetoid (ActualCategory true candidates))) = 3 := by
  rw [Nat.card_congr shearClassEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- The same entire repair span with identity transport has exactly nine isomorphism classes. -/
theorem identity_class_card :
    Nat.card (Quotient (isIsomorphicSetoid (ActualCategory false candidates))) = 9 := by
  rw [Nat.card_congr identityClassEquiv]
  simp [A, Nat.card_eq_fintype_card]

/-- Empty permission keeps the entire original unchanged actual object. -/
def emptyObject (sheared : Bool) : ActualCategory sheared ∅ := referenceRepair sheared ∅

/-- Every categorical object at empty permission is the same unchanged original repair. -/
theorem empty_object_eq (sheared : Bool) (R : ActualCategory sheared ∅) : R = emptyObject sheared := by
  rcases R with ⟨u,R⟩
  cases u
  exact congrArg (fun R : RealRepairs sheared ∅ => (R : ActualCategory sheared ∅))
    (empty_unique sheared R)

/-- The whole empty-permission isomorphism quotient has both inverse point coordinates. -/
noncomputable def emptyClassEquiv (sheared : Bool) :
    Quotient (isIsomorphicSetoid (ActualCategory sheared ∅)) ≃ Unit where
  toFun _ := ()
  invFun _ := Quotient.mk _ (emptyObject sheared)
  left_inv q := Quotient.inductionOn q (fun R =>
    congrArg (Quotient.mk (isIsomorphicSetoid (ActualCategory sheared ∅)))
      (empty_object_eq sheared R).symm)
  right_inv _ := rfl

/-- The original restricted global actual repair category has one isomorphism class. -/
theorem empty_class_card (sheared : Bool) :
    Nat.card (Quotient (isIsomorphicSetoid (ActualCategory sheared ∅))) = 1 := by
  rw [Nat.card_congr (emptyClassEquiv sheared), Nat.card_eq_fintype_card]
  rfl

end AAT.AG.RelativeRepairComposition.W3Classes
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3Classes
