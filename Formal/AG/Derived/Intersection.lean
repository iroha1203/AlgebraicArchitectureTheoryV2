import Formal.AG.Derived.LawfulLoci
import Formal.AG.Derived.Koszul
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace Intersection

variable (A : Type v) [CommRing A]

/-- V.定義4.1: classical quotient carried by the joint lawful locus `V(I_U + I_V)`. -/
abbrev classicalJointQuotient (I_U I_V : Ideal A) :=
  A ⧸ (I_U + I_V)

/-- V.定義5.1 / 5.2: Mathlib `Tor_i(O_X/I_U, O_X/I_V)` object for one chart algebra. -/
abbrev mathlibTor (I_U I_V : Ideal A) (i : Nat) : ModuleCat.{v} A :=
  (((CategoryTheory.Tor (ModuleCat.{v} A) i).obj (ModuleCat.of A (A ⧸ I_U))).obj
    (ModuleCat.of A (A ⧸ I_V)))

/--
V.定義4.1: chart-level derived intersection surface.

This records the two selected Koszul presentations and the classical degree-zero
joint quotient. It deliberately avoids a general derived category `D(O_X)`.
-/
structure ChartDerivedIntersection (I_U I_V : Ideal A) where
  leftKoszul : Koszul.KoszulComplex.{u, v} A I_U
  rightKoszul : Koszul.KoszulComplex.{u, v} A I_V

namespace ChartDerivedIntersection

variable {A}

/-- V.定義4.1: degree-zero classical quotient of the selected derived intersection. -/
abbrev classicalQuotient {I_U I_V : Ideal A}
    (_X : ChartDerivedIntersection.{u, v} A I_U I_V) :=
  classicalJointQuotient A I_U I_V

end ChartDerivedIntersection

/--
V.定義5.1 / 5.2: selected Tor bridge for law-conflict sheaves.

`Tor i` is the chosen chart-level Tor object. Homological degree `i = 1`
corresponds to the text's `H^{-1}` convention for first derived residue.
The `i = 0` bridge fixes the classical quotient `O_X / (I_U + I_V)`.
-/
structure SelectedTorBridge (I_U I_V : Ideal A) where
  Tor : Nat -> Type v
  [torAddCommGroup : (i : Nat) -> AddCommGroup (Tor i)]
  [torModule : (i : Nat) -> Module A (Tor i)]
  torLinearEquivMathlib : (i : Nat) -> Tor i ≃ₗ[A] mathlibTor A I_U I_V i
  [tor0CommRing : CommRing (Tor 0)]
  [tor0Algebra : Algebra A (Tor 0)]
  tor0AlgEquivClassicalJoint :
    Tor 0 ≃ₐ[A] classicalJointQuotient A I_U I_V

attribute [instance] SelectedTorBridge.torAddCommGroup
attribute [instance] SelectedTorBridge.torModule
attribute [instance] SelectedTorBridge.tor0CommRing
attribute [instance] SelectedTorBridge.tor0Algebra

namespace SelectedTorBridge

variable {A}

/-- V.定義5.1 / 5.2: `LawConflict_i` is the selected `Tor_i`. -/
abbrev LawConflict {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) (i : Nat) : Type v :=
  B.Tor i

/-- V.定義5.1: first law conflict sheaf, homological degree one. -/
abbrev LawConflict₁ {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) : Type v :=
  B.LawConflict 1

/-- V.定義5.1 / 5.2: definitional bridge `LawConflict_i = Tor_i`. -/
theorem lawConflict_eq_tor {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) (i : Nat) :
    B.LawConflict i = B.Tor i :=
  rfl

/-- V.定義5.1 / 5.2: selected bridge from `LawConflict_i` to Mathlib `Tor_i`. -/
def lawConflictLinearEquivMathlibTor {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) (i : Nat) :
    B.LawConflict i ≃ₗ[A] mathlibTor A I_U I_V i :=
  B.torLinearEquivMathlib i

/-- V.R3: degree-zero law conflict is the classical joint quotient. -/
def lawConflict0AlgEquivClassicalJoint {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) :
    B.LawConflict 0 ≃ₐ[A] classicalJointQuotient A I_U I_V :=
  B.tor0AlgEquivClassicalJoint

/-- V.R3: ring-equivalence form of the degree-zero law-conflict bridge. -/
def lawConflict0RingEquivClassicalJoint {I_U I_V : Ideal A}
    (B : SelectedTorBridge.{v} A I_U I_V) :
    B.LawConflict 0 ≃+* classicalJointQuotient A I_U I_V :=
  B.lawConflict0AlgEquivClassicalJoint.toRingEquiv

end SelectedTorBridge

/-- V.定義4.1 / 5.1: derived intersection together with its selected Tor bridge. -/
structure LawConflictPackage (I_U I_V : Ideal A) where
  intersection : ChartDerivedIntersection.{u, v} A I_U I_V
  torBridge : SelectedTorBridge.{v} A I_U I_V

namespace LawConflictPackage

variable {A}

/-- V.定義5.1 / 5.2: law conflict in homological degree `i`. -/
abbrev LawConflict {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) (i : Nat) : Type v :=
  P.torBridge.LawConflict i

/-- V.定義5.1: first law conflict object. -/
abbrev LawConflict₁ {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) : Type v :=
  P.LawConflict 1

/-- V.R3: package-level bridge `LawConflict_i = Tor_i`. -/
theorem lawConflict_eq_tor {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) (i : Nat) :
    P.LawConflict i = P.torBridge.Tor i :=
  rfl

/-- V.定義5.1 / 5.2: package-level bridge from `LawConflict_i` to Mathlib `Tor_i`. -/
def lawConflictLinearEquivMathlibTor {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) (i : Nat) :
    P.LawConflict i ≃ₗ[A] mathlibTor A I_U I_V i :=
  P.torBridge.lawConflictLinearEquivMathlibTor i

/-- V.R3: `LawConflict_0` recovers `O_X / (I_U + I_V)`. -/
def lawConflict0AlgEquivClassicalJoint {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) :
    P.LawConflict 0 ≃ₐ[A] classicalJointQuotient A I_U I_V :=
  P.torBridge.lawConflict0AlgEquivClassicalJoint

/-- V.R3: ring-equivalence form of `LawConflict_0 = O_X / (I_U + I_V)`. -/
def lawConflict0RingEquivClassicalJoint {I_U I_V : Ideal A}
    (P : LawConflictPackage.{u, v} A I_U I_V) :
    P.LawConflict 0 ≃+* classicalJointQuotient A I_U I_V :=
  P.torBridge.lawConflict0RingEquivClassicalJoint

end LawConflictPackage

end Intersection

namespace LawfulLoci.LawUniversePair

variable (A : Type v) [CommRing A]
variable {A}

/-- V.R3: chart-level derived intersection type attached to a Part V law-universe pair. -/
abbrev DerivedIntersectionFor
    (P : LawUniversePair.{u, v} A) :=
  Intersection.ChartDerivedIntersection.{u, v} A P.I_U P.I_V

/-- V.R3: selected derived intersection package for a law-universe pair. -/
def derivedIntersection
    (P : LawUniversePair.{u, v} A)
    (left : Koszul.KoszulComplex.{u, v} A P.I_U)
    (right : Koszul.KoszulComplex.{u, v} A P.I_V) :
    DerivedIntersectionFor P :=
  ⟨left, right⟩

end LawfulLoci.LawUniversePair

end Derived
end AAT.AG
