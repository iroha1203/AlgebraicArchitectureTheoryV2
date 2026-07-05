import Formal.AG.Derived.LawfulLoci
import Formal.AG.Derived.Koszul
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.RingTheory.TensorProduct.Quotient

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
V.R3 / V-2: Mathlib's zero-th Tor is the ordinary tensor product because
`ModuleCat` is monoidal closed, hence tensoring on the left preserves finite
colimits.
-/
noncomputable def mathlibTorZeroIsoTensor (I_U I_V : Ideal A) :
    mathlibTor A I_U I_V 0 ≅
      ModuleCat.of A (TensorProduct A (A ⧸ I_U) (A ⧸ I_V)) := by
  let F := ((CategoryTheory.MonoidalCategory.tensoringLeft (ModuleCat.{v} A)).obj
    (ModuleCat.of A (A ⧸ I_U)))
  exact (CategoryTheory.Functor.leftDerivedZeroIsoSelf F).app
    (ModuleCat.of A (A ⧸ I_V))

/--
V.R3 / V-2: quotient tensor product form of the classical joint quotient.

This is the standard composition
`A/(I_U+I_V) ≃ (A/I_U)/(I_V) ≃ (A/I_U) ⊗_A A/I_V`.
-/
noncomputable def classicalJointLinearEquivTensor (I_U I_V : Ideal A) :
    classicalJointQuotient A I_U I_V ≃ₗ[A]
      TensorProduct A (A ⧸ I_U) (A ⧸ I_V) :=
  (DoubleQuot.quotQuotEquivQuotSupₐ A I_U I_V).symm.toLinearEquiv ≪≫ₗ
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ I_U) I_V).toLinearEquiv.restrictScalars A

/--
V.R3 / V-2: canonical linear bridge from the classical joint quotient to
Mathlib `Tor_0`.
-/
noncomputable def classicalJointLinearEquivMathlibTorZero (I_U I_V : Ideal A) :
    classicalJointQuotient A I_U I_V ≃ₗ[A] mathlibTor A I_U I_V 0 :=
  classicalJointLinearEquivTensor A I_U I_V ≪≫ₗ
    (mathlibTorZeroIsoTensor A I_U I_V).symm.toLinearEquiv

/--
V.定義4.1: selected chart-level derived tensor complex.

This is the bounded surface for `(O_X/I_U) ⊗^L (O_X/I_V)` used by R3. It records
the chosen complex and its degree-zero homology carrier, but does not construct a
finite free resolution or compute higher homology.
-/
structure SelectedDerivedTensorComplex (I_U I_V : Ideal A) where
  Term : Nat -> Type v
  [termAddCommGroup : (n : Nat) -> AddCommGroup (Term n)]
  [termModule : (n : Nat) -> Module A (Term n)]
  d : (n : Nat) -> Term n.succ →ₗ[A] Term n
  d_comp_d : ∀ (n : Nat) (x : Term n.succ.succ), d n (d n.succ x) = 0
  H0 : Type v
  [h0AddCommGroup : AddCommGroup H0]
  [h0Module : Module A H0]
  h0LinearEquivClassicalJoint : H0 ≃ₗ[A] classicalJointQuotient A I_U I_V

attribute [instance] SelectedDerivedTensorComplex.termAddCommGroup
attribute [instance] SelectedDerivedTensorComplex.termModule
attribute [instance] SelectedDerivedTensorComplex.h0AddCommGroup
attribute [instance] SelectedDerivedTensorComplex.h0Module

namespace SelectedDerivedTensorComplex

variable {A}

/-- V.定義4.1: degree-zero term of the selected derived tensor complex. -/
abbrev C0 {I_U I_V : Ideal A}
    (T : SelectedDerivedTensorComplex.{v} A I_U I_V) : Type v :=
  T.Term 0

/-- V.定義4.1: selected degree-zero homology carrier. -/
abbrev homology0 {I_U I_V : Ideal A}
    (T : SelectedDerivedTensorComplex.{v} A I_U I_V) : Type v :=
  T.H0

/-- V.R3: selected `H_0` of the derived tensor complex recovers the classical joint quotient. -/
def homology0LinearEquivClassicalJoint {I_U I_V : Ideal A}
    (T : SelectedDerivedTensorComplex.{v} A I_U I_V) :
    T.homology0 ≃ₗ[A] classicalJointQuotient A I_U I_V :=
  T.h0LinearEquivClassicalJoint

end SelectedDerivedTensorComplex

/--
V.定義4.1: chart-level derived intersection surface.

This records the two selected Koszul presentations, the selected derived tensor
complex, and the classical degree-zero joint quotient. It deliberately avoids a
general derived category `D(O_X)`.
-/
structure ChartDerivedIntersection (I_U I_V : Ideal A) where
  leftKoszul : Koszul.KoszulComplex.{u, v} A I_U
  rightKoszul : Koszul.KoszulComplex.{u, v} A I_V
  derivedTensor : SelectedDerivedTensorComplex.{v} A I_U I_V

namespace ChartDerivedIntersection

variable {A}

/-- V.定義4.1: degree-zero classical quotient of the selected derived intersection. -/
abbrev classicalQuotient {I_U I_V : Ideal A}
    (_X : ChartDerivedIntersection.{u, v} A I_U I_V) :=
  classicalJointQuotient A I_U I_V

/-- V.定義4.1: selected complex representing `(O_X/I_U) ⊗^L (O_X/I_V)`. -/
def structureSheafComplex {I_U I_V : Ideal A}
    (X : ChartDerivedIntersection.{u, v} A I_U I_V) :
    SelectedDerivedTensorComplex.{v} A I_U I_V :=
  X.derivedTensor

/-- V.R3: selected degree-zero homology of the derived intersection is the joint quotient. -/
def homology0LinearEquivClassicalJoint {I_U I_V : Ideal A}
    (X : ChartDerivedIntersection.{u, v} A I_U I_V) :
    X.structureSheafComplex.homology0 ≃ₗ[A] classicalJointQuotient A I_U I_V :=
  X.structureSheafComplex.homology0LinearEquivClassicalJoint

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

/--
V.R3 / V-2: canonical selected Tor bridge.

Degree zero is represented by the classical joint quotient and bridged to
Mathlib `Tor_0` by the standard zero-th derived-functor/tensor quotient
calculation. Positive degrees are represented by Mathlib `Tor_i` itself.
-/
noncomputable def canonicalSelectedTorBridge (I_U I_V : Ideal A) :
    SelectedTorBridge.{v} A I_U I_V where
  Tor
    | 0 => classicalJointQuotient A I_U I_V
    | i + 1 => mathlibTor A I_U I_V (i + 1)
  torAddCommGroup := fun i => by
    cases i with
    | zero => infer_instance
    | succ _ => infer_instance
  torModule := fun i => by
    cases i with
    | zero => infer_instance
    | succ _ => infer_instance
  torLinearEquivMathlib := fun i => by
    cases i with
    | zero => exact classicalJointLinearEquivMathlibTorZero A I_U I_V
    | succ i => exact LinearEquiv.refl A (mathlibTor A I_U I_V (i + 1))
  tor0CommRing := inferInstance
  tor0Algebra := inferInstance
  tor0AlgEquivClassicalJoint := AlgEquiv.refl

/--
V.R3 / V-2: the canonical selected bridge has the required degree-zero
law-conflict quotient reading.
-/
noncomputable def canonicalSelectedTorBridgeLawConflict0AlgEquivClassicalJoint
    (I_U I_V : Ideal A) :
    (canonicalSelectedTorBridge A I_U I_V).Tor 0 ≃ₐ[A]
      classicalJointQuotient A I_U I_V :=
  (canonicalSelectedTorBridge A I_U I_V).tor0AlgEquivClassicalJoint

/--
V.R3 / V-2: the canonical selected bridge also supplies the Mathlib `Tor_0`
linear equivalence.
-/
noncomputable def canonicalSelectedTorBridgeLawConflict0LinearEquivMathlibTor
    (I_U I_V : Ideal A) :
    (canonicalSelectedTorBridge A I_U I_V).Tor 0 ≃ₗ[A]
      mathlibTor A I_U I_V 0 :=
  (canonicalSelectedTorBridge A I_U I_V).torLinearEquivMathlib 0

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

/--
V.R3 / V-2: canonical law-conflict package attached to an existing derived
intersection. The derived-intersection data remain explicit; the Tor bridge is
the canonical Mathlib bridge above.
-/
noncomputable def ChartDerivedIntersection.toCanonicalLawConflictPackage
    {I_U I_V : Ideal A}
    (X : ChartDerivedIntersection.{u, v} A I_U I_V) :
    LawConflictPackage.{u, v} A I_U I_V where
  intersection := X
  torBridge := canonicalSelectedTorBridge A I_U I_V

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

/--
V.R3: selected global notation for law-conflict sheaves.

This packages the notation for `H^0(X, LawConflict_i)` and hypercohomology of
the selected derived intersection. It is only notation data; it does not prove a
Cech-to-sheaf comparison or compute global cohomology.
-/
structure SelectedGlobalLawConflictReading (I_U I_V : Ideal A) where
  package : LawConflictPackage.{u, v} A I_U I_V
  H0LawConflict : Nat -> Type v
  [h0AddCommGroup : (i : Nat) -> AddCommGroup (H0LawConflict i)]
  [h0Module : (i : Nat) -> Module A (H0LawConflict i)]
  h0LawConflictLinearEquivSelected :
    (i : Nat) -> H0LawConflict i ≃ₗ[A] package.LawConflict i
  Hypercohomology : Int -> Type v
  [hyperAddCommGroup : (n : Int) -> AddCommGroup (Hypercohomology n)]
  [hyperModule : (n : Int) -> Module A (Hypercohomology n)]

attribute [instance] SelectedGlobalLawConflictReading.h0AddCommGroup
attribute [instance] SelectedGlobalLawConflictReading.h0Module
attribute [instance] SelectedGlobalLawConflictReading.hyperAddCommGroup
attribute [instance] SelectedGlobalLawConflictReading.hyperModule

namespace SelectedGlobalLawConflictReading

variable {A}

/-- V.R3: selected notation for `H^0(X, LawConflict_i)`. -/
abbrev H0 {I_U I_V : Ideal A}
    (G : SelectedGlobalLawConflictReading.{u, v} A I_U I_V) (i : Nat) : Type v :=
  G.H0LawConflict i

/-- V.R3: selected notation for `H^0(X, LawConflict_1)`. -/
abbrev H0LawConflict₁ {I_U I_V : Ideal A}
    (G : SelectedGlobalLawConflictReading.{u, v} A I_U I_V) : Type v :=
  G.H0 1

/-- V.R3: selected bridge from global notation back to the chosen local law conflict. -/
def h0LinearEquivSelectedLawConflict {I_U I_V : Ideal A}
    (G : SelectedGlobalLawConflictReading.{u, v} A I_U I_V) (i : Nat) :
    G.H0 i ≃ₗ[A] G.package.LawConflict i :=
  G.h0LawConflictLinearEquivSelected i

/-- V.R3: selected hypercohomology notation for the derived intersection. -/
abbrev hypercohomology {I_U I_V : Ideal A}
    (G : SelectedGlobalLawConflictReading.{u, v} A I_U I_V) (n : Int) : Type v :=
  G.Hypercohomology n

end SelectedGlobalLawConflictReading

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
    (right : Koszul.KoszulComplex.{u, v} A P.I_V)
    (derivedTensor : Intersection.SelectedDerivedTensorComplex.{v} A P.I_U P.I_V) :
    DerivedIntersectionFor P :=
  ⟨left, right, derivedTensor⟩

end LawfulLoci.LawUniversePair

end Derived
end AAT.AG
