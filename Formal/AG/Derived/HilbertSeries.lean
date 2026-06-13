import Formal.AG.Derived.StructurallyLawfulRepair

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace HilbertSeriesTheory

/--
V.定義12.1: Hilbert series as a degree-wise coefficient reading.

This deliberately avoids rational-function presentation; coefficients are the
selected degree-wise audit data.
-/
structure HilbertSeries where
  coeff : Nat -> Int

namespace HilbertSeries

theorem ext {H K : HilbertSeries} (h : ∀ n, H.coeff n = K.coeff n) :
    H = K := by
  cases H with
  | mk hCoeff =>
      cases K with
      | mk kCoeff =>
          congr
          funext n
          exact h n

/-- V.定義12.1: Hilbert series read from degree-wise finite dimensions. -/
def ofNatCoefficients (degreeDimension : Nat -> Nat) : HilbertSeries where
  coeff n := degreeDimension n

@[simp] theorem ofNatCoefficients_coeff (degreeDimension : Nat -> Nat) (n : Nat) :
    (ofNatCoefficients degreeDimension).coeff n = degreeDimension n :=
  rfl

instance : Zero HilbertSeries where
  zero := ⟨fun _ => 0⟩

instance : Add HilbertSeries where
  add H K := ⟨fun n => H.coeff n + K.coeff n⟩

instance : Neg HilbertSeries where
  neg H := ⟨fun n => -H.coeff n⟩

instance : Sub HilbertSeries where
  sub H K := ⟨fun n => H.coeff n - K.coeff n⟩

/-- V.定義12.1: Cauchy product of coefficient readings. -/
instance : Mul HilbertSeries where
  mul H K := ⟨fun n => (Finset.range (n + 1)).sum
    (fun i => H.coeff i * K.coeff (n - i))⟩

@[simp] theorem zero_coeff (n : Nat) :
    (0 : HilbertSeries).coeff n = 0 :=
  rfl

@[simp] theorem add_coeff (H K : HilbertSeries) (n : Nat) :
    (H + K).coeff n = H.coeff n + K.coeff n :=
  rfl

@[simp] theorem sub_coeff (H K : HilbertSeries) (n : Nat) :
    (H - K).coeff n = H.coeff n - K.coeff n :=
  rfl

/-- V.R10: degree shift of a Hilbert series. -/
def shift (d : Nat) (H : HilbertSeries) : HilbertSeries where
  coeff n := if d ≤ n then H.coeff (n - d) else 0

end HilbertSeries

/-- V.定義12.1: selected graded monomial conflict regime. -/
structure GradedMonomialConflictRegime (A : Type v) [CommRing A] where
  I_U : Ideal A
  I_V : Ideal A
  homogeneousMonomialIdeals : Prop
  homogeneousMonomialIdeals_holds : homogeneousMonomialIdeals
  ambientHilbertSeries : HilbertSeries
  quotientUHilbertSeries : HilbertSeries
  quotientVHilbertSeries : HilbertSeries
  jointQuotientHilbertSeries : HilbertSeries
  lawConflictHilbertSeries : Nat -> HilbertSeries

namespace GradedMonomialConflictRegime

variable {A : Type v} [CommRing A]

/-- V.定義12.1: the selected ideals are homogeneous monomial ideals. -/
theorem homogeneousMonomialIdeals_certificate
    (R : GradedMonomialConflictRegime A) :
    R.homogeneousMonomialIdeals :=
  R.homogeneousMonomialIdeals_holds

end GradedMonomialConflictRegime

/--
V.R10: degree-wise short exact Hilbert data.

This strengthens the earlier equality-only package: the equality of Hilbert
series is derived from degree-wise finite dimensions.
-/
structure DegreewiseShortExactPackage where
  leftDimension : Nat -> Nat
  middleDimension : Nat -> Nat
  rightDimension : Nat -> Nat
  middleDimension_eq :
    ∀ n, middleDimension n = leftDimension n + rightDimension n

namespace DegreewiseShortExactPackage

def leftHilbertSeries (S : DegreewiseShortExactPackage) : HilbertSeries :=
  HilbertSeries.ofNatCoefficients S.leftDimension

def middleHilbertSeries (S : DegreewiseShortExactPackage) : HilbertSeries :=
  HilbertSeries.ofNatCoefficients S.middleDimension

def rightHilbertSeries (S : DegreewiseShortExactPackage) : HilbertSeries :=
  HilbertSeries.ofNatCoefficients S.rightDimension

/-- V.R10: Hilbert series additivity from degree-wise short exact dimensions. -/
theorem hilbertSeries_additivity (S : DegreewiseShortExactPackage) :
    S.middleHilbertSeries = S.leftHilbertSeries + S.rightHilbertSeries := by
  apply HilbertSeries.ext
  intro n
  simp [middleHilbertSeries, leftHilbertSeries, rightHilbertSeries,
    S.middleDimension_eq n]

end DegreewiseShortExactPackage

/-- V.R10: degree-wise shifted finite free Hilbert data. -/
structure DegreewiseShiftedFreePackage where
  rank : Nat
  shiftDegree : Nat
  ambientDimension : Nat -> Nat
  shiftedDimension : Nat -> Nat
  shiftedDimension_eq :
    ∀ n, shiftedDimension n =
      rank * if shiftDegree ≤ n then ambientDimension (n - shiftDegree) else 0

namespace DegreewiseShiftedFreePackage

def ambientHilbertSeries (F : DegreewiseShiftedFreePackage) : HilbertSeries :=
  HilbertSeries.ofNatCoefficients F.ambientDimension

def shiftedFreeHilbertSeries (F : DegreewiseShiftedFreePackage) : HilbertSeries :=
  HilbertSeries.ofNatCoefficients F.shiftedDimension

/-- V.R10: shifted free Hilbert series from degree-wise dimensions. -/
theorem shiftedFree_eq_rank_smul_shift (F : DegreewiseShiftedFreePackage) :
    F.shiftedFreeHilbertSeries =
      ⟨fun n => (F.rank : Int) *
        (HilbertSeries.shift F.shiftDegree F.ambientHilbertSeries).coeff n⟩ := by
  apply HilbertSeries.ext
  intro n
  simp [shiftedFreeHilbertSeries, ambientHilbertSeries, HilbertSeries.shift,
    F.shiftedDimension_eq n]

end DegreewiseShiftedFreePackage

/-- V.R10: degree-wise Euler characteristic data for a finite complex. -/
structure DegreewiseEulerCharacteristicPackage where
  termEulerCoeff : Nat -> Int
  homologyEulerCoeff : Nat -> Int
  coeff_eq : ∀ n, termEulerCoeff n = homologyEulerCoeff n

namespace DegreewiseEulerCharacteristicPackage

def termEulerHilbertSeries (E : DegreewiseEulerCharacteristicPackage) : HilbertSeries where
  coeff := E.termEulerCoeff

def homologyEulerHilbertSeries (E : DegreewiseEulerCharacteristicPackage) : HilbertSeries where
  coeff := E.homologyEulerCoeff

/--
V.R10: finite complex Euler characteristic agrees with homology Euler
characteristic by degree-wise coefficient equality.
-/
theorem eulerCharacteristic_eq (E : DegreewiseEulerCharacteristicPackage) :
    E.termEulerHilbertSeries = E.homologyEulerHilbertSeries := by
  apply HilbertSeries.ext
  exact E.coeff_eq

end DegreewiseEulerCharacteristicPackage

/-- V.R10: short exact sequence Hilbert series additivity package. -/
structure HilbertSeriesShortExactPackage where
  left : HilbertSeries
  middle : HilbertSeries
  right : HilbertSeries
  additivity : middle = left + right

namespace HilbertSeriesShortExactPackage

/-- V.R10: Hilbert series is additive in the selected short exact sequence. -/
theorem additivity_certificate (S : HilbertSeriesShortExactPackage) :
    S.middle = S.left + S.right :=
  S.additivity

end HilbertSeriesShortExactPackage

/-- V.R10: shifted finite free module Hilbert series package. -/
structure ShiftedFreeHilbertSeriesPackage where
  rank : Nat
  shiftDegree : Nat
  ambient : HilbertSeries
  shiftedFree : HilbertSeries
  shiftedFree_eq :
    shiftedFree = ⟨fun n => (rank : Int) * (HilbertSeries.shift shiftDegree ambient).coeff n⟩

namespace ShiftedFreeHilbertSeriesPackage

/-- V.R10: shifted free module Hilbert series is rank times the shifted ambient series. -/
theorem shiftedFree_certificate (F : ShiftedFreeHilbertSeriesPackage) :
    F.shiftedFree =
      ⟨fun n => (F.rank : Int) * (HilbertSeries.shift F.shiftDegree F.ambient).coeff n⟩ :=
  F.shiftedFree_eq

end ShiftedFreeHilbertSeriesPackage

/-- V.R10: finite complex Euler characteristic package. -/
structure FiniteComplexEulerCharacteristicPackage where
  termEulerCharacteristic : HilbertSeries
  homologyEulerCharacteristic : HilbertSeries
  eulerCharacteristic_eq : termEulerCharacteristic = homologyEulerCharacteristic

namespace FiniteComplexEulerCharacteristicPackage

/--
V.R10: finite complex Euler characteristic agrees with the homology Euler
characteristic for the selected finite complex.
-/
theorem eulerCharacteristic_certificate
    (E : FiniteComplexEulerCharacteristicPackage) :
    E.termEulerCharacteristic = E.homologyEulerCharacteristic :=
  E.eulerCharacteristic_eq

end FiniteComplexEulerCharacteristicPackage

/--
V.定理12.2: selected Hilbert series conflict identity package.

The identity is stored in denominator-cleared form:
`H_{R/I_U} * H_{R/I_V} = H_R * Σ_i (-1)^i H_{LawConflict_i}`.
-/
structure HilbertSeriesConflictIdentityPackage (A : Type v) [CommRing A] where
  regime : GradedMonomialConflictRegime A
  conflictAlternatingSum : HilbertSeries
  eulerCharacteristic : FiniteComplexEulerCharacteristicPackage
  denominatorClearedIdentity :
    regime.quotientUHilbertSeries * regime.quotientVHilbertSeries =
      regime.ambientHilbertSeries * conflictAlternatingSum

namespace HilbertSeriesConflictIdentityPackage

variable {A : Type v} [CommRing A]

/-- V.定理12.2: denominator-cleared Hilbert series conflict identity. -/
theorem denominatorClearedIdentity_certificate
    (G : HilbertSeriesConflictIdentityPackage A) :
    G.regime.quotientUHilbertSeries * G.regime.quotientVHilbertSeries =
      G.regime.ambientHilbertSeries * G.conflictAlternatingSum :=
  G.denominatorClearedIdentity

/-- V.定理12.2: the selected Euler characteristic certificate used by the identity. -/
theorem eulerCharacteristic_certificate
    (G : HilbertSeriesConflictIdentityPackage A) :
    G.eulerCharacteristic.termEulerCharacteristic =
      G.eulerCharacteristic.homologyEulerCharacteristic :=
  G.eulerCharacteristic.eulerCharacteristic_certificate

/-- V.定理12.2: interference series audit reading. -/
def interferenceSeries (G : HilbertSeriesConflictIdentityPackage A) : HilbertSeries :=
  G.regime.jointQuotientHilbertSeries - G.conflictAlternatingSum

@[simp] theorem interferenceSeries_coeff
    (G : HilbertSeriesConflictIdentityPackage A) (n : Nat) :
    (G.interferenceSeries).coeff n =
      G.regime.jointQuotientHilbertSeries.coeff n - G.conflictAlternatingSum.coeff n :=
  rfl

end HilbertSeriesConflictIdentityPackage

/--
V.定理12.2: coefficient-wise certificate for the denominator-cleared Hilbert
series identity.

This is stronger than storing the series equality directly: the global equality
is reconstructed from equality in every degree.
-/
structure HilbertSeriesConflictCoefficientIdentityPackage (A : Type v) [CommRing A] where
  regime : GradedMonomialConflictRegime A
  conflictAlternatingSum : HilbertSeries
  eulerCharacteristic : FiniteComplexEulerCharacteristicPackage
  coefficientIdentity :
    ∀ n,
      (regime.quotientUHilbertSeries * regime.quotientVHilbertSeries).coeff n =
        (regime.ambientHilbertSeries * conflictAlternatingSum).coeff n

namespace HilbertSeriesConflictCoefficientIdentityPackage

variable {A : Type v} [CommRing A]

/--
V.定理12.2: denominator-cleared identity obtained from coefficient-wise data.
-/
theorem denominatorClearedIdentity_of_coefficients
    (G : HilbertSeriesConflictCoefficientIdentityPackage A) :
    G.regime.quotientUHilbertSeries * G.regime.quotientVHilbertSeries =
      G.regime.ambientHilbertSeries * G.conflictAlternatingSum := by
  apply HilbertSeries.ext
  exact G.coefficientIdentity

/-- V.定理12.2: forget the coefficient proof to the ordinary identity package. -/
def toIdentityPackage
    (G : HilbertSeriesConflictCoefficientIdentityPackage A) :
    HilbertSeriesConflictIdentityPackage A where
  regime := G.regime
  conflictAlternatingSum := G.conflictAlternatingSum
  eulerCharacteristic := G.eulerCharacteristic
  denominatorClearedIdentity := G.denominatorClearedIdentity_of_coefficients

/-- V.定理12.2: the selected Euler characteristic certificate used by the identity. -/
theorem eulerCharacteristic_certificate
    (G : HilbertSeriesConflictCoefficientIdentityPackage A) :
    G.eulerCharacteristic.termEulerCharacteristic =
      G.eulerCharacteristic.homologyEulerCharacteristic :=
  G.eulerCharacteristic.eulerCharacteristic_certificate

end HilbertSeriesConflictCoefficientIdentityPackage

/--
V.R11(c): finite degree-window audit package for a concrete Hilbert-series G5
calculation.

This is intentionally finite: it records the checked numerical window without
claiming a general monomial Hilbert-series computation beyond the selected data.
-/
structure HilbertSeriesFiniteWindowConflictAuditPackage (A : Type v) [CommRing A] where
  regime : GradedMonomialConflictRegime A
  conflictAlternatingSum : HilbertSeries
  window : Finset Nat
  coefficientIdentityOnWindow :
    ∀ n, n ∈ window →
      (regime.quotientUHilbertSeries * regime.quotientVHilbertSeries).coeff n =
        (regime.ambientHilbertSeries * conflictAlternatingSum).coeff n

namespace HilbertSeriesFiniteWindowConflictAuditPackage

variable {A : Type v} [CommRing A]

/-- V.R11(c): read the checked coefficient identity inside the finite window. -/
theorem coefficientIdentity_certificate
    (G : HilbertSeriesFiniteWindowConflictAuditPackage A) {n : Nat}
    (hn : n ∈ G.window) :
    (G.regime.quotientUHilbertSeries * G.regime.quotientVHilbertSeries).coeff n =
      (G.regime.ambientHilbertSeries * G.conflictAlternatingSum).coeff n :=
  G.coefficientIdentityOnWindow n hn

end HilbertSeriesFiniteWindowConflictAuditPackage

end HilbertSeriesTheory

end Derived
end AAT.AG
