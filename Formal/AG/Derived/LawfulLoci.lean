import Formal.AG.LawAlgebra.LawfulLocus

noncomputable section

namespace AAT.AG
namespace Derived

universe u v

namespace LawfulLoci

variable (A : Type v) [CommRing A]

/-- V.R0/R1: a selected law-universe reading on one affine chart. -/
abbrev LawUniverseReading :=
  LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} A

/-- V.R1: a pair of law universes read on the same chart algebra. -/
structure LawUniversePair where
  U : LawUniverseReading.{u, v} A
  V : LawUniverseReading.{u, v} A

namespace LawUniversePair

/-- V.定義2.1: Part V notation `I_U` for the obstruction ideal of `U`. -/
def I_U (P : LawUniversePair.{u, v} A) : Ideal A :=
  P.U.localObstructionIdeal

/-- V.定義2.1: Part V notation `I_V` for the obstruction ideal of `V`. -/
def I_V (P : LawUniversePair.{u, v} A) : Ideal A :=
  P.V.localObstructionIdeal

/-- V.定義2.1: lawful locus `Flat_U(X) = V(I_U)`. -/
def flatU (P : LawUniversePair.{u, v} A) : Set (PrimeSpectrum A) :=
  LawAlgebra.LawfulLocus.lawfulLocus A P.I_U

/-- V.定義2.1: lawful locus `Flat_V(X) = V(I_V)`. -/
def flatV (P : LawUniversePair.{u, v} A) : Set (PrimeSpectrum A) :=
  LawAlgebra.LawfulLocus.lawfulLocus A P.I_V

/-- V.定義3.1: ideal cutting out the classical joint lawful locus. -/
def classicalJointIdeal (P : LawUniversePair.{u, v} A) : Ideal A :=
  P.I_U + P.I_V

/-- V.定義3.1: classical joint lawful locus `Flat_U(X) ∩ Flat_V(X) = V(I_U + I_V)`. -/
def classicalJointLawfulLocus (P : LawUniversePair.{u, v} A) :
    Set (PrimeSpectrum A) :=
  LawAlgebra.LawfulLocus.lawfulLocus A P.classicalJointIdeal

/-- V.R1: the `U` locus reuses the Part III lawful-locus surface. -/
theorem flatU_eq_lawfulLocus (P : LawUniversePair.{u, v} A) :
    P.flatU = LawAlgebra.LawfulLocus.localLawfulLocus A P.U :=
  rfl

/-- V.R1: the `V` locus reuses the Part III lawful-locus surface. -/
theorem flatV_eq_lawfulLocus (P : LawUniversePair.{u, v} A) :
    P.flatV = LawAlgebra.LawfulLocus.localLawfulLocus A P.V :=
  rfl

/-- V.定義3.1: the classical joint locus is exactly `V(I_U + I_V)`. -/
theorem classicalJointLawfulLocus_eq_zeroLocus (P : LawUniversePair.{u, v} A) :
    P.classicalJointLawfulLocus =
      PrimeSpectrum.zeroLocus (P.I_U + P.I_V) :=
  rfl

/-- V.定義3.1: the joint locus agrees with the intersection of the two lawful loci. -/
theorem classicalJointLawfulLocus_eq_flatU_inter_flatV (P : LawUniversePair.{u, v} A) :
    P.classicalJointLawfulLocus = P.flatU ∩ P.flatV := by
  simp [classicalJointLawfulLocus, classicalJointIdeal, flatU, flatV,
    LawAlgebra.LawfulLocus.lawfulLocus, PrimeSpectrum.zeroLocus_sup]

end LawUniversePair

end LawfulLoci

end Derived
end AAT.AG
