import Formal.AG.Derived.Transfer

noncomputable section

namespace AAT.AG
namespace Derived

universe u v w

namespace RepairCriterion

/--
V.定義11.1: structurally lawful repair.

The predicate is relative to a chosen repair comparison profile `P_U`, conflict
comparison profile `Q_{U,V}`, and transfer-control reading. It does not assert a
profile-independent repair theorem.
-/
structure StructurallyLawfulRepair (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  repairProfile : RepairProfile.RepairComparisonProfile.{u}
  repairPath : RepairProfile.RepairPath repairProfile
  conflictProfile : RepairProfile.ConflictComparisonProfile.{u, v} A P
  selectedObstructionDecreases : Prop
  selectedObstructionDecreases_holds : selectedObstructionDecreases
  requiredLawfulLociReachable : Prop
  requiredLawfulLociReachable_holds : requiredLawfulLociReachable
  conflictNonIncreasingSelectedDegrees : Prop
  conflictNonIncreasingSelectedDegrees_holds : conflictNonIncreasingSelectedDegrees
  transferZeroOrControlled : Prop
  transferZeroOrControlled_holds : transferZeroOrControlled

namespace StructurallyLawfulRepair

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- V.定義11.1: selected obstruction decreases under `P_U`. -/
theorem selectedObstructionDecreases_certificate
    (R : StructurallyLawfulRepair.{u, v} A P) :
    R.selectedObstructionDecreases :=
  R.selectedObstructionDecreases_holds

/-- V.定義11.1: required lawful loci remain reachable. -/
theorem requiredLawfulLociReachable_certificate
    (R : StructurallyLawfulRepair.{u, v} A P) :
    R.requiredLawfulLociReachable :=
  R.requiredLawfulLociReachable_holds

/-- V.定義11.1: selected derived conflict does not increase in the chosen degrees. -/
theorem conflictNonIncreasingSelectedDegrees_certificate
    (R : StructurallyLawfulRepair.{u, v} A P) :
    R.conflictNonIncreasingSelectedDegrees :=
  R.conflictNonIncreasingSelectedDegrees_holds

/-- V.定義11.1: selected transfer is zero or controlled. -/
theorem transferZeroOrControlled_certificate
    (R : StructurallyLawfulRepair.{u, v} A P) :
    R.transferZeroOrControlled :=
  R.transferZeroOrControlled_holds

/-- V.定義11.1: the underlying repair path decreases the selected `U`-axis. -/
theorem uAxisDecrease_certificate
    (R : StructurallyLawfulRepair.{u, v} A P) :
    RepairProfile.UAxisObstructionDecreases R.repairProfile
      R.repairPath.targetSection R.repairPath.sourceSection :=
  R.repairPath.uAxisDecrease_certificate

/-- V.定義11.1: the conflict profile records non-increase for its selected reading. -/
theorem selectedConflictProfileDoesNotIncrease
    (R : StructurallyLawfulRepair.{u, v} A P) :
    R.conflictProfile.doesNotIncreaseSelectedConflict :=
  R.conflictProfile.doesNotIncreaseSelectedConflict_certificate

end StructurallyLawfulRepair

/--
V.定義11.1: low-degree structurally lawful repair reading, restricted to
`LawConflict_1`.
-/
structure LowDegreeStructurallyLawfulRepair (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  repair : StructurallyLawfulRepair.{u, v} A P
  degreeOne : repair.conflictProfile.Degree
  degreeOne_eq_one : repair.conflictProfile.degree degreeOne = 1

namespace LowDegreeStructurallyLawfulRepair

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- V.定義11.1: the selected low-degree conflict is degree one. -/
theorem degreeOne_certificate
    (R : LowDegreeStructurallyLawfulRepair.{u, v} A P) :
    R.repair.conflictProfile.degree R.degreeOne = 1 :=
  R.degreeOne_eq_one

/-- V.定義11.1: the low-degree selection is a positive selected degree. -/
theorem degreeOne_positive
    (R : LowDegreeStructurallyLawfulRepair.{u, v} A P) :
    0 < R.repair.conflictProfile.degree R.degreeOne :=
  R.repair.conflictProfile.selectedDegree_positive R.degreeOne

/-- V.定義11.1: low-degree reading inherits structurally lawful repair data. -/
theorem selectedObstructionDecreases_certificate
    (R : LowDegreeStructurallyLawfulRepair.{u, v} A P) :
    R.repair.selectedObstructionDecreases :=
  R.repair.selectedObstructionDecreases_certificate

/-- V.定義11.1: low-degree reading inherits transfer control. -/
theorem transferZeroOrControlled_certificate
    (R : LowDegreeStructurallyLawfulRepair.{u, v} A P) :
    R.repair.transferZeroOrControlled :=
  R.repair.transferZeroOrControlled_certificate

end LowDegreeStructurallyLawfulRepair

end RepairCriterion

end Derived
end AAT.AG
