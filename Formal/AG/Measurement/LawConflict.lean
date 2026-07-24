import Formal.AG.Measurement.Hodge
import Formal.AG.Derived.Intersection

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v w

/-!
Part VIII R7 / AC17 common ambient pairs, LawConflict measurement, and flat
base-change candidate statements.

LawConflict readings are only recorded relative to an explicitly selected
common ambient pair. The flat base-change surface is a theorem-candidate
interface; it does not assert general Tor base-change.
-/

/--
VIII.Definition 9.1: selected common ambient pair for two law ideals.

The pair fixes the common ringed ambient, selected law ideals, coefficient
objects, witness pair, and comparison profile needed before LawConflict
measurements may be compared.
-/
structure CommonAmbientPair (M : MeasurementProfile.{u, v}) where
  AmbientSpace : Type u
  StructureSheaf : Type v
  LawIdeal : Type v
  CoefficientObject : Type v
  WitnessPair : Type u
  ComparisonProfile : Type u
  SupportCarrier : Type u
  leftDomain : M.Domain
  rightDomain : M.Domain
  selectedAmbient : AmbientSpace
  selectedStructureSheaf : StructureSheaf
  leftLawIdeal : LawIdeal
  rightLawIdeal : LawIdeal
  leftCoefficient : CoefficientObject
  rightCoefficient : CoefficientObject
  selectedWitnessPair : WitnessPair
  selectedComparisonProfile : ComparisonProfile
  commonRingedSite : Prop
  commonRingedSite_cert : commonRingedSite
  lawIdealsInCommonAmbient : Prop
  lawIdealsInCommonAmbient_cert : lawIdealsInCommonAmbient
  coefficientsCompatible : Prop
  coefficientsCompatible_cert : coefficientsCompatible
  witnessesComparable : Prop
  witnessesComparable_cert : witnessesComparable
  comparisonProfileFixed : Prop
  comparisonProfileFixed_cert : comparisonProfileFixed
  noComparisonWithoutCommonAmbient : Prop
  noComparisonWithoutCommonAmbient_cert : noComparisonWithoutCommonAmbient

namespace CommonAmbientPair

/-- VIII.Definition 9.1: expose the selected common ringed-site certificate. -/
theorem commonRingedSite_holds {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M) : A.commonRingedSite :=
  A.commonRingedSite_cert

/-- VIII.Definition 9.1: expose that both law ideals live in the common ambient. -/
theorem lawIdealsInCommonAmbient_holds {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M) : A.lawIdealsInCommonAmbient :=
  A.lawIdealsInCommonAmbient_cert

/-- VIII.Definition 9.1: expose compatible coefficient data for the pair. -/
theorem coefficientsCompatible_holds {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M) : A.coefficientsCompatible :=
  A.coefficientsCompatible_cert

/-- VIII.Definition 9.1: expose the non-comparison boundary outside a common ambient. -/
theorem noComparisonWithoutCommonAmbient_holds {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M) : A.noComparisonWithoutCommonAmbient :=
  A.noComparisonWithoutCommonAmbient_cert

end CommonAmbientPair

/--
VIII.Definition 9.1: selected LawConflict measurement.

This records the Tor object and selected conflict class only after a
`CommonAmbientPair` has fixed the shared ambient and coefficient comparison
data.
-/
structure LawConflictMeasurement {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M) where
  Degree : Type u
  selectedDegree : Degree
  LeftQuotient : Type w
  RightQuotient : Type w
  TorObject : Type w
  ConflictClass : Type w
  selectedConflictClass : ConflictClass
  conflictSupport : ConflictClass -> A.SupportCarrier -> Prop
  selectedSupport : A.SupportCarrier
  ZeroConflict : ConflictClass -> Prop
  NontrivialConflict : ConflictClass -> Prop
  lawConflictTorReading : Prop
  lawConflictTorReading_cert : lawConflictTorReading
  selectedClassSupportReading : Prop
  selectedClassSupportReading_cert : selectedClassSupportReading
  commonAmbientRequired : Prop
  commonAmbientRequired_cert : commonAmbientRequired
  coefficientCompatibilityUsed : Prop
  coefficientCompatibilityUsed_cert : coefficientCompatibilityUsed
  topologyAndCoefficientBoundary : Prop
  topologyAndCoefficientBoundary_cert : topologyAndCoefficientBoundary

namespace LawConflictMeasurement

/-- VIII.Definition 9.1: expose the selected Tor formula reading. -/
theorem lawConflictTorReading_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} (L : LawConflictMeasurement A) :
    L.lawConflictTorReading :=
  L.lawConflictTorReading_cert

/-- VIII.Definition 9.1: expose the selected support reading for the conflict class. -/
theorem selectedClassSupportReading_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} (L : LawConflictMeasurement A) :
    L.selectedClassSupportReading :=
  L.selectedClassSupportReading_cert

/-- VIII.Definition 9.1: LawConflict measurements require the selected common ambient. -/
theorem commonAmbientRequired_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} (L : LawConflictMeasurement A) :
    L.commonAmbientRequired :=
  L.commonAmbientRequired_cert

/--
VIII.Definition 9.1 / R7: build a measurement LawConflict reading from the
Part V derived `LawConflictPackage`.
-/
def ofDerivedLawConflictPackage {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M)
    {R : Type v} [CommRing R] {I_U I_V : Ideal R}
    (P : Derived.Intersection.LawConflictPackage.{u, v} R I_U I_V)
    (degree : Nat)
    (selectedClass : P.LawConflict degree)
    (selectedSupport : A.SupportCarrier)
    (conflictSupport : P.LawConflict degree -> A.SupportCarrier -> Prop)
    (selectedClassSupport : conflictSupport selectedClass selectedSupport) :
    LawConflictMeasurement A where
  Degree := ULift.{u} Nat
  selectedDegree := ULift.up degree
  LeftQuotient := R ⧸ I_U
  RightQuotient := R ⧸ I_V
  TorObject := P.LawConflict degree
  ConflictClass := P.LawConflict degree
  selectedConflictClass := selectedClass
  conflictSupport := conflictSupport
  selectedSupport := selectedSupport
  ZeroConflict := fun x => x = 0
  NontrivialConflict := fun x => x ≠ 0
  lawConflictTorReading :=
    Nonempty (P.LawConflict degree ≃ₗ[R] Derived.Intersection.mathlibTor R I_U I_V degree)
  lawConflictTorReading_cert := ⟨P.lawConflictLinearEquivMathlibTor degree⟩
  selectedClassSupportReading := conflictSupport selectedClass selectedSupport
  selectedClassSupportReading_cert := selectedClassSupport
  commonAmbientRequired := A.commonRingedSite ∧ A.lawIdealsInCommonAmbient
  commonAmbientRequired_cert :=
    ⟨A.commonRingedSite_cert, A.lawIdealsInCommonAmbient_cert⟩
  coefficientCompatibilityUsed := A.coefficientsCompatible
  coefficientCompatibilityUsed_cert := A.coefficientsCompatible_cert
  topologyAndCoefficientBoundary := A.noComparisonWithoutCommonAmbient
  topologyAndCoefficientBoundary_cert := A.noComparisonWithoutCommonAmbient_cert

/--
VIII.Definition 9.1 / R7: build a measurement reading directly from an
existing selected Tor bridge.  This constructor is used when the finite chain
computation already targets that bridge, without requiring a second chart
intersection package solely to recover the same Tor equivalence.  The selected
ideals are also interpreted in the common ambient, so the ambient certificate
records the actual ideals used by the Tor bridge.
-/
def ofSelectedTorBridge {M : MeasurementProfile.{u, v}}
    (A : CommonAmbientPair M)
    {R : Type (max u v)} [CommRing R] {I_U I_V : Ideal R}
    (idealToAmbient : Ideal R → A.LawIdeal)
    (leftIdeal_ambient : idealToAmbient I_U = A.leftLawIdeal)
    (rightIdeal_ambient : idealToAmbient I_V = A.rightLawIdeal)
    (B : Derived.Intersection.SelectedTorBridge.{max u v} R I_U I_V)
    (degree : Nat)
    (selectedClass : B.LawConflict degree)
    (selectedSupport : A.SupportCarrier)
    (conflictSupport : B.LawConflict degree -> A.SupportCarrier -> Prop)
    (selectedClassSupport : conflictSupport selectedClass selectedSupport) :
    LawConflictMeasurement A where
  Degree := ULift.{u} Nat
  selectedDegree := ULift.up degree
  LeftQuotient := R ⧸ I_U
  RightQuotient := R ⧸ I_V
  TorObject := B.LawConflict degree
  ConflictClass := B.LawConflict degree
  selectedConflictClass := selectedClass
  conflictSupport := conflictSupport
  selectedSupport := selectedSupport
  ZeroConflict := fun x => x = 0
  NontrivialConflict := fun x => x ≠ 0
  lawConflictTorReading :=
    Nonempty (B.LawConflict degree ≃ₗ[R]
      Derived.Intersection.mathlibTor R I_U I_V degree)
  lawConflictTorReading_cert := ⟨B.lawConflictLinearEquivMathlibTor degree⟩
  selectedClassSupportReading := conflictSupport selectedClass selectedSupport
  selectedClassSupportReading_cert := selectedClassSupport
  commonAmbientRequired :=
    A.commonRingedSite ∧ A.lawIdealsInCommonAmbient ∧
      idealToAmbient I_U = A.leftLawIdeal ∧
        idealToAmbient I_V = A.rightLawIdeal
  commonAmbientRequired_cert :=
    ⟨A.commonRingedSite_cert, A.lawIdealsInCommonAmbient_cert,
      leftIdeal_ambient, rightIdeal_ambient⟩
  coefficientCompatibilityUsed := A.coefficientsCompatible
  coefficientCompatibilityUsed_cert := A.coefficientsCompatible_cert
  topologyAndCoefficientBoundary := A.noComparisonWithoutCommonAmbient
  topologyAndCoefficientBoundary_cert := A.noComparisonWithoutCommonAmbient_cert

/--
VIII.R7: the measurement bridge exposes the same Mathlib Tor equivalence carried
by the Part V `LawConflictPackage`.
-/
def derivedLawConflictLinearEquivMathlibTor
    {R : Type v} [CommRing R] {I_U I_V : Ideal R}
    (P : Derived.Intersection.LawConflictPackage.{u, v} R I_U I_V)
    (degree : Nat) :
    P.LawConflict degree ≃ₗ[R] Derived.Intersection.mathlibTor R I_U I_V degree :=
  P.lawConflictLinearEquivMathlibTor degree

end LawConflictMeasurement

/--
VIII.Theorem candidate 9.2: flat base-change statement interface.

The affine and sheaf/ringed-site statements are recorded separately. Both are
statement-only candidates guarded by flatness, finite presentation,
coefficient compatibility, and support-pullback assumptions.
-/
structure FlatBaseChangeCandidate {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} (L : LawConflictMeasurement A) where
  BaseRing : Type v
  FlatExtension : Type v
  PullbackLeftIdeal : Type v
  PullbackRightIdeal : Type v
  AffineTorComparison : Type v
  SheafTorComparison : Type v
  SupportPullbackData : Type u
  selectedBaseRing : BaseRing
  selectedFlatExtension : FlatExtension
  selectedPullbackLeftIdeal : PullbackLeftIdeal
  selectedPullbackRightIdeal : PullbackRightIdeal
  selectedAffineComparison : AffineTorComparison
  selectedSheafComparison : SheafTorComparison
  selectedSupportPullback : SupportPullbackData
  flatnessAssumption : Prop
  finitePresentationAssumption : Prop
  coefficientCompatibility : Prop
  supportPullbackCompatibility : Prop
  affineBaseChangeConclusion : Prop
  sheafBaseChangeConclusion : Prop
  affineBaseChangeStatement : Prop
  affineBaseChangeStatement_shape :
    affineBaseChangeStatement =
      (flatnessAssumption ->
        finitePresentationAssumption ->
          coefficientCompatibility ->
            supportPullbackCompatibility ->
              affineBaseChangeConclusion)
  sheafBaseChangeStatement : Prop
  sheafBaseChangeStatement_shape :
    sheafBaseChangeStatement =
      (flatnessAssumption ->
        finitePresentationAssumption ->
          coefficientCompatibility ->
            supportPullbackCompatibility ->
              sheafBaseChangeConclusion)
  candidateOnly : Prop
  candidateOnly_cert : candidateOnly

namespace FlatBaseChangeCandidate

/-- VIII.Theorem candidate 9.2: expose the affine statement shape. -/
theorem affineBaseChangeStatement_shape_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) :
    F.affineBaseChangeStatement =
      (F.flatnessAssumption ->
        F.finitePresentationAssumption ->
          F.coefficientCompatibility ->
            F.supportPullbackCompatibility ->
              F.affineBaseChangeConclusion) :=
  F.affineBaseChangeStatement_shape

/-- VIII.Theorem candidate 9.2: expose the sheaf/ringed-site statement shape. -/
theorem sheafBaseChangeStatement_shape_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) :
    F.sheafBaseChangeStatement =
      (F.flatnessAssumption ->
        F.finitePresentationAssumption ->
          F.coefficientCompatibility ->
            F.supportPullbackCompatibility ->
              F.sheafBaseChangeConclusion) :=
  F.sheafBaseChangeStatement_shape

/-- VIII.Theorem candidate 9.2: record that this is a candidate interface only. -/
theorem candidateOnly_holds {M : MeasurementProfile.{u, v}}
    {A : CommonAmbientPair M} {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) : F.candidateOnly :=
  F.candidateOnly_cert

end FlatBaseChangeCandidate

end Measurement
end AAT.AG
