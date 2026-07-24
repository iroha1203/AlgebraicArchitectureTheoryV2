import Formal.AG.Measurement.Hodge
import Formal.AG.Derived.Intersection
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section

namespace AAT.AG
namespace Measurement

universe u v w

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

/--
An affine scheme together with two actual Mathlib ideal sheaves on that same
scheme.

`ofSpec` is the canonical constructor used by equation-generated conflict
measurements.  It derives both ideal sheaves from coordinate-ring ideals
through `ΓSpecIso`.
-/
structure AffineIdealSheafPair where
  scheme : AlgebraicGeometry.Scheme.{u}
  schemeIsAffine : IsAffine scheme
  leftIdealSheaf : scheme.IdealSheafData
  rightIdealSheaf : scheme.IdealSheafData

namespace AffineIdealSheafPair

/-- Canonical pair of ideal sheaves on `Spec R`. -/
noncomputable def ofSpec
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    AffineIdealSheafPair.{u} := by
  let X := AlgebraicGeometry.Scheme.Spec.obj
    (op (CommRingCat.of R))
  let e := (AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of R)).commRingCatIsoToRingEquiv
  exact {
    scheme := X
    schemeIsAffine := inferInstance
    leftIdealSheaf :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map e.symm.toRingHom leftIdeal)
    rightIdealSheaf :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map e.symm.toRingHom rightIdeal)
  }

/-- The affine scheme selected by `ofSpec` is exactly `Spec R`. -/
theorem ofSpec_scheme
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    (ofSpec leftIdeal rightIdeal).scheme =
      AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of R)) :=
  rfl

/-- The left ideal sheaf is induced from the transported left coordinate
ideal. -/
theorem ofSpec_leftIdealSheaf
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    (ofSpec leftIdeal rightIdeal).leftIdealSheaf =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
          leftIdeal) :=
  rfl

/-- The right ideal sheaf is induced from the transported right coordinate
ideal. -/
theorem ofSpec_rightIdealSheaf
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    (ofSpec leftIdeal rightIdeal).rightIdealSheaf =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        (Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
          rightIdeal) :=
  rfl

/-- The top component of the left ideal sheaf recovers the original
coordinate-ring ideal through `ΓSpecIso`. -/
theorem ofSpec_leftIdealSheaf_top
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let pair := ofSpec leftIdeal rightIdeal
    let _ : IsAffine pair.scheme :=
      pair.schemeIsAffine
    Ideal.map e.toRingHom
      (pair.leftIdealSheaf.ideal
        ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          leftIdeal := by
  dsimp [ofSpec]
  have hmap :
      (AlgebraicGeometry.Spec
        (CommRingCat.of R)).presheaf.map
          (𝟙 (op (⊤ :
            (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens))) =
        𝟙 ((AlgebraicGeometry.Spec
          (CommRingCat.of R)).presheaf.obj
            (op (⊤ :
              (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens))) :=
    (AlgebraicGeometry.Spec
      (CommRingCat.of R)).presheaf.map_id _
  rw [hmap, CommRingCat.hom_id, Ideal.map_id]
  change
    Ideal.map
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
      (Ideal.map
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
        leftIdeal) =
      leftIdeal
  have hs :
      Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
          leftIdeal =
        Ideal.comap
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
          leftIdeal :=
    Ideal.map_symm
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv
  rw [hs]
  exact
    Ideal.map_comap_of_surjective
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).surjective
      leftIdeal

/-- The top component of the right ideal sheaf recovers the original
coordinate-ring ideal through `ΓSpecIso`. -/
theorem ofSpec_rightIdealSheaf_top
    {R : Type u} [CommRing R]
    (leftIdeal rightIdeal : Ideal R) :
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let pair := ofSpec leftIdeal rightIdeal
    let _ : IsAffine pair.scheme :=
      pair.schemeIsAffine
    Ideal.map e.toRingHom
      (pair.rightIdealSheaf.ideal
        ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          rightIdeal := by
  dsimp [ofSpec]
  have hmap :
      (AlgebraicGeometry.Spec
        (CommRingCat.of R)).presheaf.map
          (𝟙 (op (⊤ :
            (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens))) =
        𝟙 ((AlgebraicGeometry.Spec
          (CommRingCat.of R)).presheaf.obj
            (op (⊤ :
              (AlgebraicGeometry.Spec (CommRingCat.of R)).Opens))) :=
    (AlgebraicGeometry.Spec
      (CommRingCat.of R)).presheaf.map_id _
  rw [hmap, CommRingCat.hom_id, Ideal.map_id]
  change
    Ideal.map
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
      (Ideal.map
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
        rightIdeal) =
      rightIdeal
  have hs :
      Ideal.map
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
          rightIdeal =
        Ideal.comap
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
          rightIdeal :=
    Ideal.map_symm
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv
  rw [hs]
  exact
    Ideal.map_comap_of_surjective
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).toRingHom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv).surjective
      rightIdeal

end AffineIdealSheafPair

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
  StructureSheaf : Type (max u v + 1)
  LawIdeal : Type (max u v)
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

/--
Construct a common ambient from `Spec R` and two actual ideal sheaves induced
by coordinate-ring ideals.

The canonical `ΓSpecIso` transports each coordinate ideal into the global
sections of `Spec R`, and `IdealSheafData.ofIdealTop` extends it to an ideal
sheaf.  Module-valued Čech obstruction data remains the separate coefficient
data of the selected Čech complex.
-/
noncomputable def ofAffineSpec
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    CommonAmbientPair M where
  AmbientSpace := ULift.{u, 0} Unit
  StructureSheaf := AffineIdealSheafPair.{max u v}
  LawIdeal := Ideal R
  CoefficientObject := M.Coeff
  WitnessPair := WitnessPair
  ComparisonProfile := ComparisonProfile
  SupportCarrier := SupportCarrier
  leftDomain := leftDomain
  rightDomain := rightDomain
  selectedAmbient := ULift.up ()
  selectedStructureSheaf :=
    AffineIdealSheafPair.ofSpec leftIdeal rightIdeal
  leftLawIdeal := leftIdeal
  rightLawIdeal := rightIdeal
  leftCoefficient := selectedCoefficient
  rightCoefficient := selectedCoefficient
  selectedWitnessPair := selectedWitnessPair
  selectedComparisonProfile := selectedComparisonProfile
  commonRingedSite :=
    (AffineIdealSheafPair.ofSpec
      leftIdeal rightIdeal).scheme.toLocallyRingedSpace =
        AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)
  commonRingedSite_cert := rfl
  lawIdealsInCommonAmbient :=
    let e :=
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of R)).commRingCatIsoToRingEquiv
    let pair := AffineIdealSheafPair.ofSpec leftIdeal rightIdeal
    let _ : IsAffine pair.scheme := pair.schemeIsAffine
    Ideal.map e.toRingHom
        (pair.leftIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          leftIdeal ∧
      Ideal.map e.toRingHom
        (pair.rightIdealSheaf.ideal
          ⟨⊤, isAffineOpen_top pair.scheme⟩) =
          rightIdeal
  lawIdealsInCommonAmbient_cert :=
    ⟨AffineIdealSheafPair.ofSpec_leftIdealSheaf_top
        leftIdeal rightIdeal,
      AffineIdealSheafPair.ofSpec_rightIdealSheaf_top
        leftIdeal rightIdeal⟩
  coefficientsCompatible := selectedCoefficient = selectedCoefficient
  coefficientsCompatible_cert := rfl
  witnessesComparable := selectedWitnessPair = selectedWitnessPair
  witnessesComparable_cert := rfl
  comparisonProfileFixed :=
    selectedComparisonProfile = selectedComparisonProfile
  comparisonProfileFixed_cert := rfl
  noComparisonWithoutCommonAmbient :=
    (AffineIdealSheafPair.ofSpec
      leftIdeal rightIdeal).scheme.toLocallyRingedSpace =
        AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)
  noComparisonWithoutCommonAmbient_cert := rfl

/-- The selected structure datum is the canonical pair of actual ideal sheaves
on the affine spectrum. -/
theorem ofAffineSpec_selectedStructureSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair selectedComparisonProfile).selectedStructureSheaf =
        AffineIdealSheafPair.ofSpec leftIdeal rightIdeal :=
  rfl

/-- The selected scheme underlying the actual ideal-sheaf pair is `Spec R`. -/
theorem ofAffineSpec_selectedScheme
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair
      selectedComparisonProfile).selectedStructureSheaf.scheme =
        AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of R)) :=
  rfl

/-- The selected left ideal sheaf is induced from the left coordinate ideal. -/
theorem ofAffineSpec_leftIdealSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair
      selectedComparisonProfile).selectedStructureSheaf.leftIdealSheaf =
        AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
          (Ideal.map
            ((AlgebraicGeometry.Scheme.ΓSpecIso
              (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
            leftIdeal) :=
  rfl

/-- The selected right ideal sheaf is induced from the right coordinate ideal. -/
theorem ofAffineSpec_rightIdealSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair
      selectedComparisonProfile).selectedStructureSheaf.rightIdealSheaf =
        AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
          (Ideal.map
            ((AlgebraicGeometry.Scheme.ΓSpecIso
              (CommRingCat.of R)).commRingCatIsoToRingEquiv).symm.toRingHom
            rightIdeal) :=
  rfl

/-- The left selected ideal is the supplied ideal in the affine coordinate ring. -/
theorem ofAffineSpec_leftLawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair selectedComparisonProfile).leftLawIdeal =
        leftIdeal :=
  rfl

/-- The right selected ideal is the supplied ideal in the affine coordinate ring. -/
theorem ofAffineSpec_rightLawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair selectedComparisonProfile).rightLawIdeal =
        rightIdeal :=
  rfl

/-- Both selected ideals are transported from ideals of the affine scheme's
global section ring through Mathlib's canonical `ΓSpecIso`. -/
theorem ofAffineSpec_globalSectionsIdeals
    {M : MeasurementProfile.{u, v}}
    {R : Type (max u v)} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile SupportCarrier : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
      selectedWitnessPair selectedComparisonProfile).lawIdealsInCommonAmbient :=
  (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
    selectedCoefficient WitnessPair ComparisonProfile SupportCarrier
    selectedWitnessPair selectedComparisonProfile).lawIdealsInCommonAmbient_cert

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
