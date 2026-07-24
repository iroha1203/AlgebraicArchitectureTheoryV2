import Formal.AG.RepresentationAnalysis.RepairMarginDehn

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定義15.1: selected completeness spectrum for representation readings.

The constructors are labels for a chosen reading discipline.  They do not by
themselves prove that a family has the corresponding property.
-/
inductive CompletenessSpectrum where
  | reading
  | preserving
  | reflecting
  | conservative
  | faithful
  | complete_for_selected_purpose
  deriving DecidableEq, Repr

/--
VII.定義15.3: `U`-detecting representation family.

For a selected obstruction class `alpha`, if every selected representation
reading reports analytic zero, the family supplies the selected
`WitnessZero_U alpha` certificate.  The later theorem 15.4 is responsible for
turning `WitnessZero_U alpha` into equality with zero under explicit exactness
assumptions.
-/
structure UDetectingRepresentationFamily {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
    (F : RepresentationFamily p) where
  ObstructionClass : Type z
  analyticZeroReading : F.Index -> ObstructionClass -> Prop
  WitnessZero_U : ObstructionClass -> Prop
  detects :
    ∀ alpha : ObstructionClass,
      (∀ i : F.Index, analyticZeroReading i alpha) -> WitnessZero_U alpha
  completenessLevel : CompletenessSpectrum

namespace UDetectingRepresentationFamily

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}
variable {F : RepresentationFamily p}

/-- VII.定義15.3: apply the selected `U`-detecting certificate. -/
theorem witnessZero_of_all_readings_zero
    (D : UDetectingRepresentationFamily F)
    (alpha : D.ObstructionClass)
    (hzero : ∀ i : F.Index, D.analyticZeroReading i alpha) :
    D.WitnessZero_U alpha :=
  D.detects alpha hzero

/-- VII.定義15.3: expose the selected completeness-spectrum label. -/
def selectedCompletenessLevel
    (D : UDetectingRepresentationFamily F) :
    CompletenessSpectrum :=
  D.completenessLevel

end UDetectingRepresentationFamily

/--
VII.定義14.1: analytic reading context.

This context collects the selected vocabulary, site equation system, coverage
topology, coefficient sheaf, representation family, distance / obstruction
mass profile, witness family, and signature axes used by the Part VII reading
layer. It is a context object only: adequacy, exactness, and conservativity
theorems remain explicit assumptions in later results.
-/
structure AnalyticReadingContext {U : AtomCarrier.{u}} (Obj : ArchitectureObject U)
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (p : AATSchReadingParameter raw) where
  AtomVocabulary : Type u
  atomVocabularyOf : U.Atom -> AtomVocabulary
  CoverageTopology : Type w
  selectedCoverage : CoverageTopology
  coefficientSheaf : Type z
  representationFamily : RepresentationFamily p
  distanceMassContext : DistanceFlatnessMassContext Obj
  selectedWitnessFamily : Type z
  selectedWitness : selectedWitnessFamily
  selectedSignatureAxes : SignatureAxes U
  signatureProfile : SignatureReadingProfile selectedSignatureAxes
  detectingFamily : UDetectingRepresentationFamily representationFamily
  coverageAdequacy : Prop
  witnessExactness : Prop
  axisExactness : Prop
  coefficientDiscipline : Prop
  completenessLevel : CompletenessSpectrum

namespace AnalyticReadingContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}

/-- VII.定義14.1: expose the selected representation family. -/
def Rep (C : AnalyticReadingContext Obj p) :
    RepresentationFamily p :=
  C.representationFamily

/-- VII.定義14.1: expose the selected distance / obstruction-mass profile. -/
def distanceProfile (C : AnalyticReadingContext Obj p) :
    DistanceFlatnessMassContext Obj :=
  C.distanceMassContext

/-- VII.定義14.1: expose the selected signature axes. -/
def signatureAxes (C : AnalyticReadingContext Obj p) :
    SignatureAxes U :=
  C.selectedSignatureAxes

/-- VII.定義14.1: expose the selected `U`-detecting package. -/
def UDetecting (C : AnalyticReadingContext Obj p) :
    UDetectingRepresentationFamily C.representationFamily :=
  C.detectingFamily

/-- VII.定義14.1: package the four later adequacy/exactness assumptions. -/
def AdequacyDiscipline (C : AnalyticReadingContext Obj p) : Prop :=
  C.coverageAdequacy ∧ C.witnessExactness ∧ C.axisExactness ∧ C.coefficientDiscipline

/-- VII.定義14.1: expose coverage adequacy from the combined discipline. -/
theorem coverageAdequacy_holds
    (C : AnalyticReadingContext Obj p)
    (h : C.AdequacyDiscipline) :
    C.coverageAdequacy :=
  h.1

/-- VII.定義14.1: expose witness exactness from the combined discipline. -/
theorem witnessExactness_holds
    (C : AnalyticReadingContext Obj p)
    (h : C.AdequacyDiscipline) :
    C.witnessExactness :=
  h.2.1

/-- VII.定義14.1: expose axis exactness from the combined discipline. -/
theorem axisExactness_holds
    (C : AnalyticReadingContext Obj p)
    (h : C.AdequacyDiscipline) :
    C.axisExactness :=
  h.2.2.1

/-- VII.定義14.1: expose coefficient discipline from the combined discipline. -/
theorem coefficientDiscipline_holds
    (C : AnalyticReadingContext Obj p)
    (h : C.AdequacyDiscipline) :
    C.coefficientDiscipline :=
  h.2.2.2

/--
VII.定義15.3: use the context's selected `U`-detecting representation family.
-/
theorem witnessZero_of_all_readings_zero
    (C : AnalyticReadingContext Obj p)
    (alpha : C.detectingFamily.ObstructionClass)
    (hzero : ∀ i : C.representationFamily.Index,
      C.detectingFamily.analyticZeroReading i alpha) :
    C.detectingFamily.WitnessZero_U alpha :=
  C.detectingFamily.witnessZero_of_all_readings_zero alpha hzero

end AnalyticReadingContext

/--
VII.定理15.4: representation conservativity under explicit adequacy and
exactness assumptions.

The package is deliberately selected-obstruction-class scoped.  `U`-detecting
gives `WitnessZero_U alpha`; the conversion from that witness to `alpha =
zeroClass` is an explicit exactness assumption.
-/
structure RepresentationConservativityUnderAdequacy {U : AtomCarrier.{u}}
    {Obj : ArchitectureObject U}
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    {p : AATSchReadingParameter raw}
    (C : AnalyticReadingContext
      (S := S) (k := k) (raw := raw) Obj p) where
  zeroClass : C.detectingFamily.ObstructionClass
  IsZeroClass : C.detectingFamily.ObstructionClass -> Prop
  zeroClass_isZero : IsZeroClass zeroClass
  coverageAdequate : C.coverageAdequacy
  witnessExact : C.witnessExactness
  axisExact : C.axisExactness
  coefficientDisciplined : C.coefficientDiscipline
  witnessZero_eq_zero :
    ∀ alpha : C.detectingFamily.ObstructionClass,
      C.detectingFamily.WitnessZero_U alpha -> alpha = zeroClass

namespace RepresentationConservativityUnderAdequacy

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {p : AATSchReadingParameter raw}
variable {C : AnalyticReadingContext
  (S := S) (k := k) (raw := raw) Obj p}

/-- VII.定理15.4: expose the combined adequacy / exactness discipline. -/
theorem adequacyDiscipline
    (T : RepresentationConservativityUnderAdequacy C) :
    C.AdequacyDiscipline :=
  ⟨T.coverageAdequate, T.witnessExact, T.axisExact, T.coefficientDisciplined⟩

/--
VII.定理15.4: if all selected representation readings of `alpha` are zero,
then the selected obstruction class is the chosen zero class.
-/
theorem representation_conservativity_under_adequacy
    (T : RepresentationConservativityUnderAdequacy C)
    (alpha : C.detectingFamily.ObstructionClass)
    (hzero : ∀ i : C.representationFamily.Index,
      C.detectingFamily.analyticZeroReading i alpha) :
    alpha = T.zeroClass :=
  T.witnessZero_eq_zero alpha (C.witnessZero_of_all_readings_zero alpha hzero)

/-- VII.定理15.4: expose that the selected `zeroClass` is an actual zero class. -/
theorem zeroClass_isZero_holds
    (T : RepresentationConservativityUnderAdequacy C) :
    T.IsZeroClass T.zeroClass :=
  T.zeroClass_isZero

/--
VII.定理15.4: if all selected representation readings of `alpha` are zero,
then `alpha` is an actual zero obstruction class.
-/
theorem representation_zero_under_adequacy
    (T : RepresentationConservativityUnderAdequacy C)
    (alpha : C.detectingFamily.ObstructionClass)
    (hzero : ∀ i : C.representationFamily.Index,
      C.detectingFamily.analyticZeroReading i alpha) :
    T.IsZeroClass alpha := by
  rw [T.representation_conservativity_under_adequacy alpha hzero]
  exact T.zeroClass_isZero

end RepresentationConservativityUnderAdequacy

end RepresentationAnalysis
end AAT.AG
