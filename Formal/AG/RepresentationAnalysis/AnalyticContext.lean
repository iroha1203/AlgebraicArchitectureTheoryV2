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
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily.{u, v, w, x, y, z} p) where
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
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily.{u, v, w, x, y, z} p}

/-- VII.定義15.3: apply the selected `U`-detecting certificate. -/
theorem witnessZero_of_all_readings_zero
    (D : UDetectingRepresentationFamily.{u, v, w, x, y, z} F)
    (alpha : D.ObstructionClass)
    (hzero : ∀ i : F.Index, D.analyticZeroReading i alpha) :
    D.WitnessZero_U alpha :=
  D.detects alpha hzero

/-- VII.定義15.3: expose the selected completeness-spectrum label. -/
def selectedCompletenessLevel
    (D : UDetectingRepresentationFamily.{u, v, w, x, y, z} F) :
    CompletenessSpectrum :=
  D.completenessLevel

end UDetectingRepresentationFamily

/--
VII.定義14.1: analytic reading context.

This context collects the selected vocabulary, law universe, coverage topology,
coefficient sheaf, representation family, distance / obstruction mass profile,
witness family, and signature axes used by the Part VII reading layer.  It is a
context object only: adequacy, exactness, and conservativity theorems remain
explicit assumptions in later results.
-/
structure AnalyticReadingContext {U : AtomCarrier.{u}} (Obj : ArchitectureObject U)
    {S : Site.AATSite Obj} {k : Type v} [CommRing k]
    (p : AATSchReadingParameter.{u, v, w, x, y} S k) where
  AtomVocabulary : Type u
  atomVocabularyOf : U.Atom -> AtomVocabulary
  lawUniverse : LawUniverse U
  CoverageTopology : Type w
  selectedCoverage : CoverageTopology
  coefficientSheaf : Type z
  representationFamily : RepresentationFamily.{u, v, w, x, y, z} p
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
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義14.1: expose the selected representation family. -/
def Rep (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) :
    RepresentationFamily.{u, v, w, x, y, z} p :=
  C.representationFamily

/-- VII.定義14.1: expose the selected distance / obstruction-mass profile. -/
def distanceProfile (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) :
    DistanceFlatnessMassContext Obj :=
  C.distanceMassContext

/-- VII.定義14.1: expose the selected signature axes. -/
def signatureAxes (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) :
    SignatureAxes U :=
  C.selectedSignatureAxes

/-- VII.定義14.1: expose the selected `U`-detecting package. -/
def UDetecting (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) :
    UDetectingRepresentationFamily C.representationFamily :=
  C.detectingFamily

/-- VII.定義14.1: package the four later adequacy/exactness assumptions. -/
def AdequacyDiscipline (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) : Prop :=
  C.coverageAdequacy ∧ C.witnessExactness ∧ C.axisExactness ∧ C.coefficientDiscipline

/-- VII.定義14.1: expose coverage adequacy from the combined discipline. -/
theorem coverageAdequacy_holds
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p)
    (h : C.AdequacyDiscipline) :
    C.coverageAdequacy :=
  h.1

/-- VII.定義14.1: expose witness exactness from the combined discipline. -/
theorem witnessExactness_holds
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p)
    (h : C.AdequacyDiscipline) :
    C.witnessExactness :=
  h.2.1

/-- VII.定義14.1: expose axis exactness from the combined discipline. -/
theorem axisExactness_holds
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p)
    (h : C.AdequacyDiscipline) :
    C.axisExactness :=
  h.2.2.1

/-- VII.定義14.1: expose coefficient discipline from the combined discipline. -/
theorem coefficientDiscipline_holds
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p)
    (h : C.AdequacyDiscipline) :
    C.coefficientDiscipline :=
  h.2.2.2

/--
VII.定義15.3: use the context's selected `U`-detecting representation family.
-/
theorem witnessZero_of_all_readings_zero
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p)
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
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p) where
  zeroClass : C.detectingFamily.ObstructionClass
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
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {C : AnalyticReadingContext.{u, v, w, x, y, z} Obj p}

/-- VII.定理15.4: expose the combined adequacy / exactness discipline. -/
theorem adequacyDiscipline
    (T : RepresentationConservativityUnderAdequacy.{u, v, w, x, y, z} C) :
    C.AdequacyDiscipline :=
  ⟨T.coverageAdequate, T.witnessExact, T.axisExact, T.coefficientDisciplined⟩

/--
VII.定理15.4: if all selected representation readings of `alpha` are zero,
then the selected obstruction class is the chosen zero class.
-/
theorem representation_conservativity_under_adequacy
    (T : RepresentationConservativityUnderAdequacy.{u, v, w, x, y, z} C)
    (alpha : C.detectingFamily.ObstructionClass)
    (hzero : ∀ i : C.representationFamily.Index,
      C.detectingFamily.analyticZeroReading i alpha) :
    alpha = T.zeroClass :=
  T.witnessZero_eq_zero alpha (C.witnessZero_of_all_readings_zero alpha hzero)

end RepresentationConservativityUnderAdequacy

end RepresentationAnalysis
end AAT.AG
