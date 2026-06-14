import Formal.AG.RepresentationAnalysis.PeriodSeparation
import Formal.AG.LawAlgebra.Correspondence
import Formal.AG.Cohomology.FlatnessCriterion
import Formal.AG.Derived.Intersection

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y

/--
VII.定義7.1: signature reading selected from PRD-1 signature axes.

The profile is a reading interface: it exposes a target predicate for each
selected axis and records that the reading is exactly the PRD-1 axis-zero
predicate.  It does not add new axes or infer unselected axes.
-/
structure SignatureReadingProfile {U : AtomCarrier.{u}} (S : SignatureAxes U) where
  signatureReading : ArchitectureObject U -> S.Axis -> Prop
  signatureReading_iff_axisZero :
    ∀ Obj axis, signatureReading Obj axis ↔ S.zero Obj axis

namespace SignatureReadingProfile

variable {U : AtomCarrier.{u}} {S : SignatureAxes U}

/-- VII.定義7.1: the canonical reading profile induced by selected axes. -/
def ofSignatureAxes (S : SignatureAxes U) : SignatureReadingProfile S where
  signatureReading Obj axis := S.zero Obj axis
  signatureReading_iff_axisZero _Obj _axis := Iff.rfl

/-- VII.定義7.1: all selected signature readings vanish. -/
def RequiredSignatureReadingZero (P : SignatureReadingProfile S)
    (Obj : ArchitectureObject U) : Prop :=
  ∀ axis : S.Axis, S.selected axis -> P.signatureReading Obj axis

/--
VII.定義7.1: required signature reading zero is exactly PRD-1
`RequiredSignatureAxesZero`.
-/
theorem requiredSignatureReadingZero_iff_requiredSignatureAxesZero
    (P : SignatureReadingProfile S) (Obj : ArchitectureObject U) :
    P.RequiredSignatureReadingZero Obj ↔ RequiredSignatureAxesZero Obj S := by
  constructor
  · intro h axis hselected
    exact (P.signatureReading_iff_axisZero Obj axis).mp (h axis hselected)
  · intro h axis hselected
    exact (P.signatureReading_iff_axisZero Obj axis).mpr (h axis hselected)

/-- VII.定義7.1: expose one selected signature-axis reading. -/
theorem selected_axis_reading
    (P : SignatureReadingProfile S) {Obj : ArchitectureObject U} {axis : S.Axis}
    (h : P.RequiredSignatureReadingZero Obj) (hselected : S.selected axis) :
    P.signatureReading Obj axis :=
  h axis hselected

/-- VII.定義7.1: expose one selected PRD-1 axis-zero certificate. -/
theorem selected_axis_zero
    (P : SignatureReadingProfile S) {Obj : ArchitectureObject U} {axis : S.Axis}
    (h : P.RequiredSignatureReadingZero Obj) (hselected : S.selected axis) :
    S.zero Obj axis :=
  (P.signatureReading_iff_axisZero Obj axis).mp
    (P.selected_axis_reading h hselected)

end SignatureReadingProfile

/--
VII.定義7.2: curvature reading as the selected PRD-1 aggregate obstruction
valuation `omega_U`.

The value is a representation reading; zero is interpreted only through the
explicit zero-reflecting aggregation and correspondence assumptions supplied to
the theorems below.
-/
structure CurvatureReadingProfile {U : AtomCarrier.{u}} {Value : Type u}
    (LU : LawUniverse U) (valuation : ObstructionValuation U Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex) where
  curvatureReading : ArchitectureObject U -> Value
  curvatureReading_eq_omegaU :
    ∀ Obj, curvatureReading Obj = omegaU valuation LU aggregation Obj

namespace CurvatureReadingProfile

variable {U : AtomCarrier.{u}} {Value : Type u}
variable {LU : LawUniverse U} {valuation : ObstructionValuation U Value}
variable {aggregation :
  ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}

/-- VII.定義7.2: the canonical curvature profile induced by `omega_U`. -/
def ofOmegaU (LU : LawUniverse U) (valuation : ObstructionValuation U Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex) :
    CurvatureReadingProfile LU valuation aggregation where
  curvatureReading Obj := omegaU valuation LU aggregation Obj
  curvatureReading_eq_omegaU _Obj := rfl

/-- VII.定義7.2: zero curvature for the selected object. -/
def CurvatureZero (P : CurvatureReadingProfile LU valuation aggregation)
    (Obj : ArchitectureObject U) : Prop :=
  P.curvatureReading Obj = valuation.domain.zero

/-- VII.定義7.2: curvature zero is aggregate obstruction valuation zero. -/
theorem curvatureZero_iff_omegaU_zero
    (P : CurvatureReadingProfile LU valuation aggregation)
    (Obj : ArchitectureObject U) :
    P.CurvatureZero Obj ↔
      omegaU valuation LU aggregation Obj = valuation.domain.zero := by
  unfold CurvatureZero
  rw [P.curvatureReading_eq_omegaU Obj]

/--
VII.定義7.2: zero curvature is zero on every selected required obstruction
valuation.
-/
theorem curvatureZero_iff_requiredObstructionValuesZero
    (P : CurvatureReadingProfile LU valuation aggregation)
    (Obj : ArchitectureObject U) :
    P.CurvatureZero Obj ↔
      ∀ index : LU.RequiredIndex,
        valuation.omega (LU.law index.1) Obj = valuation.domain.zero :=
  (P.curvatureZero_iff_omegaU_zero Obj).trans
    (omegaU_zero_iff_required valuation LU aggregation Obj)

end CurvatureReadingProfile

/--
VII.定義7.2: PRD-4 obstruction-class handle read by the curvature profile.

This is a selected bridge to the already formalized
`Cohomology.GluingObstructionClass`; it does not construct a new general
cohomology comparison theorem.
-/
structure GluingObstructionCurvatureReading {U : AtomCarrier.{u}}
    {Obj : ArchitectureObject U} {S : Site.AATSite Obj}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob) where
  gluingClass : Cohomology.GluingObstructionClass K
  curvatureReadsObstructionClass : Prop
  curvatureReadsObstructionClass_holds : curvatureReadsObstructionClass

namespace GluingObstructionCurvatureReading

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}

/-- VII.定義7.2: expose the selected PRD-4 obstruction class. -/
def h1Class (G : GluingObstructionCurvatureReading K) :
    K.CoverRelativeHn 1 :=
  G.gluingClass.h1Class

/-- VII.定義7.2: the selected obstruction-class reading certificate. -/
theorem curvatureReadsObstructionClass_certificate
    (G : GluingObstructionCurvatureReading K) :
    G.curvatureReadsObstructionClass :=
  G.curvatureReadsObstructionClass_holds

end GluingObstructionCurvatureReading

/--
VII.定義7.2: PRD-5 law-conflict handle read by the curvature profile.

The selected degree is a bounded reading of an existing
`Derived.Intersection.LawConflictPackage`, not a new Tor computation.
-/
structure LawConflictCurvatureReading (A : Type v) [CommRing A]
    {I_U I_V : Ideal A}
    (P : Derived.Intersection.LawConflictPackage.{u, v} A I_U I_V) where
  selectedDegree : Nat
  curvatureReadsLawConflict : Prop
  curvatureReadsLawConflict_holds : curvatureReadsLawConflict

namespace LawConflictCurvatureReading

variable {A : Type v} [CommRing A]
variable {I_U I_V : Ideal A}
variable {P : Derived.Intersection.LawConflictPackage.{u, v} A I_U I_V}

/-- VII.定義7.2: selected law-conflict carrier read by curvature. -/
abbrev selectedLawConflict (C : LawConflictCurvatureReading A P) : Type v :=
  P.LawConflict C.selectedDegree

/-- VII.定義7.2: selected law-conflict reading is backed by PRD-5 Tor data. -/
theorem selectedLawConflict_eq_tor (C : LawConflictCurvatureReading A P) :
    C.selectedLawConflict = P.torBridge.Tor C.selectedDegree :=
  Derived.Intersection.LawConflictPackage.lawConflict_eq_tor P C.selectedDegree

/-- VII.定義7.2: the selected law-conflict reading certificate. -/
theorem curvatureReadsLawConflict_certificate
    (C : LawConflictCurvatureReading A P) :
    C.curvatureReadsLawConflict :=
  C.curvatureReadsLawConflict_holds

end LawConflictCurvatureReading

/--
VII.定義7.2: signature / curvature context for the zero-curvature to lawful
factorization theorems.

The correspondence assumptions are exactly the PRD-3 theorem arguments:
soundness, completeness, coverage, axis exactness, witness exactness, descent,
and ring-restriction compatibility.  The PRD-4 and PRD-5 reading connections
are explicit selected certificates, not inferred global claims.
-/
structure SignatureCurvatureLawfulFactorizationContext
    {U : AtomCarrier.{u}} {R : Type v} [CommRing R] {IOb : Ideal R}
    (s : LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} R IOb)
    (Obj : ArchitectureObject U) (LU : LawUniverse U) (Sig : SignatureAxes U)
    {Value : Type u} (valuation : ObstructionValuation U Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex) where
  signatureProfile : SignatureReadingProfile Sig
  curvatureProfile : CurvatureReadingProfile LU valuation aggregation
  correspondence :
    LawAlgebra.Correspondence.LawfulnessIdealCorrespondenceAssumptions
      s Obj LU Sig valuation
  obstructionClassReading : Prop
  obstructionClassReading_holds : obstructionClassReading
  lawConflictReading : Prop
  lawConflictReading_holds : lawConflictReading

namespace SignatureCurvatureLawfulFactorizationContext

variable {U : AtomCarrier.{u}} {R : Type v} [CommRing R] {IOb : Ideal R}
variable {s : LawAlgebra.LawfulLocus.LawfulSectionData.{v, w} R IOb}
variable {Obj : ArchitectureObject U} {LU : LawUniverse U}
variable {Sig : SignatureAxes U}
variable {Value : Type u} {valuation : ObstructionValuation U Value}
variable {aggregation :
  ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex}

/-- VII.定義7.2: expose the selected PRD-4 obstruction-class bridge. -/
theorem obstructionClassReading_certificate
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.obstructionClassReading :=
  C.obstructionClassReading_holds

/-- VII.定義7.2: expose the selected PRD-5 law-conflict bridge. -/
theorem lawConflictReading_certificate
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.lawConflictReading :=
  C.lawConflictReading_holds

/-- VII.定義7.2: zero curvature is selected aggregate obstruction zero. -/
theorem curvature_zero_iff_omegaU_zero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      omegaU valuation LU aggregation Obj = valuation.domain.zero :=
  C.curvatureProfile.curvatureZero_iff_omegaU_zero Obj

/--
VII.定義7.2: zero curvature is zero on every selected required obstruction
valuation.
-/
theorem curvature_zero_iff_requiredObstructionValuesZero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      ∀ index : LU.RequiredIndex,
        valuation.omega (LU.law index.1) Obj = valuation.domain.zero :=
  C.curvatureProfile.curvatureZero_iff_requiredObstructionValuesZero Obj

/-- VII.定義7.2: zero curvature is PRD-1 required signature axes zero. -/
theorem curvature_zero_iff_requiredSignatureAxesZero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔ RequiredSignatureAxesZero Obj Sig :=
  (C.curvature_zero_iff_omegaU_zero).trans
    (LawAlgebra.Correspondence.omegaU_zero_iff_requiredSignatureAxesZero
      s Obj LU Sig valuation aggregation C.correspondence)

/-- VII.定義7.1 / 7.2: zero curvature is selected signature reading zero. -/
theorem curvature_zero_iff_requiredSignatureReadingZero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      C.signatureProfile.RequiredSignatureReadingZero Obj :=
  (C.curvature_zero_iff_requiredSignatureAxesZero).trans
    (C.signatureProfile.requiredSignatureReadingZero_iff_requiredSignatureAxesZero Obj).symm

/--
VII.定義7.2: zero curvature gives factorization through the selected lawful
locus `Flat_U`.
-/
theorem factorsThroughLawfulLocus_of_curvature_zero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation)
    (hcurvature : C.curvatureProfile.CurvatureZero Obj) :
    s.FactorsThroughLawfulLocus :=
  (LawAlgebra.Correspondence.factorsThroughLawfulLocus_iff_omegaU_zero
    s Obj LU Sig valuation aggregation C.correspondence).mpr
      ((C.curvature_zero_iff_omegaU_zero).mp hcurvature)

/--
VII.定義7.2: under the same correspondence package, lawful factorization
preserves zero curvature.
-/
theorem curvature_zero_of_factorsThroughLawfulLocus
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation)
    (hfactor : s.FactorsThroughLawfulLocus) :
    C.curvatureProfile.CurvatureZero Obj :=
  (C.curvature_zero_iff_omegaU_zero).mpr
    ((LawAlgebra.Correspondence.factorsThroughLawfulLocus_iff_omegaU_zero
      s Obj LU Sig valuation aggregation C.correspondence).mp hfactor)

/--
VII.定義7.2: zero curvature and lawful factorization are equivalent under the
explicit PRD-3 correspondence assumptions.
-/
theorem curvature_zero_iff_factorsThroughLawfulLocus
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔ s.FactorsThroughLawfulLocus :=
  ⟨C.factorsThroughLawfulLocus_of_curvature_zero,
    C.curvature_zero_of_factorsThroughLawfulLocus⟩

/--
VII.定義7.2: zero selected signature reading gives lawful factorization under
axis exactness and the correspondence package.
-/
theorem factorsThroughLawfulLocus_of_requiredSignatureReadingZero
    (C : SignatureCurvatureLawfulFactorizationContext
      s Obj LU Sig valuation aggregation)
    (hsig : C.signatureProfile.RequiredSignatureReadingZero Obj) :
    s.FactorsThroughLawfulLocus :=
  C.factorsThroughLawfulLocus_of_curvature_zero
    ((C.curvature_zero_iff_requiredSignatureReadingZero).mpr hsig)

end SignatureCurvatureLawfulFactorizationContext

end RepresentationAnalysis
end AAT.AG
