import Formal.AG.RepresentationAnalysis.PeriodSeparation
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.Atom.LawfulnessZero
import Formal.AG.Cohomology.FlatnessCriterion
import Formal.AG.Derived.Intersection

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y

/--
VII.定義7.1: signature reading selected from Part I signature axes.

The profile is a reading interface: it exposes a target predicate for each
selected axis and records that the reading is exactly the Part I axis-zero
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
VII.定義7.1: required signature reading zero is exactly Part I
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

/-- VII.定義7.1: expose one selected Part I axis-zero certificate. -/
theorem selected_axis_zero
    (P : SignatureReadingProfile S) {Obj : ArchitectureObject U} {axis : S.Axis}
    (h : P.RequiredSignatureReadingZero Obj) (hselected : S.selected axis) :
    S.zero Obj axis :=
  (P.signatureReading_iff_axisZero Obj axis).mp
    (P.selected_axis_reading h hselected)

end SignatureReadingProfile

/--
VII.定義7.2: curvature reading as the selected Part I aggregate equation
obstruction valuation `omegaE`.

The value is a representation reading; zero is interpreted only through the
explicit zero-reflecting aggregation and correspondence assumptions supplied
to the theorems below.
-/
structure CurvatureReadingProfile
    {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex) where
  curvatureReading : ArchitectureObject U -> Value
  curvatureReading_eq_omegaE :
    ∀ Obj, curvatureReading Obj = omegaE valuation aggregation Obj

namespace CurvatureReadingProfile

variable {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A₀}
variable {E : ArchitecturalEquationSystem C} {Value : Type u}
variable {valuation : EquationObstructionValuation E Value}
variable {aggregation :
  ZeroReflectingAggregation Value valuation.domain E.RequiredIndex}

/-- VII.定義7.2: the canonical curvature profile induced by `omegaE`. -/
def ofOmegaE (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex) :
    CurvatureReadingProfile valuation aggregation where
  curvatureReading Obj := omegaE valuation aggregation Obj
  curvatureReading_eq_omegaE _Obj := rfl

/-- VII.定義7.2: zero curvature for the selected object. -/
def CurvatureZero (P : CurvatureReadingProfile valuation aggregation)
    (Obj : ArchitectureObject U) : Prop :=
  P.curvatureReading Obj = valuation.domain.zero

/-- VII.定義7.2: curvature zero is aggregate equation obstruction zero. -/
theorem curvatureZero_iff_omegaE_zero
    (P : CurvatureReadingProfile valuation aggregation)
    (Obj : ArchitectureObject U) :
    P.CurvatureZero Obj ↔
      omegaE valuation aggregation Obj = valuation.domain.zero := by
  unfold CurvatureZero
  rw [P.curvatureReading_eq_omegaE Obj]

/--
VII.定義7.2: zero curvature is zero on every selected required equation
obstruction valuation.
-/
theorem curvatureZero_iff_requiredObstructionValuesZero
    (P : CurvatureReadingProfile valuation aggregation)
    (Obj : ArchitectureObject U) :
    P.CurvatureZero Obj ↔
      ∀ index : E.RequiredIndex,
        valuation.omega index.1 Obj = valuation.domain.zero :=
  (P.curvatureZero_iff_omegaE_zero Obj).trans
    (omegaE_zero_iff_required valuation aggregation Obj)

end CurvatureReadingProfile

/--
VII.定義7.2: Part IV obstruction-class handle read by the curvature profile.

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

/-- VII.定義7.2: expose the selected Part IV obstruction class. -/
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
VII.定義7.2: Part V law-conflict handle read by the curvature profile.

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

/-- VII.定義7.2: selected law-conflict reading is backed by Part V Tor data. -/
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
VII.定義7.2: the selected curvature profile for one equation system and
valuation.

Implementation notes: this minimal context stores only the existing
`CurvatureReadingProfile`; Scheme, factorization, and signature premises are
kept in the comparison contexts that actually use them.
-/
structure CurvatureReadingContext
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    (E : ArchitecturalEquationSystem C) {Value : Type u}
    (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex) where
  curvatureProfile : CurvatureReadingProfile valuation aggregation

namespace CurvatureReadingContext

/-- Curvature zero in the selected profile is exactly aggregate obstruction zero. -/
theorem curvature_zero_iff_omegaE_zero
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    {valuation : EquationObstructionValuation E Value}
    {aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex}
    (K : CurvatureReadingContext E valuation aggregation)
    (Obj : ArchitectureObject U) :
    K.curvatureProfile.CurvatureZero Obj ↔
      omegaE valuation aggregation Obj = valuation.domain.zero :=
  K.curvatureProfile.curvatureZero_iff_omegaE_zero Obj

/-- Curvature zero is equivalent to vanishing of every required obstruction value. -/
theorem curvature_zero_iff_requiredObstructionValuesZero
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    {E : ArchitecturalEquationSystem C} {Value : Type u}
    {valuation : EquationObstructionValuation E Value}
    {aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex}
    (K : CurvatureReadingContext E valuation aggregation)
    (Obj : ArchitectureObject U) :
    K.curvatureProfile.CurvatureZero Obj ↔
      ∀ i : E.RequiredIndex,
        valuation.omega i.1 Obj = valuation.domain.zero :=
  K.curvatureProfile.curvatureZero_iff_requiredObstructionValuesZero Obj

end CurvatureReadingContext

/--
VII.定義7.2: comparison data from curvature to the selected signature axes.

Implementation notes: the context extends only the curvature profile and adds
the soundness, completeness, and axis-exactness premises used by its two
comparison theorems.
-/
structure CurvatureAxisComparisonContext
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    (Obj : ArchitectureObject U) (E : ArchitecturalEquationSystem C)
    (Sig : SignatureAxes U)
    {Value : Type u} (valuation : EquationObstructionValuation E Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex)
    extends CurvatureReadingContext E valuation aggregation where
  obstructionSoundness :
    ∀ i : E.RequiredIndex, EquationObstructionSound valuation i.1
  obstructionCompleteness :
    ∀ i : E.RequiredIndex, EquationObstructionComplete valuation i.1
  signatureComparison : EquationSignatureComparison E Sig

namespace CurvatureAxisComparisonContext

/-- Curvature zero is equivalent to vanishing of all required signature axes. -/
theorem curvature_zero_iff_requiredSignatureAxesZero
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    {Obj : ArchitectureObject U} {E : ArchitecturalEquationSystem C}
    {Sig : SignatureAxes U}
    {Value : Type u} {valuation : EquationObstructionValuation E Value}
    {aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex}
    (K : CurvatureAxisComparisonContext Obj E Sig valuation aggregation) :
    K.curvatureProfile.CurvatureZero Obj ↔
      RequiredSignatureAxesZero Obj Sig :=
  (K.curvatureProfile.curvatureZero_iff_omegaE_zero Obj).trans
    ((equationLawful_iff_omegaE_zero valuation aggregation
      K.obstructionSoundness K.obstructionCompleteness Obj).symm.trans
        (equationLawful_iff_requiredSignatureAxesZero
          K.signatureComparison Obj))

/-- Curvature zero is equivalent to the selected signature reading being zero. -/
theorem curvature_zero_iff_requiredSignatureReadingZero
    {A₀ : ArchitectureObject U} {C : Site.ContextPreorderCategory A₀}
    {Obj : ArchitectureObject U} {E : ArchitecturalEquationSystem C}
    {Sig : SignatureAxes U}
    {Value : Type u} {valuation : EquationObstructionValuation E Value}
    {aggregation :
      ZeroReflectingAggregation Value valuation.domain E.RequiredIndex}
    (K : CurvatureAxisComparisonContext Obj E Sig valuation aggregation)
    (signatureProfile : SignatureReadingProfile Sig) :
    K.curvatureProfile.CurvatureZero Obj ↔
      signatureProfile.RequiredSignatureReadingZero Obj :=
  K.curvature_zero_iff_requiredSignatureAxesZero.trans
    (signatureProfile.requiredSignatureReadingZero_iff_requiredSignatureAxesZero Obj).symm

end CurvatureAxisComparisonContext

variable {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]

/--
VII.定義7.2: comparison data between curvature and actual lawful factorization.

Implementation notes: the context reuses canonical closed-equational geometry
and stores only the object-point comparison and valuation hypotheses consumed
by the equation lawfulness and factorization comparison.
-/
structure CurvatureLawfulFactorizationContext
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X S.equationSystem)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    (hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) {Value : Type u}
    (valuation : EquationObstructionValuation S.equationSystem Value)
    (aggregation :
      ZeroReflectingAggregation Value valuation.domain
        S.equationSystem.RequiredIndex)
    extends CurvatureReadingContext S.equationSystem valuation aggregation where
  pointComparison : LawAlgebra.RequiredObjectPointComparison raw X R s Obj
  obstructionSoundness :
    ∀ i : S.equationSystem.RequiredIndex,
      EquationObstructionSound valuation i.1
  obstructionCompleteness :
    ∀ i : S.equationSystem.RequiredIndex,
      EquationObstructionComplete valuation i.1

/--
VII.定義7.2: comparison data between signature readings and actual lawful
factorization.

Implementation notes: the factorization target and closed geometry are
canonical parameters; the structure stores only the signature profile,
object-point comparison, and selected-axis exactness used by the theorem below.
-/
structure SignatureLawfulFactorizationContext
    (raw : LawAlgebra.RawAmbientRestrictionSystem S k)
    [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
    (X : LawAlgebra.StandardArchitectureScheme raw)
    (R : LawAlgebra.ClosedEquationalLawReading raw X S.equationSystem)
    (hR : LawAlgebra.IsClosedEquationalLawReading raw X R)
    (hclosed : LawAlgebra.RequiredClosed raw X R)
    (hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed)
    {T : AlgebraicGeometry.Scheme} (s : T ⟶ X.underlying)
    (Obj : ArchitectureObject U) (Sig : SignatureAxes U) where
  signatureProfile : SignatureReadingProfile Sig
  pointComparison : LawAlgebra.RequiredObjectPointComparison raw X R s Obj
  signatureComparison :
    EquationSignatureComparison S.equationSystem Sig

namespace CurvatureLawfulFactorizationContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X S.equationSystem}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}
variable {hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed}
variable {T : AlgebraicGeometry.Scheme} {s : T ⟶ X.underlying}
variable {Value : Type u}
variable {valuation : EquationObstructionValuation S.equationSystem Value}
variable {aggregation :
  ZeroReflectingAggregation Value valuation.domain S.equationSystem.RequiredIndex}

/-- Zero curvature produces an actual factorization through the lawful closed subscheme. -/
theorem factorsThroughLawfulClosedSubscheme_of_curvature_zero
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation)
    (hcurvature : C.curvatureProfile.CurvatureZero Obj) :
    Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme
      raw X R hR hclosed s) := by
  have hequation : S.equationSystem.EquationLawful Obj :=
    (equationLawful_iff_omegaE_zero valuation aggregation
      C.obstructionSoundness C.obstructionCompleteness Obj).mpr
      ((C.curvatureProfile.curvatureZero_iff_omegaE_zero Obj).mp hcurvature)
  have hsemantic : LawAlgebra.SemanticLawfulAlong raw X R s :=
    (LawAlgebra.semanticLawfulAlong_iff_lawfulness
      raw X R s Obj C.pointComparison).mpr hequation
  have hcorrespondence :=
    LawAlgebra.lawfulnessIdealFactorizationCorrespondence
      raw X R hR hclosed hexact s
  exact hcorrespondence.2.2.mp (hcorrespondence.2.1.mp
    (hcorrespondence.1.mp hsemantic))

/-- An actual lawful factorization forces zero curvature for the selected profile. -/
theorem curvature_zero_of_factorsThroughLawfulClosedSubscheme
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation)
    (hfactor : Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme
      raw X R hR hclosed s)) :
    C.curvatureProfile.CurvatureZero Obj := by
  have hcorrespondence :=
    LawAlgebra.lawfulnessIdealFactorizationCorrespondence
      raw X R hR hclosed hexact s
  have hsemantic : LawAlgebra.SemanticLawfulAlong raw X R s :=
    hcorrespondence.1.mpr (hcorrespondence.2.1.mpr
      (hcorrespondence.2.2.mpr hfactor))
  have hequation : S.equationSystem.EquationLawful Obj :=
    (LawAlgebra.semanticLawfulAlong_iff_lawfulness
      raw X R s Obj C.pointComparison).mp hsemantic
  apply (C.curvatureProfile.curvatureZero_iff_omegaE_zero Obj).mpr
  exact (equationLawful_iff_omegaE_zero valuation aggregation
    C.obstructionSoundness C.obstructionCompleteness Obj).mp hequation

/-- Zero curvature is equivalent to actual factorization through lawful geometry. -/
theorem curvature_zero_iff_factorsThroughLawfulClosedSubscheme
    (C : CurvatureLawfulFactorizationContext raw X R hR hclosed hexact
      s Obj valuation aggregation) :
    C.curvatureProfile.CurvatureZero Obj ↔
      Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme
        raw X R hR hclosed s) :=
  ⟨C.factorsThroughLawfulClosedSubscheme_of_curvature_zero,
    C.curvature_zero_of_factorsThroughLawfulClosedSubscheme⟩

end CurvatureLawfulFactorizationContext

namespace SignatureLawfulFactorizationContext

variable {U : AtomCarrier.{u}} {Obj : ArchitectureObject U}
variable {S : Site.AATSite Obj} {k : Type v} [CommRing k]
variable {raw : LawAlgebra.RawAmbientRestrictionSystem S k}
variable [CategoryTheory.HasSheafify S.topology (LawAlgebra.AATCommAlgCat k)]
variable {X : LawAlgebra.StandardArchitectureScheme raw}
variable {R : LawAlgebra.ClosedEquationalLawReading raw X S.equationSystem}
variable {hR : LawAlgebra.IsClosedEquationalLawReading raw X R}
variable {hclosed : LawAlgebra.RequiredClosed raw X R}
variable {hexact : LawAlgebra.RequiredLawIdealExact raw X R hR hclosed}
variable {T : AlgebraicGeometry.Scheme} {s : T ⟶ X.underlying}
variable {Sig : SignatureAxes U}

/-- A zero required-signature reading produces an actual lawful factorization. -/
theorem factorsThroughLawfulClosedSubscheme_of_requiredSignatureReadingZero
    (C : SignatureLawfulFactorizationContext raw X R hR hclosed hexact s Obj Sig)
    (hsig : C.signatureProfile.RequiredSignatureReadingZero Obj) :
    Nonempty (LawAlgebra.FactorsThroughLawfulClosedSubscheme
      raw X R hR hclosed s) :=
  (LawAlgebra.factorsThroughLawfulClosedSubscheme_iff_requiredSignatureAxesZero
    raw X R hR hclosed hexact s Obj Sig C.pointComparison
      (equationLawful_iff_requiredSignatureAxesZero
        C.signatureComparison Obj)).mpr
      ((C.signatureProfile.requiredSignatureReadingZero_iff_requiredSignatureAxesZero
        Obj).mp hsig)

end SignatureLawfulFactorizationContext

end RepresentationAnalysis
end AAT.AG
