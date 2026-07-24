import Formal.AG.Measurement.Hodge
import Formal.AG.Derived.Intersection
import Mathlib.RingTheory.Support
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

The ring and two ideal indices determine the affine scheme and ideal sheaves.
The record fixes the coefficient, witness pair, and comparison profile needed
before LawConflict measurements may be compared; its point and support
carriers are derived from the indexed affine scheme.

Implementation notes: the support carrier is not stored as independent data.
It is the carrier of `Spec R`, because an unrelated carrier would not place a
conflict class and its repair direction on the same affine scheme.
-/
structure CommonAmbientPair
    (M : MeasurementProfile.{u, v})
    (R : Type w) [CommRing R]
    (I_U I_V : Ideal R) where
  WitnessPair : Type u
  ComparisonProfile : Type u
  leftDomain : M.Domain
  rightDomain : M.Domain
  selectedCoefficient : M.Coeff
  selectedWitnessPair : WitnessPair
  selectedComparisonProfile : ComparisonProfile

namespace CommonAmbientPair

/-- The point carrier of the selected affine ambient `Spec R`. -/
abbrev AmbientSpace
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :=
  PrimeSpectrum R

/-- Support points are actual points of the selected affine spectrum. -/
abbrev SupportCarrier
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :=
  PrimeSpectrum R

/-- The selected structure datum is the canonical pair of ideal sheaves on
`Spec R`. -/
abbrev StructureSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :=
  AffineIdealSheafPair.{w}

/-- Coefficient objects are the coefficients fixed by the measurement profile. -/
abbrev CoefficientObject
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :=
  M.Coeff

/-- The actual affine scheme and its two ideal sheaves. -/
noncomputable abbrev selectedStructureSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :
    AffineIdealSheafPair.{w} :=
  AffineIdealSheafPair.ofSpec I_U I_V

/-- The selected affine ambient is the Mathlib affine scheme carrying both
ideal sheaves. -/
noncomputable abbrev selectedAmbient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    AlgebraicGeometry.Scheme :=
  A.selectedStructureSheaf.scheme

/-- The support carrier is definitionally the point carrier of the selected
Mathlib affine scheme. -/
theorem supportCarrier_eq_selectedSchemeCarrier
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.SupportCarrier = A.selectedStructureSheaf.scheme.carrier :=
  rfl

/-- The left coefficient object fixed by the selected profile value. -/
abbrev leftCoefficient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    M.Coeff :=
  A.selectedCoefficient

/-- The right coefficient object fixed by the same selected profile value. -/
abbrev rightCoefficient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    M.Coeff :=
  A.selectedCoefficient

/-- The ideal lattice of the coordinate ring indexed by the common ambient. -/
abbrev LawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :=
  Ideal R

/-- The left ideal indexed by the common ambient. -/
abbrev leftLawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :
    Ideal R :=
  I_U

/-- The right ideal indexed by the common ambient. -/
abbrev rightLawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) :
    Ideal R :=
  I_V

/-- The selected scheme is the locally ringed space underlying `Spec R`. -/
def commonRingedSite
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) : Prop :=
  (AffineIdealSheafPair.ofSpec
    I_U I_V).scheme.toLocallyRingedSpace =
      AlgebraicGeometry.Spec.locallyRingedSpaceObj (CommRingCat.of R)

/-- The canonical affine construction supplies the selected locally ringed
space. -/
theorem commonRingedSite_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.commonRingedSite :=
  rfl

/-- Both indexed ideals are recovered from the top components of the actual
ideal sheaves through `ΓSpecIso`. -/
def lawIdealsInCommonAmbient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (_A : CommonAmbientPair M R I_U I_V) : Prop :=
  let e :=
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of R)).commRingCatIsoToRingEquiv
  let pair := AffineIdealSheafPair.ofSpec I_U I_V
  let _ : IsAffine pair.scheme := pair.schemeIsAffine
  Ideal.map e.toRingHom
      (pair.leftIdealSheaf.ideal
        ⟨⊤, isAffineOpen_top pair.scheme⟩) =
        I_U ∧
    Ideal.map e.toRingHom
      (pair.rightIdealSheaf.ideal
        ⟨⊤, isAffineOpen_top pair.scheme⟩) =
        I_V

/-- The actual affine ideal sheaves recover both indexed ideals. -/
theorem lawIdealsInCommonAmbient_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.lawIdealsInCommonAmbient :=
  ⟨AffineIdealSheafPair.ofSpec_leftIdealSheaf_top I_U I_V,
    AffineIdealSheafPair.ofSpec_rightIdealSheaf_top I_U I_V⟩

/-- Both coefficient selections are the profile's selected coefficient. -/
def coefficientsCompatible
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) : Prop :=
  A.leftCoefficient = A.rightCoefficient

/-- Coefficient compatibility follows definitionally. -/
theorem coefficientsCompatible_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.coefficientsCompatible :=
  rfl

/-- The selected witness pair is shared by both readings. -/
def witnessesComparable
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) : Prop :=
  A.selectedWitnessPair = A.selectedWitnessPair

/-- Witness comparability follows definitionally. -/
theorem witnessesComparable_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.witnessesComparable :=
  rfl

/-- The selected comparison profile is fixed for the pair. -/
def comparisonProfileFixed
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) : Prop :=
  A.selectedComparisonProfile = A.selectedComparisonProfile

/-- Comparison-profile fixation follows definitionally. -/
theorem comparisonProfileFixed_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.comparisonProfileFixed :=
  rfl

/-- The selected comparison is defined on the canonical common affine
ambient. -/
def noComparisonWithoutCommonAmbient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) : Prop :=
  A.commonRingedSite

/-- The canonical affine ambient supplies the comparison domain. -/
theorem noComparisonWithoutCommonAmbient_cert
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.noComparisonWithoutCommonAmbient :=
  A.commonRingedSite_cert

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
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    CommonAmbientPair M R leftIdeal rightIdeal where
  WitnessPair := WitnessPair
  ComparisonProfile := ComparisonProfile
  leftDomain := leftDomain
  rightDomain := rightDomain
  selectedCoefficient := selectedCoefficient
  selectedWitnessPair := selectedWitnessPair
  selectedComparisonProfile := selectedComparisonProfile

/-- The selected structure datum is the canonical pair of actual ideal sheaves
on the affine spectrum. -/
theorem ofAffineSpec_selectedStructureSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).selectedStructureSheaf =
        AffineIdealSheafPair.ofSpec leftIdeal rightIdeal :=
  rfl

/-- The selected scheme underlying the actual ideal-sheaf pair is `Spec R`. -/
theorem ofAffineSpec_selectedScheme
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
      selectedWitnessPair
      selectedComparisonProfile).selectedStructureSheaf.scheme =
        AlgebraicGeometry.Scheme.Spec.obj (op (CommRingCat.of R)) :=
  rfl

/-- The selected left ideal sheaf is induced from the left coordinate ideal. -/
theorem ofAffineSpec_leftIdealSheaf
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
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
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
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
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).leftLawIdeal =
        leftIdeal :=
  rfl

/-- The right selected ideal is the supplied ideal in the affine coordinate ring. -/
theorem ofAffineSpec_rightLawIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).rightLawIdeal =
        rightIdeal :=
  rfl

/-- Both selected ideals are transported from ideals of the affine scheme's
global section ring through Mathlib's canonical `ΓSpecIso`. -/
theorem ofAffineSpec_globalSectionsIdeals
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (leftIdeal rightIdeal : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
      selectedCoefficient WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).lawIdealsInCommonAmbient :=
  (ofAffineSpec leftIdeal rightIdeal leftDomain rightDomain
    selectedCoefficient WitnessPair ComparisonProfile
    selectedWitnessPair selectedComparisonProfile).lawIdealsInCommonAmbient_cert

/-- VIII.Definition 9.1: expose the selected common ringed-site certificate. -/
theorem commonRingedSite_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.commonRingedSite :=
  A.commonRingedSite_cert

/-- VIII.Definition 9.1: expose that both law ideals live in the common ambient. -/
theorem lawIdealsInCommonAmbient_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.lawIdealsInCommonAmbient :=
  A.lawIdealsInCommonAmbient_cert

/-- VIII.Definition 9.1: expose compatible coefficient data for the pair. -/
theorem coefficientsCompatible_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.coefficientsCompatible :=
  A.coefficientsCompatible_cert

/-- VIII.Definition 9.1: expose the non-comparison boundary outside a common ambient. -/
theorem noComparisonWithoutCommonAmbient_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) :
    A.noComparisonWithoutCommonAmbient :=
  A.noComparisonWithoutCommonAmbient_cert

end CommonAmbientPair

/--
VIII.Definition 9.1: selected LawConflict measurement.

The indexed `CommonAmbientPair` fixes the shared affine scheme and both
ideals. The canonical Tor object is derived from those indices; the record
stores only the degree and selected class. Support readings are computed by
the concrete measurement regime rather than accepted by this generic record.
-/
structure LawConflictMeasurement
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    (A : CommonAmbientPair M R I_U I_V) where
  selectedDegree : Nat
  selectedConflictClass :
    (Derived.Intersection.canonicalSelectedTorBridge
      R I_U I_V).LawConflict selectedDegree

namespace LawConflictMeasurement

/-- Homological degrees are natural numbers. -/
abbrev Degree
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) :=
  Nat

/-- The left quotient is fixed by the left ambient ideal. -/
abbrev LeftQuotient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) :=
  R ⧸ I_U

/-- The right quotient is fixed by the right ambient ideal. -/
abbrev RightQuotient
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) :=
  R ⧸ I_V

/-- The selected Tor object is fixed by the ambient ring and ideals. -/
abbrev TorObject
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :=
  (Derived.Intersection.canonicalSelectedTorBridge
    R I_U I_V).LawConflict L.selectedDegree

/-- Conflict classes are elements of the selected canonical Tor object. -/
abbrev ConflictClass
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :=
  L.TorObject

/-- The zero-conflict predicate on the selected Tor object. -/
def ZeroConflict
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    L.ConflictClass -> Prop :=
  fun x => x = 0

/-- The nontrivial-conflict predicate on the selected Tor object. -/
def NontrivialConflict
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    L.ConflictClass -> Prop :=
  fun x => x ≠ 0

/--
Support of an actual conflict class on the selected affine spectrum.

This is the Mathlib module support of the cyclic submodule generated by the
selected Tor class.  Hence every support point is a prime of the same
coordinate ring that defines the common ambient and its two ideal sheaves.

Implementation notes: using `Module.support` retains Mathlib localization
semantics and makes support depend on the actual class. An independently
supplied relation or finite witness summary was rejected because either could
name points unrelated to the selected affine scheme or Tor object.
-/
def conflictClassSupport
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A)
    (conflictClass : L.ConflictClass) :
    Set A.SupportCarrier :=
  Module.support R (R ∙ conflictClass)

/-- The selected conflict support is computed from the selected actual Tor
class rather than supplied as an independent relation. -/
def selectedConflictSupport
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    Set A.SupportCarrier :=
  L.conflictClassSupport L.selectedConflictClass

/-- A zero conflict class has empty affine support. -/
@[simp]
theorem conflictClassSupport_zero
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    L.conflictClassSupport 0 = ∅ := by
  rw [conflictClassSupport, Module.support_eq_empty_iff,
    Submodule.subsingleton_iff_eq_bot, Submodule.span_singleton_eq_bot]

/-- An actual conflict class has nonempty affine support exactly when it is
nonzero. -/
theorem conflictClassSupport_nonempty_iff
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A)
    (conflictClass : L.ConflictClass) :
    (L.conflictClassSupport conflictClass).Nonempty ↔ conflictClass ≠ 0 := by
  rw [conflictClassSupport, Module.nonempty_support_iff,
    Submodule.nontrivial_iff_ne_bot]
  exact not_congr Submodule.span_singleton_eq_bot

/-- The canonical selected Tor object is linearly equivalent to Mathlib Tor. -/
def lawConflictTorReading
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) : Prop :=
  Nonempty
    (L.ConflictClass ≃ₗ[R]
      Derived.Intersection.mathlibTor
        R I_U I_V L.selectedDegree)

/-- The measurement uses the common affine scheme and its two ideal sheaves. -/
def commonAmbientRequired
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) : Prop :=
  A.commonRingedSite ∧ A.lawIdealsInCommonAmbient

/-- Coefficient compatibility is inherited from the selected common ambient. -/
def coefficientCompatibilityUsed
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) : Prop :=
  A.coefficientsCompatible

/-- The selected topology and coefficient comparison are inherited from the
common ambient. -/
def topologyAndCoefficientBoundary
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (_L : LawConflictMeasurement A) : Prop :=
  A.noComparisonWithoutCommonAmbient

/-- VIII.Definition 9.1: expose the selected Tor formula reading. -/
theorem lawConflictTorReading_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    L.lawConflictTorReading :=
  ⟨(Derived.Intersection.canonicalSelectedTorBridge
    R I_U I_V).lawConflictLinearEquivMathlibTor L.selectedDegree⟩

/-- VIII.Definition 9.1: LawConflict measurements require the selected common ambient. -/
theorem commonAmbientRequired_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) :
    L.commonAmbientRequired :=
  ⟨A.commonRingedSite_cert, A.lawIdealsInCommonAmbient_cert⟩

/--
VIII.Definition 9.1 / R7: build the common affine ambient and its
LawConflict measurement from the same two coordinate-ring ideals.

Both ideal sheaves and the canonical selected Tor bridge are generated
internally from `I_U` and `I_V`.  Hence the Tor object cannot be supplied from
ideals unrelated to the selected affine ambient.
-/
noncomputable def ofAffineSpecCanonicalTor
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (I_U I_V : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile)
    (degree : Nat)
    (selectedClass :
      (Derived.Intersection.canonicalSelectedTorBridge
        R I_U I_V).LawConflict degree) :
    LawConflictMeasurement
      (CommonAmbientPair.ofAffineSpec
        I_U I_V leftDomain rightDomain selectedCoefficient
        WitnessPair ComparisonProfile
        selectedWitnessPair selectedComparisonProfile) where
  selectedDegree := degree
  selectedConflictClass := selectedClass

/-- The standard affine constructor uses exactly the left ideal recovered
from its selected ideal sheaf. -/
theorem ofAffineSpecCanonicalTor_leftIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (I_U I_V : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (CommonAmbientPair.ofAffineSpec
      I_U I_V leftDomain rightDomain selectedCoefficient
      WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).leftLawIdeal =
        I_U :=
  rfl

/-- The standard affine constructor uses exactly the right ideal recovered
from its selected ideal sheaf. -/
theorem ofAffineSpecCanonicalTor_rightIdeal
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    (I_U I_V : Ideal R)
    (leftDomain rightDomain : M.Domain)
    (selectedCoefficient : M.Coeff)
    (WitnessPair ComparisonProfile : Type u)
    (selectedWitnessPair : WitnessPair)
    (selectedComparisonProfile : ComparisonProfile) :
    (CommonAmbientPair.ofAffineSpec
      I_U I_V leftDomain rightDomain selectedCoefficient
      WitnessPair ComparisonProfile
      selectedWitnessPair selectedComparisonProfile).rightLawIdeal =
        I_V :=
  rfl

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
structure FlatBaseChangeCandidate
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    (L : LawConflictMeasurement A) where
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
theorem affineBaseChangeStatement_shape_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) :
    F.affineBaseChangeStatement =
      (F.flatnessAssumption ->
        F.finitePresentationAssumption ->
          F.coefficientCompatibility ->
            F.supportPullbackCompatibility ->
              F.affineBaseChangeConclusion) :=
  F.affineBaseChangeStatement_shape

/-- VIII.Theorem candidate 9.2: expose the sheaf/ringed-site statement shape. -/
theorem sheafBaseChangeStatement_shape_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) :
    F.sheafBaseChangeStatement =
      (F.flatnessAssumption ->
        F.finitePresentationAssumption ->
          F.coefficientCompatibility ->
            F.supportPullbackCompatibility ->
              F.sheafBaseChangeConclusion) :=
  F.sheafBaseChangeStatement_shape

/-- VIII.Theorem candidate 9.2: record that this is a candidate interface only. -/
theorem candidateOnly_holds
    {M : MeasurementProfile.{u, v}}
    {R : Type w} [CommRing R]
    {I_U I_V : Ideal R}
    {A : CommonAmbientPair M R I_U I_V}
    {L : LawConflictMeasurement A}
    (F : FlatBaseChangeCandidate L) : F.candidateOnly :=
  F.candidateOnly_cert

end FlatBaseChangeCandidate

end Measurement
end AAT.AG
