import Formal.AG.Evolution.TemporalProductSite
import Formal.AG.Measurement.FiniteRegime

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
PRD-9 R2 / AC5--AC6 temporal coefficient surface.

The coefficient object is profile-relative: it combines the selected Part IX
coefficient profile, an obstruction sheaf over the selected AAT site, and a
finite measurement/effective-coefficient interface inherited from PRD-8.
-/

/--
IX.§3 / AC5: temporal coefficient object `TempCoeff_A`.

The temporal fibers are indexed by selected trace/context points and carry
restriction maps along the selected product/incidence legs of `Tr_E × X`.
The link to the PRD-4 obstruction sheaf is typed as a comparison map on every
temporal point, not as an unstructured global claim.
-/
structure TemporalCoefficient {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) where
  coefficientProfile : E.selectedCoefficientProfile
  obstructionSheaf : Cohomology.ObstructionSheaf S
  fiber : T.Point -> Type (max u y)
  fiberAddCommGroup : ∀ p : T.Point, AddCommGroup (fiber p)
  restrict :
    ∀ {p q : T.Point}, T.IncidenceLeg p q -> fiber q →+ fiber p
  restrict_id :
    ∀ (p : T.Point) (x : fiber p), restrict (T.idLeg p) x = x
  restrict_comp :
    ∀ {p q r : T.Point} (f : T.IncidenceLeg p q) (g : T.IncidenceLeg q r)
      (x : fiber r),
      restrict (T.compLeg f g) x = restrict f (restrict g x)
  toObstructionSection :
    ∀ p : T.Point,
      fiber p →+
        obstructionSheaf.carrier.toPresheaf.obj
          (Opposite.op
            (Site.ContextCategoryObject.of S.contextPreorder
              (T.siteRegime.context p.2)))

attribute [instance] TemporalCoefficient.fiberAddCommGroup

/-- IX.§3 / AC5: notation-style alias for the selected temporal coefficient. -/
abbrev TempCoeff_A {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    (T : TemporalSite S E) :=
  TemporalCoefficient T

namespace TemporalCoefficient

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}

/-- IX.§3 / AC5: read the obstruction sheaf backing the temporal coefficient. -/
def obstruction (C : TemporalCoefficient T) : Cohomology.ObstructionSheaf S :=
  C.obstructionSheaf

/-- IX.§3 / AC5: restriction along a selected temporal incidence leg. -/
def restriction (C : TemporalCoefficient T) {p q : T.Point}
    (f : T.IncidenceLeg p q) : C.fiber q →+ C.fiber p :=
  C.restrict f

/-- IX.§3 / AC5: temporal coefficient restriction respects identity legs. -/
theorem restrict_identity (C : TemporalCoefficient T)
    (p : T.Point) (x : C.fiber p) :
    C.restriction (T.idLeg p) x = x :=
  C.restrict_id p x

/-- IX.§3 / AC5: temporal coefficient restriction respects composed legs. -/
theorem restrict_composition (C : TemporalCoefficient T)
    {p q r : T.Point} (f : T.IncidenceLeg p q) (g : T.IncidenceLeg q r)
    (x : C.fiber r) :
    C.restriction (T.compLeg f g) x = C.restriction f (C.restriction g x) :=
  C.restrict_comp f g x

/--
IX.§3 / AC5: compare a temporal coefficient fiber with the PRD-4 obstruction
sheaf section over the architecture context component.
-/
def to_obstruction_section (C : TemporalCoefficient T) (p : T.Point) :
    C.fiber p →+
      C.obstructionSheaf.carrier.toPresheaf.obj
        (Opposite.op
          (Site.ContextCategoryObject.of S.contextPreorder
            (T.siteRegime.context p.2))) :=
  C.toObstructionSection p

end TemporalCoefficient

/--
IX.§3 / AC6: finite temporal coefficient regime.

This records that the temporal coefficient is used through a selected finite
measurement regime and its effective coefficient interface.
-/
structure FiniteTemporalCoefficientRegime {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {E : EvolutionProfile.{u, v, w, x, y, z}}
    {T : TemporalSite S E} (C : TemporalCoefficient T) where
  measurementRegime : Measurement.FiniteMeasurementRegime E.measurementProfile
  effectiveCoefficient : Measurement.EffCoeff E.measurementProfile
  effectiveCoefficient_eq : effectiveCoefficient = measurementRegime.effCoeff
  measuredCoefficientProfile :
    E.measurementProfile.Coeff -> E.selectedCoefficientProfile -> Prop
  selectedMeasurementCoefficient : E.measurementProfile.Coeff
  coefficientProfile_measured :
    measuredCoefficientProfile selectedMeasurementCoefficient C.coefficientProfile

namespace FiniteTemporalCoefficientRegime

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {E : EvolutionProfile.{u, v, w, x, y, z}}
variable {T : TemporalSite S E}
variable {C : TemporalCoefficient T}

/-- IX.§3 / AC6: read the selected PRD-8 finite measurement regime. -/
def measurement (R : FiniteTemporalCoefficientRegime C) :
    Measurement.FiniteMeasurementRegime E.measurementProfile :=
  R.measurementRegime

/-- IX.§3 / AC6: the temporal coefficient uses the selected effective interface. -/
theorem effectiveCoefficient_matches_measurement
    (R : FiniteTemporalCoefficientRegime C) :
    R.effectiveCoefficient = R.measurementRegime.effCoeff :=
  R.effectiveCoefficient_eq

/-- IX.§3 / AC6: finiteness is inherited from the selected PRD-8 measurement regime. -/
theorem finite_temporal_site (R : FiniteTemporalCoefficientRegime C) :
    R.measurementRegime.finiteSite :=
  R.measurementRegime.finiteSite_holds

/-- IX.§3 / AC6: finite-cover evidence is inherited from PRD-8. -/
theorem finite_temporal_cover (R : FiniteTemporalCoefficientRegime C) :
    R.measurementRegime.finiteCover :=
  R.measurementRegime.finiteCover_holds

/-- IX.§3 / AC6: effective-coefficient evidence is inherited from PRD-8. -/
theorem effective_coefficient_holds (R : FiniteTemporalCoefficientRegime C) :
    R.measurementRegime.effectiveCoefficient :=
  R.measurementRegime.effectiveCoefficient_holds

/-- IX.§3 / AC6: the selected temporal coefficient profile is measured by PRD-8 data. -/
theorem coefficient_backed_by_measurement
    (R : FiniteTemporalCoefficientRegime C) :
    R.measuredCoefficientProfile R.selectedMeasurementCoefficient C.coefficientProfile :=
  R.coefficientProfile_measured

end FiniteTemporalCoefficientRegime

end Evolution
end AAT.AG
