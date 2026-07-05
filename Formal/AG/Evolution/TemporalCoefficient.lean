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

/-- IX.§3 / AC5: fiber-valued temporal zero-cochains on the product site. -/
abbrev FiberZeroCochain (C : TemporalCoefficient T) : Type (max u y) :=
  (p : T.Point) -> C.fiber p

/-- IX.§3 / AC5: fiber-valued temporal one-cochains on selected incidence legs. -/
abbrev FiberIncidenceOneCochain (C : TemporalCoefficient T) : Type (max u y z) :=
  {p q : T.Point} -> T.IncidenceLeg p q -> C.fiber p

/--
IX.§3 / AC5: product-site incidence differential on temporal fiber cochains.

For a selected leg `f : p -> q`, the differential is the actual formula
`δ c f = restrict f (c q) - c p`.
-/
def incidenceDifferential (C : TemporalCoefficient T)
    (c : C.FiberZeroCochain) : C.FiberIncidenceOneCochain :=
  fun {p} {q} (f : T.IncidenceLeg p q) => C.restriction f (c q) - c p

/-- IX.§3 / AC5: the incidence differential vanishes on identity legs. -/
theorem incidenceDifferential_id (C : TemporalCoefficient T)
    (c : C.FiberZeroCochain) (p : T.Point) :
    C.incidenceDifferential c (T.idLeg p) = 0 := by
  change C.restriction (T.idLeg p) (c p) - c p = 0
  rw [C.restrict_identity]
  simp

/--
IX.§3 / AC5: the selected product-site incidence complex for temporal
coefficients.

Degree zero consists of fiber-valued functions on selected trace/context
points; degree one consists of fiber-valued functions on selected incidence
legs.  The differential is the actual incidence formula `δ c f =
restrict f (c q) - c p`.
-/
structure ProductIncidenceComplex (C : TemporalCoefficient T) where
  zeroCochain : Type (max u y)
  oneCochain : Type (max u y z)
  zero_eq : zeroCochain = C.FiberZeroCochain
  one_eq : oneCochain = C.FiberIncidenceOneCochain
  d0 : C.FiberZeroCochain -> C.FiberIncidenceOneCochain
  d0_eq : d0 = C.incidenceDifferential

namespace ProductIncidenceComplex

variable {C : TemporalCoefficient T}

/-- IX.§3 / AC5: the selected zero-cochain carrier is the temporal fiber carrier. -/
theorem zeroCochain_eq_fiber
    (K : ProductIncidenceComplex C) :
    K.zeroCochain = C.FiberZeroCochain :=
  K.zero_eq

/-- IX.§3 / AC5: the selected one-cochain carrier is the incidence-leg carrier. -/
theorem oneCochain_eq_incidence
    (K : ProductIncidenceComplex C) :
    K.oneCochain = C.FiberIncidenceOneCochain :=
  K.one_eq

/-- IX.§3 / AC5: the selected differential is the incidence formula. -/
theorem d0_eq_incidenceDifferential
    (K : ProductIncidenceComplex C) :
    K.d0 = C.incidenceDifferential :=
  K.d0_eq

/-- IX.§3 / AC5: the selected product-incidence differential kills identity legs. -/
theorem d0_id
    (K : ProductIncidenceComplex C)
    (c : C.FiberZeroCochain) (p : T.Point) :
    K.d0 c (T.idLeg p) = 0 := by
  rw [K.d0_eq_incidenceDifferential]
  exact C.incidenceDifferential_id c p

end ProductIncidenceComplex

/--
IX.§3 / AC5--AC6: product-incidence temporal coefficient data together with
the finite-poset PRD-4 comparison bridge.

This is the explicit finite poset x trace bridge used by IX-3: it keeps the
product incidence complex and the PRD-4 finite-poset comparison package in one
object, without asserting a general product-site cohomology theorem.
-/
structure ProductIncidencePRD4Comparison
    (C : TemporalCoefficient T) where
  incidenceComplex : ProductIncidenceComplex C
  finitePosetBridge : FinitePosetTemporalCechBridge T C.obstructionSheaf

namespace ProductIncidencePRD4Comparison

variable {C : TemporalCoefficient T}

/-- IX.§3 / AC5--AC6: expose the product incidence differential formula. -/
theorem incidence_d0_eq
    (P : ProductIncidencePRD4Comparison C) :
    P.incidenceComplex.d0 = C.incidenceDifferential :=
  P.incidenceComplex.d0_eq_incidenceDifferential

/-- IX.§3 / AC5--AC6: expose PRD-4 finite-poset differential compatibility. -/
theorem prd4_differential_compatible
    (P : ProductIncidencePRD4Comparison C)
    (n : Nat) (c : P.finitePosetBridge.comparison.generalComplex.Cn n) :
    P.finitePosetBridge.comparison.comparisonTarget.toFinitePosetCochain (n + 1)
        (P.finitePosetBridge.comparison.generalComplex.d n c) =
      P.finitePosetBridge.finitePosetComplex.differential n
        (P.finitePosetBridge.comparison.comparisonTarget.toFinitePosetCochain n c) :=
  P.finitePosetBridge.differential_compatible n c

end ProductIncidencePRD4Comparison

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
