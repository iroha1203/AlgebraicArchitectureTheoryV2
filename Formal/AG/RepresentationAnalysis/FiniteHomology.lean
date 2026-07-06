import Formal.AG.RepresentationAnalysis.Period
import Formal.AG.Cohomology.FinitePosetComparison
import Formal.AG.Cohomology.PeriodStokes

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y

/--
VII.定義5.2A: a selected Cech cocycle represents a selected cohomology class.

Degree zero is represented by the cocycle subtype itself.  Positive degrees use
the PRD-4 coboundary quotient constructor.
-/
def RepresentsCohomologyClass {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (degree : Nat) (h : K.CoverRelativeHn degree) (c : K.Cn degree) : Prop :=
  match degree with
  | 0 => h.1 = c
  | n + 1 =>
      ∃ hc :
        letI := K.cochainAddCommGroup (n + 2)
        K.d (n + 1) c = 0,
        K.cohomologyClassSucc n ⟨c, hc⟩ = h

/--
VII.定義5.2A: selected finite Cech chain cycle condition.

Degree zero chains have no lower boundary in this Nat-indexed surface.  Positive
degree chains are closed under the preceding selected boundary map.
-/
def FiniteCechCycleClosed (C : Cohomology.FiniteCechChainComplex.{u})
    (degree : Nat) (γ : C.Chain degree) : Prop :=
  match degree with
  | 0 => True
  | n + 1 => C.boundaryOp n γ = 0

/--
VII.定義5.2A: finite Cech strict-period representative.

The representative is explicitly relative to a selected cover-relative Cech
complex, a selected finite Cech chain complex, and a selected cochain-chain
pairing.  It does not assert that every cover has a canonical singular
realization or a canonical period pairing.
-/
structure FiniteCechStrictPeriodRepresentative {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (C : Cohomology.FiniteCechChainComplex.{u})
    (P : Cohomology.CechCochainChainPairing K C) where
  degree : Nat
  cohomologyClass : K.CoverRelativeHn degree
  cocycle : K.Cn degree
  cocycle_is_cocycle :
    letI := K.cochainAddCommGroup (degree + 1)
    K.d degree cocycle = 0
  representsCohomologyClass :
    RepresentsCohomologyClass K degree cohomologyClass cocycle
  cycle : C.Chain degree
  cycle_boundary_zero : FiniteCechCycleClosed C degree cycle
  boundaryCompatible : Prop
  boundaryCompatible_cert : boundaryCompatible
  coboundaryCompatible : Prop
  coboundaryCompatible_cert : coboundaryCompatible

namespace FiniteCechStrictPeriodRepresentative

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
variable {C : Cohomology.FiniteCechChainComplex.{u}}
variable {P : Cohomology.CechCochainChainPairing K C}

/-- VII.定義5.2A: the finite Cech pairing value of a representative. -/
def strictPeriodValue (ρ : FiniteCechStrictPeriodRepresentative K C P) : P.Period :=
  P.pair ρ.degree ρ.cocycle ρ.cycle

/-- VII.定義5.2A: expose the selected Cech cocycle condition. -/
theorem cocycle_condition (ρ : FiniteCechStrictPeriodRepresentative K C P) :
    letI := K.cochainAddCommGroup (ρ.degree + 1)
    K.d ρ.degree ρ.cocycle = 0 :=
  ρ.cocycle_is_cocycle

/-- VII.定義5.2A: expose that the selected cocycle represents the selected class. -/
theorem representsCohomologyClass_holds
    (ρ : FiniteCechStrictPeriodRepresentative K C P) :
    RepresentsCohomologyClass K ρ.degree ρ.cohomologyClass ρ.cocycle :=
  ρ.representsCohomologyClass

/-- VII.定義5.2A: expose that the selected chain is closed. -/
theorem cycle_boundary_zero_holds
    (ρ : FiniteCechStrictPeriodRepresentative K C P) :
    FiniteCechCycleClosed C ρ.degree ρ.cycle :=
  ρ.cycle_boundary_zero

/-- VII.定義5.2A: expose selected boundary compatibility. -/
theorem boundaryCompatible_holds
    (ρ : FiniteCechStrictPeriodRepresentative K C P) :
    ρ.boundaryCompatible :=
  ρ.boundaryCompatible_cert

/-- VII.定義5.2A: expose selected coboundary compatibility. -/
theorem coboundaryCompatible_holds
    (ρ : FiniteCechStrictPeriodRepresentative K C P) :
    ρ.coboundaryCompatible :=
  ρ.coboundaryCompatible_cert

/--
VII.定義5.2A: read a finite Cech representative as the AC7 strict-period data.

The trace evaluation is the selected cochain-chain pairing against the selected
cocycle representative whose class-representative relation is recorded in `ρ`.
Therefore the resulting strict period remains representative-relative until a
compatibility package is supplied.
-/
def toStrictPeriodData
    {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {F : RepresentationFamily p} {X : AATSch p}
    (ρ : FiniteCechStrictPeriodRepresentative K C P)
    (i : F.Index) : StrictPeriodData F X where
  representationIndex := i
  CoefficientObject := K.Cn ρ.degree
  CohomologyClass := K.CoverRelativeHn ρ.degree
  HomologyModel := C.Chain ρ.degree
  Cycle := C.Chain ρ.degree
  AdditiveTarget := P.Period
  additiveTargetAddCommGroup := P.periodAddCommGroup
  cohomologyClass := ρ.cohomologyClass
  cycle := ρ.cycle
  traceEvaluation := fun _ γ => P.pair ρ.degree ρ.cocycle γ
  boundaryCompatible := ρ.boundaryCompatible
  boundaryCompatible_cert := ρ.boundaryCompatible_cert
  coboundaryCompatible := ρ.coboundaryCompatible
  coboundaryCompatible_cert := ρ.coboundaryCompatible_cert

/--
VII.定義5.2A: the AC7 strict-period value obtained from a finite Cech
representative is the selected cochain-chain pairing value.
-/
theorem toStrictPeriodData_strictObstructionPeriod
    {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {F : RepresentationFamily p} {X : AATSch p}
    (ρ : FiniteCechStrictPeriodRepresentative K C P)
    (i : F.Index) :
    (ρ.toStrictPeriodData (F := F) (X := X) i).strictObstructionPeriod =
      ρ.strictPeriodValue :=
  rfl

end FiniteCechStrictPeriodRepresentative

/--
VII.定義5.2A: compatibility data under which two finite Cech strict-period
representatives have the same strict period.

The last field is the actual period-pairing compatibility.  The preceding fields
make the cocycle/cycle/coefficient hypotheses explicit on the Lean surface.
-/
structure FiniteCechStrictPeriodRepresentativeCompatibility
    {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {C : Cohomology.FiniteCechChainComplex.{u}}
    {P : Cohomology.CechCochainChainPairing K C}
    (ρ ρ' : FiniteCechStrictPeriodRepresentative K C P) where
  cohomologyClassCompatible : Prop
  cohomologyClassCompatible_cert : cohomologyClassCompatible
  coefficientCompatible : Prop
  coefficientCompatible_cert : coefficientCompatible
  cycleCompatible : Prop
  cycleCompatible_cert : cycleCompatible
  boundaryCompatibility : Prop
  boundaryCompatibility_cert : boundaryCompatibility
  coboundaryCompatibility : Prop
  coboundaryCompatibility_cert : coboundaryCompatibility
  pairingRespectsCompatibility :
    RepresentsCohomologyClass K ρ.degree ρ.cohomologyClass ρ.cocycle ->
      RepresentsCohomologyClass K ρ'.degree ρ'.cohomologyClass ρ'.cocycle ->
        FiniteCechCycleClosed C ρ.degree ρ.cycle ->
          FiniteCechCycleClosed C ρ'.degree ρ'.cycle ->
            cohomologyClassCompatible ->
      coefficientCompatible ->
        cycleCompatible ->
          boundaryCompatibility ->
            coboundaryCompatibility ->
              ρ.strictPeriodValue = ρ'.strictPeriodValue

namespace FiniteCechStrictPeriodRepresentativeCompatibility

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
variable {C : Cohomology.FiniteCechChainComplex.{u}}
variable {P : Cohomology.CechCochainChainPairing K C}
variable {ρ ρ' : FiniteCechStrictPeriodRepresentative K C P}

/--
VII.定義5.2A: strict period representative well-definedness under the selected
cocycle, cycle, coefficient, boundary, and coboundary compatibility package.
-/
theorem strictPeriodValue_wellDefined
    (H : FiniteCechStrictPeriodRepresentativeCompatibility ρ ρ') :
    ρ.strictPeriodValue = ρ'.strictPeriodValue :=
  H.pairingRespectsCompatibility
    ρ.representsCohomologyClass
    ρ'.representsCohomologyClass
    ρ.cycle_boundary_zero
    ρ'.cycle_boundary_zero
    H.cohomologyClassCompatible_cert
    H.coefficientCompatible_cert
    H.cycleCompatible_cert
    H.boundaryCompatibility_cert
    H.coboundaryCompatibility_cert

/--
VII.定義5.2A: the corresponding AC7 strict-period data have equal obstruction
periods under the same finite Cech compatibility package.
-/
theorem strictObstructionPeriod_wellDefined
    {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    {F : RepresentationFamily p} {X : AATSch p}
    (i : F.Index)
    (H : FiniteCechStrictPeriodRepresentativeCompatibility ρ ρ') :
    (ρ.toStrictPeriodData (F := F) (X := X) i).strictObstructionPeriod =
      (ρ'.toStrictPeriodData (F := F) (X := X) i).strictObstructionPeriod :=
  H.strictPeriodValue_wellDefined

end FiniteCechStrictPeriodRepresentativeCompatibility

/--
VII.定義5.2A: finite Cech strict-period context for a selected representation.
-/
structure FiniteCechStrictPeriodContext {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {𝒰 : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily p) (X : AATSch p)
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob) where
  chainComplex : Cohomology.FiniteCechChainComplex.{u}
  pairing : Cohomology.CechCochainChainPairing K chainComplex
  representative :
    FiniteCechStrictPeriodRepresentative K chainComplex pairing
  representationIndex : F.Index

namespace FiniteCechStrictPeriodContext

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily p} {X : AATSch p}
variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}

/-- VII.定義5.2A: the selected finite Cech strict-period data. -/
def strictPeriodData (D : FiniteCechStrictPeriodContext F X K) :
    StrictPeriodData F X :=
  D.representative.toStrictPeriodData D.representationIndex

/-- VII.定義5.2A: read the selected strict period from the finite Cech pairing. -/
theorem strictPeriodData_value (D : FiniteCechStrictPeriodContext F X K) :
    D.strictPeriodData.strictObstructionPeriod =
      D.representative.strictPeriodValue :=
  rfl

end FiniteCechStrictPeriodContext

namespace FiniteCechBoundary

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {𝒰 : Cohomology.CoverRelativeCechCover S}
variable {Ob : Cohomology.ObstructionSheaf S}

/-- VII.定義5.2A: the selected cover-relative Cech differential squares to zero. -/
theorem cech_d_comp_d_eq_zero
    (K : Cohomology.CoverRelativeCechComplex 𝒰 Ob)
    (n : Nat) (c : K.Cn n) :
    letI := K.cochainAddCommGroup (n + 2)
    K.d (n + 1) (K.d n c) = 0 :=
  K.d_comp_d_eq_zero n c

/-- VII.定義5.2A: the selected finite Cech chain boundary squares to zero. -/
theorem boundary_comp_zero
    (C : Cohomology.FiniteCechChainComplex.{u})
    (n : Nat) (γ : C.Chain (n + 2)) :
    C.boundaryOp n (C.boundaryOp (n + 1) γ) = 0 :=
  C.boundary_comp_zero n γ

/--
VII.定理5.3 hypothesis: the selected finite Cech pairing sends a zero chain to
zero in the period target.

The base `CechCochainChainPairing` deliberately does not require additivity in
the chain argument, so strict-period coboundary invariance must record this
equation explicitly.
-/
structure ZeroChainCompatiblePairing
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {C : Cohomology.FiniteCechChainComplex.{u}}
    (P : Cohomology.CechCochainChainPairing K C) where
  pair_zero_chain : ∀ (n : Nat) (ω : K.Cn n), P.pair n ω 0 = 0

namespace ZeroChainCompatiblePairing

variable {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
variable {C : Cohomology.FiniteCechChainComplex.{u}}
variable {P : Cohomology.CechCochainChainPairing K C}

/-- VII.定理5.3: expose the selected zero-chain pairing equation. -/
theorem pair_zero
    (Z : ZeroChainCompatiblePairing P)
    (n : Nat) (ω : K.Cn n) :
    P.pair n ω 0 = 0 :=
  Z.pair_zero_chain n ω

end ZeroChainCompatiblePairing

/--
VII.定理5.3: a selected Stokes-compatible finite Cech pairing kills
coboundaries on closed chains.

This is the load-bearing coboundary invariance used by strict-period
well-definedness: it is an equation in the selected pairing target, not a
separate `Prop` token.
-/
theorem coboundary_pair_eq_zero_on_closed_chain
    {K : Cohomology.CoverRelativeCechComplex 𝒰 Ob}
    {C : Cohomology.FiniteCechChainComplex.{u}}
    {P : Cohomology.CechCochainChainPairing K C}
    (H : Cohomology.StokesCompatiblePairing P)
    (Z : ZeroChainCompatiblePairing P)
    (n : Nat) (ω : K.Cn n) (γ : C.Chain (n + 1))
    (hγ : C.boundaryOp n γ = 0) :
    P.pair (n + 1) (K.d n ω) γ = 0 := by
  rw [H.cechStokes n ω γ, hγ]
  exact Z.pair_zero n ω

end FiniteCechBoundary

/--
VII.定義5.2A: strict-period context specialized to a PRD-2 finite-poset Cech
complex through the PRD-4 finite-poset comparison data.
-/
structure FinitePosetCechStrictPeriodContext {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {Kreg : Site.FinitePosetAATSiteRegime S}
    {Cpos : Site.FinitePosetCechComplex Kreg}
    {Ob : Cohomology.ObstructionSheaf S}
    {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily p) (X : AATSch p)
    (D : Cohomology.FinitePosetCechComparisonData Cpos Ob) where
  finiteCechContext :
    FiniteCechStrictPeriodContext F X D.generalComplex
  finitePosetChainModel : Prop
  finitePosetChainModel_cert : finitePosetChainModel
  finitePosetPairingModel : Prop
  finitePosetPairingModel_cert : finitePosetPairingModel

namespace FinitePosetCechStrictPeriodContext

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {Kreg : Site.FinitePosetAATSiteRegime S}
variable {Cpos : Site.FinitePosetCechComplex Kreg}
variable {Ob : Cohomology.ObstructionSheaf S}
variable {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily p} {X : AATSch p}
variable {D : Cohomology.FinitePosetCechComparisonData Cpos Ob}

/-- VII.定義5.2A: finite-poset comparison differential square-zero accessor. -/
theorem comparison_d_comp_d_eq_zero
    (_H : FinitePosetCechStrictPeriodContext F X D)
    (n : Nat) (c : D.generalComplex.Cn n) :
    letI := D.generalComplex.cochainAddCommGroup (n + 2)
    D.generalComplex.d (n + 1) (D.generalComplex.d n c) = 0 :=
  D.generalComplex.d_comp_d_eq_zero n c

/-- VII.定義5.2A: expose the selected finite-poset provenance of the chain model. -/
theorem finitePosetChainModel_holds
    (H : FinitePosetCechStrictPeriodContext F X D) :
    H.finitePosetChainModel :=
  H.finitePosetChainModel_cert

/-- VII.定義5.2A: expose the selected finite-poset provenance of the pairing. -/
theorem finitePosetPairingModel_holds
    (H : FinitePosetCechStrictPeriodContext F X D) :
    H.finitePosetPairingModel :=
  H.finitePosetPairingModel_cert

/-- VII.定義5.2A: the selected finite-poset Cech strict-period data. -/
def strictPeriodData (H : FinitePosetCechStrictPeriodContext F X D) :
    StrictPeriodData F X :=
  H.finiteCechContext.strictPeriodData

/-- VII.定義5.2A: the selected finite-poset Cech strict period value. -/
theorem strictPeriodData_value
    (H : FinitePosetCechStrictPeriodContext F X D) :
    H.strictPeriodData.strictObstructionPeriod =
      H.finiteCechContext.representative.strictPeriodValue :=
  rfl

end FinitePosetCechStrictPeriodContext

end RepresentationAnalysis
end AAT.AG
