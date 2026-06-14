import Formal.AG.RepresentationAnalysis.PreservationReflection

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

namespace RepresentationFamily

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}

/-- VII.定義5.1: representation reading `Read_R(X)`. -/
def RepresentationReading (F : RepresentationFamily p) (i : F.Index)
    (X : AATSch p) : F.Target i :=
  F.Read i X

/-- VII.定義5.1: representation reading is the existing family read accessor. -/
theorem representationReading_eq_read (F : RepresentationFamily p)
    (i : F.Index) (X : AATSch p) :
    F.RepresentationReading i X = F.Read i X :=
  rfl

end RepresentationFamily

/--
VII.定義5.1: convention package permitting the broad-period abbreviation.

The abbreviation is available only after this package is supplied, so the Lean
surface does not globally identify every reading with a period by default.
-/
structure BroadPeriodConvention {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily p) where
  aliasAvailable : Prop
  aliasAvailable_cert : aliasAvailable

namespace BroadPeriodConvention

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily p}

/-- VII.定義5.1: expose that the broad-period alias convention is selected. -/
theorem aliasAvailable_holds (C : BroadPeriodConvention F) :
    C.aliasAvailable :=
  C.aliasAvailable_cert

/-- VII.定義5.1: broad period alias under an explicit convention. -/
def BroadPeriod (_C : BroadPeriodConvention F) (i : F.Index)
    (X : AATSch p) : F.Target i :=
  F.Read i X

/-- VII.定義5.1: broad period alias is the selected representation reading. -/
theorem broadPeriod_eq_read (C : BroadPeriodConvention F)
    (i : F.Index) (X : AATSch p) :
    C.BroadPeriod i X = F.Read i X :=
  rfl

end BroadPeriodConvention

/--
VII.定義5.2: strict period data for a selected representation reading.

The cohomology and homology carriers are explicit selected data.  AC8 will
instantiate them with finite poset / Cech chain complexes and prove the
boundary-square-zero / representative-invariance lemmas.
-/
structure StrictPeriodData {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily p) (X : AATSch p) where
  representationIndex : F.Index
  CoefficientObject : Type z
  CohomologyClass : Type z
  HomologyModel : Type z
  Cycle : Type z
  AdditiveTarget : Type z
  additiveTargetAddCommGroup : AddCommGroup AdditiveTarget
  cohomologyClass : CohomologyClass
  cycle : Cycle
  traceEvaluation : CohomologyClass -> Cycle -> AdditiveTarget
  boundaryCompatible : Prop
  boundaryCompatible_cert : boundaryCompatible
  coboundaryCompatible : Prop
  coboundaryCompatible_cert : coboundaryCompatible

attribute [instance] StrictPeriodData.additiveTargetAddCommGroup

namespace StrictPeriodData

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily p} {X : AATSch p}

/-- VII.定義5.2: the selected reading attached to strict period data. -/
def reading (D : StrictPeriodData F X) : F.Target D.representationIndex :=
  F.Read D.representationIndex X

/-- VII.定義5.2: strict obstruction period as selected trace / evaluation. -/
def strictObstructionPeriod (D : StrictPeriodData F X) : D.AdditiveTarget :=
  D.traceEvaluation D.cohomologyClass D.cycle

/-- VII.定義5.2: strict period is computed by the selected trace / evaluation. -/
theorem strictObstructionPeriod_eq_traceEvaluation (D : StrictPeriodData F X) :
    D.strictObstructionPeriod = D.traceEvaluation D.cohomologyClass D.cycle :=
  rfl

/-- VII.定義5.2: expose selected boundary compatibility. -/
theorem boundaryCompatible_holds (D : StrictPeriodData F X) :
    D.boundaryCompatible :=
  D.boundaryCompatible_cert

/-- VII.定義5.2: expose selected coboundary compatibility. -/
theorem coboundaryCompatible_holds (D : StrictPeriodData F X) :
    D.coboundaryCompatible :=
  D.coboundaryCompatible_cert

end StrictPeriodData

/-- VII.定義5.3: period family selected from a representation family. -/
structure PeriodFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {k : Type v} [CommRing k]
    {p : AATSchReadingParameter.{u, v, w, x, y} S k}
    (F : RepresentationFamily p) where
  PeriodIndex : Type z
  representationIndex : PeriodIndex -> F.Index
  broadConvention : PeriodIndex -> BroadPeriodConvention F

namespace PeriodFamily

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {k : Type v} [CommRing k]
variable {p : AATSchReadingParameter.{u, v, w, x, y} S k}
variable {F : RepresentationFamily p}

/-- VII.定義5.3: read one selected period-family member. -/
def Read (P : PeriodFamily F) (a : P.PeriodIndex) (X : AATSch p) :
    F.Target (P.representationIndex a) :=
  F.Read (P.representationIndex a) X

/-- VII.定義5.3: sigma-package of all selected period readings at `X`. -/
def PeriodMember (P : PeriodFamily F) (_X : AATSch p) :=
  Σ a : P.PeriodIndex, F.Target (P.representationIndex a)

/-- VII.定義5.3: the selected reading gives a member of the period family. -/
def memberOfRead (P : PeriodFamily F) (a : P.PeriodIndex)
    (X : AATSch p) : P.PeriodMember X :=
  ⟨a, P.Read a X⟩

/-- VII.定義5.3: member value is the representation reading. -/
theorem memberOfRead_value (P : PeriodFamily F) (a : P.PeriodIndex)
    (X : AATSch p) :
    (P.memberOfRead a X).2 = P.Read a X :=
  rfl

/-- VII.定義5.3: period family as the set of selected representation readings. -/
def PeriodSet (P : PeriodFamily F) (X : AATSch p) :
    Set (Σ i : F.Index, F.Target i) :=
  { r | ∃ a : P.PeriodIndex, r = ⟨P.representationIndex a, P.Read a X⟩ }

/-- VII.定義5.3: characterize membership in the selected period family. -/
theorem mem_periodSet_iff (P : PeriodFamily F) (X : AATSch p)
    (r : Σ i : F.Index, F.Target i) :
    r ∈ P.PeriodSet X ↔
      ∃ a : P.PeriodIndex, r = ⟨P.representationIndex a, P.Read a X⟩ :=
  Iff.rfl

end PeriodFamily

end RepresentationAnalysis
end AAT.AG
