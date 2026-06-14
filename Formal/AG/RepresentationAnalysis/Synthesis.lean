import Formal.AG.RepresentationAnalysis.AnalyticContext

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

universe u v w x y z

/--
VII.定理16.1: assumptions for the algebraic-geometric AAT synthesis package.

The package records the predecessor tower supplied by Parts I--VI together with
the Part VII analytic reading context.  It does not add a global measurement
verdict or assert completeness beyond the selected reading discipline.
-/
structure AATSynthesisAssumptions (P : Site.PartIPrerequisites.{u})
    (k : Type v) [CommRing k] where
  architectureGeometry : Site.ArchitectureGeometry P
  ringedAATTopos : LawAlgebra.Scheme.RingedAATTopos.{u, v, y}
    architectureGeometry.site k
  architectureScheme : LawAlgebra.Scheme.ArchitectureScheme.{u, v, w, x, y}
    architectureGeometry.site k
  ringedAATTopos_eq_scheme :
    ringedAATTopos = architectureScheme.ringedTopos
  LawCoordinateAlgebra : Type w
  lawCoordinateCommRing : CommRing LawCoordinateAlgebra
  obstructionIdeal : Ideal LawCoordinateAlgebra
  lawfulLocus : Set (PrimeSpectrum LawCoordinateAlgebra)
  lawfulLocus_eq :
    lawfulLocus =
      LawAlgebra.LawfulLocus.lawfulLocus LawCoordinateAlgebra obstructionIdeal
  lawfulSection : LawAlgebra.LawfulLocus.LawfulSectionData.{w, x}
    LawCoordinateAlgebra obstructionIdeal
  cover : Cohomology.CoverRelativeCechCover architectureGeometry.site
  obstructionSheaf : Cohomology.ObstructionSheaf architectureGeometry.site
  obstructionCohomology :
    Cohomology.CoverRelativeCechComplex cover obstructionSheaf
  derivedLawGeometry : Derived.RepairProfile.RepairComparisonProfile.{u}
  stratumParameter :
    SingularityMonodromyStack.StratumReadingParameter architectureGeometry.site
  singularityMonodromyStack :
    SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y}
      stratumParameter k
  readingParameter : AATSchReadingParameter.{u, v, w, x, y}
    architectureGeometry.site k
  representationPeriodMetricAnalysis :
    AnalyticReadingContext.{u, v, w, x, y, z}
      P.architectureObject readingParameter

namespace AATSynthesisAssumptions

attribute [instance] lawCoordinateCommRing

/-- VII.定理16.1: expose the canonical lawful-locus reading. -/
theorem lawfulLocus_is_zeroLocus
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (A : AATSynthesisAssumptions.{u, v, w, x, y, z} P k) :
    A.lawfulLocus =
      LawAlgebra.LawfulLocus.lawfulLocus A.LawCoordinateAlgebra A.obstructionIdeal :=
  A.lawfulLocus_eq

end AATSynthesisAssumptions

/--
VII.定理16.1: algebraic-geometric AAT synthesis package.

The fields are the explicit tower named in R12: Atom, AtomFamily,
ArchitectureObject, ArchitectureGeometry, AATSite, RingedAATTopos,
AffineAATCharts, ArchitectureScheme, LawfulLocus, ObstructionCohomology,
DerivedLawGeometry, SingularityMonodromyStack, and
RepresentationPeriodMetricAnalysis.
-/
structure AATSynthesisPackage (P : Site.PartIPrerequisites.{u})
    (k : Type v) [CommRing k] where
  Atom : Type u
  atom_eq : Atom = P.carrier.Atom
  atomFamily : AtomFamily P.carrier
  atomFamily_eq_core : atomFamily = P.core.family
  architectureObject : ArchitectureObject P.carrier
  architectureObject_eq_core : architectureObject = P.architectureObject
  architectureGeometry : Site.ArchitectureGeometry P
  aatSite : Site.AATSite P.architectureObject
  aatSite_eq_geometry : aatSite = architectureGeometry.site
  ringedAATTopos : LawAlgebra.Scheme.RingedAATTopos.{u, v, y}
    architectureGeometry.site k
  architectureScheme : LawAlgebra.Scheme.ArchitectureScheme.{u, v, w, x, y}
    architectureGeometry.site k
  ringedAATTopos_eq_scheme :
    ringedAATTopos = architectureScheme.ringedTopos
  affineChartIndex : Type y
  affineChartIndex_eq_scheme : affineChartIndex = architectureScheme.ChartIndex
  affineAATCharts :
    architectureScheme.ChartIndex -> LawAlgebra.AffineChart.AffineAATChart.{v, w, x} k
  affineAATCharts_eq_scheme : affineAATCharts = architectureScheme.chart
  LawCoordinateAlgebra : Type w
  lawCoordinateCommRing : CommRing LawCoordinateAlgebra
  obstructionIdeal : Ideal LawCoordinateAlgebra
  lawfulLocus : Set (PrimeSpectrum LawCoordinateAlgebra)
  lawfulLocus_eq :
    lawfulLocus =
      LawAlgebra.LawfulLocus.lawfulLocus LawCoordinateAlgebra obstructionIdeal
  lawfulSection : LawAlgebra.LawfulLocus.LawfulSectionData.{w, x}
    LawCoordinateAlgebra obstructionIdeal
  cover : Cohomology.CoverRelativeCechCover architectureGeometry.site
  obstructionSheaf : Cohomology.ObstructionSheaf architectureGeometry.site
  obstructionCohomology :
    Cohomology.CoverRelativeCechComplex cover obstructionSheaf
  derivedLawGeometry : Derived.RepairProfile.RepairComparisonProfile.{u}
  stratumParameter :
    SingularityMonodromyStack.StratumReadingParameter architectureGeometry.site
  singularityMonodromyStack :
    SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y}
      stratumParameter k
  readingParameter : AATSchReadingParameter.{u, v, w, x, y}
    architectureGeometry.site k
  representationPeriodMetricAnalysis :
    AnalyticReadingContext.{u, v, w, x, y, z}
      P.architectureObject readingParameter

namespace AATSynthesisPackage

attribute [instance] lawCoordinateCommRing

/-- VII.定理16.1: the package's site is the one supplied by the geometry. -/
theorem aatSite_is_geometry_site
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (S : AATSynthesisPackage.{u, v, w, x, y, z} P k) :
    S.aatSite = S.architectureGeometry.site :=
  S.aatSite_eq_geometry

/-- VII.定理16.1: the selected ringed topos is the scheme's ringed topos. -/
theorem ringedAATTopos_is_scheme_ringedTopos
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (S : AATSynthesisPackage.{u, v, w, x, y, z} P k) :
    S.ringedAATTopos = S.architectureScheme.ringedTopos :=
  S.ringedAATTopos_eq_scheme

/-- VII.定理16.1: the selected affine charts are the scheme atlas. -/
theorem affineAATCharts_are_scheme_charts
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (S : AATSynthesisPackage.{u, v, w, x, y, z} P k) :
    S.affineAATCharts = S.architectureScheme.chart :=
  S.affineAATCharts_eq_scheme

/-- VII.定理16.1: expose the lawful locus as the selected zero locus. -/
theorem lawfulLocus_is_zeroLocus
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (S : AATSynthesisPackage.{u, v, w, x, y, z} P k) :
    S.lawfulLocus =
      LawAlgebra.LawfulLocus.lawfulLocus S.LawCoordinateAlgebra S.obstructionIdeal :=
  S.lawfulLocus_eq

/-- VII.定理16.1: expose the Part VII analytic reading context. -/
def analyticReadingContext
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (S : AATSynthesisPackage.{u, v, w, x, y, z} P k) :
    AnalyticReadingContext.{u, v, w, x, y, z}
      P.architectureObject S.readingParameter :=
  S.representationPeriodMetricAnalysis

end AATSynthesisPackage

/-- VII.定理16.1: construct the synthesis package from the selected tower. -/
def AATSynthesisAssumptions.toPackage
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (A : AATSynthesisAssumptions.{u, v, w, x, y, z} P k) :
    AATSynthesisPackage.{u, v, w, x, y, z} P k where
  Atom := P.carrier.Atom
  atom_eq := rfl
  atomFamily := P.core.family
  atomFamily_eq_core := rfl
  architectureObject := P.architectureObject
  architectureObject_eq_core := rfl
  architectureGeometry := A.architectureGeometry
  aatSite := A.architectureGeometry.site
  aatSite_eq_geometry := rfl
  ringedAATTopos := A.ringedAATTopos
  architectureScheme := A.architectureScheme
  ringedAATTopos_eq_scheme := A.ringedAATTopos_eq_scheme
  affineChartIndex := A.architectureScheme.ChartIndex
  affineChartIndex_eq_scheme := rfl
  affineAATCharts := A.architectureScheme.chart
  affineAATCharts_eq_scheme := rfl
  LawCoordinateAlgebra := A.LawCoordinateAlgebra
  lawCoordinateCommRing := A.lawCoordinateCommRing
  obstructionIdeal := A.obstructionIdeal
  lawfulLocus := A.lawfulLocus
  lawfulLocus_eq := A.lawfulLocus_eq
  lawfulSection := A.lawfulSection
  cover := A.cover
  obstructionSheaf := A.obstructionSheaf
  obstructionCohomology := A.obstructionCohomology
  derivedLawGeometry := A.derivedLawGeometry
  stratumParameter := A.stratumParameter
  singularityMonodromyStack := A.singularityMonodromyStack
  readingParameter := A.readingParameter
  representationPeriodMetricAnalysis := A.representationPeriodMetricAnalysis

/--
VII.定理16.1: Algebraic-Geometric AAT Synthesis.

Given the predecessor assumption packages and the Part VII reading context, the
AAT tower opens to a disciplined representation-period metric analysis package.
-/
theorem algebraicGeometricAATSynthesis
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    (A : AATSynthesisAssumptions.{u, v, w, x, y, z} P k) :
    A.toPackage.architectureGeometry = A.architectureGeometry ∧
      A.toPackage.aatSite = A.architectureGeometry.site ∧
      A.toPackage.ringedAATTopos = A.ringedAATTopos ∧
      A.toPackage.ringedAATTopos = A.toPackage.architectureScheme.ringedTopos ∧
      A.toPackage.affineAATCharts = A.toPackage.architectureScheme.chart ∧
      A.toPackage.architectureScheme = A.architectureScheme ∧
      A.toPackage.lawfulLocus =
        LawAlgebra.LawfulLocus.lawfulLocus
          A.toPackage.LawCoordinateAlgebra A.toPackage.obstructionIdeal ∧
      A.toPackage.obstructionCohomology = A.obstructionCohomology ∧
      A.toPackage.derivedLawGeometry = A.derivedLawGeometry ∧
      A.toPackage.singularityMonodromyStack = A.singularityMonodromyStack ∧
      A.toPackage.representationPeriodMetricAnalysis =
        A.representationPeriodMetricAnalysis :=
  ⟨rfl, rfl, rfl, A.ringedAATTopos_eq_scheme, rfl, rfl, A.lawfulLocus_eq,
    rfl, rfl, rfl, rfl⟩

end RepresentationAnalysis
end AAT.AG
