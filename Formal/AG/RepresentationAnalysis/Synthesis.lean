import Formal.AG.RepresentationAnalysis.AnalyticContext
import Formal.AG.LawAlgebra.ClosedEquationalGeometry

noncomputable section

namespace AAT.AG
namespace RepresentationAnalysis

open CategoryTheory
open AlgebraicGeometry

universe u v w x y z

/--
VII.定理16.1: algebraic-geometric AAT synthesis package.

The package stores the independently constructed Parts II--VII data once.
The Part I architecture object, site, ringed site, atlas, ideal sheaf, and
lawful closed geometry are read from their canonical owners below.

Implementation notes: only independently constructed predecessor data are
fields. Values determined by `P`, `geometry`, `raw`, the standard scheme, or
the closed-equational reading are exposed by the projections below instead of
being stored with coherence equalities.
-/
structure AATSynthesisPackage
    (P : Site.PartIPrerequisites.{u}) (k : Type v) [CommRing k]
    (geometry : Site.ArchitectureGeometry P)
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k)
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)] where
  architectureScheme : LawAlgebra.StandardArchitectureScheme raw
  lawReading :
    LawAlgebra.ClosedEquationalLawReading raw architectureScheme
      geometry.site.equationSystem
  lawReadingValid :
    LawAlgebra.IsClosedEquationalLawReading raw architectureScheme lawReading
  requiredClosed : LawAlgebra.RequiredClosed raw architectureScheme lawReading
  requiredLawIdealExact : LawAlgebra.RequiredLawIdealExact raw architectureScheme lawReading
    lawReadingValid requiredClosed
  cover : Cohomology.CoverRelativeCechCover geometry.site
  obstructionSheaf : Cohomology.ObstructionSheaf geometry.site
  obstructionCohomology : Cohomology.CoverRelativeCechComplex cover obstructionSheaf
  derivedLawGeometry : Derived.RepairProfile.RepairComparisonProfile.{u}
  stratumParameter :
    SingularityMonodromyStack.StratumReadingParameter geometry.site
  singularityMonodromyStack :
    SingularityMonodromyStack.ArchitectureStratum.{u, v, w, x, y} stratumParameter k
  readingParameter : AATSchReadingParameter raw
  representationPeriodMetricAnalysis :
    AnalyticReadingContext.{u, v, w, x, y, z} P.architectureObject readingParameter

namespace AATSynthesisPackage

/-- The Part I architecture object. -/
abbrev architectureObject
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) := P.architectureObject

/-- The site supplied by the selected architecture geometry. -/
abbrev site
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) := geometry.site

/-- The ringed AAT site canonically produced by the raw ambient system. -/
noncomputable abbrev ringedAATSite
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (_Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) := raw.toRingedSite

/-- The affine atlas owned by the selected standard architecture scheme. -/
abbrev affineAtlas
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) := Q.architectureScheme.atlas

/--
The law-generated ideal sheaf of the package reading.

Implementation notes: this definition delegates to the canonical closed-
equational geometry constructor and stores no second ideal-sheaf field.
-/
noncomputable def obstructionIdealSheaf
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    Q.architectureScheme.underlying.IdealSheafData :=
  LawAlgebra.lawGeneratedIdealSheaf raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

/--
The lawful closed subscheme selected by the package reading.

Implementation notes: the subscheme is derived from the package's canonical
scheme and validated reading rather than retained as duplicate package data.
-/
noncomputable def lawfulClosedSubscheme
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) : AlgebraicGeometry.Scheme :=
  LawAlgebra.lawfulClosedSubscheme raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

/--
The canonical closed immersion of the lawful closed subscheme.

Implementation notes: the arrow is the canonical immersion belonging to the
derived lawful closed subscheme.
-/
noncomputable def lawfulClosedImmersion
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    Q.lawfulClosedSubscheme ⟶ Q.architectureScheme.underlying :=
  LawAlgebra.lawfulClosedImmersion raw Q.architectureScheme Q.lawReading
    Q.lawReadingValid Q.requiredClosed

/-- The Part VII analytic reading context. -/
def analyticReadingContext
    {P : Site.PartIPrerequisites.{u}} {k : Type v} [CommRing k]
    {geometry : Site.ArchitectureGeometry P}
    {raw : LawAlgebra.RawAmbientRestrictionSystem geometry.site k}
    [HasSheafify geometry.site.topology (LawAlgebra.AATCommAlgCat k)]
    (Q : AATSynthesisPackage.{u, v, w, x, y, z} P k geometry raw) :
    AnalyticReadingContext.{u, v, w, x, y, z} P.architectureObject Q.readingParameter :=
  Q.representationPeriodMetricAnalysis

end AATSynthesisPackage
end RepresentationAnalysis
end AAT.AG
