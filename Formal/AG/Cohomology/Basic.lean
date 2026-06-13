import Formal.AG.Site
import Formal.AG.LawAlgebra

namespace AAT.AG
namespace Cohomology

universe u v

/--
IV.R0: prerequisite package for the Part IV obstruction-cohomology tower.

Part IV starts only after the Part II site surface and the Part III law-algebra
surface are available.  This package records those dependencies as data for the
first bootstrap module; it does not define obstruction sheaves, Cech complexes,
or cohomology groups yet.
-/
structure PartIVPrerequisites (k : Type v) [CommRing k] where
  carrier : AtomCarrier.{u}
  core : AATCorePackage carrier
  affineChart : LawAlgebra.AffineChart.AffineAATChart k

namespace PartIVPrerequisites

variable {k : Type v} [CommRing k]

/-- IV.R0: read the Part II prerequisite package supplied by the bootstrap data. -/
def sitePrerequisites (P : PartIVPrerequisites.{u, v} k) :
    Site.PartIPrerequisites.{u} where
  carrier := P.carrier
  core := P.core

/-- IV.R0: read the Part III affine chart supplied by the bootstrap data. -/
def selectedAffineChart (P : PartIVPrerequisites.{u, v} k) :
    LawAlgebra.AffineChart.AffineAATChart k :=
  P.affineChart

/--
IV.R0: the bootstrap package exposes exactly the selected architecture object
already supplied through the Part II site prerequisite surface.
-/
theorem site_architectureObject_eq (P : PartIVPrerequisites.{u, v} k) :
    P.sitePrerequisites.architectureObject = P.core.object :=
  rfl

end PartIVPrerequisites

end Cohomology
end AAT.AG
