import Formal.AG.Examples.FiniteModel
import Formal.AG.Atom.ObstructionLegacy

namespace AAT.AG

namespace FiniteModel

/-- The one-way legacy law generated from the finite equation is the NoCycle predicate. -/
theorem equationSystem_legacy_law_eq_noCycleLaw
    (C : Site.ContextPreorderCategory object) :
    (equationSystem C).toLegacyLawUniverse.law PUnit.unit = noCycleLaw := by
  apply Law.ext
  funext A
  apply propext
  exact equationHolds_iff_noCycleLaw C A

/-- The generated site legacy display is exactly the finite NoCycle equation. -/
@[simp] theorem site_law_holds_iff_noCycleLaw
    (A : ArchitectureObject carrier) :
    (site.equationSystem.toLegacyLawUniverse.law PUnit.unit).holds A ↔
      noCycleLaw.holds A := by
  exact site_equationHolds_iff_noCycleLaw A

/-- SD2: the finite site retains the generated core law universe. -/
theorem site_lawUniverse_eq_core :
    site.equationSystem.toLegacyLawUniverse =
      siteCorePackage.equationSystem.toLegacyLawUniverse :=
  rfl

end FiniteModel

end AAT.AG
