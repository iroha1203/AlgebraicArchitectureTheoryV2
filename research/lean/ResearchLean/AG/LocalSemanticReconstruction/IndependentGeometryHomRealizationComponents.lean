import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomGeometryComponents
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealizationNative
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealization
import Formal.Util.AssertStandardAxioms

/-!
# Realization on independently assembled full geometry objects

Implementation notes: both comparison APIs receive their context and Atom identifications from the
actual core Hom construction. Representative restriction rules use the
original primitive context tables. Explicit action rules use the common
query cells and the raw context references fixed by the object stages. Keeping
these two profiles separate preserves their different original Hom meanings.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

noncomputable section

universe u v

open Site GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U)

section Representative

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
variable (hl : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)

/-- The directed realization's map premises follow from the reconstructed core Hom. -/
theorem representative_maps : RepresentativeRealization.Maps (base s t p hl)
    (PackageAssembly.retained s.1 t.1 p).table where
  context := PackageAssembly.context_point_iff s.1 t.1 p hl
  atom := PackageAssembly.atom_point_iff s.1 t.1 p hl

/-- Representative naturality is imposed on the original primitive restriction responses. -/
abbrev RepresentativePoints := RepresentativeRealization.PointLaws s.1.val.2.1.val t.1.val.2.1.val
  (PackageAssembly.retained s.1 t.1 p).table

/-- Reconstructed context readings identify exactly the independent representative point laws. -/
theorem representative_points_iff : RepresentativeRealization.NativePoints (assemble s).core (assemble t).core
    (PackageAssembly.retained s.1 t.1 p).table ↔ RepresentativePoints s t p := by
  change RepresentativeRealization.PointLaws _ _ _ ↔ _
  rw [read_context s, read_context t]

/-- Construct all native directed realization fields from independent object and Hom data. -/
def representativeRealization (hp : RepresentativePoints s t p) :
    RealizationTransportSupply (assemble s).core (assemble t).core (base s t p hl) :=
  RepresentativeRealization.assemble _ _ (representative_maps s t p hl)
    ((representative_points_iff s t p).2 hp)

end Representative

section Explicit

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hl : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)

/-- The explicit realization's context and Atom premises also follow from core point recovery. -/
theorem explicit_maps : ExplicitRealization.Maps (base s t p hl)
    (PackageAssembly.retained s.1 t.1 p).table where
  context := PackageAssembly.context_point_iff s.1 t.1 p hl
  atom := PackageAssembly.atom_point_iff s.1 t.1 p hl

/-- Explicit carrier and actual-action conditions use only common primitive Hom cells. -/
abbrev ExplicitPoints := ExplicitRealization.PointLaws (assemble s).core.object (assemble t).core.object
  (PackageAssembly.retained s.1 t.1 p).table

/-- Construct the complete explicit realization on the actual independently assembled core Hom. -/
def explicitRealization (hp : ExplicitPoints s t p) :
    ExplicitRealizationTransportSupply (assemble s).core (assemble t).core (base s t p hl) :=
  ExplicitRealization.assemble _ _ (explicit_maps s t p hl) hp

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.GeometryComponents
