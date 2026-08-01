import Formal.AG.Examples.StandardGeometryReference.SectionRings

/-! # Standard geometry reference: base-to-left restriction -/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open GeometryImplementation
open scoped AlgebraicGeometry Classical

noncomputable section

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_restriction_is_localization :
    baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  letI := canonical_component_isIso baseContext
  letI := canonical_component_isIso leftContext
  rw [baseSectionRingIso, leftSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op baseContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op baseContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op leftContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  slice_lhs 2 4 => rw [canonical_restriction_conjugation]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun base_to_left_transport a


end
end AAT.AG.Examples.StandardGeometryReferenceModels
