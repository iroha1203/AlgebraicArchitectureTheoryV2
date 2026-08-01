import Formal.AG.Examples.StandardGeometryReference.SectionRings

/-! # Standard geometry reference: left-to-overlap restriction -/

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
theorem overlap_left_restriction_is_localization :
    leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom := by
  letI := canonical_component_isIso leftContext
  letI := canonical_component_isIso overlapContext
  rw [leftSectionRingIso, overlapSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right ≫
          sheafifiedRestriction referenceRaw overlapToLeft =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable overlapToLeft).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn :=
      referenceRaw.toRingedSite.canonical.naturality overlapToLeft.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op leftContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  slice_lhs 2 3 => rw [hnat]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  simp only [Category.assoc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun left_to_overlap_transport a


end
end AAT.AG.Examples.StandardGeometryReferenceModels
