import Formal.AG.Examples.StandardGeometryReference.RawGeometry
import Formal.AG.LawAlgebra.StandardScheme

/-!
# Standard geometry reference: sheafified section rings

This module identifies the four sheafified section rings with the ambient
polynomial ring and its three localization presentations.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open GeometryImplementation
open scoped AlgebraicGeometry Classical

noncomputable section

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem canonical_component_isIso (W : referenceSite.category) :
    IsIso (referenceRaw.toRingedSite.canonical.app (op W)) := by
  haveI : IsIso (CategoryTheory.toSheafify referenceSite.topology
      referenceRaw.toPresheaf) :=
    CategoryTheory.isIso_toSheafify
      (J := referenceSite.topology) referenceRaw_isSheaf
  change IsIso ((CategoryTheory.toSheafify referenceSite.topology
    referenceRaw.toPresheaf).app (op W))
  infer_instance

/--
SD0 constructor-provenance lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
It factors the canonical-map naturality calculation shared by the four reference restriction theorems.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem canonical_restriction_conjugation
    {source target : referenceSite.category} (f : source ⟶ target)
    [IsIso (referenceRaw.toRingedSite.canonical.app (op source))] :
    (referenceRaw.toRingedSite.canonical.app (op target)).right ≫
        sheafifiedRestriction referenceRaw f ≫
        inv (referenceRaw.toRingedSite.canonical.app (op source)).right =
      CommRingCat.ofHom
        (referenceRaw.restrictionStable f).quotientDesc := by
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op target)).right ≫
          sheafifiedRestriction referenceRaw f =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable f).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op source)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [← Category.assoc, hnat]
  simp only [Category.assoc]
  rw [IsIso.hom_inv_id, Category.comp_id]

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def baseSectionRingIso :
    SheafifiedSectionRing referenceRaw baseContext ≅
      CommRingCat.of AmbientRing := by
  letI := canonical_component_isIso baseContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op baseContext)).right).symm ≪≫
      baseRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftSectionRingIso :
    SheafifiedSectionRing referenceRaw leftContext ≅
      CommRingCat.of (Localization.Away leftGenerator) := by
  letI := canonical_component_isIso leftContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm ≪≫
      leftRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightSectionRingIso :
    SheafifiedSectionRing referenceRaw rightContext ≅
      CommRingCat.of (Localization.Away rightGenerator) := by
  letI := canonical_component_isIso rightContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op rightContext)).right).symm ≪≫
      rightRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def overlapSectionRingIso :
    SheafifiedSectionRing referenceRaw overlapContext ≅
      CommRingCat.of (Localization.Away overlapGenerator) := by
  letI := canonical_component_isIso overlapContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right).symm ≪≫
      overlapRawAlgebraIso


end
end AAT.AG.Examples.StandardGeometryReferenceModels
