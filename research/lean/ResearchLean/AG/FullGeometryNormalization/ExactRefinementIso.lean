import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparator
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteGeometryExactification

/-!
# Exact isomorphisms reflected from refinement isomorphisms

The refinement package and refinement geometry categories retain the complete
upper data of their exact counterparts.  This file packages the corresponding
reflection argument for isomorphisms.  A caller supplies only an exact
isomorphism at the lower stage, a refinement isomorphism at the upper stage,
and the equality identifying their forward lower maps.  The inverse lower-map
equality is then forced by functoriality, while faithfulness of the exact
embeddings reflects the two inverse laws.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

namespace UpperGeometryCleavage

set_option maxHeartbeats 3000000

/-- Lift a refinement-package isomorphism to the exact package category once
its lower map is identified with the embedding of an exact pointed
isomorphism.  No inverse compatibility certificate is requested: it follows
from functoriality of the two projections and the supplied forward equality. -/
noncomputable def exactPackageIsoOfRefinementIso
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (baseIso : packagePoint P ≅ packagePoint Q)
    (refinementIso :
      (show RefinementPackageTotalCategory U from ⟨P⟩) ≅
        (show RefinementPackageTotalCategory U from ⟨Q⟩))
    (hbase : refinementIso.hom.base =
      (exactPointedToRefinement U).map baseIso.hom) :
    (show PackageTotalCategory U from P) ≅
      (show PackageTotalCategory U from Q) := by
  have hbase_inv : refinementIso.inv.base =
      (exactPointedToRefinement U).map baseIso.inv := by
    change (refinementPackageProjection U).map refinementIso.inv =
      (exactPointedToRefinement U).map baseIso.inv
    calc
      (refinementPackageProjection U).map refinementIso.inv =
          inv ((refinementPackageProjection U).map refinementIso.hom) :=
        by simpa using
          Functor.map_inv (refinementPackageProjection U) refinementIso.hom
      _ = inv ((exactPointedToRefinement U).map baseIso.hom) :=
        IsIso.inv_eq_inv.mpr hbase
      _ = (exactPointedToRefinement U).map baseIso.inv :=
        by simpa using
          (Functor.map_inv (exactPointedToRefinement U) baseIso.hom).symm
  let forwardSeed : PackageTotalHom P Q := {
    base := baseIso.hom
    upper := refinementIso.hom.upper
    atomEquiv_eq := by
      change refinementIso.hom.upper.atomEquiv =
        baseIso.hom.doctrineHom.atomEquiv
      rw [refinementIso.hom.atomEquiv_eq, hbase]
      apply Equiv.ext
      intro atom
      rfl
  }
  let inverseSeed : PackageTotalHom Q P := {
    base := baseIso.inv
    upper := refinementIso.inv.upper
    atomEquiv_eq := by
      change refinementIso.inv.upper.atomEquiv =
        baseIso.inv.doctrineHom.atomEquiv
      rw [refinementIso.inv.atomEquiv_eq, hbase_inv]
      apply Equiv.ext
      intro atom
      rfl
  }
  let forward : PackageTotalHom P Q :=
    exactPackageHomOfRefinement forwardSeed refinementIso.hom hbase
  let inverse : PackageTotalHom Q P :=
    exactPackageHomOfRefinement inverseSeed refinementIso.inv hbase_inv
  exact {
    hom := forward
    inv := inverse
    hom_inv_id := by
      apply exactPackageToRefinement_map_injective
      rw [Functor.map_comp,
        exactPackageHomOfRefinement_toRefinement,
        exactPackageHomOfRefinement_toRefinement]
      exact refinementIso.hom_inv_id
    inv_hom_id := by
      apply exactPackageToRefinement_map_injective
      rw [Functor.map_comp,
        exactPackageHomOfRefinement_toRefinement,
        exactPackageHomOfRefinement_toRefinement]
      exact refinementIso.inv_hom_id
  }

/-- Lift a refinement-geometry isomorphism to the exact geometry category once
its package projection is identified with the embedding of an exact package
isomorphism.  The inverse projection equality is derived internally, and the
complete geometry inverse laws are reflected through the faithful exact
geometry embedding. -/
noncomputable def exactGeometryIsoOfRefinementIso
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (baseIso :
      (show PackageTotalCategory U from G.core) ≅
        (show PackageTotalCategory U from H.core))
    (refinementIso : RefinementGeometryObject.mk G ≅
      RefinementGeometryObject.mk H)
    (hbase : refinementIso.hom.base =
      (exactPackageToRefinement U).map baseIso.hom) :
    (show GeomReadCategory U from G) ≅
      (show GeomReadCategory U from H) := by
  have hbase_inv : refinementIso.inv.base =
      (exactPackageToRefinement U).map baseIso.inv := by
    change (refinementGeometryProjection U).map refinementIso.inv =
      (exactPackageToRefinement U).map baseIso.inv
    calc
      (refinementGeometryProjection U).map refinementIso.inv =
          inv ((refinementGeometryProjection U).map refinementIso.hom) :=
        by simpa using
          Functor.map_inv (refinementGeometryProjection U) refinementIso.hom
      _ = inv ((exactPackageToRefinement U).map baseIso.hom) :=
        IsIso.inv_eq_inv.mpr hbase
      _ = (exactPackageToRefinement U).map baseIso.inv :=
        by simpa using
          (Functor.map_inv (exactPackageToRefinement U) baseIso.hom).symm
  let forward : GeometryTotalHom G H :=
    exactGeometryHomOfRefinement baseIso.hom refinementIso.hom hbase
  let inverse : GeometryTotalHom H G :=
    exactGeometryHomOfRefinement baseIso.inv refinementIso.inv hbase_inv
  exact {
    hom := forward
    inv := inverse
    hom_inv_id := by
      apply (exactGeometryToRefinementGeometry U).map_injective
      rw [Functor.map_comp,
        exactGeometryHomOfRefinement_toRefinement,
        exactGeometryHomOfRefinement_toRefinement]
      exact refinementIso.hom_inv_id
    inv_hom_id := by
      apply (exactGeometryToRefinementGeometry U).map_injective
      rw [Functor.map_comp,
        exactGeometryHomOfRefinement_toRefinement,
        exactGeometryHomOfRefinement_toRefinement]
      exact refinementIso.inv_hom_id
  }

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
