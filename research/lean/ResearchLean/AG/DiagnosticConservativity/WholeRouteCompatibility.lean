import ResearchLean.AG.DiagnosticConservativity.TrianglePentagonCompatibility

/-!
# G-113 revision 2 whole-route natural-isomorphism surface

The G-111 and G-112 coherence modules expose their triangle and pentagon
routes componentwise.  Whole-route conjugacy requires the corresponding
natural isomorphisms.  This module promotes all four routes on both sides and
records that their hom components are exactly the reviewed component routes.
It also fixes equality transport as a natural isomorphism on both sides.

## Implementation notes

The route packages use `NatIso` composition with the standard functor unitors,
whiskering, and equality casts.  This makes each hom component definitionally,
or by one local normalization, the reviewed G-111/G-112 component route.  The
right pentagon keeps the associativity cast as its final factor; contravariance
therefore reverses the base equality.

Component-only aliases were rejected because they cannot be passed through
`conjugateIsoEquiv`.  Caller-supplied route isomorphisms were rejected because
they would move the G-113(h) obligation into a premise.  A conjunction of the
two predecessor coherence propositions was rejected because it would not
produce the typed whole-route cells needed by the next cross-system proof.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## G-111 covariant routes -/

/-- Equality transport promoted to a natural isomorphism for G-111 transport.
G-113(h) infrastructure definition; its data come only from base-arrow equality. -/
noncomputable def coreFiberTransportEqCastIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    {first second : source ⟶ target} (equality : first = second) :
    coreFiberTransportFunctor first ≅ coreFiberTransportFunctor second :=
  eqToIso (congrArg coreFiberTransportFunctor equality)

/-- The whole G-111 source-unit route.
G-113(h) infrastructure definition generated from the reviewed G-111 unitor and compositor. -/
noncomputable def coreFiberLeftUnitRouteIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    coreFiberTransportFunctor (𝟙 source ≫ hom) ≅
      coreFiberTransportFunctor hom :=
  coreFiberCompositor (𝟙 source) hom ≪≫
    Functor.isoWhiskerRight (coreFiberUnitor source)
      (coreFiberTransportFunctor hom) ≪≫
    Functor.leftUnitor (coreFiberTransportFunctor hom)

/-- The whole G-111 target-unit route.
G-113(h) infrastructure definition generated from the reviewed G-111 unitor and compositor. -/
noncomputable def coreFiberRightUnitRouteIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    coreFiberTransportFunctor (hom ≫ 𝟙 target) ≅
      coreFiberTransportFunctor hom :=
  coreFiberCompositor hom (𝟙 target) ≪≫
    Functor.isoWhiskerLeft (coreFiberTransportFunctor hom)
      (coreFiberUnitor target) ≪≫
    Functor.rightUnitor (coreFiberTransportFunctor hom)

/-- The whole left-associated G-111 three-arrow route.
G-113(h) infrastructure definition generated from the two reviewed G-111 compositors. -/
noncomputable def coreFiberPentagonLeftRouteIso
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    coreFiberTransportFunctor ((first ≫ second) ≫ third) ≅
      (coreFiberTransportFunctor first ⋙
        coreFiberTransportFunctor second) ⋙
          coreFiberTransportFunctor third :=
  coreFiberCompositor (first ≫ second) third ≪≫
    Functor.isoWhiskerRight (coreFiberCompositor first second)
      (coreFiberTransportFunctor third)

/-- API characterization of the G-113(h) left whole-pentagon isomorphism at
one package.  Its inputs are the three ambient base arrows and a source
package; no pentagon equation is supplied by the caller. -/
theorem coreFiberPentagonLeftRouteIso_app_trans
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (sourcePackage : CoreFiber firstObject) :
    (coreFiberPentagonLeftRouteIso first second third).app sourcePackage =
      (coreFiberCompositor (first ≫ second) third).app sourcePackage ≪≫
        (Functor.isoWhiskerRight (coreFiberCompositor first second)
          (coreFiberTransportFunctor third)).app sourcePackage := by
  rfl

/-- The whole right-associated G-111 three-arrow route.
G-113(h) infrastructure definition generated from the G-111 associativity cast and compositors. -/
noncomputable def coreFiberPentagonRightRouteIso
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    coreFiberTransportFunctor ((first ≫ second) ≫ third) ≅
      coreFiberTransportFunctor first ⋙
        (coreFiberTransportFunctor second ⋙
          coreFiberTransportFunctor third) :=
  eqToIso (congrArg coreFiberTransportFunctor
      (Category.assoc first second third)) ≪≫
    coreFiberCompositor first (second ≫ third) ≪≫
    Functor.isoWhiskerLeft (coreFiberTransportFunctor first)
      (coreFiberCompositor second third)

/-- The source-unit route is the hom component of its whole G-111 isomorphism.
G-113(h) API bridge theorem; it introduces no premise beyond the ambient arrow and package. -/
theorem coreFiberLeftUnitRouteIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (sourcePackage : CoreFiber source) :
    (coreFiberLeftUnitRouteIso hom).hom.app sourcePackage =
      coreFiberLeftUnitRoute hom sourcePackage := by
  simp [coreFiberLeftUnitRouteIso, coreFiberLeftUnitRoute,
    coreFiberCompositor, coreFiberUnitor]

/-- The target-unit route is the hom component of its whole G-111 isomorphism.
G-113(h) API bridge theorem; it introduces no premise beyond the ambient arrow and package. -/
theorem coreFiberRightUnitRouteIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (sourcePackage : CoreFiber source) :
    (coreFiberRightUnitRouteIso hom).hom.app sourcePackage =
      coreFiberRightUnitRoute hom sourcePackage := by
  simp [coreFiberRightUnitRouteIso, coreFiberRightUnitRoute,
    coreFiberCompositor, coreFiberUnitor]

/-- The left three-arrow route is the hom component of its whole G-111 isomorphism.
G-113(h) API bridge theorem for the reviewed G-111 left pentagon route. -/
theorem coreFiberPentagonLeftRouteIso_hom_app
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (sourcePackage : CoreFiber firstObject) :
    (coreFiberPentagonLeftRouteIso first second third).hom.app sourcePackage =
      coreFiberPentagonLeftRoute first second third sourcePackage := by
  rfl

/-- The right three-arrow route is the hom component of its whole G-111 isomorphism.
G-113(h) API bridge theorem for the reviewed G-111 right pentagon route and associativity cast. -/
theorem coreFiberPentagonRightRouteIso_hom_app
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (sourcePackage : CoreFiber firstObject) :
    (coreFiberPentagonRightRouteIso first second third).hom.app sourcePackage =
      coreFiberPentagonRightRoute first second third sourcePackage := by
  rfl

/-- Equality transport has the reviewed G-111 component.
G-113(h) API bridge theorem; provenance is definitional equality transport. -/
theorem coreFiberTransportEqCastIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    {first second : source ⟶ target} (equality : first = second)
    (sourcePackage : CoreFiber source) :
    (coreFiberTransportEqCastIso equality).hom.app sourcePackage =
      coreFiberTransportEqCast equality sourcePackage := by
  cases equality
  rfl

/-! ## G-112 contravariant routes -/

/-- Equality transport promoted to a natural isomorphism for G-112 reindexing.
G-113(h) infrastructure definition; its data come only from base-arrow equality. -/
noncomputable def semanticGlobalReindexEqCastIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    {first second : source ⟶ target} (equality : first = second) :
    exact_bottom_semantic_global_reindex_functor first ≅
      exact_bottom_semantic_global_reindex_functor second :=
  eqToIso (congrArg exact_bottom_semantic_global_reindex_functor equality)

/-- The whole G-112 source-unit route.
G-113(h) infrastructure definition generated from the reviewed G-112 unitor and compositor. -/
noncomputable def semanticGlobalLeftUnitRouteIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    exact_bottom_semantic_global_reindex_functor hom ≅
      exact_bottom_semantic_global_reindex_functor (𝟙 source ≫ hom) :=
  (Functor.rightUnitor
      (exact_bottom_semantic_global_reindex_functor hom)).symm ≪≫
    Functor.isoWhiskerLeft
      (exact_bottom_semantic_global_reindex_functor hom)
      (exact_bottom_semantic_global_unitor source) ≪≫
    exact_bottom_semantic_global_compositor (𝟙 source) hom

/-- The whole G-112 target-unit route.
G-113(h) infrastructure definition generated from the reviewed G-112 unitor and compositor. -/
noncomputable def semanticGlobalRightUnitRouteIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    exact_bottom_semantic_global_reindex_functor hom ≅
      exact_bottom_semantic_global_reindex_functor (hom ≫ 𝟙 target) :=
  (Functor.leftUnitor
      (exact_bottom_semantic_global_reindex_functor hom)).symm ≪≫
    Functor.isoWhiskerRight
      (exact_bottom_semantic_global_unitor target)
      (exact_bottom_semantic_global_reindex_functor hom) ≪≫
    exact_bottom_semantic_global_compositor hom (𝟙 target)

/-- The whole left-associated G-112 three-arrow route.
G-113(h) infrastructure definition generated from the two reviewed G-112 compositors. -/
noncomputable def semanticGlobalPentagonLeftRouteIso
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    exact_bottom_semantic_global_reindex_functor third ⋙
        (exact_bottom_semantic_global_reindex_functor second ⋙
          exact_bottom_semantic_global_reindex_functor first) ≅
      exact_bottom_semantic_global_reindex_functor
        ((first ≫ second) ≫ third) :=
  Functor.isoWhiskerLeft
      (exact_bottom_semantic_global_reindex_functor third)
      (exact_bottom_semantic_global_compositor first second) ≪≫
    exact_bottom_semantic_global_compositor (first ≫ second) third

/-- The whole right-associated G-112 three-arrow route.
G-113(h) infrastructure definition generated from G-112 compositors and the reversed associativity cast. -/
noncomputable def semanticGlobalPentagonRightRouteIso
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    (exact_bottom_semantic_global_reindex_functor third ⋙
        exact_bottom_semantic_global_reindex_functor second) ⋙
          exact_bottom_semantic_global_reindex_functor first ≅
      exact_bottom_semantic_global_reindex_functor
        ((first ≫ second) ≫ third) :=
  Functor.isoWhiskerRight
      (exact_bottom_semantic_global_compositor second third)
      (exact_bottom_semantic_global_reindex_functor first) ≪≫
    exact_bottom_semantic_global_compositor first (second ≫ third) ≪≫
    semanticGlobalReindexEqCastIso
      (Category.assoc first second third).symm

/-- Equality transport has the reviewed G-112 component.
G-113(h) API bridge theorem; provenance is definitional equality transport. -/
theorem semanticGlobalReindexEqCastIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    {first second : source ⟶ target} (equality : first = second)
    (targetPackage : CoreFiber target) :
    (semanticGlobalReindexEqCastIso equality).hom.app targetPackage =
      exact_bottom_semantic_global_reindex_eq_cast equality targetPackage := by
  cases equality
  rfl

/-- Conjugacy reverses equality transport exactly as required by
contravariant reindexing.  This is a G-113(h) checkpoint theorem generated by
the reviewed adjunction; no cast comparison is accepted as a premise. -/
theorem semanticGlobalTransportEquivalence_eqCast_conjugate
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    {first second : source ⟶ target} (equality : first = second) :
    conjugateIsoEquiv
        (semanticGlobalTransportReindexAdjunction second)
        (semanticGlobalTransportReindexAdjunction first)
        (coreFiberTransportEqCastIso equality) =
      semanticGlobalReindexEqCastIso equality.symm := by
  cases equality
  ext targetPackage
  simp [coreFiberTransportEqCastIso, semanticGlobalReindexEqCastIso,
    conjugateIsoEquiv]

/-- The source-unit route is the hom component of its whole G-112 isomorphism.
G-113(h) API bridge theorem for the reviewed G-112 source-unit route. -/
theorem semanticGlobalLeftUnitRouteIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    (semanticGlobalLeftUnitRouteIso hom).hom.app targetPackage =
      exact_bottom_semantic_global_left_unit_route hom targetPackage := by
  rfl

/-- The target-unit route is the hom component of its whole G-112 isomorphism.
G-113(h) API bridge theorem for the reviewed G-112 target-unit route. -/
theorem semanticGlobalRightUnitRouteIso_hom_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) (targetPackage : CoreFiber target) :
    (semanticGlobalRightUnitRouteIso hom).hom.app targetPackage =
      exact_bottom_semantic_global_right_unit_route hom targetPackage := by
  rfl

/-- The left three-arrow route is the hom component of its whole G-112 isomorphism.
G-113(h) API bridge theorem for the reviewed G-112 left pentagon route. -/
theorem semanticGlobalPentagonLeftRouteIso_hom_app
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    (semanticGlobalPentagonLeftRouteIso first second third).hom.app
        targetPackage =
      exact_bottom_semantic_global_pentagon_left_route
        first second third targetPackage := by
  rfl

/-- The right three-arrow route is the hom component of its whole G-112 isomorphism.
G-113(h) API bridge theorem for the reviewed G-112 right pentagon route and cast. -/
theorem semanticGlobalPentagonRightRouteIso_hom_app
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject)
    (targetPackage : CoreFiber fourthObject) :
    (semanticGlobalPentagonRightRouteIso first second third).hom.app
        targetPackage =
      exact_bottom_semantic_global_pentagon_right_route
        first second third targetPackage := by
  rw [semanticGlobalPentagonRightRouteIso, Iso.trans_hom,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.comp_app,
    semanticGlobalReindexEqCastIso_hom_app]
  rfl

/-! ## Whole-route coherence equations -/

/-- The whole G-111 source-unit route equals its equality cast.
G-113(h) checkpoint theorem consuming the reviewed G-111 source-unit triangle. -/
theorem coreFiberLeftUnitRouteIso_eq_cast
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    coreFiberLeftUnitRouteIso hom =
      coreFiberTransportEqCastIso (Category.id_comp hom) := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  rw [coreFiberLeftUnitRouteIso_hom_app,
    coreFiberTransportEqCastIso_hom_app]
  exact coreFiberCompositor_left_unit hom sourcePackage

/-- The whole G-111 target-unit route equals its equality cast.
G-113(h) checkpoint theorem consuming the reviewed G-111 target-unit triangle. -/
theorem coreFiberRightUnitRouteIso_eq_cast
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    coreFiberRightUnitRouteIso hom =
      coreFiberTransportEqCastIso (Category.comp_id hom) := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  rw [coreFiberRightUnitRouteIso_hom_app,
    coreFiberTransportEqCastIso_hom_app]
  exact coreFiberCompositor_right_unit hom sourcePackage

/-- The two whole G-111 three-arrow routes agree.
G-113(h) checkpoint theorem consuming the reviewed G-111 compositor associativity theorem. -/
theorem coreFiberPentagonRouteIso_eq
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    coreFiberPentagonLeftRouteIso first second third =
      coreFiberPentagonRightRouteIso first second third := by
  apply Iso.ext
  apply NatTrans.ext
  funext sourcePackage
  rw [coreFiberPentagonLeftRouteIso_hom_app,
    coreFiberPentagonRightRouteIso_hom_app]
  exact coreFiberCompositor_assoc first second third sourcePackage

/-- The whole G-112 source-unit route equals its equality cast.
G-113(h) checkpoint theorem consuming the reviewed G-112 source-unit triangle. -/
theorem semanticGlobalLeftUnitRouteIso_eq_cast
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    semanticGlobalLeftUnitRouteIso hom =
      semanticGlobalReindexEqCastIso (Category.id_comp hom).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  rw [semanticGlobalLeftUnitRouteIso_hom_app,
    semanticGlobalReindexEqCastIso_hom_app]
  exact exact_bottom_semantic_global_left_unit_triangle hom targetPackage

/-- The whole G-112 target-unit route equals its equality cast.
G-113(h) checkpoint theorem consuming the reviewed G-112 target-unit triangle. -/
theorem semanticGlobalRightUnitRouteIso_eq_cast
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (hom : source ⟶ target) :
    semanticGlobalRightUnitRouteIso hom =
      semanticGlobalReindexEqCastIso (Category.comp_id hom).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  rw [semanticGlobalRightUnitRouteIso_hom_app,
    semanticGlobalReindexEqCastIso_hom_app]
  exact exact_bottom_semantic_global_right_unit_triangle hom targetPackage

/-- The two whole G-112 three-arrow routes agree.
G-113(h) checkpoint theorem consuming the reviewed G-112 pentagon. -/
theorem semanticGlobalPentagonRouteIso_eq
    {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject fourthObject : ExtractionInstance U}
    (first : firstObject ⟶ secondObject)
    (second : secondObject ⟶ thirdObject)
    (third : thirdObject ⟶ fourthObject) :
    semanticGlobalPentagonLeftRouteIso first second third =
      semanticGlobalPentagonRightRouteIso first second third := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  rw [semanticGlobalPentagonLeftRouteIso_hom_app,
    semanticGlobalPentagonRightRouteIso_hom_app]
  exact exact_bottom_semantic_global_pentagon first second third targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
