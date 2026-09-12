import Mathlib.CategoryTheory.Idempotents.Karoubi
import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateCompositeCoefficient

/-!
# Exact complete-geometry selected factorization

This module proves the first coherent slice of G-122(C).  The target
projector is obtained by applying the actual bottom exact push and right exact
pull functors to the source selector.  Its conjugate, comparison, and Karoubi
isomorphism are then derived from the existing exact `barAlpha`.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory CategoryTheory.Idempotents
open AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 3000000

/-- The complete-geometry target projector generated from the same source
selector as G-116, transported through the actual via-base route. -/
noncomputable def authoredExactBarDAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactViaBaseGeometryAt A z k g ⟶
      authoredExactViaBaseGeometryAt A z k g := by
  classical
  by_cases selected :
      omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)
  · exact (exactGeometryPullFunctor (authoredExactRightInput A)).map
      ((geomFiberTransportFunctor
        A.context.square.semantic.square.bottom).map
          (canonicalGeometryFiberNormalization
            (authoredSouthwestGeometryFiberAt A z k g) selected.2))
  · exact 𝟙 _

/-- On the selected branch, `barD` is the source normalization transported
through the actual bottom-push/right-pull route. -/
theorem authoredExactBarDAt_eq_normalization_route
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactBarDAt A z omega k g =
      (exactGeometryPullFunctor (authoredExactRightInput A)).map
        ((geomFiberTransportFunctor
          A.context.square.semantic.square.bottom).map
            (canonicalGeometryFiberNormalization
              (authoredSouthwestGeometryFiberAt A z k g) selected.2)) := by
  simp [authoredExactBarDAt, selected]

/-- Off the selected branch, `barD` is the identity. -/
theorem authoredExactBarDAt_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as))) :
    authoredExactBarDAt A z omega k g = 𝟙 _ := by
  simp [authoredExactBarDAt, notSelected]

/-- The selected target endomorphism `barD` is idempotent. -/
theorem authoredExactBarDAt_idem
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarDAt A z omega k g ≫
        authoredExactBarDAt A z omega k g =
      authoredExactBarDAt A z omega k g := by
  classical
  by_cases selected :
      omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)
  · rw [authoredExactBarDAt_eq_normalization_route A z omega k g selected,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact canonicalGeometryNormalization_idem _ _
  · rw [authoredExactBarDAt_eq_id A z omega k g selected]
    simp

/-- The coefficient component of `barD` is the identity ring homomorphism. -/
theorem authoredExactBarDAt_coefficient_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarDAt A z omega k g).1.geometry.coefficientHom =
      RingHom.id k := by
  classical
  by_cases selected :
      omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)
  · rw [authoredExactBarDAt_eq_normalization_route A z omega k g selected,
      ]
    change
      (exactGeometryPullMap (authoredExactRightInput A)
        (geomFiberTransportMap A.context.square.semantic.square.bottom
          (canonicalGeometryFiberNormalization
            (authoredSouthwestGeometryFiberAt A z k g)
            selected.2))).1.geometry.coefficientHom = RingHom.id k
    rw [exactGeometryPullMap_coefficientHom,
      geomFiberTransportMap_coefficientHom]
    change
      (canonicalGeometryNormalization
        (authoredSouthwestGeometryFiberAt A z k g).1
        selected.2).geometry.coefficientHom = RingHom.id k
    exact canonicalGeometryNormalization_coefficientHom _ _
  · rw [authoredExactBarDAt_eq_id A z omega k g selected]
    rfl

/-- The source projector conjugate to the selected target projector. -/
noncomputable def authoredExactBarEAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactDirectGeometryAt A z k g ⟶
      authoredExactDirectGeometryAt A z k g :=
  (authoredExactBarAlphaIsoAt A z k g).hom ≫
    authoredExactBarDAt A z omega k g ≫
      (authoredExactBarAlphaIsoAt A z k g).inv

/-- The exact selected comparison `barBeta = barAlpha ≫ barD` in Lean's
composition order. -/
noncomputable def authoredExactBarBetaAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactDirectGeometryAt A z k g ⟶
      authoredExactViaBaseGeometryAt A z k g :=
  (authoredExactBarAlphaIsoAt A z k g).hom ≫
    authoredExactBarDAt A z omega k g

/-- The conjugate source endomorphism `barE` is idempotent. -/
theorem authoredExactBarEAt_idem
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarEAt A z omega k g ≫
        authoredExactBarEAt A z omega k g =
      authoredExactBarEAt A z omega k g := by
  simp only [authoredExactBarEAt, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc
      (authoredExactBarDAt A z omega k g)
      (authoredExactBarDAt A z omega k g)
      (authoredExactBarAlphaIsoAt A z k g).inv,
    authoredExactBarDAt_idem]

/-- The exact selected comparison is fixed by its source projector `barE`. -/
theorem authoredExactBarBetaAt_source_factorization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarEAt A z omega k g ≫
        authoredExactBarBetaAt A z omega k g =
      authoredExactBarBetaAt A z omega k g := by
  simp [authoredExactBarEAt, authoredExactBarBetaAt,
    Category.assoc, authoredExactBarDAt_idem]

/-- The exact selected comparison is fixed by its target projector `barD`. -/
theorem authoredExactBarBetaAt_target_factorization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarBetaAt A z omega k g ≫
        authoredExactBarDAt A z omega k g =
      authoredExactBarBetaAt A z omega k g := by
  simp [authoredExactBarBetaAt, Category.assoc,
    authoredExactBarDAt_idem]

/-- The Karoubi object cut out by the source projector `barE`. -/
noncomputable def authoredExactBarESourceKaroubiAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Karoubi (GeomFiber A.context.square.semantic.square.northeast) where
  X := authoredExactDirectGeometryAt A z k g
  p := authoredExactBarEAt A z omega k g
  idem := authoredExactBarEAt_idem A z omega k g

/-- The Karoubi object cut out by the target projector `barD`. -/
noncomputable def authoredExactBarDTargetKaroubiAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Karoubi (GeomFiber A.context.square.semantic.square.northeast) where
  X := authoredExactViaBaseGeometryAt A z k g
  p := authoredExactBarDAt A z omega k g
  idem := authoredExactBarDAt_idem A z omega k g

/-- The actual selected comparison is an isomorphism between its two Karoubi
images; its inverse is `barD ≫ barAlpha⁻¹`. -/
noncomputable def authoredExactBarBetaKaroubiIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarESourceKaroubiAt A z omega k g ≅
      authoredExactBarDTargetKaroubiAt A z omega k g where
  hom :=
    { f := authoredExactBarBetaAt A z omega k g
      comm := by
        change authoredExactBarEAt A z omega k g ≫
            authoredExactBarBetaAt A z omega k g ≫
              authoredExactBarDAt A z omega k g =
          authoredExactBarBetaAt A z omega k g
        rw [authoredExactBarBetaAt_target_factorization,
          authoredExactBarBetaAt_source_factorization] }
  inv :=
    { f := authoredExactBarDAt A z omega k g ≫
        (authoredExactBarAlphaIsoAt A z k g).inv
      comm := by
        change authoredExactBarDAt A z omega k g ≫
            (authoredExactBarDAt A z omega k g ≫
              (authoredExactBarAlphaIsoAt A z k g).inv) ≫
                authoredExactBarEAt A z omega k g =
          authoredExactBarDAt A z omega k g ≫
            (authoredExactBarAlphaIsoAt A z k g).inv
        simp only [authoredExactBarEAt, Category.assoc,
          Iso.inv_hom_id_assoc]
        rw [← Category.assoc
            (authoredExactBarDAt A z omega k g)
            (authoredExactBarDAt A z omega k g)
            (authoredExactBarAlphaIsoAt A z k g).inv,
          authoredExactBarDAt_idem,
          ← Category.assoc
            (authoredExactBarDAt A z omega k g)
            (authoredExactBarDAt A z omega k g)
            (authoredExactBarAlphaIsoAt A z k g).inv,
          authoredExactBarDAt_idem] }
  hom_inv_id := by
    apply Karoubi.Hom.ext
    change authoredExactBarBetaAt A z omega k g ≫
        (authoredExactBarDAt A z omega k g ≫
          (authoredExactBarAlphaIsoAt A z k g).inv) =
      authoredExactBarEAt A z omega k g
    simp only [authoredExactBarBetaAt, authoredExactBarEAt,
      Category.assoc]
    rw [← Category.assoc
        (authoredExactBarDAt A z omega k g)
        (authoredExactBarDAt A z omega k g)
        (authoredExactBarAlphaIsoAt A z k g).inv,
      authoredExactBarDAt_idem]
  inv_hom_id := by
    apply Karoubi.Hom.ext
    change (authoredExactBarDAt A z omega k g ≫
        (authoredExactBarAlphaIsoAt A z k g).inv) ≫
          authoredExactBarBetaAt A z omega k g =
      authoredExactBarDAt A z omega k g
    simp only [authoredExactBarBetaAt, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [authoredExactBarDAt_idem]

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
