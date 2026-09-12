import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification
import ResearchLean.AG.RealizationComparisonIdempotents.G116KaroubiExchange

/-!
# Karoubi alignment of the exact complete-geometry comparison

This module projects the actual complete-geometry Karoubi isomorphism of
G-122(C) to the northeast core fiber.  Endpoint comparison isomorphisms then
identify that projected arrow with G-116's existing Karoubi comparison.  The
same object is finally placed in G-119's core comparison category and its
raw-idempotent exchange normalization.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence TransportCoherence
open DoctrineFiberProduct RealizationComparisonIdempotents

set_option maxHeartbeats 6000000

/-- Karoubi extension of the northeast geometry-fiber projection. -/
noncomputable def authoredExactNortheastKaroubiProjection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) :
    Karoubi (GeomFiber A.context.square.semantic.square.northeast) ⥤
      Karoubi (CoreFiber A.context.square.semantic.square.northeast) :=
  (functorExtension₂ _ _).obj
    (geometryFiberProjection A.context.square.semantic.square.northeast)

/-- Projection of the actual complete-geometry Karoubi isomorphism. -/
noncomputable def authoredExactBarBetaProjectedKaroubiIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarESourceKaroubiAt A z omega k g) ≅
      (authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarDTargetKaroubiAt A z omega k g) :=
  (authoredExactNortheastKaroubiProjection A).mapIso
    (authoredExactBarBetaKaroubiIsoAt A z omega k g)

/-- Evaluation of the projected source projector. -/
@[simp] theorem authoredExactProjectedBarESource_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((authoredExactNortheastKaroubiProjection A).obj
      (authoredExactBarESourceKaroubiAt A z omega k g)).p =
        (geometryFiberProjection
          A.context.square.semantic.square.northeast).map
            (authoredExactBarEAt A z omega k g) := rfl

/-- Evaluation of the projected target projector. -/
@[simp] theorem authoredExactProjectedBarDTarget_p
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    ((authoredExactNortheastKaroubiProjection A).obj
      (authoredExactBarDTargetKaroubiAt A z omega k g)).p =
        (geometryFiberProjection
          A.context.square.semantic.square.northeast).map
            (authoredExactBarDAt A z omega k g) := rfl

/-- Evaluation of the projected actual Karoubi comparison. -/
@[simp] theorem authoredExactBarBetaProjectedKaroubiIsoAt_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom.f =
      (geometryFiberProjection
        A.context.square.semantic.square.northeast).map
          (authoredExactBarBetaAt A z omega k g) := rfl

/-- Restrict an underlying endpoint isomorphism to compatible Karoubi
projectors. -/
private noncomputable def karoubiIsoOfUnderlyingIso
    {C : Type u} [Category.{v} C] (P Q : Karoubi C)
    (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hInv : Q.p ≫ e.inv = e.inv ≫ P.p := by
    apply (cancel_mono e.hom).1
    calc
      (Q.p ≫ e.inv) ≫ e.hom = Q.p := by simp
      _ = e.inv ≫ (e.hom ≫ Q.p) := by simp
      _ = e.inv ≫ (P.p ≫ e.hom) := by rw [h]
      _ = (e.inv ≫ P.p) ≫ e.hom := by simp
  refine
    { hom :=
        { f := P.p ≫ e.hom
          comm := by
            simp only [← Category.assoc]
            rw [P.idem, h]
            simp only [Category.assoc, Q.idem] }
      inv :=
        { f := Q.p ≫ e.inv
          comm := by
            simp only [← Category.assoc]
            rw [Q.idem, hInv]
            simp only [Category.assoc, P.idem] }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [h]
    simp only [Category.assoc]
    rw [← Category.assoc Q.p Q.p e.inv, Q.idem, hInv]
    simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [hInv]
    simp only [Category.assoc]
    rw [← Category.assoc P.p P.p e.hom, P.idem, h]
    simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]

/-- The projected target projector is G-116's existing target image after the
generated endpoint support-core isomorphism. -/
noncomputable def authoredExactBarDTargetKaroubiProjectionIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarDTargetKaroubiAt A z omega k g) ≅
      authoredDiagnosticImageTargetKaroubi A omega z :=
  karoubiIsoOfUnderlyingIso _ _
    (authoredExactViaBaseSupportCoreIsoAt A z k g)
    (by
      change
        (geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarDAt A z omega k g) ≫
            (authoredExactViaBaseSupportCoreIsoAt A z k g).hom =
          (authoredExactViaBaseSupportCoreIsoAt A z k g).hom ≫
            (authoredDiagnosticImageTargetKaroubi A omega z).p
      rw [authoredDiagnosticImageTargetKaroubi_p]
      exact authoredExactBarDAt_projection A z omega k g)

/-- The projected conjugate source projector is G-116's existing source image
after the generated endpoint support-core isomorphism. -/
noncomputable def authoredExactBarESourceKaroubiProjectionIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarESourceKaroubiAt A z omega k g) ≅
      authoredDiagnosticImageSourceKaroubi A omega z :=
  karoubiIsoOfUnderlyingIso _ _
    (authoredExactDirectSupportCoreIsoAt A z k g)
    (by
      have hAlphaInv :
          (geometryFiberProjection
              A.context.square.semantic.square.northeast).map
                (authoredExactBarAlphaIsoAt A z k g).inv ≫
              (authoredExactDirectSupportCoreIsoAt A z k g).hom =
            (authoredExactViaBaseSupportCoreIsoAt A z k g).hom ≫
              inv ((authoredSupportCanonicalMate A.context).app z) := by
        apply (cancel_epi ((geometryFiberProjection
          A.context.square.semantic.square.northeast).map
            (authoredExactBarAlphaIsoAt A z k g).hom)).1
        rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
        rw [(geometryFiberProjection
          A.context.square.semantic.square.northeast).map_id]
        rw [Category.id_comp]
        rw [← Category.assoc, authoredExactBarAlphaIsoAt_projection]
        simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      change
        (geometryFiberProjection
            A.context.square.semantic.square.northeast).map
              (authoredExactBarEAt A z omega k g) ≫
            (authoredExactDirectSupportCoreIsoAt A z k g).hom =
          (authoredExactDirectSupportCoreIsoAt A z k g).hom ≫
            (authoredDiagnosticImageSourceKaroubi A omega z).p
      rw [authoredDiagnosticImageSourceKaroubi_p]
      rw [show authoredExactBarEAt A z omega k g =
          authoredExactBarBetaAt A z omega k g ≫
            (authoredExactBarAlphaIsoAt A z k g).inv by
        simp [authoredExactBarEAt, authoredExactBarBetaAt,
          Category.assoc]]
      rw [Functor.map_comp, Category.assoc, hAlphaInv]
      rw [← Category.assoc,
        authoredExactBarBetaAt_projection A z omega k g]
      simp only [Category.assoc])

/-- Evaluation of the restricted source endpoint comparison. -/
@[simp] theorem authoredExactBarESourceKaroubiProjectionIsoAt_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarESourceKaroubiProjectionIsoAt A z omega k g).hom.f =
      ((authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarESourceKaroubiAt A z omega k g)).p ≫
          (authoredExactDirectSupportCoreIsoAt A z k g).hom := rfl

/-- Evaluation of the restricted target endpoint comparison. -/
@[simp] theorem authoredExactBarDTargetKaroubiProjectionIsoAt_hom_f
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (authoredExactBarDTargetKaroubiProjectionIsoAt A z omega k g).hom.f =
      ((authoredExactNortheastKaroubiProjection A).obj
        (authoredExactBarDTargetKaroubiAt A z omega k g)).p ≫
          (authoredExactViaBaseSupportCoreIsoAt A z k g).hom := rfl

/-- G-122(C): after core projection, the actual complete-geometry Karoubi
comparison is isomorphic, as an arrow with both endpoints displayed, to the
existing G-116 Karoubi comparison. -/
noncomputable def authoredExactBarBetaKaroubiProjectionAlignmentAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Arrow.mk (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom ≅
      authoredDiagnosticKaroubiComparison A omega z :=
  Arrow.isoMk
    (authoredExactBarESourceKaroubiProjectionIsoAt A z omega k g)
    (authoredExactBarDTargetKaroubiProjectionIsoAt A z omega k g)
    (by
      apply Karoubi.Hom.ext
      have projection := authoredExactBarBetaAt_projection A z omega k g
      have precomposed := congrArg
        (fun morphism =>
          ((authoredExactNortheastKaroubiProjection A).obj
            (authoredExactBarESourceKaroubiAt A z omega k g)).p ≫ morphism)
        projection
      have sourceAbsorb := Karoubi.p_comp
        (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom
      have targetAbsorb := Karoubi.comp_p
        (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom
      have sourceAbsorb' :
          ((authoredExactNortheastKaroubiProjection A).obj
              (authoredExactBarESourceKaroubiAt A z omega k g)).p ≫
                (geometryFiberProjection
                  A.context.square.semantic.square.northeast).map
                    (authoredExactBarBetaAt A z omega k g) =
            (geometryFiberProjection
              A.context.square.semantic.square.northeast).map
                (authoredExactBarBetaAt A z omega k g) := by
        simpa only [authoredExactBarBetaProjectedKaroubiIsoAt_hom_f] using
          sourceAbsorb
      have targetAbsorb' :
          (geometryFiberProjection
              A.context.square.semantic.square.northeast).map
                (authoredExactBarBetaAt A z omega k g) ≫
              ((authoredExactNortheastKaroubiProjection A).obj
                (authoredExactBarDTargetKaroubiAt A z omega k g)).p =
            (geometryFiberProjection
              A.context.square.semantic.square.northeast).map
                (authoredExactBarBetaAt A z omega k g) := by
        simpa only [authoredExactBarBetaProjectedKaroubiIsoAt_hom_f] using
          targetAbsorb
      simpa only [Karoubi.comp_f, Arrow.mk_hom,
        authoredExactBarESourceKaroubiProjectionIsoAt_hom_f,
        authoredExactBarDTargetKaroubiProjectionIsoAt_hom_f,
        authoredExactBarBetaProjectedKaroubiIsoAt_hom_f,
        authoredDiagnosticKaroubiComparison_hom_f,
        ← Category.assoc, sourceAbsorb', targetAbsorb'] using precomposed.symm)

/-- G-119 placement: forgetting the projected exact Karoubi comparison to the
core-package comparison category gives the existing G-116 object there. -/
noncomputable def authoredExactBarBetaG119CoreComparisonIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (coreFiberComparisonInclusion
      A.context.square.semantic.square.northeast).obj
        (Arrow.mk
          (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom) ≅
      authoredDiagnosticCoreComparison A omega z :=
  (coreFiberComparisonInclusion
    A.context.square.semantic.square.northeast).mapIso
      (authoredExactBarBetaKaroubiProjectionAlignmentAt A z omega k g)

/-- G-119 exchange position: the projected actual comparison is the same
comparison object as the normalization of G-119's raw-idempotent square. -/
noncomputable def authoredExactBarBetaG119ExchangeIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Arrow.mk (authoredExactBarBetaProjectedKaroubiIsoAt A z omega k g).hom ≅
      karoubiArrowToArrowKaroubiObj
        (authoredDiagnosticRawIdempotentComparison A omega z) :=
  authoredExactBarBetaKaroubiProjectionAlignmentAt A z omega k g ≪≫
    eqToIso (authoredDiagnosticRawIdempotentComparison_exchange A omega z).symm

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
