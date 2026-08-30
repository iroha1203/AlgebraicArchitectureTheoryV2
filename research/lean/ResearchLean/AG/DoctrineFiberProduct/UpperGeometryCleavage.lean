import ResearchLean.AG.DoctrineFiberProduct.CartesianTarget
import ResearchLean.AG.DoctrineFiberProduct.RefinementBaseChange.RealizedSupport
import ResearchLean.AG.DoctrineFiberProduct.RefinementGeometry
import ResearchLean.AG.GeometryTransport.Basic

/-!
# Geometry pullback for the explicit inverse-package lifts

This G-115-local module pulls a requested target geometry package back along
the complete upper equivalence of the two explicit inverse-package
constructions. It asks for no caller-supplied `HGeom` and leaves the completed
G-112 and G-114 APIs unchanged.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport

namespace UpperGeometryCleavage

private abbrev upperContextFunctor {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :=
  f.equationTransport.contextEquivalence.functor

private abbrev upperContextInverse {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :=
  f.equationTransport.contextEquivalence.inverse

private def upperContextMap {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q)
    (W : Site.ArchCtx P.object) : Site.ArchCtx Q.object :=
  ((upperContextFunctor f).obj ⟨W⟩).ctx

private def upperContextBackwardMap {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q)
    (W : Site.ArchCtx Q.object) : Site.ArchCtx P.object :=
  ((upperContextInverse f).obj ⟨W⟩).ctx

private def pullCoverage {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (G : GeometryPackage.{u, v} U)
    (f : SignedExactCoreReadingHom P G.core) :
    Site.CoverageRequirements P.object P.equationSystem
      P.algebra.signatureReading where
  requiredSupport atom :=
    G.geometry.requirements.requiredSupport (f.atomEquiv atom)
  requiredEquationCoordinate coordinate :=
    G.geometry.requirements.requiredEquationCoordinate
      (⟨f.equationMap coordinate.1.1,
          (f.required_iff coordinate.1.1).mp coordinate.1.2⟩,
        f.atomEquiv coordinate.2)
  selectedViolationWitness coordinate :=
    G.geometry.requirements.selectedViolationWitness
      (f.equationEquiv coordinate.1, f.atomEquiv coordinate.2)
  requiredAxis axis := G.geometry.requirements.requiredAxis (f.axisMap axis)
  supportVisibleOn W atom := G.geometry.requirements.supportVisibleOn
    (upperContextMap f W) (f.atomEquiv atom)
  equationCoordinateVisibleOn W coordinate :=
    G.geometry.requirements.equationCoordinateVisibleOn
      (upperContextMap f W)
      (⟨f.equationMap coordinate.1.1,
          (f.required_iff coordinate.1.1).mp coordinate.1.2⟩,
        f.atomEquiv coordinate.2)
  violationWitnessVisibleOn W coordinate :=
    G.geometry.requirements.violationWitnessVisibleOn
      (upperContextMap f W)
      (f.equationEquiv coordinate.1, f.atomEquiv coordinate.2)
  axisReadableOn W axis := G.geometry.requirements.axisReadableOn
    (upperContextMap f W) (f.axisMap axis)
  boundaryVisibleOn W V := G.geometry.requirements.boundaryVisibleOn
    (upperContextMap f W) (upperContextMap f V)

private noncomputable def pullOverlap {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (G : GeometryPackage.{u, v} U)
    (f : SignedExactCoreReadingHom P G.core) :
    Site.ContextOverlapPullback P.contextPreorder where
  overlap base left right := upperContextBackwardMap f
    (G.geometry.overlap.overlap
      (upperContextMap f base) (upperContextMap f left) (upperContextMap f right))
  overlap_le_left {base left right} hl hr := by
    apply P.contextPreorder.trans
    · exact ((upperContextInverse f).map
        (homOfLE (G.geometry.overlap.overlap_le_left
          ((upperContextFunctor f).map (homOfLE hl)).le
          ((upperContextFunctor f).map (homOfLE hr)).le))).le
    · exact (f.equationTransport.contextEquivalence.unitIso.inv.app ⟨left⟩).le
  overlap_le_right {base left right} hl hr := by
    apply P.contextPreorder.trans
    · exact ((upperContextInverse f).map
        (homOfLE (G.geometry.overlap.overlap_le_right
          ((upperContextFunctor f).map (homOfLE hl)).le
          ((upperContextFunctor f).map (homOfLE hr)).le))).le
    · exact (f.equationTransport.contextEquivalence.unitIso.inv.app ⟨right⟩).le
  overlap_le_base {base left right} hl hr := by
    apply P.contextPreorder.trans
    · exact ((upperContextInverse f).map
        (homOfLE (G.geometry.overlap.overlap_le_base
          ((upperContextFunctor f).map (homOfLE hl)).le
          ((upperContextFunctor f).map (homOfLE hr)).le))).le
    · exact (f.equationTransport.contextEquivalence.unitIso.inv.app ⟨base⟩).le
  overlap_lift {base left right X} hl hr hXl hXr := by
    apply P.contextPreorder.trans
    · exact (f.equationTransport.contextEquivalence.unitIso.hom.app ⟨X⟩).le
    · exact ((upperContextInverse f).map
        (homOfLE (G.geometry.overlap.overlap_lift
          ((upperContextFunctor f).map (homOfLE hl)).le
          ((upperContextFunctor f).map (homOfLE hr)).le
          ((upperContextFunctor f).map (homOfLE hXl)).le
          ((upperContextFunctor f).map (homOfLE hXr)).le))).le

private noncomputable def pullSelectedGeometry {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (G : GeometryPackage.{u, v} U)
    (f : SignedExactCoreReadingHom P G.core) : Site.SelectedGeometryReading P where
  requirements := pullCoverage G f
  overlap := pullOverlap G f

private abbrev upperContextInverseOf {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (f : SignedExactCoreReadingHom P Q) :=
  f.equationTransport.contextEquivalence.inverse

/-- Reindex raw geometry using only the complete upper equivalence.

This G-115-local variant is needed for the generated backward upper map: that
map has no lower pointed morphism and therefore cannot be packaged as a
`PackageTotalHom`. -/
noncomputable def rawReindexUpper {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (sourceGeometry : Site.SelectedGeometryReading P)
    (targetGeometry : Site.SelectedGeometryReading Q)
    {k : Type v} [CommRing k]
    (f : SignedExactCoreReadingHom P Q)
    (raw : LawAlgebra.RawAmbientRestrictionSystem
      sourceGeometry.toAATSite k) :
    LawAlgebra.RawAmbientRestrictionSystem
      targetGeometry.toAATSite k where
  coordFamily W := copyCoordinateFamily (V := W.ctx)
    (raw.coordFamily ((upperContextInverseOf f).obj W))
  relationFamily W := copyRelationFamily (V := W.ctx)
    (raw.relationFamily ((upperContextInverseOf f).obj W))
  restrictionStable {X Y} h := by
    let source := raw.restrictionStable ((upperContextInverseOf f).map h)
    exact {
      restriction := { variableImage := source.restriction.variableImage }
      maps_JStruct := source.maps_JStruct
    }
  identity_polynomialMap X := by
    have hmap : (upperContextInverseOf f).map (𝟙 X) =
        𝟙 ((upperContextInverseOf f).obj X) := by simp
    cases hmap
    exact raw.identity_polynomialMap ((upperContextInverseOf f).obj X)
  composition_polynomialMap h k := by
    have hmap : (upperContextInverseOf f).map (h ≫ k) =
        (upperContextInverseOf f).map h ≫
          (upperContextInverseOf f).map k := by simp
    cases hmap
    exact raw.composition_polynomialMap
      ((upperContextInverseOf f).map h) ((upperContextInverseOf f).map k)

@[simp] theorem rawReindexUpper_id {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (geometry : Site.SelectedGeometryReading P)
    {k : Type v} [CommRing k]
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometry.toAATSite k) :
    rawReindexUpper geometry geometry (SignedExactCoreReadingHom.refl P) raw = raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

theorem rawReindexUpper_comp {U : AtomCarrier.{u}}
    {P Q R : AATCorePackage U}
    (geometryP : Site.SelectedGeometryReading P)
    (geometryQ : Site.SelectedGeometryReading Q)
    (geometryR : Site.SelectedGeometryReading R)
    {k : Type v} [CommRing k]
    (f : SignedExactCoreReadingHom P Q)
    (g : SignedExactCoreReadingHom Q R)
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometryP.toAATSite k) :
    rawReindexUpper geometryP geometryR (f.comp g) raw =
      rawReindexUpper geometryQ geometryR g
        (rawReindexUpper geometryP geometryQ f raw) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Reindexing an upper raw system commutes with coefficient base change. -/
theorem rawReindexUpper_baseChange {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (geometryP : Site.SelectedGeometryReading P)
    (geometryQ : Site.SelectedGeometryReading Q)
    {k k' : Type v} [CommRing k] [CommRing k']
    (f : SignedExactCoreReadingHom P Q)
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometryP.toAATSite k)
    (coeff : k →+* k') :
    (rawReindexUpper geometryP geometryQ f raw).baseChange coeff =
      rawReindexUpper geometryP geometryQ f (raw.baseChange coeff) := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

theorem rawReindexUpper_cancel {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U}
    (geometryP : Site.SelectedGeometryReading P)
    (geometryQ : Site.SelectedGeometryReading Q)
    {k : Type v} [CommRing k]
    (forward : SignedExactCoreReadingHom P Q)
    (backward : SignedExactCoreReadingHom Q P)
    (hcancel : backward.comp forward = SignedExactCoreReadingHom.refl Q)
    (raw : LawAlgebra.RawAmbientRestrictionSystem geometryQ.toAATSite k) :
    rawReindexUpper geometryP geometryQ forward
        (rawReindexUpper geometryQ geometryP backward raw) = raw := by
  rw [← rawReindexUpper_comp, hcancel, rawReindexUpper_id]

private theorem rawReindex_eq_rawReindexUpper {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : PackageTotalHom G.core H.core)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    rawReindex f raw = rawReindexUpper G.geometry H.geometry f.upper raw := rfl

private theorem refinementRawReindex_eq_rawReindexUpper {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U} {k : Type v} [CommRing k]
    (f : RefinementGeometryBaseHom G H)
    (raw : LawAlgebra.RawAmbientRestrictionSystem G.site k) :
    refinementRawReindex f raw =
      rawReindexUpper G.geometry H.geometry f.upper raw := rfl

private noncomputable def pullRaw {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (G : GeometryPackage.{u, v} U)
    (forward : SignedExactCoreReadingHom P G.core)
    (backward : SignedExactCoreReadingHom G.core P) :
    LawAlgebra.RawAmbientRestrictionSystem
      (pullSelectedGeometry G forward).toAATSite G.Coefficient :=
  rawReindexUpper G.geometry (pullSelectedGeometry G forward) backward G.raw

private noncomputable def pullPackage {U : AtomCarrier.{u}}
    {P : AATCorePackage U} (G : GeometryPackage.{u, v} U)
    (forward : SignedExactCoreReadingHom P G.core)
    (backward : SignedExactCoreReadingHom G.core P) : GeometryPackage.{u, v} U where
  core := P
  geometry := pullSelectedGeometry G forward
  Coefficient := G.Coefficient
  coefficientCommRing := G.coefficientCommRing
  raw := pullRaw G forward backward

/-- Target geometry pulled back to the explicit exact inverse-package lift. -/
noncomputable def exactSourceGeometry {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) : GeometryPackage.{u, v} U :=
  pullPackage G
    (inverseCorePackageForwardUpper G.core f)
    (inverseCorePackageBackwardUpper G.core f)

/-- The generated exact pullback retains the target coefficient ring. -/
theorem exactSourceGeometry_coefficient_eq {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    (exactSourceGeometry G f).Coefficient = G.Coefficient :=
  rfl

/-- The exact pullback's coefficient ring maps canonically back from the target. -/
noncomputable def exactSourceCoefficientBackwardHom {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    G.Coefficient →+* (exactSourceGeometry G f).Coefficient :=
  RingHom.id G.Coefficient

/-- The exact pullback raw system is the backward upper reindexing together
with its canonical coefficient identification. -/
theorem exactSourceGeometry_raw_backward {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    (exactSourceGeometry G f).raw =
      rawReindexUpper G.geometry (exactSourceGeometry G f).geometry
        (inverseCorePackageBackwardUpper G.core f)
        (G.raw.baseChange (exactSourceCoefficientBackwardHom G f)) := by
  unfold exactSourceGeometry pullPackage pullRaw
  unfold exactSourceCoefficientBackwardHom
  rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]

@[simp] theorem exactSourceGeometry_core {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    (exactSourceGeometry G f).core = inverseCorePackage G.core f := rfl

/-- The exact forward leg recovers the target raw system strictly. -/
theorem exactSourceGeometry_raw_forward {U : AtomCarrier.{u}}
    {X : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (f : X ⟶ packagePoint G.core) :
    G.raw = rawTransport
      (G := exactSourceGeometry G f) (H := G)
      (inverseCorePackageHom G.core f) (RingHom.id G.Coefficient) := by
  unfold rawTransport
  have hid :
      (exactSourceGeometry G f).raw.baseChange (RingHom.id G.Coefficient) =
        (exactSourceGeometry G f).raw :=
    LawAlgebra.RawAmbientRestrictionSystem.baseChange_id _
  rw [hid, rawReindex_eq_rawReindexUpper]
  exact (rawReindexUpper_cancel
    (exactSourceGeometry G f).geometry G.geometry
    (inverseCorePackageForwardUpper G.core f)
    (inverseCorePackageBackwardUpper G.core f)
    (inverseCorePackageBackward_comp_forward G.core f) G.raw).symm

/-- Target geometry pulled back to the realized-refinement inverse package.
The supplied fiber equality is used directly when selecting transport data, so
the target coefficient carrier and ring instance remain definitionally fixed. -/
noncomputable def refinementSourceGeometry {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) : GeometryPackage.{u, v} U := by
  let data := selectedTransportDataOfRealizedReflection r condition ⟨G.core, hG⟩
  exact pullPackage G
    (SelectedRefinementTransport.inverseCorePackageForwardUpper G.core data)
    (SelectedRefinementTransport.inverseCorePackageBackwardUpper G.core data)

/-- The generated realized-refinement pullback retains the target coefficient ring. -/
theorem refinementSourceGeometry_coefficient_eq {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementSourceGeometry G r condition hG).Coefficient = G.Coefficient := by
  subst Y
  rfl

/-- The realized-refinement pullback's coefficient ring maps canonically back
from the target. -/
noncomputable def refinementSourceCoefficientBackwardHom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    G.Coefficient →+* (refinementSourceGeometry G r condition hG).Coefficient := by
  subst Y
  exact RingHom.id G.Coefficient

/-- Complete backward upper map with the generated refinement source as its
literal codomain. -/
noncomputable def refinementSourceBackwardUpper {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    SignedExactCoreReadingHom G.core
      (refinementSourceGeometry G r condition hG).core := by
  subst Y
  exact SelectedRefinementTransport.inverseCorePackageBackwardUpper G.core
    (selectedTransportDataOfRealizedReflection r condition ⟨G.core, rfl⟩)

/-- The realized-refinement pullback raw system is the backward upper
reindexing together with its canonical coefficient identification. -/
theorem refinementSourceGeometry_raw_backward {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementSourceGeometry G r condition hG).raw =
      rawReindexUpper G.geometry
        (refinementSourceGeometry G r condition hG).geometry
        (refinementSourceBackwardUpper G r condition hG)
        (G.raw.baseChange
          (refinementSourceCoefficientBackwardHom G r condition hG)) := by
  subst Y
  unfold refinementSourceGeometry refinementSourceCoefficientBackwardHom
    refinementSourceBackwardUpper pullPackage pullRaw
  rw [LawAlgebra.RawAmbientRestrictionSystem.baseChange_id]

@[simp] theorem refinementSourceGeometry_core {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementSourceGeometry G r condition hG).core =
      SelectedRefinementTransport.inverseCorePackage G.core
        (selectedTransportDataOfRealizedReflection r condition
          ⟨G.core, hG⟩) := by
  subst Y
  rfl

/-- The complete refinement base hom generated from realized reflection. -/
noncomputable def refinementBaseHom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    RefinementGeometryBaseHom
      (refinementSourceGeometry G r condition hG) G := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition ⟨G.core, rfl⟩
  exact {
    base := r
    upper := SelectedRefinementTransport.inverseCorePackageForwardUpper G.core data
    atomEquiv_eq := rfl
  }

/-- The generated refinement geometry uses the literal identity on the
definitionally retained target coefficient ring. -/
noncomputable def refinementCoefficientHom {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementSourceGeometry G r condition hG).Coefficient →+*
      G.Coefficient :=
  RingHom.id G.Coefficient

/-- The refinement forward leg recovers the target raw system strictly. -/
theorem refinementSourceGeometry_raw_forward {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (G : GeometryPackage.{u, v} U)
    (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    G.raw = refinementRawTransport
      (refinementBaseHom G r condition hG)
      (refinementCoefficientHom G r condition hG) := by
  subst Y
  unfold refinementRawTransport
  simp only [refinementCoefficientHom]
  have hid :
      (refinementSourceGeometry G r condition rfl).raw.baseChange
          (RingHom.id G.Coefficient) =
        (refinementSourceGeometry G r condition rfl).raw :=
    LawAlgebra.RawAmbientRestrictionSystem.baseChange_id _
  rw [hid, refinementRawReindex_eq_rawReindexUpper]
  let data := selectedTransportDataOfRealizedReflection r condition ⟨G.core, rfl⟩
  exact (rawReindexUpper_cancel
    (refinementSourceGeometry G r condition rfl).geometry G.geometry
    (SelectedRefinementTransport.inverseCorePackageForwardUpper G.core data)
    (SelectedRefinementTransport.inverseCorePackageBackwardUpper G.core data)
    (SelectedRefinementTransport.inverseCorePackageBackward_comp_forward G.core data)
    G.raw).symm

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
