import ResearchLean.AG.LocalSemanticReconstruction.IndependentRepresentativeHomReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentExplicitHomAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Noninvertible coefficient controls for both geometry Hom readings

The same core and selected geometry carry a one-coordinate raw relation X=0
over arbitrary coefficient rings. Every directed coefficient homomorphism
acts on these packages. In particular the projection from the integer product
ring has a nonzero kernel and survives both primitive Hom round trips.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction LawAlgebra Site

variable {U : AtomCarrier.{u}}

/-- A complete fixture with fixed core and geometry and the genuine single relation X=0. -/
def unitPackage (P : AATCorePackage U) (g : SelectedGeometryReading P)
    (k : Type v) [CommRing k] : GeometryPackage.{u, v} U where
  core := P
  geometry := g
  Coefficient := k
  coefficientCommRing := inferInstance
  raw := IndependentRawLocal.unitRaw g.toAATSite k

/-- Every directed coefficient map preserves the fixture's raw coordinate and relation presentations. -/
def coefficientRawMap (P : AATCorePackage U) (g : SelectedGeometryReading P)
    {k l : Type v} [CommRing k] [CommRing l] (h : k →+* l) :
    RawAmbientRestrictionSystemExactMapAgainst g.toAATSite g.toAATSite
      (𝟭 g.toAATSite.category) h
      (IndependentRawLocal.unitRaw g.toAATSite k) (IndependentRawLocal.unitRaw g.toAATSite l) where
  coordinate W := CoordinateFamilyExactEquiv.refl
    ((IndependentRawLocal.unitRaw g.toAATSite k).coordFamily W)
  relation _ :=
    { relationEquiv := Equiv.refl _
      polynomial_eq _ := by
        simp [IndependentRawLocal.unitRaw, StructuralRelationFamily.baseChange,
          CoordinateFamilyExactEquiv.polynomialEquiv, CoordinateFamilyExactEquiv.refl] }
  restriction_polynomial _ _ := by
    simp [IndependentRawLocal.unitRaw, TypedCoordinateRestriction.polynomialMap]
    rfl

/-- Coefficient change keeps every coverage predicate and every point argument fixed. -/
def coefficientCoverage (P : AATCorePackage U) (g : SelectedGeometryReading P)
    (k l : Type v) [CommRing k] [CommRing l] :
    CoverageTransport (unitPackage P g k) (unitPackage P g l) (PackageTotalHom.id P) where
  requiredSupport _ := _root_.id
  requiredEquationCoordinate _ := _root_.id
  selectedViolationWitness _ := _root_.id
  requiredAxis _ := _root_.id
  supportVisibleOn _ _ := _root_.id
  equationCoordinateVisibleOn _ _ := _root_.id
  violationWitnessVisibleOn _ _ := _root_.id
  axisReadableOn _ _ := _root_.id
  boundaryVisibleOn _ _ := _root_.id

/-- Coefficient change leaves the selected overlap context fixed. -/
def coefficientOverlap (P : AATCorePackage U) (g : SelectedGeometryReading P)
    (k l : Type v) [CommRing k] [CommRing l] :
    OverlapTransport (unitPackage P g k) (unitPackage P g l) (PackageTotalHom.id P) where
  overlapIso _ _ _ := Iso.refl _

/-- Explicit context-action Homs retain arbitrary directed coefficient changes. -/
def explicitCoefficientHom (P : AATCorePackage U) (g : SelectedGeometryReading P)
    {k l : Type v} [CommRing k] [CommRing l] (h : k →+* l) :
    ExplicitExactGeometryHom (unitPackage P g k) (unitPackage P g l) where
  base := PackageTotalHom.id P
  coverage := coefficientCoverage P g k l
  overlap := coefficientOverlap P g k l
  coefficientHom := h
  raw := coefficientRawMap P g h
  realization := ExplicitRealizationTransportSupply.id P

/-- The representative raw condition follows from the primitive responses for the same coefficient change. -/
theorem unitPackage_raw_eq (P : AATCorePackage U) (g : SelectedGeometryReading P)
    {k l : Type v} [CommRing k] [CommRing l] (h : k →+* l) :
    (unitPackage P g l).raw = rawTransport
      (G := unitPackage P g k) (H := unitPackage P g l) (PackageTotalHom.id P) h := by
  apply (IndependentRepresentativeHom.raw_eq_iff_points
    (G := unitPackage P g k) (H := unitPackage P g l) (PackageTotalHom.id P) h).2
  intro q
  cases q <;> simp [IndependentRawLocal.read, IndependentRawLocal.unitRaw,
    IndependentRepresentativeHom.transportTable, unitPackage]

/-- Representative-selected Homs retain the same arbitrary directed coefficient changes. -/
def representativeCoefficientHom (P : AATCorePackage U) (g : SelectedGeometryReading P)
    {k l : Type v} [CommRing k] [CommRing l] (h : k →+* l) :
    GeometryTotalHom (unitPackage P g k) (unitPackage P g l) where
  base := PackageTotalHom.id P
  geometry :=
    { coverage := coefficientCoverage P g k l
      overlap := coefficientOverlap P g k l
      coefficientHom := h
      raw_eq := unitPackage_raw_eq P g h
      supportComp _ := _root_.id
      axisComp _ := _root_.id
      observableComp _ := _root_.id
      supportReads _ _ _ := _root_.id
      axisReads _ _ := _root_.id
      observableReads _ _ := _root_.id
      support_naturality _ _ := rfl
      axis_naturality _ _ := rfl
      observable_naturality _ _ := rfl }

/-- A concrete coefficient map with nonzero kernel. -/
def projection : (ℤ × ℤ) →+* ℤ := RingHom.fst ℤ ℤ

/-- The two coefficient values (0,0) and (0,1) have the same image. -/
theorem projection_not_injective : ¬ Function.Injective projection := by
  intro h
  have hp := h (a₁ := (0, 0)) (a₂ := (0, 1)) rfl
  have hc := congrArg Prod.snd hp
  norm_num at hc

/-- Explicit primitive Hom reconstruction preserves the noninjective coefficient map. -/
theorem explicit_reconstruction_noninjective (P : AATCorePackage U) (g : SelectedGeometryReading P) :
    ¬ Function.Injective
      (IndependentExplicitHom.assemble
        (IndependentExplicitHom.read (explicitCoefficientHom P g projection))).coefficientHom := by
  rw [IndependentExplicitHom.assemble_read]
  exact projection_not_injective

/-- Representative primitive Hom reconstruction preserves the same noninjective coefficient map. -/
theorem representative_reconstruction_noninjective (P : AATCorePackage U) (g : SelectedGeometryReading P) :
    ¬ Function.Injective
      (IndependentRepresentativeHom.assemble
        (IndependentRepresentativeHom.read (representativeCoefficientHom P g projection))).geometry.coefficientHom := by
  rw [IndependentRepresentativeHom.assemble_read]
  exact projection_not_injective

end

end AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentHomRefutations
