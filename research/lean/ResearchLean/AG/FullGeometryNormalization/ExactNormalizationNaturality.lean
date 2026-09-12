import ResearchLean.AG.FullGeometryNormalization.ExactNormalizationTransport
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedMateComposite
import ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationBlocker

/-!
# Canonical normalization along exact complete-geometry maps

This module discharges the operation-map and morphism-level part of G-122(B3)
for the actual exact push and pull constructions.  Endpoint admissibility is
generated from the one source datum; it is never accepted separately.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

private theorem castOperation_heq
    {U : AtomCarrier.{u}} (R : OperationReading U)
    {first first' second second' : ArchitectureObject U}
    (hfirst : first = first') (hsecond : second = second')
    (operation : R.Op first second) :
    HEq (castOperation R hfirst hsecond operation) operation := by
  cases hfirst
  cases hsecond
  rfl

private theorem transportOperation_heq
    {U : AtomCarrier.{u}} (e : U.Atom ≃ U.Atom) (R : OperationReading U)
    {first second : ArchitectureObject U} (operation : R.Op first second) :
    HEq (transportOperation e R operation) operation := by
  unfold transportOperation
  exact castOperation_heq R _ _ operation

private theorem geometryReadHom_heq_of_base_eq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {f g : PackageTotalHom G.core H.core}
    (F : GeomReadHom G H f) (T : GeomReadHom G H g)
    (hbase : f = g)
    (hcoefficient : F.coefficientHom = T.coefficientHom)
    (hsupport : HEq F.supportComp T.supportComp)
    (haxis : HEq F.axisComp T.axisComp)
    (hobservable : HEq F.observableComp T.observableComp) : HEq F T := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- Forward exact transport generates the dependent operation coherence needed
for canonical normalization naturality. -/
theorem transportAlongHom_normalization_operationCoherent
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    CanonicalNormalizationOperationCoherent
      (transportAlongHom P f) admissible
      (canonicalObjectNormalizationAdmissible_transportAlong P admissible f) := by
  unfold CanonicalNormalizationOperationCoherent
  apply Function.hfunext rfl
  intro first first' hfirst
  cases hfirst
  apply Function.hfunext rfl
  intro second second' hsecond
  cases hsecond
  apply Function.hfunext rfl
  intro operation operation' hoperation
  cases hoperation
  simp only [PackageTotalHom.comp, SignedExactCoreReadingHom.comp,
    canonicalObjectNormalizationTotal, canonicalObjectNormalizationUpper,
    transportAlongHom, transportAlongUpper]
  exact ((transportOperation_heq _ _ _).trans (cast_heq _ _)).trans
    ((cast_heq _ _).trans (transportOperation_heq _ _ _)).symm

/-- Inverse-core reindexing generates the dependent operation coherence needed
for canonical normalization naturality. -/
theorem inverseCorePackageHom_normalization_operationCoherent
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (f : X ⟶ packagePoint Q) :
    CanonicalNormalizationOperationCoherent
      (inverseCorePackageHom Q f)
      (canonicalObjectNormalizationAdmissible_inverseCorePackage Q admissible f)
      admissible := by
  unfold CanonicalNormalizationOperationCoherent
  apply Function.hfunext rfl
  intro first first' hfirst
  cases hfirst
  apply Function.hfunext rfl
  intro second second' hsecond
  cases hsecond
  apply Function.hfunext rfl
  intro operation operation' hoperation
  cases hoperation
  simp only [PackageTotalHom.comp, SignedExactCoreReadingHom.comp,
    canonicalObjectNormalizationTotal, canonicalObjectNormalizationUpper,
    inverseCorePackageHom, inverseCorePackageForwardUpper]
  exact (cast_heq _ _).trans (cast_heq _ _).symm

/-- Canonical core normalization commutes with the actual forward exact
transport morphism. -/
theorem transportAlongHom_normalization_natural
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom P.reading.doctrine E) :
    (transportAlongHom P f).comp
        (canonicalObjectNormalizationTotal (transportAlong P f)
          (canonicalObjectNormalizationAdmissible_transportAlong P admissible f)) =
      (canonicalObjectNormalizationTotal P admissible).comp
        (transportAlongHom P f) := by
  exact canonicalObjectNormalizationTotal_natural_of_operationCoherent
    (transportAlongHom P f) admissible
    (canonicalObjectNormalizationAdmissible_transportAlong P admissible f)
    (transportAlongHom_normalization_operationCoherent P admissible f)

/-- Canonical core normalization commutes with the actual inverse-core
reindexing morphism. -/
theorem inverseCorePackageHom_normalization_natural
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (Q : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible Q)
    (f : X ⟶ packagePoint Q) :
    (inverseCorePackageHom Q f).comp
        (canonicalObjectNormalizationTotal Q admissible) =
      (canonicalObjectNormalizationTotal (inverseCorePackage Q f)
          (canonicalObjectNormalizationAdmissible_inverseCorePackage Q admissible f)).comp
        (inverseCorePackageHom Q f) := by
  exact canonicalObjectNormalizationTotal_natural_of_operationCoherent
    (inverseCorePackageHom Q f)
    (canonicalObjectNormalizationAdmissible_inverseCorePackage Q admissible f)
    admissible
    (inverseCorePackageHom_normalization_operationCoherent Q admissible f)

/-- Canonical complete-geometry normalization commutes with the actual forward
exact transport morphism. -/
theorem geomTransportAlongHom_normalization_natural
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    {E : ExtractionDoctrine U}
    (f : ExactDoctrineHom G.core.reading.doctrine E) :
    canonicalGeometryNormalization G admissible ≫ geomTransportAlongHom G f =
      geomTransportAlongHom G f ≫
        canonicalGeometryNormalization (geomTransportAlong G f)
          (canonicalObjectNormalizationAdmissible_transportAlong
            G.core admissible f) := by
  have hbase :
      (canonicalGeometryNormalization G admissible ≫
          geomTransportAlongHom G f).base =
        (geomTransportAlongHom G f ≫
          canonicalGeometryNormalization (geomTransportAlong G f)
            (canonicalObjectNormalizationAdmissible_transportAlong
              G.core admissible f)).base := by
    exact (transportAlongHom_normalization_natural G.core admissible f).symm
  apply GeometryTotalHom.ext hbase
  apply geometryReadHom_heq_of_base_eq _ _ hbase <;> rfl

/-- Canonical complete-geometry normalization commutes with the selected exact
pull lift. -/
theorem exactGeometryPullLift_normalization_natural
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    canonicalGeometryNormalization (exactGeometryPull input target).1
          (canonicalGeometryNormalizationAdmissible_exactPull
            input target admissible) ≫
        exactGeometryPullLift input target =
      exactGeometryPullLift input target ≫
        canonicalGeometryNormalization target.1 admissible := by
  have hbase :
      (canonicalGeometryNormalization (exactGeometryPull input target).1
            (canonicalGeometryNormalizationAdmissible_exactPull
              input target admissible) ≫
          exactGeometryPullLift input target).base =
        (exactGeometryPullLift input target ≫
          canonicalGeometryNormalization target.1 admissible).base := by
    simpa [exactGeometryPull, exactGeometryPullObject,
      exactGeometryPullLift, UpperGeometryCleavage.generatedExactGeometryHom_base,
      UpperGeometryCleavage.exactBaseHom] using
        (inverseCorePackageHom_normalization_natural target.1.core
          admissible (exactGeometryPullBaseHom input target)).symm
  apply GeometryTotalHom.ext hbase
  apply geometryReadHom_heq_of_base_eq _ _ hbase <;> rfl

/-- Canonical normalization as an endomorphism in the complete-geometry fiber. -/
noncomputable def canonicalGeometryFiberNormalization
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) : G ⟶ G := by
  refine ⟨canonicalGeometryNormalization G.1 admissible, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{u, v} U) (𝟙 X)
    (canonicalGeometryNormalization G.1 admissible) G.2 G.2
  change (𝟙 (packagePoint G.1.core)) ≫ eqToHom G.2 =
    eqToHom G.2 ≫ 𝟙 X
  simp

/-- The actual exact push functor maps canonical normalization to the internally
generated normalization at its target. -/
theorem geomFiberTransportFunctor_map_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (source : GeomFiber.{u, v} input.semantic.source)
    (admissible : CanonicalObjectNormalizationAdmissible source.1.core) :
    (geomFiberTransportFunctor input.semantic.hom).map
        (canonicalGeometryFiberNormalization source admissible) =
      canonicalGeometryFiberNormalization
        ((geomFiberTransportFunctor input.semantic.hom).obj source)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          input source admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input.semantic.hom (geomFiberLift input.semantic.hom source) :=
    geomFiberLift_isStronglyCocartesian input.semantic.hom source
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) input.semantic.hom
    (geomFiberLift input.semantic.hom source) (𝟙 input.semantic.target)
  calc
    geomFiberLift input.semantic.hom source ≫
          ((geomFiberTransportFunctor input.semantic.hom).map
            (canonicalGeometryFiberNormalization source admissible)).1 =
        (canonicalGeometryFiberNormalization source admissible).1 ≫
          geomFiberLift input.semantic.hom source := by
      simpa only [geomFiberTransportFunctor] using
        geomFiberTransportMap_fac input.semantic.hom
          (canonicalGeometryFiberNormalization source admissible)
    _ = geomFiberLift input.semantic.hom source ≫
        (canonicalGeometryFiberNormalization
          ((geomFiberTransportFunctor input.semantic.hom).obj source)
          (canonicalGeometryNormalizationAdmissible_exactTransport
            input source admissible)).1 := by
      simpa [canonicalGeometryFiberNormalization,
        geomFiberTransportFunctor, geomFiberTransportObj,
        geomFiberTransportObject, geomFiberBaseHom] using
          geomTransportAlongHom_normalization_natural source.1 admissible
            (geomFiberBaseHom input.semantic.hom source).doctrineHom

/-- The actual exact pull functor maps canonical normalization to the internally
generated normalization at its source. -/
theorem exactGeometryPullFunctor_map_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (target : GeomFiber.{u, v} input.semantic.target)
    (admissible : CanonicalObjectNormalizationAdmissible target.1.core) :
    (exactGeometryPullFunctor input).map
        (canonicalGeometryFiberNormalization target admissible) =
      canonicalGeometryFiberNormalization
        ((exactGeometryPullFunctor input).obj target)
        (canonicalGeometryNormalizationAdmissible_exactPull
          input target admissible) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input.semantic.hom (exactGeometryPullLift input target) :=
    exactGeometryPullLift_crossStageStronglyCartesian input target
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U) input.semantic.hom
    (exactGeometryPullLift input target) (𝟙 input.semantic.source)
  calc
    ((exactGeometryPullFunctor input).map
          (canonicalGeometryFiberNormalization target admissible)).1 ≫
        exactGeometryPullLift input target =
      exactGeometryPullLift input target ≫
        (canonicalGeometryFiberNormalization target admissible).1 := by
      simpa only [exactGeometryPullFunctor] using
        exactGeometryPullMap_fac input
          (canonicalGeometryFiberNormalization target admissible)
    _ = (canonicalGeometryFiberNormalization
          ((exactGeometryPullFunctor input).obj target)
          (canonicalGeometryNormalizationAdmissible_exactPull
            input target admissible)).1 ≫
        exactGeometryPullLift input target := by
      simpa [canonicalGeometryFiberNormalization,
        exactGeometryPullFunctor] using
          (exactGeometryPullLift_normalization_natural
            input target admissible).symm

/-- Admissibility of the authored direct endpoint is generated from the single
southwest input by exact pull followed by exact push. -/
theorem authoredExactDirectGeometryAt_admissible
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    CanonicalObjectNormalizationAdmissible
      (authoredExactDirectGeometryAt A z k g).1.core :=
  canonicalGeometryNormalizationAdmissible_exactTransport
    (authoredExactTopInput A) (authoredExactLeftPulledGeometryAt A z k g)
    (canonicalGeometryNormalizationAdmissible_exactPull
      (authoredExactLeftInput A) (authoredSouthwestGeometryFiberAt A z k g)
      admissible)

/-- Admissibility of the authored via-base endpoint is generated from the same
southwest input by exact push followed by exact pull. -/
theorem authoredExactViaBaseGeometryAt_admissible
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (admissible : CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    CanonicalObjectNormalizationAdmissible
      (authoredExactViaBaseGeometryAt A z k g).1.core :=
  canonicalGeometryNormalizationAdmissible_exactPull
    (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)
    (canonicalGeometryNormalizationAdmissible_exactTransport
      (authoredExactBottomInput A) (authoredSouthwestGeometryFiberAt A z k g)
      admissible)

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
