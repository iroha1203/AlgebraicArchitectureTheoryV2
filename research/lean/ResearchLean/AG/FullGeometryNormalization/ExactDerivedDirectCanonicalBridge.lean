import ResearchLean.AG.FullGeometryNormalization.ExactDerivedBaseRefinementExactImage
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedPulledRefinementExactImage
import ResearchLean.AG.FullGeometryNormalization.ExactRefinementIso

/-!
# Exact direct-to-canonical endpoint bridges

This layer compares each literal exact two-edge endpoint with the corresponding
canonical-authored normalization.  Cartesian uniqueness is applied first at
the refinement-package stage and then at the refinement-geometry stage.  The
resulting isomorphisms are reflected back into the exact package and complete
geometry categories.

## Implementation notes

The construction applies Cartesian uniqueness at the refinement-package and
refinement-geometry projections before exactifying the result.  Directly
rebuilding all exact upper fields was rejected because it would duplicate the
accepted Cartesian universal properties.  The final fiber comparison is made
by composing the raw exact isomorphism with the cocartesian transport lift;
treating the raw isomorphism as already vertical was rejected because its
endpoints lie over isomorphic, not definitionally equal, base points.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The two embedded package morphisms in the literal base-first route compose
to a strongly Cartesian morphism over the refinement package projection. -/
private theorem directBaseRoutePackage_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base) := by
  let first := exactGeometryPullLift (authoredExactLeftInput A)
    (authoredExactBottomPulledTargetGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactBottomInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base.base)
      (((exactGeometryToRefinementGeometry U).map first).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactBottomPulledTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactLeftInput A)
            (authoredExactBottomPulledTargetGeometryAt A z k g)))).base)
      ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactBottomPulledTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactLeftInput A)
            (authoredExactBottomPulledTargetGeometryAt A z k g))))
    exact UpperGeometryCleavage.exactGeometryBase_isStronglyCartesian _ _
  letI hsecond : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base.base)
      (((exactGeometryToRefinementGeometry U).map second).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactBottomInput A)
            (authoredExactTargetGeometryAt A z k g)))).base)
      ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactBottomInput A)
            (authoredExactTargetGeometryAt A z k g))))
    exact UpperGeometryCleavage.exactGeometryBase_isStronglyCartesian _ _
  simpa [authoredExactDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementPackageProjection U)

/-- The two embedded package morphisms in the literal pulled-first route
compose to a strongly Cartesian refinement-package morphism. -/
private theorem directPulledRoutePackage_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base) := by
  let first := exactGeometryPullLift (authoredExactTopInput A)
    (authoredExactViaBaseGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactRightInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base.base)
      (((exactGeometryToRefinementGeometry U).map first).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactViaBaseGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactTopInput A)
            (authoredExactViaBaseGeometryAt A z k g)))).base)
      ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactViaBaseGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactTopInput A)
            (authoredExactViaBaseGeometryAt A z k g))))
    exact UpperGeometryCleavage.exactGeometryBase_isStronglyCartesian _ _
  letI hsecond : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base.base)
      (((exactGeometryToRefinementGeometry U).map second).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g)))).base)
      ((exactPackageToRefinement U).map
        (UpperGeometryCleavage.exactBaseHom
          (authoredExactTargetGeometryAt A z k g).1
          (exactGeometryPullBaseHom (authoredExactRightInput A)
            (authoredExactTargetGeometryAt A z k g))))
    exact UpperGeometryCleavage.exactGeometryBase_isStronglyCartesian _ _
  simpa [authoredExactDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementPackageProjection U)

/-- The embedded complete-geometry morphisms in the literal base-first route
compose to a strongly Cartesian refinement-geometry morphism. -/
private theorem directBaseRouteGeometry_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)).base)
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectBaseRouteLegAt A z k g)) := by
  let first := exactGeometryPullLift (authoredExactLeftInput A)
    (authoredExactBottomPulledTargetGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactBottomInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactLeftInput A)
      (authoredExactBottomPulledTargetGeometryAt A z k g)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactBottomInput A) (authoredExactTargetGeometryAt A z k g)
  simpa [authoredExactDirectBaseRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

/-- The embedded complete-geometry morphisms in the literal pulled-first route
compose to a strongly Cartesian refinement-geometry morphism. -/
private theorem directPulledRouteGeometry_isStronglyCartesian
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)).base)
      ((exactGeometryToRefinementGeometry U).map
        (authoredExactDirectPulledRouteLegAt A z k g)) := by
  let first := exactGeometryPullLift (authoredExactTopInput A)
    (authoredExactViaBaseGeometryAt A z k g)
  let second := exactGeometryPullLift (authoredExactRightInput A)
    (authoredExactTargetGeometryAt A z k g)
  letI hfirst : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map first).base)
      ((exactGeometryToRefinementGeometry U).map first) := by
    simpa [first] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactTopInput A) (authoredExactViaBaseGeometryAt A z k g)
  letI hsecond : (refinementGeometryProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map second).base)
      ((exactGeometryToRefinementGeometry U).map second) := by
    simpa [second] using exactGeometryPullLift_refinementStronglyCartesian
      (authoredExactRightInput A) (authoredExactTargetGeometryAt A z k g)
  simpa [authoredExactDirectPulledRouteLegAt, first, second, Functor.map_comp]
    using CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)

/-! ## Two-stage exact endpoint comparisons -/

/-- The literal exact base endpoint is isomorphic to the canonical-authored
base normalization before transport back to the original northwest point. -/
noncomputable def authoredExactDirectToCanonicalBaseGeometryIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (show GeomReadCategory U from
      (authoredExactGeneratedMateSourceGeometryAt A z k g).1) ≅
      (show GeomReadCategory U from
        (authoredExactCanonicalBaseRouteFiberAt A z k g).1) := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  let direct := (exactGeometryToRefinementGeometry U).map
    (authoredExactDirectBaseRouteLegAt A z k g)
  let canonical := input.canonicalAuthoredBaseRouteGeometryHomAt PUnit.unit
  let pointIso := authoredExactDirectToCanonicalBaseSourcePointIsoAt A z k g
  let pointRefinementIso := (exactPointedToRefinement U).mapIso pointIso
  letI hcanonicalPackage : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base := by
    simpa [canonical, input] using
      UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
        (authoredExactRefinementBCContextAt A z k g)
        (input.sourceTargetGeometryAt PUnit.unit)
  letI hdirectPackage : (refinementPackageProjection U).IsStronglyCartesian
      direct.base.base direct.base := by
    simpa [direct] using directBaseRoutePackage_isStronglyCartesian A z k g
  have packageBaseFac : direct.base.base =
      pointRefinementIso.hom ≫ canonical.base.base := by
    simpa [direct, canonical, pointRefinementIso, pointIso, input] using
      (authoredExactCanonicalBaseRoute_refinementExactImage A z k g).symm
  let packageRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
    (p := refinementPackageProjection U) (g := pointRefinementIso)
    (f := canonical.base.base) (f' := direct.base.base)
    packageBaseFac canonical.base direct.base
  let packageMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U) canonical.base.base canonical.base
    packageBaseFac direct.base
  letI hpackageMap : (refinementPackageProjection U).IsHomLift
      pointRefinementIso.hom packageMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementPackageProjection U)
      (f := canonical.base.base) (φ := canonical.base)
      (g := pointRefinementIso.hom) (f' := direct.base.base)
      packageBaseFac direct.base
  have packageHomBase : packageRefinementIso.hom.base =
      pointRefinementIso.hom := by
    change packageMap.base = pointRefinementIso.hom
    exact (@CategoryTheory.IsHomLift.eq_of_isHomLift
      _ _ _ _ (refinementPackageProjection U) _ _
      pointRefinementIso.hom packageMap hpackageMap).symm
  let packageIso := UpperGeometryCleavage.exactPackageIsoOfRefinementIso
    pointIso packageRefinementIso packageHomBase
  letI hcanonicalGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical := by
    simpa [canonical, input] using
      input.canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian PUnit.unit
  letI hdirectGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      direct.base direct := by
    simpa [direct] using directBaseRouteGeometry_isStronglyCartesian A z k g
  have packageFac : packageRefinementIso.hom ≫ canonical.base = direct.base :=
    CategoryTheory.Functor.IsStronglyCartesian.fac
      (refinementPackageProjection U) canonical.base.base canonical.base
      packageBaseFac direct.base
  have geometryBaseFac : direct.base =
      packageRefinementIso.hom ≫ canonical.base := packageFac.symm
  let geometryRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := refinementGeometryProjection U) (g := packageRefinementIso)
      (f := canonical.base) (f' := direct.base)
      geometryBaseFac canonical direct
  let geometryMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U) canonical.base canonical
    geometryBaseFac direct
  letI hgeometryMap : (refinementGeometryProjection U).IsHomLift
      packageRefinementIso.hom geometryMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementGeometryProjection U)
      (f := canonical.base) (φ := canonical)
      (g := packageRefinementIso.hom) (f' := direct.base)
      geometryBaseFac direct
  have geometryHomBase : geometryRefinementIso.hom.base =
      packageRefinementIso.hom := by
    change geometryMap.base = packageRefinementIso.hom
    exact (@CategoryTheory.IsHomLift.eq_of_isHomLift
      _ _ _ _ (refinementGeometryProjection U) _ _
      packageRefinementIso.hom geometryMap hgeometryMap).symm
  have packageToRefinement : (exactPackageToRefinement U).map packageIso.hom =
      packageRefinementIso.hom := by
    dsimp [packageIso]
    apply UpperGeometryCleavage.exactPackageHomOfRefinement_toRefinement
    exact packageHomBase
  exact UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
    packageIso geometryRefinementIso
    (geometryHomBase.trans packageToRefinement.symm)

/-- Pulled-route analogue of
`authoredExactDirectToCanonicalBaseGeometryIsoAt`. -/
noncomputable def authoredExactDirectToCanonicalPulledGeometryIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (show GeomReadCategory U from
      (authoredExactGeneratedMateTargetGeometryAt A z k g).1) ≅
      (show GeomReadCategory U from
        (authoredExactCanonicalPulledRouteFiberAt A z k g).1) := by
  let input := authoredExactCompatibleProblemDataAt A z k g
  let direct := (exactGeometryToRefinementGeometry U).map
    (authoredExactDirectPulledRouteLegAt A z k g)
  let canonical := input.canonicalAuthoredPulledRouteGeometryHomAt PUnit.unit
  let pointIso := authoredExactDirectToCanonicalPulledSourcePointIsoAt A z k g
  let pointRefinementIso := (exactPointedToRefinement U).mapIso pointIso
  letI hcanonicalPackage : (refinementPackageProjection U).IsStronglyCartesian
      canonical.base.base canonical.base := by
    simpa [canonical, input] using
      UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
        (authoredExactRefinementBCContextAt A z k g)
        (input.sourceTargetGeometryAt PUnit.unit)
  letI hdirectPackage : (refinementPackageProjection U).IsStronglyCartesian
      direct.base.base direct.base := by
    simpa [direct] using directPulledRoutePackage_isStronglyCartesian A z k g
  have packageBaseFac : direct.base.base =
      pointRefinementIso.hom ≫ canonical.base.base := by
    simpa [direct, canonical, pointRefinementIso, pointIso, input] using
      (authoredExactCanonicalPulledRoute_base_eq_direct A z k g).symm
  let packageRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := refinementPackageProjection U) (g := pointRefinementIso)
      (f := canonical.base.base) (f' := direct.base.base)
      packageBaseFac canonical.base direct.base
  let packageMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U) canonical.base.base canonical.base
    packageBaseFac direct.base
  letI hpackageMap : (refinementPackageProjection U).IsHomLift
      pointRefinementIso.hom packageMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementPackageProjection U)
      (f := canonical.base.base) (φ := canonical.base)
      (g := pointRefinementIso.hom) (f' := direct.base.base)
      packageBaseFac direct.base
  have packageHomBase : packageRefinementIso.hom.base =
      pointRefinementIso.hom := by
    change packageMap.base = pointRefinementIso.hom
    exact (@CategoryTheory.IsHomLift.eq_of_isHomLift
      _ _ _ _ (refinementPackageProjection U) _ _
      pointRefinementIso.hom packageMap hpackageMap).symm
  let packageIso := UpperGeometryCleavage.exactPackageIsoOfRefinementIso
    pointIso packageRefinementIso packageHomBase
  letI hcanonicalGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      canonical.base canonical := by
    simpa [canonical, input] using
      input.canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian PUnit.unit
  letI hdirectGeometry : (refinementGeometryProjection U).IsStronglyCartesian
      direct.base direct := by
    simpa [direct] using directPulledRouteGeometry_isStronglyCartesian A z k g
  have packageFac : packageRefinementIso.hom ≫ canonical.base = direct.base :=
    CategoryTheory.Functor.IsStronglyCartesian.fac
      (refinementPackageProjection U) canonical.base.base canonical.base
      packageBaseFac direct.base
  have geometryBaseFac : direct.base =
      packageRefinementIso.hom ≫ canonical.base := packageFac.symm
  let geometryRefinementIso :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := refinementGeometryProjection U) (g := packageRefinementIso)
      (f := canonical.base) (f' := direct.base)
      geometryBaseFac canonical direct
  let geometryMap := CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U) canonical.base canonical
    geometryBaseFac direct
  letI hgeometryMap : (refinementGeometryProjection U).IsHomLift
      packageRefinementIso.hom geometryMap :=
    CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift
      (p := refinementGeometryProjection U)
      (f := canonical.base) (φ := canonical)
      (g := packageRefinementIso.hom) (f' := direct.base)
      geometryBaseFac direct
  have geometryHomBase : geometryRefinementIso.hom.base =
      packageRefinementIso.hom := by
    change geometryMap.base = packageRefinementIso.hom
    exact (@CategoryTheory.IsHomLift.eq_of_isHomLift
      _ _ _ _ (refinementGeometryProjection U) _ _
      packageRefinementIso.hom geometryMap hgeometryMap).symm
  have packageToRefinement : (exactPackageToRefinement U).map packageIso.hom =
      packageRefinementIso.hom := by
    dsimp [packageIso]
    apply UpperGeometryCleavage.exactPackageHomOfRefinement_toRefinement
    exact packageHomBase
  exact UpperGeometryCleavage.exactGeometryIsoOfRefinementIso
    packageIso geometryRefinementIso
    (geometryHomBase.trans packageToRefinement.symm)

/-- The forward base-route geometry comparison projects to the
realization-generated source-point isomorphism.  The equality is inherited
from the two Cartesian uniqueness comparisons and their exactification. -/
theorem authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (crossStageProjection U).map
        (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom =
      (authoredExactDirectToCanonicalBaseSourcePointIsoAt A z k g).hom := by
  change (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g).hom.base.base = _
  unfold authoredExactDirectToCanonicalBaseGeometryIsoAt
  rfl

/-- The forward pulled-route geometry comparison projects to the
realization-generated pulled source-point isomorphism.  The equality is
inherited from the two Cartesian uniqueness comparisons and exactification. -/
theorem authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_projection
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (crossStageProjection U).map
        (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom =
      (authoredExactDirectToCanonicalPulledSourcePointIsoAt A z k g).hom := by
  change (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g).hom.base.base = _
  unfold authoredExactDirectToCanonicalPulledGeometryIsoAt
  rfl

/-- Turn a total exact geometry isomorphism lying over the inverse of a base
isomorphism into an isomorphism with the forward-transported endpoint. -/
private noncomputable def geomFiberIsoToTransportAlongIso
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (sigma : X ≅ Y) (source : GeomFiber.{u, v} Y)
    (target : GeomFiber.{u, v} X) (comparison : source.1 ≅ target.1)
    (hbase : (crossStageProjection U).map comparison.hom ≫
        eqToHom target.2 = eqToHom source.2 ≫ sigma.inv) :
    source ≅ (geomFiberTransportFunctor sigma.hom).obj target := by
  let lift := geomFiberLift sigma.hom target
  let transported := (geomFiberTransportFunctor sigma.hom).obj target
  let forwardTotal := comparison.hom ≫ lift
  have forward_projection :
      (crossStageProjection U).map forwardTotal ≫ eqToHom transported.2 =
        eqToHom source.2 ≫ 𝟙 Y := by
    change (crossStageProjection U).map (comparison.hom ≫ lift) ≫
        eqToHom transported.2 = eqToHom source.2 ≫ 𝟙 Y
    rw [Functor.map_comp, Category.assoc]
    change (crossStageProjection U).map comparison.hom ≫
        ((crossStageProjection U).map (geomFiberLift sigma.hom target) ≫
          eqToHom transported.2) = _
    rw [geomFiberLift_projection]
    rw [← Category.assoc, hbase]
    simp
  let forward : source ⟶ transported :=
    ⟨forwardTotal, CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection U) (𝟙 Y) forwardTotal source.2 transported.2
      forward_projection⟩
  letI hlift : (crossStageProjection U).IsStronglyCocartesian
      sigma.hom lift := by
    simpa [lift] using geomFiberLift_isStronglyCocartesian sigma.hom target
  letI : IsIso lift :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection U) sigma.hom lift
  letI : IsIso forwardTotal := by
    dsimp [forwardTotal]
    infer_instance
  letI : IsIso forward := geomFiberHom_isIso_of_total_isIso forward
  exact asIso forward

/-- The literal direct endpoint `B_z` is exactly isomorphic, in the original
northwest fiber, to the canonical-authored base normalization. -/
noncomputable def authoredExactGeneratedMateSourceToCanonicalBaseNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactGeneratedMateSourceGeometryAt A z k g ≅
      authoredExactCanonicalBaseRouteNorthwestAt A z k g := by
  apply geomFiberIsoToTransportAlongIso
    (authoredExactPullbackSourceIso A)
    (authoredExactGeneratedMateSourceGeometryAt A z k g)
    (authoredExactCanonicalBaseRouteFiberAt A z k g)
    (authoredExactDirectToCanonicalBaseGeometryIsoAt A z k g)
  rw [authoredExactDirectToCanonicalBaseGeometryIsoAt_hom_projection]
  simp [authoredExactDirectToCanonicalBaseSourcePointIsoAt, eqToIso]

/-- The literal direct endpoint `T_z` is exactly isomorphic, in the original
northwest fiber, to the canonical-authored pulled normalization. -/
noncomputable def authoredExactGeneratedMateTargetToCanonicalPulledNorthwestIsoAt
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactGeneratedMateTargetGeometryAt A z k g ≅
      authoredExactCanonicalPulledRouteNorthwestAt A z k g := by
  apply geomFiberIsoToTransportAlongIso
    (authoredExactPullbackSourceIso A)
    (authoredExactGeneratedMateTargetGeometryAt A z k g)
    (authoredExactCanonicalPulledRouteFiberAt A z k g)
    (authoredExactDirectToCanonicalPulledGeometryIsoAt A z k g)
  rw [authoredExactDirectToCanonicalPulledGeometryIsoAt_hom_projection]
  simp [authoredExactDirectToCanonicalPulledSourcePointIsoAt, eqToIso]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
