import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedLiteralMateFactor
import ResearchLean.AG.FullGeometryNormalization.SemanticExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.SemanticExactNormalizationPush

/-!
# Normalization naturality of the semantic complete mate

The admissibility at every endpoint is transported or pulled from the one
southwest core. The comparison is the generated unit, literal Cartesian mate,
and counit; no comparison or naturality equation is accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 6000000

private noncomputable def southwest
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest) :=
  semanticDerivedSouthwestGeometryFiber input Q k g endpoint_eq

private theorem southwest_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (southwest input Q k g endpoint_eq).1.core := admissible

private noncomputable def target_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactTransport
    input.square.bottom (southwest input Q k g endpoint_eq)
    (southwest_admissible input Q k g endpoint_eq admissible)

private noncomputable def left_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.left (southwest input Q k g endpoint_eq)
    (southwest_admissible input Q k g endpoint_eq admissible)

private noncomputable def direct_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedDirectGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactTransport
    input.square.top
    (semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq)
    (left_admissible input Q k g endpoint_eq admissible)

private noncomputable def via_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.right
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    (target_admissible input Q k g endpoint_eq admissible)

private noncomputable def bottom_pulled_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.bottom
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    (target_admissible input Q k g endpoint_eq admissible)

private noncomputable def B_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedBGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.left
    (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
    (bottom_pulled_admissible input Q k g endpoint_eq admissible)

private noncomputable def T_admissible
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedTGeometryAt input Q k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.top
    (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    (via_admissible input Q k g endpoint_eq admissible)

/-- The uniquely determined literal Cartesian mate commutes with the
normalizations transported from its common southeast target. -/
theorem semanticDerivedLiteralMateNorthwestIsoAt_normalization_natural
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    canonicalGeometryFiberNormalization
        (semanticDerivedBGeometryAt input Q k g endpoint_eq)
        (B_admissible input Q k g endpoint_eq admissible) ≫
      (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom =
    (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom ≫
      canonicalGeometryFiberNormalization
        (semanticDerivedTGeometryAt input Q k g endpoint_eq)
        (T_admissible input Q k g endpoint_eq admissible) := by
  classical
  let baseLeg := semanticDerivedDirectBaseRouteLegAt input Q k g endpoint_eq
  let pulledLeg := semanticDerivedDirectPulledRouteLegAt input Q k g endpoint_eq
  let mate := (semanticDerivedLiteralMateNorthwestIsoAt input Q k g endpoint_eq).hom
  let nB := canonicalGeometryFiberNormalization
    (semanticDerivedBGeometryAt input Q k g endpoint_eq)
    (B_admissible input Q k g endpoint_eq admissible)
  let nT := canonicalGeometryFiberNormalization
    (semanticDerivedTGeometryAt input Q k g endpoint_eq)
    (T_admissible input Q k g endpoint_eq admissible)
  let nTarget := canonicalGeometryFiberNormalization
    (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    (target_admissible input Q k g endpoint_eq admissible)
  have hbase : nB.1 ≫ baseLeg = baseLeg ≫ nTarget.1 := by
    let leftLift := semanticGeometryPullLift input.square.left
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
    let bottomLift := semanticGeometryPullLift input.square.bottom
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    let nBottom := canonicalGeometryFiberNormalization
      (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
      (bottom_pulled_admissible input Q k g endpoint_eq admissible)
    have hleft : nB.1 ≫ leftLift = leftLift ≫ nBottom.1 :=
      semanticGeometryPullLift_normalization_natural input.square.left
        (semanticDerivedBottomPulledTargetGeometryAt input Q k g endpoint_eq)
        (bottom_pulled_admissible input Q k g endpoint_eq admissible)
    have hbottom : nBottom.1 ≫ bottomLift = bottomLift ≫ nTarget.1 :=
      semanticGeometryPullLift_normalization_natural input.square.bottom
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
        (target_admissible input Q k g endpoint_eq admissible)
    change nB.1 ≫ (leftLift ≫ bottomLift) =
      (leftLift ≫ bottomLift) ≫ nTarget.1
    calc
      _ = (nB.1 ≫ leftLift) ≫ bottomLift := (Category.assoc _ _ _).symm
      _ = (leftLift ≫ nBottom.1) ≫ bottomLift := by rw [hleft]
      _ = leftLift ≫ (nBottom.1 ≫ bottomLift) := Category.assoc _ _ _
      _ = leftLift ≫ (bottomLift ≫ nTarget.1) := by rw [hbottom]
      _ = _ := (Category.assoc _ _ _).symm
  have hpulled : nT.1 ≫ pulledLeg = pulledLeg ≫ nTarget.1 := by
    let topLift := semanticGeometryPullLift input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    let rightLift := semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    let nVia := canonicalGeometryFiberNormalization
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
      (via_admissible input Q k g endpoint_eq admissible)
    have htop : nT.1 ≫ topLift = topLift ≫ nVia.1 :=
      semanticGeometryPullLift_normalization_natural input.square.top
        (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
        (via_admissible input Q k g endpoint_eq admissible)
    have hright : nVia.1 ≫ rightLift = rightLift ≫ nTarget.1 :=
      semanticGeometryPullLift_normalization_natural input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
        (target_admissible input Q k g endpoint_eq admissible)
    change nT.1 ≫ (topLift ≫ rightLift) =
      (topLift ≫ rightLift) ≫ nTarget.1
    calc
      _ = (nT.1 ≫ topLift) ≫ rightLift := (Category.assoc _ _ _).symm
      _ = (topLift ≫ nVia.1) ≫ rightLift := by rw [htop]
      _ = topLift ≫ (nVia.1 ≫ rightLift) := Category.assoc _ _ _
      _ = topLift ≫ (rightLift ≫ nTarget.1) := by rw [hright]
      _ = _ := (Category.assoc _ _ _).symm
  letI hpulledCart : (crossStageProjection U).IsStronglyCartesian
      ((crossStageProjection U).map pulledLeg) pulledLeg := by
    let first := semanticGeometryPullLift input.square.top
      (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    let second := semanticGeometryPullLift input.square.right
      (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    letI hfirst : (crossStageProjection U).IsStronglyCartesian
        first.base.base first := by
      simpa [first] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.top
        (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
    letI hsecond : (crossStageProjection U).IsStronglyCartesian
        second.base.base second := by
      simpa [second] using semanticGeometryPullLift_crossStageStronglyCartesian_map
        input.square.right
        (semanticDerivedTargetGeometryAt input Q k g endpoint_eq)
    simpa [pulledLeg, semanticDerivedDirectPulledRouteLegAt,
      first, second, Functor.map_comp] using
      CategoryTheory.Functor.IsStronglyCartesian.comp (crossStageProjection U)
  have hfac : mate.1 ≫ pulledLeg = baseLeg := by
    exact semanticDerivedLiteralMateNorthwestIsoAt_hom_fac
      input Q k g endpoint_eq
  have hpost : (nB ≫ mate).1 ≫ pulledLeg =
      (mate ≫ nT).1 ≫ pulledLeg := by
    change (nB.1 ≫ mate.1) ≫ pulledLeg =
      (mate.1 ≫ nT.1) ≫ pulledLeg
    calc
      _ = nB.1 ≫ (mate.1 ≫ pulledLeg) := Category.assoc _ _ _
      _ = nB.1 ≫ baseLeg := by rw [hfac]
      _ = baseLeg ≫ nTarget.1 := hbase
      _ = (mate.1 ≫ pulledLeg) ≫ nTarget.1 := by rw [hfac]
      _ = mate.1 ≫ (pulledLeg ≫ nTarget.1) := Category.assoc _ _ _
      _ = mate.1 ≫ (nT.1 ≫ pulledLeg) := by rw [hpulled]
      _ = _ := (Category.assoc _ _ _).symm
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 input.square.northwest) (nB ≫ mate).1 := (nB ≫ mate).2
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 input.square.northwest) (mate ≫ nT).1 := (mate ≫ nT).2
  exact CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U)
    ((crossStageProjection U).map pulledLeg) pulledLeg
    (𝟙 input.square.northwest) hpost


/-- The semantic complete comparison commutes with the normalizations
transported from the same southwest geometry. -/
theorem semanticDerivedBarAlphaIsoAt_normalization_natural
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U) (Q : AATCorePackage U)
    (k : Type v) [CommRing k] (g : FixedCoefficientGeometryAt Q k)
    (endpoint_eq : packagePoint Q = input.square.southwest)
    (square_isPullback : IsPullback input.square.left input.square.top
      input.square.bottom input.square.right)
    (admissible : CanonicalObjectNormalizationAdmissible Q) :
    canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input Q k g endpoint_eq)
        (direct_admissible input Q k g endpoint_eq admissible) ≫
      (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).hom =
    (semanticDerivedBarAlphaIsoAt
        input Q k g endpoint_eq square_isPullback).hom ≫
      canonicalGeometryFiberNormalization
        (semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq)
        (via_admissible input Q k g endpoint_eq admissible) := by
  let source := southwest input Q k g endpoint_eq
  let target := semanticDerivedTargetGeometryAt input Q k g endpoint_eq
  let left := semanticDerivedLeftPulledGeometryAt input Q k g endpoint_eq
  let via := semanticDerivedViaBaseGeometryAt input Q k g endpoint_eq
  let B := semanticDerivedBGeometryAt input Q k g endpoint_eq
  let T := semanticDerivedTGeometryAt input Q k g endpoint_eq
  let pushBottom := geomFiberTransportFunctor input.square.bottom
  let pullBottom := semanticGeometryPullFunctor.{u, v} input.square.bottom
  let pullLeft := semanticGeometryPullFunctor.{u, v} input.square.left
  let pushTop := geomFiberTransportFunctor input.square.top
  let pullTop := semanticGeometryPullFunctor.{u, v} input.square.top
  let pullRight := semanticGeometryPullFunctor.{u, v} input.square.right
  let nS := canonicalGeometryFiberNormalization source
    (southwest_admissible input Q k g endpoint_eq admissible)
  let nTarget := canonicalGeometryFiberNormalization target
    (target_admissible input Q k g endpoint_eq admissible)
  let nLeft := canonicalGeometryFiberNormalization left
    (left_admissible input Q k g endpoint_eq admissible)
  let nDirect := canonicalGeometryFiberNormalization
    (semanticDerivedDirectGeometryAt input Q k g endpoint_eq)
    (direct_admissible input Q k g endpoint_eq admissible)
  let nVia := canonicalGeometryFiberNormalization via
    (via_admissible input Q k g endpoint_eq admissible)
  let nB := canonicalGeometryFiberNormalization B
    (B_admissible input Q k g endpoint_eq admissible)
  let nT := canonicalGeometryFiberNormalization T
    (T_admissible input Q k g endpoint_eq admissible)
  let unit := (semanticDerivedUnitTopPushIsoAt input Q k g endpoint_eq).hom
  let mate := (semanticDerivedLiteralMateNorthwestIsoAt
    input Q k g endpoint_eq).hom
  let counit := (semanticDerivedTopCounitIsoAt input Q k g endpoint_eq).hom
  have hbottom : pushBottom.map nS = nTarget := by
    exact semanticGeomFiberTransportFunctor_map_normalization
      input.square.bottom source
      (southwest_admissible input Q k g endpoint_eq admissible)
  have hleft : pullLeft.map nS = nLeft := by
    exact semanticGeometryPullFunctor_map_normalization
      input.square.left source
      (southwest_admissible input Q k g endpoint_eq admissible)
  have hdirect : pushTop.map nLeft = nDirect := by
    exact semanticGeomFiberTransportFunctor_map_normalization
      input.square.top left
      (left_admissible input Q k g endpoint_eq admissible)
  have hvia : pullRight.map nTarget = nVia := by
    exact semanticGeometryPullFunctor_map_normalization
      input.square.right target
      (target_admissible input Q k g endpoint_eq admissible)
  have hB : pullLeft.map (pullBottom.map nTarget) = nB := by
    calc
      _ = pullLeft.map (canonicalGeometryFiberNormalization
            (pullBottom.obj target)
            (canonicalGeometryNormalizationAdmissible_semanticExactPull
              input.square.bottom target
              (target_admissible input Q k g endpoint_eq admissible))) := by
          rw [semanticGeometryPullFunctor_map_normalization]
      _ = nB := semanticGeometryPullFunctor_map_normalization
        input.square.left (pullBottom.obj target)
        (canonicalGeometryNormalizationAdmissible_semanticExactPull
          input.square.bottom target
          (target_admissible input Q k g endpoint_eq admissible))
  have hT : pullTop.map nVia = nT := by
    exact semanticGeometryPullFunctor_map_normalization
      input.square.top via
      (via_admissible input Q k g endpoint_eq admissible)
  have hunit : nDirect ≫ unit = unit ≫ pushTop.map nB := by
    have h := semanticGeometryTransportPullUnit_naturality
      input.square.bottom nS
    have h' := congrArg (fun f => pushTop.map (pullLeft.map f)) h
    simp only [Functor.map_comp] at h'
    change pushTop.map (pullLeft.map nS) ≫ unit =
      unit ≫ pushTop.map (pullLeft.map
        (pullBottom.map (pushBottom.map nS))) at h'
    rw [hleft, hdirect, hbottom, hB] at h'
    exact h'
  have hmate : pushTop.map nB ≫ pushTop.map mate =
      pushTop.map mate ≫ pushTop.map nT := by
    have h := semanticDerivedLiteralMateNorthwestIsoAt_normalization_natural
      input Q k g endpoint_eq admissible
    change nB ≫ mate = mate ≫ nT at h
    have h' := congrArg pushTop.map h
    simpa only [Functor.map_comp] using h'
  have hcounit : pushTop.map nT ≫ counit = counit ≫ nVia := by
    have h := semanticGeometryTransportPullCounit_naturality
      input.square.top nVia
    change pushTop.map (pullTop.map nVia) ≫ counit =
      counit ≫ nVia at h
    rw [hT] at h
    exact h
  rw [semanticDerivedBarAlphaIsoAt_hom]
  change nDirect ≫ (unit ≫ pushTop.map mate ≫ counit) =
    (unit ≫ pushTop.map mate ≫ counit) ≫ nVia
  calc
    _ = (nDirect ≫ unit) ≫ pushTop.map mate ≫ counit := by
      simp only [Category.assoc]
    _ = (unit ≫ pushTop.map nB) ≫ pushTop.map mate ≫ counit := by
      rw [hunit]
    _ = unit ≫ (pushTop.map nB ≫ pushTop.map mate) ≫ counit := by
      simp only [Category.assoc]
    _ = unit ≫ (pushTop.map mate ≫ pushTop.map nT) ≫ counit := by
      rw [hmate]
    _ = unit ≫ pushTop.map mate ≫ (pushTop.map nT ≫ counit) := by
      simp only [Category.assoc]
    _ = unit ≫ pushTop.map mate ≫ (counit ≫ nVia) := by
      rw [hcounit]
    _ = _ := by simp only [Category.assoc]

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
