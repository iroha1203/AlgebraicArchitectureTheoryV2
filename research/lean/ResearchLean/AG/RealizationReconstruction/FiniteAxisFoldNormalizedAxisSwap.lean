import ResearchLean.AG.FullGeometryNormalization.AmbientKernelGeometryLift
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness
import ResearchLean.AG.FullGeometryNormalization.ExactDerivedEndpointGeometry
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryTransportCounitIso
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonSection
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
import ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses
import Formal.Util.AssertStandardAxioms

/-!
# The finite-axis-fold swap at complete geometry level

The fixed finite-axis-fold input retains its authored adjacent permutation of
the three signature axes.  This file lifts that same core permutation through
the fixed complete geometry and raw restriction data.  The lift is constructed
from the original permutation and the original geometry package; it is not
accepted as an automorphism or comparison certificate.

## Implementation notes

The selected geometry has vacuous coverage requirements, one coordinate and
one relation at every context, and identity restriction.  Consequently the
axis permutation changes only the global signature-axis reading: coefficients,
raw restriction data, and the context-indexed local comparison maps remain
identity.  The square law is proved from the already constructed core swap and
extensionality of the complete geometry morphism.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldNormalizedAxisSwapAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- Heterogeneous geometry-hom extensionality after identifying the two base
maps. -/
private theorem finiteAxisFoldSwapGeometryReadHom_heq_of_base_eq
    {firstBase secondBase : PackageTotalHom
      finiteAxisFoldGeometryPackage.core finiteAxisFoldGeometryPackage.core}
    (first : GeomReadHom finiteAxisFoldGeometryPackage
      finiteAxisFoldGeometryPackage firstBase)
    (second : GeomReadHom finiteAxisFoldGeometryPackage
      finiteAxisFoldGeometryPackage secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

/-- The adjacent signature permutation leaves any raw restriction system on
the fixed transported geometry unchanged. -/
theorem finiteAxisFoldSwap_rawReindex
    (system : LawAlgebra.RawAmbientRestrictionSystem
      finiteAxisFoldGeometryPackage.site finiteAxisFoldGeometryPackage.Coefficient) :
    rawReindex (G := finiteAxisFoldGeometryPackage)
      (H := finiteAxisFoldGeometryPackage) finiteAxisFoldSwapTotal system =
      system := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Identity local geometry data over the fixed adjacent axis permutation. -/
noncomputable def finiteAxisFoldSwapGeometryReadHom :
    GeomReadHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage
      finiteAxisFoldSwapTotal where
  coverage := by
    constructor
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intro axis haxis
      simp [finiteAxisFoldGeometryPackage, geomTransportAlong,
        pushGeometryPackage, pushSelectedGeometry, pushCoverage,
        finiteAxisFoldSourceGeometryPackage,
        finiteAxisFoldSourceSelectedGeometry,
        finiteAxisFoldSourceGeometryRequirements] at haxis
    · intros
      assumption
    · intros
      assumption
    · intros
      assumption
    · intro W axis haxis
      simp [finiteAxisFoldGeometryPackage, geomTransportAlong,
        pushGeometryPackage, pushSelectedGeometry, pushCoverage,
        finiteAxisFoldSourceGeometryPackage,
        finiteAxisFoldSourceSelectedGeometry,
        finiteAxisFoldSourceGeometryRequirements] at haxis
    · intros
      assumption
  overlap := by
    constructor
    intro base left right
    exact Iso.refl _
  coefficientHom := RingHom.id Int
  raw_eq := by
    change finiteAxisFoldGeometryPackage.raw =
      rawReindex finiteAxisFoldSwapTotal
        (finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int))
    have hchange :
        finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int) =
          finiteAxisFoldGeometryPackage.raw := by
      simpa only using
        (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id
          finiteAxisFoldGeometryPackage.raw)
    rw [hchange]
    exact (finiteAxisFoldSwap_rawReindex finiteAxisFoldGeometryPackage.raw).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Complete-geometry lift of the fixed adjacent axis permutation. -/
noncomputable def finiteAxisFoldSwapGeometry :
    GeometryTotalHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage where
  base := finiteAxisFoldSwapTotal
  geometry := finiteAxisFoldSwapGeometryReadHom

/-- Applying the fixed adjacent axis permutation twice is the complete-geometry
identity. -/
theorem finiteAxisFoldSwapGeometry_comp_self :
    finiteAxisFoldSwapGeometry.comp finiteAxisFoldSwapGeometry =
      GeometryTotalHom.id finiteAxisFoldGeometryPackage := by
  have hbase := finiteAxisFoldSwapTotal_square
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldSwapGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- The fixed adjacent axis permutation as a complete-geometry automorphism. -/
noncomputable def finiteAxisFoldSwapGeometryAut :
    Aut finiteAxisFoldGeometryPackage where
  hom := finiteAxisFoldSwapGeometry
  inv := finiteAxisFoldSwapGeometry
  hom_inv_id := finiteAxisFoldSwapGeometry_comp_self
  inv_hom_id := finiteAxisFoldSwapGeometry_comp_self

/-- The complete-geometry lift moves the zero signature axis to the first
signature axis. -/
theorem finiteAxisFoldSwapGeometry_axis_zero :
    finiteAxisFoldSwapGeometry.base.upper.axisMap (0 : Fin 3) =
      (1 : Fin 3) := by
  change (Equiv.swap (0 : Fin 3) 1) 0 = 1
  rfl

/-- The complete-geometry lift of the fixed adjacent axis permutation is
nonidentity. -/
theorem finiteAxisFoldSwapGeometryAut_ne_one :
    finiteAxisFoldSwapGeometryAut ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun a : Aut finiteAxisFoldGeometryPackage =>
      a.hom.base.upper.axisMap (0 : Fin 3)) equality
  change (1 : Fin 3) = 0 at axisEquality
  omega

/-- The complete-geometry swap lies over the pointed-doctrine identity. -/
@[simp]
theorem finiteAxisFoldSwapGeometry_packageBase :
    finiteAxisFoldSwapGeometry.base.base =
      ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) := by
  rfl

/-- The fixed southwest complete geometry as an object of its actual geometry
fiber. -/
noncomputable abbrev finiteAxisFoldSouthwestGeometryFiber :=
  authoredSouthwestGeometryFiberAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))

/-- The constructed swap as a vertical endomorphism of the fixed southwest
geometry fiber. -/
noncomputable def finiteAxisFoldSouthwestSwapHom :
    finiteAxisFoldSouthwestGeometryFiber ⟶
      finiteAxisFoldSouthwestGeometryFiber := by
  refine ⟨finiteAxisFoldSwapGeometry, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{0, 0} FiniteModel.carrier)
    (𝟙 finiteAxisFoldBCDatumSquare.context.square.semantic.square.southwest)
    finiteAxisFoldSwapGeometry
    finiteAxisFoldSouthwestGeometryFiber.2
    finiteAxisFoldSouthwestGeometryFiber.2
  change finiteAxisFoldSwapGeometry.base.base ≫
      eqToHom finiteAxisFoldSouthwestGeometryFiber.2 =
    eqToHom finiteAxisFoldSouthwestGeometryFiber.2 ≫ 𝟙 _
  rw [finiteAxisFoldSwapGeometry_packageBase]
  change ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) =
    ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core)
  rfl

/-- The same constructed swap, regarded as a vertical automorphism of the
fixed southwest geometry fiber. -/
noncomputable def finiteAxisFoldSouthwestSwapAut :
    Aut finiteAxisFoldSouthwestGeometryFiber where
  hom := finiteAxisFoldSouthwestSwapHom
  inv := finiteAxisFoldSouthwestSwapHom
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldSwapGeometry_comp_self
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldSwapGeometry_comp_self

/-- The fixed southwest vertical automorphism is nonidentity. -/
theorem finiteAxisFoldSouthwestSwapAut_ne_one :
    finiteAxisFoldSouthwestSwapAut ≠ 1 := by
  intro equality
  have underlying := congrArg
    (fun a : Aut finiteAxisFoldSouthwestGeometryFiber => a.hom.1) equality
  apply finiteAxisFoldSwapGeometryAut_ne_one
  apply Iso.ext
  simpa [finiteAxisFoldSouthwestSwapAut,
    finiteAxisFoldSwapGeometryAut] using underlying

/-- Canonical complete-geometry transport preserves the global signature-axis
map of every vertical fiber morphism. -/
theorem geomFiberTransportMap_axisMap
    {U : AtomCarrier} {X Y : ExtractionInstance U} (sigma : X ⟶ Y)
    {first second : GeomFiber.{0, 0} X} (hom : first ⟶ second) :
    (geomFiberTransportMap sigma hom).1.base.upper.axisMap =
      hom.1.base.upper.axisMap := by
  have factorization := congrArg
    (fun total => total.base.upper.axisMap)
    (geomFiberTransportMap_fac sigma hom)
  simpa [GeometryTotalHom.comp, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, geomFiberLift, geomTransportAlongHom,
    geomTransportAlongGeometryHom, transportAlongHom, transportAlongUpper]
    using factorization

/-- Generated exact complete-geometry pullback preserves the global
signature-axis map of every vertical fiber morphism. -/
theorem exactGeometryPullMap_axisMap
    {U : AtomCarrier} [DecidableEq U.Atom] (input : RealizableHom U)
    {first second : GeomFiber.{0, 0} input.semantic.target}
    (hom : first ⟶ second) :
    (exactGeometryPullMap input hom).1.base.upper.axisMap =
      hom.1.base.upper.axisMap := by
  have factorization := congrArg
    (fun total => total.base.upper.axisMap)
    (exactGeometryPullMap_fac input hom)
  simpa [GeometryTotalHom.comp, PackageTotalHom.comp,
    SignedExactCoreReadingHom.comp, exactGeometryPullLift,
    UpperGeometryCleavage.generatedExactGeometryHom,
    UpperGeometryCleavage.exactBaseHom, inverseCorePackageHom,
    inverseCorePackageForwardUpper] using factorization

/-- The fixed swap after the actual exact pullback along the left edge. -/
noncomputable def finiteAxisFoldLeftPulledSwapFiberAut :
    Aut (authoredExactLeftPulledGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))) :=
  (exactGeometryPullFunctor
    (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
      finiteAxisFoldSouthwestSwapAut

/-- Exact pullback along the fixed left edge and transport along the fixed top
edge carry the authored southwest swap to the actual direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectSwapFiberAut :
    Aut (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))) :=
  (geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapIso
    finiteAxisFoldLeftPulledSwapFiberAut

/-- The actual direct endpoint automorphism retains exactly the global
signature-axis map of the original fixed swap. -/
theorem finiteAxisFoldActualDirectSwapFiberAut_axisMap :
    finiteAxisFoldActualDirectSwapFiberAut.hom.1.base.upper.axisMap =
      finiteAxisFoldSwapGeometry.base.upper.axisMap := by
  calc
    _ = finiteAxisFoldLeftPulledSwapFiberAut.hom.1.base.upper.axisMap :=
      geomFiberTransportMap_axisMap
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
        finiteAxisFoldLeftPulledSwapFiberAut.hom
    _ = finiteAxisFoldSouthwestSwapAut.hom.1.base.upper.axisMap :=
      exactGeometryPullMap_axisMap
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        finiteAxisFoldSouthwestSwapAut.hom
    _ = _ := rfl

/-- The actual pull-push route cannot erase the fixed swap: exact pullback is
faithful because its counit is invertible, and exact transport is faithful
because its unit is invertible. -/
theorem finiteAxisFoldActualDirectSwapFiberAut_ne_one :
    finiteAxisFoldActualDirectSwapFiberAut ≠ 1 := by
  let leftInput := authoredExactLeftInput finiteAxisFoldBCDatumSquare
  let topInput := authoredExactTopInput finiteAxisFoldBCDatumSquare
  let pull := exactGeometryPullFunctor leftInput
  let push := geomFiberTransportFunctor
    finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
  let adjLeft := exactGeometryTransportPullAdjunction leftInput
  let adjTop := exactGeometryTransportPullAdjunction topInput
  letI : IsIso adjLeft.counit :=
    exactGeometryTransportPullCounit_isIso leftInput
  letI : IsIso adjTop.unit :=
    exactGeometryTransportPullUnit_isIso topInput
  let pullFullyFaithful := adjLeft.fullyFaithfulROfIsIsoCounit
  let pushFullyFaithful : push.FullyFaithful := by
    simpa [push, topInput, authoredExactTopInput] using
      adjTop.fullyFaithfulLOfIsIsoUnit
  intro equality
  have mappedHom := congrArg
    (fun a : Aut (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))) => a.hom) equality
  have mappedHomIdentity :
      push.map (pull.map finiteAxisFoldSouthwestSwapAut.hom) = 𝟙 _ := by
    simpa [finiteAxisFoldActualDirectSwapFiberAut, push, pull,
      topInput, leftInput] using mappedHom
  have pushEquality :
      push.map (pull.map finiteAxisFoldSouthwestSwapAut.hom) =
        push.map (pull.map (𝟙 _)) := by
    calc
      _ = 𝟙 _ := mappedHomIdentity
      _ = push.map (pull.map (𝟙 _)) := by simp
  have pullEquality :
      pull.map finiteAxisFoldSouthwestSwapAut.hom = pull.map (𝟙 _) :=
    pushFullyFaithful.map_injective pushEquality
  have sourceEquality : finiteAxisFoldSouthwestSwapAut.hom = 𝟙 _ :=
    pullFullyFaithful.map_injective pullEquality
  apply finiteAxisFoldSouthwestSwapAut_ne_one
  apply Iso.ext
  exact sourceEquality

/-- The actual direct endpoint packaged in the admissible complete-geometry
subcategory. -/
noncomputable abbrev finiteAxisFoldActualDirectAdmissibleGeometry :=
  authoredExactDirectAdmissibleGeometryAt
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible

/-- The transported fixed swap as an automorphism of the actual admissible
direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectSwapAdmissibleAut :
    Aut finiteAxisFoldActualDirectAdmissibleGeometry where
  hom := ObjectProperty.homMk finiteAxisFoldActualDirectSwapFiberAut.hom.1
  inv := ObjectProperty.homMk finiteAxisFoldActualDirectSwapFiberAut.inv.1
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      finiteAxisFoldActualDirectSwapFiberAut.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      finiteAxisFoldActualDirectSwapFiberAut.inv_hom_id

/-- Canonical normalization of the actual direct endpoint swap. -/
noncomputable def finiteAxisFoldNormalizedDirectSwapAut :
    Aut ((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).obj
      finiteAxisFoldActualDirectAdmissibleGeometry) :=
  (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapIso
    finiteAxisFoldActualDirectSwapAdmissibleAut

/-- Canonical normalization retains the fixed axis swap, so the resulting
actual normalized endpoint automorphism is nonidentity. -/
theorem finiteAxisFoldNormalizedDirectSwapAut_ne_one :
    finiteAxisFoldNormalizedDirectSwapAut ≠ 1 := by
  intro equality
  have axisEquality := congrArg
    (fun a : Aut ((geometryNormalizationFunctor.{0, 0}
        FiniteModel.carrier).obj
          finiteAxisFoldActualDirectAdmissibleGeometry) =>
      a.hom.f.hom.base.upper.axisMap) equality
  have actualAxisIdentity :
      finiteAxisFoldActualDirectSwapFiberAut.hom.1.base.upper.axisMap =
        _root_.id := by
    simpa [finiteAxisFoldNormalizedDirectSwapAut,
      finiteAxisFoldActualDirectSwapAdmissibleAut,
      geometryNormalizationFunctor, canonicalAdmissibleGeometryNormalization,
      canonicalGeometryNormalization, canonicalObjectNormalizationTotal,
      PackageTotalHom.comp, SignedExactCoreReadingHom.comp] using axisEquality
  rw [finiteAxisFoldActualDirectSwapFiberAut_axisMap] at actualAxisIdentity
  have moved := congrFun actualAxisIdentity (0 : Fin 3)
  change (1 : Fin 3) = 0 at moved
  omega

/-- The actual `barAlpha` after canonical normalization. -/
noncomputable abbrev finiteAxisFoldNormalizedBarAlphaIso :=
  (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapIso
    (authoredExactBarAlphaAdmissibleIsoAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible)

/-- Conjugating the normalized target endpoint by `barAlpha` turns the fixed
source swap into an actual comparison-preserving pair. -/
noncomputable def finiteAxisFoldNormalizedComparisonSwap :
    FiniteAxisFoldComparisonRestrictionKernel.NormalizedComparison :=
  generatedArrowComparisonSectionHom finiteAxisFoldNormalizedBarAlphaIso
    finiteAxisFoldNormalizedDirectSwapAut

/-- The source endpoint of the constructed normalized comparison is exactly
the fixed normalized swap. -/
@[simp]
theorem finiteAxisFoldNormalizedComparisonSwap_source :
    finiteAxisFoldNormalizedComparisonSwap.1.1 =
      finiteAxisFoldNormalizedDirectSwapAut := by
  rfl

/-- The fixed finite-axis-fold input therefore has a nonidentity element in
its full actual normalized comparison group. -/
theorem finiteAxisFoldNormalizedComparisonSwap_ne_one :
    finiteAxisFoldNormalizedComparisonSwap ≠ 1 := by
  intro equality
  have sourceEquality := congrArg
    (fun t : FiniteAxisFoldComparisonRestrictionKernel.NormalizedComparison =>
      t.1.1) equality
  apply finiteAxisFoldNormalizedDirectSwapAut_ne_one
  simpa using sourceEquality

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
