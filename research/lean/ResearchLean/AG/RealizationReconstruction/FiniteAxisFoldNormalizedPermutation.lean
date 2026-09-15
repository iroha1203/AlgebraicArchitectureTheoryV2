import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNormalizedAxisSwap
import Formal.Util.AssertStandardAxioms

/-!
# All finite-axis-fold signature permutations at the normalized endpoint

The fixed finite-axis-fold input has three signature axes.  This file replaces
the single adjacent swap used in Cycle 66 by an arbitrary finite table
`p : Equiv.Perm (Fin 3)`.  The complete-geometry morphism is rebuilt from the
existing primitive package-level permutation and identity local geometry
data, then carried through the same exact left-pull and top-transport route.

No completed geometry morphism, automorphism, comparison element, or source
preimage certificate is accepted as input.  The only variable datum is the
finite permutation table itself.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 800000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance finiteAxisFoldNormalizedPermutationAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The primitive signature permutation leaves every raw restriction system
on the fixed transported geometry unchanged. -/
theorem finiteAxisFoldPermutation_rawReindex
    (permutation : Equiv.Perm (Fin 3))
    (system : LawAlgebra.RawAmbientRestrictionSystem
      finiteAxisFoldGeometryPackage.site finiteAxisFoldGeometryPackage.Coefficient) :
    rawReindex (G := finiteAxisFoldGeometryPackage)
      (H := finiteAxisFoldGeometryPackage)
      (finiteAxisFoldPermutationTotal permutation) system = system := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Identity local geometry data over one primitive signature permutation. -/
noncomputable def finiteAxisFoldPermutationGeometryReadHom
    (permutation : Equiv.Perm (Fin 3)) :
    GeomReadHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage
      (finiteAxisFoldPermutationTotal permutation) where
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
      rawReindex (finiteAxisFoldPermutationTotal permutation)
        (finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int))
    have hchange :
        finiteAxisFoldGeometryPackage.raw.baseChange (RingHom.id Int) =
          finiteAxisFoldGeometryPackage.raw := by
      simpa only using
        (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id
          finiteAxisFoldGeometryPackage.raw)
    rw [hchange]
    exact (finiteAxisFoldPermutation_rawReindex permutation
      finiteAxisFoldGeometryPackage.raw).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- Complete-geometry lift of an arbitrary primitive three-axis table. -/
noncomputable def finiteAxisFoldPermutationGeometry
    (permutation : Equiv.Perm (Fin 3)) :
    GeometryTotalHom finiteAxisFoldGeometryPackage finiteAxisFoldGeometryPackage where
  base := finiteAxisFoldPermutationTotal permutation
  geometry := finiteAxisFoldPermutationGeometryReadHom permutation

private theorem finiteAxisFoldPermutationGeometryReadHom_heq_of_base_eq
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

/-- Composition of complete-geometry permutation recipes is composition of
their finite axis tables. -/
theorem finiteAxisFoldPermutationGeometry_comp
    (first second : Equiv.Perm (Fin 3)) :
    (finiteAxisFoldPermutationGeometry first).comp
        (finiteAxisFoldPermutationGeometry second) =
      finiteAxisFoldPermutationGeometry (first.trans second) := by
  have hbase := finiteAxisFoldPermutationTotal_comp first second
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldPermutationGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- The identity axis table gives the complete-geometry identity. -/
theorem finiteAxisFoldPermutationGeometry_refl :
    finiteAxisFoldPermutationGeometry (Equiv.refl (Fin 3)) =
      GeometryTotalHom.id finiteAxisFoldGeometryPackage := by
  have hbase := finiteAxisFoldPermutationTotal_refl
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldPermutationGeometryReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- An arbitrary primitive axis table as a complete-geometry automorphism. -/
noncomputable def finiteAxisFoldPermutationGeometryAut
    (permutation : Equiv.Perm (Fin 3)) : Aut finiteAxisFoldGeometryPackage where
  hom := finiteAxisFoldPermutationGeometry permutation
  inv := finiteAxisFoldPermutationGeometry permutation.symm
  hom_inv_id := by
    change (finiteAxisFoldPermutationGeometry permutation).comp
      (finiteAxisFoldPermutationGeometry permutation.symm) = _
    rw [finiteAxisFoldPermutationGeometry_comp]
    rw [show permutation.trans permutation.symm = Equiv.refl (Fin 3) by
      apply Equiv.ext
      intro axis
      simp]
    exact finiteAxisFoldPermutationGeometry_refl
  inv_hom_id := by
    change (finiteAxisFoldPermutationGeometry permutation.symm).comp
      (finiteAxisFoldPermutationGeometry permutation) = _
    rw [finiteAxisFoldPermutationGeometry_comp]
    rw [show permutation.symm.trans permutation = Equiv.refl (Fin 3) by
      apply Equiv.ext
      intro axis
      simp]
    exact finiteAxisFoldPermutationGeometry_refl

/-- Every complete-geometry permutation recipe has exactly its input global
signature-axis table. -/
@[simp]
theorem finiteAxisFoldPermutationGeometry_axisMap
    (permutation : Equiv.Perm (Fin 3)) :
    (finiteAxisFoldPermutationGeometry permutation).base.upper.axisMap =
      permutation := by
  rfl

/-- The complete-geometry permutation lies over the pointed-doctrine
identity. -/
@[simp]
theorem finiteAxisFoldPermutationGeometry_packageBase
    (permutation : Equiv.Perm (Fin 3)) :
    (finiteAxisFoldPermutationGeometry permutation).base.base =
      ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) := by
  rfl

/-- A primitive axis table as a vertical endomorphism of the fixed southwest
geometry fiber. -/
noncomputable def finiteAxisFoldSouthwestPermutationHom
    (permutation : Equiv.Perm (Fin 3)) :
    finiteAxisFoldSouthwestGeometryFiber ⟶ finiteAxisFoldSouthwestGeometryFiber := by
  refine ⟨finiteAxisFoldPermutationGeometry permutation, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{0, 0} FiniteModel.carrier)
    (𝟙 finiteAxisFoldBCDatumSquare.context.square.semantic.square.southwest)
    (finiteAxisFoldPermutationGeometry permutation)
    finiteAxisFoldSouthwestGeometryFiber.2
    finiteAxisFoldSouthwestGeometryFiber.2
  change (finiteAxisFoldPermutationGeometry permutation).base.base ≫
      eqToHom finiteAxisFoldSouthwestGeometryFiber.2 =
    eqToHom finiteAxisFoldSouthwestGeometryFiber.2 ≫ 𝟙 _
  rw [finiteAxisFoldPermutationGeometry_packageBase]
  change ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core) =
    ExtInstHom.id (packagePoint finiteAxisFoldGeometryPackage.core)
  rfl

/-- A primitive axis table as a vertical automorphism of the fixed southwest
geometry fiber. -/
noncomputable def finiteAxisFoldSouthwestPermutationAut
    (permutation : Equiv.Perm (Fin 3)) :
    Aut finiteAxisFoldSouthwestGeometryFiber where
  hom := finiteAxisFoldSouthwestPermutationHom permutation
  inv := finiteAxisFoldSouthwestPermutationHom permutation.symm
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    calc
      (finiteAxisFoldPermutationGeometry permutation).comp
          (finiteAxisFoldPermutationGeometry permutation.symm) =
        finiteAxisFoldPermutationGeometry
          (permutation.trans permutation.symm) :=
        finiteAxisFoldPermutationGeometry_comp permutation permutation.symm
      _ = finiteAxisFoldPermutationGeometry (Equiv.refl (Fin 3)) := by
        congr 1
        apply Equiv.ext
        intro axis
        simp
      _ = GeometryTotalHom.id finiteAxisFoldGeometryPackage :=
        finiteAxisFoldPermutationGeometry_refl
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    calc
      (finiteAxisFoldPermutationGeometry permutation.symm).comp
          (finiteAxisFoldPermutationGeometry permutation) =
        finiteAxisFoldPermutationGeometry
          (permutation.symm.trans permutation) :=
        finiteAxisFoldPermutationGeometry_comp permutation.symm permutation
      _ = finiteAxisFoldPermutationGeometry (Equiv.refl (Fin 3)) := by
        congr 1
        apply Equiv.ext
        intro axis
        simp
      _ = GeometryTotalHom.id finiteAxisFoldGeometryPackage :=
        finiteAxisFoldPermutationGeometry_refl

/-- Exact pullback along the fixed left edge and transport along the fixed top
edge carry every primitive axis table to the actual direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectPermutationAut
    (permutation : Equiv.Perm (Fin 3)) :
    Aut (authoredExactDirectGeometryAt
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))) :=
  (geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapIso
    ((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
        (finiteAxisFoldSouthwestPermutationAut permutation))

/-- The actual pull-push route retains the input finite signature-axis table. -/
theorem finiteAxisFoldActualDirectPermutationAut_axisMap
    (permutation : Equiv.Perm (Fin 3)) :
    (finiteAxisFoldActualDirectPermutationAut permutation).hom.1.base.upper.axisMap =
      permutation := by
  calc
    _ = ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
        (finiteAxisFoldSouthwestPermutationAut permutation)).hom.1.base.upper.axisMap :=
      geomFiberTransportMap_axisMap
        finiteAxisFoldBCDatumSquare.context.square.semantic.square.top
        ((exactGeometryPullFunctor
          (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapIso
            (finiteAxisFoldSouthwestPermutationAut permutation)).hom
    _ = (finiteAxisFoldSouthwestPermutationAut
          permutation).hom.1.base.upper.axisMap :=
      exactGeometryPullMap_axisMap
        (authoredExactLeftInput finiteAxisFoldBCDatumSquare)
        (finiteAxisFoldSouthwestPermutationAut permutation).hom
    _ = permutation := rfl

/-- The transported primitive permutation packaged in the independently
defined admissible direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectPermutationAdmissibleAut
    (permutation : Equiv.Perm (Fin 3)) :
    Aut finiteAxisFoldActualDirectAdmissibleGeometry where
  hom := ObjectProperty.homMk
    (finiteAxisFoldActualDirectPermutationAut permutation).hom.1
  inv := ObjectProperty.homMk
    (finiteAxisFoldActualDirectPermutationAut permutation).inv.1
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      (finiteAxisFoldActualDirectPermutationAut permutation).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      (finiteAxisFoldActualDirectPermutationAut permutation).inv_hom_id

/-- Canonical normalization of an arbitrary transported finite axis table. -/
noncomputable def finiteAxisFoldNormalizedDirectPermutationAut
    (permutation : Equiv.Perm (Fin 3)) :
    Aut ((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).obj
      finiteAxisFoldActualDirectAdmissibleGeometry) :=
  (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapIso
    (finiteAxisFoldActualDirectPermutationAdmissibleAut permutation)

end

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
