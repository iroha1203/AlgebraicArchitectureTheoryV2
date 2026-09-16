import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldSourceContextPermutationAction
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualBackwardToggle
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNormalizedAxisProjection
import Formal.Util.AssertStandardAxioms

/-!
# Finite Extension permutations through the complete-geometry route

An independently supplied finite carrier `E` and a table `p : Equiv.Perm E`
already act on every context of the fixed finite-axis-fold source.  This file
lifts that primitive action to complete source geometry.  The forward context
functor remains the identity, while the stored inverse functor applies the
Extension permutation.  Consequently the local geometry comparisons remain
identity maps and satisfy naturality without accepting a completed geometry
map as input.

The ordinary group-homomorphic section stores `p⁻¹` in the backward functor.
This inverse is essential: composition of stored inverse functors has the
opposite order.  Both `p` and `p⁻¹` are therefore retained explicitly rather
than identified by the Boolean involution used in the earlier two-element
fragment.

The section is then carried, functorially, through the fixed source-to-
southwest transport, the fixed exact-left pull, top transport, admissible
packaging, and canonical normalization.  This module constructs the full
normalized automorphism homomorphism.  It does not yet prove that every image
lies in the joint local-fiber kernel, that the normalized homomorphism is
injective, or that its image covers the full residual group.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

set_option maxHeartbeats 1200000

private noncomputable abbrev FiniteAxisFoldPermutationGeometrySource :=
  finiteAxisFoldSourceGeometryPackage

private noncomputable abbrev FiniteAxisFoldPermutationGeometryCore :=
  FiniteAxisFoldPermutationGeometrySource.core

private abbrev FiniteAxisFoldPermutationGeometryContextCategory :=
  Site.ContextCategoryObject
    FiniteAxisFoldPermutationGeometryCore.contextPreorder

/-! ## Context functors and their composition order -/

/-- The primitive Extension permutation on the complete source context
category.  Morphisms exist because Extension values are invisible to the
fixed source readability relation. -/
noncomputable def finiteAxisFoldSourceContextPermutationFunctor
    {E : Type} (permutation : Equiv.Perm E) :
    FiniteAxisFoldPermutationGeometryContextCategory ⥤
      FiniteAxisFoldPermutationGeometryContextCategory where
  obj W := finiteAxisFoldSourceContextObjectPermutation permutation W
  map {W V} f := by
    apply homOfLE
    exact FiniteAxisFoldPermutationGeometryCore.contextPreorder.trans
      (finiteAxisFoldSourceContextPermutation_le_context permutation W.ctx)
      (FiniteAxisFoldPermutationGeometryCore.contextPreorder.trans f.le
        (finiteAxisFoldSourceContext_le_permutation permutation V.ctx))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Functor composition records the reversed table order forced by ordinary
categorical composition. -/
theorem finiteAxisFoldSourceContextPermutationFunctor_comp
    {E : Type} (first second : Equiv.Perm E) :
    finiteAxisFoldSourceContextPermutationFunctor first ⋙
        finiteAxisFoldSourceContextPermutationFunctor second =
      finiteAxisFoldSourceContextPermutationFunctor (second * first) := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact finiteAxisFoldSourceContextObjectPermutation_mul second first W
  · intros
    exact Subsingleton.elim _ _

/-- The identity table gives the identity context functor. -/
theorem finiteAxisFoldSourceContextPermutationFunctor_one
    (E : Type) :
    finiteAxisFoldSourceContextPermutationFunctor (1 : Equiv.Perm E) =
      CategoryTheory.Functor.id
        FiniteAxisFoldPermutationGeometryContextCategory := by
  refine CategoryTheory.Functor.ext (fun W => ?_) ?_
  · exact finiteAxisFoldSourceContextObjectPermutation_one W
  · intros
    exact Subsingleton.elim _ _

private theorem finiteAxisFoldPermutationGeometrySubsingleton_heq_of_type_eq
    {alpha beta : Sort _} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Asymmetric context equivalence with identity forward functor and the
independent permutation stored in the inverse functor. -/
noncomputable def finiteAxisFoldSourceBackwardPermutationContextEquivalence
    {E : Type} (permutation : Equiv.Perm E) :
    FiniteAxisFoldPermutationGeometryContextCategory ≌
      FiniteAxisFoldPermutationGeometryContextCategory :=
  CategoryTheory.Equivalence.mk
    (CategoryTheory.Functor.id
      FiniteAxisFoldPermutationGeometryContextCategory)
    (finiteAxisFoldSourceContextPermutationFunctor permutation)
    (NatIso.ofComponents
      (fun context => Iso.mk
        (homOfLE
          (finiteAxisFoldSourceContext_le_permutation permutation context.ctx))
        (homOfLE
          (finiteAxisFoldSourceContextPermutation_le_context permutation context.ctx))
        (by apply Subsingleton.elim)
        (by apply Subsingleton.elim))
      (by intros; apply Subsingleton.elim))
    (NatIso.ofComponents
      (fun context => Iso.mk
        (homOfLE
          (finiteAxisFoldSourceContextPermutation_le_context permutation context.ctx))
        (homOfLE
          (finiteAxisFoldSourceContext_le_permutation permutation context.ctx))
        (by apply Subsingleton.elim)
        (by apply Subsingleton.elim))
      (by intros; apply Subsingleton.elim))

/-- Stored backward actions compose in ordinary table order. -/
theorem finiteAxisFoldSourceBackwardPermutationContextEquivalence_trans
    {E : Type} (first second : Equiv.Perm E) :
    (finiteAxisFoldSourceBackwardPermutationContextEquivalence first).trans
        (finiteAxisFoldSourceBackwardPermutationContextEquivalence second) =
      finiteAxisFoldSourceBackwardPermutationContextEquivalence
        (first * second) := by
  have hfunctor :
      ((finiteAxisFoldSourceBackwardPermutationContextEquivalence first).trans
        (finiteAxisFoldSourceBackwardPermutationContextEquivalence second)).functor =
        CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory := by
    rfl
  have hinverse :
      ((finiteAxisFoldSourceBackwardPermutationContextEquivalence first).trans
        (finiteAxisFoldSourceBackwardPermutationContextEquivalence second)).inverse =
        finiteAxisFoldSourceContextPermutationFunctor (first * second) := by
    exact finiteAxisFoldSourceContextPermutationFunctor_comp second first
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldPermutationGeometrySubsingleton_heq_of_type_eq
    apply congrArg
      (fun F =>
        (CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory) ≅ F)
    rw [hfunctor, hinverse]
    rfl
  · apply finiteAxisFoldPermutationGeometrySubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => F ≅
        (CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory))
    rw [hfunctor, hinverse]
    rfl

theorem finiteAxisFoldSourceBackwardPermutationContextEquivalence_one
    (E : Type) :
    finiteAxisFoldSourceBackwardPermutationContextEquivalence
        (1 : Equiv.Perm E) =
      CategoryTheory.Equivalence.refl := by
  have hfunctor :
      (finiteAxisFoldSourceBackwardPermutationContextEquivalence
        (1 : Equiv.Perm E)).functor =
        CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory := rfl
  have hinverse :
      (finiteAxisFoldSourceBackwardPermutationContextEquivalence
        (1 : Equiv.Perm E)).inverse =
        CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory :=
    finiteAxisFoldSourceContextPermutationFunctor_one E
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldPermutationGeometrySubsingleton_heq_of_type_eq
    apply congrArg
      (fun F =>
        (CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory) ≅ F)
    rw [hfunctor, hinverse]
    rfl
  · apply finiteAxisFoldPermutationGeometrySubsingleton_heq_of_type_eq
    apply congrArg
      (fun F => F ≅
        (CategoryTheory.Functor.id
          FiniteAxisFoldPermutationGeometryContextCategory))
    rw [hfunctor, hinverse]
    rfl

/-! ## Complete source geometry -/

noncomputable def finiteAxisFoldSourceBackwardPermutationEquationTransport
    {E : Type} (permutation : Equiv.Perm E) :
    EquationSystemExactTransport
      FiniteAxisFoldPermutationGeometryCore.algebra.equationSystem
      FiniteAxisFoldPermutationGeometryCore.algebra.equationSystem
      (Equiv.refl FiniteModel.carrier.Atom) id where
  contextEquivalence :=
    finiteAxisFoldSourceBackwardPermutationContextEquivalence permutation
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl Int
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by intros; rfl

noncomputable def finiteAxisFoldSourceBackwardPermutationUpper
    {E : Type} (permutation : Equiv.Perm E) :
    SignedExactCoreReadingHom FiniteAxisFoldPermutationGeometryCore
      FiniteAxisFoldPermutationGeometryCore :=
  { SignedExactCoreReadingHom.refl FiniteAxisFoldPermutationGeometryCore with
    equationTransport :=
      finiteAxisFoldSourceBackwardPermutationEquationTransport permutation }

noncomputable def finiteAxisFoldSourceBackwardPermutationTotal
    {E : Type} (permutation : Equiv.Perm E) :
    PackageTotalHom FiniteAxisFoldPermutationGeometryCore
      FiniteAxisFoldPermutationGeometryCore where
  base := ExtInstHom.id (packagePoint FiniteAxisFoldPermutationGeometryCore)
  upper := finiteAxisFoldSourceBackwardPermutationUpper permutation
  atomEquiv_eq := rfl

theorem finiteAxisFoldSourceBackwardPermutationUpper_comp
    {E : Type} (first second : Equiv.Perm E) :
    (finiteAxisFoldSourceBackwardPermutationUpper first).comp
        (finiteAxisFoldSourceBackwardPermutationUpper second) =
      finiteAxisFoldSourceBackwardPermutationUpper (first * second) := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · rfl
  · apply equationSystemExactTransport_hext
    · rfl
    · rfl
    · exact finiteAxisFoldSourceBackwardPermutationContextEquivalence_trans
        first second
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem finiteAxisFoldSourceBackwardPermutationTotal_comp
    {E : Type} (first second : Equiv.Perm E) :
    (finiteAxisFoldSourceBackwardPermutationTotal first).comp
        (finiteAxisFoldSourceBackwardPermutationTotal second) =
      finiteAxisFoldSourceBackwardPermutationTotal (first * second) := by
  apply PackageTotalHom.ext
  · rfl
  · exact finiteAxisFoldSourceBackwardPermutationUpper_comp first second

theorem finiteAxisFoldSourceBackwardPermutationTotal_one
    (E : Type) :
    finiteAxisFoldSourceBackwardPermutationTotal (1 : Equiv.Perm E) =
      PackageTotalHom.id FiniteAxisFoldPermutationGeometryCore := by
  apply PackageTotalHom.ext
  · rfl
  · apply SignedExactCoreReadingHom.ext
    · rfl
    · rfl
    · apply equationSystemExactTransport_hext
      · rfl
      · rfl
      · exact finiteAxisFoldSourceBackwardPermutationContextEquivalence_one E
      · rfl
      · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem finiteAxisFoldSourceBackwardPermutation_rawReindex
    {E : Type} (permutation : Equiv.Perm E) :
    rawReindex (G := FiniteAxisFoldPermutationGeometrySource)
        (H := FiniteAxisFoldPermutationGeometrySource)
        (finiteAxisFoldSourceBackwardPermutationTotal permutation)
        FiniteAxisFoldPermutationGeometrySource.raw =
      FiniteAxisFoldPermutationGeometrySource.raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

noncomputable def finiteAxisFoldSourceBackwardPermutationGeomReadHom
    {E : Type} (permutation : Equiv.Perm E) :
    GeomReadHom FiniteAxisFoldPermutationGeometrySource
      FiniteAxisFoldPermutationGeometrySource
      (finiteAxisFoldSourceBackwardPermutationTotal permutation) where
  coverage := by constructor <;> intros <;> assumption
  overlap := by
    constructor
    intro base left right
    refine Iso.mk (homOfLE ?_) (homOfLE ?_)
      (by apply Subsingleton.elim) (by apply Subsingleton.elim)
    · change FiniteAxisFoldPermutationGeometryCore.contextPreorder.le
        (Site.productContext
          (finiteAxisFoldSourceContextPermutation permutation left)
          (finiteAxisFoldSourceContextPermutation permutation right))
        (Site.productContext left right)
      refine ⟨{
        supportMap := id
        axisMap := id
        observableRestrict := id }, ?_⟩
      refine ⟨fun h => h, fun h => h, ?_, fun h => ?_⟩
      · intro observable h
        cases observable <;> exact h
      · exact (Site.productContext left right).supportReads_objectFamily h
    · change FiniteAxisFoldPermutationGeometryCore.contextPreorder.le
        (Site.productContext left right)
        (Site.productContext
          (finiteAxisFoldSourceContextPermutation permutation left)
          (finiteAxisFoldSourceContextPermutation permutation right))
      refine ⟨{
        supportMap := id
        axisMap := id
        observableRestrict := id }, ?_⟩
      refine ⟨fun h => h, fun h => h, ?_, fun h => ?_⟩
      · intro observable h
        cases observable <;> exact h
      · exact (Site.productContext
          (finiteAxisFoldSourceContextPermutation permutation left)
          (finiteAxisFoldSourceContextPermutation permutation right)).supportReads_objectFamily h
  coefficientHom := RingHom.id Int
  raw_eq := by
    change FiniteAxisFoldPermutationGeometrySource.raw =
      rawReindex (finiteAxisFoldSourceBackwardPermutationTotal permutation)
        (FiniteAxisFoldPermutationGeometrySource.raw.baseChange (RingHom.id Int))
    have hchange :
        FiniteAxisFoldPermutationGeometrySource.raw.baseChange (RingHom.id Int) =
          FiniteAxisFoldPermutationGeometrySource.raw := by
      simpa only using
        (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id
          FiniteAxisFoldPermutationGeometrySource.raw)
    rw [hchange]
    exact (finiteAxisFoldSourceBackwardPermutation_rawReindex permutation).symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality := by intros; rfl
  axis_naturality := by intros; rfl
  observable_naturality := by intros; rfl

noncomputable def finiteAxisFoldSourceBackwardPermutationGeometry
    {E : Type} (permutation : Equiv.Perm E) :
    GeometryTotalHom FiniteAxisFoldPermutationGeometrySource
      FiniteAxisFoldPermutationGeometrySource where
  base := finiteAxisFoldSourceBackwardPermutationTotal permutation
  geometry := finiteAxisFoldSourceBackwardPermutationGeomReadHom permutation

private theorem finiteAxisFoldSourcePermutationGeomReadHom_heq_of_base_eq
    {firstBase secondBase : PackageTotalHom
      FiniteAxisFoldPermutationGeometryCore
      FiniteAxisFoldPermutationGeometryCore}
    (first : GeomReadHom FiniteAxisFoldPermutationGeometrySource
      FiniteAxisFoldPermutationGeometrySource firstBase)
    (second : GeomReadHom FiniteAxisFoldPermutationGeometrySource
      FiniteAxisFoldPermutationGeometrySource secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

theorem finiteAxisFoldSourceBackwardPermutationGeometry_comp
    {E : Type} (first second : Equiv.Perm E) :
    (finiteAxisFoldSourceBackwardPermutationGeometry first).comp
        (finiteAxisFoldSourceBackwardPermutationGeometry second) =
      finiteAxisFoldSourceBackwardPermutationGeometry (first * second) := by
  have hbase := finiteAxisFoldSourceBackwardPermutationTotal_comp first second
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldSourcePermutationGeomReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

theorem finiteAxisFoldSourceBackwardPermutationGeometry_one
    (E : Type) :
    finiteAxisFoldSourceBackwardPermutationGeometry (1 : Equiv.Perm E) =
      GeometryTotalHom.id FiniteAxisFoldPermutationGeometrySource := by
  have hbase := finiteAxisFoldSourceBackwardPermutationTotal_one E
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldSourcePermutationGeomReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-! ## Ordinary source group action and the fixed actual route -/

/-- A source automorphism with ordinary group orientation.  Its hom stores
`p⁻¹` backward and its inverse stores `p` backward. -/
noncomputable def finiteAxisFoldSourcePermutationGeometryAut
    {E : Type} (permutation : Equiv.Perm E) :
    Aut FiniteAxisFoldPermutationGeometrySource where
  hom := finiteAxisFoldSourceBackwardPermutationGeometry permutation⁻¹
  inv := finiteAxisFoldSourceBackwardPermutationGeometry permutation
  hom_inv_id := by
    change
      (finiteAxisFoldSourceBackwardPermutationGeometry permutation⁻¹).comp
          (finiteAxisFoldSourceBackwardPermutationGeometry permutation) =
        GeometryTotalHom.id FiniteAxisFoldPermutationGeometrySource
    rw [finiteAxisFoldSourceBackwardPermutationGeometry_comp]
    simpa using finiteAxisFoldSourceBackwardPermutationGeometry_one E
  inv_hom_id := by
    change
      (finiteAxisFoldSourceBackwardPermutationGeometry permutation).comp
          (finiteAxisFoldSourceBackwardPermutationGeometry permutation⁻¹) =
        GeometryTotalHom.id FiniteAxisFoldPermutationGeometrySource
    rw [finiteAxisFoldSourceBackwardPermutationGeometry_comp]
    simpa using finiteAxisFoldSourceBackwardPermutationGeometry_one E

/-- Arbitrary finite Extension tables act by complete source-geometry
automorphisms. -/
noncomputable def finiteAxisFoldSourcePermutationGeometrySectionHom
    (E : Type) :
    Equiv.Perm E →* Aut FiniteAxisFoldPermutationGeometrySource where
  toFun := finiteAxisFoldSourcePermutationGeometryAut
  map_one' := by
    apply Iso.ext
    exact finiteAxisFoldSourceBackwardPermutationGeometry_one E
  map_mul' first second := by
    apply Iso.ext
    rw [Aut.Aut_mul_def]
    change
      finiteAxisFoldSourceBackwardPermutationGeometry (first * second)⁻¹ =
        (finiteAxisFoldSourceBackwardPermutationGeometry second⁻¹).comp
          (finiteAxisFoldSourceBackwardPermutationGeometry first⁻¹)
    symm
    rw [finiteAxisFoldSourceBackwardPermutationGeometry_comp, mul_inv_rev]

/-- The complete source-geometry action retains the full independently
supplied finite permutation table.  Faithfulness is read from the canonical
source probes constructed before the semantic route. -/
theorem finiteAxisFoldSourcePermutationGeometrySectionHom_injective
    (E : Type) [Fintype E] :
    Function.Injective (finiteAxisFoldSourcePermutationGeometrySectionHom E) := by
  intro first second equality
  have inverseFunctorEquality := congrArg
    (fun automorphism : Aut FiniteAxisFoldPermutationGeometrySource =>
      automorphism.hom.base.upper.equationTransport.contextEquivalence.inverse)
    equality
  have inverseTableEquality : first⁻¹ = second⁻¹ := by
    apply finiteAxisFoldSourceContextObjectPermHom_injective E
    apply Equiv.ext
    intro context
    exact congrArg (fun functor => functor.obj context) inverseFunctorEquality
  calc
    first = (first⁻¹)⁻¹ := by simp
    _ = (second⁻¹)⁻¹ := congrArg Inv.inv inverseTableEquality
    _ = second := by simp

/-- Vertical form of the complete source action. -/
noncomputable def finiteAxisFoldSourcePermutationGeometryFiberSectionHom
    (E : Type) :
    Equiv.Perm E →* Aut (geomFiberMk finiteAxisFoldSourceGeometryPackage) where
  toFun permutation := {
    hom := ⟨(finiteAxisFoldSourcePermutationGeometryAut permutation).hom, by
      apply CategoryTheory.IsHomLift.of_commsq
        (crossStageProjection.{0, 0} FiniteModel.carrier)
        (𝟙 (packagePoint finiteAxisFoldSourceGeometryPackage.core))
        (finiteAxisFoldSourcePermutationGeometryAut permutation).hom rfl rfl
      rfl⟩
    inv := ⟨(finiteAxisFoldSourcePermutationGeometryAut permutation).inv, by
      apply CategoryTheory.IsHomLift.of_commsq
        (crossStageProjection.{0, 0} FiniteModel.carrier)
        (𝟙 (packagePoint finiteAxisFoldSourceGeometryPackage.core))
        (finiteAxisFoldSourcePermutationGeometryAut permutation).inv rfl rfl
      rfl⟩
    hom_inv_id := by
      apply CategoryTheory.Functor.Fiber.hom_ext
      exact (finiteAxisFoldSourcePermutationGeometryAut permutation).hom_inv_id
    inv_hom_id := by
      apply CategoryTheory.Functor.Fiber.hom_ext
      exact (finiteAxisFoldSourcePermutationGeometryAut permutation).inv_hom_id }
  map_one' := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact congrArg Iso.hom
      (map_one (finiteAxisFoldSourcePermutationGeometrySectionHom E))
  map_mul' first second := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact congrArg Iso.hom
      (map_mul (finiteAxisFoldSourcePermutationGeometrySectionHom E)
        first second)

local instance finiteAxisFoldSourcePermutationGeometryAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private theorem finiteAxisFoldSourcePermutationTransported_object_eq_southwest :
    (geomFiberTransportFunctor.{0, 0}
      finiteAxisFoldSourceToSouthwestExtInstHom).obj
        (geomFiberMk finiteAxisFoldSourceGeometryPackage) =
      finiteAxisFoldSouthwestGeometryFiber := by
  apply Subtype.ext
  rfl

/-- Retagging the canonical source-to-southwest transport is conjugation by
the proof-irrelevant endpoint equality, hence a genuine group homomorphism. -/
noncomputable def finiteAxisFoldSouthwestPermutationGeometrySectionHom
    (E : Type) :
    Equiv.Perm E →* Aut finiteAxisFoldSouthwestGeometryFiber :=
  (Aut.autMulEquivOfIso
    (eqToIso finiteAxisFoldSourcePermutationTransported_object_eq_southwest)).toMonoidHom.comp
    (((geomFiberTransportFunctor.{0, 0}
      finiteAxisFoldSourceToSouthwestExtInstHom).mapAut _).comp
        (finiteAxisFoldSourcePermutationGeometryFiberSectionHom E))

/-- The arbitrary finite Extension action at the fixed actual direct
endpoint. -/
noncomputable def finiteAxisFoldActualDirectPermutationGeometrySectionHom
    (E : Type) :
    Equiv.Perm E →*
      Aut (authoredExactDirectGeometryAt
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))) :=
  ((geomFiberTransportFunctor
      finiteAxisFoldBCDatumSquare.context.square.semantic.square.top).mapAut _).comp
    (((exactGeometryPullFunctor
      (authoredExactLeftInput finiteAxisFoldBCDatumSquare)).mapAut _).comp
        (finiteAxisFoldSouthwestPermutationGeometrySectionHom E))

/-- The same primitive finite Extension action after admissible packaging and
canonical normalization. -/
noncomputable def finiteAxisFoldNormalizedPermutationGeometrySectionHom
    (E : Type) :
    Equiv.Perm E →* Aut FiniteAxisFoldNormalizedDirectGeometry :=
  ((geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapAut _).comp
    (finiteAxisFoldActualDirectAdmissibleAutomorphismHom.comp
      (finiteAxisFoldActualDirectPermutationGeometrySectionHom E))

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
