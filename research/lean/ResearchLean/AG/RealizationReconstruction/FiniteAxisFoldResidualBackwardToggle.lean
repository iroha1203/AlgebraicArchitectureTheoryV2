import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualFaithfulAction
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldResidualContextAction
import Formal.Util.AssertStandardAxioms

/-!
# A backward-only Extension toggle for finite-axis-fold residual analysis

Cycle 76 constructed a source context involution which changes only an
Extension value.  The first complete-geometry lift used that involution in the
forward context functor, where the canonical selected context morphisms later
created an actual naturality obstruction.  This file uses an asymmetric but
equivalent presentation: the forward context functor is the identity and the
stored inverse functor is the same source-owned Extension toggle.

The unit and counit are constructed from the two readable arrows already
proved for every source context.  Consequently no completed context map or
selected representable subset is an input.  Identity local geometry data now
satisfy naturality definitionally, while the stored backward action still
moves the explicit Boolean-false context.
-/

namespace AAT.AG.RealizationReconstruction

universe v

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open CrossStageCoherence TransportCoherence FullGeometryNormalization

noncomputable section

private noncomputable abbrev FiniteAxisFoldBackwardSource :=
  finiteAxisFoldSourceGeometryPackage

private noncomputable abbrev FiniteAxisFoldBackwardCore :=
  FiniteAxisFoldBackwardSource.core

private abbrev FiniteAxisFoldBackwardContextCategory :=
  Site.ContextCategoryObject FiniteAxisFoldBackwardCore.contextPreorder

private theorem finiteAxisFoldBackwardSubsingleton_heq_of_type_eq
    {alpha beta : Sort v} [Subsingleton alpha] [Subsingleton beta]
    (type_eq : alpha = beta) (first : alpha) (second : beta) :
    HEq first second := by
  cases type_eq
  exact heq_of_eq (Subsingleton.elim _ _)

/-- Context equivalence with identity forward functor and the independently
constructed Extension toggle as its stored inverse. -/
noncomputable def finiteAxisFoldExtensionBackwardContextEquivalence :
    FiniteAxisFoldBackwardContextCategory ≌
      FiniteAxisFoldBackwardContextCategory :=
  CategoryTheory.Equivalence.mk
    (CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory)
    finiteAxisFoldExtensionToggleContextFunctor
    (NatIso.ofComponents
      (fun context => Iso.mk
        (homOfLE (finiteAxisFoldContext_le_extensionToggle context.ctx))
        (homOfLE (finiteAxisFoldExtensionToggle_le_context context.ctx))
        (by apply Subsingleton.elim)
        (by apply Subsingleton.elim))
      (by intros; apply Subsingleton.elim))
    (NatIso.ofComponents
      (fun context => Iso.mk
        (homOfLE (finiteAxisFoldExtensionToggle_le_context context.ctx))
        (homOfLE (finiteAxisFoldContext_le_extensionToggle context.ctx))
        (by apply Subsingleton.elim)
        (by apply Subsingleton.elim))
      (by intros; apply Subsingleton.elim))

/-- The asymmetric equivalence is still a strict involution: its forward
part remains identity and its stored inverse applies the toggle twice. -/
theorem finiteAxisFoldExtensionBackwardContextEquivalence_trans_self :
    finiteAxisFoldExtensionBackwardContextEquivalence.trans
        finiteAxisFoldExtensionBackwardContextEquivalence =
      CategoryTheory.Equivalence.refl := by
  have hfunctor :
      (finiteAxisFoldExtensionBackwardContextEquivalence.trans
        finiteAxisFoldExtensionBackwardContextEquivalence).functor =
      CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory := by
    change CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory ⋙
      CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory = _
    rfl
  have hinverse :
      (finiteAxisFoldExtensionBackwardContextEquivalence.trans
        finiteAxisFoldExtensionBackwardContextEquivalence).inverse =
      CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory := by
    refine CategoryTheory.Functor.ext (fun context => ?_) ?_
    · exact finiteAxisFoldExtensionToggleContextFunctor_obj_obj context
    · intros
      exact Subsingleton.elim _ _
  apply CategoryTheory.Equivalence.ext hfunctor hinverse
  · apply finiteAxisFoldBackwardSubsingleton_heq_of_type_eq
    apply congrArg
      (fun functor =>
        (CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory) ≅
          functor)
    rw [hfunctor, hinverse]
    rfl
  · apply finiteAxisFoldBackwardSubsingleton_heq_of_type_eq
    apply congrArg
      (fun functor =>
        functor ≅
          (CategoryTheory.Functor.id FiniteAxisFoldBackwardContextCategory))
    rw [hfunctor, hinverse]
    rfl

/-- Exact equation transport which stores the toggle only in its backward
context functor. -/
noncomputable def finiteAxisFoldExtensionBackwardEquationTransport :
    EquationSystemExactTransport
      FiniteAxisFoldBackwardCore.algebra.equationSystem
      FiniteAxisFoldBackwardCore.algebra.equationSystem
      (Equiv.refl FiniteModel.carrier.Atom) id where
  contextEquivalence := finiteAxisFoldExtensionBackwardContextEquivalence
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl Int
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by intros; rfl

noncomputable def finiteAxisFoldExtensionBackwardUpper :
    SignedExactCoreReadingHom FiniteAxisFoldBackwardCore
      FiniteAxisFoldBackwardCore :=
  { SignedExactCoreReadingHom.refl FiniteAxisFoldBackwardCore with
    equationTransport := finiteAxisFoldExtensionBackwardEquationTransport }

noncomputable def finiteAxisFoldExtensionBackwardTotal :
    PackageTotalHom FiniteAxisFoldBackwardCore FiniteAxisFoldBackwardCore where
  base := ExtInstHom.id (packagePoint FiniteAxisFoldBackwardCore)
  upper := finiteAxisFoldExtensionBackwardUpper
  atomEquiv_eq := rfl

theorem finiteAxisFoldExtensionBackwardUpper_comp_self :
    finiteAxisFoldExtensionBackwardUpper.comp
        finiteAxisFoldExtensionBackwardUpper =
      SignedExactCoreReadingHom.refl FiniteAxisFoldBackwardCore := by
  apply SignedExactCoreReadingHom.ext
  · rfl
  · rfl
  · apply equationSystemExactTransport_hext
    · rfl
    · rfl
    · exact finiteAxisFoldExtensionBackwardContextEquivalence_trans_self
    · rfl
    · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem finiteAxisFoldExtensionBackwardTotal_comp_self :
    finiteAxisFoldExtensionBackwardTotal.comp
        finiteAxisFoldExtensionBackwardTotal =
      PackageTotalHom.id FiniteAxisFoldBackwardCore := by
  apply PackageTotalHom.ext
  · rfl
  · exact finiteAxisFoldExtensionBackwardUpper_comp_self

theorem finiteAxisFoldExtensionBackward_rawReindex :
    rawReindex (G := FiniteAxisFoldBackwardSource)
        (H := FiniteAxisFoldBackwardSource)
        finiteAxisFoldExtensionBackwardTotal
        FiniteAxisFoldBackwardSource.raw =
      FiniteAxisFoldBackwardSource.raw := by
  apply LawAlgebra.RawAmbientRestrictionSystem.ext <;> rfl

/-- Identity local geometry comparisons are natural because the forward
context functor is definitionally the identity. -/
noncomputable def finiteAxisFoldExtensionBackwardGeomReadHom :
    GeomReadHom FiniteAxisFoldBackwardSource FiniteAxisFoldBackwardSource
      finiteAxisFoldExtensionBackwardTotal where
  coverage := by
    constructor <;> intros <;> assumption
  overlap := by
    constructor
    intro base left right
    refine Iso.mk (homOfLE ?_) (homOfLE ?_)
      (by apply Subsingleton.elim) (by apply Subsingleton.elim)
    · change FiniteAxisFoldBackwardCore.contextPreorder.le
        (Site.productContext
          (finiteAxisFoldExtensionToggleContext left)
          (finiteAxisFoldExtensionToggleContext right))
        (Site.productContext left right)
      refine ⟨{
        supportMap := id
        axisMap := id
        observableRestrict := id }, ?_⟩
      refine ⟨fun h => h, fun h => h, ?_, fun h => ?_⟩
      · intro observable h
        cases observable <;> exact h
      exact (Site.productContext left right).supportReads_objectFamily h
    · change FiniteAxisFoldBackwardCore.contextPreorder.le
        (Site.productContext left right)
        (Site.productContext
          (finiteAxisFoldExtensionToggleContext left)
          (finiteAxisFoldExtensionToggleContext right))
      refine ⟨{
        supportMap := id
        axisMap := id
        observableRestrict := id }, ?_⟩
      refine ⟨fun h => h, fun h => h, ?_, fun h => ?_⟩
      · intro observable h
        cases observable <;> exact h
      exact (Site.productContext
        (finiteAxisFoldExtensionToggleContext left)
        (finiteAxisFoldExtensionToggleContext right)).supportReads_objectFamily h
  coefficientHom := RingHom.id Int
  raw_eq := by
    change FiniteAxisFoldBackwardSource.raw =
      rawReindex finiteAxisFoldExtensionBackwardTotal
        (FiniteAxisFoldBackwardSource.raw.baseChange (RingHom.id Int))
    have hchange :
        FiniteAxisFoldBackwardSource.raw.baseChange (RingHom.id Int) =
          FiniteAxisFoldBackwardSource.raw := by
      simpa only using
        (LawAlgebra.RawAmbientRestrictionSystem.baseChange_id
          FiniteAxisFoldBackwardSource.raw)
    rw [hchange]
    exact finiteAxisFoldExtensionBackward_rawReindex.symm
  supportComp _ := _root_.id
  axisComp _ := _root_.id
  observableComp _ := _root_.id
  supportReads _ _ _ := _root_.id
  axisReads _ _ := _root_.id
  observableReads _ _ := _root_.id
  support_naturality := by intros; rfl
  axis_naturality := by intros; rfl
  observable_naturality := by intros; rfl

noncomputable def finiteAxisFoldExtensionBackwardGeometry :
    GeometryTotalHom FiniteAxisFoldBackwardSource
      FiniteAxisFoldBackwardSource where
  base := finiteAxisFoldExtensionBackwardTotal
  geometry := finiteAxisFoldExtensionBackwardGeomReadHom

private theorem finiteAxisFoldExtensionBackwardGeomReadHom_heq_of_base_eq
    {firstBase secondBase : PackageTotalHom FiniteAxisFoldBackwardCore
      FiniteAxisFoldBackwardCore}
    (first : GeomReadHom FiniteAxisFoldBackwardSource
      FiniteAxisFoldBackwardSource firstBase)
    (second : GeomReadHom FiniteAxisFoldBackwardSource
      FiniteAxisFoldBackwardSource secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

theorem finiteAxisFoldExtensionBackwardGeometry_comp_self :
    finiteAxisFoldExtensionBackwardGeometry.comp
        finiteAxisFoldExtensionBackwardGeometry =
      GeometryTotalHom.id FiniteAxisFoldBackwardSource := by
  have hbase := finiteAxisFoldExtensionBackwardTotal_comp_self
  apply GeometryTotalHom.ext hbase
  apply finiteAxisFoldExtensionBackwardGeomReadHom_heq_of_base_eq _ _ hbase rfl
  · rfl
  · rfl
  · rfl

/-- The source-owned backward-only toggle as a complete-geometry
automorphism. -/
noncomputable def finiteAxisFoldExtensionBackwardGeometryAut :
    Aut FiniteAxisFoldBackwardSource where
  hom := finiteAxisFoldExtensionBackwardGeometry
  inv := finiteAxisFoldExtensionBackwardGeometry
  hom_inv_id := finiteAxisFoldExtensionBackwardGeometry_comp_self
  inv_hom_id := finiteAxisFoldExtensionBackwardGeometry_comp_self

/-- Its stored backward functor moves the explicit Boolean-false context. -/
theorem finiteAxisFoldExtensionBackwardGeometryAut_backward_moves_false :
    (finiteAxisFoldExtensionBackwardContextEquivalence.inverse.obj
        (⟨finiteAxisFoldBooleanFalseContext⟩ :
          FiniteAxisFoldBackwardContextCategory)).ctx ≠
      finiteAxisFoldBooleanFalseContext :=
  finiteAxisFoldBooleanFalseContext_toggle_ne

/-- The complete source automorphism is nontrivial, witnessed by its stored
backward context action rather than by a chosen completed morphism input. -/
theorem finiteAxisFoldExtensionBackwardGeometryAut_ne_one :
    finiteAxisFoldExtensionBackwardGeometryAut ≠ 1 := by
  intro equality
  have backwardEquality := congrArg
    (fun automorphism : Aut FiniteAxisFoldBackwardSource =>
      (automorphism.hom.base.upper.equationTransport.contextEquivalence.inverse.obj
          (⟨finiteAxisFoldBooleanFalseContext⟩ :
            FiniteAxisFoldBackwardContextCategory)).ctx)
    equality
  exact finiteAxisFoldBooleanFalseContext_toggle_ne backwardEquality

/-- The fixed ExtInst morphism carrying the source geometry to the actual
southwest geometry. -/
noncomputable def finiteAxisFoldSourceToSouthwestExtInstHom :
    packagePoint finiteAxisFoldSourceGeometryPackage.core ⟶
      packagePoint finiteAxisFoldGeometryPackage.core :=
  (transportAlongHom finiteAxisFoldSourceGeometryPackage.core
    finiteModelDoctrineFromFixture).base

/-- The source automorphism as a vertical automorphism of its canonical
geometry fiber. -/
noncomputable def finiteAxisFoldExtensionBackwardGeometryFiberHom :
    geomFiberMk finiteAxisFoldSourceGeometryPackage ⟶
      geomFiberMk finiteAxisFoldSourceGeometryPackage := by
  refine ⟨finiteAxisFoldExtensionBackwardGeometry, ?_⟩
  apply CategoryTheory.IsHomLift.of_commsq
    (crossStageProjection.{0, 0} FiniteModel.carrier)
    (𝟙 (packagePoint finiteAxisFoldSourceGeometryPackage.core))
    finiteAxisFoldExtensionBackwardGeometry rfl rfl
  change finiteAxisFoldExtensionBackwardGeometry.base.base =
    ExtInstHom.id (packagePoint finiteAxisFoldSourceGeometryPackage.core)
  rfl

noncomputable def finiteAxisFoldExtensionBackwardGeometryFiberAut :
    Aut (geomFiberMk finiteAxisFoldSourceGeometryPackage) where
  hom := finiteAxisFoldExtensionBackwardGeometryFiberHom
  inv := finiteAxisFoldExtensionBackwardGeometryFiberHom
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldExtensionBackwardGeometry_comp_self
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact finiteAxisFoldExtensionBackwardGeometry_comp_self

/-- Functorial transport of the source-owned automorphism.  Its underlying
target geometry is definitionally the fixed southwest geometry package, so no
casted context preorder or completed southwest automorphism is an input. -/
noncomputable def finiteAxisFoldTransportedExtensionBackwardAut :
    Aut ((geomFiberTransportFunctor.{0, 0}
      finiteAxisFoldSourceToSouthwestExtInstHom).obj
        (geomFiberMk finiteAxisFoldSourceGeometryPackage)) :=
  (geomFiberTransportFunctor.{0, 0}
    finiteAxisFoldSourceToSouthwestExtInstHom).mapIso
      finiteAxisFoldExtensionBackwardGeometryFiberAut

theorem finiteAxisFoldTransportedExtensionBackward_underlying_geometry :
    ((geomFiberTransportFunctor.{0, 0}
      finiteAxisFoldSourceToSouthwestExtInstHom).obj
        (geomFiberMk finiteAxisFoldSourceGeometryPackage)).1 =
      finiteAxisFoldGeometryPackage :=
  rfl

local instance finiteAxisFoldBackwardToggleAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

private theorem finiteAxisFoldTransportedExtensionBackward_object_eq_southwest :
    (geomFiberTransportFunctor.{0, 0}
      finiteAxisFoldSourceToSouthwestExtInstHom).obj
        (geomFiberMk finiteAxisFoldSourceGeometryPackage) =
      finiteAxisFoldSouthwestGeometryFiber := by
  apply Subtype.ext
  rfl

/-- Retag the functorially transported source automorphism as an automorphism
of the already fixed actual southwest fiber.  Only proof-irrelevant endpoint
equality is changed; the geometry morphism is not reconstructed or supplied
again. -/
noncomputable def finiteAxisFoldSouthwestExtensionBackwardAut :
    Aut finiteAxisFoldSouthwestGeometryFiber :=
  (eqToIso finiteAxisFoldTransportedExtensionBackward_object_eq_southwest).symm ≪≫
    finiteAxisFoldTransportedExtensionBackwardAut ≪≫
      eqToIso finiteAxisFoldTransportedExtensionBackward_object_eq_southwest

/-- Carry the source-owned backward-only involution through the fixed exact
left pull and top transport to the actual direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectExtensionBackwardAut :
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
        finiteAxisFoldSouthwestExtensionBackwardAut)

/-- Package the transported involution in the independently fixed admissible
direct endpoint. -/
noncomputable def finiteAxisFoldActualDirectExtensionBackwardAdmissibleAut :
    Aut finiteAxisFoldActualDirectAdmissibleGeometry where
  hom := ObjectProperty.homMk
    finiteAxisFoldActualDirectExtensionBackwardAut.hom.1
  inv := ObjectProperty.homMk
    finiteAxisFoldActualDirectExtensionBackwardAut.inv.1
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      finiteAxisFoldActualDirectExtensionBackwardAut.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    exact congrArg Subtype.val
      finiteAxisFoldActualDirectExtensionBackwardAut.inv_hom_id

/-- The backward-only source recipe at the fixed normalized endpoint.  Its
survival and projection values are subsequent proof obligations, not fields
or assumptions of this construction. -/
noncomputable def finiteAxisFoldNormalizedExtensionBackwardAut :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  (geometryNormalizationFunctor.{0, 0} FiniteModel.carrier).mapIso
    finiteAxisFoldActualDirectExtensionBackwardAdmissibleAut

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end

end AAT.AG.RealizationReconstruction
