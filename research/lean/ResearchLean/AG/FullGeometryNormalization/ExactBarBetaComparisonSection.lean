import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaCanonicalComparisonSection
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaReflection

/-!
# Selector-wise section of the actual exact comparison restriction

This file constructs the section of the actual restricted comparison map.
On the selected branch it crosses explicitly from the concrete geometry-fiber
Karoubi automorphism to the canonical-normalization category, applies the
canonical section, and forgets back to the concrete fiber.  Off the selector,
both projectors are identities and the Karoubi automorphisms are unsandwiched
directly.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option maxHeartbeats 3000000

private theorem sectionObjectMap_comm_normalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    canonicalNormalizationSectionObjectMap P sigma
        (canonicalObjectNormalization P A) =
      canonicalObjectNormalization P
        (canonicalNormalizationSectionObjectMap P sigma A) := by
  calc
    _ = canonicalNormalizationSectionObjectMap P sigma
        (P.reading.objectReading.object A.configuration) := rfl
    _ = P.reading.objectReading.object (A.configuration.transport sigma) :=
      canonicalNormalizationSectionObjectMap_selected P sigma A.configuration
    _ = _ := (canonicalObjectNormalization_sectionObjectMap P sigma A).symm

private theorem section_castOperation_heq
    {U : AtomCarrier.{u}} (R : OperationReading U)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B') (operation : R.Op A B) :
    HEq (castOperation R hA hB operation) operation := by
  cases hA
  cases hB
  rfl

private theorem section_operationMap_castOperation_heq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (f : SignedExactCoreReadingHom P P)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    (operation : P.reading.operationReading.Op A B) :
    HEq (f.operationMap
      (castOperation P.reading.operationReading hA hB operation))
      (f.operationMap operation) := by
  cases hA
  cases hB
  rfl

private theorem section_operationMap_heq_of_object_eq
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (f : SignedExactCoreReadingHom P P)
    {A A' B B' : ArchitectureObject U}
    (hA : A = A') (hB : B = B')
    (op : P.reading.operationReading.Op A B)
    (op' : P.reading.operationReading.Op A' B')
    (hop : HEq op op') :
    HEq (f.operationMap op) (f.operationMap op') := by
  cases hA
  cases hB
  cases hop
  rfl

private theorem sectionUpper_comm_normalization
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P)
    (f : SignedExactCoreReadingHom P P) :
    (canonicalObjectNormalizationUpper P admissible).comp
        (canonicalNormalizationSectionUpper P admissible f) =
      (canonicalNormalizationSectionUpper P admissible f).comp
        (canonicalObjectNormalizationUpper P admissible) := by
  apply SignedExactCoreReadingHom.ext
  · apply Equiv.ext
    intro atom
    rfl
  · funext A
    exact sectionObjectMap_comm_normalization P f.atomEquiv A
  · apply equationSystemExactTransport_hext
    · apply Equiv.ext
      intro atom
      rfl
    · funext A
      exact sectionObjectMap_comm_normalization P f.atomEquiv A
    · rfl
    · rfl
    · rfl
  · apply Function.hfunext rfl
    intro A A' hA
    cases hA
    apply Function.hfunext rfl
    intro B B' hB
    cases hB
    apply Function.hfunext rfl
    intro operation operation' hoperation
    cases hoperation
    let normalizedOperation :=
      cast (admissible.operation_type_eq A B) operation
    have hAidem := canonicalObjectNormalization_idempotent P A
    have hBidem := canonicalObjectNormalization_idempotent P B
    have hleft :=
      canonicalNormalizationSectionOperationMap_heq_normalized
        P admissible f normalizedOperation
    have hsource : HEq
        (f.operationMap
          (cast (admissible.operation_type_eq
              (canonicalObjectNormalization P A)
              (canonicalObjectNormalization P B)) normalizedOperation))
        (f.operationMap normalizedOperation) := by
      exact section_operationMap_heq_of_object_eq f hAidem hBidem _ _
        (cast_heq _ _)
    have hright :=
      canonicalNormalizationSectionOperationMap_heq_normalized
        P admissible f operation
    change HEq
      (canonicalNormalizationSectionOperationMap P admissible f
        normalizedOperation)
      (cast (admissible.operation_type_eq
        (canonicalNormalizationSectionObjectMap P f.atomEquiv A)
        (canonicalNormalizationSectionObjectMap P f.atomEquiv B))
        (canonicalNormalizationSectionOperationMap P admissible f operation))
    exact (hleft.trans hsource).trans
      ((cast_heq _ _).trans hright).symm
  · rfl
  · rfl
  · rfl

private theorem sectionTotal_comm_normalization
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    (canonicalNormalizationSectionTotal G admissible f).comp
        (canonicalObjectNormalizationTotal G.core admissible) =
      (canonicalObjectNormalizationTotal G.core admissible).comp
        (canonicalNormalizationSectionTotal G admissible f) := by
  apply PackageTotalHom.ext
  · apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      rfl
  · exact (sectionUpper_comm_normalization G.core admissible f.base.upper).symm

private theorem section_geometry_heq_of_base_eq
    {U : AtomCarrier.{u}} {G : GeometryPackage.{u, v} U}
    {firstBase secondBase : PackageTotalHom G.core G.core}
    (first : GeomReadHom G G firstBase)
    (second : GeomReadHom G G secondBase)
    (hbase : firstBase = secondBase)
    (hcoefficient : first.coefficientHom = second.coefficientHom)
    (hsupport : HEq first.supportComp second.supportComp)
    (haxis : HEq first.axisComp second.axisComp)
    (hobservable : HEq first.observableComp second.observableComp) :
    HEq first second := by
  cases hbase
  exact heq_of_eq (GeomReadHom.ext hcoefficient hsupport haxis hobservable)

private theorem geometrySection_comm_normalization
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    (admissible : CanonicalObjectNormalizationAdmissible G.core)
    (f : GeometryTotalHom G G) :
    canonicalNormalizationGeometrySection G admissible f ≫
        canonicalGeometryNormalization G admissible =
      canonicalGeometryNormalization G admissible ≫
        canonicalNormalizationGeometrySection G admissible f := by
  have hbase := sectionTotal_comm_normalization G admissible f
  apply GeometryTotalHom.ext hbase
  apply section_geometry_heq_of_base_eq _ _ hbase <;> rfl

private theorem canonicalNormalizationAutomorphismSection_commutes
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U)
    (a : Aut ((geometryNormalizationFunctor.{u, v} U).obj G)) :
    (canonicalNormalizationAutomorphismSectionHom G a).hom.hom ≫
        canonicalGeometryNormalization G.obj G.property =
      canonicalGeometryNormalization G.obj G.property ≫
        (canonicalNormalizationAutomorphismSectionHom G a).hom.hom :=
  geometrySection_comm_normalization G.obj G.property a.hom.f.hom

/-- Forget an automorphism of an admissible geometry to its concrete geometry
fiber. -/
private noncomputable def forgetAdmissibleGeometryAutHom
    {U : AtomCarrier.{u}}
    (G : CanonicalNormalizationAdmissibleGeometry.{u, v} U) :
    Aut G →* Aut G.obj where
  toFun a :=
    { hom := a.hom.hom
      inv := a.inv.hom
      hom_inv_id := congrArg (fun f => f.hom) a.hom_inv_id
      inv_hom_id := congrArg (fun f => f.hom) a.inv_hom_id }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- On the selected branch, reinterpret an automorphism of the actual source
Karoubi image as an automorphism of the labelled canonical-normalization
object.  Both arrow directions are rebuilt explicitly through the admissible
full subcategory. -/
private noncomputable def selectedSourceNormalizedAutHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    Aut (authoredExactBarESourceKaroubiAt A z omega k g) →*
      Aut ((geometryNormalizationFunctor.{u, v} U).obj
        (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)) where
  toFun a := by
    let G := authoredExactDirectAdmissibleGeometryAt A z k g selected.2
    refine
      { hom :=
          { f := ObjectProperty.homMk a.hom.f.1
            comm := ?_ }
        inv :=
          { f := ObjectProperty.homMk a.inv.f.1
            comm := ?_ }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply ObjectProperty.hom_ext
      have h :
          (authoredExactBarEAt A z omega k g ≫ a.hom.f ≫
            authoredExactBarEAt A z omega k g).1 = a.hom.f.1 :=
        congrArg Subtype.val a.hom.comm
      change
        (canonicalGeometryFiberNormalization
            (authoredExactDirectGeometryAt A z k g)
            (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1 ≫
          a.hom.f.1 ≫
        (canonicalGeometryFiberNormalization
            (authoredExactDirectGeometryAt A z k g)
            (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1 =
          a.hom.f.1
      rw [← authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected]
      exact h
    · apply ObjectProperty.hom_ext
      have h :
          (authoredExactBarEAt A z omega k g ≫ a.inv.f ≫
            authoredExactBarEAt A z omega k g).1 = a.inv.f.1 :=
        congrArg Subtype.val a.inv.comm
      change
        (canonicalGeometryFiberNormalization
            (authoredExactDirectGeometryAt A z k g)
            (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1 ≫
          a.inv.f.1 ≫
        (canonicalGeometryFiberNormalization
            (authoredExactDirectGeometryAt A z k g)
            (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1 =
          a.inv.f.1
      rw [← authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg
        (fun q => (Functor.Fiber.fiberInclusion).map q.f) a.hom_inv_id
      change a.hom.f.1 ≫ a.inv.f.1 =
        (authoredExactBarEAt A z omega k g).1 at h
      change a.hom.f.1 ≫ a.inv.f.1 =
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1
      rw [← authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg
        (fun q => (Functor.Fiber.fiberInclusion).map q.f) a.inv_hom_id
      change a.inv.f.1 ≫ a.hom.f.1 =
        (authoredExactBarEAt A z omega k g).1 at h
      change a.inv.f.1 ≫ a.hom.f.1 =
        (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1
      rw [← authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected]
      exact h
  map_one' := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    change (authoredExactBarEAt A z omega k g).1 =
      (canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1
    exact congrArg Subtype.val
      (authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected)
  map_mul' a b := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    rfl

/-- When a Karoubi projector is the identity, forget a Karoubi
automorphism to an automorphism of the underlying object. -/
private noncomputable def karoubiAutUnderlyingHomOfProjectorEqId
    {C : Type u} [Category.{v} C] (P : Karoubi C) (hp : P.p = 𝟙 P.X) :
    Aut P →* Aut P.X where
  toFun a :=
    { hom := a.hom.f
      inv := a.inv.f
      hom_inv_id := by
        have h := congrArg (fun q => q.f) a.hom_inv_id
        simpa only [Karoubi.comp_f, Karoubi.id_f, hp] using h
      inv_hom_id := by
        have h := congrArg (fun q => q.f) a.inv_hom_id
        simpa only [Karoubi.comp_f, Karoubi.id_f, hp] using h }
  map_one' := by
    apply Iso.ext
    exact hp
  map_mul' _ _ := by
    apply Iso.ext
    rfl

/-- Off the selector, unsandwich both actual Karoubi endpoint
automorphisms.  Since `barE = barD = 1` and `barBeta = barAlpha`, the result
is an actual raw-compatible centralizing pair. -/
private noncomputable def authoredExactOffSelectorComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))) :
    AuthoredExactKaroubiComparisonSubgroup A z omega k g →*
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g where
  toFun pair := by
    let source := karoubiAutUnderlyingHomOfProjectorEqId
      (authoredExactBarESourceKaroubiAt A z omega k g)
      (by exact authoredExactBarEAt_eq_id A z omega k g notSelected) pair.1.1
    let target := karoubiAutUnderlyingHomOfProjectorEqId
      (authoredExactBarDTargetKaroubiAt A z omega k g)
      (by exact authoredExactBarDAt_eq_id A z omega k g notSelected) pair.1.2
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · change source.hom ≫ authoredExactBarEAt A z omega k g =
          authoredExactBarEAt A z omega k g ≫ source.hom
        simp only [authoredExactBarEAt_eq_id A z omega k g notSelected,
          Category.id_comp]
        exact Category.comp_id _
      · change target.hom ≫ authoredExactBarDAt A z omega k g =
          authoredExactBarDAt A z omega k g ≫ target.hom
        simp only [authoredExactBarDAt_eq_id A z omega k g notSelected,
          Category.id_comp]
        exact Category.comp_id _
    · change source.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom =
        (authoredExactBarAlphaIsoAt A z k g).hom ≫ target.hom
      have h := congrArg (fun q => q.f) pair.2
      change pair.1.1.hom.f ≫ authoredExactBarBetaAt A z omega k g =
        authoredExactBarBetaAt A z omega k g ≫ pair.1.2.hom.f at h
      have hbeta : authoredExactBarBetaAt A z omega k g =
          (authoredExactBarAlphaIsoAt A z k g).hom := by
        rw [authoredExactBarBetaAt_factor,
          authoredExactBarDAt_eq_id A z omega k g notSelected]
        simp
      simpa only [source, target,
        karoubiAutUnderlyingHomOfProjectorEqId, hbeta] using h
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> exact map_mul _ _ _

/-- Off the selector, restricting the explicitly unsandwiched pair recovers
the supplied actual Karoubi comparison pair. -/
private theorem authoredExactOffSelectorComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)))
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactOffSelectorComparisonSectionHom
          A z omega k g notSelected pair) = pair := by
  apply Subtype.ext
  apply Prod.ext
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactOffSelectorComparisonSectionHom
          A z omega k g notSelected pair)).1.1.hom.f =
        authoredExactBarEAt A z omega k g ≫
          (authoredExactOffSelectorComparisonSectionHom
            A z omega k g notSelected pair).1.1.1.hom ≫
          authoredExactBarEAt A z omega k g by
      exact authoredExactEndpointRestrictionHom_fst_hom_f _ _ _ _ _ _]
    simp only [authoredExactBarEAt_eq_id A z omega k g notSelected,
      Category.id_comp]
    change _ ≫ 𝟙 _ = pair.1.1.hom.f
    rw [Category.comp_id]
    rfl
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactOffSelectorComparisonSectionHom
          A z omega k g notSelected pair)).1.2.hom.f =
        authoredExactBarDAt A z omega k g ≫
          (authoredExactOffSelectorComparisonSectionHom
            A z omega k g notSelected pair).1.1.2.hom ≫
          authoredExactBarDAt A z omega k g by
      exact authoredExactEndpointRestrictionHom_snd_hom_f _ _ _ _ _ _]
    simp only [authoredExactBarDAt_eq_id A z omega k g notSelected,
      Category.id_comp]
    change _ ≫ 𝟙 _ = pair.1.2.hom.f
    rw [Category.comp_id]
    rfl

/-- The selected source lift, returned to the actual northeast geometry
fiber.  Verticality is rebuilt from the base map retained by the canonical
section and the supplied Karoubi automorphism's fiber-lift evidence. -/
private noncomputable def authoredExactSelectedSourceRawAutHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    Aut (authoredExactBarESourceKaroubiAt A z omega k g) →*
      Aut (authoredExactDirectGeometryAt A z k g) where
  toFun a := by
    let G := authoredExactDirectAdmissibleGeometryAt A z k g selected.2
    let normalized := selectedSourceNormalizedAutHom
      A z omega k g selected a
    let lifted := canonicalNormalizationAutomorphismSectionHom G normalized
    refine
      { hom := ⟨lifted.hom.hom, ?_⟩
        inv := ⟨lifted.inv.hom, ?_⟩
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply CategoryTheory.IsHomLift.of_commsq
        (crossStageProjection.{u, v} U) (𝟙 _)
        lifted.hom.hom _ _
      change lifted.hom.hom.base.base ≫
          eqToHom (authoredExactDirectGeometryAt A z k g).2 =
        eqToHom (authoredExactDirectGeometryAt A z k g).2 ≫ 𝟙 _
      change a.hom.f.1.base.base ≫
          eqToHom (authoredExactDirectGeometryAt A z k g).2 =
        eqToHom (authoredExactDirectGeometryAt A z k g).2 ≫ 𝟙 _
      letI := a.hom.f.2
      have h := CategoryTheory.IsHomLift.fac'
        (crossStageProjection.{u, v} U)
        (𝟙 A.context.square.semantic.square.northeast) a.hom.f.1
      rw [crossStageProjection_map] at h
      rw [h]
      simp
    · apply CategoryTheory.IsHomLift.of_commsq
        (crossStageProjection.{u, v} U) (𝟙 _)
        lifted.inv.hom _ _
      change lifted.inv.hom.base.base ≫
          eqToHom (authoredExactDirectGeometryAt A z k g).2 =
        eqToHom (authoredExactDirectGeometryAt A z k g).2 ≫ 𝟙 _
      change a.inv.f.1.base.base ≫
          eqToHom (authoredExactDirectGeometryAt A z k g).2 =
        eqToHom (authoredExactDirectGeometryAt A z k g).2 ≫ 𝟙 _
      letI := a.inv.f.2
      have h := CategoryTheory.IsHomLift.fac'
        (crossStageProjection.{u, v} U)
        (𝟙 A.context.square.semantic.square.northeast) a.inv.f.1
      rw [crossStageProjection_map] at h
      rw [h]
      simp
    · apply CategoryTheory.Functor.Fiber.hom_ext
      exact congrArg (fun f => f.hom) lifted.hom_inv_id
    · apply CategoryTheory.Functor.Fiber.hom_ext
      exact congrArg (fun f => f.hom) lifted.inv_hom_id
  map_one' := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    let composite :=
      (canonicalNormalizationAutomorphismSectionHom
        (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)).comp
      (selectedSourceNormalizedAutHom A z omega k g selected)
    exact congrArg (fun f => f.hom.hom) (map_one composite)
  map_mul' a b := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    let composite :=
      (canonicalNormalizationAutomorphismSectionHom
        (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)).comp
      (selectedSourceNormalizedAutHom A z omega k g selected)
    exact congrArg (fun f => f.hom.hom) (map_mul composite a b)

private noncomputable def isoConjugationAutHom
    {C : Type u} [Category.{v} C] {X Y : C} (c : X ≅ Y) :
    Aut X →* Aut Y where
  toFun a :=
    { hom := c.inv ≫ a.hom ≫ c.hom
      inv := c.inv ≫ a.inv ≫ c.hom
      hom_inv_id := by simp
      inv_hom_id := by simp }
  map_one' := by
    apply Iso.ext
    change c.inv ≫ 𝟙 X ≫ c.hom = 𝟙 Y
    simp
  map_mul' a b := by
    apply Iso.ext
    change c.inv ≫ (b.hom ≫ a.hom) ≫ c.hom =
      (c.inv ≫ b.hom ≫ c.hom) ≫ (c.inv ≫ a.hom ≫ c.hom)
    simp [Category.assoc]

private noncomputable def authoredExactSelectedComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    AuthoredExactKaroubiComparisonSubgroup A z omega k g →*
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g where
  toFun pair := by
    let source := authoredExactSelectedSourceRawAutHom
      A z omega k g selected pair.1.1
    let target := isoConjugationAutHom
      (authoredExactBarAlphaIsoAt A z k g) source
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · change source.hom ≫ authoredExactBarEAt A z omega k g =
          authoredExactBarEAt A z omega k g ≫ source.hom
        rw [authoredExactBarEAt_eq_endpoint_normalization
          A z omega k g selected]
        apply CategoryTheory.Functor.Fiber.hom_ext
        exact canonicalNormalizationAutomorphismSection_commutes
          (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
          (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)
      · change target.hom ≫ authoredExactBarDAt A z omega k g =
          authoredExactBarDAt A z omega k g ≫ target.hom
        apply (cancel_epi (authoredExactBarAlphaIsoAt A z k g).hom).1
        change
          (authoredExactBarAlphaIsoAt A z k g).hom ≫
              ((authoredExactBarAlphaIsoAt A z k g).inv ≫ source.hom ≫
                (authoredExactBarAlphaIsoAt A z k g).hom) ≫
              authoredExactBarDAt A z omega k g =
            (authoredExactBarAlphaIsoAt A z k g).hom ≫
              authoredExactBarDAt A z omega k g ≫
              ((authoredExactBarAlphaIsoAt A z k g).inv ≫ source.hom ≫
                (authoredExactBarAlphaIsoAt A z k g).hom)
        have hsource : source.hom ≫ authoredExactBarEAt A z omega k g =
            authoredExactBarEAt A z omega k g ≫ source.hom := by
          rw [authoredExactBarEAt_eq_endpoint_normalization
            A z omega k g selected]
          apply CategoryTheory.Functor.Fiber.hom_ext
          exact canonicalNormalizationAutomorphismSection_commutes
            (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
            (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)
        have hconj :
            (authoredExactBarAlphaIsoAt A z k g).hom ≫
                authoredExactBarDAt A z omega k g ≫
                (authoredExactBarAlphaIsoAt A z k g).inv =
              authoredExactBarEAt A z omega k g := by
          calc
            _ = (authoredExactBarEAt A z omega k g ≫
                  (authoredExactBarAlphaIsoAt A z k g).hom) ≫
                (authoredExactBarAlphaIsoAt A z k g).inv := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (authoredExactBarAlphaIsoAt A z k g).inv)
                (authoredExactBarAlphaAt_projector_comm A z omega k g).symm
            _ = _ := by simp
        calc
          _ = source.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom ≫
                authoredExactBarDAt A z omega k g := by simp
          _ = source.hom ≫ authoredExactBarEAt A z omega k g ≫
                (authoredExactBarAlphaIsoAt A z k g).hom := by
              rw [authoredExactBarAlphaAt_projector_comm A z omega k g]
          _ = authoredExactBarEAt A z omega k g ≫ source.hom ≫
                (authoredExactBarAlphaIsoAt A z k g).hom := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (authoredExactBarAlphaIsoAt A z k g).hom)
                hsource
          _ = _ := by
            symm
            calc
              _ = ((authoredExactBarAlphaIsoAt A z k g).hom ≫
                    authoredExactBarDAt A z omega k g ≫
                    (authoredExactBarAlphaIsoAt A z k g).inv) ≫
                  source.hom ≫
                  (authoredExactBarAlphaIsoAt A z k g).hom := by
                    simp only [Category.assoc]
              _ = _ := by rw [hconj]
    · change source.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom =
        (authoredExactBarAlphaIsoAt A z k g).hom ≫ target.hom
      simp [target, isoConjugationAutHom]
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_one _
    · change isoConjugationAutHom (authoredExactBarAlphaIsoAt A z k g)
          (authoredExactSelectedSourceRawAutHom A z omega k g selected 1) = 1
      rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul _ _ _
    · change isoConjugationAutHom (authoredExactBarAlphaIsoAt A z k g)
          (authoredExactSelectedSourceRawAutHom A z omega k g selected
            (a.1.1 * b.1.1)) =
        isoConjugationAutHom (authoredExactBarAlphaIsoAt A z k g)
            (authoredExactSelectedSourceRawAutHom A z omega k g selected a.1.1) *
          isoConjugationAutHom (authoredExactBarAlphaIsoAt A z k g)
            (authoredExactSelectedSourceRawAutHom A z omega k g selected b.1.1)
      rw [map_mul, map_mul]

private theorem authoredExactSelectedComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as))
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactSelectedComparisonSectionHom
          A z omega k g selected pair) = pair := by
  have hsource :
      (authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactSelectedComparisonSectionHom
          A z omega k g selected pair)).1.1 = pair.1.1 := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactSelectedComparisonSectionHom
          A z omega k g selected pair)).1.1.hom.f =
        authoredExactBarEAt A z omega k g ≫
          (authoredExactSelectedComparisonSectionHom
            A z omega k g selected pair).1.1.1.hom ≫
          authoredExactBarEAt A z omega k g by
      exact authoredExactEndpointRestrictionHom_fst_hom_f _ _ _ _ _ _]
    apply CategoryTheory.Functor.Fiber.hom_ext
    let G := authoredExactDirectAdmissibleGeometryAt A z k g selected.2
    let normalized := selectedSourceNormalizedAutHom
      A z omega k g selected pair.1.1
    let lifted := canonicalNormalizationAutomorphismSectionHom G normalized
    have h := congrArg (fun q => q.hom.f.hom)
      (canonicalNormalizationAutomorphismSection_rightInverse G normalized)
    change
      (authoredExactBarEAt A z omega k g).1 ≫
        lifted.hom.hom ≫
      (authoredExactBarEAt A z omega k g).1 =
        pair.1.1.hom.f.1
    have hE := congrArg Subtype.val
      (authoredExactBarEAt_eq_endpoint_normalization
        A z omega k g selected)
    rw [hE]
    change
      (canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2)).1 ≫
        lifted.hom.hom = pair.1.1.hom.f.1 at h
    rw [← Category.assoc, h]
    have hp := congrArg Subtype.val (Karoubi.comp_p pair.1.1.hom)
    change pair.1.1.hom.f.1 ≫ (authoredExactBarEAt A z omega k g).1 =
      pair.1.1.hom.f.1 at hp
    rw [hE] at hp
    exact hp
  apply Subtype.ext
  apply Prod.ext
  · exact hsource
  · apply Iso.ext
    apply (cancel_epi (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom).1
    calc
      _ = (authoredExactCompatibleRestrictionHom A z omega k g
            (authoredExactSelectedComparisonSectionHom
              A z omega k g selected pair)).1.1.hom ≫
            (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom := by
              exact (authoredExactCompatibleRestrictionHom A z omega k g
                (authoredExactSelectedComparisonSectionHom
                  A z omega k g selected pair)).2.symm
      _ = pair.1.1.hom ≫
            (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom := by rw [hsource]
      _ = _ := pair.2

/-- G-122(D)'s actual selector-wise section of the restricted comparison
homomorphism. -/
noncomputable def authoredExactComparisonSectionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactKaroubiComparisonSubgroup A z omega k g →*
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g := by
  classical
  by_cases selected : omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (A.context.supportPackage z.as)
  · exact authoredExactSelectedComparisonSectionHom
      A z omega k g selected
  · exact authoredExactOffSelectorComparisonSectionHom
      A z omega k g selected

/-- The actual selector-wise comparison section is a right inverse of the
actual compatible restriction homomorphism. -/
theorem authoredExactComparisonSection_rightInverse
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactComparisonSectionHom A z omega k g pair) = pair := by
  classical
  by_cases selected : omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (A.context.supportPackage z.as)
  · simpa [authoredExactComparisonSectionHom, selected] using
      authoredExactSelectedComparisonSection_rightInverse
        A z omega k g selected pair
  · simpa [authoredExactComparisonSectionHom, selected] using
      authoredExactOffSelectorComparisonSection_rightInverse
        A z omega k g selected pair

/-- The section retains the source package-base morphism. -/
theorem authoredExactComparisonSection_source_packageBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactComparisonSectionHom A z omega k g pair).1.1.1.hom.1.base.base =
      pair.1.1.hom.f.1.base.base := by
  classical
  by_cases selected : omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (A.context.supportPackage z.as)
  · have hsection : authoredExactComparisonSectionHom A z omega k g =
        authoredExactSelectedComparisonSectionHom A z omega k g selected := by
      unfold authoredExactComparisonSectionHom
      split
      · congr
      · contradiction
    rw [hsection]
    change
      (canonicalNormalizationAutomorphismSectionHom
        (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
        (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)).hom.hom.base.base = _
    exact canonicalNormalizationAutomorphismSection_hom_base_base
      (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
      (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)
  · have hsection : authoredExactComparisonSectionHom A z omega k g =
        authoredExactOffSelectorComparisonSectionHom A z omega k g selected := by
      unfold authoredExactComparisonSectionHom
      split
      · contradiction
      · congr
    rw [hsection]
    rfl

/-- The section retains the source coefficient homomorphism. -/
theorem authoredExactComparisonSection_source_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactComparisonSectionHom A z omega k g pair).1.1.1.hom.1.geometry.coefficientHom =
      pair.1.1.hom.f.1.geometry.coefficientHom := by
  classical
  by_cases selected : omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (A.context.supportPackage z.as)
  · have hsection : authoredExactComparisonSectionHom A z omega k g =
        authoredExactSelectedComparisonSectionHom A z omega k g selected := by
      unfold authoredExactComparisonSectionHom
      split
      · congr
      · contradiction
    rw [hsection]
    change
      (canonicalNormalizationAutomorphismSectionHom
        (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
        (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)).hom.hom.geometry.coefficientHom = _
    exact canonicalNormalizationAutomorphismSection_hom_coefficientHom
      (authoredExactDirectAdmissibleGeometryAt A z k g selected.2)
      (selectedSourceNormalizedAutHom A z omega k g selected pair.1.1)
  · have hsection : authoredExactComparisonSectionHom A z omega k g =
        authoredExactOffSelectorComparisonSectionHom A z omega k g selected := by
      unfold authoredExactComparisonSectionHom
      split
      · contradiction
      · congr
    rw [hsection]
    rfl

private theorem geometryFiberEndomorphism_packageBase_identity
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : GeomFiber.{u, v} X) (f : P ⟶ P) :
    f.1.base.base = 𝟙 (packagePoint P.1.core) := by
  letI := f.2
  have h := CategoryTheory.IsHomLift.fac'
    (crossStageProjection.{u, v} U) (𝟙 X) f.1
  rw [crossStageProjection_map] at h
  simpa using h

/-- The section retains the target package-base morphism. -/
theorem authoredExactComparisonSection_target_packageBase
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactComparisonSectionHom A z omega k g pair).1.1.2.hom.1.base.base =
      pair.1.2.hom.f.1.base.base := by
  rw [geometryFiberEndomorphism_packageBase_identity
    (authoredExactViaBaseGeometryAt A z k g)
    (authoredExactComparisonSectionHom A z omega k g pair).1.1.2.hom]
  rw [geometryFiberEndomorphism_packageBase_identity
    (authoredExactViaBaseGeometryAt A z k g) pair.1.2.hom.f]

/-- The section retains the target coefficient homomorphism. -/
theorem authoredExactComparisonSection_target_coefficientHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactKaroubiComparisonSubgroup A z omega k g) :
    (authoredExactComparisonSectionHom A z omega k g pair).1.1.2.hom.1.geometry.coefficientHom =
      pair.1.2.hom.f.1.geometry.coefficientHom := by
  have hr := congrArg (fun q => q.1.2.hom.f)
    (authoredExactComparisonSection_rightInverse A z omega k g pair)
  change
    (authoredExactCompatibleRestrictionHom A z omega k g
      (authoredExactComparisonSectionHom A z omega k g pair)).1.2.hom.f =
      pair.1.2.hom.f at hr
  rw [show
    (authoredExactCompatibleRestrictionHom A z omega k g
      (authoredExactComparisonSectionHom A z omega k g pair)).1.2.hom.f =
      authoredExactBarDAt A z omega k g ≫
        (authoredExactComparisonSectionHom A z omega k g pair).1.1.2.hom ≫
        authoredExactBarDAt A z omega k g by
    exact authoredExactEndpointRestrictionHom_snd_hom_f _ _ _ _ _ _] at hr
  have hrval := congrArg Subtype.val hr
  have hc := congrArg (fun f => f.geometry.coefficientHom) hrval
  change
    (authoredExactBarDAt A z omega k g).1.geometry.coefficientHom.comp
      ((authoredExactComparisonSectionHom A z omega k g pair).1.1.2.hom.1.geometry.coefficientHom.comp
        (authoredExactBarDAt A z omega k g).1.geometry.coefficientHom) =
      pair.1.2.hom.f.1.geometry.coefficientHom at hc
  simpa only [authoredExactBarDAt_coefficient_id, RingHom.comp_id,
    RingHom.id_comp] using hc

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
