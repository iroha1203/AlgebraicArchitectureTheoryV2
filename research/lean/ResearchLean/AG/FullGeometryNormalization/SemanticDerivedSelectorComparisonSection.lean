import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorComparisonGroup
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedCanonicalComparisonExactness
import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationIsoComparisonSection

/-! # Selector-wise section of the generic semantic comparison restriction -/

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


section Semantic

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) = input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- Reinterpret a semantic source Karoubi automorphism as an automorphism
of the actual normalized geometry. -/
private noncomputable def semanticSelectedSourceNormalizedAutHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    Aut (semanticExactBarESourceKaroubiAt input interpretation z omega k g
      endpoint_eq square_isPullback) →*
      Aut ((geometryNormalizationFunctor.{u, v} U).obj
        (semanticDerivedDirectAdmissibleGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq selected.2)) where
  toFun a := by
    let G := semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2
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
          (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ a.hom.f ≫
            semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 = a.hom.f.1 :=
        congrArg Subtype.val a.hom.comm
      change
        (canonicalGeometryFiberNormalization
            (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
            (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1 ≫
          a.hom.f.1 ≫
        (canonicalGeometryFiberNormalization
            (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
            (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1 =
          a.hom.f.1
      rw [← semanticExactBarEAt_eq_endpoint_normalization input interpretation z omega k g endpoint_eq square_isPullback selected]
      exact h
    · apply ObjectProperty.hom_ext
      have h :
          (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ a.inv.f ≫
            semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 = a.inv.f.1 :=
        congrArg Subtype.val a.inv.comm
      change
        (canonicalGeometryFiberNormalization
            (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
            (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1 ≫
          a.inv.f.1 ≫
        (canonicalGeometryFiberNormalization
            (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
            (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1 =
          a.inv.f.1
      rw [← semanticExactBarEAt_eq_endpoint_normalization input interpretation z omega k g endpoint_eq square_isPullback selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg
        (fun q => (Functor.Fiber.fiberInclusion).map q.f) a.hom_inv_id
      change a.hom.f.1 ≫ a.inv.f.1 =
        (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 at h
      change a.hom.f.1 ≫ a.inv.f.1 =
        (canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1
      rw [← semanticExactBarEAt_eq_endpoint_normalization input interpretation z omega k g endpoint_eq square_isPullback selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg
        (fun q => (Functor.Fiber.fiberInclusion).map q.f) a.inv_hom_id
      change a.inv.f.1 ≫ a.hom.f.1 =
        (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 at h
      change a.inv.f.1 ≫ a.hom.f.1 =
        (canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1
      rw [← semanticExactBarEAt_eq_endpoint_normalization input interpretation z omega k g endpoint_eq square_isPullback selected]
      exact h
  map_one' := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    change (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 =
      (canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1
    exact congrArg Subtype.val
      (semanticExactBarEAt_eq_endpoint_normalization input interpretation z omega k g endpoint_eq square_isPullback selected)
  map_mul' a b := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    rfl


/-- Off the selector, unsandwich both actual Karoubi endpoint
automorphisms.  Since `barE = barD = 1` and `barBeta = barAlpha`, the result
is an actual raw-compatible centralizing pair. -/
private noncomputable def semanticExactOffSelectorComparisonSectionHom
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
      endpoint_eq square_isPullback →*
      SemanticExactCentralizingRawComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback where
  toFun pair := by
    let source := karoubiAutUnderlyingHomOfProjectorEqId
      (semanticExactBarESourceKaroubiAt input interpretation z omega k g endpoint_eq square_isPullback)
      (by exact (semanticExactBarProjectorsAt_eq_id input interpretation z omega k g endpoint_eq square_isPullback notSelected).1) pair.1.1
    let target := karoubiAutUnderlyingHomOfProjectorEqId
      (semanticExactBarDTargetKaroubiAt input interpretation z omega k g endpoint_eq)
      (by exact semanticExactBarDAt_eq_id input interpretation z omega k g endpoint_eq notSelected) pair.1.2
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · change source.hom ≫ semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback =
          semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ source.hom
        simp only [(semanticExactBarProjectorsAt_eq_id input interpretation z omega k g endpoint_eq square_isPullback notSelected).1,
          Category.id_comp]
        exact Category.comp_id _
      · change target.hom ≫ semanticExactBarDAt input interpretation z omega k g endpoint_eq =
          semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫ target.hom
        simp only [semanticExactBarDAt_eq_id input interpretation z omega k g endpoint_eq notSelected,
          Category.id_comp]
        exact Category.comp_id _
    · change source.hom ≫ (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom =
        (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫ target.hom
      have h := congrArg (fun q => q.f) pair.2
      change pair.1.1.hom.f ≫ semanticExactBarBetaAt input interpretation z omega k g endpoint_eq square_isPullback =
        semanticExactBarBetaAt input interpretation z omega k g endpoint_eq square_isPullback ≫ pair.1.2.hom.f at h
      have hbeta : semanticExactBarBetaAt input interpretation z omega k g endpoint_eq square_isPullback =
          (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom := by
        rw [semanticExactBarBetaAt,
          semanticExactBarDAt_eq_id input interpretation z omega k g endpoint_eq notSelected]
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
private theorem semanticExactOffSelectorComparisonSection_rightInverse
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega)
    (pair : SemanticExactKaroubiComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback) :
    semanticExactCompatibleRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (semanticExactOffSelectorComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback notSelected pair) = pair := by
  apply Subtype.ext
  apply Prod.ext
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactOffSelectorComparisonSectionHom
          input interpretation z omega k g endpoint_eq square_isPullback notSelected pair)).1.1.hom.f =
        semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫
          (semanticExactOffSelectorComparisonSectionHom
            input interpretation z omega k g endpoint_eq square_isPullback notSelected pair).1.1.1.hom ≫
          semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback by
      exact semanticExactEndpointRestrictionHom_fst_hom_f
        input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactOffSelectorComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback notSelected pair).1]
    simp only [(semanticExactBarProjectorsAt_eq_id input interpretation z omega k g endpoint_eq square_isPullback notSelected).1,
      Category.id_comp]
    change _ ≫ 𝟙 _ = pair.1.1.hom.f
    rw [Category.comp_id]
    rfl
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactOffSelectorComparisonSectionHom
          input interpretation z omega k g endpoint_eq square_isPullback notSelected pair)).1.2.hom.f =
        semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
          (semanticExactOffSelectorComparisonSectionHom
            input interpretation z omega k g endpoint_eq square_isPullback notSelected pair).1.1.2.hom ≫
          semanticExactBarDAt input interpretation z omega k g endpoint_eq by
      exact semanticExactEndpointRestrictionHom_snd_hom_f
        input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactOffSelectorComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback notSelected pair).1]
    simp only [semanticExactBarDAt_eq_id input interpretation z omega k g endpoint_eq notSelected,
      Category.id_comp]
    change _ ≫ 𝟙 _ = pair.1.2.hom.f
    rw [Category.comp_id]
    rfl


/-- The selected source lift, returned to the actual northeast geometry
fiber.  Verticality is rebuilt from the base map retained by the canonical
section and the supplied Karoubi automorphism's fiber-lift evidence. -/
private noncomputable def semanticExactSelectedSourceRawAutHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    Aut (semanticExactBarESourceKaroubiAt input interpretation z omega k g
      endpoint_eq square_isPullback) →*
      Aut (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq) where
  toFun a := by
    let G := semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2
    let normalized := semanticSelectedSourceNormalizedAutHom
      input interpretation z omega k g endpoint_eq square_isPullback selected a
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
          eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 =
        eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 ≫ 𝟙 _
      change a.hom.f.1.base.base ≫
          eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 =
        eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 ≫ 𝟙 _
      letI := a.hom.f.2
      have h := CategoryTheory.IsHomLift.fac'
        (crossStageProjection.{u, v} U)
        (𝟙 input.square.northeast) a.hom.f.1
      rw [crossStageProjection_map] at h
      rw [h]
      simp
    · apply CategoryTheory.IsHomLift.of_commsq
        (crossStageProjection.{u, v} U) (𝟙 _)
        lifted.inv.hom _ _
      change lifted.inv.hom.base.base ≫
          eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 =
        eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 ≫ 𝟙 _
      change a.inv.f.1.base.base ≫
          eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 =
        eqToHom (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).2 ≫ 𝟙 _
      letI := a.inv.f.2
      have h := CategoryTheory.IsHomLift.fac'
        (crossStageProjection.{u, v} U)
        (𝟙 input.square.northeast) a.inv.f.1
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
        (semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2)).comp
      (semanticSelectedSourceNormalizedAutHom input interpretation z omega k g endpoint_eq square_isPullback selected)
    exact congrArg (fun f => f.hom.hom) (map_one composite)
  map_mul' a b := by
    apply Iso.ext
    apply CategoryTheory.Functor.Fiber.hom_ext
    let composite :=
      (canonicalNormalizationAutomorphismSectionHom
        (semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2)).comp
      (semanticSelectedSourceNormalizedAutHom input interpretation z omega k g endpoint_eq square_isPullback selected)
    exact congrArg (fun f => f.hom.hom) (map_mul composite a b)


private noncomputable def semanticExactSelectedComparisonSectionHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
      endpoint_eq square_isPullback →*
      SemanticExactCentralizingRawComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback where
  toFun pair := by
    let source := semanticExactSelectedSourceRawAutHom
      input interpretation z omega k g endpoint_eq square_isPullback selected pair.1.1
    let target := isoConjugationAutHom
      (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback) source
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · change source.hom ≫ semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback =
          semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ source.hom
        rw [semanticExactBarEAt_eq_endpoint_normalization
          input interpretation z omega k g endpoint_eq square_isPullback selected]
        apply CategoryTheory.Functor.Fiber.hom_ext
        exact canonicalNormalizationAutomorphismSection_commutes
          (semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2)
          (semanticSelectedSourceNormalizedAutHom input interpretation z omega k g endpoint_eq square_isPullback selected pair.1.1)
      · change target.hom ≫ semanticExactBarDAt input interpretation z omega k g endpoint_eq =
          semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫ target.hom
        apply (cancel_epi (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom).1
        change
          (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫
              ((semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv ≫ source.hom ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom) ≫
              semanticExactBarDAt input interpretation z omega k g endpoint_eq =
            (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫
              semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
              ((semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv ≫ source.hom ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom)
        have hsource : source.hom ≫ semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback =
            semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ source.hom := by
          rw [semanticExactBarEAt_eq_endpoint_normalization
            input interpretation z omega k g endpoint_eq square_isPullback selected]
          apply CategoryTheory.Functor.Fiber.hom_ext
          exact canonicalNormalizationAutomorphismSection_commutes
            (semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2)
            (semanticSelectedSourceNormalizedAutHom input interpretation z omega k g endpoint_eq square_isPullback selected pair.1.1)
        have hconj :
            (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫
                semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv =
              semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback := by
          calc
            _ = (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫
                  (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom) ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv)
                (semanticExactBarAlphaAt_projector_comm input interpretation z omega k g endpoint_eq square_isPullback).symm
            _ = _ := by simp
        calc
          _ = source.hom ≫ (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫
                semanticExactBarDAt input interpretation z omega k g endpoint_eq := by simp
          _ = source.hom ≫ semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom := by
              rw [semanticExactBarAlphaAt_projector_comm input interpretation z omega k g endpoint_eq square_isPullback]
          _ = semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫ source.hom ≫
                (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom := by
              simpa only [Category.assoc] using congrArg
                (fun q => q ≫ (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom)
                hsource
          _ = _ := by
            symm
            calc
              _ = ((semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫
                    semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
                    (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).inv) ≫
                  source.hom ≫
                  (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom := by
                    simp only [Category.assoc]
              _ = _ := by rw [hconj]
    · change source.hom ≫ (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom =
        (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback).hom ≫ target.hom
      simp [target, isoConjugationAutHom]
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_one _
    · change isoConjugationAutHom (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback)
          (semanticExactSelectedSourceRawAutHom input interpretation z omega k g endpoint_eq square_isPullback selected 1) = 1
      rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul _ _ _
    · change isoConjugationAutHom (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback)
          (semanticExactSelectedSourceRawAutHom input interpretation z omega k g endpoint_eq square_isPullback selected
            (a.1.1 * b.1.1)) =
        isoConjugationAutHom (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback)
            (semanticExactSelectedSourceRawAutHom input interpretation z omega k g endpoint_eq square_isPullback selected a.1.1) *
          isoConjugationAutHom (semanticDerivedBarAlphaIsoAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq square_isPullback)
            (semanticExactSelectedSourceRawAutHom input interpretation z omega k g endpoint_eq square_isPullback selected b.1.1)
      rw [map_mul, map_mul]


private theorem semanticExactSelectedComparisonSection_rightInverse
    (selected : semanticExactBarSelectedAt input interpretation z omega)
    (pair : SemanticExactKaroubiComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback) :
    semanticExactCompatibleRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (semanticExactSelectedComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback selected pair) = pair := by
  have hsource :
      (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactSelectedComparisonSectionHom
          input interpretation z omega k g endpoint_eq square_isPullback selected pair)).1.1 = pair.1.1 := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactSelectedComparisonSectionHom
          input interpretation z omega k g endpoint_eq square_isPullback selected pair)).1.1.hom.f =
        semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback ≫
          (semanticExactSelectedComparisonSectionHom
            input interpretation z omega k g endpoint_eq square_isPullback selected pair).1.1.1.hom ≫
          semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback by
      exact semanticExactEndpointRestrictionHom_fst_hom_f
        input interpretation z omega k g endpoint_eq square_isPullback
        (semanticExactSelectedComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback selected pair).1]
    apply CategoryTheory.Functor.Fiber.hom_ext
    let G := semanticDerivedDirectAdmissibleGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2
    let normalized := semanticSelectedSourceNormalizedAutHom
      input interpretation z omega k g endpoint_eq square_isPullback selected pair.1.1
    let lifted := canonicalNormalizationAutomorphismSectionHom G normalized
    have h := congrArg (fun q => q.hom.f.hom)
      (canonicalNormalizationAutomorphismSection_rightInverse G normalized)
    change
      (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 ≫
        lifted.hom.hom ≫
      (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 =
        pair.1.1.hom.f.1
    have hE := congrArg Subtype.val
      (semanticExactBarEAt_eq_endpoint_normalization
        input interpretation z omega k g endpoint_eq square_isPullback selected)
    rw [hE]
    change
      (canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible input interpretation z k g endpoint_eq selected.2)).1 ≫
        lifted.hom.hom = pair.1.1.hom.f.1 at h
    rw [← Category.assoc, h]
    have hp := congrArg Subtype.val (Karoubi.comp_p pair.1.1.hom)
    change pair.1.1.hom.f.1 ≫ (semanticExactBarEAt input interpretation z omega k g endpoint_eq square_isPullback).1 =
      pair.1.1.hom.f.1 at hp
    rw [hE] at hp
    exact hp
  apply Subtype.ext
  apply Prod.ext
  · exact hsource
  · apply Iso.ext
    apply (cancel_epi (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g endpoint_eq square_isPullback).hom).1
    calc
      _ = (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
            (semanticExactSelectedComparisonSectionHom
              input interpretation z omega k g endpoint_eq square_isPullback selected pair)).1.1.hom ≫
            (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g endpoint_eq square_isPullback).hom := by
              exact (semanticExactCompatibleRestrictionHom input interpretation z omega k g endpoint_eq square_isPullback
                (semanticExactSelectedComparisonSectionHom
                  input interpretation z omega k g endpoint_eq square_isPullback selected pair)).2.symm
      _ = pair.1.1.hom ≫
            (semanticExactBarBetaKaroubiIsoAt input interpretation z omega k g endpoint_eq square_isPullback).hom := by rw [hsource]
      _ = _ := pair.2

/-- G-122(D)'s actual selector-wise section of the restricted comparison
homomorphism. -/
noncomputable def semanticExactComparisonSectionHom :
    SemanticExactKaroubiComparisonSubgroup input interpretation z omega k g
      endpoint_eq square_isPullback →*
      SemanticExactCentralizingRawComparisonSubgroup input interpretation z omega
        k g endpoint_eq square_isPullback := by
  classical
  by_cases selected : omega z ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (semanticExactBarSourceCoreAt input interpretation z)
  · exact semanticExactSelectedComparisonSectionHom
      input interpretation z omega k g endpoint_eq square_isPullback selected
  · exact semanticExactOffSelectorComparisonSectionHom
      input interpretation z omega k g endpoint_eq square_isPullback selected

/-- The actual selector-wise comparison section is a right inverse of the
actual compatible restriction homomorphism. -/
theorem semanticExactComparisonSection_rightInverse
    (pair : SemanticExactKaroubiComparisonSubgroup input interpretation z omega
      k g endpoint_eq square_isPullback) :
    semanticExactCompatibleRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (semanticExactComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback pair) = pair := by
  classical
  by_cases selected : omega z ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible (semanticExactBarSourceCoreAt input interpretation z)
  · simpa [semanticExactComparisonSectionHom, selected] using
      semanticExactSelectedComparisonSection_rightInverse
        input interpretation z omega k g endpoint_eq square_isPullback selected pair
  · simpa [semanticExactComparisonSectionHom, selected] using
      semanticExactOffSelectorComparisonSection_rightInverse
        input interpretation z omega k g endpoint_eq square_isPullback selected pair


end Semantic

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
