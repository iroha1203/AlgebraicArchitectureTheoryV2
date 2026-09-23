import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorGlobalComparison
import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalizationIsoComparisonSection
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedSelectorBottomReflection

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

/-- Forget the admissibility wrapper on a complete geometry automorphism. -/
private noncomputable def globalForgetAdmissibleAutHom
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

/-- Recover an ordinary endpoint automorphism when its projector is identity. -/
private noncomputable def globalKaroubiAutOfIdentity
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

private noncomputable def globalIsoConjugationAutHom
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

private noncomputable def globalKaroubiIsoOfUnderlyingIso
    {C : Type u} [Category.{v} C] (P Q : Karoubi C)
    (e : P.X ≅ Q.X) (h : P.p ≫ e.hom = e.hom ≫ Q.p) : P ≅ Q := by
  have hInv : Q.p ≫ e.inv = e.inv ≫ P.p := by
    apply (cancel_mono e.hom).1
    calc
      (Q.p ≫ e.inv) ≫ e.hom = Q.p := by simp
      _ = e.inv ≫ (e.hom ≫ Q.p) := by simp
      _ = e.inv ≫ (P.p ≫ e.hom) := by rw [h]
      _ = (e.inv ≫ P.p) ≫ e.hom := by simp
  refine
    { hom :=
        { f := P.p ≫ e.hom
          comm := by
            simp only [← Category.assoc]
            rw [P.idem, h]
            simp only [Category.assoc, Q.idem] }
      inv :=
        { f := Q.p ≫ e.inv
          comm := by
            simp only [← Category.assoc]
            rw [Q.idem, hInv]
            simp only [Category.assoc, P.idem] }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [h]
    simp only [Category.assoc]
    rw [← Category.assoc Q.p Q.p e.inv, Q.idem, hInv]
    simp only [← Category.assoc, e.hom_inv_id, Category.id_comp]
  · apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f, Karoubi.id_f]
    rw [hInv]
    simp only [Category.assoc]
    rw [← Category.assoc P.p P.p e.hom, P.idem, h]
    simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]


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

/-- The full-category beta image remains an isomorphism because alpha is an
isomorphism and intertwines both selected projectors. -/
noncomputable def semanticExactGlobalBetaIso :
    SemanticExactGlobalSourceImage input interpretation z omega k g
      endpoint_eq square_isPullback ≅
    SemanticExactGlobalTargetImage input interpretation z omega k g
      endpoint_eq :=
  globalKaroubiIsoOfUnderlyingIso _ _
    (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback)
    (semanticExactGlobalAlpha_projector_comm input interpretation z omega k g
      endpoint_eq square_isPullback)

theorem semanticExactGlobalBetaIso_hom_eq :
    (semanticExactGlobalBetaIso input interpretation z omega k g endpoint_eq
      square_isPullback).hom =
    semanticExactGlobalBetaImage input interpretation z omega k g endpoint_eq
      square_isPullback := by
  apply Karoubi.Hom.ext
  change semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback ≫
      (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom =
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback ≫
      (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
        square_isPullback).hom ≫
      semanticExactGlobalD input interpretation z omega k g endpoint_eq
  have h := semanticExactGlobalAlpha_projector_comm input interpretation z
    omega k g endpoint_eq square_isPullback
  have he := semanticExactGlobalE_idem input interpretation z omega k g
    endpoint_eq square_isPullback
  calc
    _ = (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback) ≫
        (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
          square_isPullback).hom := by rw [he]
    _ = _ := by rw [Category.assoc, h, ← Category.assoc]

/-- An automorphism of the selected full Karoubi image is an automorphism of
the normalized complete geometry. -/
private noncomputable def globalSelectedNormalizedAutHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    Aut (SemanticExactGlobalSourceImage input interpretation z omega k g
      endpoint_eq square_isPullback) →*
      Aut ((geometryNormalizationFunctor.{u, v} U).obj
        (semanticDerivedDirectAdmissibleGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g
          endpoint_eq selected.2)) where
  toFun a := by
    let G := semanticDerivedDirectAdmissibleGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq selected.2
    refine
      { hom := { f := ObjectProperty.homMk a.hom.f, comm := ?_ }
        inv := { f := ObjectProperty.homMk a.inv.f, comm := ?_ }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply ObjectProperty.hom_ext
      have h := a.hom.comm
      change semanticExactGlobalE input interpretation z omega k g
          endpoint_eq square_isPullback ≫ a.hom.f ≫
        semanticExactGlobalE input interpretation z omega k g
          endpoint_eq square_isPullback = a.hom.f at h
      change canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) ≫ a.hom.f ≫
        canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) = a.hom.f
      rw [← semanticExactGlobalE_eq_normalization input interpretation z omega
        k g endpoint_eq square_isPullback selected]
      exact h
    · apply ObjectProperty.hom_ext
      have h := a.inv.comm
      change semanticExactGlobalE input interpretation z omega k g
          endpoint_eq square_isPullback ≫ a.inv.f ≫
        semanticExactGlobalE input interpretation z omega k g
          endpoint_eq square_isPullback = a.inv.f at h
      change canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) ≫ a.inv.f ≫
        canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2) = a.inv.f
      rw [← semanticExactGlobalE_eq_normalization input interpretation z omega
        k g endpoint_eq square_isPullback selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg (fun q => q.f) a.hom_inv_id
      change a.hom.f ≫ a.inv.f =
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback at h
      change a.hom.f ≫ a.inv.f =
        canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2)
      rw [← semanticExactGlobalE_eq_normalization input interpretation z omega
        k g endpoint_eq square_isPullback selected]
      exact h
    · apply Karoubi.Hom.ext
      apply ObjectProperty.hom_ext
      have h := congrArg (fun q => q.f) a.inv_hom_id
      change a.inv.f ≫ a.hom.f =
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback at h
      change a.inv.f ≫ a.hom.f =
        canonicalGeometryNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z) k g
            endpoint_eq).1
          (semanticExactDirectGeometryAt_admissible input interpretation z k g
            endpoint_eq selected.2)
      rw [← semanticExactGlobalE_eq_normalization input interpretation z omega
        k g endpoint_eq square_isPullback selected]
      exact h
  map_one' := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    change semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback = _
    exact semanticExactGlobalE_eq_normalization input interpretation z omega
      k g endpoint_eq square_isPullback selected
  map_mul' _ _ := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    apply ObjectProperty.hom_ext
    rfl

/-- Lift the selected source image automorphism to the complete source
geometry; the canonical section retains all complete-geometry components. -/
private noncomputable def globalSelectedSourceRawAutHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    Aut (SemanticExactGlobalSourceImage input interpretation z omega k g
      endpoint_eq square_isPullback) →*
      Aut (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1 :=
  (globalForgetAdmissibleAutHom
      (semanticDerivedDirectAdmissibleGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
        selected.2)).comp
    ((canonicalNormalizationAutomorphismSectionHom
      (semanticDerivedDirectAdmissibleGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
        selected.2)).comp
      (globalSelectedNormalizedAutHom input interpretation z omega k g
        endpoint_eq square_isPullback selected))

private noncomputable def globalSelectedComparisonSectionHom
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback →*
    SemanticExactGlobalRawComparison input interpretation z omega k g
      endpoint_eq square_isPullback where
  toFun pair := by
    let source := globalSelectedSourceRawAutHom input interpretation z omega
      k g endpoint_eq square_isPullback selected pair.1.1
    let c := semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
      square_isPullback
    let target := globalIsoConjugationAutHom c source
    have hsource : source.hom ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback =
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback ≫ source.hom := by
      rw [semanticExactGlobalE_eq_normalization input interpretation z omega
        k g endpoint_eq square_isPullback selected]
      exact canonicalNormalizationAutomorphismSection_commutes
        (semanticDerivedDirectAdmissibleGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
          selected.2)
        (globalSelectedNormalizedAutHom input interpretation z omega k g
          endpoint_eq square_isPullback selected pair.1.1)
    have hconj : c.hom ≫
        semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
        c.inv = semanticExactGlobalE input interpretation z omega k g
          endpoint_eq square_isPullback := by
      calc
        _ = (semanticExactGlobalE input interpretation z omega k g
              endpoint_eq square_isPullback ≫ c.hom) ≫ c.inv := by
            simpa only [c, Category.assoc] using congrArg
              (fun q => q ≫ c.inv)
              (semanticExactGlobalAlpha_projector_comm input interpretation z
                omega k g endpoint_eq square_isPullback).symm
        _ = _ := by simp
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · exact hsource
      · apply (cancel_epi c.hom).1
        change c.hom ≫ (c.inv ≫ source.hom ≫ c.hom) ≫
            semanticExactGlobalD input interpretation z omega k g endpoint_eq =
          c.hom ≫ semanticExactGlobalD input interpretation z omega k g
            endpoint_eq ≫ (c.inv ≫ source.hom ≫ c.hom)
        calc
          _ = source.hom ≫ c.hom ≫
              semanticExactGlobalD input interpretation z omega k g
                endpoint_eq := by simp
          _ = source.hom ≫
              semanticExactGlobalE input interpretation z omega k g
                endpoint_eq square_isPullback ≫ c.hom := by
                rw [semanticExactGlobalAlpha_projector_comm input
                  interpretation z omega k g endpoint_eq square_isPullback]
          _ = semanticExactGlobalE input interpretation z omega k g
              endpoint_eq square_isPullback ≫ source.hom ≫ c.hom := by
                simpa only [Category.assoc] using congrArg
                  (fun q => q ≫ c.hom) hsource
          _ = _ := by
            symm
            calc
              _ = (c.hom ≫ semanticExactGlobalD input interpretation z omega
                    k g endpoint_eq ≫ c.inv) ≫ source.hom ≫ c.hom := by
                      simp only [Category.assoc]
              _ = _ := by rw [hconj]
    · change source.hom ≫ c.hom = c.hom ≫ target.hom
      simp [target, globalIsoConjugationAutHom]
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_one _
    · change globalIsoConjugationAutHom
          (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
            square_isPullback)
          (globalSelectedSourceRawAutHom input interpretation z omega k g
            endpoint_eq square_isPullback selected 1) = 1
      rw [map_one, map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact map_mul _ _ _
    · change globalIsoConjugationAutHom
          (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
            square_isPullback)
          (globalSelectedSourceRawAutHom input interpretation z omega k g
            endpoint_eq square_isPullback selected (a.1.1 * b.1.1)) =
          globalIsoConjugationAutHom
            (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
              square_isPullback)
            (globalSelectedSourceRawAutHom input interpretation z omega k g
              endpoint_eq square_isPullback selected a.1.1) *
          globalIsoConjugationAutHom
            (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
              square_isPullback)
            (globalSelectedSourceRawAutHom input interpretation z omega k g
              endpoint_eq square_isPullback selected b.1.1)
      rw [map_mul, map_mul]

private noncomputable def globalOffComparisonSectionHom
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback →*
    SemanticExactGlobalRawComparison input interpretation z omega k g
      endpoint_eq square_isPullback where
  toFun pair := by
    have he := (semanticExactGlobalProjectors_eq_id input interpretation z
      omega k g endpoint_eq square_isPullback notSelected).1
    have hd := (semanticExactGlobalProjectors_eq_id input interpretation z
      omega k g endpoint_eq square_isPullback notSelected).2
    let source := globalKaroubiAutOfIdentity
      (SemanticExactGlobalSourceImage input interpretation z omega k g
        endpoint_eq square_isPullback) he pair.1.1
    let target := globalKaroubiAutOfIdentity
      (SemanticExactGlobalTargetImage input interpretation z omega k g
        endpoint_eq) hd pair.1.2
    refine ⟨⟨(source, target), ?_⟩, ?_⟩
    · constructor
      · change source.hom ≫ semanticExactGlobalE input interpretation z omega
          k g endpoint_eq square_isPullback =
          semanticExactGlobalE input interpretation z omega k g endpoint_eq
            square_isPullback ≫ source.hom
        rw [he]
        exact (Category.comp_id source.hom).trans
          (Category.id_comp source.hom).symm
      · change target.hom ≫ semanticExactGlobalD input interpretation z omega
          k g endpoint_eq =
          semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
            target.hom
        rw [hd]
        exact (Category.comp_id target.hom).trans
          (Category.id_comp target.hom).symm
    · change source.hom ≫
        (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
          square_isPullback).hom =
        (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
          square_isPullback).hom ≫ target.hom
      have h := congrArg (fun q => q.f) pair.2
      change pair.1.1.hom.f ≫ semanticExactGlobalBeta input interpretation z
          omega k g endpoint_eq square_isPullback =
        semanticExactGlobalBeta input interpretation z omega k g endpoint_eq
          square_isPullback ≫ pair.1.2.hom.f at h
      simpa only [source, target, globalKaroubiAutOfIdentity,
        semanticExactGlobalBeta_eq_alpha_of_not_selected input interpretation z
          omega k g endpoint_eq square_isPullback notSelected] using h
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> exact map_mul _ _ _

/-- Restriction of the selected lift recovers its supplied source image
automorphism. -/
private theorem globalSelectedSection_source_rightInverse
    (selected : semanticExactBarSelectedAt input interpretation z omega)
    (pair : SemanticExactGlobalImageComparison input interpretation z omega
      k g endpoint_eq square_isPullback) :
    (semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (globalSelectedComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback selected pair).1).1 = pair.1.1 := by
  apply Iso.ext
  apply Karoubi.Hom.ext
  rw [show
    (semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (globalSelectedComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback selected pair).1).1.hom.f =
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      (globalSelectedComparisonSectionHom input interpretation z omega k g
        endpoint_eq square_isPullback selected pair).1.1.1.hom ≫
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback by
      exact idempotentEndpointRestrictionHom_fst_hom_f _ _
        (semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
        (semanticExactGlobalE_idem input interpretation z omega k g endpoint_eq
          square_isPullback)
        (semanticExactGlobalD_idem input interpretation z omega k g endpoint_eq)
        (globalSelectedComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback selected pair).1]
  let G := semanticDerivedDirectAdmissibleGeometryAt input
    (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq
    selected.2
  let normalized := globalSelectedNormalizedAutHom input interpretation z omega
    k g endpoint_eq square_isPullback selected pair.1.1
  let lifted := canonicalNormalizationAutomorphismSectionHom G normalized
  have h := congrArg (fun q => q.hom.f.hom)
    (canonicalNormalizationAutomorphismSection_rightInverse G normalized)
  change (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback) ≫ lifted.hom.hom ≫
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback = pair.1.1.hom.f
  have hE := semanticExactGlobalE_eq_normalization input interpretation z
    omega k g endpoint_eq square_isPullback selected
  rw [hE]
  change canonicalGeometryNormalization
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g endpoint_eq).1
      (semanticExactDirectGeometryAt_admissible input interpretation z k g
        endpoint_eq selected.2) ≫ lifted.hom.hom = pair.1.1.hom.f at h
  rw [← Category.assoc, h]
  have hp := Karoubi.comp_p pair.1.1.hom
  change pair.1.1.hom.f ≫
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback = pair.1.1.hom.f at hp
  rw [hE] at hp
  exact hp

private theorem globalSelectedSection_rightInverse
    (selected : semanticExactBarSelectedAt input interpretation z omega)
    (pair : SemanticExactGlobalImageComparison input interpretation z omega
      k g endpoint_eq square_isPullback) :
    semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (globalSelectedComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback selected pair).1 = pair.1 := by
  let s := globalSelectedComparisonSectionHom input interpretation z omega k g
    endpoint_eq square_isPullback selected pair
  let E := semanticExactGlobalE input interpretation z omega k g endpoint_eq
    square_isPullback
  let D := semanticExactGlobalD input interpretation z omega k g endpoint_eq
  let c := (semanticExactGlobalAlphaIso input interpretation z k g endpoint_eq
    square_isPullback).hom
  have hraw : s.1.1.1.hom ≫ c = c ≫ s.1.1.2.hom := s.2
  have hE : s.1.1.1.hom ≫ E = E ≫ s.1.1.1.hom := s.1.2.1
  have hD : s.1.1.2.hom ≫ D = D ≫ s.1.1.2.hom := s.1.2.2
  have hbeta : s.1.1.1.hom ≫ (E ≫ c ≫ D) =
      (E ≫ c ≫ D) ≫ s.1.1.2.hom := by
    calc
      _ = E ≫ s.1.1.1.hom ≫ c ≫ D := by
        simp only [← Category.assoc, hE]
      _ = E ≫ c ≫ s.1.1.2.hom ≫ D := by
        calc
          _ = E ≫ (s.1.1.1.hom ≫ c) ≫ D := by
            simp only [Category.assoc]
          _ = E ≫ (c ≫ s.1.1.2.hom) ≫ D := by rw [hraw]
          _ = _ := by simp only [Category.assoc]
      _ = _ := by simp only [Category.assoc, hD]
  have himage :
      (semanticExactGlobalRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback s.1) ∈
      SemanticExactGlobalImageComparison input interpretation z omega k g
        endpoint_eq square_isPullback := by
    have hmem : s.1 ∈
        centralizingCompatibleSubgroup
          (semanticExactGlobalBeta input interpretation z omega k g
            endpoint_eq square_isPullback) E D := hbeta
    rw [← semanticExactGlobalRestriction_preimage_eq_beta input
      interpretation z omega k g endpoint_eq square_isPullback] at hmem
    exact hmem
  have hcomp := himage
  change (semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback s.1).1.hom ≫
      semanticExactGlobalBetaImage input interpretation z omega k g endpoint_eq
        square_isPullback =
    semanticExactGlobalBetaImage input interpretation z omega k g endpoint_eq
      square_isPullback ≫
      (semanticExactGlobalRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback s.1).2.hom at hcomp
  have hsource := globalSelectedSection_source_rightInverse input interpretation
    z omega k g endpoint_eq square_isPullback selected pair
  apply Prod.ext
  · exact hsource
  · apply Iso.ext
    apply (cancel_epi (semanticExactGlobalBetaIso input interpretation z omega
      k g endpoint_eq square_isPullback).hom).1
    rw [semanticExactGlobalBetaIso_hom_eq input interpretation z omega k g
      endpoint_eq square_isPullback]
    calc
      _ = (semanticExactGlobalRestrictionHom input interpretation z omega k g
            endpoint_eq square_isPullback s.1).1.hom ≫
          semanticExactGlobalBetaImage input interpretation z omega k g
            endpoint_eq square_isPullback := hcomp.symm
      _ = pair.1.1.hom ≫
          semanticExactGlobalBetaImage input interpretation z omega k g
            endpoint_eq square_isPullback := by rw [hsource]
      _ = _ := pair.2

private theorem globalOffSection_rightInverse
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega)
    (pair : SemanticExactGlobalImageComparison input interpretation z omega
      k g endpoint_eq square_isPullback) :
    semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback
        (globalOffComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback notSelected pair).1 = pair.1 := by
  obtain ⟨he, hd⟩ := semanticExactGlobalProjectors_eq_id input
    interpretation z omega k g endpoint_eq square_isPullback notSelected
  apply Prod.ext
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (semanticExactGlobalRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback
          (globalOffComparisonSectionHom input interpretation z omega k g
            endpoint_eq square_isPullback notSelected pair).1).1.hom.f =
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback ≫
        (globalOffComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback notSelected pair).1.1.1.hom ≫
        semanticExactGlobalE input interpretation z omega k g endpoint_eq
          square_isPullback by
        exact idempotentEndpointRestrictionHom_fst_hom_f _ _
          (semanticExactGlobalE input interpretation z omega k g endpoint_eq
            square_isPullback)
          (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
          (semanticExactGlobalE_idem input interpretation z omega k g
            endpoint_eq square_isPullback)
          (semanticExactGlobalD_idem input interpretation z omega k g
            endpoint_eq)
          (globalOffComparisonSectionHom input interpretation z omega k g
            endpoint_eq square_isPullback notSelected pair).1]
    simp only [he, Category.id_comp, Category.comp_id]
    rfl
  · apply Iso.ext
    apply Karoubi.Hom.ext
    rw [show
      (semanticExactGlobalRestrictionHom input interpretation z omega k g
        endpoint_eq square_isPullback
          (globalOffComparisonSectionHom input interpretation z omega k g
            endpoint_eq square_isPullback notSelected pair).1).2.hom.f =
        semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
        (globalOffComparisonSectionHom input interpretation z omega k g
          endpoint_eq square_isPullback notSelected pair).1.1.2.hom ≫
        semanticExactGlobalD input interpretation z omega k g endpoint_eq by
        exact idempotentEndpointRestrictionHom_snd_hom_f _ _
          (semanticExactGlobalE input interpretation z omega k g endpoint_eq
            square_isPullback)
          (semanticExactGlobalD input interpretation z omega k g endpoint_eq)
          (semanticExactGlobalE_idem input interpretation z omega k g
            endpoint_eq square_isPullback)
          (semanticExactGlobalD_idem input interpretation z omega k g
            endpoint_eq)
          (globalOffComparisonSectionHom input interpretation z omega k g
            endpoint_eq square_isPullback notSelected pair).1]
    simp only [hd, Category.id_comp, Category.comp_id]
    rfl

/-- The actual complete-geometry comparison restriction on raw-compatible
centralizing endpoint pairs. -/
noncomputable def semanticExactGlobalCompatibleRestrictionHom :
    SemanticExactGlobalRawComparison input interpretation z omega k g
      endpoint_eq square_isPullback →*
    SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback where
  toFun a := by
    let E := semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback
    let D := semanticExactGlobalD input interpretation z omega k g endpoint_eq
    let c := (semanticExactGlobalAlphaIso input interpretation z k g
      endpoint_eq square_isPullback).hom
    have hraw : a.1.1.1.hom ≫ c = c ≫ a.1.1.2.hom := a.2
    have hE : a.1.1.1.hom ≫ E = E ≫ a.1.1.1.hom := a.1.2.1
    have hD : a.1.1.2.hom ≫ D = D ≫ a.1.1.2.hom := a.1.2.2
    have hbeta : a.1.1.1.hom ≫ (E ≫ c ≫ D) =
        (E ≫ c ≫ D) ≫ a.1.1.2.hom := by
      calc
        _ = E ≫ a.1.1.1.hom ≫ c ≫ D := by
          simp only [← Category.assoc, hE]
        _ = E ≫ c ≫ a.1.1.2.hom ≫ D := by
          calc
            _ = E ≫ (a.1.1.1.hom ≫ c) ≫ D := by
              simp only [Category.assoc]
            _ = E ≫ (c ≫ a.1.1.2.hom) ≫ D := by rw [hraw]
            _ = _ := by simp only [Category.assoc]
        _ = _ := by simp only [Category.assoc, hD]
    refine ⟨semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback a.1, ?_⟩
    have hmem : a.1 ∈ centralizingCompatibleSubgroup
        (semanticExactGlobalBeta input interpretation z omega k g endpoint_eq
          square_isPullback) E D := hbeta
    rw [← semanticExactGlobalRestriction_preimage_eq_beta input interpretation
      z omega k g endpoint_eq square_isPullback] at hmem
    exact hmem
  map_one' := by
    apply Subtype.ext
    exact map_one _
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul _ _ _

/-- A section of the full complete-geometry comparison restriction, with
the diagnostic selector deciding which concrete lift is used. -/
noncomputable def semanticExactGlobalComparisonSectionHom :
    SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback →*
    SemanticExactGlobalRawComparison input interpretation z omega k g
      endpoint_eq square_isPullback := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · exact globalSelectedComparisonSectionHom input interpretation z omega k g
      endpoint_eq square_isPullback selected
  · exact globalOffComparisonSectionHom input interpretation z omega k g
      endpoint_eq square_isPullback selected

/-- The full comparison section is a right inverse on every Karoubi image
automorphism pair, including endpoint changes moving the pointed doctrine. -/
theorem semanticExactGlobalComparisonSection_rightInverse
    (pair : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback) :
    semanticExactGlobalCompatibleRestrictionHom input interpretation z omega
      k g endpoint_eq square_isPullback
        (semanticExactGlobalComparisonSectionHom input interpretation z omega
          k g endpoint_eq square_isPullback pair) = pair := by
  classical
  apply Subtype.ext
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · simpa [semanticExactGlobalCompatibleRestrictionHom,
      semanticExactGlobalComparisonSectionHom, selected] using
      globalSelectedSection_rightInverse input interpretation z omega k g
        endpoint_eq square_isPullback selected pair
  · simpa [semanticExactGlobalCompatibleRestrictionHom,
      semanticExactGlobalComparisonSectionHom, selected] using
      globalOffSection_rightInverse input interpretation z omega k g
        endpoint_eq square_isPullback selected pair

/-- Both selected projectors act as identities at their pointed-doctrine
bases, because they come from endomorphisms of the fixed geometry fiber. -/
theorem semanticExactGlobalE_bottom_id :
    (semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback).base.base =
      𝟙 (packagePoint (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1.core) := by
  exact semanticGeometryFiberMorphism_packageBase_identity
    (semanticExactBarEAt input interpretation z omega k g endpoint_eq
      square_isPullback)

theorem semanticExactGlobalD_bottom_id :
    (semanticExactGlobalD input interpretation z omega k g
      endpoint_eq).base.base =
      𝟙 (packagePoint (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z) k g
        endpoint_eq).1.core) := by
  exact semanticGeometryFiberMorphism_packageBase_identity
    (semanticExactBarDAt input interpretation z omega k g endpoint_eq)

/-- The full comparison section preserves the source endpoint's actual
pointed-doctrine map, on both selector branches. -/
theorem semanticExactGlobalComparisonSection_source_base
    (pair : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback) :
    (semanticExactGlobalComparisonSectionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair).1.1.1.hom.base.base =
    pair.1.1.hom.f.base.base := by
  let s := semanticExactGlobalComparisonSectionHom input interpretation z omega
    k g endpoint_eq square_isPullback pair
  have h := congrArg
    (fun q : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback => q.1.1.hom.f.base.base)
    (semanticExactGlobalComparisonSection_rightInverse input interpretation z
      omega k g endpoint_eq square_isPullback pair)
  change ((semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback s.1).1.hom.f.base.base) =
    pair.1.1.hom.f.base.base at h
  simp only [semanticExactGlobalRestrictionHom,
    idempotentEndpointRestrictionHom_fst_hom_f] at h
  change ((semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback ≫ s.1.1.1.hom ≫
    semanticExactGlobalE input interpretation z omega k g endpoint_eq
      square_isPullback).base.base) = pair.1.1.hom.f.base.base at h
  change (crossStageProjection.{u, v} U).map
      (semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback ≫ s.1.1.1.hom ≫
      semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback) =
    (crossStageProjection.{u, v} U).map pair.1.1.hom.f at h
  rw [Functor.map_comp, Functor.map_comp] at h
  have he : (crossStageProjection.{u, v} U).map
      (semanticExactGlobalE input interpretation z omega k g endpoint_eq
        square_isPullback) = 𝟙 _ :=
    semanticExactGlobalE_bottom_id input interpretation z omega k g
      endpoint_eq square_isPullback
  rw [he] at h
  simpa using h

/-- The full comparison section also preserves the target endpoint's
actual pointed-doctrine map. -/
theorem semanticExactGlobalComparisonSection_target_base
    (pair : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback) :
    (semanticExactGlobalComparisonSectionHom input interpretation z omega k g
      endpoint_eq square_isPullback pair).1.1.2.hom.base.base =
    pair.1.2.hom.f.base.base := by
  let s := semanticExactGlobalComparisonSectionHom input interpretation z omega
    k g endpoint_eq square_isPullback pair
  have h := congrArg
    (fun q : SemanticExactGlobalImageComparison input interpretation z omega k g
      endpoint_eq square_isPullback => q.1.2.hom.f.base.base)
    (semanticExactGlobalComparisonSection_rightInverse input interpretation z
      omega k g endpoint_eq square_isPullback pair)
  change ((semanticExactGlobalRestrictionHom input interpretation z omega k g
      endpoint_eq square_isPullback s.1).2.hom.f.base.base) =
    pair.1.2.hom.f.base.base at h
  simp only [semanticExactGlobalRestrictionHom,
    idempotentEndpointRestrictionHom_snd_hom_f] at h
  change ((semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
    s.1.1.2.hom ≫
    semanticExactGlobalD input interpretation z omega k g endpoint_eq).base.base) =
      pair.1.2.hom.f.base.base at h
  change (crossStageProjection.{u, v} U).map
      (semanticExactGlobalD input interpretation z omega k g endpoint_eq ≫
      s.1.1.2.hom ≫
      semanticExactGlobalD input interpretation z omega k g endpoint_eq) =
    (crossStageProjection.{u, v} U).map pair.1.2.hom.f at h
  rw [Functor.map_comp, Functor.map_comp] at h
  have hd : (crossStageProjection.{u, v} U).map
      (semanticExactGlobalD input interpretation z omega k g endpoint_eq) =
        𝟙 _ := semanticExactGlobalD_bottom_id input interpretation z omega k g
          endpoint_eq
  rw [hd] at h
  simpa using h

end Semantic

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
