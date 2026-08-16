import ResearchLean.AG.GeometryTransport
import ResearchLean.AG.AtomFoundation.Opcartesian
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber

/-!
# The typed projection tower for G-109

This module fixes the categorical tower used by every later cross-stage
construction.  It composes the G-108 geometry projection with the G-101 core
projection, constructs the pointed-doctrine forgetful functor, proves that its
fibers are discrete, and derives strong cocartesianness for the composite
projection from the two stage-local universal properties.

## Implementation notes

The composite universal property is proved by two successive factorizations:
first in the core stage and then in the geometry stage.  A composite
cocartesian certificate is not stored in the data.  The final doctrine stage
uses Mathlib's categorical `Functor.Fiber`; replacing it with a proposition
saying only that homs are determined by their doctrine component would omit
the required equality of pointed objects.
-/

namespace AAT.AG.CrossStageCoherence

universe u v u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open AtomFoundation
open GeometryTransport

/-- Pointed extraction instances are determined by doctrine and dependent source. -/
@[ext] theorem ExtractionInstance.ext {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (hdoctrine : X.doctrine = Y.doctrine)
    (hsource : HEq X.source Y.source) : X = Y := by
  cases X
  cases Y
  cases hdoctrine
  cases hsource
  rfl

/-- The two non-discrete stages of the reading tower, composed over `ExtInst_U`. -/
noncomputable def crossStageProjection (U : AtomCarrier.{u}) :
    GeomReadCategory.{u, v} U ⥤ ExtractionInstance U :=
  geometryProjection U ⋙ packageProjection U

/-- The composite projection forgets a geometry package down to its pointed doctrine. -/
@[simp] theorem crossStageProjection_obj {U : AtomCarrier.{u}}
    (G : GeomReadCategory.{u, v} U) :
    (crossStageProjection U).obj G = packagePoint G.core :=
  rfl

/-- The composite projection maps through both actual stage morphisms. -/
@[simp] theorem crossStageProjection_map {U : AtomCarrier.{u}}
    {G H : GeomReadCategory.{u, v} U} (F : G ⟶ H) :
    (crossStageProjection U).map F = F.base.base :=
  rfl

/-- Forget the selected source and retain the exact extraction doctrine. -/
def extInstToDoctrine (U : AtomCarrier.{u}) :
    ExtractionInstance U ⥤ ExtractionDoctrine U where
  obj X := X.doctrine
  map σ := σ.doctrineHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The doctrine forgetful functor reads the stored doctrine. -/
@[simp] theorem extInstToDoctrine_obj {U : AtomCarrier.{u}}
    (X : ExtractionInstance U) :
    (extInstToDoctrine U).obj X = X.doctrine :=
  rfl

/-- The doctrine forgetful functor reads the full exact doctrine morphism. -/
@[simp] theorem extInstToDoctrine_map {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (σ : X ⟶ Y) :
    (extInstToDoctrine U).map σ = σ.doctrineHom :=
  rfl

/--
A morphism in a fixed doctrine fiber forces equality of the selected sources.

The proof uses both the fiber equation and `ExtInstHom.source_eq`; it does not
discard the pointed part of an `ExtInstHom`.
-/
def extInstDoctrineFiberSource {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (X : (extInstToDoctrine U).Fiber D) :
    D.Source := by
  exact X.property ▸ X.1.source

/-- The canonical pointed object of the doctrine fiber selected by a source. -/
def extInstDoctrineFiberMk {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (source : D.Source) :
    (extInstToDoctrine U).Fiber D :=
  ⟨⟨D, source⟩, rfl⟩

/-- Every object in a doctrine fiber is its canonical source-pointed representative. -/
theorem extInstDoctrineFiberMk_source {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) (X : (extInstToDoctrine U).Fiber D) :
    extInstDoctrineFiberMk D (extInstDoctrineFiberSource D X) = X := by
  rcases X with ⟨⟨E, source⟩, hE⟩
  cases hE
  rfl

/-- A fiber morphism between canonical source points identifies the sources. -/
theorem extInstDoctrineFiberMk_source_eq_of_hom {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) {source target : D.Source}
    (f : extInstDoctrineFiberMk D source ⟶
      extInstDoctrineFiberMk D target) : source = target := by
  have hf : f.1.doctrineHom = (𝟙 D : D ⟶ D) := by
    letI : (extInstToDoctrine U).IsHomLift (𝟙 D) f.1 := f.2
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (a := ExtractionInstance.mk D source)
      (b := ExtractionInstance.mk D target)
      (extInstToDoctrine U) (𝟙 D) f.1).symm
  simpa [extInstDoctrineFiberMk, hf] using f.1.source_eq

/--
A morphism in a fixed doctrine fiber forces equality of the pointed objects.

The source equality is first calculated on the canonical representatives, so
the dependent source types are not replaced by an untracked cast.
-/
theorem extInstToDoctrine_fiber_obj_eq_of_hom {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U)
    {X Y : (extInstToDoctrine U).Fiber D} (f : X ⟶ Y) : X = Y := by
  rw [← extInstDoctrineFiberMk_source D X,
    ← extInstDoctrineFiberMk_source D Y] at f ⊢
  exact congrArg (extInstDoctrineFiberMk D)
    (extInstDoctrineFiberMk_source_eq_of_hom D f)

/-- The categorical fiber of `ExtInst_U → Doct_U` over every doctrine is discrete. -/
instance extInstToDoctrine_fiber_isDiscrete {U : AtomCarrier.{u}}
    (D : ExtractionDoctrine U) :
    IsDiscrete ((extInstToDoctrine U).Fiber D) where
  subsingleton X Y := by
    constructor
    intro f g
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply ExtInstHom.ext
    letI : (extInstToDoctrine U).IsHomLift (𝟙 D) f.1 := f.2
    letI : (extInstToDoctrine U).IsHomLift (𝟙 D) g.1 := g.2
    have hf := CategoryTheory.IsHomLift.fac'
      (extInstToDoctrine U) (𝟙 D) f.1
    have hg := CategoryTheory.IsHomLift.fac'
      (extInstToDoctrine U) (𝟙 D) g.1
    exact hf.trans hg.symm
  eq_of_hom f := extInstToDoctrine_fiber_obj_eq_of_hom D f

/--
Strongly cocartesian morphisms compose through a pair of projection functors.

The first hypothesis is the upper-stage universal property and the second is
the universal property of its projected morphism.  The composite property is
derived by factoring a target morphism in those two stages in order.
-/
theorem stronglyCocartesian_comp_projection
    {𝒳 : Type u₁} {𝒴 : Type u₂} {𝒵 : Type u₃}
    [Category.{v₁} 𝒳] [Category.{v₂} 𝒴] [Category.{v₃} 𝒵]
    (q : 𝒳 ⥤ 𝒴) (p : 𝒴 ⥤ 𝒵)
    {a b : 𝒳} (φ : a ⟶ b)
    [q.IsStronglyCocartesian (q.map φ) φ]
    [p.IsStronglyCocartesian (p.map (q.map φ)) (q.map φ)] :
    (q ⋙ p).IsStronglyCocartesian ((q ⋙ p).map φ) φ := by
  apply CategoryTheory.Functor.IsStronglyCocartesian.mk
  intro c g ψ hψ
  letI : (q ⋙ p).IsHomLift (((q ⋙ p).map φ) ≫ g) ψ := hψ
  letI : p.IsHomLift (p.map (q.map φ) ≫ g) (q.map ψ) := by
    have hmap := CategoryTheory.IsHomLift.eq_of_isHomLift
      (q ⋙ p) (((q ⋙ p).map φ) ≫ g) ψ
    change p.map (q.map φ) ≫ g = p.map (q.map ψ) at hmap
    rw [hmap]
    infer_instance
  rcases CategoryTheory.Functor.IsStronglyCocartesian.universal_property
      p (p.map (q.map φ)) (q.map φ) g
      (p.map (q.map φ) ≫ g) rfl (q.map ψ) with
    ⟨η, hη, hη_unique⟩
  letI : p.IsHomLift g η := hη.1
  letI : q.IsHomLift (q.map φ ≫ η) ψ := by
    rw [hη.2]
    infer_instance
  rcases CategoryTheory.Functor.IsStronglyCocartesian.universal_property
      q (q.map φ) φ η (q.map φ ≫ η) rfl ψ with
    ⟨χ, hχ, hχ_unique⟩
  letI : q.IsHomLift η χ := hχ.1
  have compositeLift : (q ⋙ p).IsHomLift g χ := by
    have hq := CategoryTheory.IsHomLift.eq_of_isHomLift q η χ
    have hp := CategoryTheory.IsHomLift.eq_of_isHomLift p g η
    have hmap : g = (q ⋙ p).map χ := by
      change g = p.map (q.map χ)
      calc
        g = p.map η := hp
        _ = p.map (q.map χ) := congrArg p.map hq
    rw [hmap]
    infer_instance
  refine ⟨χ, ⟨compositeLift, hχ.2⟩, ?_⟩
  intro χ' hχ'
  letI : (q ⋙ p).IsHomLift g χ' := hχ'.1
  letI : p.IsHomLift g (q.map χ') := by
    have hmap := CategoryTheory.IsHomLift.eq_of_isHomLift (q ⋙ p) g χ'
    change g = p.map (q.map χ') at hmap
    rw [hmap]
    infer_instance
  have hqfac : q.map φ ≫ q.map χ' = q.map ψ := by
    simpa only [← q.map_comp] using congrArg q.map hχ'.2
  have hqχ' : q.map χ' = η :=
    hη_unique (q.map χ') ⟨inferInstance, hqfac⟩
  letI : q.IsHomLift η χ' := by
    rw [← hqχ']
    infer_instance
  exact hχ_unique χ' ⟨inferInstance, hχ'.2⟩

/-- Reindex a strong cocartesian certificate along its actual hom-lift witness. -/
theorem stronglyCocartesian_of_isHomLift
    {𝒳 : Type u₁} {𝒴 : Type u₂}
    [Category.{v₁} 𝒳] [Category.{v₂} 𝒴]
    (q : 𝒳 ⥤ 𝒴) {R S : 𝒴} {a b : 𝒳}
    (f : R ⟶ S) (φ : a ⟶ b)
    [q.IsStronglyCocartesian (q.map φ) φ]
    [q.IsHomLift f φ] : q.IsStronglyCocartesian f φ := by
  subst_hom_lift q f φ
  infer_instance

/--
The G-108 canonical geometry lift is strongly cocartesian for the composite
projection to pointed doctrines.

Both local certificates are generated by the reviewed G-108 and G-101
theorems before the generic composition theorem is applied.
-/
theorem geomTransportAlongHom_isCrossStageStronglyCocartesian
    {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (σ : ExactDoctrineHom G.core.reading.doctrine E) :
    (crossStageProjection U).IsStronglyCocartesian
      ((crossStageProjection U).map (geomTransportAlongHom G σ))
      (geomTransportAlongHom G σ) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      ((geometryProjection U).map (geomTransportAlongHom G σ))
      (geomTransportAlongHom G σ) := by
    simpa only [geomTransportAlongHom_base] using
      geomTransportAlongHom_isStronglyCocartesian G σ
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map
        ((geometryProjection U).map (geomTransportAlongHom G σ)))
      ((geometryProjection U).map (geomTransportAlongHom G σ)) := by
    simpa only [geomTransportAlongHom_base, packageProjection_map] using
      AAT.AG.AtomFoundation.transportAlongHom_isStronglyCocartesian G.core σ
  exact stronglyCocartesian_comp_projection
    (geometryProjection U) (packageProjection U) (geomTransportAlongHom G σ)

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
