import ResearchLean.AG.DiagnosticConservativity.AmbidextrousLift
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# G-113 revision 2 general transport/reindexing adjunction

For an arbitrary semantic base arrow, this module reconstructs the hom
correspondence between canonical covariant transport and the G-112
semantic-global reindexing directly from their universal properties.  The
adjunction, unit, counit, and triangle identities are generated rather than
accepted from a caller.  No finite-code realization or decidable carrier is
required.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

/--
Send a vertical map out of canonical pushforward to its cartesian transpose.
The result is the unique vertical factor through the selected cartesian lift.
-/
noncomputable def semanticGlobalTransportToReindexHom
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : (coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
      targetPackage) :
    sourcePackage ⟶ (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage := by
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift baseHom
      (coreFiberLift baseHom sourcePackage) :=
    coreFiberLift_isHomLift baseHom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift baseHom
      (coreFiberLift baseHom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (baseHom ≫ 𝟙 target)
        (coreFiberLift baseHom sourcePackage ≫ hom.1))
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (packageProjection U) baseHom cartLift.hom
      (g := 𝟙 source) (f' := baseHom)
      (Category.id_comp baseHom).symm
      (coreFiberLift baseHom sourcePackage ≫ hom.1), inferInstance⟩

/-- Defining cartesian factor graph of `semanticGlobalTransportToReindexHom`. -/
theorem semanticGlobalTransportToReindexHom_fac
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : (coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
      targetPackage) :
    (semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage hom).1 ≫
        (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom =
      coreFiberLift baseHom sourcePackage ≫ hom.1 := by
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift baseHom
      (coreFiberLift baseHom sourcePackage) :=
    coreFiberLift_isHomLift baseHom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift baseHom
      (coreFiberLift baseHom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (baseHom ≫ 𝟙 target)
        (coreFiberLift baseHom sourcePackage ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (packageProjection U) baseHom cartLift.hom
    (Category.id_comp baseHom).symm
    (coreFiberLift baseHom sourcePackage ≫ hom.1)

/--
Send a vertical map into selected reindexing to its cocartesian transpose.
The result is the unique vertical factor out of the canonical G-109 lift.
-/
noncomputable def semanticGlobalReindexToTransportHom
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) :
    (coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
      targetPackage := by
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      (coreFiberLift baseHom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian baseHom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift baseHom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 source) ≫ baseHom)
        (hom.1 ≫ cartLift.hom))
  exact ⟨CategoryTheory.Functor.IsStronglyCocartesian.map
      (packageProjection U) baseHom
      (coreFiberLift baseHom sourcePackage)
      (g := 𝟙 target) (f' := baseHom)
      (Category.comp_id baseHom).symm
      (hom.1 ≫ cartLift.hom), inferInstance⟩

/-- Defining cocartesian factor graph of `semanticGlobalReindexToTransportHom`. -/
theorem semanticGlobalReindexToTransportHom_fac
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) :
    coreFiberLift baseHom sourcePackage ≫
        (semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage hom).1 =
      hom.1 ≫ (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom := by
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      (coreFiberLift baseHom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian baseHom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift baseHom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 source) ≫ baseHom)
        (hom.1 ≫ cartLift.hom))
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    (packageProjection U) baseHom
    (coreFiberLift baseHom sourcePackage)
    (Category.comp_id baseHom).symm (hom.1 ≫ cartLift.hom)

/-- Cartesian and cocartesian transposition are inverse in the target fiber. -/
theorem semanticGlobalReindexToTransportHom_toReindex
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : (coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
      targetPackage) :
    semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage
        (semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      (coreFiberLift baseHom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian baseHom sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) baseHom
    (coreFiberLift baseHom sourcePackage)
    (𝟙 target)
  change coreFiberLift baseHom sourcePackage ≫
      (semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage
        (semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage hom)).1 =
    coreFiberLift baseHom sourcePackage ≫ hom.1
  rw [semanticGlobalReindexToTransportHom_fac, semanticGlobalTransportToReindexHom_fac]

/-- Cartesian and cocartesian transposition are inverse in the source fiber. -/
theorem semanticGlobalTransportToReindexHom_toCoreTransport
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) :
    semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage
        (semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) baseHom cartLift.hom
    (𝟙 source)
  change (semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage
      (semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage hom)).1 ≫
      cartLift.hom = hom.1 ≫ cartLift.hom
  rw [semanticGlobalTransportToReindexHom_fac, semanticGlobalReindexToTransportHom_fac]

/-- The producer-derived hom-set equivalence for one semantic base arrow. -/
noncomputable def semanticGlobalTransportReindexHomEquiv
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    (targetPackage : CoreFiber target) :
    ((coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
        targetPackage) ≃
      (sourcePackage ⟶
        (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) where
  toFun := semanticGlobalTransportToReindexHom baseHom sourcePackage targetPackage
  invFun := semanticGlobalReindexToTransportHom baseHom sourcePackage targetPackage
  left_inv := semanticGlobalReindexToTransportHom_toReindex baseHom sourcePackage targetPackage
  right_inv := semanticGlobalTransportToReindexHom_toCoreTransport baseHom sourcePackage targetPackage

/-! ## Naturality of the generated correspondence -/

/-- The inverse transpose is natural in the source-fiber variable. -/
theorem semanticGlobalReindexToTransportHom_comp_left
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    {first second : CoreFiber source}
    (sourceHom : first ⟶ second)
    (targetPackage : CoreFiber target)
    (hom : second ⟶
      (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) :
    semanticGlobalReindexToTransportHom baseHom first targetPackage (sourceHom ≫ hom) =
      (coreFiberTransportFunctor baseHom).map sourceHom ≫
        semanticGlobalReindexToTransportHom baseHom second targetPackage hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      (coreFiberLift baseHom first) :=
    coreFiberLift_isStronglyCocartesian baseHom first
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) baseHom
    (coreFiberLift baseHom first)
    (𝟙 target)
  change coreFiberLift baseHom first ≫
      (semanticGlobalReindexToTransportHom baseHom first targetPackage
        (sourceHom ≫ hom)).1 =
    coreFiberLift baseHom first ≫
      ((coreFiberTransportFunctor baseHom).map sourceHom).1 ≫
      (semanticGlobalReindexToTransportHom baseHom second targetPackage hom).1
  rw [semanticGlobalReindexToTransportHom_fac]
  change (sourceHom.1 ≫ hom.1) ≫
      (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom =
    coreFiberLift baseHom first ≫
      ((coreFiberTransportFunctor baseHom).map sourceHom).1 ≫
      (semanticGlobalReindexToTransportHom baseHom second targetPackage hom).1
  have transportFac :
      coreFiberLift baseHom first ≫
          ((coreFiberTransportFunctor baseHom).map sourceHom).1 =
        sourceHom.1 ≫ coreFiberLift baseHom second := by
    simpa only [coreFiberTransportFunctor] using
      coreFiberTransportMap_fac baseHom sourceHom
  calc
    _ = sourceHom.1 ≫
        (hom.1 ≫ (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom) :=
      Category.assoc _ _ _
    _ = sourceHom.1 ≫
        (coreFiberLift baseHom second ≫
          (semanticGlobalReindexToTransportHom baseHom second targetPackage hom).1) := by
      rw [semanticGlobalReindexToTransportHom_fac]
    _ = (sourceHom.1 ≫ coreFiberLift baseHom second) ≫
        (semanticGlobalReindexToTransportHom baseHom second targetPackage hom).1 :=
      (Category.assoc _ _ _).symm
    _ = (coreFiberLift baseHom first ≫
        ((coreFiberTransportFunctor baseHom).map sourceHom).1) ≫
          (semanticGlobalReindexToTransportHom baseHom second targetPackage hom).1 := by
      rw [transportFac]
    _ = _ := Category.assoc _ _ _

/-- The forward transpose is natural in the target-fiber variable. -/
theorem semanticGlobalTransportToReindexHom_comp_right
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source)
    {first second : CoreFiber target}
    (hom : (coreFiberTransportFunctor baseHom).obj sourcePackage ⟶
      first)
    (targetHom : first ⟶ second) :
    semanticGlobalTransportToReindexHom baseHom sourcePackage second (hom ≫ targetHom) =
      semanticGlobalTransportToReindexHom baseHom sourcePackage first hom ≫
        (exact_bottom_semantic_global_reindex_functor baseHom).map targetHom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := exact_bottom_semantic_global_selected_lift baseHom second
  letI : (packageProjection U).IsStronglyCartesian baseHom cartLift.hom :=
    cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) baseHom cartLift.hom
    (𝟙 source)
  change (semanticGlobalTransportToReindexHom baseHom sourcePackage second
      (hom ≫ targetHom)).1 ≫ cartLift.hom =
    ((semanticGlobalTransportToReindexHom baseHom sourcePackage first hom).1 ≫
      ((exact_bottom_semantic_global_reindex_functor baseHom).map targetHom).1) ≫ cartLift.hom
  rw [semanticGlobalTransportToReindexHom_fac]
  rw [Category.assoc, exact_bottom_semantic_global_reindex_map_fac]
  rw [← Category.assoc, semanticGlobalTransportToReindexHom_fac]
  rfl

/-- The natural hom-equivalence package used to construct the adjunction. -/
noncomputable def semanticGlobalTransportReindexCoreHomEquiv
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    Adjunction.CoreHomEquiv
      (coreFiberTransportFunctor baseHom)
      (exact_bottom_semantic_global_reindex_functor baseHom) where
  homEquiv := semanticGlobalTransportReindexHomEquiv baseHom
  homEquiv_naturality_left_symm := by
    intro first second target sourceHom hom
    exact semanticGlobalReindexToTransportHom_comp_left baseHom sourceHom target hom
  homEquiv_naturality_right := by
    intro source first second hom targetHom
    exact semanticGlobalTransportToReindexHom_comp_right baseHom source hom targetHom

/-! ## The generated adjunction, unit, counit, and triangles -/

/--
Canonical cocartesian transport is left adjoint to G-112 semantic-global cartesian
reindexing over every semantic base arrow.
-/
noncomputable def semanticGlobalTransportReindexAdjunction
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    coreFiberTransportFunctor baseHom ⊣
      exact_bottom_semantic_global_reindex_functor baseHom :=
  Adjunction.mkOfHomEquiv (semanticGlobalTransportReindexCoreHomEquiv baseHom)

/-- The generated unit of core transport/reindexing. -/
noncomputable def semanticGlobalTransportReindexUnit
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    𝟭 (CoreFiber source) ⟶
      coreFiberTransportFunctor baseHom ⋙
        exact_bottom_semantic_global_reindex_functor baseHom :=
  (semanticGlobalTransportReindexAdjunction baseHom).unit

/-- The generated counit of core transport/reindexing. -/
noncomputable def semanticGlobalTransportReindexCounit
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    exact_bottom_semantic_global_reindex_functor baseHom ⋙
        coreFiberTransportFunctor baseHom ⟶
      𝟭 (CoreFiber target) :=
  (semanticGlobalTransportReindexAdjunction baseHom).counit

/-- The unit component is the cartesian transpose of the identity. -/
theorem semanticGlobalTransportReindexUnit_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source) :
    (semanticGlobalTransportReindexUnit baseHom).app sourcePackage =
      semanticGlobalTransportToReindexHom baseHom sourcePackage
        ((coreFiberTransportFunctor baseHom).obj sourcePackage)
        (𝟙 ((coreFiberTransportFunctor baseHom).obj sourcePackage)) := by
  rfl

/-- The counit component is the cocartesian transpose of the identity. -/
theorem semanticGlobalTransportReindexCounit_app
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (targetPackage : CoreFiber target) :
    (semanticGlobalTransportReindexCounit baseHom).app targetPackage =
      semanticGlobalReindexToTransportHom baseHom
        ((exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage)
        targetPackage
        (𝟙 ((exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage)) := by
  rfl

/-- The unit component factors the canonical cocartesian lift through the selected lift. -/
theorem semanticGlobalTransportReindexUnit_app_fac
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source) :
    ((semanticGlobalTransportReindexUnit baseHom).app sourcePackage).1 ≫
        (exact_bottom_semantic_global_selected_lift baseHom
          ((coreFiberTransportFunctor baseHom).obj sourcePackage)).hom =
      coreFiberLift baseHom sourcePackage := by
  rw [semanticGlobalTransportReindexUnit_app, semanticGlobalTransportToReindexHom_fac]
  change coreFiberLift baseHom sourcePackage ≫ 𝟙 _ =
    coreFiberLift baseHom sourcePackage
  exact Category.comp_id _

/-- The counit component factors the selected cartesian lift through the canonical lift. -/
theorem semanticGlobalTransportReindexCounit_app_fac
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (targetPackage : CoreFiber target) :
    coreFiberLift baseHom
        ((exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage) ≫
      ((semanticGlobalTransportReindexCounit baseHom).app targetPackage).1 =
        (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom := by
  rw [semanticGlobalTransportReindexCounit_app, semanticGlobalReindexToTransportHom_fac]
  change 𝟙 _ ≫ (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom =
    (exact_bottom_semantic_global_selected_lift baseHom targetPackage).hom
  exact Category.id_comp _

/-- Naturality of the generated unit. -/
theorem semanticGlobalTransportReindexUnit_naturality
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    {first second : CoreFiber source}
    (hom : first ⟶ second) :
    (𝟭 (CoreFiber source)).map hom ≫
        (semanticGlobalTransportReindexUnit baseHom).app second =
      (semanticGlobalTransportReindexUnit baseHom).app first ≫
        (coreFiberTransportFunctor baseHom ⋙
          exact_bottom_semantic_global_reindex_functor baseHom).map hom :=
  (semanticGlobalTransportReindexUnit baseHom).naturality hom

/-- Naturality of the generated counit. -/
theorem semanticGlobalTransportReindexCounit_naturality
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    {first second : CoreFiber target}
    (hom : first ⟶ second) :
    (exact_bottom_semantic_global_reindex_functor baseHom ⋙
        coreFiberTransportFunctor baseHom).map hom ≫
        (semanticGlobalTransportReindexCounit baseHom).app second =
      (semanticGlobalTransportReindexCounit baseHom).app first ≫
        (𝟭 (CoreFiber target)).map hom :=
  (semanticGlobalTransportReindexCounit baseHom).naturality hom

/-- The left triangle identity of the generated adjunction. -/
theorem semanticGlobalTransportReindex_left_triangle
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    Functor.whiskerRight (semanticGlobalTransportReindexUnit baseHom)
        (coreFiberTransportFunctor baseHom) ≫
      (Functor.associator
        (coreFiberTransportFunctor baseHom)
        (exact_bottom_semantic_global_reindex_functor baseHom)
        (coreFiberTransportFunctor baseHom)).hom ≫
      Functor.whiskerLeft (coreFiberTransportFunctor baseHom)
        (semanticGlobalTransportReindexCounit baseHom) =
      NatTrans.id
        (𝟭 (CoreFiber source) ⋙
          coreFiberTransportFunctor baseHom) :=
  (semanticGlobalTransportReindexAdjunction baseHom).left_triangle

/-- The right triangle identity of the generated adjunction. -/
theorem semanticGlobalTransportReindex_right_triangle
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    Functor.whiskerLeft (exact_bottom_semantic_global_reindex_functor baseHom)
        (semanticGlobalTransportReindexUnit baseHom) ≫
      (Functor.associator
        (exact_bottom_semantic_global_reindex_functor baseHom)
        (coreFiberTransportFunctor baseHom)
        (exact_bottom_semantic_global_reindex_functor baseHom)).inv ≫
      Functor.whiskerRight (semanticGlobalTransportReindexCounit baseHom)
        (exact_bottom_semantic_global_reindex_functor baseHom) =
      NatTrans.id
        (exact_bottom_semantic_global_reindex_functor baseHom ⋙
          𝟭 (CoreFiber source)) :=
  (semanticGlobalTransportReindexAdjunction baseHom).right_triangle

/-- Every generated unit component is invertible from cartesian uniqueness. -/
theorem semanticGlobalTransportReindexUnit_app_isIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (sourcePackage : CoreFiber source) :
    IsIso ((semanticGlobalTransportReindexUnit baseHom).app sourcePackage) := by
  let unit := (semanticGlobalTransportReindexUnit baseHom).app sourcePackage
  let selectedLift := exact_bottom_semantic_global_selected_lift baseHom
    ((coreFiberTransportFunctor baseHom).obj sourcePackage)
  let canonicalLift := coreFiberLift baseHom sourcePackage
  letI : (packageProjection U).IsStronglyCartesian baseHom
      selectedLift.hom := selectedLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCartesian baseHom
      canonicalLift := coreFiberLift_isStronglyCartesian_support
        baseHom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 source) unit.1 := unit.2
  have composed : (packageProjection U).IsStronglyCartesian
      ((𝟙 source) ≫ baseHom)
      (unit.1 ≫ selectedLift.hom) := by
    rw [Category.id_comp, semanticGlobalTransportReindexUnit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCartesian
      ((𝟙 source) ≫ baseHom)
      (unit.1 ≫ selectedLift.hom) := composed
  letI : (packageProjection U).IsStronglyCartesian
      (𝟙 source) unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := packageProjection U)
      (f := 𝟙 source) (g := baseHom)
      (φ := unit.1) (ψ := selectedLift.hom)
  letI : IsIso unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 source) unit.1
  exact coreFiberHom_isIso_of_total_isIso unit

/-- Every generated counit component is invertible from cocartesian uniqueness. -/
theorem semanticGlobalTransportReindexCounit_app_isIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target)
    (targetPackage : CoreFiber target) :
    IsIso ((semanticGlobalTransportReindexCounit baseHom).app targetPackage) := by
  let counit := (semanticGlobalTransportReindexCounit baseHom).app targetPackage
  let sourcePackage :=
    (exact_bottom_semantic_global_reindex_functor baseHom).obj targetPackage
  let canonicalLift := coreFiberLift baseHom sourcePackage
  let selectedLift := exact_bottom_semantic_global_selected_lift baseHom targetPackage
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      canonicalLift := coreFiberLift_isStronglyCocartesian
        baseHom sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian baseHom
      selectedLift.hom :=
    exact_bottom_semantic_global_selected_lift_isStronglyCocartesian baseHom targetPackage
  letI : (packageProjection U).IsHomLift
      (𝟙 target) counit.1 := counit.2
  have composed : (packageProjection U).IsStronglyCocartesian
      (baseHom ≫ 𝟙 target)
      (canonicalLift ≫ counit.1) := by
    rw [Category.comp_id, semanticGlobalTransportReindexCounit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (baseHom ≫ 𝟙 target)
      (canonicalLift ≫ counit.1) := composed
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 target) counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_comp
      (p := packageProjection U)
      (f := baseHom) (g := 𝟙 target)
      (φ := canonicalLift) (ψ := counit.1)
  letI : IsIso counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 target) counit.1
  exact coreFiberHom_isIso_of_total_isIso counit

/-- The generated unit natural transformation is an isomorphism. -/
theorem semanticGlobalTransportReindexUnit_isIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) : IsIso (semanticGlobalTransportReindexUnit baseHom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact semanticGlobalTransportReindexUnit_app_isIso baseHom

/-- The generated counit natural transformation is an isomorphism. -/
theorem semanticGlobalTransportReindexCounit_isIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) : IsIso (semanticGlobalTransportReindexCounit baseHom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact semanticGlobalTransportReindexCounit_app_isIso baseHom

/-! ## Natural isomorphisms and indexed specialization -/

/-- The generated unit, packaged as a natural isomorphism. -/
noncomputable def semanticGlobalTransportReindexUnitIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    𝟭 (CoreFiber source) ≅
      coreFiberTransportFunctor baseHom ⋙
        exact_bottom_semantic_global_reindex_functor baseHom := by
  letI : IsIso (semanticGlobalTransportReindexUnit baseHom) :=
    semanticGlobalTransportReindexUnit_isIso baseHom
  exact asIso (semanticGlobalTransportReindexUnit baseHom)

/-- The generated counit, packaged as a natural isomorphism. -/
noncomputable def semanticGlobalTransportReindexCounitIso
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    exact_bottom_semantic_global_reindex_functor baseHom ⋙
        coreFiberTransportFunctor baseHom ≅
      𝟭 (CoreFiber target) := by
  letI : IsIso (semanticGlobalTransportReindexCounit baseHom) :=
    semanticGlobalTransportReindexCounit_isIso baseHom
  exact asIso (semanticGlobalTransportReindexCounit baseHom)

/-- At every indexed vertex, the G-111 push is left adjoint to G-112 reindexing. -/
noncomputable def indexedDiagnosticTransportAdjunction
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportPush hom vertex ⊣
      indexedDiagnosticTransportReindex hom vertex :=
  semanticGlobalTransportReindexAdjunction (hom.app vertex)

/-- The indexed unit generated by the vertexwise adjunction. -/
noncomputable def indexedDiagnosticTransportUnit
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    𝟭 (CoreFiber (D.vertex vertex)) ⟶
      indexedDiagnosticTransportPush hom vertex ⋙
        indexedDiagnosticTransportReindex hom vertex :=
  semanticGlobalTransportReindexUnit (hom.app vertex)

/-- The indexed counit generated by the vertexwise adjunction. -/
noncomputable def indexedDiagnosticTransportCounit
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportReindex hom vertex ⋙
        indexedDiagnosticTransportPush hom vertex ⟶
      𝟭 (CoreFiber (E.vertex vertex)) :=
  semanticGlobalTransportReindexCounit (hom.app vertex)

/-- Every indexed unit component is invertible. -/
theorem indexedDiagnosticTransportUnit_app_isIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) (sourcePackage : CoreFiber (D.vertex vertex)) :
    IsIso ((indexedDiagnosticTransportUnit hom vertex).app sourcePackage) :=
  semanticGlobalTransportReindexUnit_app_isIso
    (hom.app vertex) sourcePackage

/-- Every indexed counit component is invertible. -/
theorem indexedDiagnosticTransportCounit_app_isIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) (targetPackage : CoreFiber (E.vertex vertex)) :
    IsIso ((indexedDiagnosticTransportCounit hom vertex).app targetPackage) :=
  semanticGlobalTransportReindexCounit_app_isIso
    (hom.app vertex) targetPackage

/-- The indexed unit is a natural isomorphism. -/
noncomputable def indexedDiagnosticTransportUnitIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    𝟭 (CoreFiber (D.vertex vertex)) ≅
      indexedDiagnosticTransportPush hom vertex ⋙
        indexedDiagnosticTransportReindex hom vertex :=
  semanticGlobalTransportReindexUnitIso (hom.app vertex)

/-- The indexed counit is a natural isomorphism. -/
noncomputable def indexedDiagnosticTransportCounitIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    indexedDiagnosticTransportReindex hom vertex ⋙
        indexedDiagnosticTransportPush hom vertex ≅
      𝟭 (CoreFiber (E.vertex vertex)) :=
  semanticGlobalTransportReindexCounitIso (hom.app vertex)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
