import ResearchLean.AG.DoctrineFiberProduct.ExactBottomGlobalLiftCoherence
import ResearchLean.AG.DoctrineFiberProduct.PackageProjectionBeckChevalleyExactness
import Mathlib.CategoryTheory.Adjunction.Basic

/-! Semantic-global transport/reindexing adjunction over every exact pointed arrow. -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

noncomputable def semanticCoreTransportToReindexHom
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      targetPackage) :
    sourcePackage ⟶ (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage := by
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift input.hom
      (coreFiberLift input.hom sourcePackage) :=
    coreFiberLift_isHomLift input.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (coreFiberLift input.hom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.hom ≫ 𝟙 input.target)
        (coreFiberLift input.hom sourcePackage ≫ hom.1))
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (packageProjection U) input.hom cartLift.hom
      (g := 𝟙 input.source) (f' := input.hom)
      (Category.id_comp input.hom).symm
      (coreFiberLift input.hom sourcePackage ≫ hom.1), inferInstance⟩

/-- Defining cartesian factor graph of `semanticCoreTransportToReindexHom`. -/
theorem semanticCoreTransportToReindexHom_fac
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      targetPackage) :
    (semanticCoreTransportToReindexHom input sourcePackage targetPackage hom).1 ≫
        (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom =
      coreFiberLift input.hom sourcePackage ≫ hom.1 := by
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift input.hom
      (coreFiberLift input.hom sourcePackage) :=
    coreFiberLift_isHomLift input.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (coreFiberLift input.hom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.hom ≫ 𝟙 input.target)
        (coreFiberLift input.hom sourcePackage ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (packageProjection U) input.hom cartLift.hom
    (Category.id_comp input.hom).symm
    (coreFiberLift input.hom sourcePackage ≫ hom.1)

/--
Send a vertical map into selected reindexing to its cocartesian transpose.
The result is the unique vertical factor out of the canonical G-109 lift.
-/
noncomputable def semanticReindexToCoreTransportHom
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) :
    (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      targetPackage := by
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      (coreFiberLift input.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 input.source) ≫ input.hom)
        (hom.1 ≫ cartLift.hom))
  exact ⟨CategoryTheory.Functor.IsStronglyCocartesian.map
      (packageProjection U) input.hom
      (coreFiberLift input.hom sourcePackage)
      (g := 𝟙 input.target) (f' := input.hom)
      (Category.comp_id input.hom).symm
      (hom.1 ≫ cartLift.hom), inferInstance⟩

/-- Defining cocartesian factor graph of `semanticReindexToCoreTransportHom`. -/
theorem semanticReindexToCoreTransportHom_fac
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) :
    coreFiberLift input.hom sourcePackage ≫
        (semanticReindexToCoreTransportHom input sourcePackage targetPackage hom).1 =
      hom.1 ≫ (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom := by
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      (coreFiberLift input.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 input.source) ≫ input.hom)
        (hom.1 ≫ cartLift.hom))
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    (packageProjection U) input.hom
    (coreFiberLift input.hom sourcePackage)
    (Category.comp_id input.hom).symm (hom.1 ≫ cartLift.hom)

/-- Cartesian and cocartesian transposition are inverse in the target fiber. -/
theorem semanticReindexToCoreTransportHom_toReindex
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      targetPackage) :
    semanticReindexToCoreTransportHom input sourcePackage targetPackage
        (semanticCoreTransportToReindexHom input sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      (coreFiberLift input.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.hom sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.hom
    (coreFiberLift input.hom sourcePackage)
    (𝟙 input.target)
  change coreFiberLift input.hom sourcePackage ≫
      (semanticReindexToCoreTransportHom input sourcePackage targetPackage
        (semanticCoreTransportToReindexHom input sourcePackage targetPackage hom)).1 =
    coreFiberLift input.hom sourcePackage ≫ hom.1
  rw [semanticReindexToCoreTransportHom_fac, semanticCoreTransportToReindexHom_fac]

/-- Cartesian and cocartesian transposition are inverse in the source fiber. -/
theorem semanticCoreTransportToReindexHom_toCoreTransport
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target)
    (hom : sourcePackage ⟶
      (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) :
    semanticCoreTransportToReindexHom input sourcePackage targetPackage
        (semanticReindexToCoreTransportHom input sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom cartLift.hom
    (𝟙 input.source)
  change (semanticCoreTransportToReindexHom input sourcePackage targetPackage
      (semanticReindexToCoreTransportHom input sourcePackage targetPackage hom)).1 ≫
      cartLift.hom = hom.1 ≫ cartLift.hom
  rw [semanticCoreTransportToReindexHom_fac, semanticReindexToCoreTransportHom_fac]

/-- The hom-set equivalence for every semantic exact pointed arrow. -/
noncomputable def semanticCoreTransportReindexHomEquiv
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    (targetPackage : CoreFiber input.target) :
    ((coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
        targetPackage) ≃
      (sourcePackage ⟶
        (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) where
  toFun := semanticCoreTransportToReindexHom input sourcePackage targetPackage
  invFun := semanticReindexToCoreTransportHom input sourcePackage targetPackage
  left_inv := semanticReindexToCoreTransportHom_toReindex input sourcePackage targetPackage
  right_inv := semanticCoreTransportToReindexHom_toCoreTransport input sourcePackage targetPackage

/-! ## Naturality of the generated correspondence -/

/-- The inverse transpose is natural in the source-fiber variable. -/
theorem semanticReindexToCoreTransportHom_comp_left
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    {first second : CoreFiber input.source}
    (sourceHom : first ⟶ second)
    (targetPackage : CoreFiber input.target)
    (hom : second ⟶
      (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) :
    semanticReindexToCoreTransportHom input first targetPackage (sourceHom ≫ hom) =
      (coreFiberTransportFunctor input.hom).map sourceHom ≫
        semanticReindexToCoreTransportHom input second targetPackage hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      (coreFiberLift input.hom first) :=
    coreFiberLift_isStronglyCocartesian input.hom first
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.hom
    (coreFiberLift input.hom first)
    (𝟙 input.target)
  change coreFiberLift input.hom first ≫
      (semanticReindexToCoreTransportHom input first targetPackage
        (sourceHom ≫ hom)).1 =
    coreFiberLift input.hom first ≫
      ((coreFiberTransportFunctor input.hom).map sourceHom).1 ≫
      (semanticReindexToCoreTransportHom input second targetPackage hom).1
  rw [semanticReindexToCoreTransportHom_fac]
  change (sourceHom.1 ≫ hom.1) ≫
      (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom =
    coreFiberLift input.hom first ≫
      ((coreFiberTransportFunctor input.hom).map sourceHom).1 ≫
      (semanticReindexToCoreTransportHom input second targetPackage hom).1
  have transportFac :
      coreFiberLift input.hom first ≫
          ((coreFiberTransportFunctor input.hom).map sourceHom).1 =
        sourceHom.1 ≫ coreFiberLift input.hom second := by
    simpa only [coreFiberTransportFunctor] using
      coreFiberTransportMap_fac input.hom sourceHom
  calc
    _ = sourceHom.1 ≫
        (hom.1 ≫ (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom) :=
      Category.assoc _ _ _
    _ = sourceHom.1 ≫
        (coreFiberLift input.hom second ≫
          (semanticReindexToCoreTransportHom input second targetPackage hom).1) := by
      rw [semanticReindexToCoreTransportHom_fac]
    _ = (sourceHom.1 ≫ coreFiberLift input.hom second) ≫
        (semanticReindexToCoreTransportHom input second targetPackage hom).1 :=
      (Category.assoc _ _ _).symm
    _ = (coreFiberLift input.hom first ≫
        ((coreFiberTransportFunctor input.hom).map sourceHom).1) ≫
          (semanticReindexToCoreTransportHom input second targetPackage hom).1 := by
      rw [transportFac]
    _ = _ := Category.assoc _ _ _

/-- The forward transpose is natural in the target-fiber variable. -/
theorem semanticCoreTransportToReindexHom_comp_right
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source)
    {first second : CoreFiber input.target}
    (hom : (coreFiberTransportFunctor input.hom).obj sourcePackage ⟶
      first)
    (targetHom : first ⟶ second) :
    semanticCoreTransportToReindexHom input sourcePackage second (hom ≫ targetHom) =
      semanticCoreTransportToReindexHom input sourcePackage first hom ≫
        (exact_bottom_semantic_global_reindex_functor input.hom).map targetHom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := exact_bottom_semantic_global_selected_lift input.hom second
  letI : (packageProjection U).IsStronglyCartesian input.hom cartLift.hom := by
    simpa only [cartSemanticInputOfHom] using cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom cartLift.hom
    (𝟙 input.source)
  change (semanticCoreTransportToReindexHom input sourcePackage second
      (hom ≫ targetHom)).1 ≫ cartLift.hom =
    ((semanticCoreTransportToReindexHom input sourcePackage first hom).1 ≫
      ((exact_bottom_semantic_global_reindex_functor input.hom).map targetHom).1) ≫ cartLift.hom
  rw [semanticCoreTransportToReindexHom_fac]
  rw [Category.assoc, exact_bottom_semantic_global_reindex_map_fac]
  rw [← Category.assoc, semanticCoreTransportToReindexHom_fac]
  rfl

/-- The natural hom-equivalence package used to construct the adjunction. -/
noncomputable def semanticCoreTransportReindexCoreHomEquiv
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    Adjunction.CoreHomEquiv
      (coreFiberTransportFunctor input.hom)
      (exact_bottom_semantic_global_reindex_functor input.hom) where
  homEquiv := semanticCoreTransportReindexHomEquiv input
  homEquiv_naturality_left_symm := by
    intro first second target sourceHom hom
    exact semanticReindexToCoreTransportHom_comp_left input sourceHom target hom
  homEquiv_naturality_right := by
    intro source first second hom targetHom
    exact semanticCoreTransportToReindexHom_comp_right input source hom targetHom

/-! ## The generated adjunction, unit, counit, and triangles -/

/--
G-109 cocartesian transport is left adjoint to G-112 semantic-global
reindexing over every exact pointed arrow.
-/
noncomputable def semanticCoreTransportReindexAdjunction
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    coreFiberTransportFunctor input.hom ⊣
      exact_bottom_semantic_global_reindex_functor input.hom :=
  Adjunction.mkOfHomEquiv (semanticCoreTransportReindexCoreHomEquiv input)


/-- The generated unit of core transport/reindexing. -/
noncomputable def semanticCoreTransportReindexUnit
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    𝟭 (CoreFiber input.source) ⟶
      coreFiberTransportFunctor input.hom ⋙
        exact_bottom_semantic_global_reindex_functor input.hom :=
  (semanticCoreTransportReindexAdjunction input).unit

/-- The generated counit of core transport/reindexing. -/
noncomputable def semanticCoreTransportReindexCounit
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    exact_bottom_semantic_global_reindex_functor input.hom ⋙
        coreFiberTransportFunctor input.hom ⟶
      𝟭 (CoreFiber input.target) :=
  (semanticCoreTransportReindexAdjunction input).counit

/-- The unit component is the cartesian transpose of the identity. -/
theorem semanticCoreTransportReindexUnit_app
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source) :
    (semanticCoreTransportReindexUnit input).app sourcePackage =
      semanticCoreTransportToReindexHom input sourcePackage
        ((coreFiberTransportFunctor input.hom).obj sourcePackage)
        (𝟙 ((coreFiberTransportFunctor input.hom).obj sourcePackage)) := by
  rfl

/-- The counit component is the cocartesian transpose of the identity. -/
theorem semanticCoreTransportReindexCounit_app
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    (semanticCoreTransportReindexCounit input).app targetPackage =
      semanticReindexToCoreTransportHom input
        ((exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage)
        targetPackage
        (𝟙 ((exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage)) := by
  rfl

/-- The unit component factors the canonical cocartesian lift through the selected lift. -/
theorem semanticCoreTransportReindexUnit_app_fac
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source) :
    ((semanticCoreTransportReindexUnit input).app sourcePackage).1 ≫
        (exact_bottom_semantic_global_selected_lift input.hom
          ((coreFiberTransportFunctor input.hom).obj sourcePackage)).hom =
      coreFiberLift input.hom sourcePackage := by
  rw [semanticCoreTransportReindexUnit_app, semanticCoreTransportToReindexHom_fac]
  change coreFiberLift input.hom sourcePackage ≫ 𝟙 _ =
    coreFiberLift input.hom sourcePackage
  exact Category.comp_id _

/-- The counit component factors the selected cartesian lift through the canonical lift. -/
theorem semanticCoreTransportReindexCounit_app_fac
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    coreFiberLift input.hom
        ((exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage) ≫
      ((semanticCoreTransportReindexCounit input).app targetPackage).1 =
        (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom := by
  rw [semanticCoreTransportReindexCounit_app, semanticReindexToCoreTransportHom_fac]
  change 𝟙 _ ≫ (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom =
    (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom
  exact Category.id_comp _


theorem semanticGlobalSelectedLift_isStronglyCocartesian
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    (packageProjection U).IsStronglyCocartesian input.hom
      (exact_bottom_semantic_global_selected_lift input.hom targetPackage).hom := by
  let explicit := strongCartesianLiftOfTarget input targetPackage
  let selected := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCartesian input.hom
      explicit.hom := explicit.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCartesian input.hom
      selected.hom := selected.isStronglyCartesian
  have base_fac : input.hom =
      (Iso.refl input.source).hom ≫ input.hom := by
    exact Category.id_comp input.hom
  let comparison : selected.domain ≅ explicit.domain :=
    CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso
      (p := packageProjection U)
      (g := Iso.refl input.source)
      (f := input.hom) (f' := input.hom)
      base_fac explicit.hom selected.hom
  have comparison_fac : comparison.hom ≫ explicit.hom = selected.hom := by
    exact CategoryTheory.Functor.IsStronglyCartesian.fac
      (packageProjection U) input.hom explicit.hom base_fac
      selected.hom
  letI : (packageProjection U).IsHomLift
      (𝟙 input.source) comparison.hom := by
    change (packageProjection U).IsHomLift
      (Iso.refl input.source).hom comparison.hom
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 input.source) comparison.hom :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      (packageProjection U) (𝟙 input.source) comparison
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      explicit.hom := strongCartesianLiftOfTarget_isStronglyCocartesian
        input targetPackage
  have composed : (packageProjection U).IsStronglyCocartesian
      ((𝟙 input.source) ≫ input.hom)
      (comparison.hom ≫ explicit.hom) :=
    CategoryTheory.Functor.IsStronglyCocartesian.comp (packageProjection U)
  simpa only [Category.id_comp, comparison_fac] using composed

theorem semanticCoreTransportReindexUnit_app_isIso
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (sourcePackage : CoreFiber input.source) :
    IsIso ((semanticCoreTransportReindexUnit input).app sourcePackage) := by
  let unit := (semanticCoreTransportReindexUnit input).app sourcePackage
  let selectedLift := exact_bottom_semantic_global_selected_lift input.hom
    ((coreFiberTransportFunctor input.hom).obj sourcePackage)
  let canonicalLift := coreFiberLift input.hom sourcePackage
  letI : (packageProjection U).IsStronglyCartesian input.hom
      selectedLift.hom := by
    simpa only [cartSemanticInputOfHom] using selectedLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCartesian input.hom
      canonicalLift := coreFiberLift_isStronglyCartesian_support
        input.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.source) unit.1 := unit.2
  have composed : (packageProjection U).IsStronglyCartesian
      ((𝟙 input.source) ≫ input.hom)
      (unit.1 ≫ selectedLift.hom) := by
    rw [Category.id_comp, semanticCoreTransportReindexUnit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCartesian
      ((𝟙 input.source) ≫ input.hom)
      (unit.1 ≫ selectedLift.hom) := composed
  letI : (packageProjection U).IsStronglyCartesian
      (𝟙 input.source) unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := packageProjection U)
      (f := 𝟙 input.source) (g := input.hom)
      (φ := unit.1) (ψ := selectedLift.hom)
  letI : IsIso unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 input.source) unit.1
  exact coreFiberHom_isIso_of_total_isIso unit

/-- Every generated counit component is invertible from cocartesian uniqueness. -/
theorem semanticCoreTransportReindexCounit_app_isIso
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U)
    (targetPackage : CoreFiber input.target) :
    IsIso ((semanticCoreTransportReindexCounit input).app targetPackage) := by
  let counit := (semanticCoreTransportReindexCounit input).app targetPackage
  let sourcePackage :=
    (exact_bottom_semantic_global_reindex_functor input.hom).obj targetPackage
  let canonicalLift := coreFiberLift input.hom sourcePackage
  let selectedLift := exact_bottom_semantic_global_selected_lift input.hom targetPackage
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      canonicalLift := coreFiberLift_isStronglyCocartesian
        input.hom sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian input.hom
      selectedLift.hom :=
    semanticGlobalSelectedLift_isStronglyCocartesian input targetPackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) counit.1 := counit.2
  have composed : (packageProjection U).IsStronglyCocartesian
      (input.hom ≫ 𝟙 input.target)
      (canonicalLift ≫ counit.1) := by
    rw [Category.comp_id, semanticCoreTransportReindexCounit_app_fac]
    infer_instance
  letI : (packageProjection U).IsStronglyCocartesian
      (input.hom ≫ 𝟙 input.target)
      (canonicalLift ≫ counit.1) := composed
  letI : (packageProjection U).IsStronglyCocartesian
      (𝟙 input.target) counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_comp
      (p := packageProjection U)
      (f := input.hom) (g := 𝟙 input.target)
      (φ := canonicalLift) (ψ := counit.1)
  letI : IsIso counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (packageProjection U) (𝟙 input.target) counit.1
  exact coreFiberHom_isIso_of_total_isIso counit

/-- The generated unit natural transformation is an isomorphism. -/
theorem semanticCoreTransportReindexUnit_isIso
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) : IsIso (semanticCoreTransportReindexUnit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact semanticCoreTransportReindexUnit_app_isIso input

/-- The generated counit natural transformation is an isomorphism. -/
theorem semanticCoreTransportReindexCounit_isIso
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) : IsIso (semanticCoreTransportReindexCounit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact semanticCoreTransportReindexCounit_app_isIso input


/-- The left triangle identity of the generated adjunction. -/
theorem semanticCoreTransportReindex_left_triangle
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    Functor.whiskerRight (semanticCoreTransportReindexUnit input)
        (coreFiberTransportFunctor input.hom) ≫
      (Functor.associator
        (coreFiberTransportFunctor input.hom)
        (exact_bottom_semantic_global_reindex_functor input.hom)
        (coreFiberTransportFunctor input.hom)).hom ≫
      Functor.whiskerLeft (coreFiberTransportFunctor input.hom)
        (semanticCoreTransportReindexCounit input) =
      NatTrans.id
        (𝟭 (CoreFiber input.source) ⋙
          coreFiberTransportFunctor input.hom) :=
  (semanticCoreTransportReindexAdjunction input).left_triangle

/-- The right triangle identity of the generated adjunction. -/
theorem semanticCoreTransportReindex_right_triangle
    {U : AtomCarrier.{u}}
    (input : CartSemanticInput U) :
    Functor.whiskerLeft (exact_bottom_semantic_global_reindex_functor input.hom)
        (semanticCoreTransportReindexUnit input) ≫
      (Functor.associator
        (exact_bottom_semantic_global_reindex_functor input.hom)
        (coreFiberTransportFunctor input.hom)
        (exact_bottom_semantic_global_reindex_functor input.hom)).inv ≫
      Functor.whiskerRight (semanticCoreTransportReindexCounit input)
        (exact_bottom_semantic_global_reindex_functor input.hom) =
      NatTrans.id
        (exact_bottom_semantic_global_reindex_functor input.hom ⋙
          𝟭 (CoreFiber input.source)) :=
  (semanticCoreTransportReindexAdjunction input).right_triangle


end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
