import ResearchLean.AG.DoctrineFiberProduct.CoreTransportReindexAdjunction
import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCleavage

/-!
# Cleavage independence of the core transport/reindexing adjunction

Cycle 35 constructs the adjunction to the fixed selected reindexing functor.
This module compares every cartesian cleavage to that selected functor, transports
the adjunction along the generated natural isomorphism, and proves that the
canonical Cycle 33 comparison intertwines the resulting hom correspondence,
unit, and counit.  An arbitrary cleavage is only a universally quantified lift
family; no adjunction or compatibility certificate is accepted from a caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 3000000

/-! ## Generated bridge from an arbitrary cleavage to the selected functor -/

/-- The canonical component from one cleavage-derived object to the selected object. -/
noncomputable def coreFiberCleavageSelectedComparisonApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    cleavage.reindexFunctor.obj targetPackage ≅
      (selectedCoreFiberReindexFunctor input).obj targetPackage where
  hom := ⟨(StrongCartesianLift.domainIso
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)).hom,
    StrongCartesianLift.domainIso_hom_isHomLift
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)⟩
  inv := ⟨(StrongCartesianLift.domainIso
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)).inv,
    StrongCartesianLift.domainIso_inv_isHomLift
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)⟩
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (selectedCoreFiberCartesianLift input targetPackage)
      (cleavage.lift targetPackage)).inv_hom_id

/-- The forward bridge followed by the selected lift is the cleavage lift. -/
theorem coreFiberCleavageSelectedComparisonApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreFiberCleavageSelectedComparisonApp input cleavage targetPackage).hom.1 ≫
        (selectedCoreFiberCartesianLift input targetPackage).hom =
      (cleavage.lift targetPackage).hom :=
  StrongCartesianLift.domainIso_hom_fac
    (selectedCoreFiberCartesianLift input targetPackage)
    (cleavage.lift targetPackage)

/-- The inverse bridge followed by the cleavage lift is the selected lift. -/
theorem coreFiberCleavageSelectedComparisonApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreFiberCleavageSelectedComparisonApp input cleavage targetPackage).inv.1 ≫
        (cleavage.lift targetPackage).hom =
      (selectedCoreFiberCartesianLift input targetPackage).hom :=
  StrongCartesianLift.domainIso_inv_fac
    (selectedCoreFiberCartesianLift input targetPackage)
    (cleavage.lift targetPackage)

/-- The bridge is natural on every vertical target-fiber map. -/
theorem coreFiberCleavageSelectedComparison_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    {sourcePackage targetPackage : CoreFiber input.semantic.target}
    (hom : sourcePackage ⟶ targetPackage) :
    cleavage.reindexFunctor.map hom ≫
        (coreFiberCleavageSelectedComparisonApp input cleavage
          targetPackage).hom =
      (coreFiberCleavageSelectedComparisonApp input cleavage
        sourcePackage).hom ≫
        (selectedCoreFiberReindexFunctor input).map hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let selectedTarget := selectedCoreFiberCartesianLift input targetPackage
  letI := selectedTarget.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom selectedTarget.hom
    (𝟙 input.semantic.source)
  change (cleavage.reindexFunctor.map hom).1 ≫
      (coreFiberCleavageSelectedComparisonApp input cleavage
        targetPackage).hom.1 ≫ selectedTarget.hom =
    (coreFiberCleavageSelectedComparisonApp input cleavage
      sourcePackage).hom.1 ≫
      ((selectedCoreFiberReindexFunctor input).map hom).1 ≫ selectedTarget.hom
  calc
    _ = (cleavage.reindexFunctor.map hom).1 ≫
        ((coreFiberCleavageSelectedComparisonApp input cleavage
          targetPackage).hom.1 ≫ selectedTarget.hom) := Category.assoc _ _ _
    _ = (cleavage.reindexFunctor.map hom).1 ≫
        (cleavage.lift targetPackage).hom := by
      rw [coreFiberCleavageSelectedComparisonApp_hom_fac]
    _ = (cleavage.lift sourcePackage).hom ≫ hom.1 :=
      cleavage.reindexFunctor_map_fac hom
    _ = ((coreFiberCleavageSelectedComparisonApp input cleavage
        sourcePackage).hom.1 ≫
          (selectedCoreFiberCartesianLift input sourcePackage).hom) ≫ hom.1 := by
      rw [coreFiberCleavageSelectedComparisonApp_hom_fac]
    _ = (coreFiberCleavageSelectedComparisonApp input cleavage
        sourcePackage).hom.1 ≫
          ((selectedCoreFiberCartesianLift input sourcePackage).hom ≫ hom.1) :=
      Category.assoc _ _ _
    _ = (coreFiberCleavageSelectedComparisonApp input cleavage
        sourcePackage).hom.1 ≫
          (((selectedCoreFiberReindexFunctor input).map hom).1 ≫
            selectedTarget.hom) := by
      rw [selectedCoreFiberReindexFunctor_map_fac]
    _ = _ := (Category.assoc _ _ _).symm

/-- The generated natural isomorphism from an arbitrary cleavage to the selected functor. -/
noncomputable def coreFiberCleavageSelectedComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    cleavage.reindexFunctor ≅ selectedCoreFiberReindexFunctor input :=
  NatIso.ofComponents (coreFiberCleavageSelectedComparisonApp input cleavage)
    (fun hom => coreFiberCleavageSelectedComparison_naturality
      input cleavage hom)

/-! ## Compatibility with the canonical comparison between two cleavages -/

/-- Passing through the canonical comparison gives the direct selected bridge. -/
theorem coreFiberCleavageComparison_selected_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (CoreFiberCartesianCleavage.comparisonApp first second targetPackage).hom ≫
        (coreFiberCleavageSelectedComparisonApp input second targetPackage).hom =
      (coreFiberCleavageSelectedComparisonApp input first targetPackage).hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let selectedLift := selectedCoreFiberCartesianLift input targetPackage
  letI := selectedLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom selectedLift.hom
    (𝟙 input.semantic.source)
  change ((CoreFiberCartesianCleavage.comparisonApp first second
      targetPackage).hom.1 ≫
        (coreFiberCleavageSelectedComparisonApp input second
          targetPackage).hom.1) ≫ selectedLift.hom =
    (coreFiberCleavageSelectedComparisonApp input first targetPackage).hom.1 ≫
      selectedLift.hom
  rw [Category.assoc, coreFiberCleavageSelectedComparisonApp_hom_fac,
    CoreFiberCartesianCleavage.comparisonApp_hom_fac,
    coreFiberCleavageSelectedComparisonApp_hom_fac]

/-- The inverse selected bridge commutes with the canonical forward comparison. -/
theorem coreFiberCleavageComparison_selected_inv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreFiberCleavageSelectedComparisonApp input first targetPackage).inv ≫
        (CoreFiberCartesianCleavage.comparisonApp first second
          targetPackage).hom =
      (coreFiberCleavageSelectedComparisonApp input second targetPackage).inv := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let secondLift := second.lift targetPackage
  letI := secondLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom secondLift.hom
    (𝟙 input.semantic.source)
  change ((coreFiberCleavageSelectedComparisonApp input first
      targetPackage).inv.1 ≫
        (CoreFiberCartesianCleavage.comparisonApp first second
          targetPackage).hom.1) ≫ secondLift.hom =
    (coreFiberCleavageSelectedComparisonApp input second targetPackage).inv.1 ≫
      secondLift.hom
  rw [Category.assoc, CoreFiberCartesianCleavage.comparisonApp_hom_fac,
    coreFiberCleavageSelectedComparisonApp_inv_fac,
    coreFiberCleavageSelectedComparisonApp_inv_fac]

/-! ## The arbitrary-cleavage adjunction -/

/-- Transport the Cycle 35 selected adjunction to an arbitrary cleavage. -/
noncomputable def coreTransportCleavageAdjunction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    coreFiberTransportFunctor input.semantic.hom ⊣ cleavage.reindexFunctor :=
  (coreTransportReindexAdjunction input).ofNatIsoRight
    (coreFiberCleavageSelectedComparison input cleavage).symm

/-- The generated arbitrary-cleavage hom equivalence is the selected transpose followed by the inverse bridge. -/
theorem coreTransportCleavageAdjunction_homEquiv_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage) :
    (coreTransportCleavageAdjunction input cleavage).homEquiv
        sourcePackage targetPackage hom =
      coreTransportToReindexHom input sourcePackage targetPackage hom ≫
        (coreFiberCleavageSelectedComparisonApp input cleavage
          targetPackage).inv := by
  unfold coreTransportCleavageAdjunction Adjunction.ofNatIsoRight
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rw [Equiv.trans_apply, Adjunction.equivHomsetRightOfNatIso_apply]
  change (coreTransportReindexAdjunction input).homEquiv
      sourcePackage targetPackage hom ≫
    (coreFiberCleavageSelectedComparisonApp input cleavage targetPackage).inv = _
  rw [show (coreTransportReindexAdjunction input).homEquiv
      sourcePackage targetPackage hom =
      coreTransportToReindexHom input sourcePackage targetPackage hom by
    change (Adjunction.mkOfHomEquiv
      (coreTransportReindexCoreHomEquiv input)).homEquiv
        sourcePackage targetPackage hom = _
    rw [Adjunction.mkOfHomEquiv_homEquiv]
    rfl]

/-- The inverse hom equivalence crosses the forward bridge before the selected inverse transpose. -/
theorem coreTransportCleavageAdjunction_homEquiv_symm_apply
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : sourcePackage ⟶ cleavage.reindexFunctor.obj targetPackage) :
    ((coreTransportCleavageAdjunction input cleavage).homEquiv
        sourcePackage targetPackage).symm hom =
      reindexToCoreTransportHom input sourcePackage targetPackage
        (hom ≫ (coreFiberCleavageSelectedComparisonApp input cleavage
          targetPackage).hom) := by
  apply ((coreTransportCleavageAdjunction input cleavage).homEquiv
    sourcePackage targetPackage).injective
  rw [Equiv.apply_symm_apply]
  rw [coreTransportCleavageAdjunction_homEquiv_apply]
  rw [coreTransportToReindexHom_toCoreTransport]
  simp

/-- Unit generated for one arbitrary cleavage. -/
noncomputable def coreTransportCleavageUnit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    𝟭 (CoreFiber input.semantic.source) ⟶
      coreFiberTransportFunctor input.semantic.hom ⋙ cleavage.reindexFunctor :=
  (coreTransportCleavageAdjunction input cleavage).unit

/-- Counit generated for one arbitrary cleavage. -/
noncomputable def coreTransportCleavageCounit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    cleavage.reindexFunctor ⋙ coreFiberTransportFunctor input.semantic.hom ⟶
      𝟭 (CoreFiber input.semantic.target) :=
  (coreTransportCleavageAdjunction input cleavage).counit

/-- The arbitrary unit is the selected unit followed by the inverse bridge. -/
theorem coreTransportCleavageUnit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source) :
    (coreTransportCleavageUnit input cleavage).app sourcePackage =
      (coreTransportReindexUnit input).app sourcePackage ≫
        (coreFiberCleavageSelectedComparisonApp input cleavage
          ((coreFiberTransportFunctor input.semantic.hom).obj
            sourcePackage)).inv := by
  have h := coreTransportCleavageAdjunction_homEquiv_apply input cleavage
    sourcePackage
    ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage)
    (𝟙 ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage))
  rw [Adjunction.homEquiv_unit] at h
  rw [cleavage.reindexFunctor.map_id] at h
  rw [coreTransportReindexUnit_app]
  simpa only [coreTransportCleavageUnit, Category.comp_id] using h

/-- The arbitrary counit first crosses the forward bridge and then uses the selected counit. -/
theorem coreTransportCleavageCounit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreTransportCleavageCounit input cleavage).app targetPackage =
      (coreFiberTransportFunctor input.semantic.hom).map
          (coreFiberCleavageSelectedComparisonApp input cleavage
            targetPackage).hom ≫
        (coreTransportReindexCounit input).app targetPackage := by
  rfl

/-- Left triangle for the arbitrary-cleavage adjunction. -/
theorem coreTransportCleavage_left_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    Functor.whiskerRight (coreTransportCleavageUnit input cleavage)
        (coreFiberTransportFunctor input.semantic.hom) ≫
      (Functor.associator (coreFiberTransportFunctor input.semantic.hom)
        cleavage.reindexFunctor
        (coreFiberTransportFunctor input.semantic.hom)).hom ≫
      Functor.whiskerLeft (coreFiberTransportFunctor input.semantic.hom)
        (coreTransportCleavageCounit input cleavage) =
      NatTrans.id (𝟭 (CoreFiber input.semantic.source) ⋙
        coreFiberTransportFunctor input.semantic.hom) :=
  (coreTransportCleavageAdjunction input cleavage).left_triangle

/-- Right triangle for the arbitrary-cleavage adjunction. -/
theorem coreTransportCleavage_right_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (cleavage : CoreFiberCartesianCleavage input.semantic) :
    Functor.whiskerLeft cleavage.reindexFunctor
        (coreTransportCleavageUnit input cleavage) ≫
      (Functor.associator cleavage.reindexFunctor
        (coreFiberTransportFunctor input.semantic.hom)
        cleavage.reindexFunctor).inv ≫
      Functor.whiskerRight (coreTransportCleavageCounit input cleavage)
        cleavage.reindexFunctor =
      NatTrans.id (cleavage.reindexFunctor ⋙
        𝟭 (CoreFiber input.semantic.source)) :=
  (coreTransportCleavageAdjunction input cleavage).right_triangle

/-! ## Independence of hom equivalence, unit, and counit -/

/-- The canonical Cycle 33 comparison intertwines the two generated hom equivalences. -/
theorem coreTransportCleavageHomEquiv_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage) :
    (coreTransportCleavageAdjunction input first).homEquiv
        sourcePackage targetPackage hom ≫
      (CoreFiberCartesianCleavage.comparisonApp first second
        targetPackage).hom =
    (coreTransportCleavageAdjunction input second).homEquiv
      sourcePackage targetPackage hom := by
  rw [coreTransportCleavageAdjunction_homEquiv_apply,
    coreTransportCleavageAdjunction_homEquiv_apply]
  rw [Category.assoc, coreFiberCleavageComparison_selected_inv]

/-- The inverse hom equivalences commute with the same canonical comparison. -/
theorem coreTransportCleavageHomEquiv_symm_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : sourcePackage ⟶ first.reindexFunctor.obj targetPackage) :
    ((coreTransportCleavageAdjunction input second).homEquiv
      sourcePackage targetPackage).symm
        (hom ≫ (CoreFiberCartesianCleavage.comparisonApp first second
          targetPackage).hom) =
    ((coreTransportCleavageAdjunction input first).homEquiv
      sourcePackage targetPackage).symm hom := by
  rw [coreTransportCleavageAdjunction_homEquiv_symm_apply,
    coreTransportCleavageAdjunction_homEquiv_symm_apply]
  rw [Category.assoc, coreFiberCleavageComparison_selected_hom]

/-- The canonical comparison intertwines the two generated units. -/
theorem coreTransportCleavageUnit_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (sourcePackage : CoreFiber input.semantic.source) :
    (coreTransportCleavageUnit input first).app sourcePackage ≫
        (CoreFiberCartesianCleavage.comparisonApp first second
          ((coreFiberTransportFunctor input.semantic.hom).obj
            sourcePackage)).hom =
      (coreTransportCleavageUnit input second).app sourcePackage := by
  rw [coreTransportCleavageUnit_app, coreTransportCleavageUnit_app]
  rw [Category.assoc, coreFiberCleavageComparison_selected_inv]

/-- The canonical comparison intertwines the two generated counits. -/
theorem coreTransportCleavageCounit_comparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (first second : CoreFiberCartesianCleavage input.semantic)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreFiberTransportFunctor input.semantic.hom).map
        (CoreFiberCartesianCleavage.comparisonApp first second
          targetPackage).hom ≫
      (coreTransportCleavageCounit input second).app targetPackage =
    (coreTransportCleavageCounit input first).app targetPackage := by
  rw [coreTransportCleavageCounit_app, coreTransportCleavageCounit_app]
  rw [← Category.assoc, ← Functor.map_comp]
  rw [coreFiberCleavageComparison_selected_hom]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
