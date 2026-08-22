import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingPresentationReplacement
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Core transport/reindexing adjunction

For one realized finite-code base arrow, the reviewed G-109 cocartesian
transport and the G-110 selected cartesian reindexing form an adjoint pair.
The hom correspondence is generated twice from the universal properties: its
forward direction factors the cocartesian lift through the selected cartesian
lift, and its inverse factors the selected cartesian lift through the canonical
cocartesian lift.  No hom equivalence, unit, counit, or triangle certificate is
accepted from a caller.
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
noncomputable def coreTransportToReindexHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage) :
    sourcePackage ⟶ (selectedCoreFiberReindexFunctor input).obj targetPackage := by
  let cartLift := selectedCoreFiberCartesianLift input targetPackage
  letI := cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage) :=
    coreFiberLift_isHomLift input.semantic.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.semantic.hom ≫ 𝟙 input.semantic.target)
        (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1))
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (packageProjection U) input.semantic.hom cartLift.hom
      (g := 𝟙 input.semantic.source) (f' := input.semantic.hom)
      (Category.id_comp input.semantic.hom).symm
      (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1), inferInstance⟩

/-- Defining cartesian factor graph of `coreTransportToReindexHom`. -/
theorem coreTransportToReindexHom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage) :
    (coreTransportToReindexHom input sourcePackage targetPackage hom).1 ≫
        (selectedCoreFiberCartesianLift input targetPackage).hom =
      coreFiberLift input.semantic.hom sourcePackage ≫ hom.1 := by
  let cartLift := selectedCoreFiberCartesianLift input targetPackage
  letI := cartLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage) :=
    coreFiberLift_isHomLift input.semantic.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.semantic.hom ≫ 𝟙 input.semantic.target)
        (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (packageProjection U) input.semantic.hom cartLift.hom
    (Category.id_comp input.semantic.hom).symm
    (coreFiberLift input.semantic.hom sourcePackage ≫ hom.1)

/--
Send a vertical map into selected reindexing to its cocartesian transpose.
The result is the unique vertical factor out of the canonical G-109 lift.
-/
noncomputable def reindexToCoreTransportHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : sourcePackage ⟶
      (selectedCoreFiberReindexFunctor input).obj targetPackage) :
    (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage := by
  let cartLift := selectedCoreFiberCartesianLift input targetPackage
  letI := cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.semantic.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 input.semantic.source) ≫ input.semantic.hom)
        (hom.1 ≫ cartLift.hom))
  exact ⟨CategoryTheory.Functor.IsStronglyCocartesian.map
      (packageProjection U) input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage)
      (g := 𝟙 input.semantic.target) (f' := input.semantic.hom)
      (Category.comp_id input.semantic.hom).symm
      (hom.1 ≫ cartLift.hom), inferInstance⟩

/-- Defining cocartesian factor graph of `reindexToCoreTransportHom`. -/
theorem reindexToCoreTransportHom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : sourcePackage ⟶
      (selectedCoreFiberReindexFunctor input).obj targetPackage) :
    coreFiberLift input.semantic.hom sourcePackage ≫
        (reindexToCoreTransportHom input sourcePackage targetPackage hom).1 =
      hom.1 ≫ (selectedCoreFiberCartesianLift input targetPackage).hom := by
  let cartLift := selectedCoreFiberCartesianLift input targetPackage
  letI := cartLift.isStronglyCartesian
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.semantic.hom sourcePackage
  letI : (packageProjection U).IsHomLift
      (𝟙 input.semantic.source) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.semantic.hom
      (hom.1 ≫ cartLift.hom) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        ((𝟙 input.semantic.source) ≫ input.semantic.hom)
        (hom.1 ≫ cartLift.hom))
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    (packageProjection U) input.semantic.hom
    (coreFiberLift input.semantic.hom sourcePackage)
    (Category.comp_id input.semantic.hom).symm (hom.1 ≫ cartLift.hom)

/-- Cartesian and cocartesian transposition are inverse in the target fiber. -/
theorem reindexToCoreTransportHom_toReindex
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      targetPackage) :
    reindexToCoreTransportHom input sourcePackage targetPackage
        (coreTransportToReindexHom input sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      (coreFiberLift input.semantic.hom sourcePackage) :=
    coreFiberLift_isStronglyCocartesian input.semantic.hom sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.semantic.hom
    (coreFiberLift input.semantic.hom sourcePackage)
    (𝟙 input.semantic.target)
  change coreFiberLift input.semantic.hom sourcePackage ≫
      (reindexToCoreTransportHom input sourcePackage targetPackage
        (coreTransportToReindexHom input sourcePackage targetPackage hom)).1 =
    coreFiberLift input.semantic.hom sourcePackage ≫ hom.1
  rw [reindexToCoreTransportHom_fac, coreTransportToReindexHom_fac]

/-- Cartesian and cocartesian transposition are inverse in the source fiber. -/
theorem coreTransportToReindexHom_toCoreTransport
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : sourcePackage ⟶
      (selectedCoreFiberReindexFunctor input).obj targetPackage) :
    coreTransportToReindexHom input sourcePackage targetPackage
        (reindexToCoreTransportHom input sourcePackage targetPackage hom) = hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := selectedCoreFiberCartesianLift input targetPackage
  letI := cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom cartLift.hom
    (𝟙 input.semantic.source)
  change (coreTransportToReindexHom input sourcePackage targetPackage
      (reindexToCoreTransportHom input sourcePackage targetPackage hom)).1 ≫
      cartLift.hom = hom.1 ≫ cartLift.hom
  rw [coreTransportToReindexHom_fac, reindexToCoreTransportHom_fac]

/-- The producer-derived hom-set equivalence for one realized base arrow. -/
noncomputable def coreTransportReindexHomEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    (targetPackage : CoreFiber input.semantic.target) :
    ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
        targetPackage) ≃
      (sourcePackage ⟶
        (selectedCoreFiberReindexFunctor input).obj targetPackage) where
  toFun := coreTransportToReindexHom input sourcePackage targetPackage
  invFun := reindexToCoreTransportHom input sourcePackage targetPackage
  left_inv := reindexToCoreTransportHom_toReindex input sourcePackage targetPackage
  right_inv := coreTransportToReindexHom_toCoreTransport input sourcePackage targetPackage

/-! ## Naturality of the generated correspondence -/

/-- The inverse transpose is natural in the source-fiber variable. -/
theorem reindexToCoreTransportHom_comp_left
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    {first second : CoreFiber input.semantic.source}
    (sourceHom : first ⟶ second)
    (targetPackage : CoreFiber input.semantic.target)
    (hom : second ⟶
      (selectedCoreFiberReindexFunctor input).obj targetPackage) :
    reindexToCoreTransportHom input first targetPackage (sourceHom ≫ hom) =
      (coreFiberTransportFunctor input.semantic.hom).map sourceHom ≫
        reindexToCoreTransportHom input second targetPackage hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian input.semantic.hom
      (coreFiberLift input.semantic.hom first) :=
    coreFiberLift_isStronglyCocartesian input.semantic.hom first
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) input.semantic.hom
    (coreFiberLift input.semantic.hom first)
    (𝟙 input.semantic.target)
  change coreFiberLift input.semantic.hom first ≫
      (reindexToCoreTransportHom input first targetPackage
        (sourceHom ≫ hom)).1 =
    coreFiberLift input.semantic.hom first ≫
      ((coreFiberTransportFunctor input.semantic.hom).map sourceHom).1 ≫
      (reindexToCoreTransportHom input second targetPackage hom).1
  rw [reindexToCoreTransportHom_fac]
  change (sourceHom.1 ≫ hom.1) ≫
      (selectedCoreFiberCartesianLift input targetPackage).hom =
    coreFiberLift input.semantic.hom first ≫
      ((coreFiberTransportFunctor input.semantic.hom).map sourceHom).1 ≫
      (reindexToCoreTransportHom input second targetPackage hom).1
  have transportFac :
      coreFiberLift input.semantic.hom first ≫
          ((coreFiberTransportFunctor input.semantic.hom).map sourceHom).1 =
        sourceHom.1 ≫ coreFiberLift input.semantic.hom second := by
    simpa only [coreFiberTransportFunctor] using
      coreFiberTransportMap_fac input.semantic.hom sourceHom
  calc
    _ = sourceHom.1 ≫
        (hom.1 ≫ (selectedCoreFiberCartesianLift input targetPackage).hom) :=
      Category.assoc _ _ _
    _ = sourceHom.1 ≫
        (coreFiberLift input.semantic.hom second ≫
          (reindexToCoreTransportHom input second targetPackage hom).1) := by
      rw [reindexToCoreTransportHom_fac]
    _ = (sourceHom.1 ≫ coreFiberLift input.semantic.hom second) ≫
        (reindexToCoreTransportHom input second targetPackage hom).1 :=
      (Category.assoc _ _ _).symm
    _ = (coreFiberLift input.semantic.hom first ≫
        ((coreFiberTransportFunctor input.semantic.hom).map sourceHom).1) ≫
          (reindexToCoreTransportHom input second targetPackage hom).1 := by
      rw [transportFac]
    _ = _ := Category.assoc _ _ _

/-- The forward transpose is natural in the target-fiber variable. -/
theorem coreTransportToReindexHom_comp_right
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source)
    {first second : CoreFiber input.semantic.target}
    (hom : (coreFiberTransportFunctor input.semantic.hom).obj sourcePackage ⟶
      first)
    (targetHom : first ⟶ second) :
    coreTransportToReindexHom input sourcePackage second (hom ≫ targetHom) =
      coreTransportToReindexHom input sourcePackage first hom ≫
        (selectedCoreFiberReindexFunctor input).map targetHom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := selectedCoreFiberCartesianLift input second
  letI := cartLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.semantic.hom cartLift.hom
    (𝟙 input.semantic.source)
  change (coreTransportToReindexHom input sourcePackage second
      (hom ≫ targetHom)).1 ≫ cartLift.hom =
    ((coreTransportToReindexHom input sourcePackage first hom).1 ≫
      ((selectedCoreFiberReindexFunctor input).map targetHom).1) ≫ cartLift.hom
  rw [coreTransportToReindexHom_fac]
  rw [Category.assoc, selectedCoreFiberReindexFunctor_map_fac]
  rw [← Category.assoc, coreTransportToReindexHom_fac]
  rfl

/-- The natural hom-equivalence package used to construct the adjunction. -/
noncomputable def coreTransportReindexCoreHomEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    Adjunction.CoreHomEquiv
      (coreFiberTransportFunctor input.semantic.hom)
      (selectedCoreFiberReindexFunctor input) where
  homEquiv := coreTransportReindexHomEquiv input
  homEquiv_naturality_left_symm := by
    intro first second target sourceHom hom
    exact reindexToCoreTransportHom_comp_left input sourceHom target hom
  homEquiv_naturality_right := by
    intro source first second hom targetHom
    exact coreTransportToReindexHom_comp_right input source hom targetHom

/-! ## The generated adjunction, unit, counit, and triangles -/

/--
G-109 cocartesian transport is left adjoint to G-110 selected cartesian
reindexing over every realized finite-code base arrow.
-/
noncomputable def coreTransportReindexAdjunction
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    coreFiberTransportFunctor input.semantic.hom ⊣
      selectedCoreFiberReindexFunctor input :=
  Adjunction.mkOfHomEquiv (coreTransportReindexCoreHomEquiv input)

/-- The generated unit of core transport/reindexing. -/
noncomputable def coreTransportReindexUnit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    𝟭 (CoreFiber input.semantic.source) ⟶
      coreFiberTransportFunctor input.semantic.hom ⋙
        selectedCoreFiberReindexFunctor input :=
  (coreTransportReindexAdjunction input).unit

/-- The generated counit of core transport/reindexing. -/
noncomputable def coreTransportReindexCounit
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    selectedCoreFiberReindexFunctor input ⋙
        coreFiberTransportFunctor input.semantic.hom ⟶
      𝟭 (CoreFiber input.semantic.target) :=
  (coreTransportReindexAdjunction input).counit

/-- The unit component is the cartesian transpose of the identity. -/
theorem coreTransportReindexUnit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source) :
    (coreTransportReindexUnit input).app sourcePackage =
      coreTransportToReindexHom input sourcePackage
        ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage)
        (𝟙 ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage)) := by
  rfl

/-- The counit component is the cocartesian transpose of the identity. -/
theorem coreTransportReindexCounit_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    (coreTransportReindexCounit input).app targetPackage =
      reindexToCoreTransportHom input
        ((selectedCoreFiberReindexFunctor input).obj targetPackage)
        targetPackage
        (𝟙 ((selectedCoreFiberReindexFunctor input).obj targetPackage)) := by
  rfl

/-- The unit component factors the canonical cocartesian lift through the selected lift. -/
theorem coreTransportReindexUnit_app_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (sourcePackage : CoreFiber input.semantic.source) :
    ((coreTransportReindexUnit input).app sourcePackage).1 ≫
        (selectedCoreFiberCartesianLift input
          ((coreFiberTransportFunctor input.semantic.hom).obj sourcePackage)).hom =
      coreFiberLift input.semantic.hom sourcePackage := by
  rw [coreTransportReindexUnit_app, coreTransportToReindexHom_fac]
  change coreFiberLift input.semantic.hom sourcePackage ≫ 𝟙 _ =
    coreFiberLift input.semantic.hom sourcePackage
  exact Category.comp_id _

/-- The counit component factors the selected cartesian lift through the canonical lift. -/
theorem coreTransportReindexCounit_app_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    coreFiberLift input.semantic.hom
        ((selectedCoreFiberReindexFunctor input).obj targetPackage) ≫
      ((coreTransportReindexCounit input).app targetPackage).1 =
        (selectedCoreFiberCartesianLift input targetPackage).hom := by
  rw [coreTransportReindexCounit_app, reindexToCoreTransportHom_fac]
  change 𝟙 _ ≫ (selectedCoreFiberCartesianLift input targetPackage).hom =
    (selectedCoreFiberCartesianLift input targetPackage).hom
  exact Category.id_comp _

/-- Naturality of the generated unit. -/
theorem coreTransportReindexUnit_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    {first second : CoreFiber input.semantic.source}
    (hom : first ⟶ second) :
    (𝟭 (CoreFiber input.semantic.source)).map hom ≫
        (coreTransportReindexUnit input).app second =
      (coreTransportReindexUnit input).app first ≫
        (coreFiberTransportFunctor input.semantic.hom ⋙
          selectedCoreFiberReindexFunctor input).map hom :=
  (coreTransportReindexUnit input).naturality hom

/-- Naturality of the generated counit. -/
theorem coreTransportReindexCounit_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    {first second : CoreFiber input.semantic.target}
    (hom : first ⟶ second) :
    (selectedCoreFiberReindexFunctor input ⋙
        coreFiberTransportFunctor input.semantic.hom).map hom ≫
        (coreTransportReindexCounit input).app second =
      (coreTransportReindexCounit input).app first ≫
        (𝟭 (CoreFiber input.semantic.target)).map hom :=
  (coreTransportReindexCounit input).naturality hom

/-- The left triangle identity of the generated adjunction. -/
theorem coreTransportReindex_left_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    Functor.whiskerRight (coreTransportReindexUnit input)
        (coreFiberTransportFunctor input.semantic.hom) ≫
      (Functor.associator
        (coreFiberTransportFunctor input.semantic.hom)
        (selectedCoreFiberReindexFunctor input)
        (coreFiberTransportFunctor input.semantic.hom)).hom ≫
      Functor.whiskerLeft (coreFiberTransportFunctor input.semantic.hom)
        (coreTransportReindexCounit input) =
      NatTrans.id
        (𝟭 (CoreFiber input.semantic.source) ⋙
          coreFiberTransportFunctor input.semantic.hom) :=
  (coreTransportReindexAdjunction input).left_triangle

/-- The right triangle identity of the generated adjunction. -/
theorem coreTransportReindex_right_triangle
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    Functor.whiskerLeft (selectedCoreFiberReindexFunctor input)
        (coreTransportReindexUnit input) ≫
      (Functor.associator
        (selectedCoreFiberReindexFunctor input)
        (coreFiberTransportFunctor input.semantic.hom)
        (selectedCoreFiberReindexFunctor input)).inv ≫
      Functor.whiskerRight (coreTransportReindexCounit input)
        (selectedCoreFiberReindexFunctor input) =
      NatTrans.id
        (selectedCoreFiberReindexFunctor input ⋙
          𝟭 (CoreFiber input.semantic.source)) :=
  (coreTransportReindexAdjunction input).right_triangle

/-! ## Exact-endpoint presentation replacement compatibility -/

/--
The canonical G-109 transport comparison for two exact-endpoint presentations
with equal decoded semantic arrows.  Only the strong-cocartesianness proposition
of the second lift is retagged; neither transport functor is cast wholesale.
-/
noncomputable def typedCoreFiberTransportPresentationComparisonApp
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic) :
    (coreFiberTransportFunctor
        (typedPresentationToSemantic first)).obj sourcePackage ≅
      (coreFiberTransportFunctor
        (typedPresentationToSemantic second)).obj sourcePackage := by
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first) sourcePackage) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first) sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic second) sourcePackage) := by
    rw [semantic_eq]
    exact coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic second) sourcePackage
  exact strongLiftComparisonIso (packageProjection U)
    (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic first) sourcePackage)
    (coreFiberLift (typedPresentationToSemantic second) sourcePackage)

/-- The forward transport comparison factors the first lift as the second lift. -/
theorem typedCoreFiberTransportPresentationComparisonApp_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic) :
    coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 =
      coreFiberLift (typedPresentationToSemantic second) sourcePackage := by
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first) sourcePackage) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first) sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic second) sourcePackage) := by
    rw [semantic_eq]
    exact coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic second) sourcePackage
  exact strongLiftComparisonHom_fac (packageProjection U)
    (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic first) sourcePackage)
    (coreFiberLift (typedPresentationToSemantic second) sourcePackage)

/-- The inverse transport comparison factors the second lift as the first lift. -/
theorem typedCoreFiberTransportPresentationComparisonApp_inv_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic) :
    coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).inv.1 =
      coreFiberLift (typedPresentationToSemantic first) sourcePackage := by
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first) sourcePackage) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first) sourcePackage
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic second) sourcePackage) := by
    rw [semantic_eq]
    exact coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic second) sourcePackage
  exact strongLiftComparisonHom_fac (packageProjection U)
    (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic second) sourcePackage)
    (coreFiberLift (typedPresentationToSemantic first) sourcePackage)

/-- The G-109 transport comparison is natural on source-fiber morphisms. -/
theorem typedCoreFiberTransportPresentationComparison_naturality
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    {sourcePackage targetPackage : CoreFiber source.toSemantic}
    (hom : sourcePackage ⟶ targetPackage) :
    (coreFiberTransportFunctor
        (typedPresentationToSemantic first)).map hom ≫
      (typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq targetPackage).hom =
    (typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq sourcePackage).hom ≫
      (coreFiberTransportFunctor
        (typedPresentationToSemantic second)).map hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first) sourcePackage) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first) sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic first) sourcePackage)
    (𝟙 target.toSemantic)
  change coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
      (((coreFiberTransportFunctor
          (typedPresentationToSemantic first)).map hom).1 ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1) =
    coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
      ((typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 ≫
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic second)).map hom).1)
  calc
    _ = (coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).map hom).1) ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 :=
      (Category.assoc _ _ _).symm
    _ = (hom.1 ≫
          coreFiberLift (typedPresentationToSemantic first) targetPackage) ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 := by
      rw [show coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).map hom).1 =
          hom.1 ≫ coreFiberLift (typedPresentationToSemantic first) targetPackage by
        simpa only [coreFiberTransportFunctor] using
          coreFiberTransportMap_fac (typedPresentationToSemantic first) hom]
    _ = hom.1 ≫ coreFiberLift (typedPresentationToSemantic second) targetPackage := by
      rw [Category.assoc,
        typedCoreFiberTransportPresentationComparisonApp_hom_fac]
    _ = (coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic second)).map hom).1) := by
      rw [show coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic second)).map hom).1 =
          hom.1 ≫ coreFiberLift (typedPresentationToSemantic second) targetPackage by
        simpa only [coreFiberTransportFunctor] using
          coreFiberTransportMap_fac (typedPresentationToSemantic second) hom]
    _ = _ := by
      rw [← Category.assoc,
        typedCoreFiberTransportPresentationComparisonApp_hom_fac]

/-- The componentwise G-109 comparison assembled as a natural isomorphism. -/
noncomputable def typedCoreFiberTransportPresentationComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second) :
    coreFiberTransportFunctor (typedPresentationToSemantic first) ≅
      coreFiberTransportFunctor (typedPresentationToSemantic second) :=
  NatIso.ofComponents
    (typedCoreFiberTransportPresentationComparisonApp first second semantic_eq)
    (by
      intro sourcePackage targetPackage hom
      exact typedCoreFiberTransportPresentationComparison_naturality
        first second semantic_eq hom)

/-- The two presentation-derived forward transposes commute with both comparisons. -/
theorem coreTransportToReindexHom_typedPresentationCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic)
    (targetPackage : CoreFiber target.toSemantic)
    (hom : (coreFiberTransportFunctor
        (typedPresentationToSemantic first)).obj sourcePackage ⟶ targetPackage) :
    coreTransportToReindexHom (typedRealizableHom first) sourcePackage
        targetPackage hom ≫
      (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
        targetPackage).hom =
    coreTransportToReindexHom (typedRealizableHom second) sourcePackage
      targetPackage
      ((typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq sourcePackage).inv ≫ hom) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let secondLift := selectedTypedCoreFiberCartesianLift second targetPackage
  letI : (packageProjection U).IsStronglyCartesian
      (typedPresentationToSemantic second) secondLift.hom := by
    simpa only [typedCartSemanticInput] using secondLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedPresentationToSemantic second)
    secondLift.hom (𝟙 source.toSemantic)
  change ((coreTransportToReindexHom (typedRealizableHom first) sourcePackage
      targetPackage hom).1 ≫
        (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1) ≫ secondLift.hom =
    (coreTransportToReindexHom (typedRealizableHom second) sourcePackage
      targetPackage
      ((typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq sourcePackage).inv ≫ hom)).1 ≫ secondLift.hom
  calc
    _ = (coreTransportToReindexHom (typedRealizableHom first) sourcePackage
          targetPackage hom).1 ≫
        ((selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫ secondLift.hom) :=
      Category.assoc _ _ _
    _ = (coreTransportToReindexHom (typedRealizableHom first) sourcePackage
          targetPackage hom).1 ≫
        (selectedTypedCoreFiberCartesianLift first targetPackage).hom := by
      rw [selectedTypedCoreFiberPresentationComparisonApp_hom_fac]
    _ = coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
        hom.1 := by
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberCartesianLift] using
        coreTransportToReindexHom_fac (typedRealizableHom first)
          sourcePackage targetPackage hom
    _ = (coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
          (typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq sourcePackage).inv.1) ≫ hom.1 := by
      rw [typedCoreFiberTransportPresentationComparisonApp_inv_fac]
    _ = coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
        ((typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).inv.1 ≫ hom.1) :=
      Category.assoc _ _ _
    _ = _ := by
      symm
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberCartesianLift] using
        coreTransportToReindexHom_fac (typedRealizableHom second)
          sourcePackage targetPackage
          ((typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq sourcePackage).inv ≫ hom)

/-- The inverse transposes commute with the same two generated comparisons. -/
theorem reindexToCoreTransportHom_typedPresentationCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic)
    (targetPackage : CoreFiber target.toSemantic)
    (hom : sourcePackage ⟶
      (selectedTypedCoreFiberReindexFunctor first).obj targetPackage) :
    (typedCoreFiberTransportPresentationComparisonApp first second semantic_eq
        sourcePackage).hom ≫
      reindexToCoreTransportHom (typedRealizableHom second) sourcePackage
        targetPackage
        (hom ≫ (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom) =
    reindexToCoreTransportHom (typedRealizableHom first) sourcePackage
      targetPackage hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first) sourcePackage) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first) sourcePackage
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic first) sourcePackage)
    (𝟙 target.toSemantic)
  change coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
      ((typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 ≫
        (reindexToCoreTransportHom (typedRealizableHom second) sourcePackage
          targetPackage
          (hom ≫ (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom)).1) =
    coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
      (reindexToCoreTransportHom (typedRealizableHom first) sourcePackage
        targetPackage hom).1
  calc
    _ = (coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
          (typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq sourcePackage).hom.1) ≫
        (reindexToCoreTransportHom (typedRealizableHom second) sourcePackage
          targetPackage
          (hom ≫ (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom)).1 :=
      (Category.assoc _ _ _).symm
    _ = coreFiberLift (typedPresentationToSemantic second) sourcePackage ≫
        (reindexToCoreTransportHom (typedRealizableHom second) sourcePackage
          targetPackage
          (hom ≫ (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom)).1 := by
      rw [typedCoreFiberTransportPresentationComparisonApp_hom_fac]
    _ = (hom.1 ≫
          (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom.1) ≫
        (selectedTypedCoreFiberCartesianLift second targetPackage).hom := by
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberCartesianLift] using
        reindexToCoreTransportHom_fac (typedRealizableHom second)
          sourcePackage targetPackage
          (hom ≫ (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom)
    _ = hom.1 ≫
        ((selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
          (selectedTypedCoreFiberCartesianLift second targetPackage).hom) :=
      Category.assoc _ _ _
    _ = hom.1 ≫
        (selectedTypedCoreFiberCartesianLift first targetPackage).hom := by
      rw [selectedTypedCoreFiberPresentationComparisonApp_hom_fac]
    _ = _ := by
      symm
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberCartesianLift] using
        reindexToCoreTransportHom_fac (typedRealizableHom first)
          sourcePackage targetPackage hom

/-- Pointwise compatibility of the two generated hom-set equivalences. -/
theorem coreTransportReindexHomEquiv_typedPresentationCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic)
    (targetPackage : CoreFiber target.toSemantic)
    (hom : (coreFiberTransportFunctor
        (typedPresentationToSemantic first)).obj sourcePackage ⟶ targetPackage) :
    (coreTransportReindexHomEquiv (typedRealizableHom first) sourcePackage
        targetPackage) hom ≫
      (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
        targetPackage).hom =
    (coreTransportReindexHomEquiv (typedRealizableHom second) sourcePackage
      targetPackage)
      ((typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq sourcePackage).inv ≫ hom) :=
  coreTransportToReindexHom_typedPresentationCompatibility first second
    semantic_eq sourcePackage targetPackage hom

/-- The generated units form the actual presentation-replacement square. -/
theorem coreTransportReindexUnit_typedPresentationCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (sourcePackage : CoreFiber source.toSemantic) :
    (coreTransportReindexUnit (typedRealizableHom first)).app sourcePackage ≫
      (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
        ((coreFiberTransportFunctor (typedPresentationToSemantic first)).obj
          sourcePackage)).hom ≫
      (selectedTypedCoreFiberReindexFunctor second).map
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom =
    (coreTransportReindexUnit
      (typedRealizableHom second)).app sourcePackage := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let secondLift := selectedTypedCoreFiberCartesianLift second
    ((coreFiberTransportFunctor
      (typedPresentationToSemantic second)).obj sourcePackage)
  letI : (packageProjection U).IsStronglyCartesian
      (typedPresentationToSemantic second) secondLift.hom := by
    simpa only [typedCartSemanticInput] using secondLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) (typedPresentationToSemantic second)
    secondLift.hom (𝟙 source.toSemantic)
  change (((coreTransportReindexUnit
      (typedRealizableHom first)).app sourcePackage).1 ≫
    (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
      ((coreFiberTransportFunctor (typedPresentationToSemantic first)).obj
        sourcePackage)).hom.1 ≫
    ((selectedTypedCoreFiberReindexFunctor second).map
      (typedCoreFiberTransportPresentationComparisonApp first second
        semantic_eq sourcePackage).hom).1) ≫ secondLift.hom =
    ((coreTransportReindexUnit
      (typedRealizableHom second)).app sourcePackage).1 ≫ secondLift.hom
  calc
    _ = (((coreTransportReindexUnit
          (typedRealizableHom first)).app sourcePackage).1 ≫
          (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic first)).obj sourcePackage)).hom.1) ≫
        (((selectedTypedCoreFiberReindexFunctor second).map
          (typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq sourcePackage).hom).1 ≫ secondLift.hom) :=
      Category.assoc _ _ _
    _ = (((coreTransportReindexUnit
          (typedRealizableHom first)).app sourcePackage).1 ≫
          (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic first)).obj sourcePackage)).hom.1) ≫
        ((selectedTypedCoreFiberCartesianLift second
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).obj sourcePackage)).hom ≫
          (typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq sourcePackage).hom.1) := by
      rw [selectedTypedCoreFiberReindexFunctor_map_fac]
    _ = ((coreTransportReindexUnit
          (typedRealizableHom first)).app sourcePackage).1 ≫
        ((selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).obj sourcePackage)).hom.1 ≫
          (selectedTypedCoreFiberCartesianLift second
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic first)).obj sourcePackage)).hom) ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 := by simp only [Category.assoc]
    _ = ((coreTransportReindexUnit
          (typedRealizableHom first)).app sourcePackage).1 ≫
        (selectedTypedCoreFiberCartesianLift first
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).obj sourcePackage)).hom ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 := by
      rw [selectedTypedCoreFiberPresentationComparisonApp_hom_fac]
    _ = coreFiberLift (typedPresentationToSemantic first) sourcePackage ≫
        (typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq sourcePackage).hom.1 := by
      rw [← Category.assoc]
      rw [show ((coreTransportReindexUnit
          (typedRealizableHom first)).app sourcePackage).1 ≫
          (selectedTypedCoreFiberCartesianLift first
            ((coreFiberTransportFunctor
              (typedPresentationToSemantic first)).obj sourcePackage)).hom =
        coreFiberLift (typedPresentationToSemantic first) sourcePackage by
        simpa only [typedRealizableHom, typedCartSemanticInput,
          selectedTypedCoreFiberCartesianLift] using
          coreTransportReindexUnit_app_fac (typedRealizableHom first)
            sourcePackage]
    _ = coreFiberLift (typedPresentationToSemantic second) sourcePackage :=
      typedCoreFiberTransportPresentationComparisonApp_hom_fac first second
        semantic_eq sourcePackage
    _ = ((coreTransportReindexUnit
          (typedRealizableHom second)).app sourcePackage).1 ≫ secondLift.hom := by
      symm
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberCartesianLift] using
        coreTransportReindexUnit_app_fac (typedRealizableHom second)
          sourcePackage

/-- The generated counits form the actual presentation-replacement square. -/
theorem coreTransportReindexCounit_typedPresentationCompatibility
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (first second : CartPresentationBetween source target)
    (semantic_eq : typedPresentationToSemantic first =
      typedPresentationToSemantic second)
    (targetPackage : CoreFiber target.toSemantic) :
    (coreFiberTransportFunctor
        (typedPresentationToSemantic first)).map
      (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
        targetPackage).hom ≫
    (typedCoreFiberTransportPresentationComparisonApp first second semantic_eq
      ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage)).hom ≫
    (coreTransportReindexCounit
      (typedRealizableHom second)).app targetPackage =
    (coreTransportReindexCounit
      (typedRealizableHom first)).app targetPackage := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  letI : (packageProjection U).IsStronglyCocartesian
      (typedPresentationToSemantic first)
      (coreFiberLift (typedPresentationToSemantic first)
        ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage)) :=
    coreFiberLift_isStronglyCocartesian
      (typedPresentationToSemantic first)
      ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage)
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (packageProjection U) (typedPresentationToSemantic first)
    (coreFiberLift (typedPresentationToSemantic first)
      ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage))
    (𝟙 target.toSemantic)
  change coreFiberLift (typedPresentationToSemantic first)
      ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage) ≫
    (((coreFiberTransportFunctor
        (typedPresentationToSemantic first)).map
      (selectedTypedCoreFiberPresentationComparisonApp first second semantic_eq
        targetPackage).hom).1 ≫
      (typedCoreFiberTransportPresentationComparisonApp first second semantic_eq
        ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage)).hom.1 ≫
      ((coreTransportReindexCounit
        (typedRealizableHom second)).app targetPackage).1) =
    coreFiberLift (typedPresentationToSemantic first)
      ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage) ≫
      ((coreTransportReindexCounit
        (typedRealizableHom first)).app targetPackage).1
  calc
    _ = (coreFiberLift (typedPresentationToSemantic first)
          ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage) ≫
          ((coreFiberTransportFunctor
            (typedPresentationToSemantic first)).map
            (selectedTypedCoreFiberPresentationComparisonApp first second
              semantic_eq targetPackage).hom).1) ≫
        ((typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq
          ((selectedTypedCoreFiberReindexFunctor second).obj
            targetPackage)).hom.1 ≫
          ((coreTransportReindexCounit
            (typedRealizableHom second)).app targetPackage).1) :=
      (Category.assoc _ _ _).symm
    _ = ((selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
          coreFiberLift (typedPresentationToSemantic first)
            ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage)) ≫
        ((typedCoreFiberTransportPresentationComparisonApp first second
          semantic_eq
          ((selectedTypedCoreFiberReindexFunctor second).obj
            targetPackage)).hom.1 ≫
          ((coreTransportReindexCounit
            (typedRealizableHom second)).app targetPackage).1) := by
      rw [show coreFiberLift (typedPresentationToSemantic first)
          ((selectedTypedCoreFiberReindexFunctor first).obj targetPackage) ≫
        ((coreFiberTransportFunctor
          (typedPresentationToSemantic first)).map
          (selectedTypedCoreFiberPresentationComparisonApp first second
            semantic_eq targetPackage).hom).1 =
        (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
          coreFiberLift (typedPresentationToSemantic first)
            ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage) by
        simpa only [coreFiberTransportFunctor] using
          coreFiberTransportMap_fac (typedPresentationToSemantic first)
            (selectedTypedCoreFiberPresentationComparisonApp first second
              semantic_eq targetPackage).hom]
    _ = (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
        (coreFiberLift (typedPresentationToSemantic first)
          ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage) ≫
          (typedCoreFiberTransportPresentationComparisonApp first second
            semantic_eq
            ((selectedTypedCoreFiberReindexFunctor second).obj
              targetPackage)).hom.1) ≫
        ((coreTransportReindexCounit
          (typedRealizableHom second)).app targetPackage).1 := by
      simp only [Category.assoc]
    _ = (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
        coreFiberLift (typedPresentationToSemantic second)
          ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage) ≫
        ((coreTransportReindexCounit
          (typedRealizableHom second)).app targetPackage).1 := by
      rw [typedCoreFiberTransportPresentationComparisonApp_hom_fac]
    _ = (selectedTypedCoreFiberPresentationComparisonApp first second
          semantic_eq targetPackage).hom.1 ≫
        (selectedTypedCoreFiberCartesianLift second targetPackage).hom := by
      rw [show coreFiberLift (typedPresentationToSemantic second)
          ((selectedTypedCoreFiberReindexFunctor second).obj targetPackage) ≫
        ((coreTransportReindexCounit
          (typedRealizableHom second)).app targetPackage).1 =
        (selectedTypedCoreFiberCartesianLift second targetPackage).hom by
        simpa only [typedRealizableHom, typedCartSemanticInput,
          selectedTypedCoreFiberReindexFunctor,
          selectedTypedCoreFiberCartesianLift] using
          coreTransportReindexCounit_app_fac (typedRealizableHom second)
            targetPackage]
    _ = (selectedTypedCoreFiberCartesianLift first targetPackage).hom :=
      selectedTypedCoreFiberPresentationComparisonApp_hom_fac first second
        semantic_eq targetPackage
    _ = _ := by
      symm
      simpa only [typedRealizableHom, typedCartSemanticInput,
        selectedTypedCoreFiberReindexFunctor,
        selectedTypedCoreFiberCartesianLift] using
        coreTransportReindexCounit_app_fac (typedRealizableHom first)
          targetPackage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
