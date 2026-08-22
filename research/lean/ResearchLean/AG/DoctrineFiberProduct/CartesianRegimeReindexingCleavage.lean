import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexingCoherence
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLiftComparison

/-!
# Cartesian cleavage choice independence

This module isolates the sole choice made by cartesian reindexing: one strong
cartesian lift at every target-fiber object.  Its object action, vertical maps,
factor graphs, functor laws, and comparison natural isomorphisms are generated
from the strong-cartesian universal property.

An arbitrary cleavage is a universally quantified comparison subject.  The
selected G-110 producer remains caller-free and is recorded separately below.
Presentation replacement, quotient descent, adjunctions, and Beck--Chevalley
mates remain later obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

set_option maxHeartbeats 2000000

/-! ## A minimal cartesian cleavage and its derived functor -/

/--
A cartesian cleavage over one literal semantic input.  The lift family is the
only field: maps, laws, comparisons, and coherence are derived data.
-/
structure CoreFiberCartesianCleavage
    {U : AtomCarrier.{u}} (input : CartSemanticInput U) where
  /-- Choose one strong cartesian lift at every target-fiber object. -/
  lift : ∀ targetPackage : CoreFiber input.target,
    StrongCartesianLift input targetPackage

namespace CoreFiberCartesianCleavage

/-- The source-fiber object selected by a cleavage. -/
noncomputable def reindexObject
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) : CoreFiber input.source :=
  (cleavage.lift targetPackage).domainObject

/-- Reflect a vertical target map through the chosen lift at its codomain. -/
noncomputable def reindexMap
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second : CoreFiber input.target} (hom : first ⟶ second) :
    cleavage.reindexObject first ⟶ cleavage.reindexObject second := by
  let firstLift := cleavage.lift first
  let secondLift := cleavage.lift second
  letI := firstLift.isStronglyCartesian
  letI := secondLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (firstLift.hom ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.hom ≫ 𝟙 input.target) (firstLift.hom ≫ hom.1))
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (packageProjection U) input.hom secondLift.hom
      (g := 𝟙 input.source) (f' := input.hom)
      (Category.id_comp input.hom).symm (firstLift.hom ≫ hom.1),
    inferInstance⟩

/-- The reflected map satisfies its defining cartesian factor graph. -/
theorem reindexMap_fac
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second : CoreFiber input.target} (hom : first ⟶ second) :
    (cleavage.reindexMap hom).1 ≫ (cleavage.lift second).hom =
      (cleavage.lift first).hom ≫ hom.1 := by
  let firstLift := cleavage.lift first
  let secondLift := cleavage.lift second
  letI := firstLift.isStronglyCartesian
  letI := secondLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift input.hom
      (firstLift.hom ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.hom ≫ 𝟙 input.target) (firstLift.hom ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (packageProjection U) input.hom secondLift.hom
    (Category.id_comp input.hom).symm (firstLift.hom ≫ hom.1)

/-- The factor graph uniquely determines a reflected vertical map. -/
theorem reindexMap_unique
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second : CoreFiber input.target} (hom : first ⟶ second)
    (candidate : cleavage.reindexObject first ⟶
      cleavage.reindexObject second)
    (candidate_fac : candidate.1 ≫ (cleavage.lift second).hom =
      (cleavage.lift first).hom ≫ hom.1) :
    candidate = cleavage.reindexMap hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let firstLift := cleavage.lift first
  let secondLift := cleavage.lift second
  letI := firstLift.isStronglyCartesian
  letI := secondLift.isStronglyCartesian
  letI : (packageProjection U).IsHomLift
      (𝟙 input.target) hom.1 := hom.2
  letI : (packageProjection U).IsHomLift
      (𝟙 input.source) candidate.1 := candidate.2
  letI : (packageProjection U).IsHomLift input.hom
      (firstLift.hom ≫ hom.1) := by
    simpa using inferInstanceAs
      ((packageProjection U).IsHomLift
        (input.hom ≫ 𝟙 input.target) (firstLift.hom ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.map_uniq
    (packageProjection U) input.hom secondLift.hom
    (Category.id_comp input.hom).symm
    (firstLift.hom ≫ hom.1) candidate.1 candidate_fac

/-- Cleavage-derived reindexing preserves identities. -/
theorem reindexMap_id
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    cleavage.reindexMap (𝟙 targetPackage) =
      𝟙 (cleavage.reindexObject targetPackage) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let lift := cleavage.lift targetPackage
  letI := lift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom lift.hom (𝟙 input.source)
  simpa using cleavage.reindexMap_fac (𝟙 targetPackage)

/-- Cleavage-derived reindexing preserves every composable pair. -/
theorem reindexMap_comp
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second third : CoreFiber input.target}
    (firstHom : first ⟶ second) (secondHom : second ⟶ third) :
    cleavage.reindexMap (firstHom ≫ secondHom) =
      cleavage.reindexMap firstHom ≫ cleavage.reindexMap secondHom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let thirdLift := cleavage.lift third
  letI := thirdLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom thirdLift.hom (𝟙 input.source)
  change
    (cleavage.reindexMap (firstHom ≫ secondHom)).1 ≫ thirdLift.hom =
      ((cleavage.reindexMap firstHom).1 ≫
        (cleavage.reindexMap secondHom).1) ≫ thirdLift.hom
  calc
    _ = (cleavage.lift first).hom ≫ (firstHom ≫ secondHom).1 :=
      cleavage.reindexMap_fac (firstHom ≫ secondHom)
    _ = (cleavage.lift first).hom ≫ (firstHom.1 ≫ secondHom.1) := rfl
    _ = ((cleavage.lift first).hom ≫ firstHom.1) ≫ secondHom.1 :=
      (Category.assoc _ _ _).symm
    _ = ((cleavage.reindexMap firstHom).1 ≫
        (cleavage.lift second).hom) ≫ secondHom.1 := by
      rw [cleavage.reindexMap_fac]
    _ = (cleavage.reindexMap firstHom).1 ≫
        ((cleavage.lift second).hom ≫ secondHom.1) :=
      Category.assoc _ _ _
    _ = (cleavage.reindexMap firstHom).1 ≫
        ((cleavage.reindexMap secondHom).1 ≫ thirdLift.hom) := by
      rw [cleavage.reindexMap_fac]
    _ = _ := (Category.assoc _ _ _).symm

/-- The reindexing functor generated by one cleavage choice. -/
noncomputable def reindexFunctor
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input) :
    CoreFiber input.target ⥤ CoreFiber input.source where
  obj := cleavage.reindexObject
  map := cleavage.reindexMap
  map_id := cleavage.reindexMap_id
  map_comp := cleavage.reindexMap_comp

/-- The functor object is exactly the domain of the chosen lift. -/
theorem reindexFunctor_obj
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    cleavage.reindexFunctor.obj targetPackage =
      (cleavage.lift targetPackage).domainObject :=
  rfl

/-- The functor map satisfies the generated cartesian factor graph. -/
theorem reindexFunctor_map_fac
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second : CoreFiber input.target} (hom : first ⟶ second) :
    (cleavage.reindexFunctor.map hom).1 ≫ (cleavage.lift second).hom =
      (cleavage.lift first).hom ≫ hom.1 :=
  cleavage.reindexMap_fac hom

/-- The functor map is the unique vertical map with its factor graph. -/
theorem reindexFunctor_map_unique
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    {first second : CoreFiber input.target} (hom : first ⟶ second)
    (candidate : cleavage.reindexFunctor.obj first ⟶
      cleavage.reindexFunctor.obj second)
    (candidate_fac : candidate.1 ≫ (cleavage.lift second).hom =
      (cleavage.lift first).hom ≫ hom.1) :
    candidate = cleavage.reindexFunctor.map hom :=
  cleavage.reindexMap_unique hom candidate candidate_fac

/-! ## Canonical comparison between two choices -/

/-- The canonical component from the first cleavage domain to the second. -/
noncomputable def comparisonApp
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    first.reindexFunctor.obj targetPackage ≅
      second.reindexFunctor.obj targetPackage where
  hom := ⟨(StrongCartesianLift.domainIso
      (second.lift targetPackage) (first.lift targetPackage)).hom,
    StrongCartesianLift.domainIso_hom_isHomLift
      (second.lift targetPackage) (first.lift targetPackage)⟩
  inv := ⟨(StrongCartesianLift.domainIso
      (second.lift targetPackage) (first.lift targetPackage)).inv,
    StrongCartesianLift.domainIso_inv_isHomLift
      (second.lift targetPackage) (first.lift targetPackage)⟩
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (second.lift targetPackage) (first.lift targetPackage)).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact (StrongCartesianLift.domainIso
      (second.lift targetPackage) (first.lift targetPackage)).inv_hom_id

/-- The forward comparison followed by the second lift is the first lift. -/
theorem comparisonApp_hom_fac
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    (comparisonApp first second targetPackage).hom.1 ≫
        (second.lift targetPackage).hom =
      (first.lift targetPackage).hom :=
  StrongCartesianLift.domainIso_hom_fac
    (second.lift targetPackage) (first.lift targetPackage)

/-- The inverse comparison followed by the first lift is the second lift. -/
theorem comparisonApp_inv_fac
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    (comparisonApp first second targetPackage).inv.1 ≫
        (first.lift targetPackage).hom =
      (second.lift targetPackage).hom :=
  StrongCartesianLift.domainIso_inv_fac
    (second.lift targetPackage) (first.lift targetPackage)

/-- The canonical comparison is natural on every vertical target map. -/
theorem comparison_naturality
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input)
    {sourcePackage targetPackage : CoreFiber input.target}
    (hom : sourcePackage ⟶ targetPackage) :
    first.reindexFunctor.map hom ≫
        (comparisonApp first second targetPackage).hom =
      (comparisonApp first second sourcePackage).hom ≫
        second.reindexFunctor.map hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let secondTarget := second.lift targetPackage
  letI := secondTarget.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom secondTarget.hom (𝟙 input.source)
  change
    (first.reindexFunctor.map hom).1 ≫
        (comparisonApp first second targetPackage).hom.1 ≫ secondTarget.hom =
      (comparisonApp first second sourcePackage).hom.1 ≫
        (second.reindexFunctor.map hom).1 ≫ secondTarget.hom
  calc
    _ = (first.reindexFunctor.map hom).1 ≫
        ((comparisonApp first second targetPackage).hom.1 ≫
          secondTarget.hom) := Category.assoc _ _ _
    _ = (first.reindexFunctor.map hom).1 ≫
        (first.lift targetPackage).hom := by
      rw [comparisonApp_hom_fac]
    _ = (first.lift sourcePackage).hom ≫ hom.1 :=
      first.reindexFunctor_map_fac hom
    _ = ((comparisonApp first second sourcePackage).hom.1 ≫
        (second.lift sourcePackage).hom) ≫ hom.1 := by
      rw [comparisonApp_hom_fac]
    _ = (comparisonApp first second sourcePackage).hom.1 ≫
        ((second.lift sourcePackage).hom ≫ hom.1) :=
      Category.assoc _ _ _
    _ = (comparisonApp first second sourcePackage).hom.1 ≫
        ((second.reindexFunctor.map hom).1 ≫ secondTarget.hom) := by
      rw [second.reindexFunctor_map_fac]
    _ = _ := (Category.assoc _ _ _).symm

/-- The canonical natural isomorphism comparing two cleavage choices. -/
noncomputable def comparison
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input) :
    first.reindexFunctor ≅ second.reindexFunctor :=
  NatIso.ofComponents (comparisonApp first second)
    (fun hom => comparison_naturality first second hom)

/-- The component comparison is reflexive. -/
theorem comparisonApp_refl
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    (comparisonApp cleavage cleavage targetPackage).hom =
      𝟙 (cleavage.reindexFunctor.obj targetPackage) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let targetLift := cleavage.lift targetPackage
  letI := targetLift.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom targetLift.hom (𝟙 input.source)
  change
    (comparisonApp cleavage cleavage targetPackage).hom.1 ≫ targetLift.hom =
      𝟙 targetLift.domain ≫ targetLift.hom
  rw [comparisonApp_hom_fac]
  simp
  rfl

/-- The whole comparison natural isomorphism is reflexive. -/
theorem comparison_refl
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (cleavage : CoreFiberCartesianCleavage input) :
    comparison cleavage cleavage = Iso.refl cleavage.reindexFunctor := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  exact comparisonApp_refl cleavage targetPackage

/-- Reversing a comparison gives the comparison in the opposite direction. -/
theorem comparison_symm
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second : CoreFiberCartesianCleavage input) :
    (comparison first second).symm = comparison second first := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  apply CategoryTheory.Functor.Fiber.hom_ext
  let firstTarget := first.lift targetPackage
  letI := firstTarget.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom firstTarget.hom (𝟙 input.source)
  change
    (comparisonApp first second targetPackage).inv.1 ≫ firstTarget.hom =
      (comparisonApp second first targetPackage).hom.1 ≫ firstTarget.hom
  rw [comparisonApp_inv_fac, comparisonApp_hom_fac]

/-- Component comparisons satisfy the three-choice cocycle. -/
theorem comparisonApp_cocycle
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second third : CoreFiberCartesianCleavage input)
    (targetPackage : CoreFiber input.target) :
    (comparisonApp first second targetPackage).hom ≫
        (comparisonApp second third targetPackage).hom =
      (comparisonApp first third targetPackage).hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let thirdTarget := third.lift targetPackage
  letI := thirdTarget.isStronglyCartesian
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (packageProjection U) input.hom thirdTarget.hom (𝟙 input.source)
  change
    ((comparisonApp first second targetPackage).hom.1 ≫
      (comparisonApp second third targetPackage).hom.1) ≫ thirdTarget.hom =
      (comparisonApp first third targetPackage).hom.1 ≫ thirdTarget.hom
  rw [Category.assoc, comparisonApp_hom_fac, comparisonApp_hom_fac,
    comparisonApp_hom_fac]

/-- Whole natural comparisons satisfy the three-choice cocycle. -/
theorem comparison_cocycle
    {U : AtomCarrier.{u}} {input : CartSemanticInput U}
    (first second third : CoreFiberCartesianCleavage input) :
    (comparison first second).trans (comparison second third) =
      comparison first third := by
  apply Iso.ext
  apply NatTrans.ext
  funext targetPackage
  exact comparisonApp_cocycle first second third targetPackage

end CoreFiberCartesianCleavage

/-! ## The producer-derived selected cleavage -/

/-- The fixed G-110 producer, packaged only as a comparison subject. -/
noncomputable def selectedCoreFiberCartesianCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    CoreFiberCartesianCleavage input.semantic where
  lift := selectedCoreFiberCartesianLift input

/-- The exact-endpoint selected cleavage used by Cycle 32. -/
noncomputable def selectedTypedCoreFiberCartesianCleavage
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    CoreFiberCartesianCleavage (typedCartSemanticInput presentation) where
  lift := selectedTypedCoreFiberCartesianLift presentation

/-- The typed selected cleavage exposes the accepted generated lift. -/
theorem selectedTypedCoreFiberCartesianCleavage_lift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target)
    (targetPackage : CoreFiber target.toSemantic) :
    (selectedTypedCoreFiberCartesianCleavage presentation).lift targetPackage =
      selectedTypedCoreFiberCartesianLift presentation targetPackage :=
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
