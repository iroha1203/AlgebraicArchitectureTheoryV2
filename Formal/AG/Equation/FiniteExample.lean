import Formal.AG.Equation.Basic

/-!
# Finite firing example for architectural equations

The fixture uses a two-Atom carrier, three equation roles, and one shared
`ArchitectureObject` input type.  Membership of the distinguished Atom makes
all residuals vanish in the positive object; removing that Atom makes the
required residual equal to `1 : Int`.  Thus the generated predicates have both
positive and negative examples without storing a truth certificate.
-/

noncomputable section

namespace AAT.AG
namespace Examples.ArchitecturalEquationSystemFiniteExample

universe u

/-- A two-Atom carrier for the finite equation-system fixture. -/
def carrier : AtomCarrier where
  AtomKind := PUnit
  Axis := PUnit
  Subject := PUnit
  Predicate := PUnit
  Payload := PUnit
  Atom := Bool
  kind := fun _ => PUnit.unit
  axis := fun _ => PUnit.unit
  subject := fun _ => PUnit.unit
  predicate := fun _ => PUnit.unit
  payload := fun _ => PUnit.unit

/-- The positive configuration contains both finite atoms. -/
def positiveConfiguration : AtomConfiguration carrier where
  family := { mem := fun atom => atom = false ∨ atom = true }
  relation := fun _ _ => False
  identification := Eq

/-- The negative configuration omits the distinguished atom `true`. -/
def negativeConfiguration : AtomConfiguration carrier where
  family := { mem := fun atom => atom = false }
  relation := fun _ _ => False
  identification := Eq

/-- A positive architecture object whose distinguished Atom is present. -/
def positiveObject : ArchitectureObject carrier where
  configuration := positiveConfiguration
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- A negative architecture object of the same input type with the distinguished Atom absent. -/
def negativeObject : ArchitectureObject carrier where
  configuration := negativeConfiguration
  StructureMaps := PUnit
  SelectedQuantities := PUnit
  structureMaps := PUnit.unit
  selectedQuantities := PUnit.unit

/-- A finite readable context used to fire the residual equations. -/
def context : Site.ArchCtx positiveObject where
  minimal := {
    Support := Bool
    Axis := Fin 2
    Observable := Bool
    supportReads := fun support atom => support = atom
    supportReads_objectFamily := by
      intro support atom _h
      cases atom <;> simp [positiveObject, positiveConfiguration]
    axisReads := fun axis => axis = 0
    observableReads := fun observable => observable = true
  }
  Extension := PUnit
  extension := PUnit.unit

/-- The standard restriction-morphism preorder on the positive fixture object. -/
def contextPreorder : Site.ContextPreorderCategory positiveObject :=
  Site.contextMorphismPreorderCategory positiveObject

/-- The selected finite context as a Mathlib-facing context-category object. -/
def contextObject : Site.ContextCategoryObject contextPreorder :=
  Site.ContextCategoryObject.of contextPreorder context

/-- Three concrete indices exhibiting required, optional, and derived equations. -/
inductive FixtureEquationIndex where
  | requiredEquation
  | optionalEquation
  | derivedEquation
  deriving DecidableEq

/-- The three equation indices exhibit required, optional, and derived roles. -/
def role : FixtureEquationIndex -> EquationRole
  | .requiredEquation => .required
  | .optionalEquation => .optional
  | .derivedEquation => .derived

/-- A nonconstant symbolic violation coordinate on the two-Atom fixture. -/
def violationValue (_index : FixtureEquationIndex) (atom : Bool) : Int :=
  match atom with
  | false => -1
  | true => 1

/-- Residual value determined from the distinguished Atom of an input object. -/
def residualValue (object : ArchitectureObject carrier) : Int := by
  classical
  exact if object.configuration.family.mem true then 0 else 1

/-- Only the selected required equation reads the object-dependent residual. -/
def indexedResidualValue (object : ArchitectureObject carrier) :
    FixtureEquationIndex -> Int
  | .requiredEquation => residualValue object
  | .optionalEquation => 0
  | .derivedEquation => 0

/--
A finite firing fixture for Issue #3729 whose required residual separates the
two fixture objects.
-/
def system : ArchitecturalEquationSystem contextPreorder where
  Index := FixtureEquationIndex
  role := role
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by
    intro W x
    rfl
  restrict_comp := by
    intro W₀ W₁ W₂ f g x
    rfl
  violationCoordinate := fun _ index atom => violationValue index atom
  violationCoordinate_restrict := by
    intro source target f index atom
    rfl
  equationResidual := fun _ object index _ => indexedResidualValue object index
  equationResidual_restrict := by
    intro source target f object index atom
    rfl

/-- The role selector has distinct positive and negative readings for all three roles. -/
theorem role_selector_separates :
    system.Required .requiredEquation ∧ ¬ system.Required .optionalEquation ∧
      system.Optional .optionalEquation ∧ ¬ system.Optional .requiredEquation ∧
      system.Derived .derivedEquation ∧ ¬ system.Derived .requiredEquation := by
  simp [ArchitecturalEquationSystem.Required,
    ArchitecturalEquationSystem.Optional, ArchitecturalEquationSystem.Derived,
    system, role]

/-- Every equation residual vanishes on the positive finite object. -/
theorem positive_equationHolds (index : FixtureEquationIndex) :
    system.EquationHolds index positiveObject := by
  cases index <;>
  intro W atom
  all_goals
    simp [system, indexedResidualValue, residualValue, positiveObject,
      positiveConfiguration]

/-- The positive finite object satisfies every required equation. -/
theorem positive_equationLawful : system.EquationLawful positiveObject := by
  intro index _hrequired
  exact positive_equationHolds index

/-- The positive finite object satisfies required, optional, and derived equations. -/
theorem positive_fullyEquationLawful :
    system.FullyEquationLawful positiveObject := by
  intro index
  exact positive_equationHolds index

/-- The required residual is nonzero on the negative finite object. -/
theorem negative_not_equationHolds_required :
    ¬ system.EquationHolds .requiredEquation negativeObject := by
  intro h
  have hz := h contextObject false
  simp [system, indexedResidualValue, residualValue, negativeObject,
    negativeConfiguration] at hz

/-- The negative finite object fails the selected required equation. -/
theorem negative_not_equationLawful :
    ¬ system.EquationLawful negativeObject := by
  intro h
  apply negative_not_equationHolds_required
  exact h .requiredEquation (by
    simp [ArchitecturalEquationSystem.Required, system, role])

/-- The negative finite object also fails full equation lawfulness. -/
theorem negative_not_fullyEquationLawful :
    ¬ system.FullyEquationLawful negativeObject := by
  intro h
  apply negative_not_equationHolds_required
  exact h .requiredEquation

/-- The finite fixture separates lawful and non-lawful objects of the same input type. -/
theorem lawfulness_separates :
    positiveObject ≠ negativeObject ∧
      system.EquationLawful positiveObject ∧
      ¬ system.EquationLawful negativeObject := by
  refine ⟨?_, positive_equationLawful, negative_not_equationLawful⟩
  intro hobjects
  apply negative_not_equationLawful
  simpa [hobjects] using positive_equationLawful

end Examples.ArchitecturalEquationSystemFiniteExample
end AAT.AG
