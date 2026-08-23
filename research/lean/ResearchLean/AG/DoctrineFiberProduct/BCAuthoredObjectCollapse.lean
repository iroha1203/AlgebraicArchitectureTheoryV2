import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredNonAxisCollapseAudit

/-!
# Object-collapse route on the fixed authored support

Architecture objects retain abstract structure-map and selected-quantity
readings in addition to their Atom configuration.  The finite reading's
generated objects use `PUnit` for both readings.  Replacing arbitrary auxiliary
readings by those canonical units therefore preserves configuration while
collapsing distinct objects over the same configuration.

Implementation notes: this module uses object erasure because the fixed finite
equation and operation readings observe the retained configuration, while the
exact-hom object field still ranges over the auxiliary readings of every
`ArchitectureObject`.  The earlier axis-collapse route is not reused: exact
axis transport is an equivalence and therefore cannot supply this
noninjectivity.  The authored diagnostic selector is deliberately kept out of
the erasure definition; making the unconditional exact factor diagnostic-
generated is the next, separately audited K2 obligation rather than a premise
hidden in this construction.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-- Forget auxiliary object readings while retaining the full Atom configuration. -/
noncomputable def finiteAxisFoldEraseObject
    (object : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject FiniteModel.carrier :=
  transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv
    (FiniteModel.objectOfConfiguration
      (transportArchitectureObject
        finiteModelDoctrineFromFixture.atomEquiv.symm object).configuration)

/-- Object erasure retains the complete configuration. -/
theorem finiteAxisFoldEraseObject_configuration
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteAxisFoldEraseObject object).configuration = object.configuration := by
  change (object.configuration.transport
      finiteModelDoctrineFromFixture.atomEquiv.symm).transport
        finiteModelDoctrineFromFixture.atomEquiv = object.configuration
  exact atomConfiguration_transport_symm_equiv _ _

/-- Inverse transport sees exactly the original configuration after erasure. -/
theorem finiteAxisFoldEraseObject_inverse_configuration
    (object : ArchitectureObject FiniteModel.carrier) :
    (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
      (finiteAxisFoldEraseObject object)).configuration =
    (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
      object).configuration := by
  simp [finiteAxisFoldEraseObject, FiniteModel.objectOfConfiguration]

/-- Erasure is determined entirely by the retained configuration. -/
theorem finiteAxisFoldEraseObject_eq_of_configuration
    {first second : ArchitectureObject FiniteModel.carrier}
    (configuration_eq : first.configuration = second.configuration) :
    finiteAxisFoldEraseObject first = finiteAxisFoldEraseObject second := by
  unfold finiteAxisFoldEraseObject
  apply congrArg (transportArchitectureObject
    finiteModelDoctrineFromFixture.atomEquiv)
  apply congrArg FiniteModel.objectOfConfiguration
  exact congrArg
    (fun configuration => configuration.transport
      finiteModelDoctrineFromFixture.atomEquiv.symm) configuration_eq

/-- A unit-decorated object over the finite cyclic configuration. -/
noncomputable def finiteAxisFoldUnitObject : ArchitectureObject FiniteModel.carrier :=
  finiteAxisFoldEraseObject FiniteModel.object

/-- A Boolean-decorated object with the same configuration. -/
noncomputable def finiteAxisFoldBoolObject : ArchitectureObject FiniteModel.carrier where
  configuration := FiniteModel.object.configuration
  StructureMaps := Bool
  SelectedQuantities := PUnit
  structureMaps := false
  selectedQuantities := PUnit.unit

/-- The two objects are genuinely distinct despite sharing their configuration. -/
theorem finiteAxisFoldUnitObject_ne_boolObject :
    finiteAxisFoldUnitObject ≠ finiteAxisFoldBoolObject := by
  intro equality
  have typeEquality := congrArg ArchitectureObject.StructureMaps equality
  have cardEquality : Fintype.card PUnit = Fintype.card Bool :=
    Fintype.card_congr (Equiv.cast typeEquality)
  norm_num at cardEquality

/-- Erasure identifies the two distinct same-configuration objects. -/
theorem finiteAxisFoldEraseObject_unit_eq_bool :
    finiteAxisFoldEraseObject finiteAxisFoldUnitObject =
      finiteAxisFoldEraseObject finiteAxisFoldBoolObject := by
  apply finiteAxisFoldEraseObject_eq_of_configuration
  exact finiteAxisFoldEraseObject_configuration FiniteModel.object

/-- The surviving object operation is a concrete noninjective map. -/
theorem finiteAxisFoldEraseObject_not_injective :
    ¬ Function.Injective finiteAxisFoldEraseObject := by
  intro injective
  exact finiteAxisFoldUnitObject_ne_boolObject
    (injective finiteAxisFoldEraseObject_unit_eq_bool)

/-- Equation residuals depend only on the object configuration. -/
def EquationResidualConfigurationInvariant
    {U : AtomCarrier.{u}} {base : ArchitectureObject U}
    {C : Site.ContextPreorderCategory base}
    (E : ArchitecturalEquationSystem C) : Prop :=
  ∀ W (first second : ArchitectureObject U) index atom,
    first.configuration = second.configuration →
      E.equationResidual W first index atom =
        E.equationResidual W second index atom

/-- A small equation system whose residual observes an auxiliary object
reading, used as the negative instance for configuration invariance. -/
noncomputable def auxiliarySensitiveEquationSystem
    (C : Site.ContextPreorderCategory FiniteModel.object) :
    ArchitecturalEquationSystem C := by
  classical
  exact {
    Index := PUnit
    role := fun _ => EquationRole.required
    Observable := fun _ => Int
    observableCommRing := fun _ => inferInstance
    restrict := fun _ => RingHom.id Int
    restrict_id := by intros; rfl
    restrict_comp := by intros; rfl
    violationCoordinate := fun _ _ _ => 0
    violationCoordinate_restrict := by intros; rfl
    equationResidual := fun _ object _ _ =>
      if object = finiteAxisFoldBoolObject then 1 else 0
    equationResidual_restrict := by intros; rfl
  }

/-- Configuration invariance is a substantive condition: an equation residual
may distinguish auxiliary readings over the same configuration. -/
theorem auxiliarySensitiveEquationSystem_not_configurationInvariant
    (C : Site.ContextPreorderCategory FiniteModel.object) :
    ¬ EquationResidualConfigurationInvariant
      (auxiliarySensitiveEquationSystem C) := by
  intro invariant
  have residual_eq := invariant
    (Site.ContextCategoryObject.of C FiniteModel.equationProbeContext)
    finiteAxisFoldUnitObject finiteAxisFoldBoolObject PUnit.unit
    FiniteModel.FiniteAtom.componentA
    (finiteAxisFoldEraseObject_configuration FiniteModel.object)
  simp [auxiliarySensitiveEquationSystem,
    finiteAxisFoldUnitObject_ne_boolObject] at residual_eq

/-- The finite NoCycle residual has configuration-only dependence. -/
theorem finiteEquationResidual_configurationInvariant
    (C : Site.ContextPreorderCategory FiniteModel.object) :
    EquationResidualConfigurationInvariant (FiniteModel.equationSystem C) := by
  intro W first second index atom configuration_eq
  have cycle_eq : FiniteModel.hasDependencyCycle first ↔
      FiniteModel.hasDependencyCycle second := by
    unfold FiniteModel.hasDependencyCycle
    rw [configuration_eq]
  by_cases first_cycle : FiniteModel.hasDependencyCycle first
  · have second_cycle := cycle_eq.mp first_cycle
    simp [FiniteModel.equationSystem, FiniteModel.noCycleResidual,
      first_cycle, second_cycle]
  · have second_cycle : ¬ FiniteModel.hasDependencyCycle second :=
      fun h => first_cycle (cycle_eq.mpr h)
    simp [FiniteModel.equationSystem, FiniteModel.noCycleResidual,
      first_cycle, second_cycle]

/-- Configuration-only residual dependence is preserved by Atom transport. -/
theorem transportEquationResidual_configurationInvariant
    {U : AtomCarrier.{u}} (e : U.Atom ≃ U.Atom)
    (base : ArchitectureObject U) (C : Site.ContextPreorderCategory base)
    (E : ArchitecturalEquationSystem C)
    (hE : EquationResidualConfigurationInvariant E) :
    EquationResidualConfigurationInvariant
      (transportEquationSystem e base C E) := by
  intro W first second index atom configuration_eq
  apply hE
  exact congrArg (fun configuration => configuration.transport e.symm)
    configuration_eq

/-- Configuration-only residual dependence is unchanged by reindexing the
selected equation-reading base object. -/
theorem castEquationResidual_configurationInvariant
    {U : AtomCarrier.{u}} {firstBase secondBase : ArchitectureObject U}
    (base_eq : firstBase = secondBase) (R : EquationReading firstBase)
    (hR : EquationResidualConfigurationInvariant R.equationSystem) :
    EquationResidualConfigurationInvariant
      (castEquationReading base_eq R).equationSystem := by
  cases base_eq
  exact hR

/-- The fixed authored-support package retains configuration-only residuals. -/
theorem finiteAxisFoldSupportPackage_equationResidual_configurationInvariant :
    EquationResidualConfigurationInvariant
      finiteAxisFoldSupportPackage.algebra.equationSystem := by
  apply castEquationResidual_configurationInvariant
  apply transportEquationResidual_configurationInvariant
  simpa [TransportCoherence.finiteWitnessSourcePackage,
    TransportCoherence.finiteWitnessSourceReading,
    FiniteModel.coreReading, FiniteModel.coreReadingFor] using
    finiteEquationResidual_configurationInvariant
      FiniteModel.coreReading.equationReading.contextPreorder

/-- Exact equation transport survives object erasure because the finite residual
depends only on the retained Atom configuration. -/
noncomputable def finiteAxisFoldEraseEquationTransport :
    EquationSystemExactTransport
      finiteAxisFoldSupportPackage.algebra.equationSystem
      finiteAxisFoldSupportPackage.algebra.equationSystem
      (Equiv.refl FiniteModel.carrier.Atom)
      finiteAxisFoldEraseObject where
  contextEquivalence :=
    CategoryTheory.Equivalence.refl
  equationEquiv := Equiv.refl _
  role_eq := by intros; rfl
  observableEquiv := fun _ => RingEquiv.refl _
  observable_naturality := by intros; rfl
  violationCoordinate_eq := by intros; rfl
  equationResidual_eq := by
    intro W object index atom
    exact finiteAxisFoldSupportPackage_equationResidual_configurationInvariant
      W object (finiteAxisFoldEraseObject object) index atom
      (finiteAxisFoldEraseObject_configuration object).symm

/-- Object erasure is an exact endomorphism of the fixed authored-support core. -/
noncomputable def finiteAxisFoldEraseUpper :
    SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage where
    atomEquiv := Equiv.refl _
    extraction_eq := by
      simp
    composition_eq := by intros; simp
    objectMap := finiteAxisFoldEraseObject
    object_formation_eq := by
      intro configuration
      simp [finiteAxisFoldEraseObject, finiteAxisFoldSupportPackage,
        AtomFoundation.transportAlong, AtomFoundation.transportCoreReading,
        AtomFoundation.transportObjectReading,
        AATCorePackage.generate,
        TransportCoherence.finiteWitnessSourcePackage,
        TransportCoherence.finiteWitnessSourceReading,
        FiniteModel.coreReading, FiniteModel.coreReadingFor,
        FiniteModel.objectReading, FiniteModel.objectOfConfiguration]
    configurationMap := fun object =>
      castConfigurationHom rfl
        (finiteAxisFoldEraseObject_configuration object).symm
        (ConfigurationHom.id object.configuration)
    configurationMap_atomMap := by
      intro object
      simpa only using
        (castConfigurationHom_atomMap rfl
          (finiteAxisFoldEraseObject_configuration object).symm
          (ConfigurationHom.id object.configuration))
    configuration_eq := by
      intro object
      rw [finiteAxisFoldEraseObject_configuration]
      exact (AtomFoundation.atomConfiguration_transport_id object.configuration).symm
    equationTransport := finiteAxisFoldEraseEquationTransport
    detectorCode_eq := by
      intro index
      change finiteAxisFoldSupportPackage.algebra.circuits.code index =
        (finiteAxisFoldSupportPackage.algebra.circuits.code index).transport
          (Equiv.refl _)
      exact (CircuitDetectorCode.transport_refl _).symm
    operationMap := by
      intro A B operation
      change ConfigurationHom
        (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm A).configuration
        (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm B).configuration
        at operation
      change ConfigurationHom
        (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
          (finiteAxisFoldEraseObject A)).configuration
        (transportArchitectureObject finiteModelDoctrineFromFixture.atomEquiv.symm
          (finiteAxisFoldEraseObject B)).configuration
      exact castConfigurationHom
        (finiteAxisFoldEraseObject_inverse_configuration A).symm
        (finiteAxisFoldEraseObject_inverse_configuration B).symm operation
    operation_naturality := by
      intro A B operation
      apply ConfigurationHom.ext
      funext atom
      simp [finiteAxisFoldSupportPackage, AtomFoundation.transportAlong,
        AtomFoundation.transportCoreReading,
        AtomFoundation.transportOperationReading,
        AATCorePackage.generate,
        TransportCoherence.finiteWitnessSourcePackage,
        TransportCoherence.finiteWitnessSourceReading,
        FiniteModel.coreReading, FiniteModel.coreReadingFor,
        FiniteModel.operationReading, ConfigurationHom.comp,
        ConfigurationHom.id]
    invariantMap := _root_.id
    invariant_transport := by
      intro index object
      exact Iff.rfl
    axisMap := _root_.id
    coordinateEquiv := fun _ => Equiv.refl _
    axis_selected_iff := fun _ => Iff.rfl
    coordinate_eq := by intros; rfl

/-- The exact object erasure lies over the identity authored-support point. -/
noncomputable def finiteAxisFoldEraseTotal :
    PackageTotalHom finiteAxisFoldSupportPackage finiteAxisFoldSupportPackage where
  base := ExtInstHom.id (packagePoint finiteAxisFoldSupportPackage)
  upper := finiteAxisFoldEraseUpper
  atomEquiv_eq := rfl

/-- Any categorical isomorphism of total packages is injective on objects. -/
theorem packageTotalHom_objectMap_injective_of_isIso
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : P ⟶ Q) [IsIso hom] :
    Function.Injective hom.upper.objectMap := by
  intro first second equality
  have leftInverse (object : ArchitectureObject U) :
      (inv hom).upper.objectMap (hom.upper.objectMap object) = object := by
    have identity := congrArg
      (fun total : PackageTotalHom P P => total.upper.objectMap object)
      (IsIso.hom_inv_id hom)
    exact identity
  calc
    first = (inv hom).upper.objectMap (hom.upper.objectMap first) :=
      (leftInverse first).symm
    _ = (inv hom).upper.objectMap (hom.upper.objectMap second) :=
      congrArg _ equality
    _ = second := leftInverse second

/-- The generated exact endomorphism is not an isomorphism: it identifies the
unit- and Boolean-decorated objects over the same finite configuration. -/
theorem finiteAxisFoldEraseTotal_not_isIso :
    ¬ IsIso (show finiteAxisFoldSupportPackage ⟶
      finiteAxisFoldSupportPackage from finiteAxisFoldEraseTotal) := by
  intro isIso
  letI : IsIso (show finiteAxisFoldSupportPackage ⟶
      finiteAxisFoldSupportPackage from finiteAxisFoldEraseTotal) := isIso
  exact finiteAxisFoldEraseObject_not_injective
    (packageTotalHom_objectMap_injective_of_isIso finiteAxisFoldEraseTotal)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
