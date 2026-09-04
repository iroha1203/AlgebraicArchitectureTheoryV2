import ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationBlocker
import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredCanonicalObjectNormalizationWitnesses

/-!
# G-117 full-subcategory naturality counterexample

The finite normalization witness is extended by a Boolean tag on every
operation.  Configuration realization forgets the tag, so the resulting
package remains normalization-admissible.  An exact endomorphism may therefore
flip the invisible tag according to the source architecture object while still
satisfying every existing configuration-level naturality law.

## Implementation notes

The tag extension keeps the fixed finite Atom, equation, invariant, signature,
and object readings unchanged.  It is used because `OperationReading` does not
require its `configurationMap` to be injective.  The endpoint-dependent flip is
an actual `PackageTotalHom` and then an actual morphism in the full admissible
fiber; it is not a supplied failure certificate.  Evaluating at the reviewed
Boolean-decorated object separates the two composite operation maps by the
Boolean values `false` and `true`.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

noncomputable local instance taggedArchitectureObjectDecidableEq :
    DecidableEq (ArchitectureObject FiniteModel.carrier) := Classical.decEq _

/-- A product cast retains the first component up to the original cast. -/
theorem taggedOperationCast_fst {alpha beta : Type} (equality : alpha = beta)
    (value : alpha × Bool) :
    (cast (congrArg (fun operationType => operationType × Bool) equality) value).1 =
      cast equality value.1 := by
  cases equality
  rfl

/-- The reviewed finite package with one configuration-invisible Boolean tag
adjoined to every selected operation. -/
noncomputable def taggedOperationPackage :
    AATCorePackage FiniteModel.carrier where
  axioms := finiteAxisFoldSupportPackage.axioms
  reading := {
    finiteAxisFoldSupportPackage.reading with
    operationReading := {
      Op := fun first second =>
        finiteAxisFoldSupportPackage.reading.operationReading.Op first second × Bool
      configurationMap := fun operation =>
        finiteAxisFoldSupportPackage.reading.operationReading.configurationMap operation.1
    }
  }

/-- Adding the invisible operation tag does not change canonical object
normalization. -/
theorem taggedOperationPackage_normalization
    (object : ArchitectureObject FiniteModel.carrier) :
    canonicalObjectNormalization taggedOperationPackage object =
      canonicalObjectNormalization finiteAxisFoldSupportPackage object := by
  rfl

/-- The tagged operation family is unchanged by canonical normalization of its
two endpoint objects. -/
theorem taggedOperationPackage_operationTypeEq
    (first second : ArchitectureObject FiniteModel.carrier) :
    taggedOperationPackage.reading.operationReading.Op first second =
      taggedOperationPackage.reading.operationReading.Op
        (canonicalObjectNormalization taggedOperationPackage first)
        (canonicalObjectNormalization taggedOperationPackage second) := by
  exact congrArg (fun operationType => operationType × Bool)
    (finiteCanonicalObjectNormalization_admissible.operation_type_eq first second)

/-- The first component of tagged-operation normalization is the reviewed
finite operation cast. -/
theorem taggedOperationPackage_operationCast_fst
    {first second : ArchitectureObject FiniteModel.carrier}
    (operation : taggedOperationPackage.reading.operationReading.Op first second) :
    (cast (taggedOperationPackage_operationTypeEq first second) operation).1 =
      cast
        (finiteCanonicalObjectNormalization_admissible.operation_type_eq
          first second) operation.1 := by
  let source_eq :=
    finiteCanonicalObjectNormalization_admissible.operation_type_eq first second
  change (cast (congrArg (fun operationType => operationType × Bool) source_eq)
    operation).1 = cast source_eq operation.1
  exact taggedOperationCast_fst source_eq operation

/-- The tagged package satisfies every canonical-normalization admissibility
field because all semantic readings use the unchanged first operation
component. -/
theorem taggedOperationPackage_admissible :
    CanonicalObjectNormalizationAdmissible taggedOperationPackage where
  equationResidual_eq := by
    simpa [taggedOperationPackage] using
      finiteCanonicalObjectNormalization_admissible.equationResidual_eq
  operation_type_eq := taggedOperationPackage_operationTypeEq
  operation_naturality := by
    intro first second operation
    change ConfigurationHom.comp
        (finiteAxisFoldSupportPackage.reading.operationReading.configurationMap
          (cast (taggedOperationPackage_operationTypeEq first second) operation).1)
        (canonicalObjectNormalizationConfigurationHom
          finiteAxisFoldSupportPackage first) =
      ConfigurationHom.comp
        (canonicalObjectNormalizationConfigurationHom
          finiteAxisFoldSupportPackage second)
        (finiteAxisFoldSupportPackage.reading.operationReading.configurationMap
          operation.1)
    rw [taggedOperationPackage_operationCast_fst]
    exact finiteCanonicalObjectNormalization_admissible.operation_naturality
      first second operation.1
  invariant_transport := by
    simpa [taggedOperationPackage] using
      finiteCanonicalObjectNormalization_admissible.invariant_transport
  coordinate_eq := by
    simpa [taggedOperationPackage] using
      finiteCanonicalObjectNormalization_admissible.coordinate_eq

/-- An exact core endomorphism that flips the invisible operation tag exactly
at the Boolean-decorated source endpoint. -/
noncomputable def taggedEndpointFlipUpper :
    SignedExactCoreReadingHom taggedOperationPackage taggedOperationPackage :=
  { SignedExactCoreReadingHom.refl taggedOperationPackage with
    operationMap := fun {first _second} operation =>
      (operation.1,
        if first = finiteAxisFoldBoolObject then !operation.2 else operation.2)
    operation_naturality := by
      intro first second operation
      change ConfigurationHom.comp
          (finiteAxisFoldSupportPackage.reading.operationReading.configurationMap
            operation.1)
          (ConfigurationHom.id first.configuration) =
        ConfigurationHom.comp
          (ConfigurationHom.id second.configuration)
          (finiteAxisFoldSupportPackage.reading.operationReading.configurationMap
            operation.1)
      apply ConfigurationHom.ext
      rfl
  }

/-- The endpoint-dependent flip as a genuine package total endomorphism over
the identity extraction point. -/
noncomputable def taggedEndpointFlipTotal :
    PackageTotalHom taggedOperationPackage taggedOperationPackage where
  base := ExtInstHom.id (packagePoint taggedOperationPackage)
  upper := taggedEndpointFlipUpper
  atomEquiv_eq := rfl

/-- The test operation at the Boolean-decorated endpoint, with initial tag
`false`. -/
noncomputable def taggedBoolOperation :
    taggedOperationPackage.reading.operationReading.Op
      finiteAxisFoldBoolObject finiteAxisFoldBoolObject := by
  refine ⟨?_, false⟩
  change ConfigurationHom
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm finiteAxisFoldBoolObject).configuration
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm finiteAxisFoldBoolObject).configuration
  exact ConfigurationHom.id _

/-- The canonical normalization sends the Boolean-decorated object to the
reviewed unit-decorated object. -/
theorem taggedBoolNormalization_eq_unit :
    canonicalObjectNormalization taggedOperationPackage finiteAxisFoldBoolObject =
      finiteAxisFoldUnitObject := by
  rw [taggedOperationPackage_normalization,
    finiteCanonicalObjectNormalization_eq_erase]
  unfold finiteAxisFoldUnitObject
  apply finiteAxisFoldEraseObject_eq_of_configuration
  exact finiteAxisFoldBoolObject_configuration

/-- A product cast leaves the Boolean tag unchanged. -/
theorem taggedOperationCast_snd {alpha beta : Type} (equality : alpha = beta)
    (value : alpha × Bool) :
    (cast (congrArg (fun operationType => operationType × Bool) equality) value).2 =
      value.2 := by
  cases equality
  rfl

/-- The tagged normalization cast leaves the Boolean operation tag unchanged. -/
theorem taggedNormalizationCast_snd
    {first second : ArchitectureObject FiniteModel.carrier}
    (operation : taggedOperationPackage.reading.operationReading.Op first second) :
    (cast (taggedOperationPackage_operationTypeEq first second) operation).2 =
      operation.2 := by
  let source_eq :=
    finiteCanonicalObjectNormalization_admissible.operation_type_eq first second
  change (cast (congrArg (fun operationType => operationType × Bool) source_eq)
    operation).2 = operation.2
  exact taggedOperationCast_snd source_eq operation

/-- The actual total normalization also preserves the Boolean operation tag. -/
theorem taggedCanonicalNormalizationOperation_snd
    {first second : ArchitectureObject FiniteModel.carrier}
    (operation : taggedOperationPackage.reading.operationReading.Op first second) :
    ((canonicalObjectNormalizationTotal taggedOperationPackage
      taggedOperationPackage_admissible).upper.operationMap operation).2 =
      operation.2 := by
  change (cast
    (taggedOperationPackage_admissible.operation_type_eq first second)
      operation).2 = operation.2
  have proof_equality :
      taggedOperationPackage_admissible.operation_type_eq first second =
        taggedOperationPackage_operationTypeEq first second :=
    Subsingleton.elim _ _
  rw [proof_equality]
  exact taggedNormalizationCast_snd operation

/-- Normalizing first moves the source away from the flip endpoint, so the
left composite evaluates the test tag to `false`. -/
theorem taggedLeftComposite_snd :
    (((canonicalObjectNormalizationTotal taggedOperationPackage
      taggedOperationPackage_admissible).comp taggedEndpointFlipTotal).upper.operationMap
        taggedBoolOperation).2 = false := by
  simp only [PackageTotalHom.comp, SignedExactCoreReadingHom.comp,
    taggedEndpointFlipTotal, taggedEndpointFlipUpper]
  change (if canonicalObjectNormalization taggedOperationPackage
      finiteAxisFoldBoolObject = finiteAxisFoldBoolObject then
        !(cast (taggedOperationPackage_operationTypeEq
          finiteAxisFoldBoolObject finiteAxisFoldBoolObject)
            taggedBoolOperation).2
      else
        (cast (taggedOperationPackage_operationTypeEq
          finiteAxisFoldBoolObject finiteAxisFoldBoolObject)
            taggedBoolOperation).2) = false
  rw [taggedNormalizationCast_snd, taggedBoolNormalization_eq_unit]
  simp [finiteAxisFoldUnitObject_ne_boolObject, taggedBoolOperation]

/-- Flipping first changes the test tag to `true`, which normalization then
preserves. -/
theorem taggedRightComposite_snd :
    ((taggedEndpointFlipTotal.comp
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible)).upper.operationMap
        taggedBoolOperation).2 = true := by
  simp only [PackageTotalHom.comp, SignedExactCoreReadingHom.comp,
    taggedEndpointFlipTotal, taggedEndpointFlipUpper]
  rw [taggedCanonicalNormalizationOperation_snd]
  simp [taggedBoolOperation]

/-- The endpoint flip fails the exact operation-map coherence isolated in
Cycle 3. -/
theorem taggedEndpointFlip_not_coherent :
    ¬ CanonicalNormalizationOperationCoherent taggedEndpointFlipTotal
      taggedOperationPackage_admissible taggedOperationPackage_admissible := by
  intro coherent
  unfold CanonicalNormalizationOperationCoherent at coherent
  have function_equality := eq_of_heq coherent
  have operation_equality := congrFun
    (congrFun (congrFun function_equality finiteAxisFoldBoolObject)
      finiteAxisFoldBoolObject) taggedBoolOperation
  have snd_equality := congrArg Prod.snd operation_equality
  rw [taggedLeftComposite_snd, taggedRightComposite_snd] at snd_equality
  contradiction

/-- The canonical normalization total morphism is not natural with respect to
the endpoint-dependent exact endomorphism. -/
theorem taggedEndpointFlip_not_natural :
    taggedEndpointFlipTotal.comp
        (canonicalObjectNormalizationTotal taggedOperationPackage
          taggedOperationPackage_admissible) ≠
      (canonicalObjectNormalizationTotal taggedOperationPackage
        taggedOperationPackage_admissible).comp taggedEndpointFlipTotal := by
  intro equality
  exact taggedEndpointFlip_not_coherent
    ((canonicalObjectNormalizationTotal_natural_iff_operationCoherent
      taggedEndpointFlipTotal taggedOperationPackage_admissible
      taggedOperationPackage_admissible).mp equality)

/-- The tagged package as an actual object of its full admissible core fiber. -/
noncomputable def taggedAdmCoreFiberObject :
    AdmCoreFiber (packagePoint taggedOperationPackage) :=
  ⟨⟨taggedOperationPackage, rfl⟩, taggedOperationPackage_admissible⟩

/-- The endpoint flip as an actual endomorphism in the full admissible core
fiber. -/
noncomputable def taggedAdmCoreFiberEndomorphism :
    taggedAdmCoreFiberObject ⟶ taggedAdmCoreFiberObject :=
  ObjectProperty.homMk
    ⟨taggedEndpointFlipTotal,
      by
        apply CategoryTheory.IsHomLift.of_commsq
          (packageProjection FiniteModel.carrier)
          (𝟙 (packagePoint taggedOperationPackage))
          taggedEndpointFlipTotal rfl rfl
        rw [packageProjection_map]
        exact Category.id_comp _⟩

/-- In the full admissible fiber, the endpoint flip does not commute with the
proposed canonical-normalization component. -/
theorem taggedAdmCoreFiberComponent_not_natural :
    taggedAdmCoreFiberEndomorphism ≫
        admissibleCanonicalNormalizationComponent taggedAdmCoreFiberObject ≠
      admissibleCanonicalNormalizationComponent taggedAdmCoreFiberObject ≫
        taggedAdmCoreFiberEndomorphism := by
  intro equality
  apply taggedEndpointFlip_not_natural
  exact congrArg (fun hom => hom.hom.1) equality

/-- Fixed counterexample to G-117(c): no endotransformation of the identity on
this full admissible fiber can have all components equal to the prescribed
canonical normalization components. -/
theorem no_taggedAdmissibleCanonicalNormalizationNatTrans :
    ¬ ∃ ν : NatTrans
        (Functor.id (AdmCoreFiber (packagePoint taggedOperationPackage)))
        (Functor.id (AdmCoreFiber (packagePoint taggedOperationPackage))),
      ∀ P, ν.app P = admissibleCanonicalNormalizationComponent P := by
  rintro ⟨ν, component_equality⟩
  apply taggedAdmCoreFiberComponent_not_natural
  have naturality := ν.naturality taggedAdmCoreFiberEndomorphism
  rw [component_equality taggedAdmCoreFiberObject] at naturality
  simpa using naturality

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
