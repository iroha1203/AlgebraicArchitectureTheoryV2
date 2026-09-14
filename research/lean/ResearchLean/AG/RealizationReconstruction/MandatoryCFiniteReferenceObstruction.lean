import ResearchLean.AG.RealizationReconstruction.OperationFiniteReferenceObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Mandatory-C finite operation-reference obstruction

The fixed G-123(C) package already admits far more operation-preserving
endomorphisms than the required uniform flip. Every Boolean-valued predicate
on source architecture objects induces an actual package endomorphism because
the operation reading forgets its Boolean tag. Evaluating at a tagged identity
operation reads the whole predicate back.

Consequently finite lists of architecture-object references, and code types
separately proved to be their surjective images, cannot decode onto all these
endomorphisms. This is an obstruction to that candidate presentation grammar;
it is not by itself a refutation of the fixed G-123 target.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct

/-- The exact mandatory-C upper reading endomorphism whose invisible Boolean
tag changes precisely at sources selected by `choice`. -/
noncomputable def taggedSourceChoiceUpper
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    SignedExactCoreReadingHom taggedOperationPackage taggedOperationPackage :=
  { SignedExactCoreReadingHom.refl taggedOperationPackage with
    operationMap := fun {first _second} operation =>
      (operation.1, if choice first then !operation.2 else operation.2)
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
      rfl }

/-- Lift a source-selected Boolean-tag action to an actual total endomorphism
of the fixed mandatory-C package over its identity extraction map. -/
noncomputable def taggedSourceChoiceTotal
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    PackageTotalHom taggedOperationPackage taggedOperationPackage where
  base := ExtInstHom.id (packagePoint taggedOperationPackage)
  upper := taggedSourceChoiceUpper choice
  atomEquiv_eq := rfl

/-- A tagged identity operation at every architecture-object endpoint, used to
read the source predicate from an ambient package endomorphism. -/
noncomputable def taggedIdentityOperation
    (source : ArchitectureObject FiniteModel.carrier) :
    taggedOperationPackage.reading.operationReading.Op source source := by
  refine ⟨?_, false⟩
  change ConfigurationHom
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm source).configuration
    (transportArchitectureObject
      finiteModelDoctrineFromFixture.atomEquiv.symm source).configuration
  exact ConfigurationHom.id _

/-- Evaluate an ambient mandatory-C package endomorphism on the tagged identity
operation at every possible source endpoint. -/
noncomputable def readTaggedSourceChoice
    (total : PackageTotalHom taggedOperationPackage taggedOperationPackage) :
    ArchitectureObject FiniteModel.carrier → Bool :=
  fun source => (total.upper.operationMap (taggedIdentityOperation source)).2

/-- Reading a source-choice endomorphism recovers the complete original source
predicate, not merely its value at the fixed Boolean example. -/
@[simp] theorem readTaggedSourceChoice_taggedSourceChoiceTotal
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    readTaggedSourceChoice (taggedSourceChoiceTotal choice) = choice := by
  funext source
  change (if choice source then true else false) = choice source
  cases choice source <;> rfl

/-- Distinct full source predicates induce distinct ambient package
endomorphisms of the exact mandatory-C package. -/
theorem taggedSourceChoiceTotal_injective :
    Function.Injective taggedSourceChoiceTotal := by
  intro first second equality
  have readEquality := congrArg readTaggedSourceChoice equality
  simpa using readEquality

/-- Cantor's diagonal Boolean predicate for a proposed enumeration of all
Boolean predicates on an arbitrary object type. -/
def objectChoiceDiagonal
    {Object : Type*} (enumeration : Object → (Object → Bool)) :
    Object → Bool :=
  fun object => !(enumeration object object)

/-- The diagonal predicate differs from the enumerated predicate at its own
index. -/
theorem objectChoiceDiagonal_ne
    {Object : Type*} (enumeration : Object → (Object → Bool)) (object : Object) :
    objectChoiceDiagonal enumeration ≠ enumeration object := by
  intro equality
  have pointEquality := congrFun equality object
  simp [objectChoiceDiagonal] at pointEquality

/-- No type can surject onto its full Boolean predicate space. -/
theorem objects_not_surjective_choices
    {Object : Type*} (enumeration : Object → (Object → Bool)) :
    ¬ Function.Surjective enumeration := by
  intro surjective
  obtain ⟨object, equality⟩ := surjective (objectChoiceDiagonal enumeration)
  exact objectChoiceDiagonal_ne enumeration object equality.symm

/-- An explicit infinite family of architecture objects, distinguished by the
finite cardinality of their authored `StructureMaps` type. -/
noncomputable def naturalArchitectureObject (index : Nat) :
    ArchitectureObject FiniteModel.carrier where
  configuration := FiniteModel.object.configuration
  StructureMaps := Fin (index + 1)
  SelectedQuantities := PUnit
  structureMaps := ⟨0, Nat.succ_pos index⟩
  selectedQuantities := PUnit.unit

/-- The `StructureMaps := Fin (n + 1)` field recovers the natural-number index,
so the explicit architecture-object family is injective. -/
theorem naturalArchitectureObject_injective :
    Function.Injective naturalArchitectureObject := by
  intro first second equality
  have typeEquality := congrArg ArchitectureObject.StructureMaps equality
  have cardinalEquality := congrArg Cardinal.mk typeEquality
  change Cardinal.mk (Fin (first + 1)) = Cardinal.mk (Fin (second + 1)) at cardinalEquality
  simpa using cardinalEquality

/-- The full mandatory-C source-object type is infinite by the explicit
natural-number injection. -/
noncomputable instance architectureObjectInfinite :
    Infinite (ArchitectureObject FiniteModel.carrier) :=
  Infinite.of_injective naturalArchitectureObject naturalArchitectureObject_injective

/-- Finite architecture-object reference lists embed back into the infinite
architecture-object type; no finiteness of the parameter type is assumed. -/
noncomputable def listArchitectureObjectEmbedding :
    List (ArchitectureObject FiniteModel.carrier) ↪
      ArchitectureObject FiniteModel.carrier :=
  Classical.choice ((Cardinal.lift_mk_le.{0}).mp (by simp))

/-- A surjective enumeration of all finite architecture-object reference lists
by architecture objects, obtained from the list embedding. -/
noncomputable def architectureObjectListEnumeration :
    ArchitectureObject FiniteModel.carrier →
      List (ArchitectureObject FiniteModel.carrier) :=
  Function.invFun listArchitectureObjectEmbedding

/-- The inverse-function enumeration covers every finite object-reference
list. -/
theorem architectureObjectListEnumeration_surjective :
    Function.Surjective architectureObjectListEnumeration :=
  (Function.leftInverse_invFun listArchitectureObjectEmbedding.injective).surjective

/-- Finite architecture-object reference lists cannot enumerate all Boolean
predicates on the full source-object type. -/
theorem listArchitectureObjects_not_surjective_choices
    (decode : List (ArchitectureObject FiniteModel.carrier) →
      (ArchitectureObject FiniteModel.carrier → Bool)) :
    ¬ Function.Surjective decode := by
  intro surjective
  exact objects_not_surjective_choices
    (decode ∘ architectureObjectListEnumeration)
    (surjective.comp architectureObjectListEnumeration_surjective)

/-- No decoder from finite object-reference lists reaches every ambient
endomorphism of the exact mandatory-C package. -/
theorem taggedSourceChoiceEndomorphisms_not_listObjectEnumerable
    (decode : List (ArchitectureObject FiniteModel.carrier) →
      PackageTotalHom taggedOperationPackage taggedOperationPackage) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  have choiceSurjective :
      Function.Surjective (readTaggedSourceChoice ∘ decode) := by
    intro choice
    obtain ⟨code, equality⟩ := decodeSurjective (taggedSourceChoiceTotal choice)
    exact ⟨code, by simp [equality]⟩
  exact listArchitectureObjects_not_surjective_choices _ choiceSurjective

/-- The same obstruction applies to a code type only when a surjection from
finite object-reference lists onto that code is separately supplied. -/
theorem no_surjectiveTaggedEndomorphismDecoder_of_listObjectGeneratedCode
    {Code : Type*}
    (ofList : List (ArchitectureObject FiniteModel.carrier) → Code)
    (ofList_surjective : Function.Surjective ofList)
    (decode : Code →
      PackageTotalHom taggedOperationPackage taggedOperationPackage) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  exact taggedSourceChoiceEndomorphisms_not_listObjectEnumerable
    (decode ∘ ofList) (decodeSurjective.comp ofList_surjective)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
