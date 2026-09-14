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

/-- Cycle 11 semantic-family constructor for fixed GOAL C: on the exact
mandatory-C reading, change only the invisible Boolean operation tag at
sources selected by the unrestricted predicate `choice`.  This is the upper
component used by `taggedSourceChoiceTotal`; the package and its operation
endpoints come from the accepted mandatory-C input, while `choice` is the
family being embedded rather than a presentation certificate. -/
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

/-- Cycle 11's principal semantic constructor: lift
`taggedSourceChoiceUpper` to an actual ambient `PackageTotalHom` of the fixed
mandatory-C package over its identity extraction map.  Its premise is only
the arbitrary source predicate; membership in a future `D_Theta` or `R_Theta`
is deliberately not supplied or asserted here. -/
noncomputable def taggedSourceChoiceTotal
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    PackageTotalHom taggedOperationPackage taggedOperationPackage where
  base := ExtInstHom.id (packagePoint taggedOperationPackage)
  upper := taggedSourceChoiceUpper choice
  atomEquiv_eq := rfl

/-- Readback API witness for Cycle 11: the accepted mandatory-C operation
family supplies a tagged identity operation at each architecture-object
source.  It is used by `readTaggedSourceChoice` to test every endpoint, so
injectivity is not inferred only from the single fixed uniform-flip example. -/
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

/-- Cycle 11 readback map from ambient mandatory-C endomorphisms to full source
predicates.  It evaluates the endomorphism on `taggedIdentityOperation` at
every source; the domain is intentionally the ambient `PackageTotalHom`, not
the still-unconstructed morphism type of `R_Theta`. -/
noncomputable def readTaggedSourceChoice
    (total : PackageTotalHom taggedOperationPackage taggedOperationPackage) :
    ArchitectureObject FiniteModel.carrier → Bool :=
  fun source => (total.upper.operationMap (taggedIdentityOperation source)).2

/-- Left-inverse theorem for the Cycle 11 constructor/readback pair.  From the
fixed package operations and an arbitrary source predicate, evaluation at
each tagged identity recovers that predicate pointwise; this is the proof-use
that prevents the semantic family from collapsing to the uniform flip. -/
@[simp] theorem readTaggedSourceChoice_taggedSourceChoiceTotal
    (choice : ArchitectureObject FiniteModel.carrier → Bool) :
    readTaggedSourceChoice (taggedSourceChoiceTotal choice) = choice := by
  funext source
  change (if choice source then true else false) = choice source
  cases choice source <;> rfl

/-- Cycle 11 semantic-family embedding theorem.  It derives injectivity of
`taggedSourceChoiceTotal` from the preceding constructed left inverse, with no
decoder, fullness, or future comparison-law membership as an input premise. -/
theorem taggedSourceChoiceTotal_injective :
    Function.Injective taggedSourceChoiceTotal := by
  intro first second equality
  have readEquality := congrArg readTaggedSourceChoice equality
  simpa using readEquality

/-- Generic cardinal API used in the Cycle 11 obstruction: form Cantor's
diagonal Boolean predicate against a proposed self-indexed enumeration.  The
arbitrary type and enumeration are auxiliary logical inputs, independent of
the fixed AAT package. -/
def objectChoiceDiagonal
    {Object : Type*} (enumeration : Object → (Object → Bool)) :
    Object → Bool :=
  fun object => !(enumeration object object)

/-- Pointwise API lemma for `objectChoiceDiagonal`: at the supplied index the
diagonal predicate differs from the candidate enumerand.  This is the local
contradiction consumed by `objects_not_surjective_choices`; it has no AAT
premise. -/
theorem objectChoiceDiagonal_ne
    {Object : Type*} (enumeration : Object → (Object → Bool)) (object : Object) :
    objectChoiceDiagonal enumeration ≠ enumeration object := by
  intro equality
  have pointEquality := congrFun equality object
  simp [objectChoiceDiagonal] at pointEquality

/-- Generic Cantor no-surjection lemma used as the cardinal core of Cycle 11.
It discharges its conclusion from an arbitrary proposed enumeration using
`objectChoiceDiagonal_ne`; it does not assume finiteness or any decoder law. -/
theorem objects_not_surjective_choices
    {Object : Type*} (enumeration : Object → (Object → Bool)) :
    ¬ Function.Surjective enumeration := by
  intro surjective
  obtain ⟨object, equality⟩ := surjective (objectChoiceDiagonal enumeration)
  exact objectChoiceDiagonal_ne enumeration object equality.symm

/-- AAT-specific cardinal witness for Cycle 11: construct an architecture
object for each natural number using the fixed finite-model configuration and
`StructureMaps := Fin (index + 1)`.  This supplies data for proving the full
mandatory-C source-object type infinite, rather than taking infinitude as a
new premise. -/
noncomputable def naturalArchitectureObject (index : Nat) :
    ArchitectureObject FiniteModel.carrier where
  configuration := FiniteModel.object.configuration
  StructureMaps := Fin (index + 1)
  SelectedQuantities := PUnit
  structureMaps := ⟨0, Nat.succ_pos index⟩
  selectedQuantities := PUnit.unit

/-- Injectivity API for `naturalArchitectureObject`.  The proof reads the
authored `StructureMaps` type back through its finite cardinality, providing
the premise required by `architectureObjectInfinite` from the constructed AAT
objects themselves. -/
theorem naturalArchitectureObject_injective :
    Function.Injective naturalArchitectureObject := by
  intro first second equality
  have typeEquality := congrArg ArchitectureObject.StructureMaps equality
  have cardinalEquality := congrArg Cardinal.mk typeEquality
  change Cardinal.mk (Fin (first + 1)) = Cardinal.mk (Fin (second + 1)) at cardinalEquality
  simpa using cardinalEquality

/-- Cycle 11 infinitude instance for the exact mandatory-C source-object type,
derived from `naturalArchitectureObject_injective`.  Its role is solely to
invoke the standard finite-list cardinal embedding below; it is not a new
assumption on the fixed GOAL input. -/
noncomputable instance architectureObjectInfinite :
    Infinite (ArchitectureObject FiniteModel.carrier) :=
  Infinite.of_injective naturalArchitectureObject naturalArchitectureObject_injective

/-- Cardinal bridge for the Cycle 11 object-list candidate grammar.  The
standard list-cardinal theorem and the proved `architectureObjectInfinite`
construct an embedding of finite source-object reference lists back into the
source-object type; no enumeration or completed semantic map is stored in the
grammar. -/
noncomputable def listArchitectureObjectEmbedding :
    List (ArchitectureObject FiniteModel.carrier) ↪
      ArchitectureObject FiniteModel.carrier :=
  Classical.choice ((Cardinal.lift_mk_le.{0}).mp (by simp))

/-- API construction turning `listArchitectureObjectEmbedding` into an
architecture-object-indexed enumeration of all finite object-reference lists.
It is an auxiliary reindexing for Cantor diagonalization, not the proposed
presentation decoder and not a premise imported from the fixed GOAL. -/
noncomputable def architectureObjectListEnumeration :
    ArchitectureObject FiniteModel.carrier →
      List (ArchitectureObject FiniteModel.carrier) :=
  Function.invFun listArchitectureObjectEmbedding

/-- Surjectivity API for `architectureObjectListEnumeration`, proved from the
left inverse of the constructed list embedding.  This discharged fact is used
to transfer a hypothetical list decoder to the self-indexed enumeration
required by `objects_not_surjective_choices`. -/
theorem architectureObjectListEnumeration_surjective :
    Function.Surjective architectureObjectListEnumeration :=
  (Function.leftInverse_invFun listArchitectureObjectEmbedding.injective).surjective

/-- First Cycle 11 no-go theorem: no decoder whose entire code is a finite list
of mandatory-C source-object references reaches every Boolean source
predicate.  It combines the constructed list enumeration with Cantor's lemma;
the restriction to this candidate reference alphabet is part of the
conclusion's scope. -/
theorem listArchitectureObjects_not_surjective_choices
    (decode : List (ArchitectureObject FiniteModel.carrier) →
      (ArchitectureObject FiniteModel.carrier → Bool)) :
    ¬ Function.Surjective decode := by
  intro surjective
  exact objects_not_surjective_choices
    (decode ∘ architectureObjectListEnumeration)
    (surjective.comp architectureObjectListEnumeration_surjective)

/-- Principal Cycle 11 obstruction for the fixed GOAL C package: a decoder
from finite source-object reference lists cannot be full onto all ambient
`PackageTotalHom` endomorphisms.  The proof actually uses the source-choice
constructor and its readback to transfer hypothetical semantic surjectivity to
the preceding predicate no-go; it makes no claim about future `R_Theta` Hom. -/
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

/-- Conditional Cycle 11 API for another code type.  The additional premise
`ofList_surjective` must be discharged by an independently constructed syntax
to show that its codes are generated by finite mandatory-C object references;
only then does the principal list obstruction rule out a surjective ambient
endomorphism decoder.  Richer primitive-reference alphabets remain outside
this theorem. -/
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
