import Mathlib.SetTheory.Cardinal.Arithmetic
import ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationCounterexample
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct

universe w

/-!
# Finite operation-reference obstruction

This file isolates a concrete obstruction that a common G-123 operation grammar must
avoid. The semantic package below has an opaque sequence tag on every operation.
Every transformation of sequence tags gives an actual package endomorphism, while a
finite list of sequence-tag references cannot enumerate all such transformations.

The result concerns this candidate finite-reference grammar. It does not assert that
the package belongs to the still-unconstructed admissible class `D_Theta`, and hence
does not refute the fixed G-123 target.
-/

abbrev OperationTag := Nat → Bool

def operationTagNot (tag : OperationTag) : OperationTag :=
  fun index => !tag index

theorem operationTagNot_ne (tag : OperationTag) : operationTagNot tag ≠ tag := by
  intro equality
  have pointEquality := congrFun equality 0
  simp [operationTagNot] at pointEquality

def operationTransformDiagonal
    (enumeration : OperationTag → (OperationTag → OperationTag)) :
    OperationTag → OperationTag :=
  fun tag => operationTagNot (enumeration tag tag)

theorem operationTransformDiagonal_ne
    (enumeration : OperationTag → (OperationTag → OperationTag)) (tag : OperationTag) :
    operationTransformDiagonal enumeration ≠ enumeration tag := by
  intro equality
  exact operationTagNot_ne _ (congrFun equality tag)

theorem operationTags_not_surjective_transformations
    (enumeration : OperationTag → (OperationTag → OperationTag)) :
    ¬ Function.Surjective enumeration := by
  intro surjective
  obtain ⟨tag, equality⟩ := surjective (operationTransformDiagonal enumeration)
  exact operationTransformDiagonal_ne enumeration tag equality.symm

noncomputable def listOperationTagEmbedding : List OperationTag ↪ OperationTag :=
  Classical.choice ((Cardinal.lift_mk_le.{0}).mp (by simp))

noncomputable def operationTagListEnumeration : OperationTag → List OperationTag :=
  Function.invFun listOperationTagEmbedding

theorem operationTagListEnumeration_surjective :
    Function.Surjective operationTagListEnumeration :=
  (Function.leftInverse_invFun listOperationTagEmbedding.injective).surjective

theorem listOperationTags_not_surjective_transformations
    (decode : List OperationTag → (OperationTag → OperationTag)) :
    ¬ Function.Surjective decode := by
  intro surjective
  exact operationTags_not_surjective_transformations
    (decode ∘ operationTagListEnumeration)
    (surjective.comp operationTagListEnumeration_surjective)

noncomputable def sequenceTaggedOperationPackage :
    AATCorePackage FiniteModel.carrier where
  axioms := taggedOperationPackage.axioms
  reading := {
    taggedOperationPackage.reading with
    operationReading := {
      Op := fun first second =>
        taggedOperationPackage.reading.operationReading.Op first second × OperationTag
      configurationMap := fun operation =>
        taggedOperationPackage.reading.operationReading.configurationMap operation.1 } }

noncomputable def sequenceTaggedBoolOperation (tag : OperationTag) :
    sequenceTaggedOperationPackage.reading.operationReading.Op
      finiteAxisFoldBoolObject finiteAxisFoldBoolObject :=
  (taggedBoolOperation, tag)

noncomputable def sequenceTransformUpper (transform : OperationTag → OperationTag) :
    SignedExactCoreReadingHom sequenceTaggedOperationPackage
      sequenceTaggedOperationPackage :=
  { SignedExactCoreReadingHom.refl sequenceTaggedOperationPackage with
    operationMap := fun operation => (operation.1, transform operation.2)
    operation_naturality := by
      intro first second operation
      change ConfigurationHom.comp
          (taggedOperationPackage.reading.operationReading.configurationMap operation.1)
          (ConfigurationHom.id first.configuration) =
        ConfigurationHom.comp
          (ConfigurationHom.id second.configuration)
          (taggedOperationPackage.reading.operationReading.configurationMap operation.1)
      apply ConfigurationHom.ext
      rfl }

noncomputable def sequenceTransformTotal (transform : OperationTag → OperationTag) :
    PackageTotalHom sequenceTaggedOperationPackage sequenceTaggedOperationPackage where
  base := ExtInstHom.id (packagePoint sequenceTaggedOperationPackage)
  upper := sequenceTransformUpper transform
  atomEquiv_eq := rfl

noncomputable def readSequenceTransform
    (total : PackageTotalHom sequenceTaggedOperationPackage sequenceTaggedOperationPackage) :
    OperationTag → OperationTag :=
  fun tag => (total.upper.operationMap (sequenceTaggedBoolOperation tag)).2

@[simp] theorem readSequenceTransform_sequenceTransformTotal
    (transform : OperationTag → OperationTag) :
    readSequenceTransform (sequenceTransformTotal transform) = transform :=
  rfl

theorem sequenceTransformTotal_injective :
    Function.Injective sequenceTransformTotal := by
  intro first second equality
  have readEquality := congrArg readSequenceTransform equality
  simpa using readEquality

theorem sequencePackageEndomorphisms_not_listTagEnumerable
    (decode : List OperationTag →
      PackageTotalHom sequenceTaggedOperationPackage sequenceTaggedOperationPackage) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  have transformSurjective :
      Function.Surjective (readSequenceTransform ∘ decode) := by
    intro transform
    obtain ⟨code, equality⟩ := decodeSurjective (sequenceTransformTotal transform)
    exact ⟨code, by simp [equality]⟩
  exact listOperationTags_not_surjective_transformations _ transformSurjective

theorem no_surjectiveEndomorphismDecoder_of_listGeneratedCode
    {Code : Type w}
    (ofList : List OperationTag → Code)
    (ofList_surjective : Function.Surjective ofList)
    (decode : Code →
      PackageTotalHom sequenceTaggedOperationPackage sequenceTaggedOperationPackage) :
    ¬ Function.Surjective decode := by
  intro decodeSurjective
  exact sequencePackageEndomorphisms_not_listTagEnumerable (decode ∘ ofList)
    (decodeSurjective.comp ofList_surjective)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
