import ResearchLean.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainRecovery
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeEdgelessCriterion
import Formal.Util.AssertStandardAxioms

namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open IndependentGeometryHomPrimitive
namespace TagChangeCommonFiniteBridge
open FiniteApplicationHomDecoders

/-- The common operation graph point tests the actual source-choice bit. -/
theorem tagNativeOperationPoint_eq_choice (choice : ArchitectureObject FiniteModel.carrier → Bool)
    (source : ArchitectureObject FiniteModel.carrier) :
    tagNativeOperationPoint choice source = choice source := by
  classical
  let F := taggedSourceChoiceExplicitExactGeometryHom choice
  let f := F.base
  let a := F.coefficientHom
  let raw := IndependentGeometryHomPrimitive.ExplicitRaw.readRaw F.base F.coefficientHom F.raw
  let realization := IndependentGeometryHomPrimitive.NativeReader.explicitRealizationRead F.base F.realization
  let h := IndependentGeometryHomPrimitive.NativeReader.readWith Mode.explicit f a raw realization
  have ho := IndependentGeometryHomPrimitive.NativeReader.readWith_object_rows Mode.explicit f a raw realization
  have hl := IndependentGeometryHomPrimitive.NativeReader.readWith_operation_rows Mode.explicit f a raw realization
  have hobj := IndependentGeometryHomPrimitive.NativeReader.readWith_object_assemble Mode.explicit f a raw realization
  have hmap := IndependentGeometryHomPrimitive.NativeReader.readWith_operation_assemble_heq Mode.explicit f a raw realization
  let S := taggedOperationGeometryPackage.core.reading.operationReading.Op
  let β := fun (objectMap : ArchitectureObject FiniteModel.carrier → ArchitectureObject FiniteModel.carrier) =>
    ∀ A B, S A B → S (objectMap A) (objectMap B)
  have hσ : (⟨CoreLaws.objectMap h ho, Operation.assemble h ho S S hl⟩ : Sigma β) =
      ⟨f.upper.objectMap, fun A B => f.upper.operationMap (A := A) (B := B)⟩ :=
    Sigma.ext hobj hmap
  let eval : Sigma β → Sigma (fun p : ArchitectureObject FiniteModel.carrier × ArchitectureObject FiniteModel.carrier => S p.1 p.2) :=
    fun z => ⟨(z.1 source, z.1 source), z.2 source source (taggedIdentityOperation source)⟩
  have hσv := congrArg eval hσ
  have hval : HEq
      (Operation.assemble h ho S S hl source source (taggedIdentityOperation source))
      (f.upper.operationMap (taggedIdentityOperation source)) :=
    (Sigma.mk.inj_iff.mp hσv).2
  have hobj_src : CoreLaws.objectMap h ho source = source := by
    rw [hobj]
    rfl
  have hf_src : f.upper.objectMap source = source := rfl
  have htype : S (CoreLaws.objectMap h ho source) (CoreLaws.objectMap h ho source) =
      S source source := congrArg₂ S hobj_src hobj_src
  have hcast : cast htype (Operation.assemble h ho S S hl source source
      (taggedIdentityOperation source)) = f.upper.operationMap (taggedIdentityOperation source) := by
    apply eq_of_heq
    exact (cast_heq htype _).trans hval
  have hp : Operation.endpoints h (source, source) (source, source) = true := by
    simpa only [hobj_src] using
      (Operation.Point.endpoints_point h ho source source)
  have he : (CoreLaws.objectMap h ho source, CoreLaws.objectMap h ho source) =
      (source, source) := by simp only [hobj_src]
  have hat : Operation.Point.atPair h S S hl (source, source) (source, source) hp
      (taggedIdentityOperation source) =
      f.upper.operationMap (taggedIdentityOperation source) := by
    have hh := Operation.Point.atPair_cast h S S hl (source, source)
      (CoreLaws.objectMap h ho source, CoreLaws.objectMap h ho source)
      (source, source) he (Operation.Point.endpoints_point h ho source source)
      hp (taggedIdentityOperation source)
    rw [← Operation.Point.assemble_eq_atPair h S S hl ho source source
      (taggedIdentityOperation source)] at hh
    simpa only [htype] using hh.symm.trans hcast
  have hquery : tagNativeOperationPoint choice source =
      h (.operation source source source source
        (.edge (S source source) (S source source)
          (taggedIdentityOperation source) ((taggedIdentityOperation source).1, true))) := rfl
  apply Bool.eq_iff_iff.mpr
  rw [hquery]
  rw [Operation.Point.forward_iff h S S hl (source, source) (source, source) hp
    (taggedIdentityOperation source) ((taggedIdentityOperation source).1, true), hat]
  simp [f, F, taggedSourceChoiceTotal, taggedSourceChoiceUpper, taggedIdentityOperation]
  constructor
  · intro hEq
    exact congrArg Prod.snd hEq
  · intro hBool
    rw [hBool]
/-- The same bit is decoded from the main local Hom operation query. -/
theorem decodeTagAt_read_choice
    (choice : ArchitectureObject FiniteModel.carrier → Bool)
    (source : ArchitectureObject FiniteModel.carrier) :
    decodeTagAt source
        (localHomTable (.geometry FiniteModel.carrier Mode.explicit)
          ((reading (.geometry FiniteModel.carrier Mode.explicit)).map
            (taggedSourceChoiceNativeHom choice))) = choice source := by
  rw [← tagPoint_read]
  exact tagNativeOperationPoint_eq_choice choice source

private abbrev TagParameter : Parameter.{0, 0} :=
  .geometry FiniteModel.carrier Mode.explicit

/-- Every coherent family has its original bit at the main local Hom's
operation point, using the same J as the inverse-limit recovery. -/
theorem decodeTagAt_J
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) :
    decodeTagAt source (localHomTable TagParameter (TagChangeMainRecovery.J family)) =
      TagChange.assemble family source := by
  rw [TagChangeMainRecovery.J_eq_read_assembled]
  exact decodeTagAt_read_choice (TagChange.assemble family) source

/-- The D pointwise permutation reading and the common main Hom operation
reading return the same Bool member of this one coherent tagged family. -/
theorem edgeless_readAt_eq_main_operation
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) :
    TagChangeEdgelessCriterion.boolPermMulEquiv
      (FinitePermutationReadingCriteria.readAt
        TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity
        (TagChangeEdgelessCriterion.edgelessChangeOfChoice
          (TagChange.assemble family)) source) =
      Multiplicative.ofAdd
        (decodeTagAt source
          (localHomTable TagParameter (TagChangeMainRecovery.J family))) := by
  rw [TagChangeEdgelessCriterion.edgeless_readAt_code, decodeTagAt_J]

/-- No finite collection of the actual main Hom operation-point queries
separates all members of the same tagged local section family. -/
theorem finite_operation_points_not_separating
    (S : Finset TagChange.TaggedArchitectureIndex) :
    ∃ family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex,
      TagChangeMainRecovery.J family ≠
        TagChangeMainRecovery.J (TagChange.read (fun _ => false)) ∧
      ∀ source ∈ S,
        decodeTagAt source (localHomTable TagParameter (TagChangeMainRecovery.J family)) =
          decodeTagAt source
            (localHomTable TagParameter
              (TagChangeMainRecovery.J (TagChange.read (fun _ => false)))) := by
  obtain ⟨family, hne, hagree⟩ := TagChangeMainRecovery.finite_J_not_separating S
  refine ⟨family, hne, ?_⟩
  intro source hsource
  rw [decodeTagAt_J, decodeTagAt_J]
  simpa only [TagChange.assemble_read] using hagree source hsource

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCommonFiniteBridge
end TagChangeCommonFiniteBridge
end AAT.AG.LocalSemanticReconstruction
