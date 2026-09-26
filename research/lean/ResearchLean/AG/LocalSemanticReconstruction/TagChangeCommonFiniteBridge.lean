import ResearchLean.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeMainRecovery
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeEdgelessCriterion
import Formal.Util.AssertStandardAxioms

/-! Relate finite D readings to operation queries in the fixed main local Hom.

Implementation notes: the bridge reads the existing operation point of the
native source-choice morphism through `J`. Its determining-predicate transfer
uses equivalences of the full coherent-family and preserving-change domains
and of their Bool-permutation values. This avoids restricting either family
to a finite presentation of the tagged source index. -/

namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open IndependentGeometryHomPrimitive
namespace TagChangeCommonFiniteBridge
open FiniteApplicationHomDecoders

/-- Transport the complete `Determining` predicate across equivalent global
families and pointwise equivalent reading values. This supplies the reusable
finite-reading step for the fixed J-to-D comparison. -/
private theorem determining_equiv
    {A B V W I : Type*} (global : A ≃ B) (value : V ≃ W)
    (readA : A → I → V) (readB : B → I → W)
    (hread : ∀ a i, readB (global a) i = value (readA a i))
    (S : Finset I) :
    FiniteReading.Determining readA S (fun _ => True) ↔
      FiniteReading.Determining readB S (fun _ => True) := by
  constructor
  · rintro ⟨hsep, hext⟩
    constructor
    · intro first second htable
      obtain ⟨first, rfl⟩ := global.surjective first
      obtain ⟨second, rfl⟩ := global.surjective second
      apply congrArg global
      apply hsep
      funext x
      apply value.injective
      simpa only [FiniteReading.restrict, ← hread] using congrFun htable x
    · intro table _
      let localTable : {x // x ∈ S} → V := fun x => value.symm (table x)
      obtain ⟨a, ha⟩ := hext localTable True.intro
      refine ⟨global a, ?_⟩
      funext x
      change readB (global a) x.1 = table x
      rw [hread]
      have hv := congrFun ha x
      change readA a x.1 = value.symm (table x) at hv
      rw [hv]
      exact value.apply_symm_apply _
  · rintro ⟨hsep, hext⟩
    constructor
    · intro first second htable
      apply global.injective
      apply hsep
      funext x
      change readB (global first) x.1 = readB (global second) x.1
      rw [hread, hread]
      exact congrArg value (congrFun htable x)
    · intro table _
      let localTable : {x // x ∈ S} → W := fun x => value (table x)
      obtain ⟨b, hb⟩ := hext localTable True.intro
      refine ⟨global.symm b, ?_⟩
      funext x
      change readA (global.symm b) x.1 = table x
      apply value.injective
      rw [← hread, global.apply_symm_apply]
      exact congrFun hb x


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

/-- The fixed main-reading parameter shared with `TagChangeMainRecovery.J`. -/
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

/-- Identify every coherent tagged family with every preserving change of the
edgeless graph, using the existing assembly and the D-domain equivalence. -/
private noncomputable def familyEquivPreserving :
    TagChange.CoherentFamily TagChange.TaggedArchitectureIndex ≃
      PermutationRestriction.PreservingChange TagChangeEdgelessCriterion.graph Bool
        TagChangeEdgelessCriterion.identity :=
  TagChange.globalTagChangeEquivCoherentFamily.symm.trans
    TagChangeEdgelessCriterion.choiceEquivPreserving

/-- Translate an operation-point Bool bit to its full D Bool permutation. -/
private noncomputable def bitEquivPerm : Bool ≃ Equiv.Perm Bool where
  toFun := TagChangeEdgelessCriterion.boolPerm
  invFun permutation := permutation false
  left_inv bit := by cases bit <;> rfl
  right_inv permutation := by
    exact TagChangeEdgelessCriterion.boolPermMulEquiv.left_inv permutation

/-- Pointwise compatibility of the actual J operation reading with D's
permutation reading under the two domain and value equivalences. -/
private theorem main_read_transport
    (family : TagChange.CoherentFamily TagChange.TaggedArchitectureIndex)
    (source : TagChange.TaggedArchitectureIndex) :
    FinitePermutationReadingCriteria.readAt
      TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity
      (familyEquivPreserving family) source =
        bitEquivPerm
          (FiniteApplicationHomDecoders.decodeTagAt source
            (localHomTable TagParameter
              (TagChangeMainRecovery.J family))) := by
  apply TagChangeEdgelessCriterion.boolPermMulEquiv.injective
  change TagChangeEdgelessCriterion.boolPermMulEquiv
      (FinitePermutationReadingCriteria.readAt
        TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity
        (TagChangeEdgelessCriterion.edgelessChangeOfChoice
          (TagChange.assemble family)) source) = _
  rw [TagChangeEdgelessCriterion.edgeless_readAt_code]
  rw [TagChangeCommonFiniteBridge.decodeTagAt_J]
  cases hbit : TagChange.assemble family source <;> rfl

/-- Every finite permutation table is edge coherent because the tagged graph
has no edges; this discharges D's table-side premise in the transfer. -/
private theorem edgeless_edge_coherent
    (S : Finset TagChange.TaggedArchitectureIndex)
    (table : {source // source ∈ S} → Equiv.Perm Bool) :
    FinitePermutationReadingCriteria.EdgeCoherent
      TagChangeEdgelessCriterion.graph Bool S table := by
  intro namedEdge
  exact namedEdge.1.elim

/-- At every finite source selection, the determining predicate for the
actual J operation queries is equivalent to D's determining predicate over
all preserving changes of the edgeless graph. -/
theorem main_operation_determining_iff_D
    (S : Finset TagChange.TaggedArchitectureIndex) :
    FiniteReading.Determining
      (fun family source => FiniteApplicationHomDecoders.decodeTagAt source
        (localHomTable TagParameter
          (TagChangeMainRecovery.J family))) S (fun _ => True) ↔
    FiniteReading.Determining
      (FinitePermutationReadingCriteria.readAt
        TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity) S
      (FinitePermutationReadingCriteria.EdgeCoherent
        TagChangeEdgelessCriterion.graph Bool S) := by
  rw [show FiniteReading.Determining
      (FinitePermutationReadingCriteria.readAt
        TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity) S
      (FinitePermutationReadingCriteria.EdgeCoherent
        TagChangeEdgelessCriterion.graph Bool S) ↔
    FiniteReading.Determining
      (FinitePermutationReadingCriteria.readAt
        TagChangeEdgelessCriterion.graph Bool TagChangeEdgelessCriterion.identity) S
      (fun _ => True) from by
        simp only [FiniteReading.Determining, FiniteReading.Extends]
        constructor
        · rintro ⟨hsep, hext⟩
          exact ⟨hsep, fun table _ => hext table (edgeless_edge_coherent S table)⟩
        · rintro ⟨hsep, hext⟩
          exact ⟨hsep, fun table _ => hext table True.intro⟩]
  exact determining_equiv familyEquivPreserving bitEquivPerm _ _
    main_read_transport S

/-- A finite set of main J operation queries determines the whole family
exactly when its source index is finite. -/
theorem finite_main_operation_determining_iff :
    (∃ S : Finset TagChange.TaggedArchitectureIndex,
      FiniteReading.Determining
        (fun family source => FiniteApplicationHomDecoders.decodeTagAt source
          (localHomTable TagParameter
            (TagChangeMainRecovery.J family))) S (fun _ => True)) ↔
      Finite TagChange.TaggedArchitectureIndex := by
  simp_rw [main_operation_determining_iff_D]
  exact TagChangeEdgelessCriterion.finite_determining_iff

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCommonFiniteBridge
end TagChangeCommonFiniteBridge
end AAT.AG.LocalSemanticReconstruction
