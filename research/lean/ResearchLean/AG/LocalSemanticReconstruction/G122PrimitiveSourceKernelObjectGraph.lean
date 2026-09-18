import ResearchLean.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph
import ResearchLean.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldAmbientKernelPresentation
import Formal.Util.AssertStandardAxioms

/-!
# Primitive object-graph quotient of the full G-122 source kernel

The complete direct normalization kernel acts on architecture objects.  This
module reads that action into the independent Bool-valued graph presentation
of `PrimitiveFiberPermutationGraph`.  Naturality of canonical object
normalization and the actual kernel equation prove that every such object
permutation preserves normalization fibers.

The construction is multiplicative and exposes a nonidentity primitive graph
coming from the source-authored ambient-kernel recipe.  The same element is
then carried through the full source-kernel equivalence to a nonidentity raw
comparison with trivial restriction, so the primitive observation is connected
to the complete comparison reconstruction in this module.

## Implementation notes

This is the exact object-action quotient of the direct normalization kernel.
It does not claim that object action alone separates complete geometry
automorphisms: atom, context, equation, operation, coefficient, raw, and local
realization components remain additional local-reading obligations.  Neither
the graph code nor the ambient recipe stores a completed automorphism.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction

noncomputable section

set_option maxHeartbeats 400000

namespace G122PrimitiveSourceKernelObjectGraph

open PrimitiveFiberPermutationGraph
open PrimitiveFiberPermutationGraph.GraphCode
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open G122FullComparisonKernelDecomposition
open G122FullSourceKernelExactDecomposition

/-- The actual direct core whose architecture-object normalization is read. -/
noncomputable abbrev ActualDirectCore :=
  finiteAxisFoldActualDirectAdmissibleGeometry.obj.core

/-- Primitive object normalization on the actual direct endpoint. -/
noncomputable def directObjectNormalization :
    ArchitectureObject FiniteModel.carrier →
      ArchitectureObject FiniteModel.carrier :=
  canonicalObjectNormalization ActualDirectCore

/-- Underlying architecture-object permutation of a complete direct-kernel
automorphism. -/
noncomputable def sourceKernelObjectPermutation
    (kernelValue : DirectNormalizationKernel) :
    Equiv.Perm (ArchitectureObject FiniteModel.carrier) where
  toFun := kernelValue.1.hom.hom.base.upper.objectMap
  invFun := kernelValue.1.inv.hom.base.upper.objectMap
  left_inv object := by
    have equality := congrArg
      (fun hom : finiteAxisFoldActualDirectAdmissibleGeometry ⟶
          finiteAxisFoldActualDirectAdmissibleGeometry =>
        hom.hom.base.upper.objectMap)
      kernelValue.1.hom_inv_id
    exact congrFun equality object
  right_inv object := by
    have equality := congrArg
      (fun hom : finiteAxisFoldActualDirectAdmissibleGeometry ⟶
          finiteAxisFoldActualDirectAdmissibleGeometry =>
        hom.hom.base.upper.objectMap)
      kernelValue.1.inv_hom_id
    exact congrFun equality object

/-- A direct-kernel automorphism fixes every normalized architecture object. -/
theorem sourceKernelObjectPermutation_fix_normalized
    (kernelValue : DirectNormalizationKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    sourceKernelObjectPermutation kernelValue
        (directObjectNormalization object) =
      directObjectNormalization object := by
  have kernelEquality : directNormalizationHom kernelValue.1 = 1 :=
    MonoidHom.mem_ker.mp kernelValue.property
  have homEquality := congrArg
    (fun automorphism : Aut FiniteAxisFoldNormalizedDirectGeometry =>
      automorphism.hom.f.hom.base.upper.objectMap)
    kernelEquality
  have pointEquality := congrFun homEquality object
  exact pointEquality

/-- Hence the object permutation of every direct-kernel automorphism stays in
one canonical-normalization fiber. -/
theorem sourceKernelObjectPermutation_normalize
    (kernelValue : DirectNormalizationKernel)
    (object : ArchitectureObject FiniteModel.carrier) :
    directObjectNormalization (sourceKernelObjectPermutation kernelValue object) =
      directObjectNormalization object := by
  have naturality := canonicalObjectNormalization_natural_apply
    kernelValue.1.hom.hom.base object
  exact naturality.symm.trans
    (sourceKernelObjectPermutation_fix_normalized kernelValue object)

/-- Complete direct-kernel automorphisms act multiplicatively on the full
fiber-preserving object-permutation subgroup. -/
noncomputable def sourceKernelObjectPermutationHom :
    DirectNormalizationKernel →*
      FiberPermutationSubgroup directObjectNormalization where
  toFun kernelValue :=
    ⟨sourceKernelObjectPermutation kernelValue,
      sourceKernelObjectPermutation_normalize kernelValue⟩
  map_one' := by
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro object
    rfl
  map_mul' first second := by
    apply Subtype.ext
    apply Equiv.Perm.ext
    intro object
    rfl

/-- The underlying permutation of the multiplicative object action is the
directly constructed object permutation. -/
@[simp]
theorem sourceKernelObjectPermutationHom_coe
    (kernelValue : DirectNormalizationKernel) :
    (sourceKernelObjectPermutationHom kernelValue).1 =
      sourceKernelObjectPermutation kernelValue :=
  rfl

/-- Primitive Bool graph codes for the object action of the direct kernel. -/
abbrev DirectObjectGraphCode :=
  GraphCode directObjectNormalization

/-- Read a complete direct-kernel element into its independent primitive
object graph. -/
noncomputable def sourceKernelObjectGraphHom :
    DirectNormalizationKernel →* DirectObjectGraphCode :=
  graphMulEquivFiberPermutation.symm.toMonoidHom.comp
    sourceKernelObjectPermutationHom

/-- Assembly of the primitive object graph recovers the complete object
permutation supplied by the direct-kernel action. -/
@[simp]
theorem assemble_sourceKernelObjectGraphHom
    (kernelValue : DirectNormalizationKernel) :
    assemble (sourceKernelObjectGraphHom kernelValue) =
      sourceKernelObjectPermutationHom kernelValue := by
  exact graphMulEquivFiberPermutation.apply_symm_apply _

/-- Object-graph reading is pointwise evaluation of the kernel automorphism,
not a stored completed map. -/
theorem sourceKernelObjectGraph_edge_iff
    (kernelValue : DirectNormalizationKernel)
    (source target : ArchitectureObject FiniteModel.carrier) :
    (sourceKernelObjectGraphHom kernelValue).edge source target = true ↔
      sourceKernelObjectPermutation kernelValue source = target := by
  exact read_edge_eq_true_iff _ _ _

/-- Graph multiplication is the local relational composition rule for direct
kernel object actions. -/
theorem sourceKernelObjectGraph_mul_edge_iff
    (first second : DirectNormalizationKernel)
    (source target : ArchitectureObject FiniteModel.carrier) :
    (sourceKernelObjectGraphHom (first * second)).edge source target = true ↔
      ∃ middle,
        (sourceKernelObjectGraphHom second).edge source middle = true ∧
          (sourceKernelObjectGraphHom first).edge middle target = true := by
  rw [map_mul]
  exact mul_edge_eq_true_iff _ _ _ _

/-! ## Nontrivial primitive witness and full-comparison connection -/

/-- The independently authored direct ambient-kernel recipe as an element of
the complete direct normalization kernel. -/
noncomputable def directAmbientSourceKernel : DirectNormalizationKernel :=
  ⟨FiniteAxisFoldAmbientKernelCode.direct.admissibleEvaluateAut,
    FiniteAxisFoldAmbientKernelCode.admissibleEvaluateAut_mem_normalizationKernel
        FiniteAxisFoldAmbientKernelCode.direct⟩

/-- Its object permutation is nonidentity before any graph encoding. -/
theorem directAmbientSourceKernel_objectPermutation_ne_one :
    sourceKernelObjectPermutation directAmbientSourceKernel ≠ 1 := by
  intro equality
  apply ambientKernelObjectMap_ne_id ActualDirectCore
  funext object
  have pointEquality := congrArg
    (fun permutation : Equiv.Perm (ArchitectureObject FiniteModel.carrier) =>
      permutation object)
    equality
  exact pointEquality

/-- The source-authored ambient kernel therefore has a nonidentity primitive
Bool graph. -/
theorem directAmbientSourceKernel_objectGraph_ne_one :
    sourceKernelObjectGraphHom directAmbientSourceKernel ≠ 1 := by
  intro equality
  apply directAmbientSourceKernel_objectPermutation_ne_one
  have mappedEquality := congrArg GraphCode.assemble equality
  have valueEquality := congrArg
    (fun permutation : FiberPermutationSubgroup directObjectNormalization =>
      permutation.1)
    mappedEquality
  simpa using valueEquality

/-- The same primitive source-kernel element transported to the full raw
comparison kernel. -/
noncomputable def directAmbientFullComparisonKernel : FullKernel :=
  sourceKernelToFullKernelHom directAmbientSourceKernel

/-- The named ambient full-kernel value is exactly the image of its source
kernel coordinate. -/
@[simp]
theorem directAmbientFullComparisonKernel_eq_sourceKernelToFullKernel :
    directAmbientFullComparisonKernel =
      sourceKernelToFullKernelHom directAmbientSourceKernel :=
  rfl

/-- The transported raw comparison has trivial normalized restriction. -/
theorem directAmbientFullComparisonKernel_restriction :
    restrictionHom directAmbientFullComparisonKernel.1 = 1 :=
  MonoidHom.mem_ker.mp directAmbientFullComparisonKernel.property

/-- The transported raw comparison remains nonidentity. -/
theorem directAmbientFullComparisonKernel_ne_one :
    directAmbientFullComparisonKernel ≠ 1 := by
  intro equality
  apply directAmbientSourceKernel_objectGraph_ne_one
  have sourceEquality := congrArg fullKernelToSourceKernelHom equality
  simpa using
    congrArg sourceKernelObjectGraphHom sourceEquality

/-- Source-kernel assembly is the canonical normalized lift followed by the
corresponding full-kernel displacement. -/
theorem assembleSourceKernel_eq_canonicalSection_mul
    (sourceKernel : DirectNormalizationKernel)
    (normalizedSource : Aut FiniteAxisFoldNormalizedDirectGeometry) :
    assembleSourceKernel (MulOpposite.op sourceKernel, normalizedSource) =
      canonicalSectionHom
          (normalizedComparisonSourceMulEquiv.symm normalizedSource) *
        (sourceKernelToFullKernelHom sourceKernel).1 := by
  rfl

/-- Cycle 61's full reconstruction assembles the ambient primitive graph at
the identity normalized source to precisely the transported raw comparison. -/
theorem assembleSourceKernel_directAmbient :
    assembleSourceKernel (MulOpposite.op directAmbientSourceKernel, 1) =
      directAmbientFullComparisonKernel.1 := by
  rw [assembleSourceKernel_eq_canonicalSection_mul]
  rw [map_one]
  simp [canonicalSectionHom]

/-- Reading the transported raw comparison recovers both its primitive
source-kernel coordinate and the identity normalized source. -/
theorem readSourceKernel_directAmbient :
    readSourceKernel directAmbientFullComparisonKernel.1 =
      (MulOpposite.op directAmbientSourceKernel, 1) := by
  rw [← assembleSourceKernel_directAmbient]
  exact readSourceKernel_assembleSourceKernel _

end G122PrimitiveSourceKernelObjectGraph

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph

end

end AAT.AG.LocalSemanticReconstruction
