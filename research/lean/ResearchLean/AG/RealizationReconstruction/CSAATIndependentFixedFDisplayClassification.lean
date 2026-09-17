import ResearchLean.AG.RealizationReconstruction.CSAATIndependentDirectedReadback
import ResearchLean.AG.RealizationReconstruction.FixedFLensConnection
import ResearchLean.AG.RealizationReconstruction.FixedFProtocolConnection
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldPermutationIntrinsicImage
import Formal.Util.AssertStandardAxioms

/-!
# Independent generated packages and the common fixed-F classifier

This module applies the same complete-update fixed-graph classification to the
independently defined generated lens and protocol package morphisms.  A package
automorphism stores only the package morphism and bijectivity of its carrier
map; the semantic change and its hidden permutation are reconstructed.

The resulting common classifier is then evaluated through the existing
finite-axis-fold table decoder.  This recovers every classified hidden
permutation in the actual intrinsic D-side subgroup.  It does not identify
that subgroup with the full G-122 comparison group, its ambient kernel, or all
of its lift fibers.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace CSAATIndependentFixedFDisplayClassification

open FixedFFiniteExamples
open FixedFLensConnection
open FixedFProtocolConnection

local instance completeUpdateVertexFinite (V : Type u) [Finite V] :
    Finite (completeUpdateGraph V).Vertex := inferInstanceAs (Finite V)

local instance completeUpdateEdgeFinite (V : Type u) [Finite V] :
    Finite (completeUpdateGraph V).Edge := inferInstanceAs (Finite (V × V))

/-- The fixed lens family input used by the product model. -/
def productLensInput (V : Type u) (reference : V) : LensFamilyInput.{u} where
  View := V
  reference := reference

/-- The fixed protocol family input retaining every complete-update operation
name and the independently fixed observation functor. -/
def completeUpdateProtocolInput (V : Type u) [Finite V] :
    ProtocolFamilyInput.{u} where
  schema := schema (completeUpdateGraph V)
  observation := observationFunctor (completeUpdateGraph V)

/-- A generated lens package endomorphism whose sole carrier map is
bijective.  No semantic morphism or classifier is stored. -/
abbrev LensIndependentPackageAut (V K : Type u) (reference : V) [Finite K] :=
  { h : LensAATIndependentGeneratedPackageHom
      (productLensInput V reference)
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) //
    Function.Bijective h.stateMap }

/-- A generated protocol package endomorphism whose map at every original
control point is bijective.  The visible operation-name action is the identity
automorphism in this common fixed-fiber comparison. -/
abbrev ProtocolIndependentPackageAut (V K : Type u)
    [Finite V] [Finite K] :=
  { h : ProtocolAATIndependentGeneratedPackageHom
      (completeUpdateProtocolInput V)
      (realization (completeUpdateGraph V) K)
      (realization (completeUpdateGraph V) K) //
    ∀ vertex, Function.Bijective (h.stateMap vertex) }

/-- Reconstruct the independent invertible lens change over the identity
visible action from a generated package automorphism. -/
noncomputable def lensPackageAutToInvertibleChange
    {V K : Type u} {reference : V} [Finite K]
    (h : LensIndependentPackageAut V K reference) :
    LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) 1 where
  h := Equiv.ofBijective h.1.stateMap h.2
  get_naturality state := by
    simpa using h.1.toSemanticHom.get_naturality state
  put_naturality state requested := by
    simpa using h.1.toSemanticHom.put_naturality state requested

/-- Translate an independent identity-visible lens change into the generated
package and retain only the derived bijectivity proof. -/
def lensPackageAutOfInvertibleChange
    {V K : Type u} {reference : V} [Finite K]
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) 1) :
    LensIndependentPackageAut V K reference :=
  ⟨LensAATIndependentGeneratedPackageHom.ofSemanticHom
      { toFun := change.h
        get_naturality := fun state => by simpa using change.get_naturality state
        put_naturality := fun state requested => by
          simpa using change.put_naturality state requested },
    change.h.bijective⟩

/-- Exact correspondence between generated lens package automorphisms and the
independently defined identity-visible lens changes. -/
noncomputable def lensPackageAutEquivInvertibleChange
    (V K : Type u) (reference : V) [Finite K] :
    LensIndependentPackageAut V K reference ≃
      LensInvertibleChange
        (LensRealization.product V K reference)
        (LensRealization.product V K reference) 1 where
  toFun := lensPackageAutToInvertibleChange
  invFun := lensPackageAutOfInvertibleChange
  left_inv h := by
    apply Subtype.ext
    ext state
    rfl
  right_inv change := by
    apply LensInvertibleChange.ext
    apply Equiv.ext
    intro state
    rfl

/-- Reconstruct the independent identity-visible protocol change from a
generated protocol package automorphism. -/
noncomputable def protocolPackageAutToInvertibleChange
    {V K : Type u} [Finite V] [Finite K]
    (h : ProtocolIndependentPackageAut V K) :
    ProtocolInvertibleChange (completeUpdateGraph V) K 1 where
  stateEquiv := fun vertex => Equiv.ofBijective (h.1.stateMap vertex) (h.2 vertex)
  edge_naturality := by
    intro source target edge state
    simpa [realization_edgeAction] using h.1.edge_map edge state
  observation_naturality := by
    intro vertex state
    exact Subsingleton.elim _ _

/-- Translate an identity-visible protocol change into the generated package.
All path and quotient-execution naturality is reconstructed by the existing
package readback. -/
def protocolPackageAutOfInvertibleChange
    {V K : Type u} [Finite V] [Finite K]
    (change : ProtocolInvertibleChange (completeUpdateGraph V) K 1) :
    ProtocolIndependentPackageAut V K :=
  ⟨ProtocolAATIndependentGeneratedPackageHom.ofForwardMorphism
      { stateMap := fun vertex state => change.stateEquiv vertex state
        edge_naturality := by
          intro source target edge state
          simpa [realization_edgeAction] using change.edge_naturality edge state
        observation_naturality := change.observation_naturality },
    fun vertex => (change.stateEquiv vertex).bijective⟩

/-- Exact correspondence between generated protocol package automorphisms and
the independently defined identity-visible protocol changes. -/
noncomputable def protocolPackageAutEquivInvertibleChange
    (V K : Type u) [Finite V] [Finite K] :
    ProtocolIndependentPackageAut V K ≃
      ProtocolInvertibleChange (completeUpdateGraph V) K 1 where
  toFun := protocolPackageAutToInvertibleChange
  invFun := protocolPackageAutOfInvertibleChange
  left_inv h := by
    apply Subtype.ext
    ext vertex state
    change h.1.stateMap vertex state = h.1.stateMap vertex state
    rfl
  right_inv change := by
    apply ProtocolInvertibleChange.ext
    funext vertex
    apply Equiv.ext
    intro state
    change change.stateEquiv vertex state = change.stateEquiv vertex state
    rfl

/-- Both independently generated package interfaces meet in the same actual
operation-preserving complete-update fixed-F change. -/
noncomputable def lensProtocolIndependentPackageEquiv
    (V K : Type u) (reference : V) [Finite V] [Finite K] :
    LensIndependentPackageAut V K reference ≃
      ProtocolIndependentPackageAut V K :=
  (lensPackageAutEquivInvertibleChange V K reference).trans
    ((LensInvertibleChange.equivPreservingFollowingChanges
      (V := V) (K := K) (reference := reference)
      (visible := (1 : Equiv.Perm V))).trans
      ((ProtocolInvertibleChange.equivPreservingFollowingChanges
        (F := completeUpdateGraph V) (K := K)
        (automorphism := (1 : FixedFGraphAutomorphism
          (completeUpdateGraph V)))).symm.trans
        (protocolPackageAutEquivInvertibleChange V K).symm))

/-- The common fixed-F classifier, read on the lens package side. -/
noncomputable def lensIndependentFixedFClassification
    (V K : Type u) (reference : V) [Finite K] :
    LensIndependentPackageAut V K reference ≃ Equiv.Perm K :=
  (lensPackageAutEquivInvertibleChange V K reference).trans
    (LensInvertibleChange.equivHiddenPermutations
      (V := V) (K := K) (reference := reference)
      (visible := (1 : Equiv.Perm V)))

/-- The protocol classifier is definitionally the same fixed-F classifier
after the package-to-package equivalence. -/
noncomputable def protocolIndependentFixedFClassification
    (V K : Type u) (reference : V) [Finite V] [Finite K] :
    ProtocolIndependentPackageAut V K ≃ Equiv.Perm K :=
  (lensProtocolIndependentPackageEquiv V K reference).symm.trans
    (lensIndependentFixedFClassification V K reference)

/-- The lens package state action is completely recovered by the common
hidden-permutation classifier. -/
theorem lens_stateMap_classification
    {V K : Type u} {reference : V} [Finite K]
    (h : LensIndependentPackageAut V K reference)
    (vertex : V) (hidden : K) :
    h.1.stateMap (vertex, hidden) =
      (vertex, lensIndependentFixedFClassification V K reference h hidden) := by
  exact (LensInvertibleChange.normalForm
    (lensPackageAutEquivInvertibleChange V K reference h) vertex hidden)

/-- The package equivalence preserves the common classifier, so the lens and
protocol statements are applications of one fixed-F classification. -/
theorem lensProtocol_classifier_compatibility
    {V K : Type u} {reference : V} [Finite V] [Finite K]
    (h : LensIndependentPackageAut V K reference) :
    protocolIndependentFixedFClassification V K reference
        (lensProtocolIndependentPackageEquiv V K reference h) =
      lensIndependentFixedFClassification V K reference h := by
  simp [protocolIndependentFixedFClassification]

/-- The protocol carrier map at every control point is recovered by the same
hidden permutation that classifies the corresponding lens package. -/
theorem protocol_stateMap_classification
    {V K : Type u} {reference : V} [Finite V] [Finite K]
    (h : ProtocolIndependentPackageAut V K)
    (vertex : V) (hidden : K) :
    h.1.stateMap vertex hidden =
      protocolIndependentFixedFClassification V K reference h hidden := by
  let lens := (lensProtocolIndependentPackageEquiv V K reference).symm h
  have classified := lens_stateMap_classification lens vertex hidden
  exact congrArg Prod.snd classified

/-- Reconstruct every directed generated lens geometry component only after
the independent package automorphism has been supplied. -/
noncomputable def lensPackageDirectedPackage
    {V K : Type u} {reference : V} [Finite K]
    (h : LensIndependentPackageAut V K reference) :
    LensAATGeneratedDirectedPackage
      (productLensInput V reference) h.1.toForwardMorphism :=
  h.1.toDirectedPackage

/-- Protocol analogue, retaining every generated named operation and
observation component. -/
noncomputable def protocolPackageDirectedPackage
    {V K : Type u} [Finite V] [Finite K]
    (h : ProtocolIndependentPackageAut V K) :
    ProtocolAATGeneratedDirectedPackage
      (completeUpdateProtocolInput V) h.1.toForwardMorphism :=
  h.1.toDirectedPackage

/-- Every common hidden classifier has an explicit finite table code. -/
noncomputable def fixedFClassifierToDCode (K : Type) [Fintype K] :
    Equiv.Perm K ≃ FiniteAxisFoldExtensionPermutationCode K :=
  FiniteAxisFoldExtensionPermutationCode.tableMulEquiv.symm.toEquiv

/-- Every common hidden classifier is recovered in the actual D-side subgroup
characterized by its complete stored-backward context action. -/
noncomputable def fixedFClassifierToDIntrinsic (K : Type) [Fintype K] :
    Equiv.Perm K ≃ FiniteAxisFoldExtensionPermutationIntrinsicImage K :=
  (fixedFClassifierToDCode K).trans
    (finiteAxisFoldExtensionPermutationIntrinsicDecoderEquiv K).toEquiv

/-- Lens generated package automorphisms recover all of their classified
hidden permutations through the finite table and actual D evaluation route. -/
noncomputable def lensPackageDIntrinsicClassification
    (V K : Type) (reference : V) [Fintype K] :
    LensIndependentPackageAut V K reference ≃
      FiniteAxisFoldExtensionPermutationIntrinsicImage K :=
  (lensIndependentFixedFClassification V K reference).trans
    (fixedFClassifierToDIntrinsic K)

/-- Protocol generated package automorphisms use the identical D-side
intrinsic recovery map. -/
noncomputable def protocolPackageDIntrinsicClassification
    (V K : Type) (reference : V) [Fintype V] [Fintype K] :
    ProtocolIndependentPackageAut V K ≃
      FiniteAxisFoldExtensionPermutationIntrinsicImage K :=
  (protocolIndependentFixedFClassification V K reference).trans
    (fixedFClassifierToDIntrinsic K)

/-- The two CS package classifications agree after actual D-side recovery. -/
theorem lensProtocol_DIntrinsic_compatibility
    {V K : Type} {reference : V} [Fintype V] [Fintype K]
    (h : LensIndependentPackageAut V K reference) :
    protocolPackageDIntrinsicClassification V K reference
        (lensProtocolIndependentPackageEquiv V K reference h) =
      lensPackageDIntrinsicClassification V K reference h := by
  simp [protocolPackageDIntrinsicClassification,
    lensPackageDIntrinsicClassification,
    protocolIndependentFixedFClassification]

/-- The D-side value of a lens package classifier is the existing actual
local-fiber-kernel section evaluated on that very permutation. -/
theorem lensPackageDIntrinsic_value
    {V K : Type} {reference : V} [Fintype K]
    (h : LensIndependentPackageAut V K reference) :
    (lensPackageDIntrinsicClassification V K reference h).1 =
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom K
        (lensIndependentFixedFClassification V K reference h) := by
  rfl

/-- The protocol route evaluates through the same actual D-side section. -/
theorem protocolPackageDIntrinsic_value
    {V K : Type} {reference : V} [Fintype V] [Fintype K]
    (h : ProtocolIndependentPackageAut V K) :
    (protocolPackageDIntrinsicClassification V K reference h).1 =
      finiteAxisFoldNormalizedPermutationLocalFiberKernelSectionHom K
        (protocolIndependentFixedFClassification V K reference h) := by
  rfl

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end CSAATIndependentFixedFDisplayClassification

end AAT.AG.RealizationReconstruction
