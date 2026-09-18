import ResearchLean.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldNatAlgorithmNormalForm
import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldFiniteCarrierUnionObstruction
import Formal.Util.AssertStandardAxioms

/-!
# Carrier-separated local reconstruction for G-122 comparisons

This module strictly enlarges the Cycle 50 comparison image.  The independent
local value contains three pieces: a global three-axis permutation, an
explicit finite table on the `Fin 3` Extension carrier, and the faithful
exact-support/parity normal form on the distinct `Nat` Extension carrier.

Actual axis projection recovers the first component.  After removing the axis
section, stored backward-context action recovers the other two components.
Carrier-specific source probes prove that the `Fin 3` and `Nat` actions do not
interfere, so the resulting reading separates codes and gives both inverse
laws on the represented actual comparison image.

The Cycle 50 image embeds by the empty-support identity `Nat` code.  A
source-owned zero-one swap on `Nat` gives an explicit comparison outside that
embedded image.  The same cycle proves unique canonical-section code and
connects every represented lift to the full actual restriction-kernel torsor.

## Implementation notes

The local value stores no actual automorphism, comparison, lift, range
witness, or kernel element.  The reader uses unique choice only after actual
axis and backward observations have proved existence and uniqueness.  We use
the existing exact-support/parity normal form rather than a completed `Nat`
permutation, because it makes source provenance and finite authored data
explicit.  The result remains a strict represented image; it does not claim
the full comparison group, independent recovery of every kernel element, or
arbitrary-Hom reconstruction.
-/

namespace AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction
open MulAction Set Subgroup

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance cycle51AtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The infinite `Nat` carrier differs from the three-element carrier. -/
private theorem nat_ne_fin3 : Nat ≠ Fin 3 := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 3))
  exact Fintype.false finiteNat

/-- The three-element carrier differs from `Nat`. -/
private theorem fin3_ne_nat : Fin 3 ≠ Nat := Ne.symm nat_ne_fin3

/-- Context-category objects are determined by their stored contexts. -/
private theorem sourceContextObject_eq_of_ctx_eq
    {A : ArchitectureObject FiniteModel.carrier}
    {C : Site.ContextPreorderCategory A}
    {first second : Site.ContextCategoryObject C}
    (equality : first.ctx = second.ctx) : first = second := by
  cases first
  cases second
  cases equality
  rfl

/-- Every `Fin 3` Extension action fixes every canonical `Nat` probe. -/
theorem fin3Action_fixes_natProbe
    (permutation : Equiv.Perm (Fin 3)) (value : Nat) :
    (finiteAxisFoldSourceContextObjectPermHom (Fin 3) permutation)
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply sourceContextObject_eq_of_ctx_eq
  simp [finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation, nat_ne_fin3]

/-- Every `Nat` Extension action fixes every canonical `Fin 3` probe. -/
theorem natAction_fixes_fin3Probe
    (permutation : Equiv.Perm Nat) (value : Fin 3) :
    (finiteAxisFoldSourceContextObjectPermHom Nat permutation)
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply sourceContextObject_eq_of_ctx_eq
  simp [finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation, fin3_ne_nat]

/-- Combined source-context action of independent `Fin 3` and `Nat`
permutations. -/
def sourcePairAction
    (pair : Equiv.Perm (Fin 3) × Equiv.Perm Nat) :
    Equiv.Perm FiniteAxisFoldSourceContextObject :=
  finiteAxisFoldSourceContextObjectPermHom Nat pair.2 *
    finiteAxisFoldSourceContextObjectPermHom (Fin 3) pair.1

/-- Carrier-specific probes recover both permutations from their joint source
action. -/
theorem sourcePairAction_injective : Function.Injective sourcePairAction := by
  intro first second equality
  apply Prod.ext
  · apply Equiv.ext
    intro value
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun W : FiniteAxisFoldSourceContextObject =>
        (⟨W.ctx.Extension, W.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have probeEquality :
        (⟨Fin 3, first.1 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨Fin 3, second.1 value⟩ := by
      simpa [sourcePairAction,
        finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, fin3_ne_nat] using
          extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2
  · apply Equiv.ext
    intro value
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    have extensionSigmaEquality := congrArg
      (fun W : FiniteAxisFoldSourceContextObject =>
        (⟨W.ctx.Extension, W.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have probeEquality :
        (⟨Nat, first.2 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨Nat, second.2 value⟩ := by
      simpa [sourcePairAction,
        finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, nat_ne_fin3] using
          extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- Independent forward/backward table on the finite Extension carrier. -/
abbrev FiniteExtensionCode :=
  FiniteAxisFoldExtensionPermutationCode (Fin 3)

/-- Independent exact-support/parity normal form on `Nat`. -/
abbrev NatCode := FiniteAxisFoldNatAlgorithmNormalForm

/-- The two carrier-specific Extension codes. -/
abbrev CarrierCode := FiniteExtensionCode × NatCode

/-- Expected actual stored-backward action of both carrier codes. -/
noncomputable def carrierBackwardAction (code : CarrierCode) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldExtensionPermutationBackwardAction (Fin 3) code.1 *
    finiteAxisFoldArbitraryCarrierBackwardAction Nat code.2.evaluate

/-- The actual stored-backward action separates the two carrier codes. -/
theorem carrierBackwardAction_injective :
    Function.Injective carrierBackwardAction := by
  intro first second equality
  have unopEquality := congrArg MulOpposite.unop equality
  change
    finiteAxisFoldTransportedSourceContextPermutation
        first.2.evaluate⁻¹ *
          finiteAxisFoldTransportedSourceContextPermutation
            (FiniteAxisFoldExtensionPermutationCode.toPerm first.1)⁻¹ =
      finiteAxisFoldTransportedSourceContextPermutation
        second.2.evaluate⁻¹ *
          finiteAxisFoldTransportedSourceContextPermutation
            (FiniteAxisFoldExtensionPermutationCode.toPerm second.1)⁻¹
    at unopEquality
  have sourceEquality :
      sourcePairAction
          ((FiniteAxisFoldExtensionPermutationCode.toPerm first.1)⁻¹,
            first.2.evaluate⁻¹) =
        sourcePairAction
          ((FiniteAxisFoldExtensionPermutationCode.toPerm second.1)⁻¹,
            second.2.evaluate⁻¹) := by
    apply Equiv.ext
    intro sourceContext
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
        finiteAxisFoldSourceToActualContextEquiv.symm
          (permutation (finiteAxisFoldSourceToActualContextEquiv sourceContext)))
      unopEquality
    simp [finiteAxisFoldTransportedSourceContextPermutation, map_inv] at evaluated
    have firstRetract := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
        (FiniteAxisFoldExtensionPermutationCode.toPerm first.1))⁻¹
          sourceContext)
    have secondRetract := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
        (FiniteAxisFoldExtensionPermutationCode.toPerm second.1))⁻¹
          sourceContext)
    change
      ((finiteAxisFoldSourceContextObjectPermHom Nat first.2.evaluate)⁻¹)
          (((finiteAxisFoldSourceContextObjectPermHom (Fin 3)
            (FiniteAxisFoldExtensionPermutationCode.toPerm first.1))⁻¹)
              sourceContext) =
        ((finiteAxisFoldSourceContextObjectPermHom Nat second.2.evaluate)⁻¹)
          (((finiteAxisFoldSourceContextObjectPermHom (Fin 3)
            (FiniteAxisFoldExtensionPermutationCode.toPerm second.1))⁻¹)
              sourceContext)
    exact
      (congrArg
          (fun context =>
            ((finiteAxisFoldSourceContextObjectPermHom Nat
              first.2.evaluate)⁻¹) context) firstRetract.symm).trans
        (evaluated.trans
          (congrArg
            (fun context =>
              ((finiteAxisFoldSourceContextObjectPermHom Nat
                second.2.evaluate)⁻¹) context) secondRetract))
  have pairEquality := sourcePairAction_injective sourceEquality
  apply Prod.ext
  · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    exact inv_injective (congrArg Prod.fst pairEquality)
  · apply FiniteAxisFoldNatAlgorithmNormalForm.evaluate_injective
    exact inv_injective (congrArg Prod.snd pairEquality)

open G122MixedAxisExtensionLocalModel
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel

/-- Independent axis, finite-carrier, and `Nat` local data. -/
abbrev LocalCode := Equiv.Perm (Fin 3) × CarrierCode

/-- Evaluate the `Nat` normal form as an actual normalized endpoint
automorphism. -/
noncomputable def natAut (code : NatCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  code.actualEvaluate.1.1.1.1

/-- Apply the finite-carrier action before the independent `Nat` action. -/
noncomputable def carrierAut (code : CarrierCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  extensionAut code.1 * natAut code.2

/-- Evaluate all three components, placing the global axis section last. -/
noncomputable def localAut (code : LocalCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  carrierAut code.2 * finiteAxisFoldNormalizedAxisSectionHom code.1

/-- Every decoded `Nat` action is invisible to global axis projection. -/
theorem natAut_axisProjection_eq_one (code : NatCode) :
    finiteAxisFoldNormalizedAxisProjection (natAut code) = 1 := by
  exact MonoidHom.mem_ker.mp code.actualEvaluate.1.1.1.2

/-- The combined carrier action is invisible to global axis projection. -/
theorem carrierAut_axisProjection_eq_one (code : CarrierCode) :
    finiteAxisFoldNormalizedAxisProjection (carrierAut code) = 1 := by
  rw [carrierAut, map_mul, extensionAut_axisProjection_eq_one,
    natAut_axisProjection_eq_one, one_mul]

/-- Global axis projection reads the first local-code component. -/
theorem localAut_axisProjection (code : LocalCode) :
    finiteAxisFoldNormalizedAxisProjection (localAut code) = code.1 := by
  rw [localAut, map_mul, carrierAut_axisProjection_eq_one,
    finiteAxisFoldNormalizedAxisProjection_section, one_mul]

/-- Actual backward observation of a `Nat` code is its primitive source
action. -/
theorem natAut_backwardObservation (code : NatCode) :
    backwardObservation (natAut code) =
      finiteAxisFoldArbitraryCarrierBackwardAction Nat code.evaluate := by
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      code.actualEvaluate = _
  exact code.actualEvaluate_backwardProjection

/-- Actual backward observation of the carrier product is the expected joint
action. -/
theorem carrierAut_backwardObservation (code : CarrierCode) :
    backwardObservation (carrierAut code) = carrierBackwardAction code := by
  change finiteAxisFoldNormalizedContextBackwardProjection
      (extensionAut code.1 * natAut code.2) = carrierBackwardAction code
  rw [map_mul]
  change backwardObservation (extensionAut code.1) *
      backwardObservation (natAut code.2) = carrierBackwardAction code
  rw [carrierBackwardAction, extensionAut_backwardObservation,
    natAut_backwardObservation]

/-- Removing the observed axis section leaves precisely the carrier product. -/
theorem localAut_stripped (code : LocalCode) :
    strippedAut (localAut code) = carrierAut code.2 := by
  rw [strippedAut, localAut_axisProjection, localAut]
  simp

/-- Backward observation after axis removal recovers the joint carrier
action. -/
theorem localAut_backwardObservation (code : LocalCode) :
    backwardObservation (strippedAut (localAut code)) =
      carrierBackwardAction code.2 := by
  rw [localAut_stripped]
  exact carrierAut_backwardObservation code.2

/-- Axis projection and carrier-separated backward observation jointly
separate all local codes. -/
theorem localAut_injective : Function.Injective localAut := by
  intro first second equality
  apply Prod.ext
  · rw [← localAut_axisProjection first, ← localAut_axisProjection second,
      equality]
  · apply carrierBackwardAction_injective
    rw [← localAut_backwardObservation first,
      ← localAut_backwardObservation second, equality]

/-- Assemble a local code into the actual normalized comparison section. -/
noncomputable def localComparison (code : LocalCode) : NormalizedComparison :=
  generatedArrowComparisonSectionHom finiteAxisFoldNormalizedBarAlphaIso
    (localAut code)

/-- Source projection of an assembled comparison is the evaluated endpoint
automorphism. -/
@[simp] theorem localComparison_source (code : LocalCode) :
    generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom (localComparison code) =
      localAut code := by
  rfl

/-- Actual normalized comparisons represented by carrier-separated codes. -/
abbrev LocalComparisonImage := Set.range localComparison

/-- Retain one assembled comparison in the represented actual image. -/
noncomputable def assemble (code : LocalCode) : LocalComparisonImage :=
  ⟨localComparison code, ⟨code, rfl⟩⟩

/-- Read the global axis component from an actual represented comparison. -/
noncomputable def axisTarget (comparison : LocalComparisonImage) :
    Equiv.Perm (Fin 3) :=
  finiteAxisFoldNormalizedAxisProjection
    (generatedArrowComparisonSourceHom
      finiteAxisFoldNormalizedBarAlphaIso.hom comparison.1)

/-- Read the stripped stored-backward action from an actual represented
comparison. -/
noncomputable def carrierTarget (comparison : LocalComparisonImage) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  backwardObservation
    (strippedAut
      (generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom comparison.1))

/-- Every represented stripped observation has exactly one carrier code. -/
theorem carrierTarget_existsUnique (comparison : LocalComparisonImage) :
    ∃! code : CarrierCode,
      carrierBackwardAction code = carrierTarget comparison := by
  rcases comparison with ⟨comparison, code, rfl⟩
  refine ⟨code.2, ?_, ?_⟩
  · exact (localAut_backwardObservation code).symm
  · intro candidate candidateEquality
    apply carrierBackwardAction_injective
    exact candidateEquality.trans (localAut_backwardObservation code)

/-- Recover the unique carrier code selected by the actual observation. -/
noncomputable def readCarrier (comparison : LocalComparisonImage) :
    CarrierCode :=
  Classical.choose (carrierTarget_existsUnique comparison)

/-- Any carrier code realizing the observation is the recovered code. -/
theorem readCarrier_unique (comparison : LocalComparisonImage)
    (code : CarrierCode)
    (equality : carrierBackwardAction code = carrierTarget comparison) :
    code = readCarrier comparison :=
  (Classical.choose_spec (carrierTarget_existsUnique comparison)).2 code equality

/-- Read all three independent components from an actual comparison. -/
noncomputable def read (comparison : LocalComparisonImage) : LocalCode :=
  (axisTarget comparison, readCarrier comparison)

/-- Reading after assembly recovers every local code. -/
@[simp] theorem read_assemble (code : LocalCode) :
    read (assemble code) = code := by
  apply Prod.ext
  · exact localAut_axisProjection code
  · change readCarrier (assemble code) = code.2
    exact (readCarrier_unique (assemble code) code.2
      (localAut_backwardObservation code).symm).symm

/-- Assembly after reading recovers every represented actual comparison. -/
@[simp] theorem assemble_read (comparison : LocalComparisonImage) :
    assemble (read comparison) = comparison := by
  rcases comparison with ⟨comparison, code, rfl⟩
  apply Subtype.ext
  change localComparison (read (assemble code)) = localComparison code
  rw [read_assemble]

/-- Two-sided reconstruction equivalence between independent local data and
the actual represented comparison image. -/
noncomputable def localComparisonEquiv :
    LocalCode ≃ LocalComparisonImage where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Empty-support finite code evaluating to the identity on `Nat`. -/
def natIdentityFiniteCode : FiniteAxisFoldNatFiniteSupportCode where
  support := ∅
  table := FiniteAxisFoldExtensionPermutationCode.ofPerm 1
  table_moves := fun (value : {x // x ∈ (∅ : Finset Nat)}) => by
    exact isEmptyElim value

/-- Identity `Nat` normal form used to embed the Cycle 50 image. -/
def natIdentityCode : NatCode where
  adjacent := false
  finite := natIdentityFiniteCode

/-- The identity `Nat` normal form evaluates to the identity permutation. -/
@[simp] theorem natIdentityCode_evaluate : natIdentityCode.evaluate = 1 := by
  apply Equiv.ext
  intro value
  simp [natIdentityCode, natIdentityFiniteCode,
    FiniteAxisFoldNatAlgorithmNormalForm.evaluate,
    FiniteAxisFoldNatFiniteSupportCode.evaluate]

/-- The actual evaluation of the identity `Nat` code is identity. -/
@[simp] theorem natAut_identityCode : natAut natIdentityCode = 1 := by
  rw [natAut, FiniteAxisFoldNatAlgorithmNormalForm.actualEvaluate,
    natIdentityCode_evaluate, map_one]
  rfl

/-- Embed a Cycle 50 mixed code by adjoining the identity `Nat` code. -/
def embedMixedCode (code : MixedCode) : LocalCode :=
  (code.1, (code.2, natIdentityCode))

/-- Adjoining the identity `Nat` component preserves distinct mixed codes. -/
theorem embedMixedCode_injective : Function.Injective embedMixedCode := by
  intro first second equality
  exact Prod.ext (congrArg (fun code : LocalCode => code.1) equality)
    (congrArg (fun code => code.2.1) equality)

/-- Endpoint evaluation of an embedded code agrees with Cycle 50. -/
theorem localAut_embedMixedCode (code : MixedCode) :
    localAut (embedMixedCode code) = mixedAut code := by
  simp [localAut, carrierAut, embedMixedCode,
    G122MixedAxisExtensionLocalModel.mixedAut]

/-- Comparison assembly of an embedded code agrees with Cycle 50. -/
theorem localComparison_embedMixedCode (code : MixedCode) :
    localComparison (embedMixedCode code) = mixedComparison code := by
  rw [localComparison, mixedComparison, localAut_embedMixedCode]

/-- Embed every Cycle 50 comparison by its unique mixed code. -/
noncomputable def embedMixedImage
    (comparison : MixedComparisonImage) : LocalComparisonImage :=
  assemble (embedMixedCode (readMixed comparison))

/-- The Cycle 50 comparison-image embedding is injective. -/
theorem embedMixedImage_injective : Function.Injective embedMixedImage := by
  intro first second equality
  have codeEquality :
      embedMixedCode (readMixed first) = embedMixedCode (readMixed second) := by
    exact localComparisonEquiv.injective equality
  exact mixedComparisonEquiv.symm.injective
    (embedMixedCode_injective codeEquality)

/-- The Cycle 50 comparison image as a subtype embedding into the enlarged
image. -/
noncomputable def mixedImageEmbedding :
    MixedComparisonImage ↪ LocalComparisonImage :=
  ⟨embedMixedImage, embedMixedImage_injective⟩

/-- The source-owned zero-one `Nat` swap has finite support. -/
private theorem natSwap_finiteSupport :
    (fixedBy Nat finiteAxisFoldNatZeroOneSwap)ᶜ.Finite := by
  apply (Set.toFinite ({0, 1} : Set Nat)).subset
  intro value moved
  simp only [Set.mem_compl_iff, mem_fixedBy] at moved
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_contra outside
  push_neg at outside
  exact moved (Equiv.swap_apply_of_ne_of_ne outside.1 outside.2)

/-- The zero-one `Nat` swap in the accepted algorithm subgroup. -/
def natSwapSource : finiteAxisFoldNatAlgorithmPermutationSubgroup :=
  ⟨finiteAxisFoldNatZeroOneSwap,
    (finiteAxisFoldNatAlgorithmPermutationSubgroup_mem_iff_coset _).2
      (Or.inl natSwap_finiteSupport)⟩

/-- The unique faithful normal form of the zero-one `Nat` swap. -/
noncomputable def natSwapCode : NatCode :=
  FiniteAxisFoldNatAlgorithmNormalForm.equivPermutationSubgroup.symm
    natSwapSource

/-- The selected normal form evaluates back to the source-owned `Nat` swap. -/
@[simp] theorem natSwapCode_evaluate :
    natSwapCode.evaluate = finiteAxisFoldNatZeroOneSwap := by
  have recovered :=
    FiniteAxisFoldNatAlgorithmNormalForm.equivPermutationSubgroup.apply_symm_apply
      natSwapSource
  exact congrArg Subtype.val recovered

/-- Identity lookup table on the finite Extension carrier. -/
def identityExtensionCode : FiniteExtensionCode :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm 1

/-- The identity finite table decodes to the identity permutation. -/
@[simp] theorem identityExtensionCode_toPerm :
    FiniteAxisFoldExtensionPermutationCode.toPerm identityExtensionCode = 1 :=
  FiniteAxisFoldExtensionPermutationCode.toPerm_ofPerm 1

/-- Local code with trivial axis and finite-carrier parts and nontrivial
source-owned `Nat` swap. -/
def natSwapLocalCode : LocalCode :=
  (1, (identityExtensionCode, natSwapCode))

/-- The explicit `Nat` swap comparison is outside every embedded Cycle 50
comparison. -/
theorem natSwapLocalCode_not_embeddedMixed
    (comparison : MixedComparisonImage) :
    assemble natSwapLocalCode ≠ embedMixedImage comparison := by
  intro equality
  have codeEquality := localComparisonEquiv.injective equality
  have natEquality := congrArg (fun code : LocalCode => code.2.2) codeEquality
  have evaluationEquality := congrArg
    FiniteAxisFoldNatAlgorithmNormalForm.evaluate natEquality
  change natSwapCode.evaluate = natIdentityCode.evaluate at evaluationEquality
  rw [natSwapCode_evaluate, natIdentityCode_evaluate] at evaluationEquality
  have moved := congrArg (fun permutation : Equiv.Perm Nat => permutation 0)
    evaluationEquality
  norm_num [finiteAxisFoldNatZeroOneSwap] at moved

/-- The Cycle 50 image is a proper subimage of the carrier-separated image. -/
theorem mixedImageEmbedding_not_surjective :
    ¬ Function.Surjective mixedImageEmbedding := by
  intro surjective
  obtain ⟨comparison, equality⟩ := surjective (assemble natSwapLocalCode)
  exact natSwapLocalCode_not_embeddedMixed comparison equality.symm

/-- The joint actual reader separates all represented comparisons. -/
theorem read_injective : Function.Injective read :=
  localComparisonEquiv.symm.injective

/-- Actual canonical section lift over one represented comparison. -/
noncomputable def canonicalLift (comparison : LocalComparisonImage) :
    AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1 :=
  ⟨authoredExactCanonicalComparisonSectionHom
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1,
    authoredExactCanonicalComparisonSection_rightInverse
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1⟩

/-- Every represented canonical section is induced by one unique independent
local code. -/
theorem canonicalSection_unique_localCode
    (comparison : LocalComparisonImage) :
    ∃! code : LocalCode,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (localComparison code) =
        (canonicalLift comparison).1 := by
  refine ⟨read comparison, ?_, ?_⟩
  · exact congrArg
      (authoredExactCanonicalComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (congrArg Subtype.val (assemble_read comparison))
  · intro candidate candidateEquality
    have normalized := congrArg
      (fun raw : RawComparison => restrictionHom raw) candidateEquality
    change restrictionHom
        (authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (localComparison candidate)) =
      restrictionHom
        (authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible comparison.1) at normalized
    rw [authoredExactCanonicalComparisonSection_rightInverse,
      authoredExactCanonicalComparisonSection_rightInverse] at normalized
    have imageEquality : assemble candidate = comparison := by
      apply Subtype.ext
      exact normalized
    exact localComparisonEquiv.injective
      (imageEquality.trans (assemble_read comparison).symm)

/-- Every lift in a represented fiber has one unique displacement from the
canonical lift by the full actual restriction kernel. -/
theorem everyLift_unique_kernel_displacement
    (comparison : LocalComparisonImage)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1) :
    ∃! kernelValue : restrictionHom.kerᵐᵒᵖ,
      kernelValue • canonicalLift comparison = lift :=
  authoredExactCanonicalComparisonLiftFiber_existsUnique_smul_eq
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1
    (canonicalLift comparison) lift

/-- Unique carrier-separated canonical-section code and the full-kernel torsor
hold together on every represented lift fiber. -/
theorem carrierSeparated_fullKernel_reconstruction
    (comparison : LocalComparisonImage)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible comparison.1) :
    (∃! code : LocalCode,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (localComparison code) =
        (canonicalLift comparison).1) ∧
    (∃! kernelValue : restrictionHom.kerᵐᵒᵖ,
      kernelValue • canonicalLift comparison = lift) :=
  ⟨canonicalSection_unique_localCode comparison,
    everyLift_unique_kernel_displacement comparison lift⟩

end
end AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel
