import ResearchLean.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel
import Formal.Util.AssertStandardAxioms

/-!
# Four-component local reconstruction for G-122 comparisons

This module strictly enlarges the carrier-separated comparison image by adding
an independent `Fin 4` Extension table to the accepted axis, `Fin 3`, and `Nat`
data.  Carrier-specific probes separate all three Extension actions.  Actual
axis projection and the stripped stored-backward action therefore recover all
four source components and yield a two-sided equivalence with the represented
normalized-comparison image.

The Cycle 51 image embeds by the identity `Fin 4` table.  A transposition of
the first two `Fin 4` values gives an explicit actual comparison outside that
image.  The same surface proves uniqueness of canonical-section codes and
connects every represented lift to the full comparison-restriction-kernel
torsor.

## Implementation notes

The local code stores only independent permutation tables and the accepted
exact-support/parity normal form.  It stores no actual automorphism,
comparison, lift, range witness, or kernel element.  Unique choice is used
only after the actual observations prove existence and uniqueness.  This is
still a represented image, not a recovery of the full comparison group or of
every full-kernel element from independent local data.
-/

namespace AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction
open MulAction Set Subgroup

noncomputable section

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance cycle52AtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

open G122MixedAxisExtensionLocalModel
open G122CarrierSeparatedComparisonLocalModel
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel

/-- The three-element carrier differs from the four-element carrier. -/
private theorem fin3_ne_fin4 : Fin 3 ≠ Fin 4 := by
  intro equality
  have cardinality := Fintype.card_congr (Equiv.cast equality)
  norm_num at cardinality

/-- The four-element carrier differs from the three-element carrier. -/
private theorem fin4_ne_fin3 : Fin 4 ≠ Fin 3 := Ne.symm fin3_ne_fin4

/-- The infinite carrier differs from the four-element carrier. -/
private theorem nat_ne_fin4 : Nat ≠ Fin 4 := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 4))
  exact Fintype.false finiteNat

/-- The four-element carrier differs from the infinite carrier. -/
private theorem fin4_ne_nat : Fin 4 ≠ Nat := Ne.symm nat_ne_fin4

/-- The infinite carrier differs from the three-element carrier. -/
private theorem nat_ne_fin3 : Nat ≠ Fin 3 := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 3))
  exact Fintype.false finiteNat

/-- The three-element carrier differs from the infinite carrier. -/
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

/-- Every `Fin 4` action fixes every canonical `Fin 3` probe. -/
theorem fin4Action_fixes_fin3Probe
    (permutation : Equiv.Perm (Fin 4)) (value : Fin 3) :
    (finiteAxisFoldSourceContextObjectPermHom (Fin 4) permutation)
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
    finiteAxisFoldExtensionValuePermutation, fin3_ne_fin4]

/-- Every `Fin 4` action fixes every canonical `Nat` probe. -/
theorem fin4Action_fixes_natProbe
    (permutation : Equiv.Perm (Fin 4)) (value : Nat) :
    (finiteAxisFoldSourceContextObjectPermHom (Fin 4) permutation)
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
    finiteAxisFoldExtensionValuePermutation, nat_ne_fin4]

/-- Every `Fin 3` action fixes every canonical `Fin 4` probe. -/
theorem fin3Action_fixes_fin4Probe
    (permutation : Equiv.Perm (Fin 3)) (value : Fin 4) :
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
    finiteAxisFoldExtensionValuePermutation, fin4_ne_fin3]

/-- Every `Nat` action fixes every canonical `Fin 4` probe. -/
theorem natAction_fixes_fin4Probe
    (permutation : Equiv.Perm Nat) (value : Fin 4) :
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
    finiteAxisFoldExtensionValuePermutation, fin4_ne_nat]

/-- Joint source action of the `Fin 3`, `Nat`, and `Fin 4` components. -/
def sourceTripleAction
    (triple : (Equiv.Perm (Fin 3) × Equiv.Perm Nat) × Equiv.Perm (Fin 4)) :
    Equiv.Perm FiniteAxisFoldSourceContextObject :=
  G122CarrierSeparatedComparisonLocalModel.sourcePairAction triple.1 *
    finiteAxisFoldSourceContextObjectPermHom (Fin 4) triple.2

/-- Carrier-specific probes recover all three permutations from their joint
source action. -/
theorem sourceTripleAction_injective : Function.Injective sourceTripleAction := by
  intro first second equality
  apply Prod.ext
  · apply Prod.ext
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
          (⟨Fin 3, first.1.1 value⟩ : Sigma fun carrier : Type => carrier) =
            ⟨Fin 3, second.1.1 value⟩ := by
        simpa [sourceTripleAction,
          G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
          finiteAxisFoldSourceContextObjectPermHom,
          finiteAxisFoldSourceContextObjectPerm,
          finiteAxisFoldSourceContextObjectPermutation,
          finiteAxisFoldSourceContextPermutation,
          finiteAxisFoldSourceExtensionProbe,
          finiteAxisFoldExtensionValuePermutation, fin3_ne_nat, fin3_ne_fin4]
          using extensionSigmaEquality
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
          (⟨Nat, first.1.2 value⟩ : Sigma fun carrier : Type => carrier) =
            ⟨Nat, second.1.2 value⟩ := by
        simpa [sourceTripleAction,
          G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
          finiteAxisFoldSourceContextObjectPermHom,
          finiteAxisFoldSourceContextObjectPerm,
          finiteAxisFoldSourceContextObjectPermutation,
          finiteAxisFoldSourceContextPermutation,
          finiteAxisFoldSourceExtensionProbe,
          finiteAxisFoldExtensionValuePermutation, nat_ne_fin3, nat_ne_fin4]
          using extensionSigmaEquality
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
        (⟨Fin 4, first.2 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨Fin 4, second.2 value⟩ := by
      simpa [sourceTripleAction,
        G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
        finiteAxisFoldSourceContextObjectPermHom,
        finiteAxisFoldSourceContextObjectPerm,
        finiteAxisFoldSourceContextObjectPermutation,
        finiteAxisFoldSourceContextPermutation,
        finiteAxisFoldSourceExtensionProbe,
        finiteAxisFoldExtensionValuePermutation, fin4_ne_fin3, fin4_ne_nat]
        using extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- Independent forward/backward table on the new finite carrier. -/
abbrev Fin4Code := FiniteAxisFoldExtensionPermutationCode (Fin 4)

/-- The accepted Cycle 51 carrier data together with a new `Fin 4` table. -/
abbrev CarrierCode := G122CarrierSeparatedComparisonLocalModel.CarrierCode × Fin4Code

/-- Expected actual stored-backward action of all three carrier codes. -/
noncomputable def carrierBackwardAction (code : CarrierCode) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldExtensionPermutationBackwardAction (Fin 4) code.2 *
    G122CarrierSeparatedComparisonLocalModel.carrierBackwardAction code.1

/-- The actual stored-backward action separates all three carrier codes. -/
theorem carrierBackwardAction_injective :
    Function.Injective carrierBackwardAction := by
  intro first second equality
  have unopEquality := congrArg MulOpposite.unop equality
  change
    (finiteAxisFoldTransportedSourceContextPermutation first.1.2.evaluate⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1)⁻¹) *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm first.2)⁻¹ =
      (finiteAxisFoldTransportedSourceContextPermutation second.1.2.evaluate⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1)⁻¹) *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm second.2)⁻¹
    at unopEquality
  have sourceEquality :
      sourceTripleAction
          (((FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1)⁻¹,
              first.1.2.evaluate⁻¹),
            (FiniteAxisFoldExtensionPermutationCode.toPerm first.2)⁻¹) =
        sourceTripleAction
          (((FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1)⁻¹,
              second.1.2.evaluate⁻¹),
            (FiniteAxisFoldExtensionPermutationCode.toPerm second.2)⁻¹) := by
    apply Equiv.ext
    intro sourceContext
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
        finiteAxisFoldSourceToActualContextEquiv.symm
          (permutation (finiteAxisFoldSourceToActualContextEquiv sourceContext)))
      unopEquality
    simp [finiteAxisFoldTransportedSourceContextPermutation,
      map_inv] at evaluated
    have firstInner := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
        (FiniteAxisFoldExtensionPermutationCode.toPerm first.2))⁻¹ sourceContext)
    have firstOuter := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
        (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1))⁻¹
          (finiteAxisFoldSourceToActualContextEquiv.symm
            (finiteAxisFoldSourceToActualContextEquiv
              (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                (FiniteAxisFoldExtensionPermutationCode.toPerm first.2))⁻¹
                  sourceContext))))
    have secondInner := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
        (FiniteAxisFoldExtensionPermutationCode.toPerm second.2))⁻¹ sourceContext)
    have secondOuter := finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply
      (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
        (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1))⁻¹
          (finiteAxisFoldSourceToActualContextEquiv.symm
            (finiteAxisFoldSourceToActualContextEquiv
              (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                (FiniteAxisFoldExtensionPermutationCode.toPerm second.2))⁻¹
                  sourceContext))))
    have firstSimplify :
        ((finiteAxisFoldSourceContextObjectPermHom Nat first.1.2.evaluate)⁻¹)
            (finiteAxisFoldSourceToActualContextEquiv.symm
              (finiteAxisFoldSourceToActualContextEquiv
                (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
                    (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1))⁻¹
                  (finiteAxisFoldSourceToActualContextEquiv.symm
                    (finiteAxisFoldSourceToActualContextEquiv
                      (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                        (FiniteAxisFoldExtensionPermutationCode.toPerm first.2))⁻¹
                          sourceContext)))))) =
          ((finiteAxisFoldSourceContextObjectPermHom Nat first.1.2.evaluate)⁻¹)
            (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
                (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1))⁻¹
              (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                (FiniteAxisFoldExtensionPermutationCode.toPerm first.2))⁻¹
                  sourceContext)) := by
      apply congrArg
      exact firstOuter.trans
        (congrArg
          (fun context =>
            ((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
              (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1))⁻¹
                context)
          firstInner)
    have secondSimplify :
        ((finiteAxisFoldSourceContextObjectPermHom Nat second.1.2.evaluate)⁻¹)
            (finiteAxisFoldSourceToActualContextEquiv.symm
              (finiteAxisFoldSourceToActualContextEquiv
                (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
                    (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1))⁻¹
                  (finiteAxisFoldSourceToActualContextEquiv.symm
                    (finiteAxisFoldSourceToActualContextEquiv
                      (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                        (FiniteAxisFoldExtensionPermutationCode.toPerm second.2))⁻¹
                          sourceContext)))))) =
          ((finiteAxisFoldSourceContextObjectPermHom Nat second.1.2.evaluate)⁻¹)
            (((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
                (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1))⁻¹
              (((finiteAxisFoldSourceContextObjectPermHom (Fin 4))
                (FiniteAxisFoldExtensionPermutationCode.toPerm second.2))⁻¹
                  sourceContext)) := by
      apply congrArg
      exact secondOuter.trans
        (congrArg
          (fun context =>
            ((finiteAxisFoldSourceContextObjectPermHom (Fin 3))
              (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1))⁻¹
                context)
          secondInner)
    have plain := firstSimplify.symm.trans (evaluated.trans secondSimplify)
    simpa [sourceTripleAction,
      G122CarrierSeparatedComparisonLocalModel.sourcePairAction] using plain
  have tripleEquality := sourceTripleAction_injective sourceEquality
  apply Prod.ext
  · apply Prod.ext
    · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
      exact inv_injective (congrArg (fun triple => triple.1.1) tripleEquality)
    · apply FiniteAxisFoldNatAlgorithmNormalForm.evaluate_injective
      exact inv_injective (congrArg (fun triple => triple.1.2) tripleEquality)
  · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    exact inv_injective (congrArg Prod.snd tripleEquality)

/-- Independent axis and three-carrier local data. -/
abbrev LocalCode := Equiv.Perm (Fin 3) × CarrierCode

/-- Evaluate the new finite-carrier table as an actual normalized endpoint
automorphism. -/
noncomputable def fin4Aut (code : Fin4Code) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  (finiteAxisFoldExtensionPermutationDecoder (Fin 4) code).1.1.1.1

/-- Apply the new finite-carrier action before the accepted carrier product. -/
noncomputable def carrierAut (code : CarrierCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  fin4Aut code.2 *
    G122CarrierSeparatedComparisonLocalModel.carrierAut code.1

/-- Evaluate all four components with the global axis section last. -/
noncomputable def localAut (code : LocalCode) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  carrierAut code.2 * finiteAxisFoldNormalizedAxisSectionHom code.1

/-- The new finite-carrier action is invisible to global axis projection. -/
theorem fin4Aut_axisProjection_eq_one (code : Fin4Code) :
    finiteAxisFoldNormalizedAxisProjection (fin4Aut code) = 1 := by
  exact MonoidHom.mem_ker.mp
    (finiteAxisFoldExtensionPermutationDecoder (Fin 4) code).1.1.1.2

/-- The complete carrier action is invisible to global axis projection. -/
theorem carrierAut_axisProjection_eq_one (code : CarrierCode) :
    finiteAxisFoldNormalizedAxisProjection (carrierAut code) = 1 := by
  rw [carrierAut, map_mul, fin4Aut_axisProjection_eq_one,
    G122CarrierSeparatedComparisonLocalModel.carrierAut_axisProjection_eq_one,
    one_mul]

/-- Global axis projection reads the first local-code component. -/
theorem localAut_axisProjection (code : LocalCode) :
    finiteAxisFoldNormalizedAxisProjection (localAut code) = code.1 := by
  rw [localAut, map_mul, carrierAut_axisProjection_eq_one,
    finiteAxisFoldNormalizedAxisProjection_section, one_mul]

/-- Actual backward observation of the `Fin 4` table is its primitive source
action. -/
theorem fin4Aut_backwardObservation (code : Fin4Code) :
    backwardObservation (fin4Aut code) =
      finiteAxisFoldExtensionPermutationBackwardAction (Fin 4) code := by
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (finiteAxisFoldExtensionPermutationDecoder (Fin 4) code) = _
  exact finiteAxisFoldExtensionPermutationDecoder_backwardProjection code

/-- Actual backward observation of the three-carrier product is the expected
joint action. -/
theorem carrierAut_backwardObservation (code : CarrierCode) :
    backwardObservation (carrierAut code) = carrierBackwardAction code := by
  change finiteAxisFoldNormalizedContextBackwardProjection
      (fin4Aut code.2 *
        G122CarrierSeparatedComparisonLocalModel.carrierAut code.1) = _
  rw [map_mul]
  change backwardObservation (fin4Aut code.2) *
      backwardObservation
        (G122CarrierSeparatedComparisonLocalModel.carrierAut code.1) = _
  rw [fin4Aut_backwardObservation,
    G122CarrierSeparatedComparisonLocalModel.carrierAut_backwardObservation]
  rfl

/-- Removing the observed axis section leaves precisely the carrier product. -/
theorem localAut_stripped (code : LocalCode) :
    strippedAut (localAut code) = carrierAut code.2 := by
  rw [strippedAut, localAut_axisProjection, localAut]
  simp

/-- Backward observation after axis removal recovers all three carrier
components. -/
theorem localAut_backwardObservation (code : LocalCode) :
    backwardObservation (strippedAut (localAut code)) =
      carrierBackwardAction code.2 := by
  rw [localAut_stripped]
  exact carrierAut_backwardObservation code.2

/-- Axis projection and carrier-separated backward observation jointly
separate all four local components. -/
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

/-- Source projection of an assembled comparison is its endpoint
automorphism. -/
@[simp] theorem localComparison_source (code : LocalCode) :
    generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom (localComparison code) =
      localAut code := by
  rfl

/-- Actual normalized comparisons represented by four-component codes. -/
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

/-- Every represented observation has exactly one three-carrier code. -/
theorem carrierTarget_existsUnique (comparison : LocalComparisonImage) :
    ∃! code : CarrierCode,
      carrierBackwardAction code = carrierTarget comparison := by
  rcases comparison with ⟨comparison, code, rfl⟩
  refine ⟨code.2, ?_, ?_⟩
  · exact (localAut_backwardObservation code).symm
  · intro candidate candidateEquality
    apply carrierBackwardAction_injective
    exact candidateEquality.trans (localAut_backwardObservation code)

/-- Recover the unique three-carrier code selected by actual observation. -/
noncomputable def readCarrier (comparison : LocalComparisonImage) : CarrierCode :=
  Classical.choose (carrierTarget_existsUnique comparison)

/-- Any carrier code realizing the observation is the recovered code. -/
theorem readCarrier_unique (comparison : LocalComparisonImage)
    (code : CarrierCode)
    (equality : carrierBackwardAction code = carrierTarget comparison) :
    code = readCarrier comparison :=
  (Classical.choose_spec (carrierTarget_existsUnique comparison)).2 code equality

/-- Read all four independent components from an actual comparison. -/
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

/-- Two-sided reconstruction between independent local data and the actual
represented comparison image. -/
noncomputable def localComparisonEquiv : LocalCode ≃ LocalComparisonImage where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Identity table on the new finite carrier. -/
def fin4IdentityCode : Fin4Code :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm 1

/-- The identity table evaluates to the identity permutation. -/
@[simp] theorem fin4IdentityCode_toPerm :
    FiniteAxisFoldExtensionPermutationCode.toPerm fin4IdentityCode = 1 :=
  FiniteAxisFoldExtensionPermutationCode.toPerm_ofPerm 1

/-- The actual evaluation of the identity `Fin 4` table is identity. -/
@[simp] theorem fin4Aut_identityCode : fin4Aut fin4IdentityCode = 1 := by
  have code_eq_one : fin4IdentityCode = 1 := by
    apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    exact fin4IdentityCode_toPerm
  rw [fin4Aut, code_eq_one, map_one]
  rfl

/-- Embed a Cycle 51 code by adjoining the identity `Fin 4` table. -/
def embedCarrierSeparatedCode
    (code : G122CarrierSeparatedComparisonLocalModel.LocalCode) : LocalCode :=
  (code.1, (code.2, fin4IdentityCode))

/-- Adjoining the identity table preserves distinct Cycle 51 codes. -/
theorem embedCarrierSeparatedCode_injective :
    Function.Injective embedCarrierSeparatedCode := by
  intro first second equality
  exact Prod.ext (congrArg (fun code : LocalCode => code.1) equality)
    (congrArg (fun code : LocalCode => code.2.1) equality)

/-- Endpoint evaluation of an embedded code agrees with Cycle 51. -/
theorem localAut_embedCarrierSeparatedCode
    (code : G122CarrierSeparatedComparisonLocalModel.LocalCode) :
    localAut (embedCarrierSeparatedCode code) =
      G122CarrierSeparatedComparisonLocalModel.localAut code := by
  simp [localAut, carrierAut, embedCarrierSeparatedCode,
    G122CarrierSeparatedComparisonLocalModel.localAut]

/-- Comparison assembly of an embedded code agrees with Cycle 51. -/
theorem localComparison_embedCarrierSeparatedCode
    (code : G122CarrierSeparatedComparisonLocalModel.LocalCode) :
    localComparison (embedCarrierSeparatedCode code) =
      G122CarrierSeparatedComparisonLocalModel.localComparison code := by
  rw [localComparison,
    G122CarrierSeparatedComparisonLocalModel.localComparison,
    localAut_embedCarrierSeparatedCode]

/-- Embed every Cycle 51 comparison by its unique local code. -/
noncomputable def embedCarrierSeparatedImage
    (comparison : G122CarrierSeparatedComparisonLocalModel.LocalComparisonImage) :
    LocalComparisonImage :=
  assemble (embedCarrierSeparatedCode
    (G122CarrierSeparatedComparisonLocalModel.read comparison))

/-- The Cycle 51 comparison-image embedding is injective. -/
theorem embedCarrierSeparatedImage_injective :
    Function.Injective embedCarrierSeparatedImage := by
  intro first second equality
  have codeEquality :
      embedCarrierSeparatedCode
          (G122CarrierSeparatedComparisonLocalModel.read first) =
        embedCarrierSeparatedCode
          (G122CarrierSeparatedComparisonLocalModel.read second) :=
    localComparisonEquiv.injective equality
  exact G122CarrierSeparatedComparisonLocalModel.localComparisonEquiv.symm.injective
    (embedCarrierSeparatedCode_injective codeEquality)

/-- The Cycle 51 image as a subtype embedding into the enlarged image. -/
noncomputable def carrierSeparatedImageEmbedding :
    G122CarrierSeparatedComparisonLocalModel.LocalComparisonImage ↪
      LocalComparisonImage :=
  ⟨embedCarrierSeparatedImage, embedCarrierSeparatedImage_injective⟩

/-- Transposition of the first two points of the new finite carrier. -/
def fin4SwapCode : Fin4Code :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm (Equiv.swap 0 1)

/-- The new table evaluates to the stated transposition. -/
@[simp] theorem fin4SwapCode_toPerm :
    FiniteAxisFoldExtensionPermutationCode.toPerm fin4SwapCode =
      Equiv.swap 0 1 :=
  FiniteAxisFoldExtensionPermutationCode.toPerm_ofPerm (Equiv.swap 0 1)

/-- Local code with accepted components trivial and the new table nontrivial. -/
def fin4SwapLocalCode : LocalCode :=
  (1, ((G122CarrierSeparatedComparisonLocalModel.identityExtensionCode,
      G122CarrierSeparatedComparisonLocalModel.natIdentityCode), fin4SwapCode))

/-- The explicit `Fin 4` swap comparison is outside every embedded Cycle 51
comparison. -/
theorem fin4SwapLocalCode_not_embedded
    (comparison : G122CarrierSeparatedComparisonLocalModel.LocalComparisonImage) :
    assemble fin4SwapLocalCode ≠ embedCarrierSeparatedImage comparison := by
  intro equality
  have codeEquality := localComparisonEquiv.injective equality
  have fin4Equality := congrArg (fun code : LocalCode => code.2.2) codeEquality
  have evaluationEquality := congrArg
    FiniteAxisFoldExtensionPermutationCode.toPerm fin4Equality
  change
    FiniteAxisFoldExtensionPermutationCode.toPerm fin4SwapCode =
      FiniteAxisFoldExtensionPermutationCode.toPerm fin4IdentityCode
    at evaluationEquality
  rw [fin4SwapCode_toPerm, fin4IdentityCode_toPerm] at evaluationEquality
  have moved := congrArg (fun permutation : Equiv.Perm (Fin 4) => permutation 0)
    evaluationEquality
  norm_num at moved

/-- The Cycle 51 image is a proper subimage of the four-component image. -/
theorem carrierSeparatedImageEmbedding_not_surjective :
    ¬ Function.Surjective carrierSeparatedImageEmbedding := by
  intro surjective
  obtain ⟨comparison, equality⟩ := surjective (assemble fin4SwapLocalCode)
  exact fin4SwapLocalCode_not_embedded comparison equality.symm

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
four-component code. -/
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

/-- Four-component section-code uniqueness and full-kernel torsor recovery
hold together on every represented lift fiber. -/
theorem fourComponent_fullKernel_reconstruction
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
end AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel
