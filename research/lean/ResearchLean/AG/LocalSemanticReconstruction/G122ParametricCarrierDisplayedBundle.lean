import ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Parametric fresh-carrier reconstruction for G-122 displayed bundles

An arbitrary finite Extension carrier, distinct from the three carriers already
used by the accepted four-component comparison model, supplies one further
independent permutation table.  Carrier-specific source probes separate the
new action from every accepted component.  The corresponding actual
comparison image is reconstructed in both directions.  Every nontrivial such
carrier gives a proper enlargement, with `Fin 5` as a concrete instance.

The same construction assembles the independent comparison table and source
kernel group code into a dependent displayed-lift bundle.  It proves actual
orbit separation, both total inverse laws, agreement with the ambient kernel
action, unique subgroup displacement, and source-action equivariance in this
module rather than postponing the connection.

The result remains a represented family.  It does not claim coverage of the
full comparison group or the full restriction kernel.
-/

namespace AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open TransportCoherence FullGeometryNormalization
open AAT.AG.RealizationReconstruction MulAction Set Subgroup

noncomputable section

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

/-- Decidable atom equality for the fixed finite-axis-fold input. -/
local instance parametricCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

open G122FourComponentComparisonLocalModel
open G122DisplayedKernelGroupTorsor
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel

/-- The accepted finite carriers have different cardinalities. -/
private theorem fin3_ne_fin4 : Fin 3 ≠ Fin 4 := by
  intro equality
  have cardinality := Fintype.card_congr (Equiv.cast equality)
  norm_num at cardinality

private theorem fin4_ne_fin3 : Fin 4 ≠ Fin 3 := Ne.symm fin3_ne_fin4

/-- The accepted infinite carrier is not either accepted finite carrier. -/
private theorem nat_ne_fin3 : Nat ≠ Fin 3 := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 3))
  exact Fintype.false finiteNat

private theorem fin3_ne_nat : Fin 3 ≠ Nat := Ne.symm nat_ne_fin3

private theorem nat_ne_fin4 : Nat ≠ Fin 4 := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 4))
  exact Fintype.false finiteNat

private theorem fin4_ne_nat : Fin 4 ≠ Nat := Ne.symm nat_ne_fin4

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

section FreshCarrier

variable (E : Type) [Fintype E] [DecidableEq E]

/-- A fresh-carrier action fixes every accepted `Fin 3` probe. -/
theorem freshAction_fixes_fin3Probe
    (fresh3 : E ≠ Fin 3) (permutation : Equiv.Perm E) (value : Fin 3) :
    (finiteAxisFoldSourceContextObjectPermHom E permutation)
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
    finiteAxisFoldExtensionValuePermutation, fresh3.symm]

/-- A fresh-carrier action fixes every accepted `Nat` probe. -/
theorem freshAction_fixes_natProbe
    (freshNat : E ≠ Nat) (permutation : Equiv.Perm E) (value : Nat) :
    (finiteAxisFoldSourceContextObjectPermHom E permutation)
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
    finiteAxisFoldExtensionValuePermutation, freshNat.symm]

/-- A fresh-carrier action fixes every accepted `Fin 4` probe. -/
theorem freshAction_fixes_fin4Probe
    (fresh4 : E ≠ Fin 4) (permutation : Equiv.Perm E) (value : Fin 4) :
    (finiteAxisFoldSourceContextObjectPermHom E permutation)
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
    finiteAxisFoldExtensionValuePermutation, fresh4.symm]

/-- On its own carrier, the fresh action applies the supplied permutation to
the primitive probe value. -/
theorem freshAction_on_freshProbe
    (permutation : Equiv.Perm E) (value : E) :
    (finiteAxisFoldSourceContextObjectPermHom E permutation)
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe (permutation value)⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply sourceContextObject_eq_of_ctx_eq
  simp [finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation]

/-- Every accepted carrier action fixes a probe on the fresh carrier. -/
theorem acceptedAction_fixes_freshProbe
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (triple : (Equiv.Perm (Fin 3) × Equiv.Perm Nat) × Equiv.Perm (Fin 4))
    (value : E) :
    G122FourComponentComparisonLocalModel.sourceTripleAction triple
        (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
          FiniteAxisFoldSourceContextObject) =
      (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
        FiniteAxisFoldSourceContextObject) := by
  apply sourceContextObject_eq_of_ctx_eq
  simp [G122FourComponentComparisonLocalModel.sourceTripleAction,
    G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
    finiteAxisFoldSourceContextObjectPermHom,
    finiteAxisFoldSourceContextObjectPerm,
    finiteAxisFoldSourceContextObjectPermutation,
    finiteAxisFoldSourceContextPermutation,
    finiteAxisFoldSourceExtensionProbe,
    finiteAxisFoldExtensionValuePermutation, fresh3, fresh4, freshNat]

/-- Joint primitive source action of the accepted carriers and one arbitrary
fresh finite carrier. -/
def sourceFreshAction
    (code : ((Equiv.Perm (Fin 3) × Equiv.Perm Nat) ×
      Equiv.Perm (Fin 4)) × Equiv.Perm E) :
    Equiv.Perm FiniteAxisFoldSourceContextObject :=
  G122FourComponentComparisonLocalModel.sourceTripleAction code.1 *
    finiteAxisFoldSourceContextObjectPermHom E code.2

/-- Carrier-specific primitive probes separate the accepted triple and the
fresh permutation simultaneously. -/
theorem sourceFreshAction_injective
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    Function.Injective (sourceFreshAction E) := by
  intro first second equality
  apply Prod.ext
  · apply Prod.ext
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
            (⟨Fin 3, first.1.1.1 value⟩ : Sigma fun carrier : Type => carrier) =
              ⟨Fin 3, second.1.1.1 value⟩ := by
          simpa [sourceFreshAction,
            G122FourComponentComparisonLocalModel.sourceTripleAction,
            G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
            finiteAxisFoldSourceContextObjectPermHom,
            finiteAxisFoldSourceContextObjectPerm,
            finiteAxisFoldSourceContextObjectPermutation,
            finiteAxisFoldSourceContextPermutation,
            finiteAxisFoldSourceExtensionProbe,
            finiteAxisFoldExtensionValuePermutation,
            fresh3.symm, fin3_ne_fin4, fin3_ne_nat,
            G122FourComponentComparisonLocalModel.fin3Action_fixes_fin4Probe,
            G122FourComponentComparisonLocalModel.fin4Action_fixes_fin3Probe]
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
            (⟨Nat, first.1.1.2 value⟩ : Sigma fun carrier : Type => carrier) =
              ⟨Nat, second.1.1.2 value⟩ := by
          simpa [sourceFreshAction,
            G122FourComponentComparisonLocalModel.sourceTripleAction,
            G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
            finiteAxisFoldSourceContextObjectPermHom,
            finiteAxisFoldSourceContextObjectPerm,
            finiteAxisFoldSourceContextObjectPermutation,
            finiteAxisFoldSourceContextPermutation,
            finiteAxisFoldSourceExtensionProbe,
            finiteAxisFoldExtensionValuePermutation,
            freshNat.symm, nat_ne_fin3, nat_ne_fin4]
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
          (⟨Fin 4, first.1.2 value⟩ : Sigma fun carrier : Type => carrier) =
            ⟨Fin 4, second.1.2 value⟩ := by
        simpa [sourceFreshAction,
          G122FourComponentComparisonLocalModel.sourceTripleAction,
          G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
          finiteAxisFoldSourceContextObjectPermHom,
          finiteAxisFoldSourceContextObjectPerm,
          finiteAxisFoldSourceContextObjectPermutation,
          finiteAxisFoldSourceContextPermutation,
          finiteAxisFoldSourceExtensionProbe,
          finiteAxisFoldExtensionValuePermutation,
          fresh4.symm, fin4_ne_fin3, fin4_ne_nat]
          using extensionSigmaEquality
      exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2
  · apply Equiv.ext
    intro value
    have evaluated := congrArg
      (fun permutation : Equiv.Perm FiniteAxisFoldSourceContextObject =>
        permutation
          (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
            FiniteAxisFoldSourceContextObject)) equality
    change
      G122FourComponentComparisonLocalModel.sourceTripleAction first.1
          ((finiteAxisFoldSourceContextObjectPermHom E first.2)
            (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
              FiniteAxisFoldSourceContextObject)) =
        G122FourComponentComparisonLocalModel.sourceTripleAction second.1
          ((finiteAxisFoldSourceContextObjectPermHom E second.2)
            (⟨finiteAxisFoldSourceExtensionProbe value⟩ :
              FiniteAxisFoldSourceContextObject))
      at evaluated
    rw [freshAction_on_freshProbe E first.2 value,
      freshAction_on_freshProbe E second.2 value,
      acceptedAction_fixes_freshProbe E fresh3 fresh4 freshNat
        first.1 (first.2 value),
      acceptedAction_fixes_freshProbe E fresh3 fresh4 freshNat
        second.1 (second.2 value)] at evaluated
    have extensionSigmaEquality := congrArg
      (fun W : FiniteAxisFoldSourceContextObject =>
        (⟨W.ctx.Extension, W.ctx.extension⟩ :
          Sigma fun carrier : Type => carrier)) evaluated
    have probeEquality :
        (⟨E, first.2 value⟩ : Sigma fun carrier : Type => carrier) =
          ⟨E, second.2 value⟩ := by
      exact extensionSigmaEquality
    exact eq_of_heq (Sigma.mk.inj_iff.mp probeEquality).2

/-- Conjugation through the fixed source-to-actual context equivalence, now
defined on the whole source permutation group. -/
noncomputable def transportSourceActionHom :
    Equiv.Perm FiniteAxisFoldSourceContextObject →*
      Equiv.Perm FiniteAxisFoldResidualContextObject where
  toFun permutation :=
    finiteAxisFoldSourceToActualContextEquiv.symm.trans
      (permutation.trans finiteAxisFoldSourceToActualContextEquiv)
  map_one' := by
    apply Equiv.ext
    intro context
    exact finiteAxisFoldSourceToActualContextEquiv.apply_symm_apply context
  map_mul' first second := by
    apply Equiv.ext
    intro context
    change finiteAxisFoldSourceToActualContextEquiv
        (first (second (finiteAxisFoldSourceToActualContextEquiv.symm context))) =
      finiteAxisFoldSourceToActualContextEquiv
        (first (finiteAxisFoldSourceToActualContextEquiv.symm
          (finiteAxisFoldSourceToActualContextEquiv
            (second (finiteAxisFoldSourceToActualContextEquiv.symm context)))))
    rw [finiteAxisFoldSourceToActualContextEquiv.symm_apply_apply]

/-- Fixed-route conjugation loses no primitive source action. -/
theorem transportSourceActionHom_injective :
    Function.Injective transportSourceActionHom := by
  intro first second equality
  apply Equiv.ext
  intro context
  have evaluated := congrArg
    (fun permutation : Equiv.Perm FiniteAxisFoldResidualContextObject =>
      finiteAxisFoldSourceToActualContextEquiv.symm
        (permutation (finiteAxisFoldSourceToActualContextEquiv context))) equality
  simpa [transportSourceActionHom] using evaluated

/-- The existing transported fixed-carrier action is the restriction of
whole-source conjugation. -/
theorem transportSourceActionHom_sourceCarrier
    (permutation : Equiv.Perm E) :
    transportSourceActionHom
        (finiteAxisFoldSourceContextObjectPermHom E permutation) =
      finiteAxisFoldTransportedSourceContextPermutation permutation :=
  rfl

/-- Independent lookup-table syntax for the additional finite carrier. -/
abbrev FreshCode := FiniteAxisFoldExtensionPermutationCode E

/-- Accepted three-carrier data together with one new arbitrary carrier. -/
abbrev CarrierCode :=
  G122FourComponentComparisonLocalModel.CarrierCode × FreshCode E

/-- Stored-backward observation expected from all four carrier tables. -/
noncomputable def carrierBackwardAction (code : CarrierCode E) :
    (Equiv.Perm FiniteAxisFoldResidualContextObject)ᵐᵒᵖ :=
  finiteAxisFoldExtensionPermutationBackwardAction E code.2 *
    G122FourComponentComparisonLocalModel.carrierBackwardAction code.1

/-- Actual stored-backward observation separates every accepted carrier table
and the arbitrary fresh table. -/
theorem carrierBackwardAction_injective
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    Function.Injective (carrierBackwardAction E) := by
  intro first second equality
  have unopEquality := congrArg MulOpposite.unop equality
  change
    (finiteAxisFoldTransportedSourceContextPermutation first.1.1.2.evaluate⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1.1)⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.2)⁻¹) *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm first.2)⁻¹ =
      (finiteAxisFoldTransportedSourceContextPermutation second.1.1.2.evaluate⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1.1)⁻¹ *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.2)⁻¹) *
        finiteAxisFoldTransportedSourceContextPermutation
          (FiniteAxisFoldExtensionPermutationCode.toPerm second.2)⁻¹
    at unopEquality
  have transportedEquality :
      transportSourceActionHom
          (sourceFreshAction E
            ((((FiniteAxisFoldExtensionPermutationCode.toPerm first.1.1.1)⁻¹,
                first.1.1.2.evaluate⁻¹),
              (FiniteAxisFoldExtensionPermutationCode.toPerm first.1.2)⁻¹),
              (FiniteAxisFoldExtensionPermutationCode.toPerm first.2)⁻¹)) =
        transportSourceActionHom
          (sourceFreshAction E
            ((((FiniteAxisFoldExtensionPermutationCode.toPerm second.1.1.1)⁻¹,
                second.1.1.2.evaluate⁻¹),
              (FiniteAxisFoldExtensionPermutationCode.toPerm second.1.2)⁻¹),
              (FiniteAxisFoldExtensionPermutationCode.toPerm second.2)⁻¹)) := by
    simpa [sourceFreshAction,
      G122FourComponentComparisonLocalModel.sourceTripleAction,
      G122CarrierSeparatedComparisonLocalModel.sourcePairAction,
      map_mul, transportSourceActionHom_sourceCarrier] using unopEquality
  have sourceEquality :=
    transportSourceActionHom_injective transportedEquality
  have codeEquality :=
    sourceFreshAction_injective E fresh3 fresh4 freshNat sourceEquality
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
        exact inv_injective (congrArg (fun code => code.1.1.1) codeEquality)
      · apply FiniteAxisFoldNatAlgorithmNormalForm.evaluate_injective
        exact inv_injective (congrArg (fun code => code.1.1.2) codeEquality)
    · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
      exact inv_injective (congrArg (fun code => code.1.2) codeEquality)
  · apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    exact inv_injective (congrArg Prod.snd codeEquality)

/-- Independent accepted four-component code and one fresh-carrier table. -/
abbrev LocalCode :=
  G122FourComponentComparisonLocalModel.LocalCode × FreshCode E

/-- Evaluate the fresh table as an actual normalized endpoint automorphism. -/
noncomputable def freshAut (code : FreshCode E) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  (finiteAxisFoldExtensionPermutationDecoder E code).1.1.1.1

/-- Evaluate the fresh action before the accepted four-component action. -/
noncomputable def localAut (code : LocalCode E) :
    Aut FiniteAxisFoldNormalizedDirectGeometry :=
  freshAut E code.2 *
    G122FourComponentComparisonLocalModel.localAut code.1

/-- The fresh action is invisible to the global axis projection. -/
theorem freshAut_axisProjection_eq_one (code : FreshCode E) :
    finiteAxisFoldNormalizedAxisProjection (freshAut E code) = 1 := by
  exact MonoidHom.mem_ker.mp
    (finiteAxisFoldExtensionPermutationDecoder E code).1.1.1.2

/-- Global axis projection reads the accepted axis component unchanged. -/
theorem localAut_axisProjection (code : LocalCode E) :
    finiteAxisFoldNormalizedAxisProjection (localAut E code) = code.1.1 := by
  rw [localAut, map_mul, freshAut_axisProjection_eq_one,
    G122FourComponentComparisonLocalModel.localAut_axisProjection, one_mul]

/-- Actual backward observation of the fresh table is its primitive source
action transported along the fixed route. -/
theorem freshAut_backwardObservation (code : FreshCode E) :
    G122MixedAxisExtensionLocalModel.backwardObservation
        (freshAut E code) =
      finiteAxisFoldExtensionPermutationBackwardAction E code := by
  change finiteAxisFoldResidualLocalFiberKernelBackwardProjection
      (finiteAxisFoldExtensionPermutationDecoder E code) = _
  exact finiteAxisFoldExtensionPermutationDecoder_backwardProjection code

/-- Removing the global axis section leaves the fresh action followed by all
accepted carrier actions. -/
theorem localAut_stripped (code : LocalCode E) :
    G122MixedAxisExtensionLocalModel.strippedAut (localAut E code) =
      freshAut E code.2 *
        G122FourComponentComparisonLocalModel.carrierAut code.1.2 := by
  rw [G122MixedAxisExtensionLocalModel.strippedAut,
    localAut_axisProjection, localAut,
    G122FourComponentComparisonLocalModel.localAut]
  simp [mul_assoc]

/-- Backward observation after removing the axis section recovers the joint
four-carrier action. -/
theorem localAut_backwardObservation (code : LocalCode E) :
    G122MixedAxisExtensionLocalModel.backwardObservation
        (G122MixedAxisExtensionLocalModel.strippedAut
          (localAut E code)) =
      carrierBackwardAction E (code.1.2, code.2) := by
  rw [localAut_stripped]
  change finiteAxisFoldNormalizedContextBackwardProjection
      (freshAut E code.2 *
        G122FourComponentComparisonLocalModel.carrierAut code.1.2) = _
  rw [map_mul]
  change G122MixedAxisExtensionLocalModel.backwardObservation
        (freshAut E code.2) *
      G122MixedAxisExtensionLocalModel.backwardObservation
        (G122FourComponentComparisonLocalModel.carrierAut code.1.2) = _
  rw [freshAut_backwardObservation,
    G122FourComponentComparisonLocalModel.carrierAut_backwardObservation]
  rfl

/-- Axis and stored-backward observations separate every component of the
parametric local code. -/
theorem localAut_injective
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    Function.Injective (localAut E) := by
  intro first second equality
  apply Prod.ext
  · apply Prod.ext
    · rw [← localAut_axisProjection E first,
        ← localAut_axisProjection E second, equality]
    · have carrierEquality :
          carrierBackwardAction E (first.1.2, first.2) =
            carrierBackwardAction E (second.1.2, second.2) := by
        rw [← localAut_backwardObservation E first,
          ← localAut_backwardObservation E second, equality]
      exact congrArg (fun code : CarrierCode E => code.1)
        (carrierBackwardAction_injective E fresh3 fresh4 freshNat
          carrierEquality)
  · have carrierEquality :
        carrierBackwardAction E (first.1.2, first.2) =
          carrierBackwardAction E (second.1.2, second.2) := by
      rw [← localAut_backwardObservation E first,
        ← localAut_backwardObservation E second, equality]
    exact congrArg (fun code : CarrierCode E => code.2)
      (carrierBackwardAction_injective E fresh3 fresh4 freshNat carrierEquality)

/-- Assemble a parametric local code into an actual normalized comparison. -/
noncomputable def localComparison (code : LocalCode E) : NormalizedComparison :=
  generatedArrowComparisonSectionHom finiteAxisFoldNormalizedBarAlphaIso
    (localAut E code)

/-- Source projection of an assembled comparison is its endpoint
automorphism. -/
@[simp] theorem localComparison_source (code : LocalCode E) :
    generatedArrowComparisonSourceHom
        finiteAxisFoldNormalizedBarAlphaIso.hom (localComparison E code) =
      localAut E code := by
  rfl

/-- Actual normalized comparisons represented by the parametric code. -/
abbrev LocalComparisonImage := Set.range (localComparison E)

/-- Assemble one independent code into the represented actual image. -/
noncomputable def assemble (code : LocalCode E) : LocalComparisonImage E :=
  ⟨localComparison E code, ⟨code, rfl⟩⟩

/-- Every represented comparison has exactly one parametric local code. -/
theorem code_existsUnique
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (comparison : LocalComparisonImage E) :
    ∃! code : LocalCode E, localComparison E code = comparison.1 := by
  rcases comparison with ⟨comparison, code, rfl⟩
  refine ⟨code, rfl, ?_⟩
  intro candidate equality
  apply localAut_injective E fresh3 fresh4 freshNat
  exact congrArg
    (generatedArrowComparisonSourceHom finiteAxisFoldNormalizedBarAlphaIso.hom)
    equality

/-- Read the unique parametric code selected by actual comparison
observation. -/
noncomputable def read
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (comparison : LocalComparisonImage E) : LocalCode E :=
  Classical.choose (code_existsUnique E fresh3 fresh4 freshNat comparison)

/-- Reading after assembly recovers every independent code. -/
@[simp] theorem read_assemble
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (code : LocalCode E) :
    read E fresh3 fresh4 freshNat (assemble E code) = code := by
  exact ((Classical.choose_spec
    (code_existsUnique E fresh3 fresh4 freshNat (assemble E code))).2
      code rfl).symm

/-- Assembly after reading recovers every represented actual comparison. -/
@[simp] theorem assemble_read
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (comparison : LocalComparisonImage E) :
    assemble E (read E fresh3 fresh4 freshNat comparison) = comparison := by
  apply Subtype.ext
  exact (Classical.choose_spec
    (code_existsUnique E fresh3 fresh4 freshNat comparison)).1

/-- Two-sided reconstruction for every finite carrier distinct from the three
accepted carriers. -/
noncomputable def localComparisonEquiv
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    LocalCode E ≃ LocalComparisonImage E where
  toFun := assemble E
  invFun := read E fresh3 fresh4 freshNat
  left_inv := read_assemble E fresh3 fresh4 freshNat
  right_inv := assemble_read E fresh3 fresh4 freshNat

end FreshCarrier

section NontrivialFreshCarrier

variable (E : Type) [Fintype E] [DecidableEq E] [Nontrivial E]
variable (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)

/-- Identity lookup table on an arbitrary fresh carrier. -/
def freshIdentityCode : FreshCode E :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm 1

/-- The identity fresh table evaluates to the identity actual automorphism. -/
@[simp] theorem freshAut_identityCode :
    freshAut E (freshIdentityCode E) = 1 := by
  have code_eq_one : freshIdentityCode E = 1 := by
    apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    rfl
  rw [freshAut, code_eq_one, map_one]
  rfl

/-- Embed an accepted four-component code using the identity fresh table. -/
def embedFourCodeFor
    (code : G122FourComponentComparisonLocalModel.LocalCode) : LocalCode E :=
  (code, freshIdentityCode E)

/-- The arbitrary-carrier code embedding is injective. -/
theorem embedFourCodeFor_injective : Function.Injective (embedFourCodeFor E) := by
  intro first second equality
  exact congrArg Prod.fst equality

/-- Endpoint evaluation of an embedded accepted code is unchanged. -/
theorem localAut_embedFourCodeFor
    (code : G122FourComponentComparisonLocalModel.LocalCode) :
    localAut E (embedFourCodeFor E code) =
      G122FourComponentComparisonLocalModel.localAut code := by
  simp [localAut, embedFourCodeFor]

/-- Embed the accepted actual image into the arbitrary-carrier instance. -/
noncomputable def embedFourImageFor
    (comparison : G122FourComponentComparisonLocalModel.LocalComparisonImage) :
    LocalComparisonImage E :=
  assemble E (embedFourCodeFor E
    (G122FourComponentComparisonLocalModel.read comparison))

/-- The accepted actual image remains separated after adjoining any fresh
nontrivial carrier. -/
theorem embedFourImageFor_injective
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    Function.Injective (embedFourImageFor E) := by
  intro first second equality
  have codeEquality :
      embedFourCodeFor E (G122FourComponentComparisonLocalModel.read first) =
        embedFourCodeFor E
          (G122FourComponentComparisonLocalModel.read second) :=
    (localComparisonEquiv E fresh3 fresh4 freshNat).injective equality
  exact G122FourComponentComparisonLocalModel.localComparisonEquiv.symm.injective
    (embedFourCodeFor_injective E codeEquality)

/-- First chosen point of a nontrivial fresh carrier. -/
noncomputable def firstFreshPoint : E :=
  Classical.choose (exists_pair_ne E)

/-- Second chosen point of a nontrivial fresh carrier. -/
noncomputable def secondFreshPoint : E :=
  Classical.choose (Classical.choose_spec (exists_pair_ne E))

/-- The two chosen fresh-carrier points are distinct. -/
theorem firstFreshPoint_ne_secondFreshPoint :
    firstFreshPoint E ≠ secondFreshPoint E :=
  Classical.choose_spec (Classical.choose_spec (exists_pair_ne E))

/-- A nonidentity table on every nontrivial fresh carrier. -/
noncomputable def freshSwapCode : FreshCode E :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm
    (Equiv.swap (firstFreshPoint E) (secondFreshPoint E))

/-- Local code trivial on accepted components and nontrivial on the fresh
carrier. -/
noncomputable def freshSwapLocalCode : LocalCode E :=
  ((1, ((G122CarrierSeparatedComparisonLocalModel.identityExtensionCode,
      G122CarrierSeparatedComparisonLocalModel.natIdentityCode),
      G122FourComponentComparisonLocalModel.fin4IdentityCode)),
    freshSwapCode E)

/-- The fresh swap comparison is outside the embedded accepted image for
every nontrivial fresh carrier. -/
theorem freshSwap_not_embedded
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (comparison : G122FourComponentComparisonLocalModel.LocalComparisonImage) :
    assemble E (freshSwapLocalCode E) ≠
      embedFourImageFor E comparison := by
  intro equality
  have codeEquality :=
    (localComparisonEquiv E fresh3 fresh4 freshNat).injective equality
  have freshEquality := congrArg (fun code : LocalCode E => code.2) codeEquality
  have evaluationEquality := congrArg
    FiniteAxisFoldExtensionPermutationCode.toPerm freshEquality
  change Equiv.swap (firstFreshPoint E) (secondFreshPoint E) = 1
    at evaluationEquality
  have moved := congrArg
    (fun permutation : Equiv.Perm E => permutation (firstFreshPoint E))
    evaluationEquality
  change (Equiv.swap (firstFreshPoint E) (secondFreshPoint E))
      (firstFreshPoint E) =
    (1 : Equiv.Perm E) (firstFreshPoint E) at moved
  rw [Equiv.swap_apply_left] at moved
  change secondFreshPoint E = firstFreshPoint E at moved
  exact firstFreshPoint_ne_secondFreshPoint E moved.symm

/-- Every nontrivial fresh carrier produces a proper enlargement of the
accepted actual comparison image. -/
theorem embedFourImageFor_not_surjective
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat) :
    ¬ Function.Surjective (embedFourImageFor E) := by
  intro surjective
  obtain ⟨comparison, equality⟩ :=
    surjective (assemble E (freshSwapLocalCode E))
  exact freshSwap_not_embedded E fresh3 fresh4 freshNat comparison equality.symm

end NontrivialFreshCarrier

section Fin5StrictEnlargement

/-- `Fin 5` is fresh relative to every accepted carrier. -/
theorem fin5_ne_fin3 : Fin 5 ≠ Fin 3 := by
  intro equality
  have cardinality := Fintype.card_congr (Equiv.cast equality)
  norm_num at cardinality

theorem fin5_ne_fin4 : Fin 5 ≠ Fin 4 := by
  intro equality
  have cardinality := Fintype.card_congr (Equiv.cast equality)
  norm_num at cardinality

theorem fin5_ne_nat : Fin 5 ≠ Nat := by
  intro equality
  have finiteNat : Fintype Nat := equality ▸ (inferInstance : Fintype (Fin 5))
  exact Fintype.false finiteNat

/-- Identity lookup table on the concrete fresh carrier. -/
def fin5IdentityCode : FreshCode (Fin 5) :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm 1

/-- The identity fresh table evaluates to the identity actual automorphism. -/
@[simp] theorem freshAut_fin5IdentityCode :
    freshAut (Fin 5) fin5IdentityCode = 1 := by
  have code_eq_one : fin5IdentityCode = 1 := by
    apply FiniteAxisFoldExtensionPermutationCode.toPerm_injective
    rfl
  rw [freshAut, code_eq_one, map_one]
  rfl

/-- Embed every accepted four-component code by adjoining an identity `Fin 5`
table. -/
def embedFourCode
    (code : G122FourComponentComparisonLocalModel.LocalCode) :
    LocalCode (Fin 5) :=
  (code, fin5IdentityCode)

/-- The concrete embedding is injective. -/
theorem embedFourCode_injective : Function.Injective embedFourCode := by
  intro first second equality
  exact congrArg Prod.fst equality

/-- Actual endpoint evaluation preserves every accepted four-component code. -/
theorem localAut_embedFourCode
    (code : G122FourComponentComparisonLocalModel.LocalCode) :
    localAut (Fin 5) (embedFourCode code) =
      G122FourComponentComparisonLocalModel.localAut code := by
  simp [localAut, embedFourCode]

/-- Actual comparison assembly preserves every accepted code. -/
theorem localComparison_embedFourCode
    (code : G122FourComponentComparisonLocalModel.LocalCode) :
    localComparison (Fin 5) (embedFourCode code) =
      G122FourComponentComparisonLocalModel.localComparison code := by
  rw [localComparison,
    G122FourComponentComparisonLocalModel.localComparison,
    localAut_embedFourCode]

/-- Embed the whole accepted comparison image into the `Fin 5` instance. -/
noncomputable def embedFourImage
    (comparison : G122FourComponentComparisonLocalModel.LocalComparisonImage) :
    LocalComparisonImage (Fin 5) :=
  assemble (Fin 5) (embedFourCode
    (G122FourComponentComparisonLocalModel.read comparison))

/-- The accepted actual image remains separated after the new carrier is
adjoined. -/
theorem embedFourImage_injective : Function.Injective embedFourImage := by
  intro first second equality
  have codeEquality :
      embedFourCode (G122FourComponentComparisonLocalModel.read first) =
        embedFourCode (G122FourComponentComparisonLocalModel.read second) :=
    (localComparisonEquiv (Fin 5) fin5_ne_fin3 fin5_ne_fin4 fin5_ne_nat).injective
      equality
  exact G122FourComponentComparisonLocalModel.localComparisonEquiv.symm.injective
    (embedFourCode_injective codeEquality)

/-- Swap the first two values of the concrete fresh carrier. -/
def fin5SwapCode : FreshCode (Fin 5) :=
  FiniteAxisFoldExtensionPermutationCode.ofPerm (Equiv.swap 0 1)

/-- A local code trivial on every accepted component and nontrivial on the
fresh carrier. -/
def fin5SwapLocalCode : LocalCode (Fin 5) :=
  ((1, ((G122CarrierSeparatedComparisonLocalModel.identityExtensionCode,
      G122CarrierSeparatedComparisonLocalModel.natIdentityCode),
      G122FourComponentComparisonLocalModel.fin4IdentityCode)),
    fin5SwapCode)

/-- The explicit fresh-carrier swap comparison is outside the accepted
four-component image. -/
theorem fin5Swap_not_embedded
    (comparison : G122FourComponentComparisonLocalModel.LocalComparisonImage) :
    assemble (Fin 5) fin5SwapLocalCode ≠ embedFourImage comparison := by
  intro equality
  have codeEquality :=
    (localComparisonEquiv (Fin 5) fin5_ne_fin3 fin5_ne_fin4 fin5_ne_nat).injective
      equality
  have freshEquality := congrArg (fun code : LocalCode (Fin 5) => code.2)
    codeEquality
  have evaluationEquality := congrArg
    FiniteAxisFoldExtensionPermutationCode.toPerm freshEquality
  change Equiv.swap 0 1 = 1 at evaluationEquality
  have moved := congrArg (fun permutation : Equiv.Perm (Fin 5) => permutation 0)
    evaluationEquality
  norm_num at moved

/-- The parametric construction gives a concrete proper enlargement at
`Fin 5`. -/
theorem embedFourImage_not_surjective :
    ¬ Function.Surjective embedFourImage := by
  intro surjective
  obtain ⟨comparison, equality⟩ :=
    surjective (assemble (Fin 5) fin5SwapLocalCode)
  exact fin5Swap_not_embedded comparison equality.symm

end Fin5StrictEnlargement

section DisplayedBundle

variable (E : Type) [Fintype E] [DecidableEq E]
variable (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)

/-- Full actual lift fiber over one represented parametric comparison. -/
abbrev LiftFiber (comparison : LocalComparisonImage E) :=
  AuthoredExactCanonicalComparisonLiftFiber
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1

/-- Actual canonical section lift over a represented comparison. -/
noncomputable def canonicalLift (comparison : LocalComparisonImage E) :
    LiftFiber E comparison :=
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
parametric comparison code. -/
theorem canonicalSection_unique_localCode
    (fresh3 : E ≠ Fin 3) (fresh4 : E ≠ Fin 4) (freshNat : E ≠ Nat)
    (comparison : LocalComparisonImage E) :
    ∃! code : LocalCode E,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (localComparison E code) =
        (canonicalLift E comparison).1 := by
  refine ⟨read E fresh3 fresh4 freshNat comparison, ?_, ?_⟩
  · exact congrArg
      (authoredExactCanonicalComparisonSectionHom
        finiteAxisFoldBCDatumSquare
        (Discrete.mk DoubleDiamondTwoCell.second)
        Int
        (finiteAxisFoldFixedCoefficientGeometryFamily
          (Discrete.mk DoubleDiamondTwoCell.second))
        finiteCanonicalObjectNormalization_admissible)
      (congrArg Subtype.val
        (assemble_read E fresh3 fresh4 freshNat comparison))
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
          (localComparison E candidate)) =
      restrictionHom
        (authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible comparison.1)
      at normalized
    rw [authoredExactCanonicalComparisonSection_rightInverse,
      authoredExactCanonicalComparisonSection_rightInverse] at normalized
    have imageEquality : assemble E candidate = comparison := by
      apply Subtype.ext
      exact normalized
    exact (localComparisonEquiv E fresh3 fresh4 freshNat).injective
      (imageEquality.trans
        (assemble_read E fresh3 fresh4 freshNat comparison).symm)

/-- Evaluate a source kernel-group code on the actual canonical lift. -/
noncomputable def orbitLift (comparison : LocalComparisonImage E)
    (code : GroupCode) : LiftFiber E comparison :=
  evaluate code • canonicalLift E comparison

/-- Actual action separates all source kernel-group codes. -/
theorem orbitLift_injective (comparison : LocalComparisonImage E) :
    Function.Injective (orbitLift E comparison) := by
  intro first second equality
  apply evaluate_injective
  exact authoredExactCanonicalComparisonLiftFiber_action_free
    finiteAxisFoldBCDatumSquare
    (Discrete.mk DoubleDiamondTwoCell.second)
    Int
    (finiteAxisFoldFixedCoefficientGeometryFamily
      (Discrete.mk DoubleDiamondTwoCell.second))
    finiteCanonicalObjectNormalization_admissible comparison.1
    (canonicalLift E comparison) equality

/-- Displayed actual orbit over a represented parametric comparison. -/
abbrev DisplayedFiber (comparison : LocalComparisonImage E) :=
  Set.range (orbitLift E comparison)

/-- Assemble one source kernel code into the displayed actual orbit. -/
noncomputable def orbitPoint (comparison : LocalComparisonImage E)
    (code : GroupCode) : DisplayedFiber E comparison :=
  ⟨orbitLift E comparison code, ⟨code, rfl⟩⟩

/-- Every displayed point has exactly one source kernel code. -/
theorem orbitCode_existsUnique (comparison : LocalComparisonImage E)
    (point : DisplayedFiber E comparison) :
    ∃! code : GroupCode, orbitLift E comparison code = point.1 := by
  rcases point with ⟨point, code, rfl⟩
  exact ⟨code, rfl, fun candidate equality =>
    orbitLift_injective E comparison equality⟩

/-- Read the unique source kernel code from a displayed point. -/
noncomputable def readOrbit (comparison : LocalComparisonImage E)
    (point : DisplayedFiber E comparison) : GroupCode :=
  Classical.choose (orbitCode_existsUnique E comparison point)

/-- Orbit readback and assembly are inverse in the source-to-actual
direction. -/
@[simp] theorem readOrbit_orbitPoint (comparison : LocalComparisonImage E)
    (code : GroupCode) :
    readOrbit E comparison (orbitPoint E comparison code) = code := by
  exact ((Classical.choose_spec
    (orbitCode_existsUnique E comparison (orbitPoint E comparison code))).2
      code rfl).symm

/-- Orbit assembly and readback are inverse in the actual-to-source
direction. -/
@[simp] theorem orbitPoint_readOrbit (comparison : LocalComparisonImage E)
    (point : DisplayedFiber E comparison) :
    orbitPoint E comparison (readOrbit E comparison point) = point := by
  apply Subtype.ext
  exact (Classical.choose_spec (orbitCode_existsUnique E comparison point)).1

/-- Two-sided reconstruction of every displayed fiber. -/
noncomputable def orbitEquiv (comparison : LocalComparisonImage E) :
    GroupCode ≃ DisplayedFiber E comparison where
  toFun := orbitPoint E comparison
  invFun := readOrbit E comparison
  left_inv := readOrbit_orbitPoint E comparison
  right_inv := orbitPoint_readOrbit E comparison

/-- Transport actual generated-subgroup multiplication to the displayed
fiber through source-code readback. -/
noncomputable def fiberAction (comparison : LocalComparisonImage E)
    (value : ActualSubgroup) (point : DisplayedFiber E comparison) :
    DisplayedFiber E comparison :=
  orbitPoint E comparison (G122DisplayedKernelGroupTorsor.read value *
    readOrbit E comparison point)

noncomputable instance displayedFiberSMul
    (comparison : LocalComparisonImage E) :
    SMul ActualSubgroup (DisplayedFiber E comparison) :=
  ⟨fiberAction E comparison⟩

/-- The transported operation is a genuine action on every parametric
displayed fiber. -/
noncomputable instance displayedFiberMulAction
    (comparison : LocalComparisonImage E) :
    MulAction ActualSubgroup (DisplayedFiber E comparison) where
  one_smul point := by
    change orbitPoint E comparison
      (G122DisplayedKernelGroupTorsor.read (1 : ActualSubgroup) *
        readOrbit E comparison point) = point
    rw [G122DisplayedFiberBundleReconstruction.subgroupRead_one, one_mul,
      orbitPoint_readOrbit]
  mul_smul first second point := by
    change fiberAction E comparison (first * second) point =
      fiberAction E comparison first (fiberAction E comparison second point)
    simp only [fiberAction]
    rw [readOrbit_orbitPoint,
      G122DisplayedFiberBundleReconstruction.subgroupRead_mul, mul_assoc]

/-- The transported action is the ambient actual restriction-kernel action on
underlying lifts. -/
theorem fiberAction_val (comparison : LocalComparisonImage E)
    (value : ActualSubgroup) (point : DisplayedFiber E comparison) :
    (value • point).1 = value.1 • point.1 := by
  let code := readOrbit E comparison point
  have valueEquality :
      evaluate (G122DisplayedKernelGroupTorsor.read value) = value.1 := by
    exact congrArg Subtype.val
      (G122DisplayedKernelGroupTorsor.assemble_read value)
  have pointEquality : orbitLift E comparison code = point.1 := by
    exact congrArg Subtype.val (orbitPoint_readOrbit E comparison point)
  change orbitLift E comparison
      (G122DisplayedKernelGroupTorsor.read value * code) = value.1 • point.1
  calc
    orbitLift E comparison
        (G122DisplayedKernelGroupTorsor.read value * code) =
        evaluate (G122DisplayedKernelGroupTorsor.read value) •
          orbitLift E comparison code := by
      simp only [orbitLift, evaluate_mul, mul_smul]
    _ = value.1 • orbitLift E comparison code := by rw [valueEquality]
    _ = value.1 • point.1 := congrArg (fun lift => value.1 • lift) pointEquality

/-- Between any two displayed points there is one unique actual generated
subgroup displacement. -/
theorem displayedFiber_existsUnique_smul_eq
    (comparison : LocalComparisonImage E)
    (first second : DisplayedFiber E comparison) :
    ∃! value : ActualSubgroup, value • first = second := by
  let firstCode := readOrbit E comparison first
  let secondCode := readOrbit E comparison second
  let displacement := G122DisplayedKernelGroupTorsor.assemble
    (secondCode * firstCode⁻¹)
  have actionEquality : displacement • first = second := by
    apply Subtype.ext
    rw [fiberAction_val]
    change evaluate (secondCode * firstCode⁻¹) • first.1 = second.1
    rw [← (congrArg Subtype.val (orbitPoint_readOrbit E comparison first))]
    rw [← (congrArg Subtype.val (orbitPoint_readOrbit E comparison second))]
    change evaluate (secondCode * firstCode⁻¹) •
        orbitLift E comparison firstCode = orbitLift E comparison secondCode
    calc
      evaluate (secondCode * firstCode⁻¹) •
          orbitLift E comparison firstCode =
        orbitLift E comparison ((secondCode * firstCode⁻¹) * firstCode) := by
          rw [orbitLift, ← mul_smul, ← evaluate_mul]
          rfl
      _ = orbitLift E comparison secondCode := by simp
  refine ⟨displacement, actionEquality, ?_⟩
  intro candidate candidateEquality
  apply G122DisplayedKernelGroupTorsor.sourceActualMulEquiv.symm.injective
  have actedEquality : candidate • first = displacement • first :=
    candidateEquality.trans actionEquality.symm
  have orbitEquality := congrArg Subtype.val actedEquality
  change orbitLift E comparison
      (G122DisplayedKernelGroupTorsor.read candidate * firstCode) =
    orbitLift E comparison
      (G122DisplayedKernelGroupTorsor.read displacement * firstCode)
    at orbitEquality
  exact mul_right_cancel (orbitLift_injective E comparison orbitEquality)

/-- Orbit assembly intertwines source left multiplication with the actual
generated-subgroup action. -/
theorem orbitPoint_equivariant (comparison : LocalComparisonImage E)
    (value : ActualSubgroup) (code : GroupCode) :
    orbitPoint E comparison
        (G122DisplayedKernelGroupTorsor.read value * code) =
      value • orbitPoint E comparison code := by
  change orbitPoint E comparison
      (G122DisplayedKernelGroupTorsor.read value * code) =
    orbitPoint E comparison
      (G122DisplayedKernelGroupTorsor.read value *
        readOrbit E comparison (orbitPoint E comparison code))
  rw [readOrbit_orbitPoint]

/-- Independent parametric comparison code and source kernel-group code. -/
abbrev TotalCode := LocalCode E × GroupCode

/-- Dependent total space of represented comparisons and displayed lifts. -/
abbrev TotalDisplayedSpace :=
  Σ comparison : LocalComparisonImage E, DisplayedFiber E comparison

/-- Assemble the independent comparison and kernel codes together. -/
noncomputable def totalAssemble (code : TotalCode E) :
    TotalDisplayedSpace E :=
  ⟨assemble E code.1, orbitPoint E (assemble E code.1) code.2⟩

/-- Read both independent codes from the dependent actual total space. -/
noncomputable def totalRead (point : TotalDisplayedSpace E) : TotalCode E :=
  (read E fresh3 fresh4 freshNat point.1,
    readOrbit E point.1 point.2)

/-- Reading after dependent assembly recovers both source codes. -/
@[simp] theorem totalRead_assemble (code : TotalCode E) :
    totalRead E fresh3 fresh4 freshNat (totalAssemble E code) = code := by
  rcases code with ⟨comparisonCode, kernelCode⟩
  apply Prod.ext
  · exact read_assemble E fresh3 fresh4 freshNat comparisonCode
  · exact readOrbit_orbitPoint E (assemble E comparisonCode) kernelCode

/-- Dependent assembly after reading recovers the actual comparison and
displayed lift. -/
@[simp] theorem totalAssemble_read (point : TotalDisplayedSpace E) :
    totalAssemble E (totalRead E fresh3 fresh4 freshNat point) = point := by
  rcases point with ⟨comparison, point⟩
  rcases comparison with ⟨comparisonValue, comparisonCode, rfl⟩
  change totalAssemble E
      (read E fresh3 fresh4 freshNat (assemble E comparisonCode),
        readOrbit E (assemble E comparisonCode) point) =
    ⟨assemble E comparisonCode, point⟩
  rw [read_assemble]
  simp only [totalAssemble]
  exact Sigma.ext rfl (heq_of_eq (orbitPoint_readOrbit E _ point))

/-- Product source syntax reconstructs the whole dependent displayed bundle
with both inverse laws. -/
noncomputable def totalReconstructionEquiv :
    TotalCode E ≃ TotalDisplayedSpace E where
  toFun := totalAssemble E
  invFun := totalRead E fresh3 fresh4 freshNat
  left_inv := totalRead_assemble E fresh3 fresh4 freshNat
  right_inv := totalAssemble_read E fresh3 fresh4 freshNat

/-- Parametric comparison reconstruction, dependent total reconstruction,
principal actual action, and equivariance hold on one theorem surface. -/
theorem reconstruction_principal_and_equivariant
    (point : TotalDisplayedSpace E)
    (target : DisplayedFiber E point.1)
    (value : ActualSubgroup) (code : GroupCode) :
    (∃! comparisonCode : LocalCode E,
      authoredExactCanonicalComparisonSectionHom
          finiteAxisFoldBCDatumSquare
          (Discrete.mk DoubleDiamondTwoCell.second)
          Int
          (finiteAxisFoldFixedCoefficientGeometryFamily
            (Discrete.mk DoubleDiamondTwoCell.second))
          finiteCanonicalObjectNormalization_admissible
          (localComparison E comparisonCode) =
        (canonicalLift E point.1).1) ∧
    totalAssemble E (totalRead E fresh3 fresh4 freshNat point) = point ∧
    (∃! displacement : ActualSubgroup, displacement • point.2 = target) ∧
    orbitPoint E point.1
        (G122DisplayedKernelGroupTorsor.read value * code) =
      value • orbitPoint E point.1 code :=
  ⟨canonicalSection_unique_localCode E fresh3 fresh4 freshNat point.1,
    totalAssemble_read E fresh3 fresh4 freshNat point,
    displayedFiber_existsUnique_smul_eq E point.1 point.2 target,
    orbitPoint_equivariant E point.1 value code⟩

end DisplayedBundle

end
end AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle
