import ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeReindexing
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULiftWitnesses
import ResearchLean.AG.CrossStageCoherence.FiniteWitnesses

/-!
# Finite witnesses for producer-derived cartesian reindexing

The selected reindexing functor is fired on the existing noninvertible
selective-two realized prefix.  Its endpoint package is a four-axis core
transported to the exact finite-code support point, and the target fiber carries
a genuinely nonidentity axis-swap automorphism.  The factor graph and both
functor laws are exercised with that map.

A second control uses the identity realized arrow at the same endpoint.  Its
internally chosen strong cartesian lift is an isomorphism, so the nonidentity
target automorphism cannot be sent to the identity.  This separates actual map
dependence from a constant-map implementation.  Neither control supplies a
lift, cleavage, factor, or functor-law certificate to the producer.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Decidable equality for the finite-model Atom carrier used by this witness. -/
local instance finiteCartesianReindexAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-! ## A nonidentity vertical map at the finite support endpoint -/

/-- The four-axis G-109 core transported to the finite-code support doctrine. -/
noncomputable def finiteReindexFourAxisCore : AATCorePackage FiniteModel.carrier :=
  transportAlong FiniteCrossStageWitness.core finiteModelDoctrineFromFixture

/-- The transported four-axis core lies at the exact support endpoint. -/
theorem finiteReindexFourAxisCore_point :
    packagePoint finiteReindexFourAxisCore =
      finitePortfolioSupportInstance.toSemantic := by
  rfl

/-- The transported core as an object over the target of the selective-two prefix. -/
noncomputable def finiteReindexFourAxisTarget :
    CoreFiber finiteSelectiveTwoToSupportInput.semantic.target :=
  ⟨finiteReindexFourAxisCore, by rfl⟩

/-- Swap the first two visible signature axes. -/
def finiteReindexAxisSwap : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1

/-- A vertical total endomorphism implementing the visible axis swap. -/
noncomputable def finiteReindexAxisSwapTotal :
    PackageTotalHom finiteReindexFourAxisCore finiteReindexFourAxisCore where
  base := ExtInstHom.id (packagePoint finiteReindexFourAxisCore)
  upper :=
    { SignedExactCoreReadingHom.refl finiteReindexFourAxisCore with
      axisMap := finiteReindexAxisSwap
      coordinateEquiv := fun _ => finiteReindexAxisSwap
      axis_selected_iff := fun _ => Iff.rfl
      coordinate_eq := by
        intro object axis
        rfl }
  atomEquiv_eq := rfl

/-- The axis swap as an actual morphism in the support endpoint fiber. -/
noncomputable def finiteReindexAxisSwapHom :
    finiteReindexFourAxisTarget ⟶ finiteReindexFourAxisTarget := by
  refine ⟨finiteReindexAxisSwapTotal, ?_⟩
  change (packageProjection FiniteModel.carrier).IsHomLift
    ((packageProjection FiniteModel.carrier).map finiteReindexAxisSwapTotal)
    finiteReindexAxisSwapTotal
  infer_instance

/-- Axis zero in the transported four-axis signature. -/
def finiteReindexAxisZero :
    finiteReindexFourAxisCore.reading.signatureReading.Axis := by
  change Fin 4
  exact 0

/-- Axis one in the transported four-axis signature. -/
def finiteReindexAxisOne :
    finiteReindexFourAxisCore.reading.signatureReading.Axis := by
  change Fin 4
  exact 1

/-- The two selected transported axes remain distinct. -/
theorem finiteReindexAxisZero_ne_one :
    finiteReindexAxisZero ≠ finiteReindexAxisOne := by
  change (0 : Fin 4) ≠ 1
  decide

/-- The target-fiber map actually swaps axis zero with axis one. -/
theorem finiteReindexAxisSwapHom_axis_zero :
    finiteReindexAxisSwapHom.1.upper.axisMap finiteReindexAxisZero =
      finiteReindexAxisOne := by
  change finiteReindexAxisSwap (0 : Fin 4) = 1
  simp [finiteReindexAxisSwap]

/-- The vertical target-fiber control is genuinely nonidentity. -/
theorem finiteReindexAxisSwapHom_ne_id :
    finiteReindexAxisSwapHom ≠ 𝟙 finiteReindexFourAxisTarget := by
  intro equality
  have haxis := congrArg
    (fun hom : finiteReindexFourAxisTarget ⟶ finiteReindexFourAxisTarget =>
      hom.1.upper.axisMap finiteReindexAxisZero) equality
  have hswap : finiteReindexAxisOne = finiteReindexAxisZero := by
    simpa only [finiteReindexAxisSwapHom_axis_zero] using haxis
  exact finiteReindexAxisZero_ne_one hswap.symm

/-! ## The selected functor on a noninvertible realized base arrow -/

/-- The selected regime is fired on the existing noninvertible realized prefix. -/
theorem finiteSelectiveTwoReindexInput_not_isIso :
    ¬ IsIso finiteSelectiveTwoToSupportInput.semantic.hom :=
  finiteSelectiveTwoToSupportInput_not_isIso

/-- Its generated reindexed object at the four-axis target. -/
noncomputable def finiteSelectiveTwoReindexedFourAxisObject :
    CoreFiber finiteSelectiveTwoToSupportInput.semantic.source :=
  (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput).obj
    finiteReindexFourAxisTarget

/-- The selected map action on the nonidentity vertical axis swap. -/
noncomputable def finiteSelectiveTwoReindexedAxisSwap :
    finiteSelectiveTwoReindexedFourAxisObject ⟶
      finiteSelectiveTwoReindexedFourAxisObject :=
  (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput).map
    finiteReindexAxisSwapHom

/-- The selected factor graph is fired on a noninvertible base and nonidentity map. -/
theorem finiteSelectiveTwoReindexedAxisSwap_fac :
    finiteSelectiveTwoReindexedAxisSwap.1 ≫
        (selectedCoreFiberCartesianLift finiteSelectiveTwoToSupportInput
          finiteReindexFourAxisTarget).hom =
      (selectedCoreFiberCartesianLift finiteSelectiveTwoToSupportInput
        finiteReindexFourAxisTarget).hom ≫ finiteReindexAxisSwapHom.1 :=
  selectedCoreFiberReindexFunctor_map_fac
    finiteSelectiveTwoToSupportInput finiteReindexAxisSwapHom

/-- The selected functor's identity law fires at the transported four-axis object. -/
theorem finiteSelectiveTwoReindex_map_id :
    (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput).map
        (𝟙 finiteReindexFourAxisTarget) =
      𝟙 finiteSelectiveTwoReindexedFourAxisObject :=
  selectedCoreFiberReindexFunctor_map_id
    finiteSelectiveTwoToSupportInput finiteReindexFourAxisTarget

/-- The selected functor's composition law fires twice on the axis swap. -/
theorem finiteSelectiveTwoReindex_map_comp :
    (selectedCoreFiberReindexFunctor finiteSelectiveTwoToSupportInput).map
        (finiteReindexAxisSwapHom ≫ finiteReindexAxisSwapHom) =
      finiteSelectiveTwoReindexedAxisSwap ≫
        finiteSelectiveTwoReindexedAxisSwap :=
  selectedCoreFiberReindexFunctor_map_comp
    finiteSelectiveTwoToSupportInput finiteReindexAxisSwapHom
      finiteReindexAxisSwapHom

/-! ## A sensitivity control where the generated lift is invertible -/

/-- The finite support endpoint's generated identity arrow. -/
def finiteReindexSupportIdentityInput : RealizableHom FiniteModel.carrier :=
  realizableHomOf (idPresentation finitePortfolioSupportInstance)

/-- Its semantic bottom arrow is the categorical identity. -/
theorem finiteReindexSupportIdentityInput_hom :
    finiteReindexSupportIdentityInput.semantic.hom =
      𝟙 finitePortfolioSupportInstance.toSemantic :=
  toSemanticCart_idPresentation_hom finitePortfolioSupportInstance

/-- The same four-axis package over the identity input's target. -/
noncomputable def finiteReindexIdentityFourAxisTarget :
    CoreFiber finiteReindexSupportIdentityInput.semantic.target :=
  ⟨finiteReindexFourAxisCore, by rfl⟩

/-- The same axis swap at the identity input's target fiber. -/
noncomputable def finiteReindexIdentityAxisSwapHom :
    finiteReindexIdentityFourAxisTarget ⟶
      finiteReindexIdentityFourAxisTarget := by
  refine ⟨finiteReindexAxisSwapTotal, ?_⟩
  change (packageProjection FiniteModel.carrier).IsHomLift
    ((packageProjection FiniteModel.carrier).map finiteReindexAxisSwapTotal)
    finiteReindexAxisSwapTotal
  infer_instance

/-- The identity-input target swap remains nonidentity. -/
theorem finiteReindexIdentityAxisSwapHom_ne_id :
    finiteReindexIdentityAxisSwapHom ≠ 𝟙 finiteReindexIdentityFourAxisTarget := by
  intro equality
  have haxis := congrArg
    (fun hom : finiteReindexIdentityFourAxisTarget ⟶
        finiteReindexIdentityFourAxisTarget =>
      hom.1.upper.axisMap finiteReindexAxisZero) equality
  have hswap : finiteReindexAxisOne = finiteReindexAxisZero := by
    change finiteReindexAxisSwapTotal.upper.axisMap finiteReindexAxisZero =
      (PackageTotalHom.id finiteReindexFourAxisCore).upper.axisMap
        finiteReindexAxisZero at haxis
    simpa only [finiteReindexAxisSwapHom_axis_zero] using haxis
  exact finiteReindexAxisZero_ne_one hswap.symm

/--
The selected reindexing map is genuinely sensitive to its actual target map:
over an identity base, the generated cartesian lift is an isomorphism and hence
cancels in the defining factor graph.
-/
theorem finiteReindexIdentityAxisSwap_map_ne_id :
    (selectedCoreFiberReindexFunctor finiteReindexSupportIdentityInput).map
        finiteReindexIdentityAxisSwapHom ≠
      𝟙 ((selectedCoreFiberReindexFunctor finiteReindexSupportIdentityInput).obj
        finiteReindexIdentityFourAxisTarget) := by
  intro hmap
  let lift := selectedCoreFiberCartesianLift finiteReindexSupportIdentityInput
    finiteReindexIdentityFourAxisTarget
  letI := lift.isStronglyCartesian
  letI : IsIso finiteReindexSupportIdentityInput.semantic.hom :=
    finiteReindexSupportIdentityInput_hom.symm ▸
      CategoryTheory.IsIso.id finitePortfolioSupportInstance.toSemantic
  letI : IsIso lift.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (packageProjection FiniteModel.carrier)
      finiteReindexSupportIdentityInput.semantic.hom lift.hom
  have hfac := selectedCoreFiberReindexFunctor_map_fac
    finiteReindexSupportIdentityInput finiteReindexIdentityAxisSwapHom
  rw [hmap] at hfac
  apply finiteReindexIdentityAxisSwapHom_ne_id
  apply CategoryTheory.Functor.Fiber.hom_ext
  rw [← cancel_epi lift.hom]
  simpa using hfac.symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
