import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedReflectedUniversalProperty
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelRealizationULiftWitnesses
import ResearchLean.AG.DoctrineFiberProduct.FiniteModelStrongLiftIsoTransport

/-!
# Realization-compatible finite-model strong-lift reflection

This module completes a realized finite-model prefix by an authored tail to the
selected finite core package.  A supplied strong-cartesian lift on the genuine
rebased realization is pulled to the direct semantic lift, composed with the
canonical high completion tail, reflected by the generated Cycle 26 universal
property, and finally cancelled against the canonical low completion tail.

The resulting prefix lift is produced for every realized input and completion
tail.  Endpoint packages, semantic isomorphisms, factors, factorization laws,
and strong-cartesian certificates are generated internally.

This is a normalized generated-endpoint checkpoint, not the fixed-ledger
`FiniteModelLift`: the Cycle 26 reflector deliberately retains the canonical
generated low domain and hom and compares against the generated high lift; both
anchors ultimately come from `strongCartesianLiftOfTarget`.  The supplied lift
is materially used in the comparison, factor graphs, and returned certificate,
but the construction does not cover an arbitrary
`CartesianLiftNonexistence.targetPackage`.  In particular this module does not
package its data theorem as a no-lift result.  The selected global-left branch
already proves the source counterexample type empty, so such a conditional
wrapper would not be nonvacuous evidence for the fixed ledger item.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-- Executable equality for the fixed low finite carrier; never a caller premise. -/
local instance finiteModelLiftSourceAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom :=
  finiteModelRealizationULiftAtomDecidableEq

/-! ## Canonical low and high completion data -/

/-- Complete a realized finite-model prefix by a tail to the selected core point. -/
noncomputable def finiteModelCompletedGeneratedInput
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    FiniteGeneratedLiftInput where
  source := input.semantic.source
  hom := input.semantic.hom ≫ tail

/-- The completed generated input records the literal prefix-tail composite. -/
@[simp]
theorem finiteModelCompletedGeneratedInput_hom
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    (finiteModelCompletedGeneratedInput input tail).hom =
      input.semantic.hom ≫ tail :=
  rfl

/-- The inverse-reindexed low package at the endpoint of the realized prefix. -/
noncomputable def finiteModelCompletedLowTarget
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    CoreFiber input.semantic.target :=
  ⟨inverseCorePackage FiniteModel.corePackage tail,
    inverseCorePackage_point FiniteModel.corePackage tail⟩

/-- The direct-high inverse-reindexed package at the lifted prefix endpoint. -/
noncomputable def finiteModelCompletedDirectHighTarget
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    CoreFiber (finiteModelLiftSemanticInput.{u} input.semantic).target :=
  ⟨inverseCorePackage finiteModelLiftCorePackage.{u}
      (finiteModelLiftExtInstHom.{u} tail),
    inverseCorePackage_point finiteModelLiftCorePackage.{u}
      (finiteModelLiftExtInstHom.{u} tail)⟩

/-- The high prefix target transported to the genuine rebased realization endpoint. -/
noncomputable def finiteModelCompletedRebasedHighTarget
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    CoreFiber (finiteModelLiftRealizableHom.{u} input).semantic.target :=
  (finiteModelLiftRealizableHomSemanticIso.{u} input).transportTarget
    (finiteModelCompletedDirectHighTarget.{u} input tail)

/-- Semantic input of the low completion tail. -/
noncomputable def finiteModelCompletedLowTailInput
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    CartSemanticInput FiniteModel.carrier where
  source := input.semantic.target
  target := packagePoint FiniteModel.corePackage
  hom := tail

/-- Canonical inverse-package hom for the low completion tail. -/
noncomputable def finiteModelCompletedLowTailHom
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    (finiteModelCompletedLowTarget input tail).1 ⟶
      FiniteModel.corePackage :=
  inverseCorePackageHom FiniteModel.corePackage tail

/-- The canonical low tail as a strong-cartesian lift, generated without a prefix lift. -/
noncomputable def finiteModelCompletedLowTailLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    StrongCartesianLift
      (finiteModelCompletedLowTailInput input tail)
      (finiteModelCompletedGeneratedInput input tail).lowTarget where
  domain := (finiteModelCompletedLowTarget input tail).1
  hom := finiteModelCompletedLowTailHom input tail
  isStronglyCartesian := by
    simpa [finiteModelCompletedLowTailInput,
      finiteModelCompletedLowTailHom] using
        inverseCorePackageHom_isStronglyCartesian
          FiniteModel.corePackage tail

/-- Semantic input of the directly lifted high completion tail. -/
noncomputable def finiteModelCompletedHighTailInput
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    CartSemanticInput finiteModelLiftCarrier.{u} where
  source := (finiteModelLiftSemanticInput.{u} input.semantic).target
  target := packagePoint finiteModelLiftCorePackage.{u}
  hom := finiteModelLiftExtInstHom.{u} tail

/-- Canonical inverse-package hom for the directly lifted high completion tail. -/
noncomputable def finiteModelCompletedHighTailHom
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    (finiteModelCompletedDirectHighTarget.{u} input tail).1 ⟶
      finiteModelLiftCorePackage.{u} :=
  inverseCorePackageHom finiteModelLiftCorePackage.{u}
    (finiteModelLiftExtInstHom.{u} tail)

/-- The canonical directly lifted high completion tail. -/
noncomputable def finiteModelCompletedHighTailLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage) :
    StrongCartesianLift
      (finiteModelCompletedHighTailInput.{u} input tail)
      (finiteModelCompletedGeneratedInput input tail).highTarget where
  domain := (finiteModelCompletedDirectHighTarget.{u} input tail).1
  hom := finiteModelCompletedHighTailHom.{u} input tail
  isStronglyCartesian := by
    simpa [finiteModelCompletedHighTailInput,
      finiteModelCompletedHighTailHom] using
        inverseCorePackageHom_isStronglyCartesian
          finiteModelLiftCorePackage.{u}
          (finiteModelLiftExtInstHom.{u} tail)

/-! ## Pulled and completed high lift -/

/-- Pull the supplied rebased high prefix lift to the direct semantic lift. -/
noncomputable def finiteModelCompletedPulledHighPrefixLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    StrongCartesianLift
      (finiteModelLiftSemanticInput.{u} input.semantic)
      (finiteModelCompletedDirectHighTarget.{u} input tail) :=
  (finiteModelLiftRealizableHomSemanticIso.{u} input).pullStrongCartesianLift
    (finiteModelCompletedDirectHighTarget.{u} input tail) lift

/-- The public high transport triangle retains the supplied high hom as its middle leg. -/
theorem finiteModelCompletedHighTransport_triangle
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    (coreFiberLiftIsoOfIso
        (finiteModelLiftRealizableHomSemanticIso.{u} input).sourceIso.symm
        lift.domainObject).hom ≫
          (finiteModelCompletedPulledHighPrefixLift.{u}
            input tail lift).hom ≫
        (coreFiberLiftIsoOfIso
          (finiteModelLiftRealizableHomSemanticIso.{u} input).targetIso
          (finiteModelCompletedDirectHighTarget.{u} input tail)).hom =
      lift.hom := by
  exact
    (finiteModelLiftRealizableHomSemanticIso.{u} input).pullStrongCartesianLift_conjugation_triangle
      (finiteModelCompletedDirectHighTarget.{u} input tail) lift

/-- Compose the pulled high prefix lift with the generated high completion tail. -/
noncomputable def finiteModelCompletedHighLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    StrongCartesianLift
      (finiteModelCompletedGeneratedInput input tail).highInput
      (finiteModelCompletedGeneratedInput input tail).highTarget where
  domain :=
    (finiteModelCompletedPulledHighPrefixLift.{u} input tail lift).domain
  hom :=
    (finiteModelCompletedPulledHighPrefixLift.{u} input tail lift).hom ≫
      finiteModelCompletedHighTailHom.{u} input tail
  isStronglyCartesian := by
    letI :=
      (finiteModelCompletedPulledHighPrefixLift.{u}
        input tail lift).isStronglyCartesian
    letI highTailStrong :
        (packageProjection finiteModelLiftCarrier.{u}).IsStronglyCartesian
          (finiteModelCompletedHighTailInput.{u} input tail).hom
          (finiteModelCompletedHighTailHom.{u} input tail) := by
      simpa [finiteModelCompletedHighTailInput] using
        (finiteModelCompletedHighTailLift.{u}
          input tail).isStronglyCartesian
    simpa [finiteModelCompletedGeneratedInput,
      finiteModelCompletedHighTailInput,
      finiteModelLiftSemanticInput,
      finiteModelLiftExtInstHom_comp] using
        CategoryTheory.Functor.IsStronglyCartesian.comp
          (packageProjection finiteModelLiftCarrier.{u})
          (f := (finiteModelLiftSemanticInput.{u} input.semantic).hom)
          (g := (finiteModelCompletedHighTailInput.{u} input tail).hom)
          (φ := (finiteModelCompletedPulledHighPrefixLift.{u}
            input tail lift).hom)
          (ψ := finiteModelCompletedHighTailHom.{u} input tail)

/-! ## Reflection and structural cancellation of the low completion tail -/

/-- Reflect the actual completed high lift by the Cycle 26 universal property. -/
noncomputable def finiteModelReflectedCompletedLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    StrongCartesianLift
      (finiteModelCompletedGeneratedInput input tail).lowInput
      (finiteModelCompletedGeneratedInput input tail).lowTarget :=
  reflectNormalizedStrongCartesianLift.{u}
    (finiteModelCompletedGeneratedInput input tail)
    (finiteModelCompletedHighLift.{u} input tail lift)

/-- The reflected completed lift exposes the entire generated Cycle 26 component graph. -/
theorem finiteModelReflectedCompletedLift_components
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    ReflectedGeneratedComponentGraph.{u}
      (finiteModelCompletedGeneratedInput input tail)
      (finiteModelCompletedHighLift.{u} input tail lift)
      (finiteModelReflectedCompletedLift.{u} input tail lift).hom := by
  simpa [finiteModelReflectedCompletedLift] using
    reflectNormalizedHighHom_components.{u}
      (finiteModelCompletedGeneratedInput input tail)
      (finiteModelCompletedHighLift.{u} input tail lift)

/-- Factor the reflected full lift through the canonical low completion tail. -/
noncomputable def finiteModelCompletedLowFactor
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    (finiteModelReflectedCompletedLift.{u} input tail lift).domain ⟶
      (finiteModelCompletedLowTarget input tail).1 := by
  letI lowTailStrong :
      (packageProjection FiniteModel.carrier).IsStronglyCartesian
        tail (finiteModelCompletedLowTailHom input tail) := by
    simpa [finiteModelCompletedLowTailInput] using
      (finiteModelCompletedLowTailLift input tail).isStronglyCartesian
  letI :=
    (finiteModelReflectedCompletedLift.{u}
      input tail lift).isStronglyCartesian
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (p := packageProjection FiniteModel.carrier)
    tail (finiteModelCompletedLowTailHom input tail)
    (g := input.semantic.hom)
    (f' := (finiteModelCompletedGeneratedInput input tail).lowInput.hom)
    rfl (finiteModelReflectedCompletedLift.{u} input tail lift).hom

/-- The generated low factor lies over the original realized prefix. -/
theorem finiteModelCompletedLowFactor_isHomLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    (packageProjection FiniteModel.carrier).IsHomLift
      input.semantic.hom
      (finiteModelCompletedLowFactor.{u} input tail lift) := by
  letI lowTailStrong :
      (packageProjection FiniteModel.carrier).IsStronglyCartesian
        tail (finiteModelCompletedLowTailHom input tail) := by
    simpa [finiteModelCompletedLowTailInput] using
      (finiteModelCompletedLowTailLift input tail).isStronglyCartesian
  letI :=
    (finiteModelReflectedCompletedLift.{u}
      input tail lift).isStronglyCartesian
  unfold finiteModelCompletedLowFactor
  infer_instance

/-- The generated low factor followed by the low tail is the reflected full lift. -/
theorem finiteModelCompletedLowFactor_triangle
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    finiteModelCompletedLowFactor.{u} input tail lift ≫
        finiteModelCompletedLowTailHom input tail =
      (finiteModelReflectedCompletedLift.{u} input tail lift).hom := by
  letI lowTailStrong :
      (packageProjection FiniteModel.carrier).IsStronglyCartesian
        tail (finiteModelCompletedLowTailHom input tail) := by
    simpa [finiteModelCompletedLowTailInput] using
      (finiteModelCompletedLowTailLift input tail).isStronglyCartesian
  letI :=
    (finiteModelReflectedCompletedLift.{u}
      input tail lift).isStronglyCartesian
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (p := packageProjection FiniteModel.carrier)
    tail (finiteModelCompletedLowTailHom input tail)
    (g := input.semantic.hom)
    (f' := (finiteModelCompletedGeneratedInput input tail).lowInput.hom)
    rfl (finiteModelReflectedCompletedLift.{u} input tail lift).hom

/--
Reflect a supplied rebased high lift and cancel the completion tail, producing
a strong-cartesian lift of the original realized prefix.
-/
noncomputable def finiteModelReflectCompletedStrongCartesianLift
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    StrongCartesianLift input.semantic
      (finiteModelCompletedLowTarget input tail) where
  domain := (finiteModelReflectedCompletedLift.{u} input tail lift).domain
  hom := finiteModelCompletedLowFactor.{u} input tail lift
  isStronglyCartesian := by
    letI tailStrong :
        (packageProjection FiniteModel.carrier).IsStronglyCartesian
          tail (finiteModelCompletedLowTailHom input tail) := by
      simpa [finiteModelCompletedLowTailInput] using
        (finiteModelCompletedLowTailLift input tail).isStronglyCartesian
    letI factorLift : (packageProjection FiniteModel.carrier).IsHomLift
        input.semantic.hom
        (finiteModelCompletedLowFactor.{u} input tail lift) :=
      finiteModelCompletedLowFactor_isHomLift.{u} input tail lift
    letI reflectedStrong :=
      (finiteModelReflectedCompletedLift.{u}
        input tail lift).isStronglyCartesian
    letI compositeStrong :
        (packageProjection FiniteModel.carrier).IsStronglyCartesian
          (input.semantic.hom ≫ tail)
          (finiteModelCompletedLowFactor.{u} input tail lift ≫
            finiteModelCompletedLowTailHom input tail) := by
      rw [finiteModelCompletedLowFactor_triangle]
      simpa [finiteModelCompletedGeneratedInput] using reflectedStrong
    exact CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := packageProjection FiniteModel.carrier)
      (f := input.semantic.hom) (g := tail)
      (φ := finiteModelCompletedLowFactor.{u} input tail lift)
      (ψ := finiteModelCompletedLowTailHom input tail)

/-- The producer's hom is exactly the low-tail universal-property factor. -/
@[simp]
theorem finiteModelReflectCompletedStrongCartesianLift_hom
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    (finiteModelReflectCompletedStrongCartesianLift.{u}
      input tail lift).hom =
        finiteModelCompletedLowFactor.{u} input tail lift :=
  rfl

/-- The returned prefix lift followed by the canonical tail is the reflected full lift. -/
theorem finiteModelReflectCompletedStrongCartesianLift_triangle
    (input : RealizableHom FiniteModel.carrier)
    (tail : input.semantic.target ⟶ packagePoint FiniteModel.corePackage)
    (lift : StrongCartesianLift
      (finiteModelLiftRealizableHom.{u} input).semantic
      (finiteModelCompletedRebasedHighTarget.{u} input tail)) :
    (finiteModelReflectCompletedStrongCartesianLift.{u}
        input tail lift).hom ≫
        finiteModelCompletedLowTailHom input tail =
      (finiteModelReflectedCompletedLift.{u} input tail lift).hom :=
  finiteModelCompletedLowFactor_triangle.{u} input tail lift

/-! ## Concrete nonvacuity firing -/

/-- An actual rebased high lift at the selected noninvertible realized prefix. -/
noncomputable def finiteSelectiveTwoCompletedRebasedHighLift :
    StrongCartesianLift
      (finiteModelLiftRealizableHom.{u}
        finiteSelectiveTwoToSupportInput).semantic
      (finiteModelCompletedRebasedHighTarget.{u}
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom) :=
  strongCartesianLiftOfTarget _ _

/-- The generic producer fires on the selected noninvertible realized prefix. -/
noncomputable def finiteSelectiveTwoFiniteModelStrongLift :
    StrongCartesianLift finiteSelectiveTwoToSupportInput.semantic
      (finiteModelCompletedLowTarget
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom) :=
  finiteModelReflectCompletedStrongCartesianLift.{u}
    finiteSelectiveTwoToSupportInput
    finitePortfolioSupportToCoreHom
    finiteSelectiveTwoCompletedRebasedHighLift.{u}

/-- The concrete firing retains the generated high transport triangle. -/
theorem finiteSelectiveTwoFiniteModelHighTransport_triangle :
    (coreFiberLiftIsoOfIso
        (finiteModelLiftRealizableHomSemanticIso.{u}
          finiteSelectiveTwoToSupportInput).sourceIso.symm
        finiteSelectiveTwoCompletedRebasedHighLift.{u}.domainObject).hom ≫
          (finiteModelCompletedPulledHighPrefixLift.{u}
            finiteSelectiveTwoToSupportInput
            finitePortfolioSupportToCoreHom
            finiteSelectiveTwoCompletedRebasedHighLift.{u}).hom ≫
        (coreFiberLiftIsoOfIso
          (finiteModelLiftRealizableHomSemanticIso.{u}
            finiteSelectiveTwoToSupportInput).targetIso
          (finiteModelCompletedDirectHighTarget.{u}
            finiteSelectiveTwoToSupportInput
            finitePortfolioSupportToCoreHom)).hom =
      finiteSelectiveTwoCompletedRebasedHighLift.{u}.hom :=
  finiteModelCompletedHighTransport_triangle.{u}
    finiteSelectiveTwoToSupportInput
    finitePortfolioSupportToCoreHom
    finiteSelectiveTwoCompletedRebasedHighLift.{u}

/-- The concrete firing retains the complete reflected component graph. -/
theorem finiteSelectiveTwoFiniteModelReflected_components :
    ReflectedGeneratedComponentGraph.{u}
      (finiteModelCompletedGeneratedInput
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom)
      (finiteModelCompletedHighLift.{u}
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom
        finiteSelectiveTwoCompletedRebasedHighLift.{u})
      (finiteModelReflectedCompletedLift.{u}
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom
        finiteSelectiveTwoCompletedRebasedHighLift.{u}).hom :=
  finiteModelReflectedCompletedLift_components.{u}
    finiteSelectiveTwoToSupportInput
    finitePortfolioSupportToCoreHom
    finiteSelectiveTwoCompletedRebasedHighLift.{u}

/-- The concrete firing retains the low-tail cancellation triangle. -/
theorem finiteSelectiveTwoFiniteModelStrongLift_triangle :
    finiteSelectiveTwoFiniteModelStrongLift.{u}.hom ≫
        finiteModelCompletedLowTailHom
          finiteSelectiveTwoToSupportInput
          finitePortfolioSupportToCoreHom =
      (finiteModelReflectedCompletedLift.{u}
        finiteSelectiveTwoToSupportInput
        finitePortfolioSupportToCoreHom
        finiteSelectiveTwoCompletedRebasedHighLift.{u}).hom :=
  finiteModelReflectCompletedStrongCartesianLift_triangle.{u}
    finiteSelectiveTwoToSupportInput
    finitePortfolioSupportToCoreHom
    finiteSelectiveTwoCompletedRebasedHighLift.{u}

/-- The same concrete firing path records noninvertibility before and after rebasing. -/
theorem finiteSelectiveTwoFiniteModelStrongLift_noninvertible :
    (¬ IsIso finiteSelectiveTwoToSupportInput.semantic.hom) ∧
      (¬ IsIso
        (finiteModelLiftRealizableHom.{u}
          finiteSelectiveTwoToSupportInput).semantic.hom) :=
  ⟨finiteSelectiveTwoToSupportInput_not_isIso,
    finiteSelectiveTwoToSupportLiftedInput_not_isIso.{u}⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
