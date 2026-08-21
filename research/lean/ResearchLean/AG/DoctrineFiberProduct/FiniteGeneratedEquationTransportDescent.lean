import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationRoleDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedObservableNaturalityDescent
import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedEquationGeneratorDescent

/-!
# Complete generated equation-system transport descent

This module assembles the complete low equation-system exact transport reflected
from an actual normalized high factor.  Its context, equation-index, observable,
role, naturality, violation-coordinate, and residual fields are the internally
generated results of the preceding descent modules.  No law, transport,
comparison, or certificate is accepted from the caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/--
The exact low equation-system transport type generated from an ambient prefix
and an actual high strong-cartesian lift.
-/
abbrev FiniteGeneratedReflectedEquationSystemExactTransportOutput
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :=
  EquationSystemExactTransport
    (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem
    input.lowGeneratedLift.domain.algebra.equationSystem
    (finiteGeneratedReflectedUpperAtomEquiv input lift base)
    (finiteGeneratedReflectedArchitectureObject input lift base)

/--
Assemble the seven exact equation-transport fields reflected from the actual
normalized high factor.
-/
noncomputable def finiteGeneratedReflectedEquationSystemExactTransport
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteGeneratedReflectedEquationSystemExactTransportOutput input lift base where
  contextEquivalence :=
    finiteGeneratedReflectedContextEquivalence input lift base
  equationEquiv :=
    finiteGeneratedReflectedEquationIndexEquiv input lift base
  role_eq :=
    finiteGeneratedReflectedEquationRole_eq input lift base
  observableEquiv :=
    finiteGeneratedReflectedEquationObservableEquiv input lift base
  observable_naturality :=
    finiteGeneratedReflectedEquationObservableEquiv_naturality input lift base
  violationCoordinate_eq :=
    finiteGeneratedReflectedViolationCoordinate_eq input lift base
  equationResidual_eq :=
    finiteGeneratedReflectedEquationResidual_eq input lift base

/-! ## Public component and law graphs -/

/-- The assembled context equivalence is the Cycle 20 reflected equivalence. -/
@[simp]
theorem finiteGeneratedReflectedEquationSystemExactTransport_contextEquivalence
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).contextEquivalence =
      finiteGeneratedReflectedContextEquivalence input lift base :=
  rfl

/-- The assembled equation-index equivalence is the reflected actual equivalence. -/
@[simp]
theorem finiteGeneratedReflectedEquationSystemExactTransport_equationEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).equationEquiv =
      finiteGeneratedReflectedEquationIndexEquiv input lift base :=
  rfl

/-- Every assembled observable component is the reflected actual ring equivalence. -/
@[simp]
theorem finiteGeneratedReflectedEquationSystemExactTransport_observableEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).observableEquiv W =
      finiteGeneratedReflectedEquationObservableEquiv input lift base W :=
  rfl

/-- The assembled transport preserves the role of every generated equation index. -/
theorem finiteGeneratedReflectedEquationSystemExactTransport_role_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index) :
    input.lowGeneratedLift.domain.algebra.equationSystem.role
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).equationMap
          index) =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.role
        index :=
  (finiteGeneratedReflectedEquationSystemExactTransport input lift base).role_eq index

/-- The assembled observable equivalences commute with every reflected restriction map. -/
theorem finiteGeneratedReflectedEquationSystemExactTransport_observable_naturality
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    {W V : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder)}
    (map : W ⟶ V)
    (value : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Observable V) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).observableEquiv W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.restrict
          map value) =
      input.lowGeneratedLift.domain.algebra.equationSystem.restrict
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).contextForward_map
          map)
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).observableEquiv V
          value) :=
  (finiteGeneratedReflectedEquationSystemExactTransport input lift base).observable_naturality
    map value

/-- The assembled transport preserves every generated violation coordinate. -/
theorem finiteGeneratedReflectedEquationSystemExactTransport_violationCoordinate_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).observableEquiv W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
          W index atom) =
      input.lowGeneratedLift.domain.algebra.equationSystem.violationCoordinate
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).contextForward W)
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).equationMap index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) :=
  (finiteGeneratedReflectedEquationSystemExactTransport input lift base).violationCoordinate_eq
    W index atom

/-- The assembled transport preserves every residual of every low architecture object. -/
theorem finiteGeneratedReflectedEquationSystemExactTransport_equationResidual_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (W : Site.ContextCategoryObject
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.contextPreorder))
    (object : ArchitectureObject FiniteModel.carrier)
    (index : (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    (finiteGeneratedReflectedEquationSystemExactTransport input lift base).observableEquiv W
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.algebra.equationSystem.equationResidual
          W object index atom) =
      input.lowGeneratedLift.domain.algebra.equationSystem.equationResidual
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).contextForward W)
        (finiteGeneratedReflectedArchitectureObject input lift base object)
        ((finiteGeneratedReflectedEquationSystemExactTransport input lift base).equationMap index)
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) :=
  (finiteGeneratedReflectedEquationSystemExactTransport input lift base).equationResidual_eq
    W object index atom

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
