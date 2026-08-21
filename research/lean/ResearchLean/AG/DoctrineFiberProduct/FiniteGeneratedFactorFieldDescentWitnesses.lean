import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescent

/-!
# Concrete finite witnesses for generated-factor field descent

This module specializes the computational field-descent API to the existing
two-source firing chain.  The semantic input, supplied high lift, source
package, and prefix arrow are all generated from
`finiteSelectiveTwoGeneratedChain`.

The public surface first names the generated fixture input, supplied lift,
package, prefix, and actual normalized high factor.  It then records the fields
read from that factor: its reflected base, upper Atom graph, core-object
configuration, and concrete configuration map.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Internally generated firing data -/

/-- The tail input of the concrete noninvertible two-source chain. -/
def finiteSelectiveTwoFieldDescentInput : FiniteGeneratedLiftInput :=
  finiteSelectiveTwoGeneratedChain.tailGeneratedInput

/-- The theorem-generated high lift used as the concrete supplied lift. -/
noncomputable def finiteSelectiveTwoFieldDescentLift :
    StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u}
        finiteSelectiveTwoFieldDescentInput)
      (FiniteGeneratedLiftInput.highTarget.{u}
        finiteSelectiveTwoFieldDescentInput) :=
  FiniteGeneratedLiftInput.highGeneratedLift.{u}
    finiteSelectiveTwoFieldDescentInput

/-- The inverse-generated package of the concrete direct composite. -/
noncomputable def finiteSelectiveTwoFieldDescentPackage :
    AATCorePackage FiniteModel.carrier :=
  inverseCorePackage FiniteModel.corePackage
    (finiteSelectiveTwoGeneratedChain.first ≫
      finiteSelectiveTwoGeneratedChain.second)

/-- The concrete prefix arrow from the direct-composite package point to the tail source. -/
def finiteSelectiveTwoFieldDescentBase :
    packagePoint finiteSelectiveTwoFieldDescentPackage ⟶
      finiteSelectiveTwoFieldDescentInput.source :=
  finiteSelectiveTwoGeneratedChain.first

/-- The actual normalized high factor formed from the internally generated firing data. -/
noncomputable def finiteSelectiveTwoActualNormalizedHighFactor :=
    finiteGeneratedNormalizedHighFactor.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase

/-! ## Reflected base and noninvertibility -/

/-- The base reflected directly from the concrete actual normalized high factor. -/
noncomputable def finiteSelectiveTwoActualReflectedBase :
    packagePoint finiteSelectiveTwoFieldDescentPackage ⟶
      finiteSelectiveTwoFieldDescentInput.source :=
    finiteGeneratedReflectedBase.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase

/-- The actual reflected base is exactly the concrete chain's first arrow. -/
theorem finiteSelectiveTwoActualReflectedBase_eq_first :
    finiteSelectiveTwoActualReflectedBase.{u} =
      finiteSelectiveTwoGeneratedChain.first := by
  simpa [finiteSelectiveTwoActualReflectedBase,
    finiteSelectiveTwoFieldDescentBase] using
      (finiteGeneratedReflectedBase_eq.{u}
        finiteSelectiveTwoFieldDescentInput
        finiteSelectiveTwoFieldDescentLift.{u}
        finiteSelectiveTwoFieldDescentBase)

/-- The actual reflected base remains genuinely noninvertible. -/
theorem finiteSelectiveTwoActualReflectedBase_not_isIso :
    ¬ IsIso finiteSelectiveTwoActualReflectedBase.{u} := by
  rw [finiteSelectiveTwoActualReflectedBase_eq_first.{u}]
  exact finiteSelectiveTwoGeneratedChain_first_not_isIso

/-- Lifting the actual reflected base recovers the base of the actual high factor. -/
theorem finiteSelectiveTwoActualReflectedBase_high_graph :
    finiteModelLiftExtInstHom.{u} finiteSelectiveTwoActualReflectedBase.{u} =
      finiteSelectiveTwoActualNormalizedHighFactor.{u}.base := by
  simpa [finiteSelectiveTwoActualReflectedBase,
    finiteSelectiveTwoActualNormalizedHighFactor] using
      (finiteGeneratedReflectedBase_high_graph.{u}
        finiteSelectiveTwoFieldDescentInput
        finiteSelectiveTwoFieldDescentLift.{u}
        finiteSelectiveTwoFieldDescentBase)

/-- The actual high factor base is the canonical lift of the concrete first arrow. -/
theorem finiteSelectiveTwoActualHighFactor_base_graph :
    finiteSelectiveTwoActualNormalizedHighFactor.{u}.base =
      finiteModelLiftExtInstHom.{u}
        finiteSelectiveTwoGeneratedChain.first := by
  exact finiteGeneratedNormalizedHighFactor_base_graph.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase

/-! ## Reflected upper Atom field -/

/-- The upper Atom equivalence reflected from the concrete actual high factor. -/
noncomputable def finiteSelectiveTwoActualReflectedUpperAtomEquiv :
    FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom :=
    finiteGeneratedReflectedUpperAtomEquiv.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase

/-- The reflected actual upper Atom map is the concrete first-arrow Atom map. -/
theorem finiteSelectiveTwoActualReflectedUpperAtomEquiv_eq_first :
    finiteSelectiveTwoActualReflectedUpperAtomEquiv.{u} =
      finiteSelectiveTwoGeneratedChain.first.doctrineHom.atomEquiv := by
  simpa [finiteSelectiveTwoActualReflectedUpperAtomEquiv,
    finiteSelectiveTwoFieldDescentBase] using
      (finiteGeneratedReflectedUpperAtomEquiv_eq.{u}
        finiteSelectiveTwoFieldDescentInput
        finiteSelectiveTwoFieldDescentLift.{u}
        finiteSelectiveTwoFieldDescentBase)

/-- The concrete actual high upper Atom map is the lifted first-arrow Atom map. -/
theorem finiteSelectiveTwoActualHighFactor_upper_atom_graph
    (atom : FiniteModel.carrier.Atom) :
    finiteSelectiveTwoActualNormalizedHighFactor.{u}.upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (finiteSelectiveTwoGeneratedChain.first.doctrineHom.atomEquiv atom) := by
  calc
    _ = finiteModelLiftCarrierEquiv.{u}.atom
        (finiteSelectiveTwoActualReflectedUpperAtomEquiv.{u} atom) :=
      by
        simpa [finiteSelectiveTwoActualNormalizedHighFactor,
          finiteSelectiveTwoActualReflectedUpperAtomEquiv] using
            (finiteGeneratedReflectedUpperAtomEquiv_high_graph.{u}
              finiteSelectiveTwoFieldDescentInput
              finiteSelectiveTwoFieldDescentLift.{u}
              finiteSelectiveTwoFieldDescentBase atom).symm
    _ = _ := by
      rw [finiteSelectiveTwoActualReflectedUpperAtomEquiv_eq_first.{u}]

/-! ## Concrete object configuration and configuration map -/

/-- The configuration reflected from the actual high image of the finite core object. -/
noncomputable def finiteSelectiveTwoReflectedCoreObjectConfiguration :
    AtomConfiguration FiniteModel.carrier :=
    finiteGeneratedReflectedObjectConfiguration.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase
    FiniteModel.corePackage.object

/-- The reflected core-object configuration lifts back to the actual high object image. -/
theorem finiteSelectiveTwoReflectedCoreObjectConfiguration_high_graph :
    finiteModelLiftAtomConfiguration.{u}
        finiteSelectiveTwoReflectedCoreObjectConfiguration.{u} =
      (finiteSelectiveTwoActualNormalizedHighFactor.{u}.upper.objectMap
        (finiteModelLiftArchitectureObject.{u}
          FiniteModel.corePackage.object)).configuration := by
  simpa [finiteSelectiveTwoReflectedCoreObjectConfiguration,
    finiteSelectiveTwoActualNormalizedHighFactor] using
      (finiteGeneratedReflectedObjectConfiguration_high_graph.{u}
        finiteSelectiveTwoFieldDescentInput
        finiteSelectiveTwoFieldDescentLift.{u}
        finiteSelectiveTwoFieldDescentBase
        FiniteModel.corePackage.object)

/-- The configuration map reflected from the actual high image of the finite core object. -/
noncomputable def finiteSelectiveTwoReflectedCoreObjectConfigurationMap :
    ConfigurationHom FiniteModel.corePackage.object.configuration
      finiteSelectiveTwoReflectedCoreObjectConfiguration.{u} :=
    finiteGeneratedReflectedConfigurationMap.{u}
    finiteSelectiveTwoFieldDescentInput
    finiteSelectiveTwoFieldDescentLift.{u}
    finiteSelectiveTwoFieldDescentBase
    FiniteModel.corePackage.object

/-- The reflected concrete configuration map has the first arrow's Atom graph. -/
theorem finiteSelectiveTwoReflectedCoreObjectConfigurationMap_atom_graph
    (atom : FiniteModel.carrier.Atom) :
    finiteSelectiveTwoReflectedCoreObjectConfigurationMap.{u}.atomMap atom =
      finiteSelectiveTwoGeneratedChain.first.doctrineHom.atomEquiv atom := by
  simpa [finiteSelectiveTwoReflectedCoreObjectConfigurationMap,
    finiteSelectiveTwoFieldDescentBase] using
      (finiteGeneratedReflectedConfigurationMap_atom_eq.{u}
        finiteSelectiveTwoFieldDescentInput
        finiteSelectiveTwoFieldDescentLift.{u}
        finiteSelectiveTwoFieldDescentBase
        FiniteModel.corePackage.object atom)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
