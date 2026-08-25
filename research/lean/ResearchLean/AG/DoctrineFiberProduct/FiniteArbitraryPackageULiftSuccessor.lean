import ResearchLean.AG.DoctrineFiberProduct.FiniteArbitraryPackageULiftZero

/-!
# Successor-universe arbitrary package rebase

The tagged context equivalence supplies a symbolic `.{u + 1}` successor-form
endpoint schema.  This module transports arbitrary architectural equations,
finite detector syntax, and the complete core package through that equivalence.
It accepts the source package and derives target soundness from source soundness;
no separately supplied target package or target soundness certificate is accepted.

The resulting `.{u + 1}` schema and the separate exact-zero construction do
not constitute one symbolic `.{u}` producer, because Lean universe parameters
cannot be split at term level.  That fixed-ledger producer remains open.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Successor-universe arbitrary equations -/

/-- Transport an arbitrary equation system through the tagged context equivalence. -/
noncomputable def finiteModelTaggedLiftEquationSystem
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (objectReading : ObjectReading FiniteModel.carrier)
    (equations : ArchitecturalEquationSystem preorder) :
    ArchitecturalEquationSystem
      (finiteModelLiftContextPreorderAt.{u} preorder) where
  Index := ULift.{u + 1} equations.Index
  role index := equations.role index.down
  Observable context := ULift.{u + 1} (equations.Observable
    ((finiteModelReflectedContextFunctor.{u} preorder).obj context))
  observableCommRing _ := inferInstance
  restrict := by
    intro source target morphism
    exact ULift.ringEquiv.symm.toRingHom.comp
      ((equations.restrict
        ((finiteModelReflectedContextFunctor.{u} preorder).map morphism)).comp
          ULift.ringEquiv.toRingHom)
  restrict_id := by
    intro context value
    rcases value with ⟨value⟩
    apply ULift.ext
    simpa using equations.restrict_id
      ((finiteModelReflectedContextFunctor.{u} preorder).obj context) value
  restrict_comp := by
    intro first second third f g value
    rcases value with ⟨value⟩
    apply ULift.ext
    simpa using equations.restrict_comp
      ((finiteModelReflectedContextFunctor.{u} preorder).map f)
      ((finiteModelReflectedContextFunctor.{u} preorder).map g) value
  violationCoordinate := fun context index atom => ULift.up
    (equations.violationCoordinate
      ((finiteModelReflectedContextFunctor.{u} preorder).obj context)
      index.down (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom))
  violationCoordinate_restrict := by
    intro source target morphism index atom
    apply ULift.ext
    simpa using equations.violationCoordinate_restrict
      ((finiteModelReflectedContextFunctor.{u} preorder).map morphism)
      index.down (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom)
  equationResidual := fun context object index atom => ULift.up
    (equations.equationResidual
      ((finiteModelReflectedContextFunctor.{u} preorder).obj context)
      (finiteModelNormalizeArchitectureObject.{u + 1} objectReading object)
      index.down (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom))
  equationResidual_restrict := by
    intro source target morphism object index atom
    apply ULift.ext
    simpa using equations.equationResidual_restrict
      ((finiteModelReflectedContextFunctor.{u} preorder).map morphism)
      (finiteModelNormalizeArchitectureObject.{u + 1} objectReading object)
      index.down (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom)

/-- The successor lift preserves arbitrary equation fulfillment exactly. -/
theorem finiteModelTaggedLiftEquationSystem_holds_iff
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (objectReading : ObjectReading FiniteModel.carrier)
    (equations : ArchitecturalEquationSystem preorder)
    (index : equations.Index)
    (object : ArchitectureObject finiteModelLiftCarrier.{u + 1}) :
    (finiteModelTaggedLiftEquationSystem objectReading equations).EquationHolds
        (ULift.up index) object ↔
      equations.EquationHolds index
        (finiteModelNormalizeArchitectureObject.{u + 1}
          objectReading object) := by
  constructor
  · intro hholds context atom
    have lifted := hholds
      ((finiteModelTaggedContextFunctor.{u} preorder).obj context)
      (finiteModelLiftCarrierEquiv.{u + 1}.atom atom)
    have down := congrArg ULift.down lifted
    change equations.equationResidual
        ((finiteModelReflectedContextFunctor.{u} preorder).obj
          ((finiteModelTaggedContextFunctor.{u} preorder).obj context))
        (finiteModelNormalizeArchitectureObject.{u + 1} objectReading object)
        index atom = 0 at down
    let unitMorphism :=
      (finiteModelTaggedContextEquivalence.{u} preorder).unitIso.hom.app context
    have restricted := congrArg (equations.restrict unitMorphism) down
    rw [map_zero] at restricted
    exact (equations.equationResidual_restrict unitMorphism
      (finiteModelNormalizeArchitectureObject.{u + 1} objectReading object)
      index atom).symm.trans restricted
  · intro hholds context atom
    apply ULift.ext
    exact hholds
      ((finiteModelReflectedContextFunctor.{u} preorder).obj context)
      (finiteModelLiftCarrierEquiv.{u + 1}.atom.symm atom)

/-! ## Successor-universe arbitrary detectors -/

/-- Query semantics agree with object-reading normalization. -/
@[simp]
theorem finiteModelReflectCircuitQuery_normalize_holds_iff
    (objectReading : ObjectReading FiniteModel.carrier)
    (query : CircuitQuery finiteModelLiftCarrier.{u + 1})
    (object : ArchitectureObject finiteModelLiftCarrier.{u + 1}) :
    query.Holds object ↔
      (finiteModelReflectCircuitQuery.{u + 1} query).Holds
        (finiteModelNormalizeArchitectureObject.{u + 1}
          objectReading object) := by
  cases query <;>
    simp [CircuitQuery.Holds, finiteModelReflectCircuitQuery,
      finiteModelNormalizeArchitectureObject,
      finiteModelReflectAtomConfiguration, finiteModelReflectAtomFamily,
      objectReading.configuration_eq]

/-- Signed finite data agree with object-reading normalization. -/
@[simp]
theorem finiteModelReflectFiniteCircuitDatum_normalize_matches_iff
    (objectReading : ObjectReading FiniteModel.carrier)
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{u + 1})
    (object : ArchitectureObject finiteModelLiftCarrier.{u + 1}) :
    datum.Matches object ↔
      (finiteModelReflectFiniteCircuitDatum.{u + 1} datum).Matches
        (finiteModelNormalizeArchitectureObject.{u + 1}
          objectReading object) := by
  constructor
  · intro hmatches query expected hmem
    have liftedMem :
        (finiteModelLiftCircuitQuery.{u + 1} query, expected) ∈
          (finiteModelLiftFiniteCircuitDatum.{u + 1}
            (finiteModelReflectFiniteCircuitDatum.{u + 1} datum)).queries :=
      List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩
    have liftedMem' :
        (finiteModelLiftCircuitQuery.{u + 1} query, expected) ∈ datum.queries := by
      simpa using liftedMem
    have hmapped := hmatches
      (finiteModelLiftCircuitQuery.{u + 1} query) expected liftedMem'
    simpa using ((finiteModelReflectCircuitQuery_normalize_holds_iff
      objectReading (finiteModelLiftCircuitQuery.{u + 1} query) object).symm.trans
        hmapped)
  · intro hmatches query expected hmem
    have hmapped := hmatches
      (finiteModelReflectCircuitQuery.{u + 1} query) expected
      (List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩)
    exact (finiteModelReflectCircuitQuery_normalize_holds_iff
      objectReading query object).trans hmapped

/-- Rebase every arbitrary detector program at a successor universe. -/
noncomputable def finiteModelTaggedLiftEquationCircuitReading
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    {equations : ArchitecturalEquationSystem preorder}
    (objectReading : ObjectReading FiniteModel.carrier)
    (circuits : EquationCircuitReading equations) :
    EquationCircuitReading
      (finiteModelTaggedLiftEquationSystem.{u} objectReading equations) where
  code index := finiteModelLiftCircuitDetectorCode.{u + 1}
    (circuits.code index.down)

/-- Sound arbitrary source detectors remain sound at every successor universe. -/
theorem finiteModelTaggedLiftEquationCircuitReading_sound
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    {equations : ArchitecturalEquationSystem preorder}
    (objectReading : ObjectReading FiniteModel.carrier)
    (circuits : EquationCircuitReading equations)
    (sound : circuits.Sound) :
    (finiteModelTaggedLiftEquationCircuitReading.{u}
      objectReading circuits).Sound := by
  intro index object datum hmatches haccepts
  rcases index with ⟨index⟩
  have reflectedMatches :=
    (finiteModelReflectFiniteCircuitDatum_normalize_matches_iff
      objectReading datum object).mp hmatches
  have reflectedAccepts :
      (circuits.code index).eval
          (finiteModelReflectFiniteCircuitDatum.{u + 1} datum) = true := by
    rw [← finiteModelLiftCircuitDetectorCode_eval_reflect.{u + 1}
      (circuits.code index) datum]
    exact haccepts
  exact (finiteModelTaggedLiftEquationSystem_holds_iff.{u}
    objectReading equations index object).mp.mt
      (sound index _ _ reflectedMatches reflectedAccepts)

/-- Rebase an arbitrary complete equation reading at a successor universe. -/
noncomputable def finiteModelTaggedLiftEquationReading
    {A : ArchitectureObject FiniteModel.carrier}
    (objectReading : ObjectReading FiniteModel.carrier)
    (reading : EquationReading A) :
    EquationReading (finiteModelLiftArchitectureObject.{u + 1} A) where
  contextPreorder := finiteModelLiftContextPreorderAt.{u} reading.contextPreorder
  equationSystem := finiteModelTaggedLiftEquationSystem.{u}
    objectReading reading.equationSystem
  circuits := finiteModelTaggedLiftEquationCircuitReading.{u}
    objectReading reading.circuits
  circuitSound := finiteModelTaggedLiftEquationCircuitReading_sound.{u}
    objectReading reading.circuits reading.circuitSound

/-! ## Successor-universe arbitrary core-package assembly -/

/-- Assemble every reading field of an arbitrary finite-carrier package. -/
noncomputable def finiteModelTaggedLiftCoreReading
    (package : AATCorePackage FiniteModel.carrier) :
    CoreReading finiteModelLiftCarrier.{u + 1} where
  doctrine := finiteModelLiftExtractionDoctrine.{u + 1} package.reading.doctrine
  source := ULift.up package.reading.source
  family_listFinite := by
    simpa using finiteModelLiftAtomFamily_listFinite.{u + 1}
      package.reading.family_listFinite
  composition := finiteModelLiftCompositionReading.{u + 1}
    package.reading.composition
  objectReading := finiteModelLiftObjectReading.{u + 1}
    package.reading.objectReading
  equationReading := finiteModelTaggedLiftEquationReading.{u}
    package.reading.objectReading package.reading.equationReading
  invariantReading := finiteModelLiftInvariantFamilyAt.{u + 1}
    package.reading.objectReading package.reading.invariantReading
  signatureReading := finiteModelLiftArchitectureSignatureAt.{u + 1}
    package.reading.objectReading package.reading.signatureReading
  operationReading := finiteModelLiftOperationReadingAt.{u + 1}
    package.reading.objectReading package.reading.operationReading

/-- Generate the arbitrary package at every successor universe endpoint. -/
noncomputable def finiteModelTaggedLiftCorePackage
    (package : AATCorePackage FiniteModel.carrier) :
    AATCorePackage finiteModelLiftCarrier.{u + 1} :=
  AATCorePackage.generate
    (finiteModelLiftAtomAxiomSystem.{u + 1} package.axioms)
    (finiteModelTaggedLiftCoreReading.{u} package)

/-- The successor-universe generated object is the canonical object lift. -/
theorem finiteModelTaggedLiftCorePackage_object
    (package : AATCorePackage FiniteModel.carrier) :
    (finiteModelTaggedLiftCorePackage.{u} package).object =
      finiteModelLiftArchitectureObject.{u + 1} package.object := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
