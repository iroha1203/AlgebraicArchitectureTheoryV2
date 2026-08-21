import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorComparison

/-!
# Computational field descent for the generated finite factor

This module reflects only fields whose endpoints are canonical finite-model
universe lifts.  It first reflects exact doctrine and pointed-doctrine homs,
then applies those constructions directly to the base of the actual normalized
high factor.  It also reads that factor's upper Atom equivalence, object
configuration, and configuration map directly.

The opaque `StructureMaps` and `SelectedQuantities` fields of an arbitrary high
`ArchitectureObject` are not descended.  Nor is the
`EquationSystemExactTransport.contextEquivalence` field.  Consequently this
module constructs no `SignedExactCoreReadingHom`, `PackageTotalHom`, ambient
factor reflection, or `FiniteModelLift` witness.  `finiteModelSemanticDescent`
is not used or presented as full object descent.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Exact-doctrine hom reflection -/

/--
Reflect an exact doctrine hom whose source and target doctrines are canonical
finite-model universe lifts.  Both computational maps are obtained by
conjugating with `ULift` and the canonical Atom equivalence.
-/
def finiteModelReflectExactDoctrineHom
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E)) :
    ExactDoctrineHom D E where
  sourceMap source := (hom.sourceMap (ULift.up source)).down
  atomEquiv := finiteModelLiftCarrierEquiv.{u}.atom.trans
    (hom.atomEquiv.trans finiteModelLiftCarrierEquiv.{u}.atom.symm)
  normalize_eq source := by
    simpa [finiteModelLiftExtractionDoctrine] using
      congrArg ULift.down (hom.normalize_eq (ULift.up source))
  extraction_iff source atom := by
    simpa [finiteModelLiftExtractionDoctrine] using
      hom.extraction_iff (ULift.up source)
        (finiteModelLiftCarrierEquiv.{u}.atom atom)

/-- Reflected source maps are the `ULift.down` of the actual high source map. -/
@[simp]
theorem finiteModelReflectExactDoctrineHom_sourceMap
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E))
    (source : D.Source) :
    (finiteModelReflectExactDoctrineHom hom).sourceMap source =
      (hom.sourceMap (ULift.up source)).down :=
  rfl

/-- Reflected Atom maps are the inverse-conjugates of the actual high Atom map. -/
@[simp]
theorem finiteModelReflectExactDoctrineHom_atomEquiv
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E))
    (atom : FiniteModel.carrier.Atom) :
    (finiteModelReflectExactDoctrineHom hom).atomEquiv atom =
      finiteModelLiftCarrierEquiv.{u}.atom.symm
        (hom.atomEquiv (finiteModelLiftCarrierEquiv.{u}.atom atom)) :=
  rfl

/-- Lifting the reflected Atom value recovers the actual high Atom value. -/
theorem finiteModelReflectExactDoctrineHom_atom_graph
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E))
    (atom : FiniteModel.carrier.Atom) :
    finiteModelLiftCarrierEquiv.{u}.atom
        ((finiteModelReflectExactDoctrineHom hom).atomEquiv atom) =
      hom.atomEquiv (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  simp [finiteModelReflectExactDoctrineHom]

/-- Reflecting a canonically lifted exact doctrine hom recovers the source hom. -/
@[simp]
theorem finiteModelReflectExactDoctrineHom_lift
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E) :
    finiteModelReflectExactDoctrineHom
        (finiteModelLiftExactDoctrineHom.{u} hom) = hom := by
  apply ExactDoctrineHom.ext
  · funext source
    rfl
  · apply Equiv.ext
    intro atom
    simp [finiteModelReflectExactDoctrineHom,
      finiteModelLiftExactDoctrineHom]

/-- Lifting a reflected exact hom recovers every hom between lifted doctrines. -/
@[simp]
theorem finiteModelLiftExactDoctrineHom_reflect
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E)) :
    finiteModelLiftExactDoctrineHom.{u}
        (finiteModelReflectExactDoctrineHom hom) = hom := by
  apply ExactDoctrineHom.ext
  · funext source
    rcases source with ⟨source⟩
    rfl
  · apply Equiv.ext
    intro atom
    rcases atom with ⟨atom⟩
    simp [finiteModelReflectExactDoctrineHom,
      finiteModelLiftExactDoctrineHom]

/-! ## Pointed-doctrine hom reflection -/

/-- Reflect a pointed exact hom between canonical lifted finite-model instances. -/
def finiteModelReflectExtInstHom
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom (finiteModelLiftExtractionInstance.{u} X)
      (finiteModelLiftExtractionInstance.{u} Y)) :
    ExtInstHom X Y where
  doctrineHom := finiteModelReflectExactDoctrineHom hom.doctrineHom
  source_eq := by
    simpa [finiteModelReflectExactDoctrineHom] using
      congrArg ULift.down hom.source_eq

/-- The reflected pointed hom uses the reflected actual doctrine hom. -/
@[simp]
theorem finiteModelReflectExtInstHom_doctrineHom
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom (finiteModelLiftExtractionInstance.{u} X)
      (finiteModelLiftExtractionInstance.{u} Y)) :
    (finiteModelReflectExtInstHom hom).doctrineHom =
      finiteModelReflectExactDoctrineHom hom.doctrineHom :=
  rfl

/-- The reflected pointed source map is the down-map of the actual high source map. -/
@[simp]
theorem finiteModelReflectExtInstHom_sourceMap
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom (finiteModelLiftExtractionInstance.{u} X)
      (finiteModelLiftExtractionInstance.{u} Y)) :
    (finiteModelReflectExtInstHom hom).doctrineHom.sourceMap X.source =
      (hom.doctrineHom.sourceMap (ULift.up X.source)).down :=
  rfl

/-- Reflecting a lifted pointed hom recovers the original pointed hom. -/
@[simp]
theorem finiteModelReflectExtInstHom_lift
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) :
    finiteModelReflectExtInstHom (finiteModelLiftExtInstHom.{u} hom) = hom := by
  apply ExtInstHom.ext
  exact finiteModelReflectExactDoctrineHom_lift hom.doctrineHom

/-- Lifting a reflected pointed hom recovers every hom between lifted instances. -/
@[simp]
theorem finiteModelLiftExtInstHom_reflect
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom (finiteModelLiftExtractionInstance.{u} X)
      (finiteModelLiftExtractionInstance.{u} Y)) :
    finiteModelLiftExtInstHom.{u} (finiteModelReflectExtInstHom hom) = hom := by
  apply ExtInstHom.ext
  exact finiteModelLiftExactDoctrineHom_reflect hom.doctrineHom

/-! ## Actual normalized-factor base descent -/

/--
Reflect the base of the actual normalized high factor.  The definition reads
that factor's `base` field directly and contains no independently generated low
factor or cartesian certificate.
-/
noncomputable def finiteGeneratedReflectedBase
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    ExtInstHom (packagePoint package) input.source :=
  finiteModelReflectExtInstHom
    (finiteGeneratedNormalizedHighFactor input lift base).base

/-- The actual normalized high base is the lift of its reflected base. -/
theorem finiteGeneratedReflectedBase_high_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteModelLiftExtInstHom.{u}
        (finiteGeneratedReflectedBase input lift base) =
      (finiteGeneratedNormalizedHighFactor input lift base).base :=
  finiteModelLiftExtInstHom_reflect _

/-- The actual normalized high factor has the canonically lifted prefix base. -/
theorem finiteGeneratedNormalizedHighFactor_base_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    (finiteGeneratedNormalizedHighFactor input lift base).base =
      finiteModelLiftExtInstHom.{u} base := by
  rw [finiteGeneratedNormalizedHighFactor_eq_canonical input lift base]
  rfl

/-- Reflection of the actual normalized high base is exactly the low prefix. -/
theorem finiteGeneratedReflectedBase_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedReflectedBase input lift base = base := by
  rw [finiteGeneratedReflectedBase,
    finiteGeneratedNormalizedHighFactor_base_graph]
  exact finiteModelReflectExtInstHom_lift base

/-! ## Actual upper Atom field descent -/

/-- Reflect an arbitrary high finite-carrier Atom equivalence by conjugation. -/
def finiteModelReflectAtomEquiv
    (equiv : finiteModelLiftCarrier.{u}.Atom ≃
      finiteModelLiftCarrier.{u}.Atom) :
    FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom :=
  finiteModelLiftCarrierEquiv.{u}.atom.trans
    (equiv.trans finiteModelLiftCarrierEquiv.{u}.atom.symm)

/-- The reflected Atom equivalence reproduces the high value on lifted Atoms. -/
@[simp]
theorem finiteModelReflectAtomEquiv_graph
    (equiv : finiteModelLiftCarrier.{u}.Atom ≃
      finiteModelLiftCarrier.{u}.Atom)
    (atom : FiniteModel.carrier.Atom) :
    finiteModelLiftCarrierEquiv.{u}.atom
        (finiteModelReflectAtomEquiv equiv atom) =
      equiv (finiteModelLiftCarrierEquiv.{u}.atom atom) := by
  simp [finiteModelReflectAtomEquiv]

/-- Reflect the upper Atom equivalence read directly from the normalized factor. -/
noncomputable def finiteGeneratedReflectedUpperAtomEquiv
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom :=
  finiteModelReflectAtomEquiv
    (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv

/-- The actual high upper Atom map is the lift of the reflected upper Atom map. -/
theorem finiteGeneratedReflectedUpperAtomEquiv_high_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (atom : FiniteModel.carrier.Atom) :
    finiteModelLiftCarrierEquiv.{u}.atom
        (finiteGeneratedReflectedUpperAtomEquiv input lift base atom) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) :=
  finiteModelReflectAtomEquiv_graph _ atom

/-- The reflected actual upper Atom map is the low prefix Atom map. -/
theorem finiteGeneratedReflectedUpperAtomEquiv_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteGeneratedReflectedUpperAtomEquiv input lift base =
      base.doctrineHom.atomEquiv := by
  apply Equiv.ext
  intro atom
  change finiteModelLiftCarrierEquiv.{u}.atom.symm
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom)) = _
  rw [(finiteGeneratedNormalizedHighFactor input lift base).atomEquiv_eq,
    finiteGeneratedNormalizedHighFactor_base_graph,
    finiteModelLiftExtInstHom_atomEquiv]
  exact finiteModelLiftCarrierEquiv.{u}.atom.symm_apply_apply _

/-! ## Actual object-configuration and configuration-map descent -/

/--
Reflect the configuration of the actual high upper object image.  Only the
configuration is descended; this is not an `ArchitectureObject` reflection.
-/
noncomputable def finiteGeneratedReflectedObjectConfiguration
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    AtomConfiguration FiniteModel.carrier :=
  finiteModelReflectAtomConfiguration
    ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
      (finiteModelLiftArchitectureObject.{u} object)).configuration

/-- Lifting the reflected configuration recovers the actual high object configuration. -/
theorem finiteGeneratedReflectedObjectConfiguration_high_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteModelLiftAtomConfiguration.{u}
        (finiteGeneratedReflectedObjectConfiguration input lift base object) =
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object)).configuration :=
  finiteModelLiftAtomConfiguration_reflect _

/--
Reflect the actual upper configuration map on a canonically lifted object,
casting only the source endpoint through the proved configuration round trip.
-/
noncomputable def finiteGeneratedReflectedConfigurationMap
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    ConfigurationHom object.configuration
      (finiteGeneratedReflectedObjectConfiguration input lift base object) :=
  castConfigurationHom
    (finiteModelReflectAtomConfiguration_lift.{u} object.configuration)
    rfl
    (finiteModelReflectConfigurationHom
      ((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} object)))

/-- The reflected configuration map has the reflected actual upper Atom map. -/
theorem finiteGeneratedReflectedConfigurationMap_atom_graph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier)
    (atom : FiniteModel.carrier.Atom) :
    (finiteGeneratedReflectedConfigurationMap input lift base object).atomMap atom =
      finiteGeneratedReflectedUpperAtomEquiv input lift base atom := by
  rw [finiteGeneratedReflectedConfigurationMap,
    castConfigurationHom_atomMap,
    finiteModelReflectConfigurationHom_atomMap]
  change finiteModelLiftCarrierEquiv.{u}.atom.symm
      (((finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} object)).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom)) = _
  rw [(finiteGeneratedNormalizedHighFactor input lift base).upper.configurationMap_atomMap]
  rfl

/-- The reflected actual configuration map uses the original low prefix Atom value. -/
theorem finiteGeneratedReflectedConfigurationMap_atom_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier)
    (atom : FiniteModel.carrier.Atom) :
    (finiteGeneratedReflectedConfigurationMap input lift base object).atomMap atom =
      base.doctrineHom.atomEquiv atom := by
  rw [finiteGeneratedReflectedConfigurationMap_atom_graph,
    finiteGeneratedReflectedUpperAtomEquiv_eq]

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
