import ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedInvariantSignatureMapDescent

/-!
# Generated upper structural-law descent

This module reflects four structural fields of the actual normalized high
upper to the two generated low finite-model domains: `configuration_eq`,
`extraction_eq`, `composition_eq`, and `object_formation_eq`.  Each final proof
crosses to the canonical high image, consumes the corresponding field of
`finiteGeneratedNormalizedHighFactor`, and returns by a canonical finite lift
round trip or injectivity argument.

No low upper, known low law, whole-factor comparison equality, caller image
certificate, global lift, choice, or empty elimination is used.  The complete
object image is used only to retain the opaque fields in object formation.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation

/-! ## Cross-carrier generated structural images -/

/--
The actual high Atom equivalence is the carrier conjugate of the reflected
Atom equivalence.  This field-level equality is proved from the actual high
pointwise graph and does not compare whole factors.
-/
theorem finiteGeneratedStructuralActualHighAtomEquiv_eq_lift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    finiteModelLiftAtomEquiv.{u}
        (finiteGeneratedReflectedUpperAtomEquiv input lift base) =
      (finiteGeneratedNormalizedHighFactor input lift base).upper.atomEquiv := by
  apply Equiv.ext
  intro atom
  rcases atom with ⟨atom⟩
  simpa [finiteModelLiftAtomEquiv] using
    (finiteGeneratedReflectedUpperAtomEquiv_high_graph.{u}
      input lift base atom)

/-- Canonical finite family lifting is injective. -/
theorem finiteModelLiftAtomFamily_injective :
    Function.Injective (finiteModelLiftAtomFamily.{u}) :=
  Function.LeftInverse.injective finiteModelReflectAtomFamily_lift.{u}

/--
Canonical family lifting commutes with transport by an arbitrary finite Atom
equivalence and its conjugated high image.
-/
theorem finiteModelLiftAtomFamily_transport_equiv
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (family : AtomFamily FiniteModel.carrier) :
    finiteModelLiftAtomFamily.{u} (family.transport equiv) =
      (finiteModelLiftAtomFamily.{u} family).transport
        (finiteModelLiftAtomEquiv.{u} equiv) := by
  ext atom
  rcases atom with ⟨atom⟩
  simp [finiteModelLiftAtomFamily, finiteModelLiftAtomEquiv,
    AtomFamily.transport]
  constructor
  · rintro ⟨source, hsource, htarget⟩
    refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source, ?_, ?_⟩
    · simpa using hsource
    · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom htarget
  · rintro ⟨source, hsource, htarget⟩
    refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source, ?_, ?_⟩
    · simpa using hsource
    · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm htarget

/--
The family of a high inverse-generated domain is the canonical lift of the
family of its low inverse-generated domain.
-/
theorem finiteGeneratedDomainFamily_high_image
    (input : FiniteGeneratedLiftInput) :
    finiteModelLiftAtomFamily.{u} input.lowGeneratedLift.domain.family =
      input.highGeneratedLift.domain.family := by
  change finiteModelLiftAtomFamily.{u}
      (input.source.doctrine.atomize input.source.source) =
    (finiteModelLiftExtractionDoctrine.{u} input.source.doctrine).atomize
      (ULift.up input.source.source)
  exact (finiteModelLiftExtractionDoctrine_atomize.{u}
    input.source.doctrine input.source.source).symm

/--
Composition in a high inverse-generated domain on a lifted family is the
canonical lift of composition in the corresponding low generated domain.
-/
theorem finiteGeneratedDomainComposition_high_image
    (input : FiniteGeneratedLiftInput)
    (family : AtomFamily FiniteModel.carrier)
    (hfinite : family.ListFinite) :
    input.highGeneratedLift.domain.reading.composition.compose
        (finiteModelLiftAtomFamily.{u} family)
        (finiteModelLiftAtomFamily_listFinite.{u} hfinite) =
      finiteModelLiftAtomConfiguration.{u}
        (input.lowGeneratedLift.domain.reading.composition.compose
          family hfinite) := by
  change
    (transportCompositionReading
      (finiteModelLiftExactDoctrineHom.{u}
        input.hom.doctrineHom).atomEquiv.symm
      (finiteModelLiftCompositionReading.{u}
        FiniteModel.compositionReading)).compose
        (finiteModelLiftAtomFamily.{u} family)
        (finiteModelLiftAtomFamily_listFinite.{u} hfinite) =
      finiteModelLiftAtomConfiguration.{u}
        ((transportCompositionReading input.hom.doctrineHom.atomEquiv.symm
          FiniteModel.compositionReading).compose family hfinite)
  simp [transportCompositionReading, finiteModelLiftCompositionReading,
    finiteModelLiftAtomFamily_transport_equiv,
    finiteModelLiftAtomConfiguration_transport_equiv]
  have hfamily :
      finiteModelReflectAtomFamily.{u}
          ((finiteModelLiftAtomFamily.{u} family).transport
            (finiteModelLiftExactDoctrineHom.{u}
              input.hom.doctrineHom).atomEquiv) =
        family.transport input.hom.doctrineHom.atomEquiv := by
    exact (congrArg finiteModelReflectAtomFamily.{u}
      (finiteModelLiftAtomFamily_transport_equiv.{u}
        input.hom.doctrineHom.atomEquiv family).symm).trans
      (finiteModelReflectAtomFamily_lift.{u}
        (family.transport input.hom.doctrineHom.atomEquiv))
  have hsymm :
      (finiteModelLiftExactDoctrineHom.{u}
        input.hom.doctrineHom).atomEquiv.symm =
        finiteModelLiftAtomEquiv.{u}
          input.hom.doctrineHom.atomEquiv.symm := by
    change (finiteModelLiftAtomEquiv.{u}
      input.hom.doctrineHom.atomEquiv).symm = _
    exact finiteModelLiftAtomEquiv_symm.{u}
      input.hom.doctrineHom.atomEquiv
  have hinput :
      (⟨finiteModelReflectAtomFamily.{u}
          ((finiteModelLiftAtomFamily.{u} family).transport
            (finiteModelLiftExactDoctrineHom.{u}
              input.hom.doctrineHom).atomEquiv),
        finiteModelReflectAtomFamily_listFinite.{u}
          ((finiteModelLiftAtomFamily_listFinite.{u} hfinite).transport
            (finiteModelLiftExactDoctrineHom.{u}
              input.hom.doctrineHom).atomEquiv)⟩ :
        {F : AtomFamily FiniteModel.carrier // F.ListFinite}) =
      ⟨family.transport input.hom.doctrineHom.atomEquiv,
        hfinite.transport input.hom.doctrineHom.atomEquiv⟩ := by
    apply Subtype.ext
    exact hfamily
  have hcompose :
      FiniteModel.compositionReading.compose
          (finiteModelReflectAtomFamily.{u}
            ((finiteModelLiftAtomFamily.{u} family).transport
              (finiteModelLiftExactDoctrineHom.{u}
                input.hom.doctrineHom).atomEquiv))
          (finiteModelReflectAtomFamily_listFinite.{u}
            ((finiteModelLiftAtomFamily_listFinite.{u} hfinite).transport
              (finiteModelLiftExactDoctrineHom.{u}
                input.hom.doctrineHom).atomEquiv)) =
        FiniteModel.compositionReading.compose
          (family.transport input.hom.doctrineHom.atomEquiv)
          (hfinite.transport input.hom.doctrineHom.atomEquiv) :=
    congrArg
      (fun input : {F : AtomFamily FiniteModel.carrier // F.ListFinite} =>
        FiniteModel.compositionReading.compose input.1 input.2)
      hinput
  rw [hcompose]
  exact congrArg
    (fun equiv : Equiv.Perm finiteModelLiftCarrier.{u}.Atom =>
      (finiteModelLiftAtomConfiguration.{u}
        (FiniteModel.compositionReading.compose
          (family.transport input.hom.doctrineHom.atomEquiv)
          (hfinite.transport input.hom.doctrineHom.atomEquiv))).transport equiv)
    hsymm

/--
Object formation in a high inverse-generated domain on a lifted configuration
is the complete lift of object formation in the low generated domain.
-/
theorem finiteGeneratedDomainObjectFormation_high_image
    (input : FiniteGeneratedLiftInput)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    input.highGeneratedLift.domain.reading.objectReading.object
        (finiteModelLiftAtomConfiguration.{u} configuration) =
      finiteModelLiftArchitectureObject.{u}
        (input.lowGeneratedLift.domain.reading.objectReading.object
          configuration) := by
  change
    (transportObjectReading
      (finiteModelLiftExactDoctrineHom.{u}
        input.hom.doctrineHom).atomEquiv.symm
      (finiteModelLiftObjectReading.{u} FiniteModel.objectReading)).object
        (finiteModelLiftAtomConfiguration.{u} configuration) =
      finiteModelLiftArchitectureObject.{u}
        ((transportObjectReading input.hom.doctrineHom.atomEquiv.symm
          FiniteModel.objectReading).object configuration)
  simp [transportObjectReading, finiteModelLiftObjectReading,
    finiteModelLiftArchitectureObject_transport_equiv,
    finiteModelLiftAtomConfiguration_transport_equiv,
    finiteModelLiftAtomEquiv_symm]
  have hconfiguration :
      finiteModelReflectAtomConfiguration.{u}
          ((finiteModelLiftAtomConfiguration.{u} configuration).transport
            (finiteModelLiftExactDoctrineHom.{u}
              input.hom.doctrineHom).atomEquiv) =
        configuration.transport input.hom.doctrineHom.atomEquiv := by
    exact (congrArg finiteModelReflectAtomConfiguration.{u}
      (finiteModelLiftAtomConfiguration_transport_equiv.{u}
        input.hom.doctrineHom.atomEquiv configuration).symm).trans
      (finiteModelReflectAtomConfiguration_lift.{u}
        (configuration.transport input.hom.doctrineHom.atomEquiv))
  have hsymm :
      (finiteModelLiftExactDoctrineHom.{u}
        input.hom.doctrineHom).atomEquiv.symm =
        finiteModelLiftAtomEquiv.{u}
          input.hom.doctrineHom.atomEquiv.symm := by
    change (finiteModelLiftAtomEquiv.{u}
      input.hom.doctrineHom.atomEquiv).symm = _
    exact finiteModelLiftAtomEquiv_symm.{u}
      input.hom.doctrineHom.atomEquiv
  rw [hconfiguration, hsymm]

/-! ## Reflected exact structural fields -/

/--
The complete reflected object configuration is transport by the reflected
actual upper Atom equivalence.

The proof lifts both configurations, uses the actual normalized high
`configuration_eq` at the lifted object, and cancels configuration lifting.
-/
theorem finiteGeneratedReflectedConfiguration_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (object : ArchitectureObject FiniteModel.carrier) :
    (finiteGeneratedReflectedArchitectureObject input lift base object).configuration =
      object.configuration.transport
        (finiteGeneratedReflectedUpperAtomEquiv input lift base) := by
  apply finiteModelLiftAtomConfiguration_injective.{u}
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  have hactual := actual.upper.configuration_eq
    (finiteModelLiftArchitectureObject.{u} object)
  have hatom := finiteGeneratedStructuralActualHighAtomEquiv_eq_lift.{u}
    input lift base
  calc
    finiteModelLiftAtomConfiguration.{u}
        (finiteGeneratedReflectedArchitectureObject input lift base object).configuration =
      (actual.upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object)).configuration := by
          rw [finiteGeneratedReflectedArchitectureObject_configuration]
          exact finiteGeneratedReflectedObjectConfiguration_high_graph.{u}
            input lift base object
    _ = (finiteModelLiftArchitectureObject.{u} object).configuration.transport
          actual.upper.atomEquiv := hactual
    _ = (finiteModelLiftArchitectureObject.{u} object).configuration.transport
          (finiteModelLiftAtomEquiv.{u}
            (finiteGeneratedReflectedUpperAtomEquiv input lift base)) := by
      rw [hatom]
    _ = finiteModelLiftAtomConfiguration.{u}
          (object.configuration.transport
            (finiteGeneratedReflectedUpperAtomEquiv input lift base)) :=
      (finiteModelLiftAtomConfiguration_transport_equiv.{u}
        (finiteGeneratedReflectedUpperAtomEquiv input lift base)
        object.configuration).symm

/--
The generated target family is exact transport of the generated source family
by the reflected actual upper Atom equivalence.

The actual normalized high `extraction_eq` is the central equality between
the two independently generated family images.
-/
theorem finiteGeneratedReflectedExtraction_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source) :
    input.lowGeneratedLift.domain.family =
      (finiteGeneratedOuterInput input base).lowGeneratedLift.domain.family.transport
        (finiteGeneratedReflectedUpperAtomEquiv input lift base) := by
  apply finiteModelLiftAtomFamily_injective.{u}
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  have hactual := actual.upper.extraction_eq
  have hatom := finiteGeneratedStructuralActualHighAtomEquiv_eq_lift.{u}
    input lift base
  calc
    finiteModelLiftAtomFamily.{u} input.lowGeneratedLift.domain.family =
        input.highGeneratedLift.domain.family :=
      finiteGeneratedDomainFamily_high_image.{u} input
    _ = outer.highGeneratedLift.domain.family.transport
          actual.upper.atomEquiv := hactual
    _ = (finiteModelLiftAtomFamily.{u}
          outer.lowGeneratedLift.domain.family).transport
            actual.upper.atomEquiv := by
      rw [finiteGeneratedDomainFamily_high_image.{u} outer]
    _ = (finiteModelLiftAtomFamily.{u}
          outer.lowGeneratedLift.domain.family).transport
            (finiteModelLiftAtomEquiv.{u}
              (finiteGeneratedReflectedUpperAtomEquiv input lift base)) := by
      rw [hatom]
    _ = finiteModelLiftAtomFamily.{u}
          (outer.lowGeneratedLift.domain.family.transport
            (finiteGeneratedReflectedUpperAtomEquiv input lift base)) :=
      (finiteModelLiftAtomFamily_transport_equiv.{u}
        (finiteGeneratedReflectedUpperAtomEquiv input lift base)
        outer.lowGeneratedLift.domain.family).symm

/--
The reflected composition law holds for every low family and every finiteness
proof.  The actual normalized high `composition_eq` is consumed at the
canonical lifted source family; proof irrelevance aligns the transported
finiteness witnesses.
-/
theorem finiteGeneratedReflectedComposition_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (family : AtomFamily FiniteModel.carrier)
    (hfinite : family.ListFinite) :
    input.lowGeneratedLift.domain.reading.composition.compose
        (family.transport
          (finiteGeneratedReflectedUpperAtomEquiv input lift base))
        (hfinite.transport
          (finiteGeneratedReflectedUpperAtomEquiv input lift base)) =
      ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.composition.compose
        family hfinite).transport
          (finiteGeneratedReflectedUpperAtomEquiv input lift base) := by
  apply finiteModelLiftAtomConfiguration_injective.{u}
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  let reflected := finiteGeneratedReflectedUpperAtomEquiv input lift base
  let lowTransported := family.transport reflected
  let highFamily := finiteModelLiftAtomFamily.{u} family
  let highTransported := highFamily.transport actual.upper.atomEquiv
  have hatom := finiteGeneratedStructuralActualHighAtomEquiv_eq_lift.{u}
    input lift base
  have hfamily :
      finiteModelLiftAtomFamily.{u} lowTransported = highTransported := by
    calc
      finiteModelLiftAtomFamily.{u} lowTransported =
          highFamily.transport (finiteModelLiftAtomEquiv.{u} reflected) :=
        finiteModelLiftAtomFamily_transport_equiv.{u} reflected family
      _ = highTransported := by rw [hatom]
  have htargetInput :
      (⟨finiteModelLiftAtomFamily.{u} lowTransported,
          finiteModelLiftAtomFamily_listFinite.{u}
            (hfinite.transport reflected)⟩ :
        {F : AtomFamily finiteModelLiftCarrier.{u} // F.ListFinite}) =
      ⟨highTransported,
        (finiteModelLiftAtomFamily_listFinite.{u} hfinite).transport
          actual.upper.atomEquiv⟩ := by
    apply Subtype.ext
    exact hfamily
  have hactual := actual.upper.composition_eq highFamily
    (finiteModelLiftAtomFamily_listFinite.{u} hfinite)
  calc
    finiteModelLiftAtomConfiguration.{u}
        (input.lowGeneratedLift.domain.reading.composition.compose
          lowTransported (hfinite.transport reflected)) =
      input.highGeneratedLift.domain.reading.composition.compose
        (finiteModelLiftAtomFamily.{u} lowTransported)
        (finiteModelLiftAtomFamily_listFinite.{u}
          (hfinite.transport reflected)) :=
      (finiteGeneratedDomainComposition_high_image.{u}
        input lowTransported (hfinite.transport reflected)).symm
    _ = input.highGeneratedLift.domain.reading.composition.compose
          highTransported
          ((finiteModelLiftAtomFamily_listFinite.{u} hfinite).transport
            actual.upper.atomEquiv) := by
      exact congrArg
        (fun F : {G : AtomFamily finiteModelLiftCarrier.{u} // G.ListFinite} =>
          input.highGeneratedLift.domain.reading.composition.compose F.1 F.2)
        htargetInput
    _ = (outer.highGeneratedLift.domain.reading.composition.compose
          highFamily (finiteModelLiftAtomFamily_listFinite.{u} hfinite)).transport
            actual.upper.atomEquiv := hactual
    _ = (finiteModelLiftAtomConfiguration.{u}
          (outer.lowGeneratedLift.domain.reading.composition.compose
            family hfinite)).transport actual.upper.atomEquiv := by
      rw [finiteGeneratedDomainComposition_high_image.{u} outer family hfinite]
    _ = (finiteModelLiftAtomConfiguration.{u}
          (outer.lowGeneratedLift.domain.reading.composition.compose
            family hfinite)).transport
          (finiteModelLiftAtomEquiv.{u} reflected) := by rw [hatom]
    _ = finiteModelLiftAtomConfiguration.{u}
          ((outer.lowGeneratedLift.domain.reading.composition.compose
            family hfinite).transport reflected) :=
      (finiteModelLiftAtomConfiguration_transport_equiv.{u} reflected
        (outer.lowGeneratedLift.domain.reading.composition.compose
          family hfinite)).symm

/--
The reflected complete object map commutes with generated object formation for
every low configuration.

The actual normalized high `object_formation_eq` supplies the configuration
equality after both generated object-formation images are aligned.  The
accepted complete reflected-object theorem supplies only the two opaque
finite-model fields.
-/
theorem finiteGeneratedReflectedObjectFormation_eq
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift
      (FiniteGeneratedLiftInput.highInput.{u} input)
      (FiniteGeneratedLiftInput.highTarget.{u} input))
    {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.source)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteGeneratedReflectedArchitectureObject input lift base
        ((finiteGeneratedOuterInput input base).lowGeneratedLift.domain.reading.objectReading.object
          configuration) =
      input.lowGeneratedLift.domain.reading.objectReading.object
        (configuration.transport
          (finiteGeneratedReflectedUpperAtomEquiv input lift base)) := by
  let outer := finiteGeneratedOuterInput input base
  let actual := finiteGeneratedNormalizedHighFactor input lift base
  let reflected := finiteGeneratedReflectedUpperAtomEquiv input lift base
  let sourceObject := outer.lowGeneratedLift.domain.reading.objectReading.object
    configuration
  let targetObject := input.lowGeneratedLift.domain.reading.objectReading.object
    (configuration.transport reflected)
  have hatom := finiteGeneratedStructuralActualHighAtomEquiv_eq_lift.{u}
    input lift base
  have hconfiguration :
      finiteModelLiftAtomConfiguration.{u}
          (configuration.transport reflected) =
        (finiteModelLiftAtomConfiguration.{u} configuration).transport
          actual.upper.atomEquiv := by
    calc
      finiteModelLiftAtomConfiguration.{u}
          (configuration.transport reflected) =
        (finiteModelLiftAtomConfiguration.{u} configuration).transport
          (finiteModelLiftAtomEquiv.{u} reflected) :=
        finiteModelLiftAtomConfiguration_transport_equiv.{u}
          reflected configuration
      _ = (finiteModelLiftAtomConfiguration.{u} configuration).transport
          actual.upper.atomEquiv := by rw [hatom]
  have hactual := actual.upper.object_formation_eq
    (finiteModelLiftAtomConfiguration.{u} configuration)
  have hsource := finiteGeneratedDomainObjectFormation_high_image.{u}
    outer configuration
  have htarget := finiteGeneratedDomainObjectFormation_high_image.{u}
    input (configuration.transport reflected)
  have hhigh :
      finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject input lift base sourceObject) =
        finiteModelLiftArchitectureObject.{u} targetObject := by
    calc
      finiteModelLiftArchitectureObject.{u}
          (finiteGeneratedReflectedArchitectureObject input lift base sourceObject) =
        actual.upper.objectMap
          (finiteModelLiftArchitectureObject.{u} sourceObject) :=
        finiteGeneratedReflectedArchitectureObject_high_image.{u}
          input lift base sourceObject
      _ = actual.upper.objectMap
          (outer.highGeneratedLift.domain.reading.objectReading.object
            (finiteModelLiftAtomConfiguration.{u} configuration)) := by
        rw [hsource]
      _ = input.highGeneratedLift.domain.reading.objectReading.object
          ((finiteModelLiftAtomConfiguration.{u} configuration).transport
            actual.upper.atomEquiv) := hactual
      _ = input.highGeneratedLift.domain.reading.objectReading.object
          (finiteModelLiftAtomConfiguration.{u}
            (configuration.transport reflected)) := by rw [hconfiguration]
      _ = finiteModelLiftArchitectureObject.{u} targetObject := htarget
  have hconfig :
      (finiteGeneratedReflectedArchitectureObject input lift base sourceObject).configuration =
        targetObject.configuration := by
    apply finiteModelLiftAtomConfiguration_injective.{u}
    exact congrArg ArchitectureObject.configuration hhigh
  calc
    finiteGeneratedReflectedArchitectureObject input lift base sourceObject =
        FiniteModel.objectOfConfiguration
          (finiteGeneratedReflectedArchitectureObject input lift base sourceObject).configuration := by
      rw [finiteGeneratedReflectedArchitectureObject_transport]
      rfl
    _ = FiniteModel.objectOfConfiguration targetObject.configuration :=
      congrArg FiniteModel.objectOfConfiguration hconfig
    _ = targetObject := by
      rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
