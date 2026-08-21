import ResearchLean.AG.DoctrineFiberProduct.FiniteModelLiftComparison
import ResearchLean.AG.DoctrineFiberProduct.CartesianTargetWitnesses

/-!
# Naturality of generated lifts for the finite-model universe lift

This module lifts the lower pointed-doctrine data of a finite-model arrow and
compares the generated high-universe lift with an arbitrary strong lift over
the same generated endpoints.  The normalization uses the inverse triangle of
the canonical domain isomorphism, so its result depends on the supplied strong
lift while being equal to the generated high lift.

The constructions are specialized to the canonical finite-model carrier lift
and the selected `FiniteModel.corePackage` target.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Lower pointed-doctrine naturality -/

/-- Lift a pointed finite-model extraction instance through the canonical `ULift`. -/
def finiteModelLiftExtractionInstance
    (pointed : ExtractionInstance FiniteModel.carrier) :
    ExtractionInstance finiteModelLiftCarrier.{u} where
  doctrine := finiteModelLiftExtractionDoctrine.{u} pointed.doctrine
  source := ULift.up pointed.source

/-- The lifted pointed instance has the canonically lifted doctrine. -/
@[simp]
theorem finiteModelLiftExtractionInstance_doctrine
    (pointed : ExtractionInstance FiniteModel.carrier) :
    (finiteModelLiftExtractionInstance.{u} pointed).doctrine =
      finiteModelLiftExtractionDoctrine.{u} pointed.doctrine :=
  rfl

/-- The lifted pointed instance selects the lifted source. -/
@[simp]
theorem finiteModelLiftExtractionInstance_source
    (pointed : ExtractionInstance FiniteModel.carrier) :
    (finiteModelLiftExtractionInstance.{u} pointed).source =
      ULift.up pointed.source :=
  rfl

/-- The selected finite-model package point lifts to the selected lifted package point. -/
@[simp]
theorem finiteModelLiftPackagePoint :
    finiteModelLiftExtractionInstance.{u}
        (packagePoint FiniteModel.corePackage) =
      packagePoint finiteModelLiftCorePackage.{u} :=
  rfl

/--
Lift an exact finite-model doctrine morphism by conjugating its Atom map with
the canonical carrier equivalence and lifting its source map pointwise.
-/
def finiteModelLiftExactDoctrineHom
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E) :
    ExactDoctrineHom (finiteModelLiftExtractionDoctrine.{u} D)
      (finiteModelLiftExtractionDoctrine.{u} E) where
  sourceMap source := ULift.up (hom.sourceMap source.down)
  atomEquiv := finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
    (hom.atomEquiv.trans finiteModelLiftCarrierEquiv.{u}.atom)
  normalize_eq source := by
    apply ULift.ext
    exact hom.normalize_eq source.down
  extraction_iff source atom := by
    simpa [finiteModelLiftExtractionDoctrine] using
      hom.extraction_iff source.down
        (finiteModelLiftCarrierEquiv.{u}.atom.symm atom)

/-- The lifted exact morphism maps a lifted source by lifting its source-map value. -/
@[simp]
theorem finiteModelLiftExactDoctrineHom_sourceMap
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E) (source : D.Source) :
    (finiteModelLiftExactDoctrineHom.{u} hom).sourceMap (ULift.up source) =
      ULift.up (hom.sourceMap source) :=
  rfl

/-- The Atom map of a lifted exact morphism commutes with the carrier lift. -/
@[simp]
theorem finiteModelLiftExactDoctrineHom_atomEquiv
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E) (atom : FiniteModel.carrier.Atom) :
    (finiteModelLiftExactDoctrineHom.{u} hom).atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom (hom.atomEquiv atom) := by
  simp [finiteModelLiftExactDoctrineHom]

/-- Canonical doctrine lifting preserves identity exact morphisms. -/
@[simp]
theorem finiteModelLiftExactDoctrineHom_id
    (D : ExtractionDoctrine FiniteModel.carrier) :
    finiteModelLiftExactDoctrineHom.{u} (ExactDoctrineHom.id D) =
      ExactDoctrineHom.id (finiteModelLiftExtractionDoctrine.{u} D) := by
  apply ExactDoctrineHom.ext
  · funext source
    rcases source with ⟨source⟩
    rfl
  · apply Equiv.ext
    intro atom
    simp [finiteModelLiftExactDoctrineHom, ExactDoctrineHom.id]

/-- Canonical doctrine lifting preserves composition in first-then-second order. -/
@[simp]
theorem finiteModelLiftExactDoctrineHom_comp
    {D E F : ExtractionDoctrine FiniteModel.carrier}
    (first : ExactDoctrineHom D E) (second : ExactDoctrineHom E F) :
    finiteModelLiftExactDoctrineHom.{u} (first.comp second) =
      (finiteModelLiftExactDoctrineHom.{u} first).comp
        (finiteModelLiftExactDoctrineHom.{u} second) := by
  apply ExactDoctrineHom.ext
  · funext source
    rcases source with ⟨source⟩
    rfl
  · apply Equiv.ext
    intro atom
    simp [finiteModelLiftExactDoctrineHom, ExactDoctrineHom.comp]

/-- Lift a pointed exact morphism between finite-model extraction instances. -/
def finiteModelLiftExtInstHom
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) :
    ExtInstHom (finiteModelLiftExtractionInstance.{u} X)
      (finiteModelLiftExtractionInstance.{u} Y) where
  doctrineHom := finiteModelLiftExactDoctrineHom.{u} hom.doctrineHom
  source_eq := congrArg ULift.up hom.source_eq

/-- The doctrine component of a lifted pointed morphism is the lifted exact morphism. -/
@[simp]
theorem finiteModelLiftExtInstHom_doctrineHom
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) :
    (finiteModelLiftExtInstHom.{u} hom).doctrineHom =
      finiteModelLiftExactDoctrineHom.{u} hom.doctrineHom :=
  rfl

/-- A lifted pointed morphism has the pointwise lifted source map. -/
@[simp]
theorem finiteModelLiftExtInstHom_sourceMap
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) (source : X.doctrine.Source) :
    (finiteModelLiftExtInstHom.{u} hom).doctrineHom.sourceMap
        (ULift.up source) = ULift.up (hom.doctrineHom.sourceMap source) :=
  rfl

/-- The pointed-morphism Atom map commutes with the canonical carrier lift. -/
@[simp]
theorem finiteModelLiftExtInstHom_atomEquiv
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) (atom : FiniteModel.carrier.Atom) :
    (finiteModelLiftExtInstHom.{u} hom).doctrineHom.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (hom.doctrineHom.atomEquiv atom) :=
  finiteModelLiftExactDoctrineHom_atomEquiv hom.doctrineHom atom

/-- The lifted pointed morphism maps the selected source to the lifted target source. -/
@[simp]
theorem finiteModelLiftExtInstHom_source_eq
    {X Y : ExtractionInstance FiniteModel.carrier}
    (hom : ExtInstHom X Y) :
    (finiteModelLiftExtInstHom.{u} hom).doctrineHom.sourceMap
        (ULift.up X.source) = ULift.up Y.source := by
  exact congrArg ULift.up hom.source_eq

/-- Pointed-morphism lifting preserves identities. -/
@[simp]
theorem finiteModelLiftExtInstHom_id
    (X : ExtractionInstance FiniteModel.carrier) :
    finiteModelLiftExtInstHom.{u} (ExtInstHom.id X) =
      ExtInstHom.id (finiteModelLiftExtractionInstance.{u} X) := by
  apply ExtInstHom.ext
  exact finiteModelLiftExactDoctrineHom_id X.doctrine

/-- Pointed-morphism lifting preserves first-then-second composition. -/
@[simp]
theorem finiteModelLiftExtInstHom_comp
    {X Y Z : ExtractionInstance FiniteModel.carrier}
    (first : ExtInstHom X Y) (second : ExtInstHom Y Z) :
    finiteModelLiftExtInstHom.{u} (first.comp second) =
      (finiteModelLiftExtInstHom.{u} first).comp
        (finiteModelLiftExtInstHom.{u} second) := by
  apply ExtInstHom.ext
  exact finiteModelLiftExactDoctrineHom_comp
    first.doctrineHom second.doctrineHom

/-! ## Cross-carrier transport graphs -/

/--
Canonical configuration lifting commutes with direct-image transport by an
exact doctrine morphism and its conjugated lifted Atom equivalence.
-/
theorem finiteModelLiftAtomConfiguration_transport
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    finiteModelLiftAtomConfiguration.{u}
        (configuration.transport hom.atomEquiv) =
      (finiteModelLiftAtomConfiguration.{u} configuration).transport
        (finiteModelLiftExactDoctrineHom.{u} hom).atomEquiv := by
  apply AtomConfiguration.ext
  · ext atom
    rcases atom with ⟨atom⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily,
      finiteModelLiftExactDoctrineHom, AtomConfiguration.transport,
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
  · intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftExactDoctrineHom,
      AtomConfiguration.transport]
    constructor
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source₁,
        finiteModelLiftCarrierEquiv.{u}.atom source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hsecond
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source₁,
        finiteModelLiftCarrierEquiv.{u}.atom.symm source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hsecond
  · intro first second
    rcases first with ⟨first⟩
    rcases second with ⟨second⟩
    simp [finiteModelLiftAtomConfiguration, finiteModelLiftExactDoctrineHom,
      AtomConfiguration.transport]
    constructor
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom source₁,
        finiteModelLiftCarrierEquiv.{u}.atom source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom hsecond
    · rintro ⟨source₁, source₂, hsource, hfirst, hsecond⟩
      refine ⟨finiteModelLiftCarrierEquiv.{u}.atom.symm source₁,
        finiteModelLiftCarrierEquiv.{u}.atom.symm source₂, ?_, ?_, ?_⟩
      · simpa using hsource
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hfirst
      · simpa using congrArg finiteModelLiftCarrierEquiv.{u}.atom.symm hsecond

/--
Canonical architecture-object lifting commutes with same-carrier object
transport by an exact doctrine morphism and its lifted Atom equivalence.
-/
theorem finiteModelLiftArchitectureObject_transport
    {D E : ExtractionDoctrine FiniteModel.carrier}
    (hom : ExactDoctrineHom D E)
    (object : ArchitectureObject FiniteModel.carrier) :
    transportArchitectureObject
        (finiteModelLiftExactDoctrineHom.{u} hom).atomEquiv
        (finiteModelLiftArchitectureObject.{u} object) =
      finiteModelLiftArchitectureObject.{u}
        (transportArchitectureObject hom.atomEquiv object) := by
  cases object with
  | mk configuration StructureMaps SelectedQuantities structureMaps selectedQuantities =>
      simp [transportArchitectureObject, finiteModelLiftArchitectureObject,
        finiteModelLiftAtomConfiguration_transport]

/--
Canonical circuit-query lifting commutes with same-carrier transport after
conjugating the source Atom equivalence to the lifted carrier.
-/
theorem finiteModelLiftCircuitQuery_transport
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (query : CircuitQuery FiniteModel.carrier) :
    finiteModelLiftCircuitQuery.{u} (query.transport equiv) =
      (finiteModelLiftCircuitQuery.{u} query).transport
        (finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
          (equiv.trans finiteModelLiftCarrierEquiv.{u}.atom)) := by
  cases query <;>
    simp [finiteModelLiftCircuitQuery, CircuitQuery.transport]

/--
Canonical signed-circuit lifting commutes with same-carrier transport after
conjugating the source Atom equivalence to the lifted carrier.
-/
theorem finiteModelLiftFiniteCircuitDatum_transport
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    finiteModelLiftFiniteCircuitDatum.{u} (datum.transport equiv) =
      (finiteModelLiftFiniteCircuitDatum.{u} datum).transport
        (finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
          (equiv.trans finiteModelLiftCarrierEquiv.{u}.atom)) := by
  cases datum with
  | mk queries =>
      simp [finiteModelLiftFiniteCircuitDatum,
        FiniteCircuitDatum.transport, List.map_map,
        Function.comp_def, finiteModelLiftCircuitQuery_transport]

/--
Canonical detector-code lifting commutes with same-carrier transport after
conjugating the source Atom equivalence to the lifted carrier.
-/
theorem finiteModelLiftCircuitDetectorCode_transport
    (equiv : Equiv.Perm FiniteModel.carrier.Atom)
    (code : CircuitDetectorCode FiniteModel.carrier) :
    finiteModelLiftCircuitDetectorCode.{u} (code.transport equiv) =
      (finiteModelLiftCircuitDetectorCode.{u} code).transport
        (finiteModelLiftCarrierEquiv.{u}.atom.symm.trans
          (equiv.trans finiteModelLiftCarrierEquiv.{u}.atom)) := by
  induction code with
  | reject => rfl
  | exact datum =>
      simp [finiteModelLiftCircuitDetectorCode,
        CircuitDetectorCode.transport,
        finiteModelLiftFiniteCircuitDatum_transport]
  | any left right hleft hright =>
      simp [finiteModelLiftCircuitDetectorCode,
        CircuitDetectorCode.transport, hleft, hright]

/-! ## Generated low and high lifts at the selected finite target -/

/--
A base finite-model arrow whose target is the pointed doctrine selected by
`FiniteModel.corePackage`.
-/
structure FiniteGeneratedLiftInput where
  /-- Source pointed extraction instance. -/
  source : ExtractionInstance FiniteModel.carrier
  /-- Exact pointed arrow to the selected finite-model package point. -/
  hom : source ⟶ packagePoint FiniteModel.corePackage

namespace FiniteGeneratedLiftInput

/-- The base-carrier semantic input represented by a generated-lift input. -/
noncomputable def lowInput (input : FiniteGeneratedLiftInput) :
    CartSemanticInput FiniteModel.carrier where
  source := input.source
  target := packagePoint FiniteModel.corePackage
  hom := input.hom

/-- The low semantic input retains the supplied lower arrow. -/
@[simp]
theorem lowInput_hom (input : FiniteGeneratedLiftInput) :
    input.lowInput.hom = input.hom :=
  rfl

/-- The selected finite-model package as the exact low-universe target fiber object. -/
noncomputable def lowTarget (input : FiniteGeneratedLiftInput) :
    CoreFiber input.lowInput.target :=
  ⟨FiniteModel.corePackage, rfl⟩

/-- Lifting the selected base package point gives the selected lifted package point. -/
@[simp]
theorem lift_packagePoint :
    finiteModelLiftExtractionInstance.{u}
        (packagePoint FiniteModel.corePackage) =
      packagePoint finiteModelLiftCorePackage.{u} :=
  rfl

/-- The high-universe semantic input obtained from the generated lower arrow. -/
noncomputable def highInput (input : FiniteGeneratedLiftInput) :
    CartSemanticInput finiteModelLiftCarrier.{u} where
  source := finiteModelLiftExtractionInstance.{u} input.source
  target := packagePoint finiteModelLiftCorePackage.{u}
  hom := finiteModelLiftExtInstHom.{u} input.hom

/-- The high semantic input uses exactly the canonically lifted lower arrow. -/
@[simp]
theorem highInput_hom (input : FiniteGeneratedLiftInput) :
    input.highInput.hom = finiteModelLiftExtInstHom.{u} input.hom :=
  rfl

/-- The selected lifted finite-model package as the exact high target fiber object. -/
noncomputable def highTarget (input : FiniteGeneratedLiftInput) :
    CoreFiber input.highInput.target :=
  ⟨finiteModelLiftCorePackage.{u}, rfl⟩

/-- The generated strong cartesian lift of the base arrow to the selected base package. -/
noncomputable def lowGeneratedLift (input : FiniteGeneratedLiftInput) :
    StrongCartesianLift input.lowInput input.lowTarget :=
  strongCartesianLiftOfTarget input.lowInput input.lowTarget

/-- The generated strong cartesian lift of the lifted arrow to the selected lifted package. -/
noncomputable def highGeneratedLift (input : FiniteGeneratedLiftInput) :
    StrongCartesianLift input.highInput input.highTarget :=
  strongCartesianLiftOfTarget input.highInput input.highTarget

/-! ## Independent high inverse-package generation from the low arrow -/

/--
The lower arrow used by the high inverse-package constructor.  It is obtained
by canonically lifting the supplied low arrow and aligning the selected target
fiber equality in the same first-then-second order as
`strongCartesianLiftOfTarget`.
-/
noncomputable def highAlignedBaseFromLowData (input : FiniteGeneratedLiftInput) :
    input.highInput.source ⟶ packagePoint finiteModelLiftCorePackage.{u} :=
  input.highInput.hom ≫ eqToHom (by rfl)

/-- Target alignment does not change the canonically lifted lower arrow. -/
@[simp]
theorem highAlignedBaseFromLowData_eq
    (input : FiniteGeneratedLiftInput) :
    input.highAlignedBaseFromLowData =
      finiteModelLiftExtInstHom.{u} input.hom := by
  simp [highAlignedBaseFromLowData]

/--
The named high package generated directly from the lifted low arrow by the
canonical inverse-package constructor.
-/
noncomputable def highPackageFromLowData (input : FiniteGeneratedLiftInput) :
    AATCorePackage finiteModelLiftCarrier.{u} :=
  inverseCorePackage finiteModelLiftCorePackage.{u}
    input.highAlignedBaseFromLowData

/--
The named total hom generated with the named high package from the same lifted
low arrow.
-/
noncomputable def highPackageHomFromLowData (input : FiniteGeneratedLiftInput) :
    input.highPackageFromLowData ⟶ finiteModelLiftCorePackage.{u} :=
  inverseCorePackageHom finiteModelLiftCorePackage.{u}
    input.highAlignedBaseFromLowData

/-- The independently generated high package lies over the lifted low source. -/
@[simp]
theorem highPackageFromLowData_point (input : FiniteGeneratedLiftInput) :
    packagePoint (highPackageFromLowData.{u} input) =
      (highInput.{u} input).source := by
  unfold highPackageFromLowData
  exact inverseCorePackage_point finiteModelLiftCorePackage.{u}
    input.highAlignedBaseFromLowData

/-- The named high total hom projects to the canonically lifted lower arrow. -/
@[simp]
theorem highPackageHomFromLowData_base (input : FiniteGeneratedLiftInput) :
    input.highPackageHomFromLowData.base =
      finiteModelLiftExtInstHom.{u} input.hom := by
  change input.highAlignedBaseFromLowData = _
  exact input.highAlignedBaseFromLowData_eq

/-- The package projection of the named high total hom is the lifted low arrow. -/
theorem highPackageHomFromLowData_projection
    (input : FiniteGeneratedLiftInput) :
    (packageProjection finiteModelLiftCarrier.{u}).map
        input.highPackageHomFromLowData = input.highInput.hom := by
  exact input.highPackageHomFromLowData_base

/-- The generated high lift domain is the independently generated high package. -/
theorem highGeneratedLift_domain_eq_highPackageFromLowData
    (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.domain = input.highPackageFromLowData := by
  rfl

/-- The generated high lift hom is the independently generated high total hom. -/
theorem highGeneratedLift_hom_eq_highPackageHomFromLowData
    (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.hom = input.highPackageHomFromLowData := by
  rfl

/-! ## Observational equation-component graphs -/

/--
The generated low upper equation map retains the fixed finite-model equation
index.  This is one projection of the same-carrier generated upper; it is not
a cross-carrier `EquationSystemExactTransport` equality.
-/
theorem lowGeneratedLift_upper_equationMap_heq
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index) :
    HEq
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationMap index) index := by
  exact inverseCoreEquationForward_equationMap_heq
    FiniteModel.corePackage input.hom index

/--
The independently generated high upper equation map retains its lifted
finite-model equation index.  This records only the computational index graph.
-/
theorem highPackageHomFromLowData_upper_equationMap_heq
    (input : FiniteGeneratedLiftInput)
    (index : (highPackageFromLowData.{u} input).algebra.equationSystem.Index) :
    HEq ((highPackageHomFromLowData.{u} input).upper.equationMap index) index := by
  change HEq
    ((inverseCoreEquationForward finiteModelLiftCorePackage.{u}
      input.highAlignedBaseFromLowData).equationMap index) index
  exact inverseCoreEquationForward_equationMap_heq
    finiteModelLiftCorePackage.{u} input.highAlignedBaseFromLowData index

/-- Canonically lift an equation index of the selected finite-model target package. -/
def targetEquationIndexLift
    (index : FiniteModel.corePackage.algebra.equationSystem.Index) :
    finiteModelLiftCorePackage.{u}.algebra.equationSystem.Index :=
  ULift.up index

/--
Lift an equation index of the low inverse-generated domain by mapping it to the
low target, lifting that target index, and using the inverse of the generated
high equation-index equivalence.  No index correspondence is supplied by the
caller.
-/
noncomputable def generatedDomainEquationIndexLift
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index) :
    (highPackageFromLowData.{u} input).algebra.equationSystem.Index :=
  (highPackageHomFromLowData.{u} input).upper.equationTransport.equationEquiv.symm
    (targetEquationIndexLift.{u}
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).equationMap index))

/--
The generated high equation map commutes exactly with the canonical target
index lift.  This is an observational equation component, not an equality of
the complete cross-carrier equation transports.
-/
theorem generatedUpper_equationMap_graph
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index) :
    (highPackageHomFromLowData.{u} input).upper.equationMap
        (generatedDomainEquationIndexLift.{u} input index) =
      targetEquationIndexLift.{u}
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).equationMap index) := by
  exact Equiv.apply_symm_apply
    (highPackageHomFromLowData.{u} input).upper.equationTransport.equationEquiv _

/-- The selected target detector commutes with canonical equation-index lifting. -/
theorem targetDetectorCode_graph
    (index : FiniteModel.corePackage.algebra.equationSystem.Index) :
    finiteModelLiftCorePackage.{u}.algebra.circuits.code
        (targetEquationIndexLift.{u} index) =
      finiteModelLiftCircuitDetectorCode.{u}
        (FiniteModel.corePackage.algebra.circuits.code index) := by
  cases index
  rfl

/--
Equation fulfillment in the selected lifted target is exactly fulfillment in
the selected finite-model target on a canonically lifted object.  The proof
uses the direct NoCycle semantics; it does not postulate a cross-carrier
context equivalence.
-/
theorem targetEquationHolds_graph
    (index : FiniteModel.corePackage.algebra.equationSystem.Index)
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteModelLiftCorePackage.{u}.algebra.equationSystem.EquationHolds
        (targetEquationIndexLift.{u} index)
        (finiteModelLiftArchitectureObject.{u} object) ↔
      FiniteModel.corePackage.algebra.equationSystem.EquationHolds
        index object := by
  cases index
  change
    (finiteModelLiftEquationSystem.{u} _).EquationHolds
        (ULift.up PUnit.unit) (finiteModelLiftArchitectureObject.{u} object) ↔
      (FiniteModel.equationSystem _).EquationHolds PUnit.unit object
  rw [finiteModelLiftEquationHolds_iff_source]
  rw [FiniteModel.equationHolds_iff_noCycle,
    FiniteModel.equationHolds_iff_noCycle]
  simp [FiniteModel.hasDependencyCycle, finiteModelSemanticDescent,
    finiteModelLiftArchitectureObject, FiniteModel.objectOfConfiguration]

/--
The detector on the high inverse-generated domain is exactly the canonical
cross-carrier lift of the detector on the low inverse-generated domain.

This theorem compares detector syntax only.  Together with the equation-index
graph it is a projection of generated upper naturality, not a claim that the
complete `EquationSystemExactTransport` or `PackageTotalHom` has been lifted.
-/
theorem inverseGeneratedDomain_detectorCode_graph
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index) :
    (highPackageFromLowData.{u} input).algebra.circuits.code
        (generatedDomainEquationIndexLift.{u} input index) =
      finiteModelLiftCircuitDetectorCode.{u}
        ((inverseCorePackage FiniteModel.corePackage
          input.hom).algebra.circuits.code index) := by
  let lowUpper := inverseCorePackageForwardUpper FiniteModel.corePackage input.hom
  let highUpper := (highPackageHomFromLowData.{u} input).upper
  have hhigh := highUpper.detectorCode_eq
    (generatedDomainEquationIndexLift.{u} input index)
  have hlow := lowUpper.detectorCode_eq index
  have htarget := targetDetectorCode_graph.{u} (lowUpper.equationMap index)
  have htransport :
      (finiteModelLiftCircuitDetectorCode.{u}
          ((inverseCorePackage FiniteModel.corePackage input.hom).algebra.circuits.code
            index)).transport highUpper.atomEquiv =
        finiteModelLiftCircuitDetectorCode.{u}
          (((inverseCorePackage FiniteModel.corePackage input.hom).algebra.circuits.code
            index).transport lowUpper.atomEquiv) := by
    rw [show highUpper.atomEquiv =
        (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv by
      dsimp [highUpper]
      calc
        input.highPackageHomFromLowData.upper.atomEquiv =
            input.highPackageHomFromLowData.base.doctrineHom.atomEquiv :=
          input.highPackageHomFromLowData.atomEquiv_eq
        _ = (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv :=
          congrArg (fun hom => hom.doctrineHom.atomEquiv)
            input.highPackageHomFromLowData_base]
    rw [show lowUpper.atomEquiv = input.hom.doctrineHom.atomEquiv by
      rfl]
    exact (finiteModelLiftCircuitDetectorCode_transport.{u}
      input.hom.doctrineHom.atomEquiv
      ((inverseCorePackage FiniteModel.corePackage input.hom).algebra.circuits.code
        index)).symm
  have htransported :
      ((highPackageFromLowData.{u} input).algebra.circuits.code
          (generatedDomainEquationIndexLift.{u} input index)).transport
          highUpper.atomEquiv =
        (finiteModelLiftCircuitDetectorCode.{u}
          ((inverseCorePackage FiniteModel.corePackage input.hom).algebra.circuits.code
            index)).transport highUpper.atomEquiv := by
    calc
      _ = finiteModelLiftCorePackage.{u}.algebra.circuits.code
          (highUpper.equationMap
            (generatedDomainEquationIndexLift.{u} input index)) := hhigh.symm
      _ = finiteModelLiftCorePackage.{u}.algebra.circuits.code
          (targetEquationIndexLift.{u} (lowUpper.equationMap index)) := by
            rw [generatedUpper_equationMap_graph]
      _ = finiteModelLiftCircuitDetectorCode.{u}
          (FiniteModel.corePackage.algebra.circuits.code
            (lowUpper.equationMap index)) := htarget
      _ = finiteModelLiftCircuitDetectorCode.{u}
          (((inverseCorePackage FiniteModel.corePackage input.hom).algebra.circuits.code
            index).transport lowUpper.atomEquiv) := congrArg _ hlow
      _ = _ := htransport.symm
  have hcancel := congrArg
    (fun code => code.transport highUpper.atomEquiv.symm) htransported
  simpa using hcancel

/--
Equation fulfillment is preserved and reflected between the low and high
inverse-generated domains on canonically lifted objects.  Each side uses its
own same-carrier exact equation transport; no cross-carrier context
equivalence is supplied or asserted.
-/
theorem inverseGeneratedDomain_equationHolds_iff
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).algebra.equationSystem.Index)
    (object : ArchitectureObject FiniteModel.carrier) :
    (inverseCorePackage FiniteModel.corePackage input.hom).algebra.equationSystem.EquationHolds
        index object ↔
      (highPackageFromLowData.{u} input).algebra.equationSystem.EquationHolds
        (generatedDomainEquationIndexLift.{u} input index)
        (finiteModelLiftArchitectureObject.{u} object) := by
  let lowUpper := inverseCorePackageForwardUpper FiniteModel.corePackage input.hom
  let highUpper := (highPackageHomFromLowData.{u} input).upper
  rw [lowUpper.equation_holds_iff, highUpper.equation_holds_iff]
  rw [generatedUpper_equationMap_graph]
  have hobject :
      highUpper.objectMap (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u} (lowUpper.objectMap object) := by
    change
      transportArchitectureObject
          (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
          (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u}
          (transportArchitectureObject input.hom.doctrineHom.atomEquiv object)
    exact finiteModelLiftArchitectureObject_transport.{u}
      input.hom.doctrineHom object
  rw [hobject]
  exact (targetEquationHolds_graph.{u}
    (lowUpper.equationMap index) (lowUpper.objectMap object)).symm

/--
The upper Atom equivalence of the named high hom is generated from the lifted
lower doctrine hom.
-/
theorem highPackageHomFromLowData_upper_atomEquiv
    (input : FiniteGeneratedLiftInput) :
    input.highPackageHomFromLowData.upper.atomEquiv =
      (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv := by
  calc
    input.highPackageHomFromLowData.upper.atomEquiv =
        input.highPackageHomFromLowData.base.doctrineHom.atomEquiv :=
      input.highPackageHomFromLowData.atomEquiv_eq
    _ = (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv :=
      congrArg (fun hom => hom.doctrineHom.atomEquiv)
        input.highPackageHomFromLowData_base

/-- The named high upper Atom map has the exact cross-carrier pointwise graph. -/
@[simp]
theorem highPackageHomFromLowData_upper_atom_graph
    (input : FiniteGeneratedLiftInput) (atom : FiniteModel.carrier.Atom) :
    input.highPackageHomFromLowData.upper.atomEquiv
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        (input.hom.doctrineHom.atomEquiv atom) := by
  rw [input.highPackageHomFromLowData_upper_atomEquiv]
  exact finiteModelLiftExtInstHom_atomEquiv input.hom atom

/-- The generated low upper Atom equivalence is the supplied low Atom equivalence. -/
theorem lowGeneratedLift_upper_atomEquiv
    (input : FiniteGeneratedLiftInput) :
    input.lowGeneratedLift.hom.upper.atomEquiv =
      input.hom.doctrineHom.atomEquiv := by
  calc
    input.lowGeneratedLift.hom.upper.atomEquiv =
        input.lowGeneratedLift.hom.base.doctrineHom.atomEquiv :=
      input.lowGeneratedLift.hom.atomEquiv_eq
    _ = input.hom.doctrineHom.atomEquiv :=
      congrArg (fun base => base.doctrineHom.atomEquiv)
        (show input.lowGeneratedLift.hom.base = input.hom by
          simp [lowGeneratedLift, strongCartesianLiftOfTarget, lowTarget,
            lowInput, inverseCorePackageHom])

/-- The generated low upper object map is transport by the supplied low Atom map. -/
theorem lowGeneratedLift_upper_objectMap
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier) :
    input.lowGeneratedLift.hom.upper.objectMap object =
      transportArchitectureObject input.hom.doctrineHom.atomEquiv object := by
  rw [← input.lowGeneratedLift_upper_atomEquiv]
  rfl

/-- The named high upper object map is canonical transport by the lifted Atom map. -/
theorem highPackageHomFromLowData_upper_objectMap
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    input.highPackageHomFromLowData.upper.objectMap object =
      transportArchitectureObject
        (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv
        object := by
  rw [← input.highPackageHomFromLowData_upper_atomEquiv]
  rfl

/--
The generated high upper object map on a lifted object is the lift of the low
generated upper object map.
-/
theorem highPackageHomFromLowData_upper_objectMap_lift
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier) :
    input.highPackageHomFromLowData.upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object) =
      finiteModelLiftArchitectureObject.{u}
        (input.lowGeneratedLift.hom.upper.objectMap object) := by
  rw [input.highPackageHomFromLowData_upper_objectMap]
  rw [input.lowGeneratedLift_upper_objectMap]
  change
    transportArchitectureObject
        (finiteModelLiftExactDoctrineHom.{u} input.hom.doctrineHom).atomEquiv
        (finiteModelLiftArchitectureObject.{u} object) =
      finiteModelLiftArchitectureObject.{u}
        (transportArchitectureObject input.hom.doctrineHom.atomEquiv object)
  exact finiteModelLiftArchitectureObject_transport.{u}
    input.hom.doctrineHom object

/--
The target configuration of the high map on a lifted object is the canonical
lift of the target configuration of the corresponding low map.
-/
theorem highPackageHomFromLowData_upper_configurationMap_target
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier) :
    (input.highPackageHomFromLowData.upper.objectMap
        (finiteModelLiftArchitectureObject.{u} object)).configuration =
      finiteModelLiftAtomConfiguration.{u}
        (input.lowGeneratedLift.hom.upper.objectMap object).configuration := by
  exact congrArg ArchitectureObject.configuration
    (input.highPackageHomFromLowData_upper_objectMap_lift object)

/--
After the generated target-endpoint equality, the high configuration map on a
lifted object is exactly the canonical lift of the low configuration map.
-/
theorem highPackageHomFromLowData_upper_configurationMap_lift
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier) :
    input.highPackageHomFromLowData.upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} object) =
      castConfigurationHom rfl
        (input.highPackageHomFromLowData_upper_configurationMap_target
          object).symm
        (finiteModelLiftConfigurationHom.{u}
          (input.lowGeneratedLift.hom.upper.configurationMap object)) := by
  apply ConfigurationHom.ext
  rw [castConfigurationHom_atomMap,
    finiteModelLiftConfigurationHom_atomMap,
    input.highPackageHomFromLowData.upper.configurationMap_atomMap,
    input.lowGeneratedLift.hom.upper.configurationMap_atomMap,
    input.highPackageHomFromLowData_upper_atomEquiv,
    input.lowGeneratedLift_upper_atomEquiv]
  rfl

/-- The cross-carrier configuration-map equality has the exact pointwise Atom graph. -/
@[simp]
theorem highPackageHomFromLowData_upper_configurationMap_atom_graph
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier)
    (atom : FiniteModel.carrier.Atom) :
    (input.highPackageHomFromLowData.upper.configurationMap
        (finiteModelLiftArchitectureObject.{u} object)).atomMap
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        ((input.lowGeneratedLift.hom.upper.configurationMap object).atomMap
          atom) := by
  rw [input.highPackageHomFromLowData.upper.configurationMap_atomMap,
    input.lowGeneratedLift.hom.upper.configurationMap_atomMap,
    input.highPackageHomFromLowData_upper_atom_graph]
  exact congrArg finiteModelLiftCarrierEquiv.{u}.atom
    (congrFun (congrArg Equiv.toFun
      input.lowGeneratedLift_upper_atomEquiv) atom).symm

/-- The mapped object's configuration is direct image by the lifted lower Atom map. -/
theorem highPackageHomFromLowData_upper_configuration
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (input.highPackageHomFromLowData.upper.objectMap object).configuration =
      object.configuration.transport
        (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv := by
  calc
    (input.highPackageHomFromLowData.upper.objectMap object).configuration =
        object.configuration.transport
          input.highPackageHomFromLowData.upper.atomEquiv :=
      input.highPackageHomFromLowData.upper.configuration_eq object
    _ = object.configuration.transport
          (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv :=
      congrArg (fun atomMap => object.configuration.transport atomMap)
        (congrArg Equiv.toFun
          input.highPackageHomFromLowData_upper_atomEquiv)

/-- The named high configuration map uses exactly the lifted lower Atom map. -/
theorem highPackageHomFromLowData_upper_configurationMap_atomMap
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject finiteModelLiftCarrier.{u}) :
    (input.highPackageHomFromLowData.upper.configurationMap object).atomMap =
      (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv := by
  calc
    (input.highPackageHomFromLowData.upper.configurationMap object).atomMap =
        input.highPackageHomFromLowData.upper.atomEquiv :=
      input.highPackageHomFromLowData.upper.configurationMap_atomMap object
    _ = (finiteModelLiftExtInstHom.{u} input.hom).doctrineHom.atomEquiv :=
      congrArg Equiv.toFun input.highPackageHomFromLowData_upper_atomEquiv

/-! ## Invariant and signature observations -/

/-- Canonically lift an invariant index of the selected finite-model target. -/
def targetInvariantIndexLift
    (index : FiniteModel.corePackage.reading.invariantReading.Index) :
    finiteModelLiftCorePackage.{u}.reading.invariantReading.Index :=
  ULift.up index

/-- Canonically lift an invariant index of the low inverse-generated domain. -/
def generatedDomainInvariantIndexLift
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.invariantReading.Index) :
    (highPackageFromLowData.{u} input).reading.invariantReading.Index :=
  ULift.up index

/-- The generated upper invariant-index maps commute with canonical lifting. -/
theorem generatedUpper_invariantMap_graph
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.invariantReading.Index) :
    (highPackageHomFromLowData.{u} input).upper.invariantMap
        (generatedDomainInvariantIndexLift.{u} input index) =
      targetInvariantIndexLift.{u}
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).invariantMap index) := by
  rfl

/--
The low and high inverse-generated singleton invariants have the same truth
value on a base object and its canonical lift.
-/
theorem inverseGeneratedDomain_invariant_holds_iff
    (input : FiniteGeneratedLiftInput)
    (index : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.invariantReading.Index)
    (object : ArchitectureObject FiniteModel.carrier) :
    (match (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.invariantReading.invariant index with
      | .function _ => False
      | .predicate predicate => predicate.holds object) ↔
      (match (highPackageFromLowData.{u} input).reading.invariantReading.invariant
          (generatedDomainInvariantIndexLift.{u} input index) with
        | .function _ => False
        | .predicate predicate =>
            predicate.holds (finiteModelLiftArchitectureObject.{u} object)) := by
  rfl

/-- Canonically lift a signature axis of the selected finite-model target. -/
def targetSignatureAxisLift
    (axis : FiniteModel.corePackage.reading.signatureReading.Axis) :
    finiteModelLiftCorePackage.{u}.reading.signatureReading.Axis :=
  ULift.up axis

/-- Canonically lift a signature axis of the low inverse-generated domain. -/
def generatedDomainSignatureAxisLift
    (input : FiniteGeneratedLiftInput)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis) :
    (highPackageFromLowData.{u} input).reading.signatureReading.Axis :=
  ULift.up axis

/-- The generated upper axis maps commute with canonical lifting. -/
theorem generatedUpper_axisMap_graph
    (input : FiniteGeneratedLiftInput)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis) :
    (highPackageHomFromLowData.{u} input).upper.axisMap
        (generatedDomainSignatureAxisLift.{u} input axis) =
      targetSignatureAxisLift.{u}
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).axisMap axis) := by
  rfl

/-- Selected-axis status is preserved and reflected on generated domain axes. -/
theorem inverseGeneratedDomain_axis_selected_iff
    (input : FiniteGeneratedLiftInput)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis) :
    (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.selected axis ↔
      (highPackageFromLowData.{u} input).reading.signatureReading.selected
        (generatedDomainSignatureAxisLift.{u} input axis) := by
  rfl

/-- Lift a coordinate value on the selected finite-model target signature. -/
def targetSignatureCoordinateLift
    (axis : FiniteModel.corePackage.reading.signatureReading.Axis)
    (coordinate : FiniteModel.corePackage.reading.signatureReading.Coordinate
      axis) :
    finiteModelLiftCorePackage.{u}.reading.signatureReading.Coordinate
      (targetSignatureAxisLift.{u} axis) :=
  ULift.up coordinate

/-- Lift a coordinate value on the low inverse-generated domain signature. -/
def generatedDomainSignatureCoordinateLift
    (input : FiniteGeneratedLiftInput)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis)
    (coordinate : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Coordinate axis) :
    (highPackageFromLowData.{u} input).reading.signatureReading.Coordinate
      (generatedDomainSignatureAxisLift.{u} input axis) :=
  ULift.up coordinate

/-- The generated upper coordinate equivalences commute pointwise with lifting. -/
theorem generatedUpper_coordinateEquiv_graph
    (input : FiniteGeneratedLiftInput)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis)
    (coordinate : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Coordinate axis) :
    (highPackageHomFromLowData.{u} input).upper.coordinateEquiv
        (generatedDomainSignatureAxisLift.{u} input axis)
        (generatedDomainSignatureCoordinateLift.{u} input axis coordinate) =
      targetSignatureCoordinateLift.{u}
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).axisMap axis)
        ((inverseCorePackageForwardUpper FiniteModel.corePackage
          input.hom).coordinateEquiv axis coordinate) := by
  rfl

/-- Signature coordinate reads commute on generated domain objects and axes. -/
theorem inverseGeneratedDomain_coordinate_graph
    (input : FiniteGeneratedLiftInput)
    (object : ArchitectureObject FiniteModel.carrier)
    (axis : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.signatureReading.Axis) :
    (highPackageFromLowData.{u} input).reading.signatureReading.coordinate
        (finiteModelLiftArchitectureObject.{u} object)
        (generatedDomainSignatureAxisLift.{u} input axis) =
      ULift.up
        ((inverseCorePackage FiniteModel.corePackage
          input.hom).reading.signatureReading.coordinate object axis) := by
  rfl

/-! ## Operation observations -/

/--
Lift an operation of the low inverse-generated domain to the high
inverse-generated domain.  Its endpoint casts are generated from the proved
object-map graph; no operation or endpoint comparison is accepted as input.
-/
noncomputable def generatedDomainOperationLift
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.operationReading.Op source target) :
    (highPackageFromLowData.{u} input).reading.operationReading.Op
      (finiteModelLiftArchitectureObject.{u} source)
      (finiteModelLiftArchitectureObject.{u} target) := by
  change ConfigurationHom
    ((input.highPackageHomFromLowData.upper.objectMap
      (finiteModelLiftArchitectureObject.{u} source)).configuration)
    ((input.highPackageHomFromLowData.upper.objectMap
      (finiteModelLiftArchitectureObject.{u} target)).configuration)
  exact castConfigurationHom
    (input.highPackageHomFromLowData_upper_configurationMap_target source).symm
    (input.highPackageHomFromLowData_upper_configurationMap_target target).symm
    (finiteModelLiftConfigurationHom.{u}
      ((inverseCorePackageForwardUpper FiniteModel.corePackage
        input.hom).operationMap operation))

/-- The generated upper operation maps commute with the canonical operation lift. -/
theorem generatedUpper_operationMap_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.operationReading.Op source target) :
    input.highPackageHomFromLowData.upper.operationMap
        (generatedDomainOperationLift.{u} input operation) =
      castConfigurationHom
        (input.highPackageHomFromLowData_upper_configurationMap_target source).symm
        (input.highPackageHomFromLowData_upper_configurationMap_target target).symm
        (finiteModelLiftConfigurationHom.{u}
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).operationMap operation)) := by
  rfl

/--
The configuration map read from a generated high operation is exactly the
endpoint-cast lift of the configuration map read from the generated low
operation.
-/
theorem generatedUpper_operation_configurationMap_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.operationReading.Op source target) :
    finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
        (input.highPackageHomFromLowData.upper.operationMap
          (generatedDomainOperationLift.{u} input operation)) =
      castConfigurationHom
        (input.highPackageHomFromLowData_upper_configurationMap_target source).symm
        (input.highPackageHomFromLowData_upper_configurationMap_target target).symm
        (finiteModelLiftConfigurationHom.{u}
          (FiniteModel.corePackage.reading.operationReading.configurationMap
            ((inverseCorePackageForwardUpper FiniteModel.corePackage
              input.hom).operationMap operation))) := by
  rfl

/-- The generated operation graph has the exact pointwise lifted Atom map. -/
@[simp]
theorem generatedUpper_operation_atomMap_graph
    (input : FiniteGeneratedLiftInput)
    {source target : ArchitectureObject FiniteModel.carrier}
    (operation : (inverseCorePackage FiniteModel.corePackage
      input.hom).reading.operationReading.Op source target)
    (atom : FiniteModel.carrier.Atom) :
    (finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
      (input.highPackageHomFromLowData.upper.operationMap
        (generatedDomainOperationLift.{u} input operation))).atomMap
        (finiteModelLiftCarrierEquiv.{u}.atom atom) =
      finiteModelLiftCarrierEquiv.{u}.atom
        ((FiniteModel.corePackage.reading.operationReading.configurationMap
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).operationMap operation)).atomMap atom) := by
  rw [input.generatedUpper_operation_configurationMap_graph operation,
    castConfigurationHom_atomMap, finiteModelLiftConfigurationHom_atomMap]
  rfl

/-- Every generated low lift projects to the original base arrow. -/
theorem lowGeneratedLift_base (input : FiniteGeneratedLiftInput) :
    (input.lowGeneratedLift).hom.base = input.hom := by
  simp [lowGeneratedLift, strongCartesianLiftOfTarget, lowTarget, lowInput,
    inverseCorePackageHom]

/-- Every generated high lift projects to the canonically lifted base arrow. -/
theorem highGeneratedLift_base (input : FiniteGeneratedLiftInput) :
    input.highGeneratedLift.hom.base =
      finiteModelLiftExtInstHom.{u} input.hom := by
  simp [highGeneratedLift, strongCartesianLiftOfTarget, highTarget, highInput,
    inverseCorePackageHom]

/-- The domain package of the generated low lift lies over the original source. -/
theorem lowGeneratedLift_domain_point (input : FiniteGeneratedLiftInput) :
    packagePoint input.lowGeneratedLift.domain = input.source := by
  letI := input.lowGeneratedLift.isStronglyCartesian
  exact CategoryTheory.IsHomLift.domain_eq
    (packageProjection FiniteModel.carrier) input.lowInput.hom
      input.lowGeneratedLift.hom

/-- The domain package of the generated high lift lies over the lifted source. -/
theorem highGeneratedLift_domain_point (input : FiniteGeneratedLiftInput) :
    packagePoint input.highGeneratedLift.domain =
      finiteModelLiftExtractionInstance.{u} input.source := by
  letI := input.highGeneratedLift.isStronglyCartesian
  exact CategoryTheory.IsHomLift.domain_eq
    (packageProjection finiteModelLiftCarrier.{u}) input.highInput.hom
      input.highGeneratedLift.hom

/-! ## Normalization of an arbitrary high lift -/

/--
Normalize a supplied high strong lift to the generated high domain by first
following the inverse canonical domain comparison and then the supplied lift.
-/
noncomputable def normalizedHighHom (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    input.highGeneratedLift.domain ⟶ finiteModelLiftCorePackage.{u} :=
  (StrongCartesianLift.canonicalDomainIso lift).inv ≫ lift.hom

/--
The inverse comparison triangle identifies the normalized supplied lift with
the generated high lift.
-/
theorem normalizedHighHom_eq_highGeneratedLift
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    input.normalizedHighHom lift = input.highGeneratedLift.hom := by
  exact StrongCartesianLift.domainIso_inv_fac input.highGeneratedLift lift

/--
After identifying the generated domain with the named low-data construction,
normalization of the supplied lift is the named generated total hom.
-/
theorem normalizedHighHom_eq_highPackageHomFromLowData
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    input.normalizedHighHom lift = input.highPackageHomFromLowData := by
  calc
    input.normalizedHighHom lift = input.highGeneratedLift.hom :=
      input.normalizedHighHom_eq_highGeneratedLift lift
    _ = input.highPackageHomFromLowData :=
      input.highGeneratedLift_hom_eq_highPackageHomFromLowData

/-- The normalized hom has the same lower component as the generated high lift. -/
theorem normalizedHighHom_base (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    (input.normalizedHighHom lift).base =
      finiteModelLiftExtInstHom.{u} input.hom := by
  rw [input.normalizedHighHom_eq_highGeneratedLift lift]
  exact input.highGeneratedLift_base

/-- The package projection sends the normalized high hom to the lifted base arrow. -/
theorem normalizedHighHom_projection (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    (packageProjection finiteModelLiftCarrier.{u}).map
        (input.normalizedHighHom lift) = input.highInput.hom := by
  exact input.normalizedHighHom_base lift

/-- The normalized hom has exactly the generated high upper component. -/
theorem normalizedHighHom_upper (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget) :
    (input.normalizedHighHom lift).upper = input.highGeneratedLift.hom.upper := by
  exact congrArg PackageTotalHom.upper
    (input.normalizedHighHom_eq_highGeneratedLift lift)

end FiniteGeneratedLiftInput

/-! ## Generated observational naturality packet -/

/--
Proof-only observational naturality for the package hom generated from one
finite-model lower arrow.

Every object, hom, index lift, operation lift, and endpoint equality occurring
below is a named construction from `input`.  This record is not a
cross-carrier equality of `AATCorePackage`, `PackageTotalHom`, or
`EquationSystemExactTransport`, and it does not assert a functor or a
full/faithful embedding between the two package categories.
-/
structure GeneratedPackageHomULiftNaturality
    (input : FiniteGeneratedLiftInput) : Prop where
  /-- The generated high lift uses the independently named high package. -/
  high_domain :
    input.highGeneratedLift.domain = input.highPackageFromLowData
  /-- The generated high lift uses the independently named high total hom. -/
  high_hom :
    input.highGeneratedLift.hom = input.highPackageHomFromLowData
  /-- The independently named high package lies over the lifted source. -/
  domain_point :
    packagePoint input.highPackageFromLowData = input.highInput.source
  /-- The selected finite target point is the canonical lift of the base point. -/
  target_point :
    finiteModelLiftExtractionInstance.{u}
        (packagePoint FiniteModel.corePackage) =
      packagePoint finiteModelLiftCorePackage.{u}
  /-- The named high lower component is the lift of the generated low component. -/
  base :
    input.highPackageHomFromLowData.base =
      finiteModelLiftExtInstHom.{u} input.lowGeneratedLift.hom.base
  /-- The named high hom projects to the canonically lifted input arrow. -/
  projection :
    (packageProjection finiteModelLiftCarrier.{u}).map
        input.highPackageHomFromLowData = input.highInput.hom
  /-- The upper Atom maps commute pointwise with the carrier lift. -/
  upper_atom :
    ∀ atom : FiniteModel.carrier.Atom,
      input.highPackageHomFromLowData.upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (input.lowGeneratedLift.hom.upper.atomEquiv atom)
  /-- The upper object maps commute on canonically lifted objects. -/
  upper_object :
    ∀ object : ArchitectureObject FiniteModel.carrier,
      input.highPackageHomFromLowData.upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u}
          (input.lowGeneratedLift.hom.upper.objectMap object)
  /-- The upper configuration maps commute after generated endpoint casts. -/
  upper_configurationMap :
    ∀ object : ArchitectureObject FiniteModel.carrier,
      input.highPackageHomFromLowData.upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} object) =
        castConfigurationHom rfl
          (input.highPackageHomFromLowData_upper_configurationMap_target
            object).symm
          (finiteModelLiftConfigurationHom.{u}
            (input.lowGeneratedLift.hom.upper.configurationMap object))
  /-- The upper equation-index maps commute with the generated index lift. -/
  upper_equationMap :
    ∀ index : (inverseCorePackage FiniteModel.corePackage
        input.hom).algebra.equationSystem.Index,
      input.highPackageHomFromLowData.upper.equationMap
          (input.generatedDomainEquationIndexLift index) =
        FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).equationMap index)
  /-- Detector syntax on the generated domains commutes with canonical lifting. -/
  domain_detectorCode :
    ∀ index : (inverseCorePackage FiniteModel.corePackage
        input.hom).algebra.equationSystem.Index,
      input.highPackageFromLowData.algebra.circuits.code
          (input.generatedDomainEquationIndexLift index) =
        finiteModelLiftCircuitDetectorCode.{u}
          ((inverseCorePackage FiniteModel.corePackage
            input.hom).algebra.circuits.code index)
  /-- Equation semantics is preserved and reflected on lifted domain objects. -/
  domain_equationHolds :
    ∀ (index : (inverseCorePackage FiniteModel.corePackage
        input.hom).algebra.equationSystem.Index)
      (object : ArchitectureObject FiniteModel.carrier),
      (inverseCorePackage FiniteModel.corePackage
          input.hom).algebra.equationSystem.EquationHolds index object ↔
        input.highPackageFromLowData.algebra.equationSystem.EquationHolds
          (input.generatedDomainEquationIndexLift index)
          (finiteModelLiftArchitectureObject.{u} object)
  /-- Generated operation configuration maps commute after endpoint casts. -/
  upper_operation :
    ∀ {source target : ArchitectureObject FiniteModel.carrier}
      (operation : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.operationReading.Op source target),
      finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
          (input.highPackageHomFromLowData.upper.operationMap
            (input.generatedDomainOperationLift operation)) =
        castConfigurationHom
          (input.highPackageHomFromLowData_upper_configurationMap_target
            source).symm
          (input.highPackageHomFromLowData_upper_configurationMap_target
            target).symm
          (finiteModelLiftConfigurationHom.{u}
            (FiniteModel.corePackage.reading.operationReading.configurationMap
              ((inverseCorePackageForwardUpper FiniteModel.corePackage
                input.hom).operationMap operation)))
  /-- The generated upper invariant-index maps commute with lifting. -/
  upper_invariantMap :
    ∀ index : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.invariantReading.Index,
      input.highPackageHomFromLowData.upper.invariantMap
          (input.generatedDomainInvariantIndexLift index) =
        FiniteGeneratedLiftInput.targetInvariantIndexLift.{u}
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).invariantMap index)
  /-- Generated singleton invariant semantics agrees on lifted objects. -/
  domain_invariant :
    ∀ (index : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.invariantReading.Index)
      (object : ArchitectureObject FiniteModel.carrier),
      (match (inverseCorePackage FiniteModel.corePackage
          input.hom).reading.invariantReading.invariant index with
        | .function _ => False
        | .predicate predicate => predicate.holds object) ↔
        (match input.highPackageFromLowData.reading.invariantReading.invariant
            (input.generatedDomainInvariantIndexLift index) with
          | .function _ => False
          | .predicate predicate =>
              predicate.holds (finiteModelLiftArchitectureObject.{u} object))
  /-- The generated upper signature-axis maps commute with lifting. -/
  upper_axisMap :
    ∀ axis : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.Axis,
      input.highPackageHomFromLowData.upper.axisMap
          (input.generatedDomainSignatureAxisLift axis) =
        FiniteGeneratedLiftInput.targetSignatureAxisLift.{u}
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).axisMap axis)
  /-- Selected-axis status is preserved and reflected on generated axes. -/
  domain_axis_selected :
    ∀ axis : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.Axis,
      (inverseCorePackage FiniteModel.corePackage
          input.hom).reading.signatureReading.selected axis ↔
        input.highPackageFromLowData.reading.signatureReading.selected
          (input.generatedDomainSignatureAxisLift axis)
  /-- The generated upper coordinate equivalences commute pointwise. -/
  upper_coordinateEquiv :
    ∀ (axis : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.Axis)
      (coordinate : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.Coordinate axis),
      input.highPackageHomFromLowData.upper.coordinateEquiv
          (input.generatedDomainSignatureAxisLift axis)
          (input.generatedDomainSignatureCoordinateLift axis coordinate) =
        FiniteGeneratedLiftInput.targetSignatureCoordinateLift.{u}
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).axisMap axis)
          ((inverseCorePackageForwardUpper FiniteModel.corePackage
            input.hom).coordinateEquiv axis coordinate)
  /-- Generated domain signature coordinates commute on lifted objects. -/
  domain_coordinate :
    ∀ (object : ArchitectureObject FiniteModel.carrier)
      (axis : (inverseCorePackage FiniteModel.corePackage
        input.hom).reading.signatureReading.Axis),
      input.highPackageFromLowData.reading.signatureReading.coordinate
          (finiteModelLiftArchitectureObject.{u} object)
          (input.generatedDomainSignatureAxisLift axis) =
        ULift.up
          ((inverseCorePackage FiniteModel.corePackage
            input.hom).reading.signatureReading.coordinate object axis)
  /-- Every ambient high lift normalizes to the same named generated high hom. -/
  normalized :
    ∀ lift : StrongCartesianLift input.highInput input.highTarget,
      input.normalizedHighHom lift = input.highPackageHomFromLowData

/--
Exact component contract for the next normalized-hom reflection step.

The reflected low hom and the supplied ambient high lift are explicit indices,
while every comparison inside the structure is a proposition about named
generated data.  A future producer must return this structure; it must not
accept a value of it from the caller.  This signature does not itself prove
reflection or strong cartesianness of the reflected hom.
-/
structure ReflectedGeneratedComponentGraph
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget)
    (reflected : input.lowGeneratedLift.domain ⟶ FiniteModel.corePackage) :
    Prop where
  /-- The supplied high lift is normalized by the canonical inverse triangle. -/
  normalized :
    input.normalizedHighHom lift = input.highPackageHomFromLowData
  /-- The exact generated observational packet is produced internally. -/
  generated_naturality :
    GeneratedPackageHomULiftNaturality.{u} input
  /-- The reflected hom lies over the original low semantic arrow. -/
  reflected_base :
    reflected.base = input.hom
  /-- The normalized high lower component is the lift of the reflected one. -/
  normalized_base :
    (input.normalizedHighHom lift).base =
      finiteModelLiftExtInstHom.{u} reflected.base
  /-- The reflected low source package lies over the original source instance. -/
  low_domain_point :
    packagePoint input.lowGeneratedLift.domain = input.lowInput.source
  /-- The normalized high source package lies over the lifted source instance. -/
  high_domain_point :
    packagePoint input.highGeneratedLift.domain = input.highInput.source
  /-- The low target point lifts to the selected high target point. -/
  target_point :
    finiteModelLiftExtractionInstance.{u}
        (packagePoint FiniteModel.corePackage) =
      packagePoint finiteModelLiftCorePackage.{u}
  /-- Package projection sends the normalized high hom to the lifted bottom arrow. -/
  normalized_projection :
    (packageProjection finiteModelLiftCarrier.{u}).map
        (input.normalizedHighHom lift) = input.highInput.hom
  /-- The normalized and reflected upper Atom maps commute pointwise. -/
  upper_atom :
    ∀ atom : FiniteModel.carrier.Atom,
      (input.normalizedHighHom lift).upper.atomEquiv
          (finiteModelLiftCarrierEquiv.{u}.atom atom) =
        finiteModelLiftCarrierEquiv.{u}.atom
          (reflected.upper.atomEquiv atom)
  /-- The normalized and reflected object maps commute on lifted objects. -/
  upper_object :
    ∀ object : ArchitectureObject FiniteModel.carrier,
      (input.normalizedHighHom lift).upper.objectMap
          (finiteModelLiftArchitectureObject.{u} object) =
        finiteModelLiftArchitectureObject.{u}
          (reflected.upper.objectMap object)
  /-- The normalized configuration maps commute after the generated object cast. -/
  upper_configurationMap :
    ∀ object : ArchitectureObject FiniteModel.carrier,
      (input.normalizedHighHom lift).upper.configurationMap
          (finiteModelLiftArchitectureObject.{u} object) =
        castConfigurationHom rfl
          (congrArg ArchitectureObject.configuration
            (upper_object object)).symm
          (finiteModelLiftConfigurationHom.{u}
            (reflected.upper.configurationMap object))
  /-- The normalized and reflected equation maps commute with the generated lift. -/
  upper_equationMap :
    ∀ index : input.lowGeneratedLift.domain.algebra.equationSystem.Index,
      (input.normalizedHighHom lift).upper.equationMap
          (input.generatedDomainEquationIndexLift index) =
        FiniteGeneratedLiftInput.targetEquationIndexLift.{u}
          (reflected.upper.equationMap index)
  /-- Detector syntax on the reflected low and normalized high domains agrees. -/
  domain_detectorCode :
    ∀ index : input.lowGeneratedLift.domain.algebra.equationSystem.Index,
      input.highGeneratedLift.domain.algebra.circuits.code
          (input.generatedDomainEquationIndexLift index) =
        finiteModelLiftCircuitDetectorCode.{u}
          (input.lowGeneratedLift.domain.algebra.circuits.code index)
  /-- Equation semantics agrees on every reflected low object and its lift. -/
  domain_equationHolds :
    ∀ (index : input.lowGeneratedLift.domain.algebra.equationSystem.Index)
      (object : ArchitectureObject FiniteModel.carrier),
      input.lowGeneratedLift.domain.algebra.equationSystem.EquationHolds
          index object ↔
        input.highGeneratedLift.domain.algebra.equationSystem.EquationHolds
          (input.generatedDomainEquationIndexLift index)
          (finiteModelLiftArchitectureObject.{u} object)
  /-- Normalized and reflected operation reads commute after generated endpoint casts. -/
  upper_operation :
    ∀ {source target : ArchitectureObject FiniteModel.carrier}
      (operation : input.lowGeneratedLift.domain.reading.operationReading.Op
        source target),
      finiteModelLiftCorePackage.{u}.reading.operationReading.configurationMap
          ((input.normalizedHighHom lift).upper.operationMap
            (input.generatedDomainOperationLift operation)) =
        castConfigurationHom
          (congrArg ArchitectureObject.configuration
            (upper_object source)).symm
          (congrArg ArchitectureObject.configuration
            (upper_object target)).symm
          (finiteModelLiftConfigurationHom.{u}
            (FiniteModel.corePackage.reading.operationReading.configurationMap
              (reflected.upper.operationMap operation)))
  /-- The normalized and reflected invariant maps commute on generated indices. -/
  upper_invariantMap :
    ∀ index : input.lowGeneratedLift.domain.reading.invariantReading.Index,
      (input.normalizedHighHom lift).upper.invariantMap
          (input.generatedDomainInvariantIndexLift index) =
        FiniteGeneratedLiftInput.targetInvariantIndexLift.{u}
          (reflected.upper.invariantMap index)
  /-- Generated domain invariant truth agrees on lifted objects. -/
  domain_invariant :
    ∀ (index : input.lowGeneratedLift.domain.reading.invariantReading.Index)
      (object : ArchitectureObject FiniteModel.carrier),
      (match input.lowGeneratedLift.domain.reading.invariantReading.invariant
          index with
        | .function _ => False
        | .predicate predicate => predicate.holds object) ↔
        (match input.highGeneratedLift.domain.reading.invariantReading.invariant
            (input.generatedDomainInvariantIndexLift index) with
          | .function _ => False
          | .predicate predicate =>
              predicate.holds (finiteModelLiftArchitectureObject.{u} object))
  /-- The normalized and reflected signature-axis maps commute. -/
  upper_axisMap :
    ∀ axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis,
      (input.normalizedHighHom lift).upper.axisMap
          (input.generatedDomainSignatureAxisLift axis) =
        FiniteGeneratedLiftInput.targetSignatureAxisLift.{u}
          (reflected.upper.axisMap axis)
  /-- Generated domain selected-axis status is preserved and reflected. -/
  domain_axis_selected :
    ∀ axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis,
      input.lowGeneratedLift.domain.reading.signatureReading.selected axis ↔
        input.highGeneratedLift.domain.reading.signatureReading.selected
          (input.generatedDomainSignatureAxisLift axis)
  /-- The normalized and reflected coordinate equivalences commute pointwise. -/
  upper_coordinateEquiv :
    ∀ (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis)
      (coordinate :
        input.lowGeneratedLift.domain.reading.signatureReading.Coordinate axis),
      (input.normalizedHighHom lift).upper.coordinateEquiv
          (input.generatedDomainSignatureAxisLift axis)
          (input.generatedDomainSignatureCoordinateLift axis coordinate) =
        FiniteGeneratedLiftInput.targetSignatureCoordinateLift.{u}
          (reflected.upper.axisMap axis)
          (reflected.upper.coordinateEquiv axis coordinate)
  /-- Generated domain coordinate values agree on lifted objects and axes. -/
  domain_coordinate :
    ∀ (object : ArchitectureObject FiniteModel.carrier)
      (axis : input.lowGeneratedLift.domain.reading.signatureReading.Axis),
      input.highGeneratedLift.domain.reading.signatureReading.coordinate
          (finiteModelLiftArchitectureObject.{u} object)
          (input.generatedDomainSignatureAxisLift axis) =
        ULift.up
          (input.lowGeneratedLift.domain.reading.signatureReading.coordinate
            object axis)

/--
Exact theorem-output surface for the ambient universal property that the next
reflection step must generate.  The factor function is output data indexed by
every ambient low competitor; neither it nor any of its laws may be supplied
to the future producer by a caller.  This structure fixes the full Mathlib
factorization and uniqueness quantifiers, while proof-use of the supplied high
lift remains an extrinsic acceptance obligation because proof irrelevance
cannot encode that provenance in the result type.
-/
structure ReflectedGeneratedUniversalProperty
    (input : FiniteGeneratedLiftInput)
    (lift : StrongCartesianLift input.highInput input.highTarget)
    (reflected : input.lowGeneratedLift.domain ⟶ FiniteModel.corePackage) :
    Type (u + 2) where
  /-- All generated cross-carrier component graphs for the reflected hom. -/
  components : ReflectedGeneratedComponentGraph input lift reflected
  /-- Generated factor for every ambient low universal-property problem. -/
  factor : ∀ {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom],
    package ⟶ input.lowGeneratedLift.domain
  /-- Every generated factor lies over the requested low base arrow. -/
  factor_isHomLift : ∀ {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom],
    (packageProjection FiniteModel.carrier).IsHomLift base (factor base hom)
  /-- Every generated factor followed by the reflected hom is the competitor. -/
  factor_fac : ∀ {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom],
    factor base hom ≫ reflected = hom
  /-- The generated factor is unique among every ambient low factor. -/
  factor_unique : ∀ {package : AATCorePackage FiniteModel.carrier}
    (base : packagePoint package ⟶ input.lowInput.source)
    (hom : package ⟶ FiniteModel.corePackage)
    [(packageProjection FiniteModel.carrier).IsHomLift
      (base ≫ input.lowInput.hom) hom]
    (candidate : package ⟶ input.lowGeneratedLift.domain)
    [(packageProjection FiniteModel.carrier).IsHomLift base candidate],
    candidate ≫ reflected = hom → candidate = factor base hom

/--
Generate the complete observational naturality packet from the finite lower
arrow.  No proof field or comparison object is accepted from the caller.
-/
theorem generatedPackageHomULiftNaturality
    (input : FiniteGeneratedLiftInput) :
    GeneratedPackageHomULiftNaturality.{u} input where
  high_domain := input.highGeneratedLift_domain_eq_highPackageFromLowData
  high_hom := input.highGeneratedLift_hom_eq_highPackageHomFromLowData
  domain_point := input.highPackageFromLowData_point
  target_point := finiteModelLiftPackagePoint
  base := by
    rw [input.highPackageHomFromLowData_base, input.lowGeneratedLift_base]
  projection := input.highPackageHomFromLowData_projection
  upper_atom := by
    intro atom
    rw [input.highPackageHomFromLowData_upper_atom_graph,
      input.lowGeneratedLift_upper_atomEquiv]
  upper_object := input.highPackageHomFromLowData_upper_objectMap_lift
  upper_configurationMap :=
    input.highPackageHomFromLowData_upper_configurationMap_lift
  upper_equationMap := input.generatedUpper_equationMap_graph
  domain_detectorCode := input.inverseGeneratedDomain_detectorCode_graph
  domain_equationHolds := input.inverseGeneratedDomain_equationHolds_iff
  upper_operation := input.generatedUpper_operation_configurationMap_graph
  upper_invariantMap := input.generatedUpper_invariantMap_graph
  domain_invariant :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_invariant_holds_iff.{u} input
  upper_axisMap := input.generatedUpper_axisMap_graph
  domain_axis_selected :=
    FiniteGeneratedLiftInput.inverseGeneratedDomain_axis_selected_iff.{u} input
  upper_coordinateEquiv := input.generatedUpper_coordinateEquiv_graph
  domain_coordinate := input.inverseGeneratedDomain_coordinate_graph
  normalized := input.normalizedHighHom_eq_highPackageHomFromLowData

/-! ## Generated package-hom identity and composition coherence -/

/--
A two-arrow chain ending at one selected target package.  The chain contains
only pointed-doctrine data; every package, lift, comparison isomorphism, and
factorization equation below is generated from these four fields.
-/
structure GeneratedLiftChain {U : AtomCarrier.{u}}
    (targetPackage : AATCorePackage U) where
  /-- Source pointed instance of the first arrow. -/
  source : ExtractionInstance U
  /-- Shared middle pointed instance. -/
  middle : ExtractionInstance U
  /-- First arrow of the chain. -/
  first : source ⟶ middle
  /-- Second arrow, ending at the point selected by the fixed package. -/
  second : middle ⟶ packagePoint targetPackage

namespace GeneratedLiftChain

/-- Semantic input for the second arrow of a generated chain. -/
noncomputable def tailInput {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) : CartSemanticInput U where
  source := chain.middle
  target := packagePoint Q
  hom := chain.second

/-- The selected target package for the second arrow. -/
noncomputable def tailTarget {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) : CoreFiber chain.tailInput.target :=
  ⟨Q, rfl⟩

/-- The generated lift of the second arrow. -/
noncomputable def tailLift {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    StrongCartesianLift chain.tailInput chain.tailTarget :=
  strongCartesianLiftOfTarget chain.tailInput chain.tailTarget

/-- Semantic input for the direct composite arrow. -/
noncomputable def compositeInput {U : AtomCarrier.{u}}
    {Q : AATCorePackage U} (chain : GeneratedLiftChain Q) :
    CartSemanticInput U where
  source := chain.source
  target := packagePoint Q
  hom := chain.first ≫ chain.second

/-- The selected target package for the direct composite arrow. -/
noncomputable def compositeTarget {U : AtomCarrier.{u}}
    {Q : AATCorePackage U} (chain : GeneratedLiftChain Q) :
    CoreFiber chain.compositeInput.target :=
  ⟨Q, rfl⟩

/-- The lift generated directly from the composite bottom arrow. -/
noncomputable def directLift {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    StrongCartesianLift chain.compositeInput chain.compositeTarget :=
  strongCartesianLiftOfTarget chain.compositeInput chain.compositeTarget

/-- The generated tail lift lies over the chain's middle pointed instance. -/
theorem tailLift_domain_point {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    packagePoint chain.tailLift.domain = chain.middle := by
  letI := chain.tailLift.isStronglyCartesian
  exact CategoryTheory.IsHomLift.domain_eq
    (packageProjection U) chain.tailInput.hom chain.tailLift.hom

/-- Semantic input for lifting the first arrow to the generated tail domain. -/
noncomputable def headInput {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) : CartSemanticInput U where
  source := chain.source
  target := packagePoint chain.tailLift.domain
  hom := chain.first ≫ eqToHom chain.tailLift_domain_point.symm

/-- The generated tail domain as target of the first-arrow lift. -/
noncomputable def headTarget {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) : CoreFiber chain.headInput.target :=
  ⟨chain.tailLift.domain, rfl⟩

/-- The generated lift of the first arrow to the generated tail domain. -/
noncomputable def headLift {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    StrongCartesianLift chain.headInput chain.headTarget :=
  strongCartesianLiftOfTarget chain.headInput chain.headTarget

/--
The staged composite of the two generated package homs.  Its universal
property is the actual Mathlib composition of the two strong-cartesian
properties, not a separately supplied certificate.
-/
noncomputable def stagedLift {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    StrongCartesianLift chain.compositeInput chain.compositeTarget where
  domain := chain.headLift.domain
  hom := chain.headLift.hom ≫ chain.tailLift.hom
  isStronglyCartesian := by
    letI := chain.headLift.isStronglyCartesian
    letI := chain.tailLift.isStronglyCartesian
    simpa [headInput, compositeInput, tailInput] using
      CategoryTheory.Functor.IsStronglyCartesian.comp
        (packageProjection U)
        (f := chain.headInput.hom) (g := chain.tailInput.hom)
        (φ := chain.headLift.hom) (ψ := chain.tailLift.hom)

/-- Canonical vertical compositor from the staged domain to the direct domain. -/
noncomputable def compIso {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    chain.stagedLift.domain ≅ chain.directLift.domain :=
  StrongCartesianLift.domainIso chain.directLift chain.stagedLift

/--
The canonical compositor identifies direct and staged generated package homs.
Strict equality is neither needed nor claimed because their domains differ.
-/
theorem compIso_fac {U : AtomCarrier.{u}} {Q : AATCorePackage U}
    (chain : GeneratedLiftChain Q) :
    chain.compIso.hom ≫ chain.directLift.hom = chain.stagedLift.hom :=
  StrongCartesianLift.domainIso_hom_fac _ _

/-- The generated lift of the literal identity bottom arrow. -/
noncomputable def identityGeneratedLift {U : AtomCarrier.{u}}
    (Q : AATCorePackage U) :
    StrongCartesianLift (packageIdentitySemanticInput Q)
      (packageIdentityTarget Q) :=
  strongCartesianLiftOfTarget (packageIdentitySemanticInput Q)
    (packageIdentityTarget Q)

/-- Canonical vertical unitor from the generated identity domain to the package. -/
noncomputable def unitIso {U : AtomCarrier.{u}} (Q : AATCorePackage U) :
    (identityGeneratedLift Q).domain ≅ Q :=
  StrongCartesianLift.domainIso
    (packageIdentityStrongCartesianLift Q) (identityGeneratedLift Q)

/-- The canonical unitor identifies the generated and literal identity homs. -/
theorem unitIso_fac {U : AtomCarrier.{u}} (Q : AATCorePackage U) :
    (unitIso Q).hom ≫ 𝟙 Q = (identityGeneratedLift Q).hom :=
  StrongCartesianLift.domainIso_hom_fac _ _

end GeneratedLiftChain

/-- Two finite-model pointed arrows ending at the selected finite package. -/
abbrev FiniteSelectedGeneratedChain :=
  GeneratedLiftChain FiniteModel.corePackage

namespace FiniteSelectedGeneratedChain

/-- Lift both lower arrows of a selected finite chain through the canonical carrier lift. -/
def lift (chain : FiniteSelectedGeneratedChain) :
    GeneratedLiftChain finiteModelLiftCorePackage.{u} where
  source := finiteModelLiftExtractionInstance.{u} chain.source
  middle := finiteModelLiftExtractionInstance.{u} chain.middle
  first := finiteModelLiftExtInstHom.{u} chain.first
  second := finiteModelLiftExtInstHom.{u} chain.second

/-- Repackage the direct composite as the finite generated-input surface. -/
def compositeGeneratedInput (chain : FiniteSelectedGeneratedChain) :
    FiniteGeneratedLiftInput where
  source := chain.source
  hom := chain.first ≫ chain.second

/-- Repackage the tail arrow as the finite generated-input surface. -/
def tailGeneratedInput (chain : FiniteSelectedGeneratedChain) :
    FiniteGeneratedLiftInput where
  source := chain.middle
  hom := chain.second

/-- The high chain composite is the canonical lift of the low composite arrow. -/
theorem lift_composite_base (chain : FiniteSelectedGeneratedChain) :
    chain.lift.compositeInput.hom =
      finiteModelLiftExtInstHom.{u} chain.compositeGeneratedInput.hom := by
  exact (finiteModelLiftExtInstHom_comp chain.first chain.second).symm

end FiniteSelectedGeneratedChain

/-- The literal identity arrow as a finite generated-input value. -/
noncomputable def finiteIdentityGeneratedInput : FiniteGeneratedLiftInput where
  source := packagePoint FiniteModel.corePackage
  hom := 𝟙 (packagePoint FiniteModel.corePackage)

/-- The high arrow generated from the finite identity is the literal high identity. -/
theorem finiteIdentityGeneratedInput_high_base :
    finiteIdentityGeneratedInput.highInput.hom =
      𝟙 (packagePoint finiteModelLiftCorePackage.{u}) := by
  exact finiteModelLiftExtInstHom_id (packagePoint FiniteModel.corePackage)

/--
The generated-package unit/compositor contract at the selected finite target.
It quantifies every two-arrow finite chain and generates all packages, lifts,
vertical isomorphisms, and observational packets internally.  It is not a
functor on arbitrary packages at either carrier.
-/
structure GeneratedPackageHomULiftCoherence : Prop where
  /-- Low generated identity is the literal package identity up to the canonical unitor. -/
  low_unit :
    (GeneratedLiftChain.unitIso FiniteModel.corePackage).hom ≫
        𝟙 FiniteModel.corePackage =
      (GeneratedLiftChain.identityGeneratedLift FiniteModel.corePackage).hom
  /-- High generated identity is the literal package identity up to the canonical unitor. -/
  high_unit :
    (GeneratedLiftChain.unitIso finiteModelLiftCorePackage.{u}).hom ≫
        𝟙 finiteModelLiftCorePackage.{u} =
      (GeneratedLiftChain.identityGeneratedLift
        finiteModelLiftCorePackage.{u}).hom
  /-- The high unit bottom arrow is the canonical lift of the low identity. -/
  high_unit_base :
    finiteIdentityGeneratedInput.highInput.hom =
      𝟙 (packagePoint finiteModelLiftCorePackage.{u})
  /-- Every low direct composite agrees with staged package-hom composition up to canonical iso. -/
  low_comp : ∀ chain : FiniteSelectedGeneratedChain,
    chain.compIso.hom ≫ chain.directLift.hom = chain.stagedLift.hom
  /-- Every lifted direct composite agrees with staged package-hom composition up to canonical iso. -/
  high_comp : ∀ chain : FiniteSelectedGeneratedChain,
    (chain.lift.compIso).hom ≫ (chain.lift.directLift).hom =
      (chain.lift.stagedLift).hom
  /-- High direct-composite bases are canonical lifts of low composites. -/
  high_comp_base : ∀ chain : FiniteSelectedGeneratedChain,
    chain.lift.compositeInput.hom =
      finiteModelLiftExtInstHom.{u} chain.compositeGeneratedInput.hom
  /-- Identity-arrow low/high observations are generated without caller fields. -/
  identity_naturality :
    GeneratedPackageHomULiftNaturality.{u} finiteIdentityGeneratedInput
  /-- Composite-arrow low/high observations are generated without caller fields. -/
  composite_naturality : ∀ chain : FiniteSelectedGeneratedChain,
    GeneratedPackageHomULiftNaturality.{u} chain.compositeGeneratedInput
  /-- Tail-arrow low/high observations are generated without caller fields. -/
  tail_naturality : ∀ chain : FiniteSelectedGeneratedChain,
    GeneratedPackageHomULiftNaturality.{u} chain.tailGeneratedInput

/-- Generate the complete selected-target unit/compositor coherence packet. -/
theorem generatedPackageHomULiftCoherence :
    GeneratedPackageHomULiftCoherence.{u} where
  low_unit := GeneratedLiftChain.unitIso_fac FiniteModel.corePackage
  high_unit := GeneratedLiftChain.unitIso_fac finiteModelLiftCorePackage.{u}
  high_unit_base := finiteIdentityGeneratedInput_high_base
  low_comp := GeneratedLiftChain.compIso_fac
  high_comp := fun chain => GeneratedLiftChain.compIso_fac chain.lift
  high_comp_base := FiniteSelectedGeneratedChain.lift_composite_base
  identity_naturality :=
    generatedPackageHomULiftNaturality finiteIdentityGeneratedInput
  composite_naturality := fun chain =>
    generatedPackageHomULiftNaturality chain.compositeGeneratedInput
  tail_naturality := fun chain =>
    generatedPackageHomULiftNaturality chain.tailGeneratedInput

/-! ## A noninvertible generated input from the finite portfolio -/

local instance finiteGeneratedLiftAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/--
The exact pointed bridge from the portfolio's finite-code support endpoint
back to the point selected by `FiniteModel.corePackage`.
-/
def finitePortfolioSupportToCoreHom :
    finitePortfolioSupportInstance.toSemantic ⟶
      packagePoint FiniteModel.corePackage where
  doctrineHom := finiteModelDoctrineToFixture
  source_eq := finiteModelSourceEquiv_one

/--
Compose the two-source portfolio arrow, its endpoint bridge, and the exact
finite-code-to-fixture comparison to obtain an arrow to the selected target.
-/
def finiteSelectiveTwoToCoreHom :
    finiteSelectiveTwoInput.semantic.source ⟶
      packagePoint FiniteModel.corePackage :=
  finiteSelectiveTwoInput.semantic.hom ≫
    finiteSelectiveOneToSupportInput.semantic.hom ≫
      finitePortfolioSupportToCoreHom

/--
The concrete two-source portfolio as a genuine two-arrow selected-target
chain.  Its first arrow is already noninvertible; no package, lift, or
coherence comparison is supplied as input.
-/
def finiteSelectiveTwoGeneratedChain : FiniteSelectedGeneratedChain where
  source := finiteSelectiveTwoInput.semantic.source
  middle := finiteSelectiveTwoInput.semantic.target
  first := finiteSelectiveTwoInput.semantic.hom
  second := finiteSelectiveOneToSupportInput.semantic.hom ≫
    finitePortfolioSupportToCoreHom

/-- The concrete chain's first arrow is genuinely noninvertible. -/
theorem finiteSelectiveTwoGeneratedChain_first_not_isIso :
    ¬ IsIso finiteSelectiveTwoGeneratedChain.first :=
  finiteSelectiveTwoInput_not_isIso

/-- The direct composite of the concrete chain is the previously named portfolio arrow. -/
theorem finiteSelectiveTwoGeneratedChain_composite_hom :
    finiteSelectiveTwoGeneratedChain.first ≫
        finiteSelectiveTwoGeneratedChain.second =
      finiteSelectiveTwoToCoreHom := by
  simp [finiteSelectiveTwoGeneratedChain, finiteSelectiveTwoToCoreHom]

/-- The composed portfolio arrow supplies a concrete generated-lift input. -/
def finiteSelectiveTwoGeneratedLiftInput : FiniteGeneratedLiftInput where
  source := finiteSelectiveTwoInput.semantic.source
  hom := finiteSelectiveTwoToCoreHom

/-- The concrete arrow to the selected package point still collapses two source cells. -/
theorem finiteSelectiveTwoToCore_sourceMap_not_injective :
    ¬ Function.Injective
      finiteSelectiveTwoToCoreHom.doctrineHom.sourceMap := by
  intro hinjective
  apply finiteSelectiveTwoSourceMap_not_injective
  intro first second heq
  apply hinjective
  change
    finitePortfolioSupportToCoreHom.doctrineHom.sourceMap
        (finiteSelectiveOneToSupportInput.semantic.hom.doctrineHom.sourceMap
          (finiteSelectiveTwoInput.semantic.hom.doctrineHom.sourceMap first)) =
      finitePortfolioSupportToCoreHom.doctrineHom.sourceMap
        (finiteSelectiveOneToSupportInput.semantic.hom.doctrineHom.sourceMap
          (finiteSelectiveTwoInput.semantic.hom.doctrineHom.sourceMap second))
  exact congrArg
    (fun source =>
      finitePortfolioSupportToCoreHom.doctrineHom.sourceMap
        (finiteSelectiveOneToSupportInput.semantic.hom.doctrineHom.sourceMap source))
    heq

/-- The concrete generated-lift input has a genuinely noninvertible lower arrow. -/
theorem finiteSelectiveTwoToCoreHom_not_isIso :
    ¬ IsIso finiteSelectiveTwoToCoreHom := by
  intro hiso
  letI : IsIso finiteSelectiveTwoToCoreHom := hiso
  exact finiteSelectiveTwoToCore_sourceMap_not_injective
    (extInstHom_sourceMap_injective_of_isIso finiteSelectiveTwoToCoreHom)

/-- The concrete chain's direct composite remains genuinely noninvertible. -/
theorem finiteSelectiveTwoGeneratedChain_composite_not_isIso :
    ¬ IsIso
      (finiteSelectiveTwoGeneratedChain.first ≫
        finiteSelectiveTwoGeneratedChain.second) := by
  rw [finiteSelectiveTwoGeneratedChain_composite_hom]
  exact finiteSelectiveTwoToCoreHom_not_isIso

/-- The generated compositor laws fire on the noninvertible chain in both carriers. -/
theorem finiteSelectiveTwoGeneratedChain_composition_coherence :
    (finiteSelectiveTwoGeneratedChain.compIso.hom ≫
        finiteSelectiveTwoGeneratedChain.directLift.hom =
      finiteSelectiveTwoGeneratedChain.stagedLift.hom) ∧
    (((FiniteSelectedGeneratedChain.lift.{u}
        finiteSelectiveTwoGeneratedChain).compIso).hom ≫
        (FiniteSelectedGeneratedChain.lift.{u}
          finiteSelectiveTwoGeneratedChain).directLift.hom =
      (FiniteSelectedGeneratedChain.lift.{u}
        finiteSelectiveTwoGeneratedChain).stagedLift.hom) := by
  exact ⟨GeneratedLiftChain.compIso_fac _,
    GeneratedLiftChain.compIso_fac _⟩

/--
The noninvertible two-source portfolio input carries the generated
observational naturality packet at every target universe.
-/
theorem finiteSelectiveTwoGeneratedPackageHomULiftNaturality :
    GeneratedPackageHomULiftNaturality.{u}
      finiteSelectiveTwoGeneratedLiftInput :=
  generatedPackageHomULiftNaturality finiteSelectiveTwoGeneratedLiftInput

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
