import ResearchLean.AG.DoctrineFiberProduct.FiniteArbitraryPackageULift

/-!
# Exact universe-zero arbitrary context rebase

At universe zero the original finite carrier and its canonical `ULift` carrier
have context fields in the same universe.  Hence arbitrary contexts can be
transported in both directions while retaining their four carrier types
literally.  This supplies the exact `u = 0` endpoint omitted by the tagged
successor-universe construction.

The module constructs context objects, raw context morphisms, arbitrary context
preorders and their category equivalence, then transports arbitrary equation
systems, finite detector semantics, and the complete source package reading.
Cross-carrier total-hom graphs, supplied strong-lift reflection, and the named
`FiniteModelLift` corollary remain later obligations.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation

/-! ## Exact architecture-object round trip -/

/-- Rebase an arbitrary architecture object without lifting its auxiliary carriers. -/
def finiteModelZeroLiftArchitectureObject
    (object : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject finiteModelLiftCarrier.{0} where
  configuration := finiteModelLiftAtomConfiguration.{0} object.configuration
  StructureMaps := object.StructureMaps
  SelectedQuantities := object.SelectedQuantities
  structureMaps := object.structureMaps
  selectedQuantities := object.selectedQuantities

/-- Reflect an arbitrary exact-zero lifted architecture object. -/
def finiteModelZeroReflectArchitectureObject
    (object : ArchitectureObject finiteModelLiftCarrier.{0}) :
    ArchitectureObject FiniteModel.carrier where
  configuration := finiteModelReflectAtomConfiguration.{0} object.configuration
  StructureMaps := object.StructureMaps
  SelectedQuantities := object.SelectedQuantities
  structureMaps := object.structureMaps
  selectedQuantities := object.selectedQuantities

/-- Exact-zero architecture-object reflection is a strict left inverse. -/
@[simp]
theorem finiteModelZeroReflectArchitectureObject_lift
    (object : ArchitectureObject FiniteModel.carrier) :
    finiteModelZeroReflectArchitectureObject
        (finiteModelZeroLiftArchitectureObject object) = object := by
  rcases object with
    ⟨configuration, StructureMaps, SelectedQuantities,
      structureMaps, selectedQuantities⟩
  simp [finiteModelZeroReflectArchitectureObject,
    finiteModelZeroLiftArchitectureObject]

/-- Exact-zero architecture-object lifting is a strict right inverse. -/
@[simp]
theorem finiteModelZeroLiftArchitectureObject_reflect
    (object : ArchitectureObject finiteModelLiftCarrier.{0}) :
    finiteModelZeroLiftArchitectureObject
        (finiteModelZeroReflectArchitectureObject object) = object := by
  rcases object with
    ⟨configuration, StructureMaps, SelectedQuantities,
      structureMaps, selectedQuantities⟩
  simp [finiteModelZeroReflectArchitectureObject,
    finiteModelZeroLiftArchitectureObject,
    finiteModelLiftAtomConfiguration_reflect]

/-! ## Exact object reading -/

/-- Lift an arbitrary object reading at the exact universe-zero endpoint. -/
def finiteModelZeroLiftObjectReading
    (reading : ObjectReading FiniteModel.carrier) :
    ObjectReading finiteModelLiftCarrier.{0} where
  object configuration :=
    finiteModelZeroLiftArchitectureObject
      (reading.object (finiteModelReflectAtomConfiguration.{0} configuration))
  configuration_eq configuration := by
    change finiteModelLiftAtomConfiguration.{0}
      (reading.object
        (finiteModelReflectAtomConfiguration.{0} configuration)).configuration =
      configuration
    rw [reading.configuration_eq]
    exact finiteModelLiftAtomConfiguration_reflect.{0} configuration

/-- The exact-zero object reading retains the strict selected-object round trip. -/
@[simp]
theorem finiteModelZeroLiftObjectReading_object_lift
    (reading : ObjectReading FiniteModel.carrier)
    (configuration : AtomConfiguration FiniteModel.carrier) :
    (finiteModelZeroLiftObjectReading reading).object
        (finiteModelLiftAtomConfiguration.{0} configuration) =
      finiteModelZeroLiftArchitectureObject (reading.object configuration) := by
  simp [finiteModelZeroLiftObjectReading]

/-! ## Exact context object round trip -/

/-- Rebase a low context to the exact universe-zero lifted carrier. -/
def finiteModelZeroLiftArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext A) :
    Site.ArchitectureContext (finiteModelZeroLiftArchitectureObject A) where
  minimal := {
    Support := context.Support
    Axis := context.Axis
    Observable := context.Observable
    supportReads := fun support atom =>
      context.minimal.supportReads support
        (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)
    supportReads_objectFamily := by
      intro support atom hread
      simpa [finiteModelZeroLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using
        context.supportReads_objectFamily hread
    axisReads := context.minimal.axisReads
    observableReads := context.minimal.observableReads
  }
  Extension := context.Extension
  extension := context.extension

/-- Reflect an exact universe-zero lifted context to the original carrier. -/
def finiteModelZeroReflectArchitectureContext
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext
      (finiteModelZeroLiftArchitectureObject A)) :
    Site.ArchitectureContext A where
  minimal := {
    Support := context.Support
    Axis := context.Axis
    Observable := context.Observable
    supportReads := fun support atom =>
      context.minimal.supportReads support
        (finiteModelLiftCarrierEquiv.{0}.atom atom)
    supportReads_objectFamily := by
      intro support atom hread
      have lifted := context.supportReads_objectFamily hread
      simpa [finiteModelZeroLiftArchitectureObject,
        finiteModelLiftAtomConfiguration, finiteModelLiftAtomFamily] using lifted
    axisReads := context.minimal.axisReads
    observableReads := context.minimal.observableReads
  }
  Extension := context.Extension
  extension := context.extension

/-- Exact zero reflection is a strict left inverse. -/
@[simp]
theorem finiteModelZeroReflectArchitectureContext_lift
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext A) :
    finiteModelZeroReflectArchitectureContext
        (finiteModelZeroLiftArchitectureContext context) = context := by
  rcases context with
    ⟨⟨Support, Axis, Observable, supportReads, supportFamily,
      axisReads, observableReads⟩, Extension, extension⟩
  simp [finiteModelZeroReflectArchitectureContext,
    finiteModelZeroLiftArchitectureContext]
  exact ⟨rfl, rfl, rfl⟩

/-- Exact zero lifting is a strict right inverse. -/
@[simp]
theorem finiteModelZeroLiftArchitectureContext_reflect
    {A : ArchitectureObject FiniteModel.carrier}
    (context : Site.ArchitectureContext
      (finiteModelZeroLiftArchitectureObject A)) :
    finiteModelZeroLiftArchitectureContext
        (finiteModelZeroReflectArchitectureContext context) = context := by
  rcases context with
    ⟨⟨Support, Axis, Observable, supportReads, supportFamily,
      axisReads, observableReads⟩, Extension, extension⟩
  simp [finiteModelZeroReflectArchitectureContext,
    finiteModelZeroLiftArchitectureContext]
  exact ⟨rfl, rfl, rfl⟩

/-! ## Exact raw context-morphism lift, reflection, and restriction preservation -/

/-- Rebase all three maps of a low raw context morphism at universe zero. -/
def finiteModelZeroLiftContextMorphism
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext A}
    (morphism : Site.ContextMorphism source target) :
    Site.ContextMorphism
      (finiteModelZeroLiftArchitectureContext source)
      (finiteModelZeroLiftArchitectureContext target) where
  supportMap := morphism.supportMap
  axisMap := morphism.axisMap
  observableRestrict := morphism.observableRestrict

/-- Reflect all three maps of an exact zero lifted raw context morphism. -/
def finiteModelZeroReflectContextMorphism
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext
      (finiteModelZeroLiftArchitectureObject A)}
    (morphism : Site.ContextMorphism source target) :
    Site.ContextMorphism
      (finiteModelZeroReflectArchitectureContext source)
      (finiteModelZeroReflectArchitectureContext target) where
  supportMap := morphism.supportMap
  axisMap := morphism.axisMap
  observableRestrict := morphism.observableRestrict

/-- Exact zero raw-morphism lifting preserves restriction. -/
theorem finiteModelZeroLiftContextMorphism_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext A}
    (morphism : Site.ContextMorphism source target)
    (restriction : morphism.IsRestriction) :
    (finiteModelZeroLiftContextMorphism morphism).IsRestriction := by
  rcases restriction with ⟨support, axis, observable, nongenerating⟩
  exact ⟨support, axis, observable, by
    intro selected atom hread
    exact (finiteModelZeroLiftArchitectureContext target).supportReads_objectFamily
      hread⟩

/-- Exact zero raw-morphism reflection preserves restriction. -/
theorem finiteModelZeroReflectContextMorphism_isRestriction
    {A : ArchitectureObject FiniteModel.carrier}
    {source target : Site.ArchitectureContext
      (finiteModelZeroLiftArchitectureObject A)}
    (morphism : Site.ContextMorphism source target)
    (restriction : morphism.IsRestriction) :
    (finiteModelZeroReflectContextMorphism morphism).IsRestriction := by
  rcases restriction with ⟨support, axis, observable, nongenerating⟩
  exact ⟨support, axis, observable, by
    intro selected atom hread
    exact (finiteModelZeroReflectArchitectureContext target).supportReads_objectFamily
      hread⟩

/-! ## Exact arbitrary preorder and category equivalence -/

/-- Rebase an arbitrary low context preorder to the exact zero lifted object. -/
noncomputable def finiteModelZeroLiftContextPreorderAt
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    Site.ContextPreorderCategory
      (finiteModelZeroLiftArchitectureObject A) where
  le source target := preorder.le
    (finiteModelZeroReflectArchitectureContext source)
    (finiteModelZeroReflectArchitectureContext target)
  refl context := preorder.refl _
  trans := fun first second => preorder.trans first second
  readableMorphism := by
    intro source target relation
    exact finiteModelCastContextMorphism
      (finiteModelZeroLiftArchitectureContext_reflect source) rfl
      (finiteModelCastContextMorphism rfl
        (finiteModelZeroLiftArchitectureContext_reflect target).symm
        (finiteModelZeroLiftContextMorphism
          (preorder.readableMorphism relation)))
  readableMorphism_isRestriction := by
    intro source target relation
    exact finiteModelCastContextMorphism_isRestriction
      (finiteModelZeroLiftArchitectureContext_reflect source) rfl
      (finiteModelCastContextMorphism rfl
        (finiteModelZeroLiftArchitectureContext_reflect target).symm
        (finiteModelZeroLiftContextMorphism
          (preorder.readableMorphism relation)))
      (finiteModelCastContextMorphism_isRestriction rfl
        (finiteModelZeroLiftArchitectureContext_reflect target).symm
        (finiteModelZeroLiftContextMorphism
          (preorder.readableMorphism relation))
        (finiteModelZeroLiftContextMorphism_isRestriction
          (preorder.readableMorphism relation)
          (preorder.readableMorphism_isRestriction relation)))

abbrev FiniteModelZeroLowContextObject
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :=
  @Site.ContextCategoryObject FiniteModel.carrier A preorder

abbrev FiniteModelZeroHighContextObject
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :=
  @Site.ContextCategoryObject finiteModelLiftCarrier.{0}
    (finiteModelZeroLiftArchitectureObject A)
    (finiteModelZeroLiftContextPreorderAt preorder)

/-- Exact-zero forward context functor. -/
noncomputable def finiteModelZeroContextFunctor
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelZeroLowContextObject preorder ⥤
      FiniteModelZeroHighContextObject preorder where
  obj context := ⟨finiteModelZeroLiftArchitectureContext context.ctx⟩
  map := by
    intro source target morphism
    apply homOfLE
    simpa [finiteModelZeroLiftContextPreorderAt] using leOfHom morphism
  map_id := by intros; exact Subsingleton.elim _ _
  map_comp := by intros; exact Subsingleton.elim _ _

/-- Exact-zero inverse context functor. -/
noncomputable def finiteModelZeroReflectedContextFunctor
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelZeroHighContextObject preorder ⥤
      FiniteModelZeroLowContextObject preorder where
  obj context := ⟨finiteModelZeroReflectArchitectureContext context.ctx⟩
  map := by
    intro source target morphism
    apply homOfLE
    exact leOfHom morphism
  map_id := by intros; exact Subsingleton.elim _ _
  map_comp := by intros; exact Subsingleton.elim _ _

/-- Exact universe-zero equivalence for every finite-carrier context preorder. -/
noncomputable def finiteModelZeroContextEquivalence
    {A : ArchitectureObject FiniteModel.carrier}
    (preorder : Site.ContextPreorderCategory A) :
    FiniteModelZeroLowContextObject preorder ≌
      FiniteModelZeroHighContextObject preorder where
  functor := finiteModelZeroContextFunctor preorder
  inverse := finiteModelZeroReflectedContextFunctor preorder
  unitIso := NatIso.ofComponents (fun context => eqToIso (by
    rcases context with ⟨context⟩
    simp [finiteModelZeroContextFunctor,
      finiteModelZeroReflectedContextFunctor]))
    (by intros; exact Subsingleton.elim _ _)
  counitIso := NatIso.ofComponents (fun context => eqToIso (by
    rcases context with ⟨context⟩
    simp [finiteModelZeroContextFunctor,
      finiteModelZeroReflectedContextFunctor]))
    (by intros; exact Subsingleton.elim _ _)
  functor_unitIso_comp _ := Subsingleton.elim _ _

/-! ## Exact arbitrary architectural equation system -/

/--
Rebase every field of an arbitrary architectural equation system through the
exact-zero context equivalence.  Observable rings and equation indices retain
their literal low carriers; only contexts, atoms, and architecture objects are
transported.
-/
noncomputable def finiteModelZeroLiftEquationSystem
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (equations : ArchitecturalEquationSystem preorder) :
    ArchitecturalEquationSystem
      (finiteModelZeroLiftContextPreorderAt preorder) where
  Index := equations.Index
  role := equations.role
  Observable context := equations.Observable
    ((finiteModelZeroReflectedContextFunctor preorder).obj context)
  observableCommRing _ := inferInstance
  restrict := by
    intro source target morphism
    exact equations.restrict
      ((finiteModelZeroReflectedContextFunctor preorder).map morphism)
  restrict_id := by
    intro context value
    simpa using equations.restrict_id
      ((finiteModelZeroReflectedContextFunctor preorder).obj context) value
  restrict_comp := by
    intro first second third f g value
    simpa using equations.restrict_comp
      ((finiteModelZeroReflectedContextFunctor preorder).map f)
      ((finiteModelZeroReflectedContextFunctor preorder).map g) value
  violationCoordinate := fun context index atom =>
    equations.violationCoordinate
      ((finiteModelZeroReflectedContextFunctor preorder).obj context)
      index (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)
  violationCoordinate_restrict := by
    intro source target morphism index atom
    simpa using equations.violationCoordinate_restrict
      ((finiteModelZeroReflectedContextFunctor preorder).map morphism)
      index (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)
  equationResidual := fun context object index atom =>
    equations.equationResidual
      ((finiteModelZeroReflectedContextFunctor preorder).obj context)
      (finiteModelZeroReflectArchitectureObject object)
      index (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)
  equationResidual_restrict := by
    intro source target morphism object index atom
    simpa using equations.equationResidual_restrict
      ((finiteModelZeroReflectedContextFunctor preorder).map morphism)
      (finiteModelZeroReflectArchitectureObject object)
      index (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)

/-- Exact-zero equation roles are retained literally. -/
@[simp]
theorem finiteModelZeroLiftEquationSystem_role
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (equations : ArchitecturalEquationSystem preorder)
    (index : equations.Index) :
    (finiteModelZeroLiftEquationSystem equations).role index =
      equations.role index :=
  rfl

/-- Residuals on lifted contexts, objects, and atoms are the original residuals. -/
@[simp]
theorem finiteModelZeroLiftEquationSystem_residual_lift
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (equations : ArchitecturalEquationSystem preorder)
    (context : FiniteModelZeroLowContextObject preorder)
    (object : ArchitectureObject FiniteModel.carrier)
    (index : equations.Index) (atom : FiniteModel.carrier.Atom) :
    (finiteModelZeroLiftEquationSystem equations).equationResidual
        ((finiteModelZeroContextFunctor preorder).obj context)
        (finiteModelZeroLiftArchitectureObject object) index
        (finiteModelLiftCarrierEquiv.{0}.atom atom) =
      equations.equationResidual context object index atom := by
  change equations.equationResidual
      ⟨finiteModelZeroReflectArchitectureContext
        (finiteModelZeroLiftArchitectureContext context.ctx)⟩
      (finiteModelZeroReflectArchitectureObject
        (finiteModelZeroLiftArchitectureObject object)) index atom = _
  have contextEq :
      (⟨finiteModelZeroReflectArchitectureContext
        (finiteModelZeroLiftArchitectureContext context.ctx)⟩ :
        FiniteModelZeroLowContextObject preorder) = context := by
    rcases context with ⟨context⟩
    simp
  simp only [finiteModelZeroReflectArchitectureObject_lift]
  apply eq_of_heq
  cases contextEq
  rfl

/-! ## Exact arbitrary circuit and equation readings -/

/-- A high query reads exactly as its reflected query on the exact-zero object reflection. -/
@[simp]
theorem finiteModelZeroReflectCircuitQuery_holds_iff
    (query : CircuitQuery finiteModelLiftCarrier.{0})
    (object : ArchitectureObject finiteModelLiftCarrier.{0}) :
    query.Holds object ↔
      (finiteModelReflectCircuitQuery.{0} query).Holds
        (finiteModelZeroReflectArchitectureObject object) := by
  cases query <;>
    simp [CircuitQuery.Holds, finiteModelReflectCircuitQuery,
      finiteModelZeroReflectArchitectureObject,
      finiteModelReflectAtomConfiguration, finiteModelReflectAtomFamily]

/-- Signed finite data retain their semantics under exact-zero object reflection. -/
@[simp]
theorem finiteModelZeroReflectFiniteCircuitDatum_matches_iff
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{0})
    (object : ArchitectureObject finiteModelLiftCarrier.{0}) :
    datum.Matches object ↔
      (finiteModelReflectFiniteCircuitDatum.{0} datum).Matches
        (finiteModelZeroReflectArchitectureObject object) := by
  constructor
  · intro hmatches query expected hmem
    have liftedMem :
        (finiteModelLiftCircuitQuery.{0} query, expected) ∈
          (finiteModelLiftFiniteCircuitDatum.{0}
            (finiteModelReflectFiniteCircuitDatum.{0} datum)).queries :=
      List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩
    have liftedMem' :
        (finiteModelLiftCircuitQuery.{0} query, expected) ∈ datum.queries := by
      simpa using liftedMem
    have hmapped := hmatches (finiteModelLiftCircuitQuery.{0} query) expected
      liftedMem'
    simpa using ((finiteModelZeroReflectCircuitQuery_holds_iff
      (finiteModelLiftCircuitQuery.{0} query) object).symm.trans hmapped)
  · intro hmatches query expected hmem
    have hmapped := hmatches (finiteModelReflectCircuitQuery.{0} query) expected
      (List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩)
    exact (finiteModelZeroReflectCircuitQuery_holds_iff query object).trans hmapped

/-- Exact-zero lifting preserves every arbitrary equation-holds predicate. -/
theorem finiteModelZeroLiftEquationSystem_holds_iff
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    (equations : ArchitecturalEquationSystem preorder)
    (index : equations.Index)
    (object : ArchitectureObject finiteModelLiftCarrier.{0}) :
    (finiteModelZeroLiftEquationSystem equations).EquationHolds index object ↔
      equations.EquationHolds index
        (finiteModelZeroReflectArchitectureObject object) := by
  constructor
  · intro hholds context atom
    have lifted := hholds
      ((finiteModelZeroContextFunctor preorder).obj context)
      (finiteModelLiftCarrierEquiv.{0}.atom atom)
    simpa [finiteModelZeroLiftEquationSystem] using lifted
  · intro hholds context atom
    exact hholds
      ((finiteModelZeroReflectedContextFunctor preorder).obj context)
      (finiteModelLiftCarrierEquiv.{0}.atom.symm atom)

/-- Lift an arbitrary detector family by recursively rebasing its finite syntax. -/
noncomputable def finiteModelZeroLiftEquationCircuitReading
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    {equations : ArchitecturalEquationSystem preorder}
    (circuits : EquationCircuitReading equations) :
    EquationCircuitReading (finiteModelZeroLiftEquationSystem equations) where
  code index := finiteModelLiftCircuitDetectorCode.{0} (circuits.code index)

/-- Lifted arbitrary detector evaluation is reflection of target syntax. -/
theorem finiteModelZeroLiftEquationCircuitReading_eval_reflect
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    {equations : ArchitecturalEquationSystem preorder}
    (circuits : EquationCircuitReading equations)
    (index : equations.Index)
    (datum : FiniteCircuitDatum finiteModelLiftCarrier.{0}) :
    ((finiteModelZeroLiftEquationCircuitReading circuits).code index).eval datum =
      (circuits.code index).eval
        (finiteModelReflectFiniteCircuitDatum.{0} datum) := by
  exact finiteModelLiftCircuitDetectorCode_eval_reflect.{0}
    (circuits.code index) datum

/-- Sound arbitrary source detectors remain sound after exact-zero rebasing. -/
theorem finiteModelZeroLiftEquationCircuitReading_sound
    {A : ArchitectureObject FiniteModel.carrier}
    {preorder : Site.ContextPreorderCategory A}
    {equations : ArchitecturalEquationSystem preorder}
    (circuits : EquationCircuitReading equations)
    (sound : circuits.Sound) :
    (finiteModelZeroLiftEquationCircuitReading circuits).Sound := by
  intro index object datum hmatches haccepts
  have reflectedMatches :
      (finiteModelReflectFiniteCircuitDatum.{0} datum).Matches
        (finiteModelZeroReflectArchitectureObject object) :=
    (finiteModelZeroReflectFiniteCircuitDatum_matches_iff datum object).mp hmatches
  have reflectedAccepts :
      (circuits.code index).eval
          (finiteModelReflectFiniteCircuitDatum.{0} datum) = true := by
    rw [← finiteModelZeroLiftEquationCircuitReading_eval_reflect circuits index datum]
    exact haccepts
  exact (finiteModelZeroLiftEquationSystem_holds_iff equations index object).mp.mt
    (sound index _ _ reflectedMatches reflectedAccepts)

/-- Rebase an arbitrary complete equation reading at the exact-zero endpoint. -/
noncomputable def finiteModelZeroLiftEquationReading
    {A : ArchitectureObject FiniteModel.carrier}
    (reading : EquationReading A) :
    EquationReading (finiteModelZeroLiftArchitectureObject A) where
  contextPreorder := finiteModelZeroLiftContextPreorderAt reading.contextPreorder
  equationSystem := finiteModelZeroLiftEquationSystem reading.equationSystem
  circuits := finiteModelZeroLiftEquationCircuitReading reading.circuits
  circuitSound := finiteModelZeroLiftEquationCircuitReading_sound
    reading.circuits reading.circuitSound

/-! ## Exact arbitrary core-package assembly -/

/-- Assemble the exact-zero lift of every reading field of an arbitrary package. -/
noncomputable def finiteModelZeroLiftCoreReading
    (package : AATCorePackage FiniteModel.carrier) :
    CoreReading finiteModelLiftCarrier.{0} where
  doctrine := finiteModelLiftExtractionDoctrine.{0} package.reading.doctrine
  source := ULift.up package.reading.source
  family_listFinite := by
    simpa using finiteModelLiftAtomFamily_listFinite.{0}
      package.reading.family_listFinite
  composition := finiteModelLiftCompositionReading.{0}
    package.reading.composition
  objectReading := finiteModelZeroLiftObjectReading package.reading.objectReading
  equationReading := finiteModelZeroLiftEquationReading
    package.reading.equationReading
  invariantReading := finiteModelLiftInvariantFamilyAt.{0}
    package.reading.objectReading package.reading.invariantReading
  signatureReading := finiteModelLiftArchitectureSignatureAt.{0}
    package.reading.objectReading package.reading.signatureReading
  operationReading := finiteModelLiftOperationReadingAt.{0}
    package.reading.objectReading package.reading.operationReading

/-- Generate the exact-zero target package from transported axioms and readings. -/
noncomputable def finiteModelZeroLiftCorePackage
    (package : AATCorePackage FiniteModel.carrier) :
    AATCorePackage finiteModelLiftCarrier.{0} :=
  AATCorePackage.generate
    (finiteModelLiftAtomAxiomSystem.{0} package.axioms)
    (finiteModelZeroLiftCoreReading package)

/-- Exact-zero package generation retains the transported Atom axioms. -/
@[simp]
theorem finiteModelZeroLiftCorePackage_axioms
    (package : AATCorePackage FiniteModel.carrier) :
    (finiteModelZeroLiftCorePackage package).axioms =
      finiteModelLiftAtomAxiomSystem.{0} package.axioms :=
  rfl

/-- Exact-zero package generation retains the assembled arbitrary reading. -/
@[simp]
theorem finiteModelZeroLiftCorePackage_reading
    (package : AATCorePackage FiniteModel.carrier) :
    (finiteModelZeroLiftCorePackage package).reading =
      finiteModelZeroLiftCoreReading package :=
  rfl

/-- The exact-zero generated object is the direct arbitrary object rebase. -/
theorem finiteModelZeroLiftCorePackage_object
    (package : AATCorePackage FiniteModel.carrier) :
    (finiteModelZeroLiftCorePackage package).object =
      finiteModelZeroLiftArchitectureObject package.object := by
  rfl

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
