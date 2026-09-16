import ResearchLean.AG.RealizationReconstruction.CSAATLawTransport
import Formal.Util.AssertStandardAxioms

/-!
# Object, context, and residual transport for the CS law systems

Cycle 127 transports law indices and polynomial coordinates.  This module
adds the actual endpoint architecture objects, a heterogeneous map between
their canonical full-family contexts, and residual-level preservation.  A
raw morphism need not be injective, so the correct forward condition is that
vanishing source residuals have vanishing target residuals.  The corresponding
conditional residual square is proved from the raw operation squares rather
than accepted as a certificate.

Unconditional equality of the characteristic `0/1` residuals is deliberately
not used: a fixed noninjective lens example below maps a nonzero source
residual to a zero target residual.  This refutes that candidate square only;
it does not restrict the arbitrary semantic morphisms in the forward API.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Heterogeneous canonical-context maps -/

/-- Component data between contexts over possibly different architecture
objects.  It is heterogeneous because the existing `Site.ContextMorphism` is
intentionally homogeneous over one fixed object. -/
structure HeterogeneousContextMap {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (source : Site.ArchitectureContext sourceObject)
    (target : Site.ArchitectureContext targetObject) where
  supportMap : source.Support → target.Support
  axisMap : source.Axis → target.Axis
  observableRestrict : target.Observable → source.Observable

/-- Identity heterogeneous context component. -/
def HeterogeneousContextMap.id {U : AtomCarrier.{u}}
    {object : ArchitectureObject U} (context : Site.ArchitectureContext object) :
    HeterogeneousContextMap context context where
  supportMap value := value
  axisMap value := value
  observableRestrict value := value

/-- Composition of heterogeneous context components. -/
def HeterogeneousContextMap.comp {U : AtomCarrier.{u}}
    {firstObject secondObject thirdObject : ArchitectureObject U}
    {first : Site.ArchitectureContext firstObject}
    {second : Site.ArchitectureContext secondObject}
    {third : Site.ArchitectureContext thirdObject}
    (f : HeterogeneousContextMap first second)
    (g : HeterogeneousContextMap second third) :
    HeterogeneousContextMap first third where
  supportMap := g.supportMap ∘ f.supportMap
  axisMap := g.axisMap ∘ f.axisMap
  observableRestrict := f.observableRestrict ∘ g.observableRestrict

/-- Rebase a context on a target object whose family contains the complete
vocabulary, retaining every support, axis, observable, predicate, and
extension rather than selecting only the canonical unit context. -/
def fullFamilyContextRebase {U : AtomCarrier.{u}}
    {sourceObject : ArchitectureObject U} (targetObject : ArchitectureObject U)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (W : Site.ArchitectureContext sourceObject) :
    Site.ArchitectureContext targetObject where
  minimal := {
    Support := W.Support
    Axis := W.Axis
    Observable := W.Observable
    supportReads := W.minimal.supportReads
    supportReads_objectFamily := fun {_ atom} _ => target_all atom
    axisReads := W.minimal.axisReads
    observableReads := W.minimal.observableReads }
  Extension := W.Extension
  extension := W.extension

/-- Rebase the data of a context morphism between full-family objects. -/
def fullFamilyContextMorphismRebase {U : AtomCarrier.{u}}
    {sourceObject : ArchitectureObject U} (targetObject : ArchitectureObject U)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ArchitectureContext sourceObject}
    (f : Site.ContextMorphism W V) :
    Site.ContextMorphism (fullFamilyContextRebase targetObject target_all W)
      (fullFamilyContextRebase targetObject target_all V) where
  supportMap := f.supportMap
  axisMap := f.axisMap
  observableRestrict := f.observableRestrict

/-- A selected restriction remains a restriction after full-family rebasing. -/
theorem fullFamilyContextMorphismRebase_isRestriction
    {U : AtomCarrier.{u}} {sourceObject : ArchitectureObject U}
    (targetObject : ArchitectureObject U)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ArchitectureContext sourceObject}
    (f : Site.ContextMorphism W V) (hf : f.IsRestriction) :
    (fullFamilyContextMorphismRebase targetObject target_all f).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hf.1
  · exact hf.2.1
  · exact hf.2.2.1
  · intro support atom _
    exact target_all atom

/-- Every full-family endpoint receives the complete source context category;
the functor copies all context data and all selected restriction maps. -/
noncomputable def fullFamilyContextFunctor {U : AtomCarrier.{u}}
    (sourceObject targetObject : ArchitectureObject U)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom) :
    Site.ContextCategoryObject (Site.contextMorphismPreorderCategory sourceObject) ⥤
      Site.ContextCategoryObject (Site.contextMorphismPreorderCategory targetObject) where
  obj W := ⟨fullFamilyContextRebase targetObject target_all W.ctx⟩
  map := by
    intro W V h
    let relation := leOfHom h
    let f := Classical.choose relation
    have hf := Classical.choose_spec relation
    exact homOfLE ⟨fullFamilyContextMorphismRebase targetObject target_all f,
      fullFamilyContextMorphismRebase_isRestriction targetObject target_all f hf⟩
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The actual source object of a raw lens-law morphism. -/
def lensLawSourceObject {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target}
    (_f : LensLawHom source target) :
    ArchitectureObject (lensAATCarrier input) :=
  lensLawObject input Source source

/-- The actual target object of a raw lens-law morphism. -/
def lensLawTargetObject {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target}
    (_f : LensLawHom source target) :
    ArchitectureObject (lensAATCarrier input) :=
  lensLawObject input Target target

/-- The fixed Atom configuration is transported by the identity map; state
transport remains the independent `f.toFun` component. -/
def lensLawConfigurationMap {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    ConfigurationHom (lensLawSourceObject f).configuration
      (lensLawTargetObject f).configuration :=
  ConfigurationHom.id _

/-- Canonical full-family source context for a raw lens-law morphism. -/
def lensLawSourceContext {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    Site.ArchitectureContext (lensLawSourceObject f) :=
  fullFamilyUnitContext _ (fun _ => trivial)

/-- Canonical full-family target context for a raw lens-law morphism. -/
def lensLawTargetContext {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    Site.ArchitectureContext (lensLawTargetObject f) :=
  fullFamilyUnitContext _ (fun _ => trivial)

/-- The canonical lens contexts are connected by their actual unit support,
axis, and observable components. -/
def lensLawContextMap {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    HeterogeneousContextMap (lensLawSourceContext f) (lensLawTargetContext f) where
  supportMap value := value
  axisMap value := value
  observableRestrict value := value

/-- All lens contexts, not only the canonical unit context, are carried to the
actual target Law object without inspecting or shrinking their readings. -/
noncomputable def lensLawContextFunctor {Source Target : Type u}
    {input : LensFamilyInput.{u}}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory (lensLawSourceObject f)) ⥤
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory (lensLawTargetObject f)) :=
  fullFamilyContextFunctor _ _ (fun _ => trivial)

/-- The actual source object of a raw protocol-law morphism. -/
def protocolLawSourceObject {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (_a : ProtocolLawHom source target) :
    ArchitectureObject (protocolAATCarrier input) :=
  protocolLawObject input Source source

/-- The actual target object of a raw protocol-law morphism. -/
def protocolLawTargetObject {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (_a : ProtocolLawHom source target) :
    ArchitectureObject (protocolAATCarrier input) :=
  protocolLawObject input Target target

/-- Protocol Law objects retain the full fixed operation-name vocabulary. -/
def protocolLawConfigurationMap {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    ConfigurationHom (protocolLawSourceObject a).configuration
      (protocolLawTargetObject a).configuration :=
  ConfigurationHom.id _

/-- Canonical full-family source context for a protocol-law morphism. -/
def protocolLawSourceContext {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    Site.ArchitectureContext (protocolLawSourceObject a) :=
  fullFamilyUnitContext _ (fun _ => trivial)

/-- Canonical full-family target context for a protocol-law morphism. -/
def protocolLawTargetContext {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    Site.ArchitectureContext (protocolLawTargetObject a) :=
  fullFamilyUnitContext _ (fun _ => trivial)

/-- The canonical protocol contexts are connected without identifying their
dependent state carriers. -/
def protocolLawContextMap {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    HeterogeneousContextMap (protocolLawSourceContext a)
      (protocolLawTargetContext a) where
  supportMap value := value
  axisMap value := value
  observableRestrict value := value

/-- Every protocol context and selected restriction map is copied to the
actual target Law object while retaining all dependent operation names. -/
noncomputable def protocolLawContextFunctor {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory (protocolLawSourceObject a)) ⥤
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory (protocolLawTargetObject a)) :=
  fullFamilyContextFunctor _ _ (fun _ => trivial)

/-! ## Residual-zero transport -/

/-- Lens violation coordinates commute with the actual all-context functor and
the Cycle 127 coordinate-ring homomorphism. -/
theorem lensLawViolationCoordinate_map (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Source source)))
    (index : LensLawIndex input.View Source) (atom : LensAATAtom input) :
    lensLawCoordinateMap input f
        ((lensLawEquationSystem input Source source).violationCoordinate W
          (ULift.up index) atom) =
      (lensLawEquationSystem input Target target).violationCoordinate
        ((lensLawContextFunctor f).obj W)
        (ULift.up (lensLawIndexMap f index)) atom := by
  exact lensLawCoordinateMap_violation input f index atom

/-- Lens coordinate transport commutes with every selected context
restriction copied by the all-context functor. -/
theorem lensLawCoordinateMap_restrict (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Source source))}
    (contextMap : W ⟶ V) (polynomial : LensLawCoordinateRing input Source) :
    lensLawCoordinateMap input f
        ((lensLawEquationSystem input Source source).restrict contextMap polynomial) =
      (lensLawEquationSystem input Target target).restrict
        ((lensLawContextFunctor f).map contextMap)
        (lensLawCoordinateMap input f polynomial) := by
  rfl

/-- At every actual context and Atom, a lens residual vanishes exactly when
its stored raw equation holds. -/
theorem lensLawResidual_zero_iff (input : LensFamilyInput.{u})
    (Carrier : Type u) (base data : LensLawStructure input.View Carrier)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Carrier base)))
    (index : LensLawIndex input.View Carrier) (atom : LensAATAtom input) :
    (lensLawEquationSystem input Carrier base).equationResidual W
        (lensLawObject input Carrier data) (ULift.up index) atom = 0 ↔
      index.Holds data := by
  classical
  by_cases h : index.Holds data <;> simp [lensLawEquationSystem, h]

/-- Raw lens squares transport residual vanishing between independently
chosen actual contexts. -/
theorem lensLawResidual_zero_map (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Source source)))
    (targetContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Target target)))
    (index : LensLawIndex input.View Source) (atom : LensAATAtom input)
    (hzero : (lensLawEquationSystem input Source source).equationResidual
      sourceContext (lensLawObject input Source source) (ULift.up index) atom = 0) :
    (lensLawEquationSystem input Target target).equationResidual targetContext
      (lensLawObject input Target target) (ULift.up (lensLawIndexMap f index)) atom = 0 := by
  apply (lensLawResidual_zero_iff input Target target target targetContext
    (lensLawIndexMap f index) atom).mpr
  exact lensLawIndexMap_holds f index
    ((lensLawResidual_zero_iff input Source source source sourceContext index atom).mp hzero)

/-- Residual vanishing is preserved at the context selected by the actual
all-context functor. -/
theorem lensLawResidual_zero_map_contextFunctor (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Source source)))
    (index : LensLawIndex input.View Source) (atom : LensAATAtom input)
    (hzero : (lensLawEquationSystem input Source source).equationResidual
      sourceContext (lensLawObject input Source source) (ULift.up index) atom = 0) :
    (lensLawEquationSystem input Target target).equationResidual
      ((lensLawContextFunctor f).obj sourceContext)
      (lensLawObject input Target target) (ULift.up (lensLawIndexMap f index)) atom = 0 :=
  lensLawResidual_zero_map input f sourceContext
    ((lensLawContextFunctor f).obj sourceContext) index atom hzero

/-- On the source zero locus, the coordinate map and target residual form the
actual forward residual square. -/
theorem lensLawResidual_commutes_of_zero (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Source source)))
    (targetContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input Target target)))
    (index : LensLawIndex input.View Source) (atom : LensAATAtom input)
    (hzero : (lensLawEquationSystem input Source source).equationResidual
      sourceContext (lensLawObject input Source source) (ULift.up index) atom = 0) :
    lensLawCoordinateMap input f
        ((lensLawEquationSystem input Source source).equationResidual sourceContext
          (lensLawObject input Source source) (ULift.up index) atom) =
      (lensLawEquationSystem input Target target).equationResidual targetContext
        (lensLawObject input Target target)
        (ULift.up (lensLawIndexMap f index)) atom := by
  rw [hzero, map_zero, lensLawResidual_zero_map input f sourceContext targetContext
    index atom hzero]

/-- Lens residual-zero transport composes in the same order as raw morphisms. -/
theorem lensLawResidual_zero_map_comp (input : LensFamilyInput.{u})
    {A B C : Type u} {first : LensLawStructure input.View A}
    {second : LensLawStructure input.View B} {third : LensLawStructure input.View C}
    (f : LensLawHom first second) (g : LensLawHom second third)
    (firstContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input A first)))
    (secondContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input B second)))
    (thirdContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (lensLawObject input C third)))
    (index : LensLawIndex input.View A) (atom : LensAATAtom input)
    (hzero : (lensLawEquationSystem input A first).equationResidual firstContext
      (lensLawObject input A first) (ULift.up index) atom = 0) :
    (lensLawEquationSystem input C third).equationResidual thirdContext
      (lensLawObject input C third)
      (ULift.up (lensLawIndexMap (LensLawHom.comp f g) index)) atom = 0 := by
  rw [lensLawIndexMap_comp]
  exact lensLawResidual_zero_map input g secondContext thirdContext _ atom
    (lensLawResidual_zero_map input f firstContext secondContext index atom hzero)

/-- At every actual context and Atom, a protocol residual vanishes exactly
when its raw relation or observation equation holds. -/
theorem protocolLawResidual_zero_iff (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (base data : ProtocolLawStructure input State)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input State base)))
    (index : ProtocolLawIndex State) (atom : ProtocolAATAtom input) :
    (protocolLawEquationSystem input State base).equationResidual W
        (protocolLawObject input State data) (ULift.up index) atom = 0 ↔
      index.Holds data := by
  classical
  by_cases h : index.Holds data <;> simp [protocolLawEquationSystem, h]

/-- Protocol violation coordinates commute with all-context transport. -/
theorem protocolLawViolationCoordinate_map (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (W : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Source source)))
    (index : ProtocolLawIndex Source) (atom : ProtocolAATAtom input) :
    protocolLawCoordinateMap input a
        ((protocolLawEquationSystem input Source source).violationCoordinate W
          (ULift.up index) atom) =
      (protocolLawEquationSystem input Target target).violationCoordinate
        ((protocolLawContextFunctor a).obj W)
        (ULift.up (protocolLawIndexMap a index)) atom := by
  exact protocolLawCoordinateMap_violation input a index atom

/-- Protocol coordinate transport commutes with every copied restriction. -/
theorem protocolLawCoordinateMap_restrict (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Source source))}
    (contextMap : W ⟶ V) (polynomial : ProtocolLawCoordinateRing input Source) :
    protocolLawCoordinateMap input a
        ((protocolLawEquationSystem input Source source).restrict contextMap polynomial) =
      (protocolLawEquationSystem input Target target).restrict
        ((protocolLawContextFunctor a).map contextMap)
        (protocolLawCoordinateMap input a polynomial) := by
  rfl

/-- Raw protocol squares transport residual vanishing at every actual context. -/
theorem protocolLawResidual_zero_map (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Source source)))
    (targetContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Target target)))
    (index : ProtocolLawIndex Source) (atom : ProtocolAATAtom input)
    (hzero : (protocolLawEquationSystem input Source source).equationResidual
      sourceContext (protocolLawObject input Source source) (ULift.up index) atom = 0) :
    (protocolLawEquationSystem input Target target).equationResidual targetContext
      (protocolLawObject input Target target)
      (ULift.up (protocolLawIndexMap a index)) atom = 0 := by
  apply (protocolLawResidual_zero_iff input Target target target targetContext
    (protocolLawIndexMap a index) atom).mpr
  exact protocolLawIndexMap_holds a index
    ((protocolLawResidual_zero_iff input Source source source sourceContext index atom).mp hzero)

/-- Protocol residual vanishing is preserved at the functorially transported
actual context. -/
theorem protocolLawResidual_zero_map_contextFunctor
    (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Source source)))
    (index : ProtocolLawIndex Source) (atom : ProtocolAATAtom input)
    (hzero : (protocolLawEquationSystem input Source source).equationResidual
      sourceContext (protocolLawObject input Source source) (ULift.up index) atom = 0) :
    (protocolLawEquationSystem input Target target).equationResidual
      ((protocolLawContextFunctor a).obj sourceContext)
      (protocolLawObject input Target target)
      (ULift.up (protocolLawIndexMap a index)) atom = 0 :=
  protocolLawResidual_zero_map input a sourceContext
    ((protocolLawContextFunctor a).obj sourceContext) index atom hzero

/-- The protocol coordinate map commutes with actual residuals on the source
zero locus. -/
theorem protocolLawResidual_commutes_of_zero (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Source source)))
    (targetContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input Target target)))
    (index : ProtocolLawIndex Source) (atom : ProtocolAATAtom input)
    (hzero : (protocolLawEquationSystem input Source source).equationResidual
      sourceContext (protocolLawObject input Source source) (ULift.up index) atom = 0) :
    protocolLawCoordinateMap input a
        ((protocolLawEquationSystem input Source source).equationResidual sourceContext
          (protocolLawObject input Source source) (ULift.up index) atom) =
      (protocolLawEquationSystem input Target target).equationResidual targetContext
        (protocolLawObject input Target target)
        (ULift.up (protocolLawIndexMap a index)) atom := by
  rw [hzero, map_zero, protocolLawResidual_zero_map input a sourceContext targetContext
    index atom hzero]

/-- Protocol residual-zero transport respects raw morphism composition. -/
theorem protocolLawResidual_zero_map_comp (input : ProtocolFamilyInput.{u})
    {A B C : input.schema.Vertex → Type u}
    {first : ProtocolLawStructure input A} {second : ProtocolLawStructure input B}
    {third : ProtocolLawStructure input C}
    (f : ProtocolLawHom first second) (g : ProtocolLawHom second third)
    (firstContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input A first)))
    (secondContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input B second)))
    (thirdContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory (protocolLawObject input C third)))
    (index : ProtocolLawIndex A) (atom : ProtocolAATAtom input)
    (hzero : (protocolLawEquationSystem input A first).equationResidual firstContext
      (protocolLawObject input A first) (ULift.up index) atom = 0) :
    (protocolLawEquationSystem input C third).equationResidual thirdContext
      (protocolLawObject input C third)
      (ULift.up (protocolLawIndexMap (ProtocolLawHom.comp f g) index)) atom = 0 := by
  rw [protocolLawIndexMap_comp]
  exact protocolLawResidual_zero_map input g secondContext thirdContext _ atom
    (protocolLawResidual_zero_map input f firstContext secondContext index atom hzero)

/-! ## Exact residual equality is not the arbitrary-map condition -/

/-- The fixed one-view input for the residual noncommutation witness. -/
def collapsedBoolLensInput : LensFamilyInput where
  View := PUnit
  reference := PUnit.unit

/-- A raw source whose update toggles its Boolean state. -/
def collapsedBoolLensSource : LensLawStructure PUnit Bool where
  get _ := PUnit.unit
  put state _ := !state

/-- The unique raw lens operations on the one-point target. -/
def collapsedBoolLensTarget : LensLawStructure PUnit PUnit where
  get _ := PUnit.unit
  put _ _ := PUnit.unit

/-- The noninjective raw lens morphism collapsing both source states. -/
def collapseBoolLensLawHom : LensLawHom collapsedBoolLensSource collapsedBoolLensTarget where
  toFun _ := PUnit.unit
  get_naturality _ := rfl
  put_naturality _ _ := rfl

/-- The selected source PutGet instance fails. -/
theorem collapsedBoolLensSource_not_putGet :
    ¬ (LensLawIndex.putGet false).Holds collapsedBoolLensSource := by
  simp [LensLawIndex.Holds, collapsedBoolLensSource]

/-- Its mapped one-point target instance holds. -/
theorem collapsedBoolLensTarget_putGet :
    (lensLawIndexMap collapseBoolLensLawHom (LensLawIndex.putGet false)).Holds
      collapsedBoolLensTarget := by
  simp [lensLawIndexMap, LensLawIndex.Holds, collapsedBoolLensTarget,
    collapseBoolLensLawHom]

/-- The actual source context used to evaluate the nonzero residual. -/
def collapsedBoolLensSourceContext : Site.ContextCategoryObject
    (Site.contextMorphismPreorderCategory
      (lensLawObject collapsedBoolLensInput Bool collapsedBoolLensSource)) :=
  ⟨fullFamilyUnitContext _ (fun _ => trivial)⟩

/-- The actual target context used to evaluate the zero residual. -/
def collapsedBoolLensTargetContext : Site.ContextCategoryObject
    (Site.contextMorphismPreorderCategory
      (lensLawObject collapsedBoolLensInput PUnit collapsedBoolLensTarget)) :=
  ⟨fullFamilyUnitContext _ (fun _ => trivial)⟩

/-- The characteristic residual square cannot commute unconditionally for all
arbitrary noninjective raw morphisms. -/
theorem collapseBoolLens_residual_not_commute :
    lensLawCoordinateMap collapsedBoolLensInput collapseBoolLensLawHom
        ((lensLawEquationSystem collapsedBoolLensInput Bool
          collapsedBoolLensSource).equationResidual collapsedBoolLensSourceContext
            (lensLawObject collapsedBoolLensInput Bool collapsedBoolLensSource)
            (ULift.up (LensLawIndex.putGet false)) (.point)) ≠
      (lensLawEquationSystem collapsedBoolLensInput PUnit
        collapsedBoolLensTarget).equationResidual collapsedBoolLensTargetContext
          (lensLawObject collapsedBoolLensInput PUnit collapsedBoolLensTarget)
          (ULift.up (lensLawIndexMap collapseBoolLensLawHom
            (LensLawIndex.putGet false))) (.point) := by
  simp [lensLawCoordinateMap, lensLawEquationSystem, collapsedBoolLensInput,
    collapsedBoolLensSource, collapsedBoolLensTarget, collapseBoolLensLawHom,
    LensLawIndex.Holds, lensLawIndexMap]

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
