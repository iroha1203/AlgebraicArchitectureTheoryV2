import ResearchLean.AG.LocalSemanticReconstruction.ProtocolRestrictionReading
import Formal.Util.AssertStandardAxioms

/-!
# Observation-aware finite protocol restriction models

For a fixed protocol input, an observed restriction model consists of a
`FintypeCat`-valued diagram on every quotient execution together with its
primitive observation map into the parameter-owned observation diagram.
Morphisms are coherent families of finite-state maps satisfying the local
observation square.  Their identities and composites are componentwise.

This choice keeps every state carrier finite without imposing finiteness on
the observation carriers.  The observation map is primitive local data, not
a completed morphism between realizations.  Forgetting it recovers the finite
restriction diagram of `ProtocolRestrictionReading`.

The accepted protocol reading is fully faithful on this local Hom surface:
an observation-compatible local family assembles to the accepted semantic
natural transformation, and reading and assembly are inverse.  Object
assembly and the four-branch local-model equivalence remain separate
obligations.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u v

/-- Forget the finite enumerations in a protocol restriction diagram while
retaining its complete restriction action. -/
noncomputable def protocolFiniteDiagramUnderlying
    (input : ProtocolFamilyInput.{u}) :
    LocalModelCategory (ProtocolRestrictionIndex input) FintypeCat.{u} ⥤
      LocalModelCategory (ProtocolRestrictionIndex input) (Type u) :=
  (Functor.whiskeringRight
      ((ProtocolRestrictionIndex input)ᵒᵖ) FintypeCat.{u} (Type u)).obj
    FintypeCat.incl

/-- The fixed observation functor, transported to the double-opposite domain
of the finite restriction diagrams.  Its carriers remain arbitrary types. -/
def protocolObservationDiagram (input : ProtocolFamilyInput.{u}) :
    LocalModelCategory (ProtocolRestrictionIndex input) (Type u) where
  obj q := input.observation.obj q.unop.unop
  map f := input.observation.map f.unop.unop
  map_id q := input.observation.map_id q.unop.unop
  map_comp f g := input.observation.map_comp f.unop.unop g.unop.unop

/-- A coherent finite-state restriction diagram equipped with its primitive
map to the parameter-owned observation diagram. -/
structure ProtocolObservedRestrictionModel (input : ProtocolFamilyInput.{u}) where
  /-- Finite state at every quotient execution and every restriction map. -/
  stateDiagram :
    LocalModelCategory (ProtocolRestrictionIndex input) FintypeCat.{u}
  /-- Observation of the local states; its target need not be finite. -/
  observe :
    (protocolFiniteDiagramUnderlying input).obj stateDiagram ⟶
      protocolObservationDiagram input

/-- A morphism of observed restriction models is a coherent finite-state
family satisfying the observation square. -/
@[ext]
structure ProtocolObservedRestrictionHom
    {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolObservedRestrictionModel input) where
  /-- The componentwise finite-state map, coherent with every restriction. -/
  stateMap : X.stateDiagram ⟶ Y.stateDiagram
  /-- The state map preserves the parameter-owned observation. -/
  observation_naturality :
    (protocolFiniteDiagramUnderlying input).map stateMap ≫ Y.observe = X.observe

/-- Observed finite restriction models form a category with componentwise
identities and composition. -/
instance protocolObservedRestrictionModelCategory
    (input : ProtocolFamilyInput.{u}) :
    Category (ProtocolObservedRestrictionModel input) where
  Hom := ProtocolObservedRestrictionHom
  id X :=
    { stateMap := 𝟙 X.stateDiagram
      observation_naturality := by simp }
  comp first second :=
    { stateMap := first.stateMap ≫ second.stateMap
      observation_naturality := by
        rw [Functor.map_comp, Category.assoc,
          second.observation_naturality, first.observation_naturality] }
  id_comp f := by
    apply ProtocolObservedRestrictionHom.ext
    exact Category.id_comp f.stateMap
  comp_id f := by
    apply ProtocolObservedRestrictionHom.ext
    exact Category.comp_id f.stateMap
  assoc f g h := by
    apply ProtocolObservedRestrictionHom.ext
    exact Category.assoc f.stateMap g.stateMap h.stateMap

/-- Forgetting observation data and its preservation equation recovers the
underlying finite restriction diagram and natural transformation. -/
def protocolObservedRestrictionForget (input : ProtocolFamilyInput.{u}) :
    ProtocolObservedRestrictionModel input ⥤
      LocalModelCategory (ProtocolRestrictionIndex input) FintypeCat.{u} where
  obj X := X.stateDiagram
  map f := f.stateMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The observation-aware local model read from an accepted protocol
realization. -/
noncomputable def protocolObservedRestrictionObject
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolObservedRestrictionModel input where
  stateDiagram := protocolRestrictionDiagram input X
  observe :=
    { app := fun q ↦ X.observation.app q.unop.unop
      naturality := by
        intro q r f
        exact X.observation.naturality f.unop.unop }

/-- The observation-aware local morphism read from an admitted closed-family
protocol morphism. -/
noncomputable def protocolObservedRestrictionMap
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y) :
    protocolObservedRestrictionObject input X ⟶
      protocolObservedRestrictionObject input Y where
  stateMap := protocolRestrictionMap input f
  observation_naturality := by
    apply NatTrans.ext
    funext q state
    simpa [protocolFiniteDiagramUnderlying,
      protocolObservedRestrictionObject, protocolRestrictionMap] using
      congrFun (NatTrans.congr_app
      f.down.toSemanticHom.observation_naturality q.unop.unop) state

/-- Reading of every accepted protocol realization and morphism into the
observation-aware finite restriction category. -/
noncomputable def protocolObservedRestrictionReading
    (input : ProtocolFamilyInput.{u}) :
    FamilyRealization.{u, v} (.protocol input) ⥤
      ProtocolObservedRestrictionModel input where
  obj X := by
    cases X with
    | protocol realization =>
        exact protocolObservedRestrictionObject input realization
  map {X Y} f := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target =>
          exact protocolObservedRestrictionMap input f
  map_id X := by
    cases X with
    | protocol realization =>
      apply ProtocolObservedRestrictionHom.ext
      apply NatTrans.ext
      funext q
      apply FintypeCat.hom_ext
      intro state
      rfl
  map_comp {X Y Z} f g := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol middle =>
        cases Z with
        | protocol target =>
          apply ProtocolObservedRestrictionHom.ext
          apply NatTrans.ext
          funext q
          apply FintypeCat.hom_ext
          intro state
          rfl

/-- No-unfold compatibility: forgetting observation from an observed object
returns the Cycle 21 finite restriction diagram. -/
@[simp] theorem protocolObservedRestrictionForget_obj
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    (protocolObservedRestrictionForget input).obj
        (protocolObservedRestrictionObject input X) =
      protocolRestrictionDiagram input X :=
  rfl

/-- No-unfold compatibility on morphisms with the Cycle 21 reading. -/
@[simp] theorem protocolObservedRestrictionForget_map
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : FamilyRealization.protocol X ⟶ FamilyRealization.protocol Y) :
    (protocolObservedRestrictionForget input).map
        (protocolObservedRestrictionMap input f) =
      protocolRestrictionMap input f :=
  rfl

/-- Assemble an observation-compatible local morphism into an accepted
closed-family protocol morphism.  The input stores only local components and
their restriction and observation equations. -/
noncomputable def protocolObservedRestrictionAssemble
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : protocolObservedRestrictionObject input X ⟶
      protocolObservedRestrictionObject input Y) :
    (FamilyRealization.protocol X : FamilyRealization (.protocol input)) ⟶
      FamilyRealization.protocol Y :=
  closedFamilyProtocolHom
    { toNatTrans :=
        { app := fun q state ↦
            f.stateMap.app (Opposite.op (Opposite.op q)) state
          naturality := by
            intro q r g
            funext state
            simpa [protocolObservedRestrictionObject,
              protocolRestrictionDiagram] using congrArg
              (fun h :
                (protocolObservedRestrictionObject input X).stateDiagram.obj
                    (Opposite.op (Opposite.op q)) ⟶
                  (protocolObservedRestrictionObject input Y).stateDiagram.obj
                    (Opposite.op (Opposite.op r)) ↦ h state)
              (f.stateMap.naturality g.op.op) }
      observation_naturality := by
        apply NatTrans.ext
        funext q state
        exact congrFun (NatTrans.congr_app f.observation_naturality
          (Opposite.op (Opposite.op q))) state }

/-- Reading an assembled observed local morphism returns that local morphism. -/
@[simp] theorem protocolObservedRestriction_read_assemble
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : protocolObservedRestrictionObject input X ⟶
      protocolObservedRestrictionObject input Y) :
    protocolObservedRestrictionMap input
        (protocolObservedRestrictionAssemble input f) = f := by
  apply ProtocolObservedRestrictionHom.ext
  apply NatTrans.ext
  funext q
  apply FintypeCat.hom_ext
  intro state
  rfl

/-- Assembling the observed reading of an admitted protocol morphism returns
that same admitted morphism. -/
@[simp] theorem protocolObservedRestriction_assemble_read
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : (FamilyRealization.protocol X : FamilyRealization (.protocol input)) ⟶
      FamilyRealization.protocol Y) :
    protocolObservedRestrictionAssemble input
        (protocolObservedRestrictionMap input f) = f := by
  apply ULift.ext
  apply ProtocolAATIndependentGeneratedPackageHom.ext
  funext vertex state
  rfl

/-- The admitted protocol Hom is exactly the coherent observation-preserving
local Hom between the two finite restriction readings. -/
noncomputable def protocolObservedRestrictionHomEquiv
    (input : ProtocolFamilyInput.{u})
    (X Y : ProtocolRealization input.schema input.observation) :
    ((FamilyRealization.protocol X : FamilyRealization (.protocol input)) ⟶
      FamilyRealization.protocol Y) ≃
      (protocolObservedRestrictionObject input X ⟶
        protocolObservedRestrictionObject input Y) where
  toFun := protocolObservedRestrictionMap input
  invFun := protocolObservedRestrictionAssemble input
  left_inv := protocolObservedRestriction_assemble_read input
  right_inv := protocolObservedRestriction_read_assemble input

/-- The observation-aware protocol reading is faithful: coherent local
components distinguish every admitted morphism. -/
noncomputable def protocolObservedRestrictionReadingFaithful
    (input : ProtocolFamilyInput.{u}) :
    (protocolObservedRestrictionReading input).Faithful where
  map_injective := fun {X Y} first second equality => by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target =>
        exact (protocolObservedRestrictionHomEquiv input source target).injective
          equality

/-- The observation-aware protocol reading is full: every coherent local
state family preserving observation assembles to an admitted morphism. -/
noncomputable def protocolObservedRestrictionReadingFull
    (input : ProtocolFamilyInput.{u}) :
    (protocolObservedRestrictionReading input).Full where
  map_surjective := fun {X Y} => by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target =>
        exact (protocolObservedRestrictionHomEquiv input source target).surjective

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
