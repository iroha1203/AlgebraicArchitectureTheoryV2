import ResearchLean.AG.RealizationReconstruction.CSAATArchitectureObjects
import Formal.AG.Equation.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Formal.Util.AssertStandardAxioms

/-!
# CS laws as object-dependent AAT equation systems

This module constructs actual `ArchitecturalEquationSystem` values from the raw
laws of the two independent CS models in G-123(E).  A system fixes only carrier
types and equation syntax.  Its residual reads the operations stored in the
architecture object supplied at evaluation time.  Symbolic coordinates are
distinct multivariate-polynomial variables indexed by the original equation
instance and Atom.

The construction is prior to a complete AAT core or geometry.  It does not
claim Law transport along arbitrary AAT morphisms or an AAT-to-CS readback.

## Implementation notes

The system's `base` object fixes only the context-category type.  Residuals
deliberately inspect the object supplied at evaluation time: closing over the
base operations would make every later object test the same equations.  The
typed `Option` readers reject an incompatible `StructureMaps` carrier by a
nonzero residual instead of accepting a cast-free default.  Raw structures
store operations and observations but never a law certificate.  Finally,
coordinates use one polynomial variable for each equation instance and Atom;
a single coordinate would erase precisely the indexing later transport must
preserve, even though the present characteristic residual is shared across
Atoms for one equation instance.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A concrete context used to read one residual from an object whose complete
fixed Atom vocabulary is selected. -/
def fullFamilyUnitContext {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (all_mem : ∀ atom, A.configuration.family.mem atom) :
    Site.ArchitectureContext A where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => True
    supportReads_objectFamily := fun {_ _} _ => all_mem _
    axisReads := fun _ => True
    observableReads := fun _ => True }
  Extension := PUnit
  extension := PUnit.unit

/-! ## Lens laws -/

/-- Lens operations on fixed carriers, with no law proof or finiteness certificate. -/
structure LensLawStructure (View Carrier : Type u) where
  get : Carrier → View
  put : Carrier → View → Carrier

/-- Forget only the dependent carrier packaging of raw n1015 lens data. -/
def LensData.toLawStructure {View : Type u} (L : LensData View) :
    LensLawStructure View L.Carrier where
  get := L.get
  put := L.put

/-- The three fully quantified n1015 (L1) equation instances on fixed carriers. -/
inductive LensLawIndex (View Carrier : Type u) : Type u
  | putGet (state : Carrier)
  | getPut (state : Carrier) (view : View)
  | putPut (state : Carrier) (first second : View)

/-- Direct meaning of one raw lens-law instance. -/
def LensLawIndex.Holds {View Carrier : Type u}
    (data : LensLawStructure View Carrier) : LensLawIndex View Carrier → Prop
  | .putGet state => data.put state (data.get state) = state
  | .getPut state view => data.get (data.put state view) = view
  | .putPut state first second =>
      data.put (data.put state first) second = data.put state second

/-- An AAT object whose structure-map value is exactly the raw lens operation pair. -/
def lensLawObject (input : LensFamilyInput.{u}) (Carrier : Type u)
    (data : LensLawStructure input.View Carrier) :
    ArchitectureObject (lensAATCarrier input) where
  configuration := typedRoleConfiguration (.point : LensAATAtom input)
  StructureMaps := ULift.{u + 1, u} (LensLawStructure input.View Carrier)
  SelectedQuantities := ULift.{u + 1, u} input.View
  structureMaps := ULift.up data
  selectedQuantities := ULift.up input.reference

/-- Read fixed-carrier lens operations from the evaluated architecture object. -/
noncomputable def lensLawStructure? (input : LensFamilyInput.{u})
    (Carrier : Type u) (object : ArchitectureObject (lensAATCarrier input)) :
    Option (LensLawStructure input.View Carrier) := by
  classical
  exact if h : object.StructureMaps =
      ULift.{u + 1, u} (LensLawStructure input.View Carrier) then
    some (h ▸ object.structureMaps).down
  else none

/-- Reading a constructed lens-law object returns its actual operation data. -/
@[simp] theorem lensLawStructure?_object (input : LensFamilyInput.{u})
    (Carrier : Type u) (data : LensLawStructure input.View Carrier) :
    lensLawStructure? input Carrier (lensLawObject input Carrier data) = some data := by
  classical
  unfold lensLawStructure?
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

/-- The lens coordinate ring has one symbolic variable per law instance and Atom. -/
abbrev LensLawCoordinateRing (input : LensFamilyInput.{u}) (Carrier : Type u) :=
  MvPolynomial
    (ULift.{u + 1, u} (LensLawIndex input.View Carrier) × LensAATAtom input) Int

/-- The object-dependent AAT equation system for lens operations on fixed carriers. -/
noncomputable def lensLawEquationSystem (input : LensFamilyInput.{u})
    (Carrier : Type u) (base : LensLawStructure input.View Carrier) :
    ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory (lensLawObject input Carrier base)) where
  Index := ULift.{u + 1, u} (LensLawIndex input.View Carrier)
  role _ := .required
  Observable _ := LensLawCoordinateRing input Carrier
  observableCommRing _ := inferInstance
  restrict _ := RingHom.id _
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl
  violationCoordinate _ index atom := MvPolynomial.X (index, atom)
  violationCoordinate_restrict _ _ _ := rfl
  equationResidual _ object index _ := by
    classical
    exact MvPolynomial.C (if
      (lensLawStructure? input Carrier object).elim False index.down.Holds then 0 else 1)
  equationResidual_restrict _ _ _ _ := rfl

/-- On a constructed lens object, residual vanishing is exactly its stored equation. -/
theorem lensLawEquationHolds_iff (input : LensFamilyInput.{u})
    (Carrier : Type u) (base data : LensLawStructure input.View Carrier)
    (index : LensLawIndex input.View Carrier) :
    (lensLawEquationSystem input Carrier base).EquationHolds (ULift.up index)
        (lensLawObject input Carrier data) ↔ index.Holds data := by
  classical
  constructor
  · intro h
    have hresidual := h
      ⟨fullFamilyUnitContext (lensLawObject input Carrier base) (fun _ => trivial)⟩
      (.point : LensAATAtom input)
    by_cases hLaw : index.Holds data
    · exact hLaw
    · simp [lensLawEquationSystem, hLaw] at hresidual
  · intro hLaw _ _
    simp [lensLawEquationSystem, hLaw]

/-- AAT lawfulness is equivalent to all three original L1 laws. -/
theorem lensEquationLawful_iff (input : LensFamilyInput.{u})
    (Carrier : Type u) (base data : LensLawStructure input.View Carrier) :
    (lensLawEquationSystem input Carrier base).EquationLawful
        (lensLawObject input Carrier data) ↔
      (∀ state, data.put state (data.get state) = state) ∧
      (∀ state view, data.get (data.put state view) = view) ∧
      (∀ state first second,
        data.put (data.put state first) second = data.put state second) := by
  constructor
  · intro lawful
    refine ⟨?_, ?_, ?_⟩
    · intro state
      exact (lensLawEquationHolds_iff input Carrier base data (.putGet state)).mp
        (lawful (ULift.up (.putGet state)) rfl)
    · intro state view
      exact (lensLawEquationHolds_iff input Carrier base data (.getPut state view)).mp
        (lawful (ULift.up (.getPut state view)) rfl)
    · intro state first second
      exact (lensLawEquationHolds_iff input Carrier base data
        (.putPut state first second)).mp
        (lawful (ULift.up (.putPut state first second)) rfl)
  · rintro ⟨putGet, getPut, putPut⟩ index _
    apply (lensLawEquationHolds_iff input Carrier base data index.down).mpr
    cases index.down with
    | putGet state => exact putGet state
    | getPut state view => exact getPut state view
    | putPut state first second => exact putPut state first second

/-- Every independent lens realization discharges the object-dependent residuals. -/
theorem lensRealization_equationLawful {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure).EquationLawful
      (lensLawObject input X.Carrier X.toLensData.toLawStructure) :=
  (lensEquationLawful_iff input X.Carrier X.toLensData.toLawStructure
    X.toLensData.toLawStructure).mpr
      ⟨X.condition.put_get, X.condition.get_put, X.condition.put_put⟩

/-! ### A concrete non-lawful lens object -/

/-- A raw Bool lens candidate whose updates ignore the requested view. -/
def ignoredBoolLensLawStructure : LensLawStructure Bool Bool where
  get := id
  put := fun state _ => state

/-- The raw Bool candidate fails the requested-view instance of `get-put`. -/
theorem ignoredBoolLensLawStructure_not_getPut :
    ¬ (LensLawIndex.getPut false true).Holds ignoredBoolLensLawStructure := by
  simp [LensLawIndex.Holds, ignoredBoolLensLawStructure]

/-! ## Protocol laws -/

/-- Protocol operations and observations on fixed state carriers, without laws. -/
structure ProtocolLawStructure (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u) where
  edgeAction : ∀ {source target}, input.schema.Edge source target →
    State source → State target
  observe : ∀ vertex, State vertex →
    input.observation.obj (input.schema.vertexObject vertex)

/-- The fixed relation instances and named-edge observation squares. -/
inductive ProtocolLawIndex {input : ProtocolFamilyInput.{u}}
    (State : input.schema.Vertex → Type u) : Type u
  | relation (r : input.schema.RelationIndex)
      (state : State (input.schema.relationSource r))
  | observation {source target : input.schema.Vertex}
      (edge : input.schema.Edge source target) (state : State source)

/-- Direct meaning of one raw protocol relation or observation equation. -/
def ProtocolLawIndex.Holds {input : ProtocolFamilyInput.{u}}
    {State : input.schema.Vertex → Type u}
    (data : ProtocolLawStructure input State) : ProtocolLawIndex State → Prop
  | .relation r state =>
      input.schema.evaluatePath data.edgeAction (input.schema.relationLeft r) state =
        input.schema.evaluatePath data.edgeAction (input.schema.relationRight r) state
  | .observation edge state =>
      input.observation.map (input.schema.edgeMorphism edge) (data.observe _ state) =
        data.observe _ (data.edgeAction edge state)

/-- An AAT object storing exact protocol operations and observations. -/
def protocolLawObject (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u) (data : ProtocolLawStructure input State) :
    ArchitectureObject (protocolAATCarrier input) where
  configuration := typedRoleConfiguration (.point : ProtocolAATAtom input)
  StructureMaps := ULift.{u + 1, u} (ProtocolLawStructure input State)
  SelectedQuantities := PUnit
  structureMaps := ULift.up data
  selectedQuantities := PUnit.unit

/-- Read fixed-carrier protocol operations from the evaluated object. -/
noncomputable def protocolLawStructure? (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (object : ArchitectureObject (protocolAATCarrier input)) :
    Option (ProtocolLawStructure input State) := by
  classical
  exact if h : object.StructureMaps =
      ULift.{u + 1, u} (ProtocolLawStructure input State) then
    some (h ▸ object.structureMaps).down
  else none

/-- Reading a constructed protocol-law object returns its stored operations. -/
@[simp] theorem protocolLawStructure?_object (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (data : ProtocolLawStructure input State) :
    protocolLawStructure? input State (protocolLawObject input State data) =
      some data := by
  classical
  unfold protocolLawStructure?
  split
  · rfl
  · rename_i h
    exact (h rfl).elim

/-- One symbolic variable for every protocol equation instance and Atom. -/
abbrev ProtocolLawCoordinateRing (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u) :=
  MvPolynomial
    (ULift.{u + 1, u} (ProtocolLawIndex State) × ProtocolAATAtom input) Int

/-- The object-dependent AAT equation system for fixed protocol state carriers. -/
noncomputable def protocolLawEquationSystem (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (base : ProtocolLawStructure input State) :
    ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory (protocolLawObject input State base)) where
  Index := ULift.{u + 1, u} (ProtocolLawIndex State)
  role _ := .required
  Observable _ := ProtocolLawCoordinateRing input State
  observableCommRing _ := inferInstance
  restrict _ := RingHom.id _
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl
  violationCoordinate _ index atom := MvPolynomial.X (index, atom)
  violationCoordinate_restrict _ _ _ := rfl
  equationResidual _ object index _ := by
    classical
    exact MvPolynomial.C (if
      (protocolLawStructure? input State object).elim False index.down.Holds then 0 else 1)
  equationResidual_restrict _ _ _ _ := rfl

/-- Residual vanishing on a constructed protocol object is its stored equation. -/
theorem protocolLawEquationHolds_iff (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (base data : ProtocolLawStructure input State)
    (index : ProtocolLawIndex State) :
    (protocolLawEquationSystem input State base).EquationHolds (ULift.up index)
        (protocolLawObject input State data) ↔ index.Holds data := by
  classical
  constructor
  · intro h
    have hresidual := h
      ⟨fullFamilyUnitContext (protocolLawObject input State base) (fun _ => trivial)⟩
      (.point : ProtocolAATAtom input)
    by_cases hLaw : index.Holds data
    · exact hLaw
    · simp [protocolLawEquationSystem, hLaw] at hresidual
  · intro hLaw _ _
    simp [protocolLawEquationSystem, hLaw]

/-- Protocol AAT lawfulness is all relations and all named-edge observations. -/
theorem protocolEquationLawful_iff (input : ProtocolFamilyInput.{u})
    (State : input.schema.Vertex → Type u)
    (base data : ProtocolLawStructure input State) :
    (protocolLawEquationSystem input State base).EquationLawful
        (protocolLawObject input State data) ↔
      (∀ (r : input.schema.RelationIndex)
        (state : State (input.schema.relationSource r)),
        input.schema.evaluatePath data.edgeAction (input.schema.relationLeft r) state =
          input.schema.evaluatePath data.edgeAction (input.schema.relationRight r) state) ∧
      (∀ {source target : input.schema.Vertex}
        (edge : input.schema.Edge source target) (state : State source),
        input.observation.map (input.schema.edgeMorphism edge)
            (data.observe source state) =
          data.observe target (data.edgeAction edge state)) := by
  constructor
  · intro lawful
    constructor
    · intro r state
      exact (protocolLawEquationHolds_iff input State base data
        (.relation r state)).mp (lawful (ULift.up (.relation r state)) rfl)
    · intro source target edge state
      exact (protocolLawEquationHolds_iff input State base data
        (.observation edge state)).mp (lawful (ULift.up (.observation edge state)) rfl)
  · rintro ⟨relations, observations⟩ index _
    apply (protocolLawEquationHolds_iff input State base data index.down).mpr
    cases index.down with
    | relation r state => exact relations r state
    | observation edge state => exact observations edge state

/-- Extract raw operations and observations; no law proof is copied. -/
def ProtocolRealization.toLawStructure {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolLawStructure input X.State where
  edgeAction := X.edgeAction
  observe := X.observe

/-- Named-edge evaluation agrees with the realization on every finite path. -/
theorem protocolEvaluatePath_eq_pathAction {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation)
    {source target : input.schema.Vertex} (path : Quiver.Path source target) :
    input.schema.evaluatePath X.edgeAction path = X.pathAction path := by
  induction path with
  | nil =>
      change (𝟙 (X.State source)) = X.toFunctor.map
        ((CategoryTheory.Quotient.functor input.schema.pathRelation).map
          (Quiver.Path.nil : Quiver.Path source source))
      have hquotient :
          (CategoryTheory.Quotient.functor input.schema.pathRelation).map
              (Quiver.Path.nil : Quiver.Path source source) =
            𝟙 (input.schema.vertexObject source) :=
        (CategoryTheory.Quotient.functor input.schema.pathRelation).map_id source
      rw [hquotient]
      exact (X.toFunctor.map_id _).symm
  | cons path edge ih =>
      change input.schema.evaluatePath X.edgeAction path ≫ X.edgeAction edge =
        X.toFunctor.map ((CategoryTheory.Quotient.functor input.schema.pathRelation).map
          (path.cons edge))
      rw [ih]
      have hquotient :
          (CategoryTheory.Quotient.functor input.schema.pathRelation).map
              (path.cons edge) =
            (CategoryTheory.Quotient.functor input.schema.pathRelation).map path ≫
              (CategoryTheory.Quotient.functor input.schema.pathRelation).map
                (Quiver.Hom.toPath edge) := by
        exact (CategoryTheory.Quotient.functor input.schema.pathRelation).map_comp
          path (Quiver.Hom.toPath edge)
      rw [hquotient, X.toFunctor.map_comp]
      rfl

/-- Every independent protocol realization discharges the object-dependent
residuals from quotient soundness and observation naturality. -/
theorem protocolRealization_equationLawful {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    (protocolLawEquationSystem input X.State X.toLawStructure).EquationLawful
      (protocolLawObject input X.State X.toLawStructure) := by
  apply (protocolEquationLawful_iff input X.State X.toLawStructure
    X.toLawStructure).mpr
  constructor
  · intro r state
    change input.schema.evaluatePath X.edgeAction (input.schema.relationLeft r) state =
      input.schema.evaluatePath X.edgeAction (input.schema.relationRight r) state
    rw [protocolEvaluatePath_eq_pathAction, protocolEvaluatePath_eq_pathAction]
    exact DFunLike.congr_fun
      (congrArg X.toFunctor.map (input.schema.relation_sound r)) state
  · intro source target edge state
    exact DFunLike.congr_fun
      (NatTrans.naturality X.observation (input.schema.edgeMorphism edge)).symm state

/-! ### A concrete non-lawful protocol object -/

/-- The sole vertex of the concrete negative protocol schema. -/
inductive TogglingProtocolVertex
  | point
  deriving DecidableEq, Fintype

/-- One vertex and one named edge, with the generating equation `id = edge`. -/
def togglingProtocolSchema : ProtocolSchema where
  Vertex := TogglingProtocolVertex
  vertex_finite := inferInstance
  Edge := fun _ _ => PUnit
  edge_finite := fun _ _ => inferInstance
  RelationIndex := PUnit
  relation_finite := inferInstance
  relationSource := fun _ => .point
  relationTarget := fun _ => .point
  relationLeft := fun _ =>
    @Quiver.Path.nil TogglingProtocolVertex ⟨fun _ _ => PUnit⟩ .point
  relationRight := fun _ =>
    @Quiver.Hom.toPath TogglingProtocolVertex ⟨fun _ _ => PUnit⟩
      .point .point PUnit.unit

/-- The constant one-point observation functor for the negative protocol example. -/
def togglingProtocolObservation : togglingProtocolSchema.ExecutionCategory ⥤ Type where
  obj _ := PUnit
  map _ _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Fixed protocol input for the concrete relation failure. -/
def togglingProtocolInput : ProtocolFamilyInput where
  schema := togglingProtocolSchema
  observation := togglingProtocolObservation

/-- The named edge toggles Bool, so it cannot satisfy the equation `id = edge`. -/
def togglingProtocolLawStructure :
    ProtocolLawStructure togglingProtocolInput (fun _ => Bool) where
  edgeAction := fun _ state => !state
  observe := fun _ _ => PUnit.unit

/-- The concrete protocol candidate fails its generating relation at `false`. -/
theorem togglingProtocolLawStructure_not_relation :
    ¬ (ProtocolLawIndex.relation (input := togglingProtocolInput)
      PUnit.unit false).Holds togglingProtocolLawStructure := by
  change ¬ (false = true)
  decide

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
