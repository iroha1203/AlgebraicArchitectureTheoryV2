import ResearchLean.AG.RealizationReconstruction.CSAATLawSystems
import Formal.Util.AssertStandardAxioms

/-!
# Raw CS morphisms transport the constructed AAT law instances

This module works before endpoint lawfulness: a raw law morphism consists only
of a carrier map and the original operation/observation squares.  Those squares
transport every Cycle 126 equation instance and its polynomial coordinate.
Every arbitrary semantic CS morphism constructs such a raw morphism, but the
preservation theorem does not use endpoint `LensRealization` or
`ProtocolRealization` lawfulness.

## Implementation notes

Stating preservation only between lawful realizations would be vacuous because
the target laws would already hold.  The raw structures below therefore contain
exactly the morphism data needed for nontrivial preservation, with no target
lawfulness or AAT preservation certificate.  Index maps retain every view,
relation, named edge, and Atom.  No reverse truth implication is claimed.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens transport -/

/-- A map of raw lens operation structures satisfying exactly the n1015 (L2)
get/put squares, before either endpoint is assumed lawful. -/
structure LensLawHom {View Source Target : Type u}
    (source : LensLawStructure View Source)
    (target : LensLawStructure View Target) where
  toFun : Source → Target
  get_naturality : ∀ state, target.get (toFun state) = source.get state
  put_naturality : ∀ state view,
    toFun (source.put state view) = target.put (toFun state) view

/-- Identity raw lens-law morphism; this is the normal form for index and
coordinate identity rewrites below. -/
def LensLawHom.id {View Carrier : Type u} (data : LensLawStructure View Carrier) :
    LensLawHom data data where
  toFun := fun state => state
  get_naturality _ := rfl
  put_naturality _ _ := rfl

/-- Composition of raw lens-law morphisms, with the source-to-target order used
by the CS category. -/
def LensLawHom.comp {View A B C : Type u}
    {first : LensLawStructure View A} {second : LensLawStructure View B}
    {third : LensLawStructure View C}
    (f : LensLawHom first second) (g : LensLawHom second third) :
    LensLawHom first third where
  toFun := g.toFun ∘ f.toFun
  get_naturality state := (g.get_naturality _).trans (f.get_naturality state)
  put_naturality state view := by
    simp only [Function.comp_apply, f.put_naturality, g.put_naturality]

/-- Every arbitrary semantic lens morphism supplies the raw n1015 (L2) squares;
no injectivity, inverse, or Law certificate is added. -/
def LensRealization.Hom.toLawHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    LensLawHom X.toLensData.toLawStructure Y.toLensData.toLawStructure where
  toFun := f.toFun
  get_naturality := f.get_naturality
  put_naturality := f.put_naturality

/-- Transport every fully quantified lens-law instance by a raw L2 map. -/
def lensLawIndexMap {View Source Target : Type u}
    {source : LensLawStructure View Source} {target : LensLawStructure View Target}
    (f : LensLawHom source target) :
    LensLawIndex View Source → LensLawIndex View Target
  | .putGet state => .putGet (f.toFun state)
  | .getPut state view => .getPut (f.toFun state) view
  | .putPut state first second => .putPut (f.toFun state) first second

/-- Raw lens index transport rewrites identity applications to the input index. -/
@[simp] theorem lensLawIndexMap_id {View Carrier : Type u}
    (data : LensLawStructure View Carrier) (index : LensLawIndex View Carrier) :
    lensLawIndexMap (LensLawHom.id data) index = index := by
  cases index <;> rfl

/-- Raw lens index transport rewrites a composite to successive transport. -/
@[simp] theorem lensLawIndexMap_comp {View A B C : Type u}
    {first : LensLawStructure View A} {second : LensLawStructure View B}
    {third : LensLawStructure View C}
    (f : LensLawHom first second) (g : LensLawHom second third)
    (index : LensLawIndex View A) :
    lensLawIndexMap (LensLawHom.comp f g) index =
      lensLawIndexMap g (lensLawIndexMap f index) := by
  cases index <;> rfl

/-- The raw n1015 (L2) squares nonvacuously preserve each source law instance;
the target structure is not assumed lawful. -/
theorem lensLawIndexMap_holds {View Source Target : Type u}
    {source : LensLawStructure View Source} {target : LensLawStructure View Target}
    (f : LensLawHom source target) (index : LensLawIndex View Source)
    (h : index.Holds source) : (lensLawIndexMap f index).Holds target := by
  cases index with
  | putGet state =>
      change target.put (f.toFun state) (target.get (f.toFun state)) = f.toFun state
      rw [f.get_naturality, ← f.put_naturality]
      exact congrArg f.toFun h
  | getPut state view =>
      change target.get (target.put (f.toFun state) view) = view
      rw [← f.put_naturality, f.get_naturality]
      exact h
  | putPut state first second =>
      change target.put (target.put (f.toFun state) first) second =
        target.put (f.toFun state) second
      rw [← f.put_naturality, ← f.put_naturality, ← f.put_naturality]
      exact congrArg f.toFun h

/-- Rename lens equation/Atom coordinates by the raw index map. -/
noncomputable def lensLawCoordinateMap (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target) :
    LensLawCoordinateRing input Source →+* LensLawCoordinateRing input Target :=
  (MvPolynomial.rename fun coordinate :
      ULift.{u + 1, u} (LensLawIndex input.View Source) × LensAATAtom input =>
    (ULift.up (lensLawIndexMap f coordinate.1.down), coordinate.2)).toRingHom

/-- Lens coordinate transport sends a variable to the exact mapped index and
unchanged Atom. -/
@[simp] theorem lensLawCoordinateMap_violation (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (index : LensLawIndex input.View Source) (atom : LensAATAtom input) :
    lensLawCoordinateMap input f (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (lensLawIndexMap f index), atom) := by
  simp [lensLawCoordinateMap]

/-- Lens coordinate identity rewrites to the identity ring hom. -/
@[simp] theorem lensLawCoordinateMap_id (input : LensFamilyInput.{u})
    {Carrier : Type u} (data : LensLawStructure input.View Carrier) :
    lensLawCoordinateMap input (LensLawHom.id data) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lensLawCoordinateMap]
  · rcases value with ⟨index, atom⟩
    simp [lensLawCoordinateMap]

/-- Lens coordinate composition rewrites to target-after-source ring maps. -/
@[simp] theorem lensLawCoordinateMap_comp (input : LensFamilyInput.{u})
    {A B C : Type u} {first : LensLawStructure input.View A}
    {second : LensLawStructure input.View B} {third : LensLawStructure input.View C}
    (f : LensLawHom first second) (g : LensLawHom second third) :
    lensLawCoordinateMap input (LensLawHom.comp f g) =
      (lensLawCoordinateMap input g).comp (lensLawCoordinateMap input f) := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [lensLawCoordinateMap]
  · rcases value with ⟨index, atom⟩
    simp [lensLawCoordinateMap]

/-- Raw L2 preservation carries actual Cycle 126 `EquationHolds` between
independently supplied operation structures. -/
theorem lensLawEquationHolds_map (input : LensFamilyInput.{u})
    {Source Target : Type u} {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target} (f : LensLawHom source target)
    (index : LensLawIndex input.View Source)
    (h : (lensLawEquationSystem input Source source).EquationHolds
      (ULift.up index) (lensLawObject input Source source)) :
    (lensLawEquationSystem input Target target).EquationHolds
      (ULift.up (lensLawIndexMap f index)) (lensLawObject input Target target) := by
  apply (lensLawEquationHolds_iff input Target target target _).mpr
  exact lensLawIndexMap_holds f index
    ((lensLawEquationHolds_iff input Source source source index).mp h)

/-! ## Protocol transport -/

/-- A raw protocol operation/observation map satisfying exactly the generator
and observation squares, before endpoint lawfulness. -/
structure ProtocolLawHom {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    (source : ProtocolLawStructure input Source)
    (target : ProtocolLawStructure input Target) where
  stateMap : ∀ vertex, Source vertex → Target vertex
  edge_naturality : ∀ {v w} (edge : input.schema.Edge v w) (state : Source v),
    stateMap w (source.edgeAction edge state) = target.edgeAction edge (stateMap v state)
  observation_naturality : ∀ vertex state,
    target.observe vertex (stateMap vertex state) = source.observe vertex state

/-- Identity raw protocol-law morphism and normal form for later rewrites. -/
def ProtocolLawHom.id {input : ProtocolFamilyInput.{u}}
    {State : input.schema.Vertex → Type u} (data : ProtocolLawStructure input State) :
    ProtocolLawHom data data where
  stateMap := fun _ state => state
  edge_naturality _ _ := rfl
  observation_naturality _ _ := rfl

/-- Composition of raw protocol-law morphisms in source-to-target order. -/
def ProtocolLawHom.comp {input : ProtocolFamilyInput.{u}}
    {A B C : input.schema.Vertex → Type u}
    {first : ProtocolLawStructure input A} {second : ProtocolLawStructure input B}
    {third : ProtocolLawStructure input C}
    (f : ProtocolLawHom first second) (g : ProtocolLawHom second third) :
    ProtocolLawHom first third where
  stateMap vertex := g.stateMap vertex ∘ f.stateMap vertex
  edge_naturality edge state := by
    simp only [Function.comp_apply, f.edge_naturality, g.edge_naturality]
  observation_naturality vertex state := by
    simp only [Function.comp_apply, g.observation_naturality, f.observation_naturality]

/-- Every arbitrary semantic protocol morphism supplies the raw edge and
observation squares, with no invertibility or Law certificate. -/
def ProtocolRealization.Hom.toLawHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ProtocolLawHom X.toLawStructure Y.toLawStructure where
  stateMap := protocolStateMap a
  edge_naturality edge state := by
    simpa [protocolStateMap, Function.comp_apply] using
      DFunLike.congr_fun (ProtocolRealization.edge_naturality a edge) state
  observation_naturality vertex state := by
    simpa [protocolStateMap, Function.comp_apply] using
      DFunLike.congr_fun (ProtocolRealization.observation_app a vertex) state

/-- Transport every protocol relation or observation instance by a raw map. -/
def protocolLawIndexMap {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    ProtocolLawIndex Source → ProtocolLawIndex Target
  | .relation r state => .relation r (a.stateMap _ state)
  | .observation edge state => .observation edge (a.stateMap _ state)

/-- Raw protocol index identity rewrites to the input index. -/
@[simp] theorem protocolLawIndexMap_id {input : ProtocolFamilyInput.{u}}
    {State : input.schema.Vertex → Type u} (data : ProtocolLawStructure input State)
    (index : ProtocolLawIndex State) :
    protocolLawIndexMap (ProtocolLawHom.id data) index = index := by
  cases index <;> rfl

/-- Raw protocol index composition rewrites to successive transport. -/
@[simp] theorem protocolLawIndexMap_comp {input : ProtocolFamilyInput.{u}}
    {A B C : input.schema.Vertex → Type u}
    {first : ProtocolLawStructure input A} {second : ProtocolLawStructure input B}
    {third : ProtocolLawStructure input C}
    (f : ProtocolLawHom first second) (g : ProtocolLawHom second third)
    (index : ProtocolLawIndex A) :
    protocolLawIndexMap (ProtocolLawHom.comp f g) index =
      protocolLawIndexMap g (protocolLawIndexMap f index) := by
  cases index <;> rfl

/-- Raw generator squares extend to every finite path. -/
theorem protocolEvaluatePath_naturality {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    {v w : input.schema.Vertex} (path : Quiver.Path v w) (state : Source v) :
    a.stateMap w (input.schema.evaluatePath source.edgeAction path state) =
      input.schema.evaluatePath target.edgeAction path (a.stateMap v state) := by
  induction path with
  | nil => rfl
  | cons path edge ih =>
      change a.stateMap _ (source.edgeAction edge
          (input.schema.evaluatePath source.edgeAction path state)) =
        target.edgeAction edge
          (input.schema.evaluatePath target.edgeAction path (a.stateMap _ state))
      rw [a.edge_naturality, ih]

/-- Raw protocol squares nonvacuously preserve each source law instance; the
target structure is not assumed lawful. -/
theorem protocolLawIndexMap_holds {input : ProtocolFamilyInput.{u}}
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (index : ProtocolLawIndex Source) (h : index.Holds source) :
    (protocolLawIndexMap a index).Holds target := by
  cases index with
  | relation r state =>
      change input.schema.evaluatePath target.edgeAction
          (input.schema.relationLeft r) (a.stateMap _ state) =
        input.schema.evaluatePath target.edgeAction
          (input.schema.relationRight r) (a.stateMap _ state)
      rw [← protocolEvaluatePath_naturality a _ state,
        ← protocolEvaluatePath_naturality a _ state, h]
  | observation edge state =>
      change input.observation.map (input.schema.edgeMorphism edge)
          (target.observe _ (a.stateMap _ state)) =
        target.observe _ (target.edgeAction edge (a.stateMap _ state))
      rw [a.observation_naturality, ← a.edge_naturality,
        a.observation_naturality]
      exact h

/-- Rename protocol equation/Atom coordinates by the raw index map. -/
noncomputable def protocolLawCoordinateMap (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target) :
    ProtocolLawCoordinateRing input Source →+* ProtocolLawCoordinateRing input Target :=
  (MvPolynomial.rename fun coordinate :
      ULift.{u + 1, u} (ProtocolLawIndex Source) × ProtocolAATAtom input =>
    (ULift.up (protocolLawIndexMap a coordinate.1.down), coordinate.2)).toRingHom

/-- Protocol coordinate transport sends a variable to the exact mapped index
and unchanged Atom. -/
@[simp] theorem protocolLawCoordinateMap_violation (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (index : ProtocolLawIndex Source) (atom : ProtocolAATAtom input) :
    protocolLawCoordinateMap input a (MvPolynomial.X (ULift.up index, atom)) =
      MvPolynomial.X (ULift.up (protocolLawIndexMap a index), atom) := by
  simp [protocolLawCoordinateMap]

/-- Protocol coordinate identity rewrites to the identity ring hom. -/
@[simp] theorem protocolLawCoordinateMap_id (input : ProtocolFamilyInput.{u})
    {State : input.schema.Vertex → Type u} (data : ProtocolLawStructure input State) :
    protocolLawCoordinateMap input (ProtocolLawHom.id data) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [protocolLawCoordinateMap]
  · rcases value with ⟨index, atom⟩
    simp [protocolLawCoordinateMap]

/-- Protocol coordinate composition rewrites to target-after-source maps. -/
@[simp] theorem protocolLawCoordinateMap_comp (input : ProtocolFamilyInput.{u})
    {A B C : input.schema.Vertex → Type u}
    {first : ProtocolLawStructure input A} {second : ProtocolLawStructure input B}
    {third : ProtocolLawStructure input C}
    (f : ProtocolLawHom first second) (g : ProtocolLawHom second third) :
    protocolLawCoordinateMap input (ProtocolLawHom.comp f g) =
      (protocolLawCoordinateMap input g).comp (protocolLawCoordinateMap input f) := by
  apply MvPolynomial.ringHom_ext <;> intro value
  · simp [protocolLawCoordinateMap]
  · rcases value with ⟨index, atom⟩
    simp [protocolLawCoordinateMap]

/-- Raw protocol preservation carries actual Cycle 126 `EquationHolds` between
independently supplied operation structures. -/
theorem protocolLawEquationHolds_map (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target} (a : ProtocolLawHom source target)
    (index : ProtocolLawIndex Source)
    (h : (protocolLawEquationSystem input Source source).EquationHolds
      (ULift.up index) (protocolLawObject input Source source)) :
    (protocolLawEquationSystem input Target target).EquationHolds
      (ULift.up (protocolLawIndexMap a index))
      (protocolLawObject input Target target) := by
  apply (protocolLawEquationHolds_iff input Target target target _).mpr
  exact protocolLawIndexMap_holds a index
    ((protocolLawEquationHolds_iff input Source source source index).mp h)

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
