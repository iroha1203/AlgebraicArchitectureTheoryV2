import ResearchLean.AG.LocalSemanticReconstruction.IndependentAATPrimitiveReconstruction
import ResearchLean.AG.RealizationReconstruction.CSAATArchitectureObjects
import Formal.Util.AssertStandardAxioms

/-!
# G-124 III-1: CS component projections

The coefficient component of both CS families is the fixed base ring `ℤ`.
The lens observation component is the get slice: its arrows retain the full
state function and its get square, including noninjective functions.
-/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionCS

open CategoryTheory
open AAT.AG.RealizationReconstruction
open AAT.AG.AtomFoundation
open IndependentAATPrimitiveReconstruction
open IndependentLensPrimitiveReconstruction

universe u

/-- The constant integer coefficient functor used by each CS branch.  Its
domain universe is explicit so the global parameter lift can reuse it. -/
noncomputable def constantIntegerCoefficient (C : Type (u + 1)) [Category C] :
    C ⥤ CommRingCat where
  obj _ := CommRingCat.of ℤ
  map _ := 𝟙 (CommRingCat.of ℤ)
  map_id _ := rfl
  map_comp _ _ := by simp

/-- The native lens AAT connection has fixed coefficient `ℤ`. -/
noncomputable def lensCoefficientNative (input : LensFamilyInput.{u}) :
    NativeCategory (Parameter.lens input : Parameter.{u, u}) ⥤ CommRingCat :=
  constantIntegerCoefficient _

/-- The primitive lens component retains the fixed integer coefficient
without assembling the semantic lens. -/
noncomputable def lensCoefficientLocal (input : LensFamilyInput.{u}) :
    LocalCategory (Parameter.lens input : Parameter.{u, u}) ⥤ CommRingCat :=
  constantIntegerCoefficient _

/-- The native protocol AAT connection has fixed coefficient `ℤ`. -/
noncomputable def protocolCoefficientNative (input : ProtocolFamilyInput.{u}) :
    NativeCategory (Parameter.protocol input : Parameter.{u, u}) ⥤ CommRingCat :=
  constantIntegerCoefficient _

/-- The primitive protocol component retains the fixed integer coefficient
without assembling the semantic protocol. -/
noncomputable def protocolCoefficientLocal (input : ProtocolFamilyInput.{u}) :
    LocalCategory (Parameter.protocol input : Parameter.{u, u}) ⥤ CommRingCat :=
  constantIntegerCoefficient _

/-- The lens coefficient square is pointwise identity on `ℤ`. -/
noncomputable def lensCoefficientReadingIso (input : LensFamilyInput.{u}) :
    reading (Parameter.lens input : Parameter.{u, u}) ⋙
      lensCoefficientLocal input ≅ lensCoefficientNative input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The protocol coefficient square is pointwise identity on `ℤ`. -/
noncomputable def protocolCoefficientReadingIso (input : ProtocolFamilyInput.{u}) :
    reading (Parameter.protocol input : Parameter.{u, u}) ⋙
      protocolCoefficientLocal input ≅ protocolCoefficientNative input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- Native lens bottom projection: the exact extraction doctrine together
with its selected point.  Every semantic lens Hom is retained, including
noninjective state maps. -/
def lensBottomNative (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ⥤
      ExtractionInstance (lensAATCarrier input) where
  obj lens := ⟨lensAATExtractionDoctrine lens, .point⟩
  map morphism := ⟨lensAATExactDoctrineHom morphism, rfl⟩
  map_id lens := by
    apply ExtInstHom.ext
    exact lensAATExactDoctrineHom_id lens
  map_comp first second := by
    apply ExtInstHom.ext
    exact lensAATExactDoctrineHom_comp first second

/-- The native lens bottom source map evaluates to the original state map. -/
theorem lensBottomNative_state (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) (state : source.Carrier) :
    ((lensBottomNative input).map morphism).doctrineHom.sourceMap
      (.state state) = .state (morphism.toFun state) :=
  lensAATExactDoctrineHom_sourceMap_state morphism state

/-- Native protocol bottom projection: the exact extraction doctrine and its
selected point, on all natural transformations over the observation functor. -/
def protocolBottomNative (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ⥤
      ExtractionInstance (protocolAATCarrier input) where
  obj realization := ⟨protocolAATExtractionDoctrine realization, .point⟩
  map morphism := ⟨protocolAATExactDoctrineHom morphism, rfl⟩
  map_id realization := by
    apply ExtInstHom.ext
    exact protocolAATExactDoctrineHom_id realization
  map_comp first second := by
    apply ExtInstHom.ext
    exact protocolAATExactDoctrineHom_comp first second

/-- The native protocol bottom source map evaluates to the original state
component at each schema vertex. -/
theorem protocolBottomNative_state (input : ProtocolFamilyInput.{u})
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (state : source.State vertex) :
    ((protocolBottomNative input).map morphism).doctrineHom.sourceMap
      (.state vertex state) =
        .state vertex (protocolStateMap morphism vertex state) :=
  protocolAATExactDoctrineHom_sourceMap_state morphism vertex state

/-- A get-slice object retains the complete carrier and its point evaluation
to the fixed visible type.  There is no lens-law or full-realization field. -/
structure LensGetSlice (view : Type u) where
  Carrier : Type u
  get : Carrier → view

/-- An arrow of the get slice is an arbitrary state function preserving the
visible value. -/
@[ext]
structure LensGetSlice.Hom {view : Type u}
    (source target : LensGetSlice view) where
  toFun : source.Carrier → target.Carrier
  get_naturality : ∀ state, target.get (toFun state) = source.get state

instance (view : Type u) : Category (LensGetSlice view) where
  Hom := LensGetSlice.Hom
  id object := ⟨id, fun _ => rfl⟩
  comp first second :=
    ⟨second.toFun ∘ first.toFun,
      fun state => (second.get_naturality (first.toFun state)).trans
        (first.get_naturality state)⟩
  id_comp _ := by ext state; rfl
  comp_id _ := by ext state; rfl
  assoc _ _ _ := by ext state; rfl

/-- The native lens observation projection forgets put but retains the get
square of every original morphism. -/
def lensObservationNative (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ⥤ LensGetSlice input.View where
  obj lens := ⟨lens.Carrier, lens.get⟩
  map morphism := ⟨morphism.toFun, morphism.get_naturality⟩
  map_id _ := by apply LensGetSlice.Hom.ext; funext state; rfl
  map_comp _ _ := by apply LensGetSlice.Hom.ext; funext state; rfl

/-- The local lens observation object selects the carrier and get-point graph.
Its definition never invokes complete lens assembly. -/
noncomputable def lensObservationObject (input : LensFamilyInput.{u})
    (object : IndependentLensPrimitiveReconstruction.Object input) :
    LensGetSlice input.View :=
  ⟨object.Carrier, assembleGet object⟩

@[simp] theorem lensObservationObject_get (input : LensFamilyInput.{u})
    (object : IndependentLensPrimitiveReconstruction.Object input)
    (state : object.Carrier) :
    (lensObservationObject input object).get state = assembleGet object state := rfl

/-- The local get-slice arrow selects the directed state-map graph.  The
preservation proof is exactly the primitive get formula at a fixed point. -/
noncomputable def lensObservationMap (input : LensFamilyInput.{u})
    {source target : IndependentLensPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) :
    LensGetSlice.Hom (lensObservationObject input source)
      (lensObservationObject input target) where
  toFun := morphism.toFun
  get_naturality state := by
    apply (get_edge_iff target (morphism.toFun state) (assembleGet source state)).mp
    exact morphism.get_rule state (morphism.toFun state)
      (assembleGet source state)
      ⟨(morphism.edge_iff state (morphism.toFun state)).mpr rfl,
        (get_edge_iff source state (assembleGet source state)).mpr rfl⟩

@[simp] theorem lensObservationMap_state (input : LensFamilyInput.{u})
    {source target : IndependentLensPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) (state : source.Carrier) :
    (lensObservationMap input morphism).toFun state = morphism.toFun state := rfl

/-- The local lens observation projection is functorial under direct point
graph identity and composition. -/
noncomputable def lensObservationLocal (input : LensFamilyInput.{u}) :
    IndependentLensPrimitiveReconstruction.Object input ⥤
      LensGetSlice input.View where
  obj := lensObservationObject input
  map := lensObservationMap input
  map_id object := by
    apply LensGetSlice.Hom.ext
    funext state
    change (identityHom object).toFun state = state
    simpa only [Hom.toFun, Hom.table, identityHom, homGlue_fragments]
      using congrFun (IndependentCarrierGraph.assemble_identity object.Carrier) state
  map_comp first second := by
    apply LensGetSlice.Hom.ext
    funext state
    simpa only [Hom.toFun, Hom.table, composeHom, homGlue_fragments]
      using congrFun (IndependentCarrierGraph.assemble_compose _ _ _
        first.table first.lawful second.table second.lawful) state

/-- The local A1 source is formed from the carrier-reference cell, with the
same four roles as the native CS doctrine and no completed lens field. -/
inductive LensLocalSource (carrier view : Type u) : Type (u + 1)
  | point
  | state (value : carrier)
  | view (value : view)
  | write (state : carrier) (value : view)

def lensLocalExtracts (input : LensFamilyInput.{u})
    {carrier : Type u} (source : LensLocalSource carrier input.View)
    (atom : LensAATAtom input) : Prop :=
  match source with
  | .point => True
  | .state _ => atom = .state ∨ atom = .read ∨ atom = .get
  | .view _ => atom = .view
  | .write _ _ => atom = .write ∨ atom = .put

/-- The local extraction doctrine is selected from the carrier cell alone;
its extraction predicate is the original role-specific A1 predicate. -/
def lensLocalDoctrine (input : LensFamilyInput.{u})
    (object : IndependentLensPrimitiveReconstruction.Object input) :
    ExtractionDoctrine (lensAATCarrier input) where
  Source := LensLocalSource object.Carrier input.View
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows _ _ := True
  semanticAllows _ source atom := lensLocalExtracts input source atom
  resolutionAllows _ _ _ := True
  sourceSemantics _ _ := True
  normalize := id

def lensBottomObject (input : LensFamilyInput.{u})
    (object : IndependentLensPrimitiveReconstruction.Object input) :
    ExtractionInstance (lensAATCarrier input) :=
  ⟨lensLocalDoctrine input object, .point⟩

/-- The primitive state graph induces the complete A1 source map, preserving
the point and every state, visible, and write source. -/
noncomputable def lensBottomMap (input : LensFamilyInput.{u})
    {source target : IndependentLensPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) :
    lensBottomObject input source ⟶ lensBottomObject input target where
  doctrineHom :=
    { sourceMap := fun role => match role with
        | .point => .point
        | .state state => .state (morphism.toFun state)
        | .view view => .view view
        | .write state view => .write (morphism.toFun state) view
      atomEquiv := Equiv.refl _
      normalize_eq _ := rfl
      extraction_iff source atom := by
        cases source <;> exact Iff.rfl }
  source_eq := rfl

/-- The local A1 source projection evaluates the original directed state
point graph even when its function is not injective. -/
theorem lensBottomMap_state (input : LensFamilyInput.{u})
    {source target : IndependentLensPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) (state : source.Carrier) :
    (lensBottomMap input morphism).doctrineHom.sourceMap (.state state) =
      .state (morphism.toFun state) := rfl

private theorem lensPrimitiveMap_id (input : LensFamilyInput.{u})
    (object : IndependentLensPrimitiveReconstruction.Object input) :
    (identityHom object).toFun = id := by
  have h := congrArg LensGetSlice.Hom.toFun
    ((lensObservationLocal input).map_id object)
  exact h

private theorem lensPrimitiveMap_comp (input : LensFamilyInput.{u})
    {source middle target : IndependentLensPrimitiveReconstruction.Object input}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    (composeHom first second).toFun = second.toFun ∘ first.toFun := by
  have h := congrArg LensGetSlice.Hom.toFun
    ((lensObservationLocal input).map_comp first second)
  exact h

/-- The primitive lens bottom source construction is functorial for every
lawful state graph, without an injectivity condition. -/
noncomputable def lensBottomLocal (input : LensFamilyInput.{u}) :
    IndependentLensPrimitiveReconstruction.Object input ⥤
      ExtractionInstance (lensAATCarrier input) where
  obj := lensBottomObject input
  map := lensBottomMap input
  map_id object := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      change (lensBottomMap input (identityHom object)).doctrineHom.sourceMap role =
        (ExtInstHom.id (lensBottomObject input object)).doctrineHom.sourceMap role
      cases role <;> simp [lensBottomMap, ExtInstHom.id,
        ExactDoctrineHom.id, lensPrimitiveMap_id input object]
    · rfl
  map_comp first second := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      change (lensBottomMap input (composeHom first second)).doctrineHom.sourceMap role =
        (ExtInstHom.comp (lensBottomMap input first)
          (lensBottomMap input second)).doctrineHom.sourceMap role
      cases role <;> simp [lensBottomMap, ExtInstHom.comp,
        ExactDoctrineHom.comp, lensPrimitiveMap_comp input first second]
    · rfl

/-- Primitive protocol A1 sources retain the role of every state and named
step, using only the vertex-carrier cells of the local object table. -/
inductive ProtocolLocalSource (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input) :
    Type (u + 1)
  | point
  | state (vertex : input.schema.Vertex) (value : object.State vertex)
  | step {source target : input.schema.Vertex}
      (edge : input.schema.Edge source target) (value : object.State source)

def protocolLocalExtracts (input : ProtocolFamilyInput.{u})
    {object : IndependentProtocolPrimitiveReconstruction.Object input}
    (source : ProtocolLocalSource input object)
    (atom : ProtocolAATAtom input) : Prop :=
  match source with
  | .point => True
  | .state vertex _ =>
      atom = .state vertex ∨ atom = .observation vertex ∨ atom = .observe vertex
  | .step edge _ => atom = .edge edge

/-- The primitive protocol bottom doctrine reads each vertex carrier from
the local table, with exactly the original role-specific extraction law. -/
def protocolLocalDoctrine (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input) :
    ExtractionDoctrine (protocolAATCarrier input) where
  Source := ProtocolLocalSource input object
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows _ _ := True
  semanticAllows _ source atom := protocolLocalExtracts input source atom
  resolutionAllows _ _ _ := True
  sourceSemantics _ _ := True
  normalize := id

def protocolBottomObject (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input) :
    ExtractionInstance (protocolAATCarrier input) :=
  ⟨protocolLocalDoctrine input object, .point⟩

/-- The local vertex-map graphs induce the complete A1 source action on
states and named steps, without an injectivity premise. -/
noncomputable def protocolBottomMap (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) :
    protocolBottomObject input source ⟶ protocolBottomObject input target where
  doctrineHom :=
    { sourceMap := fun role => match role with
        | .point => .point
        | .state vertex value => .state vertex (morphism.component vertex value)
        | .step edge value => .step edge (morphism.component _ value)
      atomEquiv := Equiv.refl _
      normalize_eq _ := rfl
      extraction_iff source atom := by
        cases source <;> exact Iff.rfl }
  source_eq := rfl

theorem protocolBottomMap_state (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (state : source.State vertex) :
    (protocolBottomMap input morphism).doctrineHom.sourceMap
      (.state vertex state) = .state vertex (morphism.component vertex state) := rfl

private theorem protocolPrimitiveMap_id (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input)
    (vertex : input.schema.Vertex) :
    (IndependentProtocolPrimitiveReconstruction.identityHom object).component vertex = id := by
  simpa only [IndependentProtocolPrimitiveReconstruction.Hom.component,
    IndependentProtocolPrimitiveReconstruction.vertexMapTable_identityHom]
    using IndependentCarrierGraph.assemble_identity (object.State vertex)

private theorem protocolPrimitiveMap_comp (input : ProtocolFamilyInput.{u})
    {source middle target : IndependentProtocolPrimitiveReconstruction.Object input}
    (first : source ⟶ middle) (second : middle ⟶ target)
    (vertex : input.schema.Vertex) :
    (IndependentProtocolPrimitiveReconstruction.composeHom first second).component vertex =
      second.component vertex ∘ first.component vertex := by
  simpa only [IndependentProtocolPrimitiveReconstruction.Hom.component,
    IndependentProtocolPrimitiveReconstruction.vertexMapTable_composeHom]
    using IndependentCarrierGraph.assemble_compose
      (source.State vertex) (middle.State vertex) (target.State vertex)
      (IndependentProtocolPrimitiveReconstruction.vertexMapTable first.table vertex)
      (first.lawful vertex)
      (IndependentProtocolPrimitiveReconstruction.vertexMapTable second.table vertex)
      (second.lawful vertex)

/-- The protocol bottom source projection respects direct graph identity and
composition at every vertex, including noninjective maps. -/
noncomputable def protocolBottomLocal (input : ProtocolFamilyInput.{u}) :
    IndependentProtocolPrimitiveReconstruction.Object input ⥤
      ExtractionInstance (protocolAATCarrier input) where
  obj := protocolBottomObject input
  map := protocolBottomMap input
  map_id object := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      change (protocolBottomMap input
          (IndependentProtocolPrimitiveReconstruction.identityHom object)).doctrineHom.sourceMap
            role =
        (ExtInstHom.id (protocolBottomObject input object)).doctrineHom.sourceMap role
      cases role with
      | point => rfl
      | state vertex value =>
          exact congrArg (ProtocolLocalSource.state vertex)
            (congrFun (protocolPrimitiveMap_id input object vertex) value)
      | step edge value =>
          exact congrArg (ProtocolLocalSource.step edge)
            (congrFun (protocolPrimitiveMap_id input object _) value)
    · rfl
  map_comp first second := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      change (protocolBottomMap input
          (IndependentProtocolPrimitiveReconstruction.composeHom first second)).doctrineHom.sourceMap
            role =
        (ExtInstHom.comp (protocolBottomMap input first)
          (protocolBottomMap input second)).doctrineHom.sourceMap role
      cases role with
      | point => rfl
      | state vertex value =>
          exact congrArg (ProtocolLocalSource.state vertex)
            (congrFun (protocolPrimitiveMap_comp input first second vertex) value)
      | step edge value =>
          exact congrArg (ProtocolLocalSource.step edge)
            (congrFun (protocolPrimitiveMap_comp input first second _) value)
    · rfl

/-- The protocol observation slice stores a state functor on the quotient
execution category and its natural map to the fixed observation functor.
Finiteness and full protocol realization are not target fields. -/
structure ProtocolObservationSlice (input : ProtocolFamilyInput.{u}) where
  state : input.schema.ExecutionCategory ⥤ Type u
  observe : state ⟶ input.observation

/-- A slice arrow is an arbitrary natural state map commuting with observe. -/
@[ext]
structure ProtocolObservationSlice.Hom {input : ProtocolFamilyInput.{u}}
    (source target : ProtocolObservationSlice input) where
  stateMap : source.state ⟶ target.state
  observe_square : stateMap ≫ target.observe = source.observe

instance (input : ProtocolFamilyInput.{u}) :
    Category (ProtocolObservationSlice input) where
  Hom := ProtocolObservationSlice.Hom
  id object := ⟨𝟙 object.state, by simp⟩
  comp first second :=
    ⟨first.stateMap ≫ second.stateMap, by
      rw [Category.assoc, second.observe_square, first.observe_square]⟩
  id_comp _ := by ext; simp
  comp_id _ := by ext; simp
  assoc _ _ _ := by ext; simp [Category.assoc]

/-- Native protocol observation projection retains the complete quotient
state action and its original observation square. -/
def protocolObservationNative (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ⥤
      ProtocolObservationSlice input where
  obj realization := ⟨realization.toFunctor, realization.observation⟩
  map morphism := ⟨morphism.toNatTrans, morphism.observation_naturality⟩
  map_id _ := by apply ProtocolObservationSlice.Hom.ext; rfl
  map_comp _ _ := by apply ProtocolObservationSlice.Hom.ext; rfl

/-- The local observation slice is assembled from vertex, named-edge, and
observation point graphs, with path action obtained by quotient extension. -/
noncomputable def protocolObservationObject (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input) :
    ProtocolObservationSlice input :=
  ⟨IndependentProtocolPrimitiveReconstruction.assembledFunctor object,
    IndependentProtocolPrimitiveReconstruction.assembledObservation object⟩

@[simp] theorem protocolObservationObject_state (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input)
    (vertex : input.schema.Vertex) :
    (protocolObservationObject input object).state.obj
      (input.schema.vertexObject vertex) = object.State vertex := rfl

@[simp] theorem protocolObservationObject_edge (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input)
    {source target : input.schema.Vertex} (edge : input.schema.Edge source target)
    (state : object.State source) :
    (protocolObservationObject input object).state.map
      (input.schema.edgeMorphism edge) state =
        IndependentProtocolPrimitiveReconstruction.assembleEdge object edge state := rfl

@[simp] theorem protocolObservationObject_observe (input : ProtocolFamilyInput.{u})
    (object : IndependentProtocolPrimitiveReconstruction.Object input)
    (vertex : input.schema.Vertex) (state : object.State vertex) :
    (protocolObservationObject input object).observe.app
      (input.schema.vertexObject vertex) state =
        IndependentProtocolPrimitiveReconstruction.assembleObservation object vertex state := rfl

/-- One primitive edge-preservation formula yields its generator square. -/
private theorem protocolPrimitiveEdgeSquare (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) {v w : input.schema.Vertex}
    (edge : input.schema.Edge v w) :
    morphism.component w ∘
        IndependentProtocolPrimitiveReconstruction.assembleEdge source edge =
      IndependentProtocolPrimitiveReconstruction.assembleEdge target edge ∘
        morphism.component v := by
  funext state
  let image := morphism.component v state
  let sourceNext := IndependentProtocolPrimitiveReconstruction.assembleEdge source edge state
  let targetNext := IndependentProtocolPrimitiveReconstruction.assembleEdge target edge image
  apply (morphism.edge_iff w sourceNext targetNext).mp
  exact ((IndependentProtocolPrimitiveReconstruction.edgePreservationFormula_evaluate_iff_raw
    source.table target.table morphism.table edge state image sourceNext targetNext).mp
      (morphism.edge_formula edge state image sourceNext targetNext)).2.2.2.2
    ⟨⟨(morphism.edge_iff v state image).mpr rfl,
        (IndependentProtocolPrimitiveReconstruction.edge_edge_iff
          source edge state sourceNext).mpr rfl⟩,
      (IndependentProtocolPrimitiveReconstruction.edge_edge_iff
        target edge image targetNext).mpr rfl⟩

/-- One primitive observation-preservation formula yields its visible square. -/
private theorem protocolPrimitiveObserveSquare (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex) :
    IndependentProtocolPrimitiveReconstruction.assembleObservation target vertex ∘
        morphism.component vertex =
      IndependentProtocolPrimitiveReconstruction.assembleObservation source vertex := by
  funext state
  let image := morphism.component vertex state
  let value := IndependentProtocolPrimitiveReconstruction.assembleObservation source vertex state
  apply (IndependentProtocolPrimitiveReconstruction.observe_edge_iff
    target vertex image value).mp
  exact ((IndependentProtocolPrimitiveReconstruction.observationPreservationFormula_evaluate_iff_raw
    source.table target.table morphism.table vertex state image value).mp
      (morphism.observation_formula vertex state image value)).2.2
    ⟨(morphism.edge_iff vertex state image).mpr rfl,
      (IndependentProtocolPrimitiveReconstruction.observe_edge_iff
        source vertex state value).mpr rfl⟩

/-- The edge squares extend to every free path directly from the primitive
graph formulas. -/
private noncomputable def protocolPrimitivePathNat (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) :
    IndependentProtocolPrimitiveReconstruction.assembledPathFunctor source ⟶
      IndependentProtocolPrimitiveReconstruction.assembledPathFunctor target :=
  Paths.liftNatTrans morphism.component (protocolPrimitiveEdgeSquare input morphism)

/-- A primitive Hom gives the state transformation by its directed vertex
graphs.  Naturality across quotient paths follows from the generator
preservation formulas; the data field itself uses no complete assembler. -/
noncomputable def protocolObservationMap (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) :
    protocolObservationObject input source ⟶
      protocolObservationObject input target where
  stateMap :=
    { app := fun execution => morphism.component execution.as
      naturality := by
        intro first second arrow
        apply CategoryTheory.Quotient.induction (r := input.schema.pathRelation)
          (P := fun {a b} path =>
            (IndependentProtocolPrimitiveReconstruction.assembledFunctor source).map path ≫
              morphism.component b.as =
                morphism.component a.as ≫
                  (IndependentProtocolPrimitiveReconstruction.assembledFunctor target).map path)
        intro first second path
        exact (protocolPrimitivePathNat input morphism).naturality path }
  observe_square := by
    ext execution state
    exact congrFun (protocolPrimitiveObserveSquare input morphism execution.as) state

@[simp] theorem protocolObservationMap_state (input : ProtocolFamilyInput.{u})
    {source target : IndependentProtocolPrimitiveReconstruction.Object input}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (state : source.State vertex) :
    (protocolObservationMap input morphism).stateMap.app
      (input.schema.vertexObject vertex) state = morphism.component vertex state := rfl

/-- Direct protocol observation projection on primitive objects and Hom
graphs.  Composition is verified at each vertex of the quotient category. -/
noncomputable def protocolObservationLocal (input : ProtocolFamilyInput.{u}) :
    IndependentProtocolPrimitiveReconstruction.Object input ⥤
      ProtocolObservationSlice input where
  obj := protocolObservationObject input
  map := protocolObservationMap input
  map_id object := by
    apply ProtocolObservationSlice.Hom.ext
    apply NatTrans.ext
    funext execution state
    exact congrFun (protocolPrimitiveMap_id input object execution.as) state
  map_comp first second := by
    apply ProtocolObservationSlice.Hom.ext
    apply NatTrans.ext
    funext execution state
    exact congrFun (protocolPrimitiveMap_comp input first second execution.as) state

private theorem lensReadCarrier (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    (readObject lens).Carrier = lens.Carrier := rfl

private theorem lensReadGet (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    assembleGet (readObject lens) = lens.get := by
  exact IndependentCarrierGraph.assemble_read _ _ lens.get

/-- Primitive lens get graphs agree with the original get slice, naturally
in every semantic lens morphism. -/
noncomputable def lensObservationReadingIso (input : LensFamilyInput.{u}) :
    IndependentLensPrimitiveReconstruction.readingFunctor input ⋙
      lensObservationLocal input ≅ lensObservationNative input :=
  NatIso.ofComponents (fun lens =>
    { hom :=
        { toFun := id
          get_naturality := fun state =>
            (congrFun (lensReadGet input lens) state).symm }
      inv :=
        { toFun := id
          get_naturality := fun state =>
            congrFun (lensReadGet input lens) state }
      hom_inv_id := by apply LensGetSlice.Hom.ext; funext state; rfl
      inv_hom_id := by apply LensGetSlice.Hom.ext; funext state; rfl }) (by
    intro source target morphism
    apply LensGetSlice.Hom.ext
    funext state
    change (IndependentLensPrimitiveReconstruction.readHom morphism).toFun state =
      morphism.toFun state
    exact congrFun (IndependentCarrierGraph.assemble_read source.Carrier
      target.Carrier morphism.toFun) state)

/-- The quotient-path observation projection of a read primitive protocol
agrees naturally with the native state and observation transformation. -/
noncomputable def protocolObservationReadingIso
    (input : ProtocolFamilyInput.{u}) :
    IndependentProtocolPrimitiveReconstruction.readingFunctor input ⋙
      protocolObservationLocal input ≅ protocolObservationNative input :=
  NatIso.ofComponents (fun realization =>
    (protocolObservationNative input).mapIso
      (IndependentProtocolPrimitiveReconstruction.assembleObjectReadIso realization)) (by
    intro source target morphism
    apply ProtocolObservationSlice.Hom.ext
    apply NatTrans.ext
    funext execution state
    change (IndependentProtocolPrimitiveReconstruction.readHom morphism).component
      execution.as state =
        (ProtocolRealization.res morphism).component execution.as state
    exact congrFun (IndependentCarrierGraph.assemble_read _ _
      ((ProtocolRealization.res morphism).component execution.as)) state)

private def lensSourceToNative (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    LensLocalSource (readObject lens).Carrier input.View → LensAATSource lens
  | .point => .point
  | .state value => .state value
  | .view value => .view value
  | .write state view => .write state view

private def lensSourceFromNative (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    LensAATSource lens → LensLocalSource (readObject lens).Carrier input.View
  | .point => .point
  | .state value => .state value
  | .view value => .view value
  | .write state view => .write state view

/-- The A1 source carrier of a read primitive lens is canonically equivalent
to the original four-summand source, with its point and all roles preserved. -/
def lensSourceEquiv (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    LensLocalSource (readObject lens).Carrier input.View ≃ LensAATSource lens where
  toFun := lensSourceToNative input lens
  invFun := lensSourceFromNative input lens
  left_inv source := by cases source <;> rfl
  right_inv source := by cases source <;> rfl

/-- The local pointed doctrine read from a semantic lens and its native A1
pointed doctrine are isomorphic by the explicit constructor equivalence. -/
noncomputable def lensBottomReadingComponent (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    lensBottomObject input (readObject lens) ≅
      (lensBottomNative input).obj lens where
  hom :=
    { doctrineHom :=
        { sourceMap := lensSourceEquiv input lens
          atomEquiv := Equiv.refl _
          normalize_eq _ := rfl
          extraction_iff source atom := by cases source <;> exact Iff.rfl }
      source_eq := rfl }
  inv :=
    { doctrineHom :=
        { sourceMap := (lensSourceEquiv input lens).symm
          atomEquiv := Equiv.refl _
          normalize_eq _ := rfl
          extraction_iff source atom := by cases source <;> exact Iff.rfl }
      source_eq := rfl }
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      cases source <;> rfl
    · rfl
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      cases source <;> rfl
    · rfl

/-- The explicit A1 source equivalence intertwines every original lens state
map with its primitive directed graph, naturally in arbitrary Homs. -/
noncomputable def lensBottomReadingIso (input : LensFamilyInput.{u}) :
    IndependentLensPrimitiveReconstruction.readingFunctor input ⋙
      lensBottomLocal input ≅ lensBottomNative input :=
  NatIso.ofComponents (lensBottomReadingComponent input) (by
    intro source target morphism
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      cases role with
      | point => rfl
      | state value =>
          exact congrArg LensAATSource.state
            (congrFun (IndependentCarrierGraph.assemble_read source.Carrier
              target.Carrier morphism.toFun) value)
      | view value => rfl
      | write state view =>
          exact congrArg (fun image => LensAATSource.write image view)
            (congrFun (IndependentCarrierGraph.assemble_read source.Carrier
              target.Carrier morphism.toFun) state)
    · rfl)

private def protocolSourceToNative (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation) :
    ProtocolLocalSource input (IndependentProtocolPrimitiveReconstruction.readObject
      realization) → ProtocolAATSource realization
  | .point => .point
  | .state vertex value => .state vertex value
  | .step edge value => .step edge value

private def protocolSourceFromNative (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation) :
    ProtocolAATSource realization →
      ProtocolLocalSource input (IndependentProtocolPrimitiveReconstruction.readObject
        realization)
  | .point => .point
  | .state vertex value => .state vertex value
  | .step edge value => .step edge value

/-- The protocol A1 source after primitive reading is constructorwise
equivalent to the native source at every vertex and named step. -/
def protocolSourceEquiv (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation) :
    ProtocolLocalSource input (IndependentProtocolPrimitiveReconstruction.readObject
      realization) ≃ ProtocolAATSource realization where
  toFun := protocolSourceToNative input realization
  invFun := protocolSourceFromNative input realization
  left_inv source := by cases source <;> rfl
  right_inv source := by cases source <;> rfl

/-- Constructorwise source transport identifies the local and native pointed
protocol doctrines while retaining the original exact extraction laws. -/
noncomputable def protocolBottomReadingComponent (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation) :
    protocolBottomObject input
      (IndependentProtocolPrimitiveReconstruction.readObject realization) ≅
      (protocolBottomNative input).obj realization where
  hom :=
    { doctrineHom :=
        { sourceMap := protocolSourceEquiv input realization
          atomEquiv := Equiv.refl _
          normalize_eq _ := rfl
          extraction_iff source atom := by cases source <;> exact Iff.rfl }
      source_eq := rfl }
  inv :=
    { doctrineHom :=
        { sourceMap := (protocolSourceEquiv input realization).symm
          atomEquiv := Equiv.refl _
          normalize_eq _ := rfl
          extraction_iff source atom := by cases source <;> exact Iff.rfl }
      source_eq := rfl }
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      cases source <;> rfl
    · rfl
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext source
      cases source <;> rfl
    · rfl

/-- Primitive vertex maps intertwine the original protocol A1 source maps,
naturally for arbitrary observation-preserving protocol Homs. -/
noncomputable def protocolBottomReadingIso (input : ProtocolFamilyInput.{u}) :
    IndependentProtocolPrimitiveReconstruction.readingFunctor input ⋙
      protocolBottomLocal input ≅ protocolBottomNative input :=
  NatIso.ofComponents (protocolBottomReadingComponent input) (by
    intro source target morphism
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · funext role
      cases role with
      | point => rfl
      | state vertex value =>
          exact congrArg (ProtocolAATSource.state vertex)
            (congrFun (IndependentCarrierGraph.assemble_read _ _
              ((ProtocolRealization.res morphism).component vertex)) value)
      | step edge value =>
          exact congrArg (ProtocolAATSource.step edge)
            (congrFun (IndependentCarrierGraph.assemble_read _ _
              ((ProtocolRealization.res morphism).component _)) value)
    · rfl)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionCS

end AAT.AG.LocalSemanticReconstruction.G124ProjectionCS
