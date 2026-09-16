import ResearchLean.AG.RealizationReconstruction.CSAATLawResidualTransport
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Generated forward AAT morphism interfaces for the two CS semantics

The primitive fields below are the preservation squares of the actual named
AAT operations constructed in Cycle 125.  They do not contain a semantic Hom,
an A1 map, a Law morphism, residual preservation, or a readback certificate.
From those operation squares this module reconstructs the original arbitrary
CS morphism, and then generates its A1 doctrine, Law-object, context, index,
coordinate, and residual components from the already proved constructors.

Thus the forward construction and the reverse recovery use the same named
operation data.  Complete coverage/overlap/coefficient geometry and readback
from that later complete-geometry morphism remain separate obligations.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation

universe u

/-! ## Lens named-operation morphisms -/

/-- Preservation data for the actual named AAT `get` and `put` operations.
The single `stateMap` occurs in both squares, so the two copies of the state
carrier cannot vary independently. -/
@[ext]
structure LensAATForwardMorphism {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) where
  stateMap : X.Carrier → Y.Carrier
  get_naturality : ∀ state,
    lensGetAATFunction Y (stateMap state) = lensGetAATFunction X state
  put_naturality : ∀ state view,
    stateMap (lensPutAATFunction X (state, view)) =
      lensPutAATFunction Y (stateMap state, view)

namespace LensAATForwardMorphism

/-- Recover the independently defined n1015 (L2) semantic morphism from the
two actual named-operation squares. -/
def toSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) : X ⟶ Y where
  toFun := f.stateMap
  get_naturality := f.get_naturality
  put_naturality := f.put_naturality

/-- Every arbitrary semantic lens morphism constructs the named-operation
forward interface; no invertibility or presentation membership is added. -/
def ofSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    LensAATForwardMorphism X Y where
  stateMap := f.toFun
  get_naturality := f.get_naturality
  put_naturality := f.put_naturality

/-- Reading back after forward translation recovers the whole semantic lens
morphism, not only its action on a selected generator. -/
@[simp] theorem toSemanticHom_ofSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    (ofSemanticHom f).toSemanticHom = f := by
  apply LensRealization.Hom.ext
  rfl

/-- Rebuilding the forward interface after readback recovers every primitive
field and square. -/
@[simp] theorem ofSemanticHom_toSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    ofSemanticHom f.toSemanticHom = f := by
  ext state
  rfl

/-- Exact correspondence between original lens morphisms and preservation of
the two actual named AAT operations. -/
def semanticHomEquiv {input : LensFamilyInput.{u}}
    (X Y : LensRealization input.View input.reference) :
    (X ⟶ Y) ≃ LensAATForwardMorphism X Y where
  toFun := ofSemanticHom
  invFun := toSemanticHom
  left_inv := toSemanticHom_ofSemanticHom
  right_inv := ofSemanticHom_toSemanticHom

/-- The A1 source map is generated from the named-operation interface. -/
def sourceMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) : LensAATSource X → LensAATSource Y :=
  lensAATSourceMap f.toSemanticHom

/-- The exact A1 doctrine map is generated, not accepted as a field. -/
def doctrineHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    ExactDoctrineHom (lensAATExtractionDoctrine X) (lensAATExtractionDoctrine Y) :=
  lensAATExactDoctrineHom f.toSemanticHom

/-- The raw Law morphism is generated from the same named-operation squares. -/
def lawHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensLawHom X.toLensData.toLawStructure Y.toLensData.toLawStructure :=
  f.toSemanticHom.toLawHom

/-- The all-context Law functor is generated from the operation interface. -/
noncomputable def lawContextFunctor {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :=
  lensLawContextFunctor f.lawHom

/-- The complete equation-index map is generated from the operation interface. -/
def lawIndexMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensLawIndex input.View X.Carrier → LensLawIndex input.View Y.Carrier :=
  lensLawIndexMap f.lawHom

/-- The equation-instance/Atom coordinate map is generated from the same data. -/
noncomputable def lawCoordinateMap {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensLawCoordinateRing input X.Carrier →+* LensLawCoordinateRing input Y.Carrier :=
  lensLawCoordinateMap input f.lawHom

/-- Source residual zero is transported by the generated Law and context
components; residual preservation is not a structure field. -/
theorem lawResidual_zero_map {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (lensLawObject input X.Carrier X.toLensData.toLawStructure)))
    (index : LensLawIndex input.View X.Carrier) (atom : LensAATAtom input)
    (hzero : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).equationResidual sourceContext
        (lensLawObject input X.Carrier X.toLensData.toLawStructure)
        (ULift.up index) atom = 0) :
    (lensLawEquationSystem input Y.Carrier
      Y.toLensData.toLawStructure).equationResidual
        ((f.lawContextFunctor).obj sourceContext)
        (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)
        (ULift.up (f.lawIndexMap index)) atom = 0 :=
  lensLawResidual_zero_map_contextFunctor input f.lawHom sourceContext index atom hzero

/-- Identity forward interface. -/
def id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) : LensAATForwardMorphism X X :=
  ofSemanticHom (𝟙 X)

/-- Composition is generated by semantic composition reconstructed from the
named-operation squares. -/
def comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    LensAATForwardMorphism X Z :=
  ofSemanticHom (f.toSemanticHom ≫ g.toSemanticHom)

/-- Translating the primitive identity interface recovers the semantic identity. -/
@[simp] theorem toSemanticHom_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    (id X).toSemanticHom = 𝟙 X :=
  toSemanticHom_ofSemanticHom _

/-- Translating primitive-interface composition recovers semantic composition. -/
@[simp] theorem toSemanticHom_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    (comp f g).toSemanticHom = f.toSemanticHom ≫ g.toSemanticHom :=
  toSemanticHom_ofSemanticHom _

/-- Reading back the semantic identity is the primitive identity interface. -/
@[simp] theorem ofSemanticHom_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    ofSemanticHom (𝟙 X) = id X :=
  rfl

/-- Readback takes semantic composition to primitive-interface composition. -/
@[simp] theorem ofSemanticHom_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofSemanticHom (f ≫ g) = comp (ofSemanticHom f) (ofSemanticHom g) := by
  simp [comp]

end LensAATForwardMorphism

/-! ## Protocol named-operation morphisms -/

/-- Preservation data for every actual named protocol edge and observation.
No all-path natural transformation or semantic Hom is stored. -/
@[ext]
structure ProtocolAATForwardMorphism {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation) where
  stateMap : ∀ vertex, X.State vertex → Y.State vertex
  edge_naturality : ∀ {source target} (edge : input.schema.Edge source target)
    (state : X.State source),
    stateMap target (protocolEdgeAATFunction X edge state) =
      protocolEdgeAATFunction Y edge (stateMap source state)
  observation_naturality : ∀ vertex (state : X.State vertex),
    protocolObserveAATFunction Y vertex (stateMap vertex state) =
      protocolObserveAATFunction X vertex state

namespace ProtocolAATForwardMorphism

/-- Convert named-operation squares to the independently defined generator map. -/
def toGeneratorMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) : ProtocolRealization.GeneratorMap X Y where
  component := a.stateMap
  edge_naturality := by
    intro source target edge
    funext state
    exact a.edge_naturality edge state
  observation_naturality := by
    intro vertex
    funext state
    exact a.observation_naturality vertex state

/-- Extend the named-operation squares to every quotient execution and recover
the original independent protocol Hom. -/
def toSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) : X ⟶ Y :=
  ProtocolRealization.ext a.toGeneratorMap

/-- Restrict every arbitrary semantic protocol Hom to the actual named AAT
operations; no invertibility or completed transformation is stored. -/
def ofSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    ProtocolAATForwardMorphism X Y where
  stateMap := protocolStateMap a
  edge_naturality := protocolEdge_square a
  observation_naturality vertex state := by
    symm
    exact protocolObservation_square a vertex state

/-- Readback after forward translation recovers the complete natural
transformation on every quotient execution. -/
@[simp] theorem toSemanticHom_ofSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (a : X ⟶ Y) :
    (ofSemanticHom a).toSemanticHom = a := by
  exact ProtocolRealization.ext_res a

/-- Forward translation after readback recovers every named edge and
observation component. -/
@[simp] theorem ofSemanticHom_toSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :
    ofSemanticHom a.toSemanticHom = a := by
  ext vertex state
  rfl

/-- Exact correspondence between complete protocol morphisms and preservation
of every actual named AAT edge and observation operation. -/
def semanticHomEquiv {input : ProtocolFamilyInput.{u}}
    (X Y : ProtocolRealization input.schema input.observation) :
    (X ⟶ Y) ≃ ProtocolAATForwardMorphism X Y where
  toFun := ofSemanticHom
  invFun := toSemanticHom
  left_inv := toSemanticHom_ofSemanticHom
  right_inv := ofSemanticHom_toSemanticHom

/-- The A1 source map is generated from the reconstructed complete Hom. -/
def sourceMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) : ProtocolAATSource X → ProtocolAATSource Y :=
  protocolAATSourceMap a.toSemanticHom

/-- The exact A1 doctrine map is generated from named operations. -/
def doctrineHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :
    ExactDoctrineHom (protocolAATExtractionDoctrine X)
      (protocolAATExtractionDoctrine Y) :=
  protocolAATExactDoctrineHom a.toSemanticHom

/-- The raw Law morphism is generated from the same edge and observation squares. -/
def lawHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :
    ProtocolLawHom X.toLawStructure Y.toLawStructure :=
  a.toSemanticHom.toLawHom

/-- The all-context Law functor is generated from named operations. -/
noncomputable def lawContextFunctor {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :=
  protocolLawContextFunctor a.lawHom

/-- The complete relation/observation index map is generated. -/
def lawIndexMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :
    ProtocolLawIndex X.State → ProtocolLawIndex Y.State :=
  protocolLawIndexMap a.lawHom

/-- The equation-instance/Atom polynomial map is generated. -/
noncomputable def lawCoordinateMap {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) :
    ProtocolLawCoordinateRing input X.State →+* ProtocolLawCoordinateRing input Y.State :=
  protocolLawCoordinateMap input a.lawHom

/-- Residual-zero preservation is derived from the named-operation interface. -/
theorem lawResidual_zero_map {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y)
    (sourceContext : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory
        (protocolLawObject input X.State X.toLawStructure)))
    (index : ProtocolLawIndex X.State) (atom : ProtocolAATAtom input)
    (hzero : (protocolLawEquationSystem input X.State
      X.toLawStructure).equationResidual sourceContext
        (protocolLawObject input X.State X.toLawStructure)
        (ULift.up index) atom = 0) :
    (protocolLawEquationSystem input Y.State
      Y.toLawStructure).equationResidual ((a.lawContextFunctor).obj sourceContext)
        (protocolLawObject input Y.State Y.toLawStructure)
        (ULift.up (a.lawIndexMap index)) atom = 0 :=
  protocolLawResidual_zero_map_contextFunctor input a.lawHom sourceContext index atom hzero

/-- Identity protocol forward interface. -/
def id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolAATForwardMorphism X X :=
  ofSemanticHom (𝟙 X)

/-- Composition of generated protocol interfaces. -/
def comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) (b : ProtocolAATForwardMorphism Y Z) :
    ProtocolAATForwardMorphism X Z :=
  ofSemanticHom (a.toSemanticHom ≫ b.toSemanticHom)

/-- Translating the primitive protocol identity recovers the semantic identity. -/
@[simp] theorem toSemanticHom_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    (id X).toSemanticHom = 𝟙 X :=
  toSemanticHom_ofSemanticHom _

/-- Translating primitive protocol composition recovers semantic composition. -/
@[simp] theorem toSemanticHom_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (a : ProtocolAATForwardMorphism X Y) (b : ProtocolAATForwardMorphism Y Z) :
    (comp a b).toSemanticHom = a.toSemanticHom ≫ b.toSemanticHom :=
  toSemanticHom_ofSemanticHom _

/-- Reading back the semantic identity is the primitive protocol identity. -/
@[simp] theorem ofSemanticHom_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    ofSemanticHom (𝟙 X) = id X :=
  rfl

/-- Protocol readback takes semantic composition to primitive composition. -/
@[simp] theorem ofSemanticHom_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    ofSemanticHom (f ≫ g) = comp (ofSemanticHom f) (ofSemanticHom g) := by
  simp [comp]

end ProtocolAATForwardMorphism

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
