import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedDirectedPackage
import Formal.Util.AssertStandardAxioms

/-!
# Independent operation-level readback from generated packages

The morphism interfaces below are not indexed by a pre-existing primitive
forward morphism and do not store a semantic Hom.  Their only computational
fields are the CS carrier maps; their laws are stated through the selected
Extension payload decoded from the actual generated core context.  From those
fields we reconstruct the primitive forward interface, every Cycle 175
generated geometry component, and the independently defined CS semantic Hom.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-! ## Lens -/

/-- An AAT-facing lens package morphism with no stored `LensAATForwardMorphism`
or semantic Hom.  The same state map occurs in both generated-payload laws. -/
@[ext]
structure LensAATIndependentGeneratedPackageHom
    (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference) where
  stateMap : X.Carrier → Y.Carrier
  get_map : ∀ state,
    (lensAATGeneratedExtensionPayload input Y).1.down.get (stateMap state) =
      (lensAATGeneratedExtensionPayload input X).1.down.get state
  put_map : ∀ state view,
    stateMap ((lensAATGeneratedExtensionPayload input X).1.down.put state view) =
      (lensAATGeneratedExtensionPayload input Y).1.down.put (stateMap state) view

namespace LensAATIndependentGeneratedPackageHom

/-- Reconstruct the primitive named-operation morphism from the independent
generated-payload fields. -/
def toForwardMorphism {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (h : LensAATIndependentGeneratedPackageHom input X Y) :
    LensAATForwardMorphism X Y where
  stateMap := h.stateMap
  get_naturality := by
    simpa using h.get_map
  put_naturality := by
    simpa using h.put_map

/-- Translate the primitive interface to the independent generated-payload
package.  No geometry certificate is accepted. -/
def ofForwardMorphism {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    LensAATIndependentGeneratedPackageHom input X Y where
  stateMap := f.stateMap
  get_map := (lensAATGeneratedExtensionCoherence input f).get_map
  put_map := (lensAATGeneratedExtensionCoherence input f).put_map

@[simp] theorem toForwardMorphism_ofForwardMorphism
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    (ofForwardMorphism (input := input) f).toForwardMorphism = f := by
  ext state
  rfl

@[simp] theorem ofForwardMorphism_toForwardMorphism
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (h : LensAATIndependentGeneratedPackageHom input X Y) :
    ofForwardMorphism (input := input) h.toForwardMorphism = h := by
  ext state
  rfl

/-- Exact equivalence with the primitive operation interface, proved from all
stored computational fields rather than a projected index. -/
def forwardMorphismEquiv (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference) :
    LensAATIndependentGeneratedPackageHom input X Y ≃
      LensAATForwardMorphism X Y where
  toFun := toForwardMorphism
  invFun := ofForwardMorphism (input := input)
  left_inv := ofForwardMorphism_toForwardMorphism
  right_inv := toForwardMorphism_ofForwardMorphism

/-- Independent semantic readback. -/
def toSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (h : LensAATIndependentGeneratedPackageHom input X Y) : X ⟶ Y :=
  h.toForwardMorphism.toSemanticHom

/-- Forward translation from every independent semantic lens morphism. -/
def ofSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (f : X ⟶ Y) : LensAATIndependentGeneratedPackageHom input X Y :=
  ofForwardMorphism (input := input) (LensAATForwardMorphism.ofSemanticHom f)

@[simp] theorem toSemanticHom_ofSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (f : X ⟶ Y) :
    (ofSemanticHom (input := input) f).toSemanticHom = f := by
  simp [toSemanticHom, ofSemanticHom]

@[simp] theorem ofSemanticHom_toSemanticHom {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (h : LensAATIndependentGeneratedPackageHom input X Y) :
    ofSemanticHom (input := input) h.toSemanticHom = h := by
  simp [toSemanticHom, ofSemanticHom]

/-- The complete independent lens Hom correspondence. -/
def semanticHomEquiv (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference) :
    LensAATIndependentGeneratedPackageHom input X Y ≃ (X ⟶ Y) where
  toFun := toSemanticHom
  invFun := ofSemanticHom (input := input)
  left_inv := ofSemanticHom_toSemanticHom
  right_inv := toSemanticHom_ofSemanticHom

/-- All generated geometry fields are reconstructed from the operation-level
package; none is stored as a certificate. -/
noncomputable def toDirectedPackage {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference}
    (h : LensAATIndependentGeneratedPackageHom input X Y) :
    LensAATGeneratedDirectedPackage input h.toForwardMorphism :=
  lensAATGeneratedDirectedPackage input h.toForwardMorphism

end LensAATIndependentGeneratedPackageHom

/-! ## Protocol -/

/-- An AAT-facing protocol package morphism containing one vertexwise state
map and the generated-payload equations for every named edge and observation.
No primitive or semantic morphism is stored. -/
@[ext]
structure ProtocolAATIndependentGeneratedPackageHom
    (input : ProtocolFamilyInput.{u})
    (X Y : ProtocolRealization input.schema input.observation) where
  stateMap : ∀ vertex, X.State vertex → Y.State vertex
  edge_map : ∀ {source target} (edge : input.schema.Edge source target)
      (state : X.State source),
    stateMap target
        ((protocolAATGeneratedExtensionPayload input X).1.down.edgeAction edge state) =
      (protocolAATGeneratedExtensionPayload input Y).1.down.edgeAction edge
        (stateMap source state)
  observation_map : ∀ vertex (state : X.State vertex),
    (protocolAATGeneratedExtensionPayload input Y).1.down.observe vertex
        (stateMap vertex state) =
      (protocolAATGeneratedExtensionPayload input X).1.down.observe vertex state

namespace ProtocolAATIndependentGeneratedPackageHom

def toForwardMorphism {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (h : ProtocolAATIndependentGeneratedPackageHom input X Y) :
    ProtocolAATForwardMorphism X Y where
  stateMap := h.stateMap
  edge_naturality := by
    intro source target edge state
    simpa using h.edge_map edge state
  observation_naturality := by
    intro vertex state
    simpa using h.observation_map vertex state

def ofForwardMorphism {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    ProtocolAATIndependentGeneratedPackageHom input X Y where
  stateMap := f.stateMap
  edge_map := (protocolAATGeneratedExtensionCoherence input f).edge_map
  observation_map :=
    (protocolAATGeneratedExtensionCoherence input f).observation_map

@[simp] theorem toForwardMorphism_ofForwardMorphism
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    (ofForwardMorphism (input := input) f).toForwardMorphism = f := by
  ext vertex state
  rfl

@[simp] theorem ofForwardMorphism_toForwardMorphism
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (h : ProtocolAATIndependentGeneratedPackageHom input X Y) :
    ofForwardMorphism (input := input) h.toForwardMorphism = h := by
  ext vertex state
  rfl

def forwardMorphismEquiv (input : ProtocolFamilyInput.{u})
    (X Y : ProtocolRealization input.schema input.observation) :
    ProtocolAATIndependentGeneratedPackageHom input X Y ≃
      ProtocolAATForwardMorphism X Y where
  toFun := toForwardMorphism
  invFun := ofForwardMorphism (input := input)
  left_inv := ofForwardMorphism_toForwardMorphism
  right_inv := toForwardMorphism_ofForwardMorphism

/-- Read back a complete natural transformation on every quotient execution
from the vertex maps and named generator squares. -/
def toSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (h : ProtocolAATIndependentGeneratedPackageHom input X Y) : X ⟶ Y :=
  h.toForwardMorphism.toSemanticHom

def ofSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (f : X ⟶ Y) : ProtocolAATIndependentGeneratedPackageHom input X Y :=
  ofForwardMorphism (input := input) (ProtocolAATForwardMorphism.ofSemanticHom f)

@[simp] theorem toSemanticHom_ofSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (f : X ⟶ Y) :
    (ofSemanticHom (input := input) f).toSemanticHom = f := by
  simp [toSemanticHom, ofSemanticHom]

@[simp] theorem ofSemanticHom_toSemanticHom {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (h : ProtocolAATIndependentGeneratedPackageHom input X Y) :
    ofSemanticHom (input := input) h.toSemanticHom = h := by
  simp [toSemanticHom, ofSemanticHom]

def semanticHomEquiv (input : ProtocolFamilyInput.{u})
    (X Y : ProtocolRealization input.schema input.observation) :
    ProtocolAATIndependentGeneratedPackageHom input X Y ≃ (X ⟶ Y) where
  toFun := toSemanticHom
  invFun := ofSemanticHom (input := input)
  left_inv := ofSemanticHom_toSemanticHom
  right_inv := toSemanticHom_ofSemanticHom

/-- Reconstruct all generated protocol geometry fields from the independent
operation-level package. -/
noncomputable def toDirectedPackage {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation}
    (h : ProtocolAATIndependentGeneratedPackageHom input X Y) :
    ProtocolAATGeneratedDirectedPackage input h.toForwardMorphism :=
  protocolAATGeneratedDirectedPackage input h.toForwardMorphism

end ProtocolAATIndependentGeneratedPackageHom

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
