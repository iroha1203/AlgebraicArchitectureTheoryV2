import Formal.Arch.Layering
import Formal.Arch.ThinCategory

namespace Formal.Arch

universe u

/--
Initial v2 definition: decomposability is strict layerability.

Other characterizations such as acyclicity, nilpotence, and finite propagation
are grown as theorems rather than folded into this definition.
-/
def Decomposable {C : Type u} (G : ArchGraph C) : Prop :=
  StrictLayered G

/-- The initial definition is definitionally the same as strict layerability. -/
theorem decomposable_iff_strictLayered {C : Type u} {G : ArchGraph C} :
    Decomposable G ↔ StrictLayered G :=
  Iff.rfl

/-- Decomposable graphs are acyclic under the initial definition. -/
theorem decomposable_acyclic {C : Type u} {G : ArchGraph C}
    (h : Decomposable G) : Acyclic G :=
  strictLayered_acyclic h

/-- Decomposable graphs have finite propagation under the initial definition. -/
theorem decomposable_finitePropagation {C : Type u} {G : ArchGraph C}
    (h : Decomposable G) : FinitePropagation G :=
  finitePropagation_of_strictLayered h

/-- Four-layer example used as the first positive decomposability witness. -/
inductive FourLayerComponent where
  | ui
  | service
  | domain
  | database
  deriving DecidableEq

namespace FourLayerComponent

/-- Dependencies flow from upper layers to lower layers. -/
inductive edge : FourLayerComponent → FourLayerComponent → Prop where
  | ui_service : edge ui service
  | service_domain : edge service domain
  | domain_database : edge domain database

/-- The sample four-layer graph. -/
def graph : ArchGraph FourLayerComponent where
  edge := edge

/-- Concrete layer assignment for the four-layer sample. -/
def layer : Layering FourLayerComponent
  | ui => 3
  | service => 2
  | domain => 1
  | database => 0

/-- The four-layer sample strictly decreases along dependencies. -/
theorem strictLayering : StrictLayering graph layer := by
  intro c d h
  cases h <;> decide

/-- The four-layer sample is decomposable. -/
theorem decomposable : Decomposable graph :=
  ⟨layer, strictLayering⟩

end FourLayerComponent

end Formal.Arch

