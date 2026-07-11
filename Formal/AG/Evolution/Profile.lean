import Formal.AG.Evolution.TraceCategory

noncomputable section

namespace AAT.AG
namespace Evolution

universe u v w x y z

/-!
Part IX R1 / AC2--AC3 evolution profile and geometry surface.

An evolution profile fixes a static geometry universe, a measurement profile,
and one selected trace category. All later temporal laws and obstruction
readings are relative to this chosen profile.
-/

/--
IX.§1 / R1: evolution profile for the selected Part IX trace layer.

The profile carries the static geometry universe and selected trace. It does
not assert anything about unselected events, external runtime time, or future
paths outside the trace category.
-/
structure EvolutionProfile where
  BaseGeometry : Type u
  BaseMorphism : BaseGeometry -> BaseGeometry -> Type v
  baseId : (X : BaseGeometry) -> BaseMorphism X X
  baseComp :
    {X Y Z : BaseGeometry} ->
      BaseMorphism X Y -> BaseMorphism Y Z -> BaseMorphism X Z
  measurementProfile : Measurement.MeasurementProfile.{w, x}
  trace : TraceCategory.{y, z}
  selectedOperations : Type (max u v)
  selectedStateFamily : trace.Obj -> Type (max w x y z)
  selectedTemporalLaws : Type (max y z)
  selectedCoefficientProfile : Type (max w x)

namespace EvolutionProfile

/-- IX.§1: read the selected trace category of an evolution profile. -/
def traceCategory (E : EvolutionProfile.{u, v, w, x, y, z}) :
    TraceCategory.{y, z} :=
  E.trace

/-- IX.§1: read the selected measurement profile of an evolution profile. -/
def measurement (E : EvolutionProfile.{u, v, w, x, y, z}) :
    Measurement.MeasurementProfile.{w, x} :=
  E.measurementProfile

/--
IX.Principle 2.2 boundary: selected trace relativity.

This is a documentation-level boundary record, not a theorem about unselected
events. It only exposes the trace category already fixed by the profile.
-/
structure TraceRelativity (E : EvolutionProfile.{u, v, w, x, y, z}) where
  selectedTrace : TraceCategory.{y, z}
  selectedTrace_eq : selectedTrace = E.trace

/-- IX.Principle 2.2: read the selected trace-relativity boundary. -/
def traceRelativityBoundary (E : EvolutionProfile.{u, v, w, x, y, z}) :
    E.TraceRelativity :=
  { selectedTrace := E.trace
    selectedTrace_eq := rfl }

end EvolutionProfile

/--
IX.§1 / AC3: evolution geometry over the selected trace category.

This is a functor-like surface from `Tr_E` to the selected static geometry
universe. The base geometry is supplied by the profile, so this definition
does not claim a category of all possible AAT geometries.
-/
structure EvolutionGeometry (E : EvolutionProfile.{u, v, w, x, y, z}) where
  obj : E.trace.Obj -> E.BaseGeometry
  map : ∀ {t₀ t₁ : E.trace.Obj}, E.trace.Hom t₀ t₁ -> E.BaseMorphism (obj t₀) (obj t₁)
  map_id : ∀ t : E.trace.Obj, map (E.trace.id t) = E.baseId (obj t)
  map_comp :
    ∀ {t₀ t₁ t₂ : E.trace.Obj} (f : E.trace.Hom t₀ t₁) (g : E.trace.Hom t₁ t₂),
      map (E.trace.comp f g) = E.baseComp (map f) (map g)

namespace EvolutionGeometry

variable {E : EvolutionProfile.{u, v, w, x, y, z}}

/-- IX.§1 / AC3: read the static geometry at a selected trace object. -/
def geometryAt (G : EvolutionGeometry E) (t : E.trace.Obj) : E.BaseGeometry :=
  G.obj t

/-- IX.§1 / AC3: selected trace identities map to selected base identities. -/
theorem map_identity (G : EvolutionGeometry E) (t : E.trace.Obj) :
    G.map (E.trace.id t) = E.baseId (G.obj t) :=
  G.map_id t

/-- IX.§1 / AC3: selected trace composition maps to selected base composition. -/
theorem map_composition (G : EvolutionGeometry E)
    {t₀ t₁ t₂ : E.trace.Obj} (f : E.trace.Hom t₀ t₁) (g : E.trace.Hom t₁ t₂) :
    G.map (E.trace.comp f g) = E.baseComp (G.map f) (G.map g) :=
  G.map_comp f g

end EvolutionGeometry

end Evolution
end AAT.AG
