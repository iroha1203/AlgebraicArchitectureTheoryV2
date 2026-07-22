import Formal.AG.Atom.ArchitectureObject

namespace AAT.AG
namespace Site

universe u

/--
II.定義3.1: the minimal Architecture Context model over an architecture object.

The minimal reading records the carrier types for support, selected axes, and
observable data, together with the predicates that say which atoms, axes, and
observables are visible in the context.
-/
structure MinimalContext {U : AtomCarrier.{u}} (A : ArchitectureObject U) where
  Support : Type u
  Axis : Type u
  Observable : Type u
  supportReads : Support -> U.Atom -> Prop
  supportReads_objectFamily :
    ∀ {support atom}, supportReads support atom -> A.configuration.family.mem atom
  axisReads : Axis -> Prop
  observableReads : Observable -> Prop

/--
II.定義3.1: a general Architecture Context is an extension of the minimal
support / axis / observable reading.
-/
structure ArchitectureContext {U : AtomCarrier.{u}} (A : ArchitectureObject U) where
  minimal : MinimalContext A
  Extension : Type u
  extension : Extension

namespace ArchitectureContext

/-- II.定義3.1: read the minimal support carrier of a context. -/
def Support {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W : ArchitectureContext A) : Type u :=
  W.minimal.Support

/-- II.定義3.1: read the minimal axis carrier of a context. -/
def Axis {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W : ArchitectureContext A) : Type u :=
  W.minimal.Axis

/-- II.定義3.1: read the minimal observable carrier of a context. -/
def Observable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W : ArchitectureContext A) : Type u :=
  W.minimal.Observable

/-- II-3: every atom read by a context belongs to the selected object family. -/
theorem supportReads_objectFamily {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W : ArchitectureContext A) {support : W.Support} {atom : U.Atom}
    (h : W.minimal.supportReads support atom) :
    A.configuration.family.mem atom :=
  W.minimal.supportReads_objectFamily h

end ArchitectureContext

/-- II-3: support maps preserve selected Atom readings. -/
def SupportMapPreservesReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (supportMap : source.Support -> target.Support) : Prop :=
  ∀ {support atom}, source.minimal.supportReads support atom ->
    target.minimal.supportReads (supportMap support) atom

/-- II-3: axis maps preserve selected readable axes. -/
def AxisMapPreservesReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (axisMap : source.Axis -> target.Axis) : Prop :=
  ∀ {axis}, source.minimal.axisReads axis ->
    target.minimal.axisReads (axisMap axis)

/-- II-3: observable restriction is functorial on selected readable observables. -/
def ObservableRestrictionFunctorial {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (observableRestrict : target.Observable -> source.Observable) : Prop :=
  ∀ {observable}, target.minimal.observableReads observable ->
    source.minimal.observableReads (observableRestrict observable)

/--
II-3: a support map is non-generating when atoms read at its target image are
still atoms of the selected architecture object.
-/
def SupportMapNonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (supportMap : source.Support -> target.Support) : Prop :=
  ∀ {support atom}, target.minimal.supportReads (supportMap support) atom ->
    A.configuration.family.mem atom

/-- II-3: projection may forget axes only through the selected readable-axis map. -/
def AxisMapForgetsOnlyReadableAxes {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (axisMap : source.Axis -> target.Axis) : Prop :=
  ∀ {axis}, target.minimal.axisReads (axisMap axis) ->
    source.minimal.axisReads axis

/-- II-3: support refinement reflects selected support readings along the map. -/
def SupportMapReflectsReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (supportMap : source.Support -> target.Support) : Prop :=
  ∀ {support atom}, target.minimal.supportReads (supportMap support) atom ->
    source.minimal.supportReads support atom

/-- II-3: axis refinement reflects selected axis readings along the map. -/
def AxisMapReflectsReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (axisMap : source.Axis -> target.Axis) : Prop :=
  ∀ {axis}, target.minimal.axisReads (axisMap axis) ->
    source.minimal.axisReads axis

/-- II-3: support refinement is witnessed by preservation of support readings. -/
def SupportMapRefinesReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (supportMap : source.Support -> target.Support) : Prop :=
  SupportMapPreservesReads source target supportMap ∧
    SupportMapReflectsReads source target supportMap

/-- II-3: axis refinement is witnessed by preservation of axis readings. -/
def AxisMapRefinesReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (axisMap : source.Axis -> target.Axis) : Prop :=
  AxisMapPreservesReads source target axisMap ∧
    AxisMapReflectsReads source target axisMap

/-- II-3: base change compatibility is the selected support/axis/observable square. -/
def BaseChangeCompatibleReads {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A)
    (supportMap : source.Support -> target.Support)
    (axisMap : source.Axis -> target.Axis)
    (observableRestrict : target.Observable -> source.Observable) : Prop :=
  SupportMapRefinesReads source target supportMap ∧
    AxisMapRefinesReads source target axisMap ∧
      ObservableRestrictionFunctorial source target observableRestrict

/--
II.定義4.1 / §5: a readable context morphism from a local context to the
context it reads into.

The morphism keeps the minimal data explicit: local support and axes map into
the target reading, while target observables restrict back to local
observables. Role predicates are defined below as concrete conditions over
these maps and the selected support, axis, observable, and object-family
readings.
-/
structure ContextMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A) where
  supportMap : source.Support -> target.Support
  axisMap : source.Axis -> target.Axis
  observableRestrict : target.Observable -> source.Observable

namespace ContextMorphism

/-- II-3: compatibility projection for the old support-readability role name. -/
def supportReadable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  SupportMapPreservesReads source target f.supportMap

/-- II-3: compatibility projection for the old axis-readability role name. -/
def axisReadable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  AxisMapPreservesReads source target f.axisMap

/-- II-3: compatibility projection for the old observable-functorial role name. -/
def observableFunctorial {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  ObservableRestrictionFunctorial source target f.observableRestrict

/-- II-3: compatibility projection for the old non-generation role name. -/
def nonGenerating {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  SupportMapNonGenerating source target f.supportMap

/-- II-3: compatibility projection for the old axis-forgetting role name. -/
def axisForgetting {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  AxisMapForgetsOnlyReadableAxes source target f.axisMap

/-- II-3: compatibility projection for the old support-refinement role name. -/
def supportRefinement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  SupportMapRefinesReads source target f.supportMap

/-- II-3: compatibility projection for the old axis-refinement role name. -/
def axisRefinement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  AxisMapRefinesReads source target f.axisMap

/-- II-3: compatibility projection for the old base-change role name. -/
def baseChangeCompatible {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  BaseChangeCompatibleReads source target f.supportMap f.axisMap
    f.observableRestrict

/-- II-3: concrete restriction role for a context morphism. -/
def ConcreteRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.supportReadable ∧ f.axisReadable ∧ f.observableFunctorial ∧
    f.nonGenerating

/-- II-3: concrete projection role for a context morphism. -/
def ConcreteProjection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.axisForgetting

/-- II-3: concrete refinement role for a context morphism. -/
def ConcreteRefinement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.supportRefinement ∧ f.axisRefinement

/-- II-3: concrete base-change role for a context morphism. -/
def ConcreteBaseChange {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.baseChangeCompatible

/-- II.§5.1: restriction preserves readable support, axes, and observables. -/
def IsRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.ConcreteRestriction

/-- II.§5.2: projection is restriction plus selected axis forgetting. -/
def IsProjection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.ConcreteProjection

/-- II.§5.3: refinement is restriction plus support and axis refinement. -/
def IsRefinement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.ConcreteRefinement

/-- II.§5.4: base change is restriction compatible with the selected pullback reading. -/
def IsBaseChange {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.ConcreteBaseChange

/-- II.§5.1: a restriction morphism records support readability. -/
theorem supportReadable_of_restriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRestriction) :
    f.supportReadable :=
  h.1

/-- II.§5.1: a restriction morphism records axis readability. -/
theorem axisReadable_of_restriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRestriction) :
    f.axisReadable :=
  h.2.1

/-- II.§5.1: a restriction morphism records functorial observable restriction. -/
theorem observableFunctorial_of_restriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRestriction) :
    f.observableFunctorial :=
  h.2.2.1

/-- II.§5.1 / 5.2 / 5.3: context morphisms do not create atoms. -/
theorem nonGenerating_of_restriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRestriction) :
    f.nonGenerating :=
  h.2.2.2

/-- II.§5.2: projection records that hidden axes are forgotten, not zero. -/
theorem axisForgetting_of_projection {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsProjection) :
    f.axisForgetting :=
  h.2

/-- II.§5.3: refinement records support refinement. -/
theorem supportRefinement_of_refinement {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRefinement) :
    f.supportRefinement :=
  h.2.1

/-- II.§5.3: refinement records axis refinement. -/
theorem axisRefinement_of_refinement {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsRefinement) :
    f.axisRefinement :=
  h.2.2

/-- II.§5.4: base change records compatibility with the selected pullback reading. -/
theorem baseChangeCompatible_of_baseChange {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {source target : ArchitectureContext A}
    {f : ContextMorphism source target} (h : f.IsBaseChange) :
    f.baseChangeCompatible :=
  h.2

end ContextMorphism

end Site
end AAT.AG
