import Formal.AG.Site.Basic

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

end ArchitectureContext

/--
II.定義4.1 / §5: a readable context morphism from a local context to the
context it reads into.

The morphism keeps the minimal data explicit: local support and axes map into
the target reading, while target observables restrict back to local
observables. The proposition fields record the selected role assumptions used
by later category, coverage, and sheaf constructions.
-/
structure ContextMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (source target : ArchitectureContext A) where
  supportMap : source.Support -> target.Support
  axisMap : source.Axis -> target.Axis
  observableRestrict : target.Observable -> source.Observable
  supportReadable : Prop
  axisReadable : Prop
  observableFunctorial : Prop
  nonGenerating : Prop
  axisForgetting : Prop
  supportRefinement : Prop
  axisRefinement : Prop
  baseChangeCompatible : Prop

namespace ContextMorphism

/-- II.§5.1: restriction preserves readable support, axes, and observables. -/
def IsRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.supportReadable ∧ f.axisReadable ∧ f.observableFunctorial ∧ f.nonGenerating

/-- II.§5.2: projection is restriction plus selected axis forgetting. -/
def IsProjection {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.axisForgetting

/-- II.§5.3: refinement is restriction plus support and axis refinement. -/
def IsRefinement {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.supportRefinement ∧ f.axisRefinement

/-- II.§5.4: base change is restriction compatible with the selected pullback reading. -/
def IsBaseChange {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {source target : ArchitectureContext A}
    (f : ContextMorphism source target) : Prop :=
  f.IsRestriction ∧ f.baseChangeCompatible

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
