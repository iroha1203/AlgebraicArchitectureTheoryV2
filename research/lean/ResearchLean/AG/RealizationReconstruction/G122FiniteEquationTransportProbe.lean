import ResearchLean.AG.RealizationReconstruction.G122FiniteCoreProbe
import Formal.Util.AssertStandardAxioms

/-!
# Finite probes for G-122 equation-transport maps

The outer core probe records equation-index images but not the context and
observable maps carried by `EquationSystemExactTransport`.  This module adds a
finite source-point interface for those maps.  A probe stores source-package
contexts, readable arrows between selected contexts, and observable values at
selected contexts.  It stores no target image or completed equivalence.

For an arbitrary generated-object `GeometryTotalHom`, the forward context
functor and observable equivalence are evaluated on a source probe.  The
inverse context functor is evaluated on an independently supplied probe for
the target package.  This preserves both directions of the actual context
equivalence without defining either direction from a decoder image.

## Implementation notes

The restrictions sample functor object/arrow maps and the forward functions of
the context-indexed ring equivalences.  They do not reconstruct the whole
`CategoryTheory.Equivalence`: unit/counit data and finite separation remain
open.  No inverse observable value is accepted as target-side probe data,
because its source context would itself depend on the morphism being observed.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory GeometryTransport

universe u v

/-- Finite context, readable-arrow, and observable source values for one
generated G-122 package. -/
structure G122FiniteEquationTransportProbe (Θ : G122FamilyInput.{u, v})
    (X : G122GeneratedGeometryObject Θ) where
  /-- Number of selected contexts. -/
  contextCard : Nat
  /-- Selected contexts of the package's generated core. -/
  contextValue : Fin contextCard →
    Site.ContextCategoryObject (X.package Θ).core.contextPreorder
  /-- Number of selected readable context arrows. -/
  arrowCard : Nat
  /-- Source-context index of each selected arrow. -/
  arrowSource : Fin arrowCard → Fin contextCard
  /-- Target-context index of each selected arrow. -/
  arrowTarget : Fin arrowCard → Fin contextCard
  /-- Selected readable arrow with its exact context endpoints. -/
  arrowValue : ∀ i, contextValue (arrowSource i) ⟶
    contextValue (arrowTarget i)
  /-- Number of selected observable values at each context. -/
  observableCard : Fin contextCard → Nat
  /-- Selected source observable values at each selected context. -/
  observableValue : ∀ i, Fin (observableCard i) →
    (X.package Θ).core.algebra.equationSystem.Observable (contextValue i)

namespace G122FiniteEquationTransportProbe

/-- Restrict the forward context functor to selected source contexts. -/
noncomputable def forwardContextRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.contextCard →
      Site.ContextCategoryObject (Y.package Θ).core.contextPreorder :=
  fun i => f.base.upper.equationTransport.contextForward
    (probe.contextValue i)

/-- Restrict the forward context functor to selected readable source arrows. -/
noncomputable def forwardArrowRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, forwardContextRestriction probe f (probe.arrowSource i) ⟶
      forwardContextRestriction probe f (probe.arrowTarget i) :=
  fun i => f.base.upper.equationTransport.contextForward_map
    (probe.arrowValue i)

/-- Restrict the inverse context functor to selected target contexts.  The
probe belongs to the target package and remains independent of the morphism. -/
noncomputable def backwardContextRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ Y)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.contextCard →
      Site.ContextCategoryObject (X.package Θ).core.contextPreorder :=
  fun i => f.base.upper.equationTransport.contextBackward
    (probe.contextValue i)

/-- Restrict the inverse context functor to selected readable target arrows. -/
noncomputable def backwardArrowRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ Y)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, backwardContextRestriction probe f (probe.arrowSource i) ⟶
      backwardContextRestriction probe f (probe.arrowTarget i) :=
  fun i => f.base.upper.equationTransport.contextBackward_map
    (probe.arrowValue i)

/-- Restrict the forward observable-ring equivalence to selected source
contexts and source observable values. -/
noncomputable def observableRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, Fin (probe.observableCard i) →
      (Y.package Θ).core.algebra.equationSystem.Observable
        (forwardContextRestriction probe f i) :=
  fun i j => f.base.upper.equationTransport.observableEquiv
    (probe.contextValue i) (probe.observableValue i j)

/-- The identity morphism leaves every selected forward context unchanged. -/
theorem forwardContextRestriction_id
    {Θ : G122FamilyInput.{u, v}} {X : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (i : Fin probe.contextCard) :
    forwardContextRestriction probe (G122GeneratedGeometryObject.id Θ X) i =
      probe.contextValue i :=
  rfl

/-- The identity morphism leaves every selected forward context arrow
unchanged. -/
theorem forwardArrowRestriction_id
    {Θ : G122FamilyInput.{u, v}} {X : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (i : Fin probe.arrowCard) :
    forwardArrowRestriction probe (G122GeneratedGeometryObject.id Θ X) i =
      probe.arrowValue i :=
  rfl

/-- The identity morphism leaves every selected backward context unchanged. -/
theorem backwardContextRestriction_id
    {Θ : G122FamilyInput.{u, v}} {X : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (i : Fin probe.contextCard) :
    backwardContextRestriction probe (G122GeneratedGeometryObject.id Θ X) i =
      probe.contextValue i :=
  rfl

/-- The identity morphism leaves every selected backward context arrow
unchanged. -/
theorem backwardArrowRestriction_id
    {Θ : G122FamilyInput.{u, v}} {X : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (i : Fin probe.arrowCard) :
    backwardArrowRestriction probe (G122GeneratedGeometryObject.id Θ X) i =
      probe.arrowValue i :=
  rfl

/-- The identity morphism leaves every selected observable unchanged. -/
theorem observableRestriction_id
    {Θ : G122FamilyInput.{u, v}} {X : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (i : Fin probe.contextCard) (j : Fin (probe.observableCard i)) :
    observableRestriction probe (G122GeneratedGeometryObject.id Θ X) i j =
      probe.observableValue i j :=
  rfl

/-- Forward context-object restriction follows actual composition. -/
theorem forwardContextRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) :
    forwardContextRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.equationTransport.contextForward
        (forwardContextRestriction probe first i) :=
  rfl

/-- Forward context-arrow restriction follows actual composition. -/
theorem forwardArrowRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.arrowCard) :
    forwardArrowRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.equationTransport.contextForward_map
        (forwardArrowRestriction probe first i) :=
  rfl

/-- Backward context-object restriction follows the reverse order of actual
inverse-functor composition. -/
theorem backwardContextRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ Z)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) :
    backwardContextRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      first.base.upper.equationTransport.contextBackward
        (backwardContextRestriction probe second i) :=
  rfl

/-- Backward context-arrow restriction follows the reverse order of actual
inverse-functor composition. -/
theorem backwardArrowRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ Z)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.arrowCard) :
    backwardArrowRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      first.base.upper.equationTransport.contextBackward_map
        (backwardArrowRestriction probe second i) :=
  rfl

/-- Observable restriction follows the context-indexed ring equivalences of
actual composition. -/
theorem observableRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteEquationTransportProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) (j : Fin (probe.observableCard i)) :
    observableRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i j =
      second.base.upper.equationTransport.observableEquiv
        (forwardContextRestriction probe first i)
        (observableRestriction probe first i j) :=
  rfl

end G122FiniteEquationTransportProbe

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
