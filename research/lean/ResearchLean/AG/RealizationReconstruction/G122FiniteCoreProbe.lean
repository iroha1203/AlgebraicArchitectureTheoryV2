import ResearchLean.AG.RealizationReconstruction.G122FiniteGeometryProbe
import Formal.Util.AssertStandardAxioms

/-!
# Finite source probes for the outer G-122 core maps

This module extends the finite restriction surface from the geometry layer to
the source map of `PackageTotalHom.base` and the outer map fields of
`PackageTotalHom.upper`.  A probe stores only finitely indexed source values:
sources, Atoms, architecture objects, equation indices, endpoint-typed
operations, invariant indices, signature axes, and coordinates on those axes.
It stores no completed morphism, target image, or extension certificate.

The restrictions apply every arbitrary generated-object `GeometryTotalHom` to
those source values.  Both the lower doctrine Atom map and the upper exact-core
Atom map are exposed, and their pointwise equality is derived from the actual
`PackageTotalHom.atomEquiv_eq` compatibility field.

## Implementation notes

This is still not the complete core restriction required for reconstruction.
In particular, the context-equivalence and observable-equivalence data inside
`EquationSystemExactTransport` are not sampled here, and no finite probe is
claimed to separate arbitrary maps.  The equation-index restriction below is
only one outer projection of that larger transport.
-/

namespace AAT.AG.RealizationReconstruction

open AtomFoundation GeometryTransport

universe u v

/-- Finite source points for the lower doctrine maps and outer exact-core map
fields of arbitrary generated G-122 morphisms. -/
structure G122FiniteCoreProbe (Θ : G122FamilyInput.{u, v})
    (X : G122GeneratedGeometryObject Θ) where
  /-- Number of selected extraction-doctrine source values. -/
  sourceCard : Nat
  /-- Selected source values for the lower exact doctrine map. -/
  sourceValue : Fin sourceCard → (X.package Θ).core.reading.doctrine.Source
  /-- Number of selected primitive Atoms. -/
  atomCard : Nat
  /-- Selected primitive Atoms, shared by the lower and upper Atom maps. -/
  atomValue : Fin atomCard → Θ.Carrier.Atom
  /-- Number of selected architecture objects. -/
  objectCard : Nat
  /-- Selected architecture objects for the upper object map. -/
  objectValue : Fin objectCard → ArchitectureObject Θ.Carrier
  /-- Number of selected equation indices. -/
  equationCard : Nat
  /-- Selected indices for the equation transport's index equivalence. -/
  equationValue : Fin equationCard →
    (X.package Θ).core.algebra.equationSystem.Index
  /-- Number of selected endpoint-typed operations. -/
  operationCard : Nat
  /-- Source endpoint of each selected operation. -/
  operationSource : Fin operationCard → ArchitectureObject Θ.Carrier
  /-- Target endpoint of each selected operation. -/
  operationTarget : Fin operationCard → ArchitectureObject Θ.Carrier
  /-- Selected operation at its exact source and target endpoints. -/
  operationValue : ∀ i, (X.package Θ).core.reading.operationReading.Op
    (operationSource i) (operationTarget i)
  /-- Number of selected invariant indices. -/
  invariantCard : Nat
  /-- Selected invariant indices. -/
  invariantValue : Fin invariantCard →
    (X.package Θ).core.reading.invariantReading.Index
  /-- Number of selected signature axes. -/
  axisCard : Nat
  /-- Selected signature axes. -/
  axisValue : Fin axisCard → (X.package Θ).core.reading.signatureReading.Axis
  /-- Number of selected coordinates on each selected axis. -/
  coordinateCard : Fin axisCard → Nat
  /-- Selected coordinates on each selected source axis. -/
  coordinateValue : ∀ i, Fin (coordinateCard i) →
    (X.package Θ).core.reading.signatureReading.Coordinate (axisValue i)

namespace G122FiniteCoreProbe

/-- Restrict the lower exact-doctrine source map. -/
noncomputable def sourceRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.sourceCard → (Y.package Θ).core.reading.doctrine.Source :=
  fun i => f.base.base.doctrineHom.sourceMap (probe.sourceValue i)

/-- Restrict the lower exact-doctrine Atom equivalence. -/
noncomputable def lowerAtomRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.atomCard → Θ.Carrier.Atom :=
  fun i => f.base.base.doctrineHom.atomEquiv (probe.atomValue i)

/-- Restrict the upper exact-core Atom equivalence. -/
noncomputable def upperAtomRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.atomCard → Θ.Carrier.Atom :=
  fun i => f.base.upper.atomEquiv (probe.atomValue i)

/-- Restrict the upper architecture-object map. -/
noncomputable def objectRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.objectCard → ArchitectureObject Θ.Carrier :=
  fun i => f.base.upper.objectMap (probe.objectValue i)

/-- Restrict the equation-index map supplied by the upper equation transport. -/
noncomputable def equationRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.equationCard → (Y.package Θ).core.algebra.equationSystem.Index :=
  fun i => f.base.upper.equationMap (probe.equationValue i)

/-- Restrict the endpoint-dependent upper operation map. -/
noncomputable def operationRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, (Y.package Θ).core.reading.operationReading.Op
      (f.base.upper.objectMap (probe.operationSource i))
      (f.base.upper.objectMap (probe.operationTarget i)) :=
  fun i => f.base.upper.operationMap (probe.operationValue i)

/-- Restrict the upper invariant-index map. -/
noncomputable def invariantRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.invariantCard → (Y.package Θ).core.reading.invariantReading.Index :=
  fun i => f.base.upper.invariantMap (probe.invariantValue i)

/-- Restrict the upper signature-axis map. -/
noncomputable def axisRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.axisCard → (Y.package Θ).core.reading.signatureReading.Axis :=
  fun i => f.base.upper.axisMap (probe.axisValue i)

/-- Restrict the dependent coordinate equivalence on every selected axis. -/
noncomputable def coordinateRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, Fin (probe.coordinateCard i) →
      (Y.package Θ).core.reading.signatureReading.Coordinate
        (f.base.upper.axisMap (probe.axisValue i)) :=
  fun i j => f.base.upper.coordinateEquiv (probe.axisValue i)
    (probe.coordinateValue i j)

/-- The two restricted Atom maps agree because the actual lower and upper
maps of `PackageTotalHom` are required to use the same Atom equivalence. -/
theorem lowerAtomRestriction_eq_upperAtomRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    lowerAtomRestriction probe f = upperAtomRestriction probe f := by
  funext i
  exact congrArg (fun equivalence => equivalence (probe.atomValue i))
    f.base.atomEquiv_eq |>.symm

/-- Lower source restriction follows actual composition pointwise. -/
theorem sourceRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.sourceCard) :
    sourceRestriction probe (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.base.doctrineHom.sourceMap (sourceRestriction probe first i) :=
  rfl

/-- Lower Atom restriction follows actual composition pointwise. -/
theorem lowerAtomRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.atomCard) :
    lowerAtomRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.base.doctrineHom.atomEquiv
        (lowerAtomRestriction probe first i) :=
  rfl

/-- Upper Atom restriction follows actual composition pointwise. -/
theorem upperAtomRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.atomCard) :
    upperAtomRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.atomEquiv (upperAtomRestriction probe first i) :=
  rfl

/-- Upper object restriction follows actual composition pointwise. -/
theorem objectRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.objectCard) :
    objectRestriction probe (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.objectMap (objectRestriction probe first i) :=
  rfl

/-- Equation-index restriction follows actual composition pointwise. -/
theorem equationRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.equationCard) :
    equationRestriction probe (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.equationMap (equationRestriction probe first i) :=
  rfl

/-- Endpoint-typed operation restriction follows actual composition
pointwise. -/
theorem operationRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.operationCard) :
    operationRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.operationMap (operationRestriction probe first i) :=
  rfl

/-- Invariant restriction follows actual composition pointwise. -/
theorem invariantRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.invariantCard) :
    invariantRestriction probe (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.invariantMap (invariantRestriction probe first i) :=
  rfl

/-- Axis restriction follows actual composition pointwise. -/
theorem axisRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.axisCard) :
    axisRestriction probe (G122GeneratedGeometryObject.comp Θ first second) i =
      second.base.upper.axisMap (axisRestriction probe first i) :=
  rfl

/-- Dependent coordinate restriction follows actual composition pointwise. -/
theorem coordinateRestriction_comp
    {Θ : G122FamilyInput.{u, v}} {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteCoreProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.axisCard) (j : Fin (probe.coordinateCard i)) :
    coordinateRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i j =
      second.base.upper.coordinateEquiv
        (first.base.upper.axisMap (probe.axisValue i))
        (coordinateRestriction probe first i j) :=
  rfl

end G122FiniteCoreProbe

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
