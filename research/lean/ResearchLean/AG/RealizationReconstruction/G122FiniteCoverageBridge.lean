import ResearchLean.AG.RealizationReconstruction.G122FiniteTotalRestriction
import Formal.Util.AssertStandardAxioms

/-!
# Coverage consequences for finite G-122 core probes

Cycle 49 isolated finite observational agreement from equality of complete
morphisms.  This module proves the first noncircular direction needed by a
separation argument: if the selected points actually cover a source carrier,
then agreement on the corresponding restriction determines the whole map on
that carrier.

Coverage is not stored in a probe and is not asserted for the fixed G-123
inputs.  It is passed as an ordinary surjectivity premise and used to choose a
probe index for every source value.  The same premise also constructs a
`Finite` instance for the covered carrier.  Thus exhaustive finite point
coverage cannot be the final parameter-relative strategy for primitive
carriers that the fixed target permits to be infinite.

## Implementation notes

The bridge covers the seven nondependent outer-core maps: doctrine sources,
lower and upper Atoms, architecture objects, equation indices, invariant
indices, and signature axes.  Endpoint-dependent operations and coordinates,
equation-equivalence data, and geometry-local data need dependent coverage
statements and remain open.  None of the theorems concludes equality of the
complete Hom.
-/

namespace AAT.AG.RealizationReconstruction

universe u v

namespace G122FiniteTotalHomProbe

/-- Exhaustive finite selection of doctrine sources makes agreement determine
the complete lower source map. -/
theorem sourceMap_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.sourceValue) :
    first.base.base.doctrineHom.sourceMap =
      second.base.base.doctrineHom.sourceMap := by
  funext source
  obtain ⟨i, rfl⟩ := covers source
  exact agreement.source i

/-- Exhaustive finite Atom selection makes agreement determine the complete
lower Atom equivalence. -/
theorem lowerAtomEquiv_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.atomValue) :
    first.base.base.doctrineHom.atomEquiv =
      second.base.base.doctrineHom.atomEquiv := by
  apply Equiv.ext
  intro atom
  obtain ⟨i, rfl⟩ := covers atom
  exact agreement.lowerAtom i

/-- Exhaustive finite Atom selection makes agreement determine the complete
upper Atom equivalence independently of the lower map. -/
theorem upperAtomEquiv_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.atomValue) :
    first.base.upper.atomEquiv = second.base.upper.atomEquiv := by
  apply Equiv.ext
  intro atom
  obtain ⟨i, rfl⟩ := covers atom
  exact agreement.upperAtom i

/-- Exhaustive finite object selection makes agreement determine the complete
architecture-object map. -/
theorem objectMap_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.objectValue) :
    first.base.upper.objectMap = second.base.upper.objectMap := by
  funext object
  obtain ⟨i, rfl⟩ := covers object
  exact agreement.object i

/-- Exhaustive finite equation-index selection makes agreement determine the
complete equation-index map. -/
theorem equationMap_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.equationValue) :
    first.base.upper.equationMap = second.base.upper.equationMap := by
  funext equation
  obtain ⟨i, rfl⟩ := covers equation
  exact agreement.equation i

/-- Exhaustive finite invariant-index selection makes agreement determine the
complete invariant-index map. -/
theorem invariantMap_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.invariantValue) :
    first.base.upper.invariantMap = second.base.upper.invariantMap := by
  funext invariant
  obtain ⟨i, rfl⟩ := covers invariant
  exact agreement.invariant i

/-- Exhaustive finite axis selection makes agreement determine the complete
signature-axis map. -/
theorem axisMap_eq_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    {probe : G122FiniteTotalHomProbe Θ X Y}
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (agreement : Agreement probe first second)
    (covers : Function.Surjective probe.core.axisValue) :
    first.base.upper.axisMap = second.base.upper.axisMap := by
  funext axis
  obtain ⟨i, rfl⟩ := covers axis
  exact agreement.axis i

/-- A finite probe that exhaustively covers doctrine sources proves that the
source carrier is finite. -/
theorem finite_source_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y)
    (covers : Function.Surjective probe.core.sourceValue) :
    Finite (X.package Θ).core.reading.doctrine.Source :=
  Finite.of_surjective probe.core.sourceValue covers

/-- A finite probe that exhaustively covers primitive Atoms proves that the
Atom carrier is finite. -/
theorem finite_atom_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y)
    (covers : Function.Surjective probe.core.atomValue) :
    Finite Θ.Carrier.Atom :=
  Finite.of_surjective probe.core.atomValue covers

/-- A finite probe that exhaustively covers architecture objects proves that
their full carrier is finite. -/
theorem finite_object_of_surjective
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteTotalHomProbe Θ X Y)
    (covers : Function.Surjective probe.core.objectValue) :
    Finite (ArchitectureObject Θ.Carrier) :=
  Finite.of_surjective probe.core.objectValue covers

end G122FiniteTotalHomProbe

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
