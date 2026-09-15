import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldComparisonIndex
import Formal.Util.AssertStandardAxioms

/-!
# Finite source probes for arbitrary G-122 geometry morphisms

This module takes a first finite restriction of the independent morphism space
fixed in `G122OriginalInput`.  A probe contains only finitely indexed points of
the source coefficient ring and of the source context-local support, axis, and
observable carriers.  It contains no morphism, target value, extension,
representability witness, or equality certificate.

Every arbitrary `GeometryTotalHom` between generated G-122 objects can be
restricted to those points.  The four restriction operations below expose the
map fields used by `GeomReadHom.ext`; coverage, overlap, raw compatibility, and
preservation laws are not added to the probe.  The composition laws show that
the recorded values are genuine evaluations of the original morphism rather
than an independently supplied table.

## Implementation notes

The probe is parameter-relative: its entries may refer to the original
possibly infinite G-122 data, while each displayed family is indexed by a
`Fin` type.  No converse extension or uniqueness theorem is asserted.  In
particular, equality of these finite restrictions need not imply equality of
the underlying morphisms, and this module does not yet restrict the
computational fields of `PackageTotalHom`.
-/

namespace AAT.AG.RealizationReconstruction

open GeometryTransport

universe u v

/-- A finite family of source points at which to observe the four map fields
used by `GeomReadHom.ext` for a generated G-122 morphism.  Only source data are
stored; no completed morphism or target image is a field. -/
structure G122FiniteGeometryProbe (Θ : G122FamilyInput.{u, v})
    (X : G122GeneratedGeometryObject Θ) where
  /-- Number of selected source coefficient values. -/
  coefficientCard : Nat
  /-- Selected source coefficient values. -/
  coefficientValue : Fin coefficientCard → (X.package Θ).Coefficient
  /-- Number of selected source contexts. -/
  contextCard : Nat
  /-- Selected source contexts. -/
  contextValue : Fin contextCard → (X.package Θ).site.category
  /-- Number of support values selected at each source context. -/
  supportCard : Fin contextCard → Nat
  /-- Selected support values at each source context. -/
  supportValue : ∀ i, Fin (supportCard i) → (contextValue i).ctx.Support
  /-- Number of axis values selected at each source context. -/
  axisCard : Fin contextCard → Nat
  /-- Selected axis values at each source context. -/
  axisValue : ∀ i, Fin (axisCard i) → (contextValue i).ctx.Axis
  /-- Number of observable values selected at each source context. -/
  observableCard : Fin contextCard → Nat
  /-- Selected observable values at each source context. -/
  observableValue : ∀ i, Fin (observableCard i) → (contextValue i).ctx.Observable

namespace G122FiniteGeometryProbe

/-- A nonempty one-context probe constructor.  Its four entries are supplied
from the source package and do not depend on a morphism or target package. -/
def singleLocal (Θ : G122FamilyInput.{u, v})
    (X : G122GeneratedGeometryObject Θ)
    (coefficient : (X.package Θ).Coefficient)
    (context : (X.package Θ).site.category)
    (support : context.ctx.Support) (axis : context.ctx.Axis)
    (observable : context.ctx.Observable) : G122FiniteGeometryProbe Θ X where
  coefficientCard := 1
  coefficientValue _ := coefficient
  contextCard := 1
  contextValue _ := context
  supportCard _ := 1
  supportValue _ _ := support
  axisCard _ := 1
  axisValue _ _ := axis
  observableCard _ := 1
  observableValue _ _ := observable

/-- Restrict the coefficient map of an arbitrary complete generated-object
morphism to the finitely selected source coefficients. -/
noncomputable def coefficientRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    Fin probe.coefficientCard → (Y.package Θ).Coefficient :=
  fun i => f.geometry.coefficientHom (probe.coefficientValue i)

/-- Restrict the support comparison of an arbitrary complete
generated-object morphism to the finitely selected context-local supports. -/
noncomputable def supportRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, Fin (probe.supportCard i) →
      (contextForward f.base (probe.contextValue i)).ctx.Support :=
  fun i j => f.geometry.supportComp (probe.contextValue i)
    (probe.supportValue i j)

/-- Restrict the axis comparison of an arbitrary complete generated-object
morphism to the finitely selected context-local axes. -/
noncomputable def axisRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, Fin (probe.axisCard i) →
      (contextForward f.base (probe.contextValue i)).ctx.Axis :=
  fun i j => f.geometry.axisComp (probe.contextValue i)
    (probe.axisValue i j)

/-- Restrict the observable comparison of an arbitrary complete
generated-object morphism to the finitely selected context-local
observables. -/
noncomputable def observableRestriction
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (f : G122GeneratedGeometryObject.Hom Θ X Y) :
    ∀ i, Fin (probe.observableCard i) →
      (contextForward f.base (probe.contextValue i)).ctx.Observable :=
  fun i j => f.geometry.observableComp (probe.contextValue i)
    (probe.observableValue i j)

/-- Coefficient restriction follows actual composition pointwise. -/
theorem coefficientRestriction_comp
    {Θ : G122FamilyInput.{u, v}}
    {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.coefficientCard) :
    coefficientRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i =
      second.geometry.coefficientHom (coefficientRestriction probe first i) :=
  rfl

/-- Support restriction follows actual composition pointwise. -/
theorem supportRestriction_comp
    {Θ : G122FamilyInput.{u, v}}
    {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) (j : Fin (probe.supportCard i)) :
    supportRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i j =
      second.geometry.supportComp
        (contextForward first.base (probe.contextValue i))
        (supportRestriction probe first i j) :=
  rfl

/-- Axis restriction follows actual composition pointwise. -/
theorem axisRestriction_comp
    {Θ : G122FamilyInput.{u, v}}
    {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) (j : Fin (probe.axisCard i)) :
    axisRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i j =
      second.geometry.axisComp
        (contextForward first.base (probe.contextValue i))
        (axisRestriction probe first i j) :=
  rfl

/-- Observable restriction follows actual composition pointwise. -/
theorem observableRestriction_comp
    {Θ : G122FamilyInput.{u, v}}
    {X Y Z : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    (first : G122GeneratedGeometryObject.Hom Θ X Y)
    (second : G122GeneratedGeometryObject.Hom Θ Y Z)
    (i : Fin probe.contextCard) (j : Fin (probe.observableCard i)) :
    observableRestriction probe
        (G122GeneratedGeometryObject.comp Θ first second) i j =
      second.geometry.observableComp
        (contextForward first.base (probe.contextValue i))
        (observableRestriction probe first i j) :=
  rfl

/-- A detected coefficient-restriction difference is a sound witness that
the original arbitrary complete morphisms differ.  No converse is claimed. -/
theorem hom_ne_of_coefficientRestriction_ne
    {Θ : G122FamilyInput.{u, v}} {X Y : G122GeneratedGeometryObject Θ}
    (probe : G122FiniteGeometryProbe Θ X)
    {first second : G122GeneratedGeometryObject.Hom Θ X Y}
    (different : coefficientRestriction probe first ≠
      coefficientRestriction probe second) : first ≠ second := by
  intro equal
  exact different (congrArg (coefficientRestriction probe) equal)

end G122FiniteGeometryProbe

/-! ## Restriction of the fixed finite-axis-fold comparison cases -/

/-- Source probes for the common direct-route endpoint of the three fixed
finite-axis-fold comparison cases. -/
abbrev FiniteAxisFoldGeometryProbe :=
  G122FiniteGeometryProbe finiteAxisFoldG122FamilyInput
    (.direct finiteAxisFoldG122CellInput)

/-- Observe the coefficient component of the actual comparison selected by a
fixed case index.  The comparison arrow is evaluated first and is not stored
in the probe. -/
noncomputable def finiteAxisFoldCoefficientRestriction
    (probe : FiniteAxisFoldGeometryProbe)
    (code : FiniteAxisFoldComparisonCode) :=
  probe.coefficientRestriction code.evaluate

/-- Observe the support component of the actual comparison selected by a
fixed case index. -/
noncomputable def finiteAxisFoldSupportRestriction
    (probe : FiniteAxisFoldGeometryProbe)
    (code : FiniteAxisFoldComparisonCode) :=
  probe.supportRestriction code.evaluate

/-- Observe the axis component of the actual comparison selected by a fixed
case index. -/
noncomputable def finiteAxisFoldAxisRestriction
    (probe : FiniteAxisFoldGeometryProbe)
    (code : FiniteAxisFoldComparisonCode) :=
  probe.axisRestriction code.evaluate

/-- Observe the observable component of the actual comparison selected by a
fixed case index. -/
noncomputable def finiteAxisFoldObservableRestriction
    (probe : FiniteAxisFoldGeometryProbe)
    (code : FiniteAxisFoldComparisonCode) :=
  probe.observableRestriction code.evaluate

/-- The constant-one comparison and five-factor comparison have the same
coefficient restriction on every finite source probe because their actual
arrows are equal. -/
theorem finiteAxisFold_identityBarBeta_coefficientRestriction_eq
    (probe : FiniteAxisFoldGeometryProbe) :
    finiteAxisFoldCoefficientRestriction probe .identityBarBeta =
      finiteAxisFoldCoefficientRestriction probe .barAlpha := by
  unfold finiteAxisFoldCoefficientRestriction
  rw [FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha]

/-- The constant-one comparison and five-factor comparison have the same
support restriction on every finite source probe. -/
theorem finiteAxisFold_identityBarBeta_supportRestriction_eq
    (probe : FiniteAxisFoldGeometryProbe)
    (i : Fin probe.contextCard) (j : Fin (probe.supportCard i)) :
    HEq (finiteAxisFoldSupportRestriction probe .identityBarBeta i j)
      (finiteAxisFoldSupportRestriction probe .barAlpha i j) := by
  unfold finiteAxisFoldSupportRestriction
  rw [FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha]

/-- The constant-one comparison and five-factor comparison have the same axis
restriction on every finite source probe. -/
theorem finiteAxisFold_identityBarBeta_axisRestriction_eq
    (probe : FiniteAxisFoldGeometryProbe)
    (i : Fin probe.contextCard) (j : Fin (probe.axisCard i)) :
    HEq (finiteAxisFoldAxisRestriction probe .identityBarBeta i j)
      (finiteAxisFoldAxisRestriction probe .barAlpha i j) := by
  unfold finiteAxisFoldAxisRestriction
  rw [FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha]

/-- The constant-one comparison and five-factor comparison have the same
observable restriction on every finite source probe. -/
theorem finiteAxisFold_identityBarBeta_observableRestriction_eq
    (probe : FiniteAxisFoldGeometryProbe)
    (i : Fin probe.contextCard) (j : Fin (probe.observableCard i)) :
    HEq (finiteAxisFoldObservableRestriction probe .identityBarBeta i j)
      (finiteAxisFoldObservableRestriction probe .barAlpha i j) := by
  unfold finiteAxisFoldObservableRestriction
  rw [FiniteAxisFoldComparisonCode.evaluate_identityBarBeta_eq_barAlpha]

end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
