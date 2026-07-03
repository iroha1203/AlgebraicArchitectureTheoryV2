import Formal.AG.SemanticRepair.Bootstrap
import Mathlib.Data.Fintype.Basic

noncomputable section

namespace AAT.AG
namespace SemanticRepair

universe u v w x

/--
X.定義2.1: semantic atom projection.

This bundles the semantic atom vocabulary `Λ`, the component vocabulary `K`,
and the projection `π : Λ -> K`.  The component vocabulary is a type parameter
of the object, not the Research-side fixed `BridgeComponent`.
-/
structure SemanticAtomProjection where
  SemanticAtom : Type u
  Component : Type v
  project : SemanticAtom -> Component

namespace SemanticAtomProjection

/-- X.定義2.1: the semantic support predicate on `Λ`. -/
abbrev Support (P : SemanticAtomProjection.{u, v}) :=
  P.SemanticAtom -> Prop

end SemanticAtomProjection

/--
X.定義2.2: finite semantic repair cover datum.

The datum records finite chart and transition indexes together with the
holonomy support `R(𝒰) ⊂ K` selected by the cover.  The projected residual
below is a raw semantic atom value whose component lies in `R(𝒰)`; it is not a
decision procedure, quotient, or global coherence claim.
-/
structure FiniteSemanticRepairCoverDatum (K : Type v) where
  Chart : Type w
  Transition : Type x
  chartFinite : Fintype Chart
  transitionFinite : Fintype Transition
  holonomySupport : K -> Prop

namespace FiniteSemanticRepairCoverDatum

attribute [instance] chartFinite transitionFinite

end FiniteSemanticRepairCoverDatum

/--
X.定義2.2: semantic residual atom predicate.

`SemanticProjectedResidual P cover atom` is exactly
`P.project atom ∈ R(𝒰)`.  It marks the raw semantic atom as a residual for the
selected finite cover datum; it is deliberately a value-level predicate, not a
certificate that any support closes it.
-/
def SemanticProjectedResidual
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component)
    (atom : P.SemanticAtom) : Prop :=
  cover.holonomySupport (P.project atom)

/-- X.定義2.2: the residual predicate is `π⁻¹(R(𝒰))`. -/
theorem semanticProjectedResidual_iff_holonomySupport
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component)
    (atom : P.SemanticAtom) :
    SemanticProjectedResidual P cover atom <->
      cover.holonomySupport (P.project atom) :=
  Iff.rfl

/-- X.定義2.3: a support semantically closes every residual atom. -/
def SemanticRepairClosed
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component)
    (support : P.Support) : Prop :=
  forall atom, SemanticProjectedResidual P cover atom -> support atom

/--
X.定義2.4: the support covers every residual component, possibly through a
different semantic atom in the same projected component.
-/
def ResidualComponentCoveredSupport
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component)
    (support : P.Support) : Prop :=
  forall residual,
    SemanticProjectedResidual P cover residual ->
      exists candidate, support candidate /\ P.project candidate = P.project residual

/--
X.定義2.4: component coverage is faithful back to the actual residual atom.
-/
def ResidualComponentFaithfulSupport
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component)
    (support : P.Support) : Prop :=
  forall residual candidate,
    SemanticProjectedResidual P cover residual ->
      support candidate ->
        P.project candidate = P.project residual ->
          support residual

/--
X.補題2.5: semantic closure decomposes into residual-component coverage and
faithfulness.
-/
theorem semanticRepairClosed_iff_residualComponentCovered_and_faithful
    {P : SemanticAtomProjection.{u, v}}
    {cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component}
    {support : P.Support} :
    SemanticRepairClosed P cover support <->
      ResidualComponentCoveredSupport P cover support /\
        ResidualComponentFaithfulSupport P cover support := by
  constructor
  · intro hclosed
    constructor
    · intro residual hresidual
      exact ⟨residual, hclosed residual hresidual, rfl⟩
    · intro residual _candidate hresidual _hcandidate _hprojection
      exact hclosed residual hresidual
  · intro hsupport residual hresidual
    rcases hsupport.1 residual hresidual with
      ⟨candidate, hcandidate, hprojection⟩
    exact hsupport.2 residual candidate hresidual hcandidate hprojection

/-! ## X.例2.6: coverage without faithfulness -/

namespace CoverageWithoutFaithfulness

/-- X.例2.6: three semantic atoms `t`, `s`, and `o`. -/
inductive Atom where
  | t
  | s
  | o
deriving DecidableEq

/-- X.例2.6: component vocabulary with an alias component. -/
inductive Component where
  | trace
  | shared
deriving DecidableEq

open Atom
open Component

/-- X.例2.6: alias projection sends both `s` and `o` to the same component. -/
def projection : SemanticAtomProjection where
  SemanticAtom := Atom
  Component := Component
  project
    | t => trace
    | s => shared
    | o => shared

/-- X.例2.6: finite cover whose holonomy support contains both components. -/
def cover : FiniteSemanticRepairCoverDatum Component where
  Chart := Fin 2
  Transition := Fin 1
  chartFinite := inferInstance
  transitionFinite := inferInstance
  holonomySupport
    | trace => True
    | shared => True

/-- X.例2.6: the support `S = {t, s}`. -/
def support : projection.Support
  | t => True
  | s => True
  | o => False

/-- X.例2.6: `S = {t, s}` covers every residual component. -/
theorem support_residualComponentCovered :
    ResidualComponentCoveredSupport projection cover support := by
  intro residual _hresidual
  cases residual with
  | t => exact ⟨t, trivial, rfl⟩
  | s => exact ⟨s, trivial, rfl⟩
  | o => exact ⟨s, trivial, rfl⟩

/-- X.例2.6: component coverage is not faithful to the actual residual atom. -/
theorem support_not_residualComponentFaithful :
    Not (ResidualComponentFaithfulSupport projection cover support) := by
  intro hfaithful
  have ho : support o :=
    hfaithful o s (by simp [SemanticProjectedResidual, cover, projection])
      trivial rfl
  simp [support] at ho

/-- X.例2.6: the support does not semantically close the selected residuals. -/
theorem support_not_semanticRepairClosed :
    Not (SemanticRepairClosed projection cover support) := by
  intro hclosed
  have ho : support o :=
    hclosed o (by simp [SemanticProjectedResidual, cover, projection])
  simp [support] at ho

/--
X.例2.6: coverage without faithfulness.

The three-atom alias projection has component coverage for `S = {t, s}`, but
it is not faithful to the residual atom `o`, and therefore is not closed.
-/
theorem covered_not_faithful_not_closed :
    ResidualComponentCoveredSupport projection cover support /\
      Not (ResidualComponentFaithfulSupport projection cover support) /\
      Not (SemanticRepairClosed projection cover support) :=
  ⟨support_residualComponentCovered,
    support_not_residualComponentFaithful,
    support_not_semanticRepairClosed⟩

end CoverageWithoutFaithfulness

/-- X.例2.6: named exported form of coverage without faithfulness. -/
theorem coverageWithoutFaithfulness_covered_not_faithful_not_closed :
    ResidualComponentCoveredSupport
        CoverageWithoutFaithfulness.projection
        CoverageWithoutFaithfulness.cover
        CoverageWithoutFaithfulness.support /\
      Not
        (ResidualComponentFaithfulSupport
          CoverageWithoutFaithfulness.projection
          CoverageWithoutFaithfulness.cover
          CoverageWithoutFaithfulness.support) /\
      Not
        (SemanticRepairClosed
          CoverageWithoutFaithfulness.projection
          CoverageWithoutFaithfulness.cover
          CoverageWithoutFaithfulness.support) :=
  CoverageWithoutFaithfulness.covered_not_faithful_not_closed

end SemanticRepair
end AAT.AG
