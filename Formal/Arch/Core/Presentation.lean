import Formal.Arch.Core.Graph

namespace Formal.Arch

universe u v

/--
A selected presentation of an ambient architecture universe.

`embed` says how the bounded component type is read inside the ambient
system.  The presentation does not assert that every ambient component or
ambient relation has been selected.
-/
structure SelectedPresentation (Ambient : Type u) (Selected : Type v) where
  embed : Selected -> Ambient

namespace SelectedPresentation

/-- The identity presentation used when the selected and ambient universes are the same. -/
def identity (C : Type u) : SelectedPresentation C C where
  embed := id

/-- An ambient component is covered by a selected presentation when it is in its image. -/
def Covers {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected) (a : Ambient) : Prop :=
  ∃ x : Selected, P.embed x = a

/-- The identity presentation covers every component of its universe. -/
theorem covers_identity {C : Type u} (c : C) :
    Covers (identity C) c := by
  exact ⟨c, rfl⟩

end SelectedPresentation

/-- A claim whose meaning is indexed by a selected presentation. -/
abbrev PresentationClaim (Ambient : Type u) (Selected : Type v) :=
  SelectedPresentation Ambient Selected -> Prop

/--
The Foundations judgement form: a claim is licensed only at the selected
presentation where it is evaluated.
-/
def AATJudgement {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (claim : PresentationClaim Ambient Selected) : Prop :=
  claim P

/-- The judgement form is exactly evaluation at the supplied presentation. -/
theorem aatJudgement_iff {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (claim : PresentationClaim Ambient Selected) :
    AATJudgement P claim ↔ claim P :=
  Iff.rfl

/-- Restrict an ambient edge relation to the selected presentation. -/
def EdgeRestriction {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (edge : Ambient -> Ambient -> Prop) : Selected -> Selected -> Prop :=
  fun src dst => edge (P.embed src) (P.embed dst)

/-- Restrict an ambient architecture graph to the selected presentation. -/
def GraphRestriction {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (G : ArchGraph Ambient) : ArchGraph Selected where
  edge := EdgeRestriction P G.edge

/-- Two ambient relations are indistinguishable through a selected presentation. -/
def SameEdgeRestriction {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (left right : Ambient -> Ambient -> Prop) : Prop :=
  forall src dst : Selected,
    EdgeRestriction P left src dst ↔ EdgeRestriction P right src dst

/--
An ambient relation is completely represented by a selected presentation when
every ambient edge has selected endpoints mapping to it.

This is an explicit premise, not something supplied by `ComponentUniverse` or
`ArchitectureCore` for an arbitrary ambient system.
-/
def CompleteForRelation {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (edge : Ambient -> Ambient -> Prop) : Prop :=
  forall {src dst : Ambient}, edge src dst ->
    ∃ selectedSrc selectedDst : Selected,
      P.embed selectedSrc = src ∧ P.embed selectedDst = dst

/-- Graph-level spelling of `CompleteForRelation`. -/
def CompleteForGraph {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected) (G : ArchGraph Ambient) : Prop :=
  CompleteForRelation P G.edge

/-- The left endpoint of a completely represented edge is covered by the presentation. -/
theorem completeForRelation_left_covered {Ambient : Type u} {Selected : Type v}
    {P : SelectedPresentation Ambient Selected}
    {edge : Ambient -> Ambient -> Prop}
    (hComplete : CompleteForRelation P edge) {src dst : Ambient}
    (hEdge : edge src dst) :
    P.Covers src := by
  rcases hComplete hEdge with ⟨selectedSrc, _selectedDst, hSrc, _hDst⟩
  exact ⟨selectedSrc, hSrc⟩

/-- The right endpoint of a completely represented edge is covered by the presentation. -/
theorem completeForRelation_right_covered {Ambient : Type u} {Selected : Type v}
    {P : SelectedPresentation Ambient Selected}
    {edge : Ambient -> Ambient -> Prop}
    (hComplete : CompleteForRelation P edge) {src dst : Ambient}
    (hEdge : edge src dst) :
    P.Covers dst := by
  rcases hComplete hEdge with ⟨_selectedSrc, selectedDst, _hSrc, hDst⟩
  exact ⟨selectedDst, hDst⟩

/-- A presentation covering every ambient component is complete for every relation. -/
theorem completeForRelation_of_covers_all {Ambient : Type u} {Selected : Type v}
    (P : SelectedPresentation Ambient Selected)
    (edge : Ambient -> Ambient -> Prop)
    (hCovers : forall a : Ambient, P.Covers a) :
    CompleteForRelation P edge := by
  intro src dst _hEdge
  rcases hCovers src with ⟨selectedSrc, hSrc⟩
  rcases hCovers dst with ⟨selectedDst, hDst⟩
  exact ⟨selectedSrc, selectedDst, hSrc, hDst⟩

/-- The identity presentation is complete for every relation on its own universe. -/
theorem completeForRelation_identity {C : Type u}
    (edge : C -> C -> Prop) :
    CompleteForRelation (SelectedPresentation.identity C) edge := by
  exact completeForRelation_of_covers_all
    (SelectedPresentation.identity C) edge SelectedPresentation.covers_identity

/-- Restricting a relation through the identity presentation leaves it unchanged. -/
theorem edgeRestriction_identity {C : Type u}
    (edge : C -> C -> Prop) :
    EdgeRestriction (SelectedPresentation.identity C) edge = edge := by
  funext src dst
  simp [EdgeRestriction, SelectedPresentation.identity]

namespace CompleteExtractionCounterexample

/-- One selected component. -/
inductive SelectedComponent where
  | component
  deriving DecidableEq, Repr

/-- The ambient universe has the selected component plus one out-of-scope component. -/
inductive AmbientComponent where
  | component
  | outside
  deriving DecidableEq, Repr

/-- Embed the selected component into the ambient universe. -/
def embed : SelectedComponent -> AmbientComponent
  | SelectedComponent.component => AmbientComponent.component

/-- The selected presentation used by the counterexample. -/
def presentation : SelectedPresentation AmbientComponent SelectedComponent where
  embed := embed

/-- Ambient relation with no edges. -/
def ambientBaseEdge : AmbientComponent -> AmbientComponent -> Prop :=
  fun _src _dst => False

/-- Ambient relation that adds one edge from an out-of-scope component. -/
def ambientWithOutOfScopeEdge : AmbientComponent -> AmbientComponent -> Prop
  | AmbientComponent.outside, AmbientComponent.component => True
  | _, _ => False

/-- The selected embedding never maps a selected component to the out-of-scope component. -/
theorem embed_ne_outside (selected : SelectedComponent) :
    embed selected ≠ AmbientComponent.outside := by
  cases selected
  intro h
  cases h

/-- The two ambient relations have the same selected restriction. -/
theorem same_selectedRestriction :
    SameEdgeRestriction presentation ambientBaseEdge ambientWithOutOfScopeEdge := by
  intro src dst
  cases src
  cases dst
  simp [EdgeRestriction, presentation, embed, ambientBaseEdge,
    ambientWithOutOfScopeEdge]

/-- The empty ambient relation is completely represented by the selected presentation. -/
theorem complete_base :
    CompleteForRelation presentation ambientBaseEdge := by
  intro _src _dst hEdge
  cases hEdge

/--
The relation with an out-of-scope edge is not completely represented by the
selected presentation.
-/
theorem not_complete_withOutOfScopeEdge :
    ¬ CompleteForRelation presentation ambientWithOutOfScopeEdge := by
  intro hComplete
  have hEdge :
      ambientWithOutOfScopeEdge AmbientComponent.outside AmbientComponent.component := by
    simp [ambientWithOutOfScopeEdge]
  rcases hComplete hEdge with ⟨selectedSrc, _selectedDst, hSrc, _hDst⟩
  exact embed_ne_outside selectedSrc hSrc

/--
Concrete non-implication package: equal selected restrictions do not force
ambient complete-extraction status to agree.
-/
theorem selectedRestriction_same_but_completeExtraction_differs :
    SameEdgeRestriction presentation ambientBaseEdge ambientWithOutOfScopeEdge ∧
      CompleteForRelation presentation ambientBaseEdge ∧
      ¬ CompleteForRelation presentation ambientWithOutOfScopeEdge := by
  exact ⟨same_selectedRestriction, complete_base, not_complete_withOutOfScopeEdge⟩

/--
Existential form of the Foundations counterexample.

There are two ambient relations with the same selected presentation-level
reading, while complete extraction holds for one and fails for the other.
-/
theorem exists_sameSelectedRestriction_completeExtraction_differs :
    ∃ (P : SelectedPresentation AmbientComponent SelectedComponent)
      (base withOutOfScope : AmbientComponent -> AmbientComponent -> Prop),
      SameEdgeRestriction P base withOutOfScope ∧
        CompleteForRelation P base ∧ ¬ CompleteForRelation P withOutOfScope := by
  exact ⟨presentation, ambientBaseEdge, ambientWithOutOfScopeEdge,
    selectedRestriction_same_but_completeExtraction_differs⟩

end CompleteExtractionCounterexample

end Formal.Arch
