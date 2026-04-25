import Formal.Arch.ThinCategory

namespace Formal.Arch

universe u v

/-- A projection from concrete components to abstract interface components. -/
structure InterfaceProjection (C : Type u) (A : Type v) where
  expose : C → A

/-- The abstract dependency graph used as the target of projection. -/
abbrev AbstractGraph (A : Type v) := ArchGraph A

/-- Dependencies induced at the abstract level by one concrete component. -/
def ProjectedDeps {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (c : C) (a : A) : Prop :=
  ∃ d : C, G.edge c d ∧ π.expose d = a

/-- Every concrete dependency edge is represented in the abstract graph. -/
def RespectsProjection {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  ∀ {c d : C}, G.edge c d → GA.edge (π.expose c) (π.expose d)

/-- Projection soundness: every concrete edge is represented abstractly. -/
abbrev ProjectionSound {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  RespectsProjection G π GA

/-- Projection completeness: every abstract edge is induced by some concrete edge. -/
def ProjectionComplete {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  ∀ {a b : A}, GA.edge a b →
    ∃ c d : C, π.expose c = a ∧ π.expose d = b ∧ G.edge c d

/-- Exact projection: sound and complete with respect to abstract edges. -/
def ProjectionExact {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  ProjectionSound G π GA ∧ ProjectionComplete G π GA

/-- Exact projection includes projection soundness. -/
theorem projectionSound_of_projectionExact {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : ProjectionExact G π GA) : ProjectionSound G π GA :=
  h.1

/-- Exact projection includes projection completeness. -/
theorem projectionComplete_of_projectionExact {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : ProjectionExact G π GA) : ProjectionComplete G π GA :=
  h.2

/--
The quotient is well-defined when representatives of the same abstraction
induce the same abstract outgoing dependency predicate.

This is a strong representative-stability condition.
-/
def QuotientWellDefined {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) : Prop :=
  ∀ {c₁ c₂ : C}, π.expose c₁ = π.expose c₂ →
    ∀ a : A, ProjectedDeps G π c₁ a ↔ ProjectedDeps G π c₂ a

/-- Strong representative-stability for quotienting concrete components. -/
abbrev RepresentativeStable {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) : Prop :=
  QuotientWellDefined G π

/--
DIP-compatible projection, in the current strong operational sense:
projection soundness plus representative stability.
-/
def DIPCompatible {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  ProjectionSound G π GA ∧ RepresentativeStable G π

/--
Stronger exact DIP: exact projection plus representative stability.

`DIPCompatible` is the strong operational projection condition used by the
current core; `StrongDIPCompatible` adds projection completeness, so it is the
exact-projection refinement.
-/
def StrongDIPCompatible {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A) : Prop :=
  ProjectionExact G π GA ∧ RepresentativeStable G π

/-- Exact DIP refines the current strong operational DIP condition. -/
theorem dipCompatible_of_strongDIPCompatible {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : StrongDIPCompatible G π GA) : DIPCompatible G π GA :=
  ⟨projectionSound_of_projectionExact h.1, h.2⟩

/-- Identity projection respects the original graph. -/
theorem respectsProjection_id {C : Type u} (G : ArchGraph C) :
    RespectsProjection G ⟨id⟩ G := by
  intro c d h
  exact h

/-- Identity projection has a well-defined quotient. -/
theorem quotientWellDefined_id {C : Type u} (G : ArchGraph C) :
    QuotientWellDefined G ⟨id⟩ := by
  intro c₁ c₂ h a
  cases h
  exact Iff.rfl

/-- Identity projection is DIP-compatible. -/
theorem dipCompatible_id {C : Type u} (G : ArchGraph C) :
    DIPCompatible G ⟨id⟩ G :=
  ⟨respectsProjection_id G, quotientWellDefined_id G⟩

/-- Identity projection is complete. -/
theorem projectionComplete_id {C : Type u} (G : ArchGraph C) :
    ProjectionComplete G ⟨id⟩ G := by
  intro a b h
  exact ⟨a, b, rfl, rfl, h⟩

/-- Identity projection is exact. -/
theorem projectionExact_id {C : Type u} (G : ArchGraph C) :
    ProjectionExact G ⟨id⟩ G :=
  ⟨respectsProjection_id G, projectionComplete_id G⟩

/-- Identity projection is strong-DIP-compatible. -/
theorem strongDIPCompatible_id {C : Type u} (G : ArchGraph C) :
    StrongDIPCompatible G ⟨id⟩ G :=
  ⟨projectionExact_id G, quotientWellDefined_id G⟩

/-- Projection sends concrete reachability to abstract reachability when edges are respected. -/
def mapReachable {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : RespectsProjection G π GA) :
    ∀ {c d : C}, Reachable G c d → Reachable GA (π.expose c) (π.expose d)
  | _, _, Reachable.refl _ => Reachable.refl _
  | _, _, Reachable.step hEdge rest => Reachable.step (h hEdge) (mapReachable h rest)

end Formal.Arch
