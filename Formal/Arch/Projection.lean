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

/--
Concrete dependency edges whose projected abstract edge is missing.

The supplied component list is the finite measurement universe. Duplicates in
the list intentionally duplicate measured pairs, matching the executable
signature metrics.
-/
def projectionSoundnessViolationEdges {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (components : List C) : List (C × C) :=
  components.flatMap (fun c =>
    (components.filter (fun d =>
      decide (G.edge c d) && ! decide (GA.edge (π.expose c) (π.expose d)))).map
        (fun d => (c, d)))

/--
Membership in projection-soundness violations is exactly a measured concrete
edge whose projected abstract edge is absent.
-/
theorem mem_projectionSoundnessViolationEdges_iff {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    [DecidableRel G.edge] [DecidableRel GA.edge]
    {components : List C} {edge : C × C} :
    edge ∈ projectionSoundnessViolationEdges G π GA components ↔
      edge.1 ∈ components ∧ edge.2 ∈ components ∧ G.edge edge.1 edge.2 ∧
        ¬ GA.edge (π.expose edge.1) (π.expose edge.2) := by
  rcases edge with ⟨c, d⟩
  simp [projectionSoundnessViolationEdges]

/--
Executable projection bridge metric: the number of measured concrete
dependencies that are not represented by an abstract edge.
-/
def projectionSoundnessViolation {C : Type u} {A : Type v}
    (G : ArchGraph C) (π : InterfaceProjection C A) (GA : AbstractGraph A)
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (components : List C) : Nat :=
  (projectionSoundnessViolationEdges G π GA components).length

/--
If projection soundness holds, the finite executable violation count is zero.
-/
theorem projectionSoundnessViolation_eq_zero_of_projectionSound
    {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    [DecidableRel G.edge] [DecidableRel GA.edge]
    (components : List C) (h : ProjectionSound G π GA) :
    projectionSoundnessViolation G π GA components = 0 := by
  have hNoViolation : ∀ c d : C,
      (decide (G.edge c d) &&
          ! decide (GA.edge (π.expose c) (π.expose d))) = false := by
    intro c d
    by_cases hEdge : G.edge c d
    · have hAbstract : GA.edge (π.expose c) (π.expose d) := h hEdge
      simp [hEdge, hAbstract]
    · simp [hEdge]
  induction components with
  | nil =>
      simp [projectionSoundnessViolation, projectionSoundnessViolationEdges]
  | cons _ _ ih =>
      simp [projectionSoundnessViolation, projectionSoundnessViolationEdges,
        hNoViolation]
      simpa [projectionSoundnessViolation, projectionSoundnessViolationEdges,
        hNoViolation] using ih

/--
If every concrete edge is represented in the measurement universe, zero
projection-soundness violations imply graph-level projection soundness.
-/
theorem projectionSound_of_projectionSoundnessViolation_eq_zero
    {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    [DecidableRel G.edge] [DecidableRel GA.edge]
    {components : List C}
    (hEdgeClosed : ∀ {c d : C}, G.edge c d → c ∈ components ∧ d ∈ components)
    (hZero : projectionSoundnessViolation G π GA components = 0) :
    ProjectionSound G π GA := by
  intro c d hEdge
  by_cases hAbstract : GA.edge (π.expose c) (π.expose d)
  · exact hAbstract
  have hClosed := hEdgeClosed hEdge
  have hMem : (c, d) ∈ projectionSoundnessViolationEdges G π GA components := by
    rw [mem_projectionSoundnessViolationEdges_iff]
    exact ⟨hClosed.1, hClosed.2, hEdge, hAbstract⟩
  have hPositive : 0 < projectionSoundnessViolation G π GA components := by
    unfold projectionSoundnessViolation
    exact List.length_pos_of_mem hMem
  exact False.elim ((Nat.ne_of_gt hPositive) hZero)

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

/-- Projection completeness turns an abstract edge into a concrete edge witness. -/
theorem projectedConcreteEdge_of_projectionComplete {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : ProjectionComplete G π GA) {a b : A} (hEdge : GA.edge a b) :
    ∃ c d : C, π.expose c = a ∧ π.expose d = b ∧ G.edge c d :=
  h hEdge

/--
Exact projection identifies abstract edges with projected concrete edge
witnesses.
-/
theorem abstractEdge_iff_projectedConcreteEdge_of_projectionExact
    {C : Type u} {A : Type v}
    {G : ArchGraph C} {π : InterfaceProjection C A} {GA : AbstractGraph A}
    (h : ProjectionExact G π GA) {a b : A} :
    GA.edge a b ↔
      ∃ c d : C, π.expose c = a ∧ π.expose d = b ∧ G.edge c d := by
  constructor
  · intro hEdge
    exact projectedConcreteEdge_of_projectionComplete
      (projectionComplete_of_projectionExact h) hEdge
  · rintro ⟨c, d, hc, hd, hEdge⟩
    have hAbstract : GA.edge (π.expose c) (π.expose d) :=
      projectionSound_of_projectionExact h hEdge
    simpa [hc, hd] using hAbstract

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
