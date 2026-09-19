import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAtomReadings
import Formal.AG.ReadingFunctoriality.Core
import Formal.Util.AssertStandardAxioms

/-!
# Pointwise matching of transported family and configuration references

The common Hom declaration contains Boolean matching cells for candidate
native family/configuration references. Positive flags compare primitive
membership, relation, and identification points under true Atom-graph pairs.
Negative flags must exhibit a point mismatch. Exact equality with native
transport is derived afterwards, and the matching cells have no free choices.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.TransportMatch

noncomputable section

universe u v

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- The upper Atom equivalence is an output of its primitive point rows. -/
def atomEquiv (t : Table.{u, v} U mode) (h : Atom.IsLawful (Atom.upper t)) : U.Atom ≃ U.Atom :=
  Atom.assemble (Atom.upper t) h

/-- A true common Atom point is exactly the derived native forward image equation. -/
theorem edge_iff (t : Table.{u, v} U mode) (h : Atom.IsLawful (Atom.upper t)) (a b : U.Atom) :
    t (.atom .forward a b) = true ↔ atomEquiv t h a = b := by
  constructor
  · exact Atom.assemble_eq_of_edge (Atom.upper t) h
  · rintro rfl
    exact Atom.edge_assemble (Atom.upper t) h a

/-- Native direct-image family transport reduces to one source membership at an equivalence image. -/
theorem family_transport_image (F : AtomFamily U) (e : U.Atom ≃ U.Atom) (a : U.Atom) :
    (F.transport e).mem (e a) ↔ F.mem a := by
  constructor
  · rintro ⟨b, hb, he⟩
    have hab := e.injective he
    subst b
    exact hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Native relation transport reduces to its one source point pair. -/
theorem relation_transport_image (C : AtomConfiguration U) (e : U.Atom ≃ U.Atom) (a b : U.Atom) :
    (C.transport e).relation (e a) (e b) ↔ C.relation a b := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have hxa := e.injective hx
    have hyb := e.injective hy
    subst x
    subst y
    exact hxy
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

/-- Native identification transport reduces to its one source point pair. -/
theorem identification_transport_image (C : AtomConfiguration U) (e : U.Atom ≃ U.Atom) (a b : U.Atom) :
    (C.transport e).identification (e a) (e b) ↔ C.identification a b := by
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    have hxa := e.injective hx
    have hyb := e.injective hy
    subst x
    subst y
    exact hxy
  · intro h
    exact ⟨a, b, h, rfl, rfl⟩

/-- Exact transport of a family is derived from primitive membership comparisons at true graph pairs. -/
theorem family_eq_of_points (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t))
    (F F' : AtomFamily U)
    (h : ∀ a b, t (.atom .forward a b) = true → (F.mem a ↔ F'.mem b)) :
    F' = F.transport (atomEquiv t ha) := by
  apply AtomFamily.ext
  intro b
  obtain ⟨a, rfl⟩ := (atomEquiv t ha).surjective b
  exact (h a _ ((edge_iff t ha a _).2 rfl)).symm.trans (family_transport_image F _ a).symm

/-- Exact configuration transport is derived from family matching and primitive relation/identification pairs. -/
theorem configuration_eq_of_points (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t))
    (C C' : AtomConfiguration U) (hf : C'.family = C.family.transport (atomEquiv t ha))
    (h : ∀ a a' b b', t (.atom .forward a a') = true → t (.atom .forward b b') = true →
      (C.relation a b ↔ C'.relation a' b') ∧ (C.identification a b ↔ C'.identification a' b')) :
    C' = C.transport (atomEquiv t ha) := by
  apply AtomConfiguration.ext hf
  · intro a' b'
    obtain ⟨a, rfl⟩ := (atomEquiv t ha).surjective a'
    obtain ⟨b, rfl⟩ := (atomEquiv t ha).surjective b'
    exact ((h a _ b _ ((edge_iff t ha a _).2 rfl) ((edge_iff t ha b _).2 rfl)).1).symm.trans
      (relation_transport_image C _ a b).symm
  · intro a' b'
    obtain ⟨a, rfl⟩ := (atomEquiv t ha).surjective a'
    obtain ⟨b, rfl⟩ := (atomEquiv t ha).surjective b'
    exact ((h a _ b _ ((edge_iff t ha a _).2 rfl) ((edge_iff t ha b _).2 rfl)).2).symm.trans
      (identification_transport_image C _ a b).symm

/-- Transport matching requires primitive point equations or a concrete failed point, never whole transport equality. -/
structure IsLawful (t : Table.{u, v} U mode) : Prop where
  /-- A positive family match preserves membership at every true Atom point pair. -/
  family_yes : ∀ F F', t (.familyTransport F F') = true →
    ∀ a b, t (.atom .forward a b) = true → (F.mem a ↔ F'.mem b)
  /-- A negative family match exhibits a true Atom pair with differing membership. -/
  family_no : ∀ F F', t (.familyTransport F F') = false →
    ∃ a b, t (.atom .forward a b) = true ∧ ¬ (F.mem a ↔ F'.mem b)
  /-- A positive configuration match has a family match and both primitive point comparisons. -/
  configuration_yes : ∀ C C', t (.configurationTransport C C') = true →
    t (.familyTransport C.family C'.family) = true ∧
      ∀ a a' b b', t (.atom .forward a a') = true → t (.atom .forward b b') = true →
        (C.relation a b ↔ C'.relation a' b') ∧ (C.identification a b ↔ C'.identification a' b')
  /-- A negative configuration match fails its family flag or exhibits one relation/identification mismatch. -/
  configuration_no : ∀ C C', t (.configurationTransport C C') = false →
    t (.familyTransport C.family C'.family) = false ∨
      ∃ a a' b b', t (.atom .forward a a') = true ∧ t (.atom .forward b b') = true ∧
        ¬ ((C.relation a b ↔ C'.relation a' b') ∧ (C.identification a b ↔ C'.identification a' b'))

/-- Family matching flags are exactly equality to the native transport constructed from Atom points. -/
theorem family_iff (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t)) (h : IsLawful t)
    (F F' : AtomFamily U) : t (.familyTransport F F') = true ↔ F' = F.transport (atomEquiv t ha) := by
  constructor
  · intro hf
    exact family_eq_of_points t ha F F' (h.family_yes F F' hf)
  · rintro rfl
    cases hf : t (.familyTransport F (F.transport (atomEquiv t ha))) with
    | true => rfl
    | false =>
      obtain ⟨a, b, hab, hp⟩ := h.family_no _ _ hf
      have he := (edge_iff t ha a b).1 hab
      subst b
      exact False.elim (hp (family_transport_image F _ a).symm)

/-- Configuration matching flags are exactly equality to the derived native full configuration transport. -/
theorem configuration_iff (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t)) (h : IsLawful t)
    (C C' : AtomConfiguration U) :
    t (.configurationTransport C C') = true ↔ C' = C.transport (atomEquiv t ha) := by
  constructor
  · intro hc
    obtain ⟨hf, hp⟩ := h.configuration_yes C C' hc
    exact configuration_eq_of_points t ha C C' ((family_iff t ha h _ _).1 hf) hp
  · rintro rfl
    cases hc : t (.configurationTransport C (C.transport (atomEquiv t ha))) with
    | true => rfl
    | false =>
      rcases h.configuration_no _ _ hc with hf | ⟨a, a', b, b', haa, hbb, hp⟩
      · exact False.elim (Bool.noConfusion (hf.symm.trans ((family_iff t ha h _ _).2 rfl)))
      · have heA := (edge_iff t ha a a').1 haa
        have heB := (edge_iff t ha b b').1 hbb
        subst a'
        subst b'
        exact False.elim (hp ⟨(relation_transport_image C _ a b).symm,
          (identification_transport_image C _ a b).symm⟩)

/-- Fill only the derived transport-matching cells from the primitive Atom equivalence. -/
def completeMatching (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t)) : Table.{u, v} U mode := by
  classical
  intro q
  exact match q with
    | .familyTransport F F' => decide (F' = F.transport (atomEquiv t ha))
    | .configurationTransport C C' => decide (C' = C.transport (atomEquiv t ha))
    | q => t q

/-- Completing matching metadata leaves every upper Atom point exactly unchanged. -/
theorem upper_completeMatching (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t)) :
    Atom.upper (completeMatching t ha) = Atom.upper t := rfl

/-- Primitive Atom assembly supplies each positive transport match and each finite mismatch witness. -/
theorem completeMatching_isLawful (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t)) :
    IsLawful (completeMatching t ha) := by
  classical
  constructor
  · intro F F' hf a b hab
    have hF : F' = F.transport (atomEquiv t ha) := of_decide_eq_true hf
    subst F'
    have he := (edge_iff t ha a b).1 hab
    subst b
    exact (family_transport_image F _ a).symm
  · intro F F' hf
    have hne : F' ≠ F.transport (atomEquiv t ha) := of_decide_eq_false hf
    by_contra hn
    push_neg at hn
    exact hne (family_eq_of_points t ha F F' hn)
  · intro C C' hc
    have hC : C' = C.transport (atomEquiv t ha) := of_decide_eq_true hc
    subst C'
    refine ⟨?_, ?_⟩
    · change decide ((C.transport (atomEquiv t ha)).family = C.family.transport (atomEquiv t ha)) = true
      simp [AtomConfiguration.transport]
    · intro a a' b b' haa hbb
      have heA := (edge_iff t ha a a').1 haa
      have heB := (edge_iff t ha b b').1 hbb
      subst a'
      subst b'
      exact ⟨(relation_transport_image C _ a b).symm, (identification_transport_image C _ a b).symm⟩
  · intro C C' hc
    have hne : C' ≠ C.transport (atomEquiv t ha) := of_decide_eq_false hc
    by_cases hf : C'.family = C.family.transport (atomEquiv t ha)
    · right
      by_contra hn
      push_neg at hn
      exact hne (configuration_eq_of_points t ha C C' hf hn)
    · left
      simpa [completeMatching] using hf

/-- All lawful matching cells equal their derived canonical values; metadata introduces no choices. -/
theorem completeMatching_eq_self (t : Table.{u, v} U mode) (ha : Atom.IsLawful (Atom.upper t))
    (h : IsLawful t) : completeMatching t ha = t := by
  classical
  funext q
  cases q <;> try rfl
  case familyTransport F F' =>
      apply Bool.eq_iff_iff.mpr
      simpa [completeMatching] using (family_iff t ha h F F').symm
  case configurationTransport C C' =>
      apply Bool.eq_iff_iff.mpr
      simpa [completeMatching] using (configuration_iff t ha h C C').symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.TransportMatch

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.TransportMatch
