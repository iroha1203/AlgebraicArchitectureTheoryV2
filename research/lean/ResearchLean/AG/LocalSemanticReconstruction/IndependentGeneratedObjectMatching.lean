import ResearchLean.AG.LocalSemanticReconstruction.IndependentCorePrimitiveReadings
import Formal.Util.AssertStandardAxioms

/-!
# Primitive matching of generated family, configuration, and object references

These Boolean cells are derived typing metadata for candidate references.
Positive cells obey point equations; negative cells supply a failed point.
No completed geometry object, equality to an assembler output, or global
extension witness is stored in a local condition. The derived matching
theorems identify the unique active native reference after primitive assembly.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeneratedObjectMatching

noncomputable section

universe u

open IndependentCorePrimitive

variable {U : AtomCarrier.{u}}

/-- Candidate addresses are declared before choosing the generating primitive tables. -/
inductive Query (U : AtomCarrier.{u}) where
  /-- Matching of a raw Atom-family reference. -/
  | family (F : AtomFamily U)
  /-- Matching of a raw configuration reference. -/
  | configuration (C : AtomConfiguration U)
  /-- Matching of a raw architecture-object reference. -/
  | object (A : ArchitectureObject U)

/-- One Boolean typing response at each candidate reference. -/
abbrev Table (U : AtomCarrier.{u}) := Query U → Bool

/-- The normalized selected source is one active primitive normalization response. -/
def normalized (te : Extraction.Table U) (he : Extraction.IsTyped te) :
    Extraction.carrier te .source :=
  (te (.normalize (Extraction.carrier te .source) (Extraction.point te .source))).down.get
    ((he.normalize _ _).2 rfl)

/-- One Atom admission is the conjunction of the four named primitive readings. -/
def extracted (te : Extraction.Table U) (he : Extraction.IsTyped te) (a : U.Atom) : Prop :=
  (te (.vocabulary _ (Extraction.point te .vocabulary) a)).down ∧
  (te (.semantic _ _ (Extraction.point te .semantic) (normalized te he) a)).down ∧
  (te (.resolution _ _ (Extraction.point te .resolution) (normalized te he) a)).down ∧
  (te (.source _ (normalized te he) a)).down

/-- The point expression has exactly the native generated-family meaning. -/
theorem extracted_iff_family (te : Extraction.Table U) (he : Extraction.IsTyped te) (a : U.Atom) :
    extracted te he a ↔ (Generation.family te he).mem a := Iff.rfl

/-- A source-only view of the native object's configuration and two primitive selected values. -/
def objectView : ArchitectureObject U ≃ AtomConfiguration U × SelectedValue.{u} × SelectedValue.{u} where
  toFun A := ⟨A.configuration, ⟨A.StructureMaps, A.structureMaps⟩,
    ⟨A.SelectedQuantities, A.selectedQuantities⟩⟩
  invFun d := ⟨d.1, d.2.1.1, d.2.2.1, d.2.1.2, d.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Configuration equality and the two primitive carrier/value pairs determine the full object. -/
theorem object_ext {A B : ArchitectureObject U} (hc : A.configuration = B.configuration)
    (hs : (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u}) = ⟨B.StructureMaps, B.structureMaps⟩)
    (hq : (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u}) =
      ⟨B.SelectedQuantities, B.selectedQuantities⟩) : A = B :=
  objectView.injective (Prod.ext hc (Prod.ext hs hq))

variable (te : Extraction.Table U) (he : Extraction.IsTyped te)
variable (tc : Composition.Table U) (tf : ObjectFormation.Table U)

/-- Positive matches obey local point equations; negative matches must exhibit an actual failed point. -/
structure IsLawful (t : Table U) : Prop where
  /-- Every candidate family point agrees with its four primitive admission readings. -/
  family_true : ∀ F, t (.family F) = true → ∀ a, F.mem a ↔ extracted te he a
  /-- A rejected family carries an Atom at which its membership differs. -/
  family_false : ∀ F, t (.family F) = false → ∃ a, ¬ (F.mem a ↔ extracted te he a)
  /-- A matching configuration has a matching family and both pointwise composition readings. -/
  configuration_true : ∀ C, t (.configuration C) = true →
    t (.family C.family) = true ∧ ∀ (hf : C.family.ListFinite) a b,
      (C.relation a b ↔ tc (.relation C.family hf a b)) ∧
        (C.identification a b ↔ tc (.identification C.family hf a b))
  /-- A rejected configuration fails its family match or one relation/identification pair. -/
  configuration_false : ∀ C, t (.configuration C) = false →
    t (.family C.family) = false ∨ ∃ (hf : C.family.ListFinite) (a b : U.Atom),
      ¬ ((C.relation a b ↔ tc (.relation C.family hf a b)) ∧
        (C.identification a b ↔ tc (.identification C.family hf a b)))
  /-- A matching object has a matching configuration and both selected primitive carrier/value pairs. -/
  object_true : ∀ A, t (.object A) = true →
    t (.configuration A.configuration) = true ∧
      tf (.structureMaps A.configuration) = ⟨A.StructureMaps, A.structureMaps⟩ ∧
      tf (.selectedQuantities A.configuration) = ⟨A.SelectedQuantities, A.selectedQuantities⟩
  /-- A rejected object fails its configuration match or one selected primitive pair. -/
  object_false : ∀ A, t (.object A) = false →
    t (.configuration A.configuration) = false ∨
      tf (.structureMaps A.configuration) ≠ ⟨A.StructureMaps, A.structureMaps⟩ ∨
      tf (.selectedQuantities A.configuration) ≠ ⟨A.SelectedQuantities, A.selectedQuantities⟩

/-- Family matching is derived to mean exact equality with the generated family. -/
theorem family_iff (t : Table U) (ht : IsLawful te he tc tf t) (F : AtomFamily U) :
    t (.family F) = true ↔ F = Generation.family te he := by
  constructor
  · intro h
    apply AtomFamily.ext
    intro a
    exact (ht.family_true F h a).trans (extracted_iff_family te he a)
  · rintro rfl
    cases h : t (.family (Generation.family te he)) with
    | true => rfl
    | false =>
      obtain ⟨a, ha⟩ := ht.family_false _ h
      exact False.elim (ha (extracted_iff_family te he a).symm)

variable (hc : Composition.IsLawful tc) (hf : (Generation.family te he).ListFinite)

/-- Configuration matching is derived from family matching and the two primitive point families. -/
theorem configuration_iff (t : Table U) (ht : IsLawful te he tc tf t) (C : AtomConfiguration U) :
    t (.configuration C) = true ↔ C = Generation.configuration te he tc hc hf := by
  constructor
  · intro h
    have hF := (family_iff te he tc tf t ht C.family).1 (ht.configuration_true C h).1
    have hfin : C.family.ListFinite := hF.symm ▸ hf
    apply AtomConfiguration.ext hF
    · intro a b
      simpa [Generation.configuration, Composition.assemble, Composition.configuration, hF]
        using ((ht.configuration_true C h).2 hfin a b).1
    · intro a b
      simpa [Generation.configuration, Composition.assemble, Composition.configuration, hF]
        using ((ht.configuration_true C h).2 hfin a b).2
  · rintro rfl
    cases h : t (.configuration (Generation.configuration te he tc hc hf)) with
    | true => rfl
    | false =>
      rcases ht.configuration_false _ h with hF | ⟨hfin, a, b, hp⟩
      · have htF := (family_iff te he tc tf t ht (Generation.family te he)).2 rfl
        exact False.elim (Bool.noConfusion (hF.symm.trans htF))
      · exact False.elim (hp ⟨Iff.rfl, Iff.rfl⟩)

/-- Object matching is derived from primitive configuration, type-reference, and selected-value comparisons. -/
theorem object_iff (t : Table U) (ht : IsLawful te he tc tf t) (A : ArchitectureObject U) :
    t (.object A) = true ↔ A = Generation.object te he tc hc tf hf := by
  constructor
  · intro h
    obtain ⟨hC, hS, hQ⟩ := ht.object_true A h
    have hconf := (configuration_iff te he tc tf hc hf t ht A.configuration).1 hC
    apply object_ext hconf
    · simpa [Generation.object, ObjectFormation.assemble, ObjectFormation.object, hconf] using hS.symm
    · simpa [Generation.object, ObjectFormation.assemble, ObjectFormation.object, hconf] using hQ.symm
  · rintro rfl
    cases h : t (.object (Generation.object te he tc hc tf hf)) with
    | true => rfl
    | false =>
      rcases ht.object_false _ h with hC | hS | hQ
      · have htC := (configuration_iff te he tc tf hc hf t ht
          (Generation.configuration te he tc hc hf)).2 rfl
        exact False.elim (Bool.noConfusion (hC.symm.trans htC))
      · exact False.elim (hS rfl)
      · exact False.elim (hQ rfl)

/-- The canonical matching reader is a derived output of primitive generation. -/
def read : Table U := by
  classical
  intro q
  cases q with
  | family F => exact decide (F = Generation.family te he)
  | configuration C => exact decide (C = Generation.configuration te he tc hc hf)
  | object A => exact decide (A = Generation.object te he tc hc tf hf)

/-- Primitive generation supplies every positive match and every finite point refutation. -/
theorem read_isLawful : IsLawful te he tc tf (read te he tc tf hc hf) where
  family_true F h := by
    classical
    have heq : F = Generation.family te he := of_decide_eq_true h
    subst F
    exact fun a => (extracted_iff_family te he a).symm
  family_false F h := by
    classical
    have hne : F ≠ Generation.family te he := of_decide_eq_false h
    by_contra hn
    push_neg at hn
    exact hne (AtomFamily.ext (fun a => (hn a).trans (extracted_iff_family te he a)))
  configuration_true C h := by
    classical
    have heq : C = Generation.configuration te he tc hc hf := of_decide_eq_true h
    subst C
    exact ⟨by
      change decide (Generation.family te he = Generation.family te he) = true
      simp, fun _ _ _ => ⟨Iff.rfl, Iff.rfl⟩⟩
  configuration_false C h := by
    classical
    have hne : C ≠ Generation.configuration te he tc hc hf := of_decide_eq_false h
    by_cases hF : C.family = Generation.family te he
    · right
      refine ⟨hF.symm ▸ hf, ?_⟩
      by_contra hn
      push_neg at hn
      apply hne
      apply AtomConfiguration.ext hF
      · intro a b
        simpa [Generation.configuration, Composition.assemble, Composition.configuration, hF]
          using (hn a b).1
      · intro a b
        simpa [Generation.configuration, Composition.assemble, Composition.configuration, hF]
          using (hn a b).2
    · left
      simpa [read] using hF
  object_true A h := by
    classical
    have heq : A = Generation.object te he tc hc tf hf := of_decide_eq_true h
    subst A
    exact ⟨by
      change decide (Generation.configuration te he tc hc hf = Generation.configuration te he tc hc hf) = true
      simp, rfl, rfl⟩
  object_false A h := by
    classical
    have hne : A ≠ Generation.object te he tc hc tf hf := of_decide_eq_false h
    by_cases hC : A.configuration = Generation.configuration te he tc hc hf
    · by_cases hS : tf (.structureMaps A.configuration) = ⟨A.StructureMaps, A.structureMaps⟩
      · by_cases hQ : tf (.selectedQuantities A.configuration) = ⟨A.SelectedQuantities, A.selectedQuantities⟩
        · apply False.elim
          apply hne
          apply object_ext hC
          · simpa [Generation.object, ObjectFormation.assemble, ObjectFormation.object, hC] using hS.symm
          · simpa [Generation.object, ObjectFormation.assemble, ObjectFormation.object, hC] using hQ.symm
        · exact Or.inr (Or.inr hQ)
      · exact Or.inr (Or.inl hS)
    · left
      simpa [read] using hC

/-- Point matching laws recover all canonical flags, so the typing metadata adds no choices. -/
theorem eq_read (t : Table U) (ht : IsLawful te he tc tf t) : t = read te he tc tf hc hf := by
  funext q
  apply Bool.eq_iff_iff.mpr
  cases q with
  | family F => simpa [read] using family_iff te he tc tf t ht F
  | configuration C => simpa [read] using configuration_iff te he tc tf hc hf t ht C
  | object A => simpa [read] using object_iff te he tc tf hc hf t ht A

include hc hf in
/-- Lawful matching metadata is unique for the fixed primitive generating fields. -/
theorem unique (t s : Table U) (ht : IsLawful te he tc tf t) (hs : IsLawful te he tc tf s) :
    t = s := (eq_read te he tc tf hc hf t ht).trans (eq_read te he tc tf hc hf s hs).symm

/-- The generated architecture reference is active, derived without an existence field in the local laws. -/
theorem generated_object_active (t : Table U) (ht : IsLawful te he tc tf t) :
    t (.object (Generation.object te he tc hc tf hf)) = true :=
  (object_iff te he tc tf hc hf t ht _).2 rfl

/-- All-false matching flags are rejected by the required point refutation at the generated family. -/
theorem all_false_not_lawful : ¬ IsLawful te he tc tf (fun _ => false) := by
  intro ht
  have h := (family_iff te he tc tf (fun _ => false) ht (Generation.family te he)).2 rfl
  exact Bool.noConfusion h

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeneratedObjectMatching

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeneratedObjectMatching
