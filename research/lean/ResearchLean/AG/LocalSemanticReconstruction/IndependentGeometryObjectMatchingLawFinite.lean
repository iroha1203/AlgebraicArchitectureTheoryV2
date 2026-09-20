import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectFoundationExtendedLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for generated-object matching and active rows

Positive matching cells are accompanied by all point equations they claim.
Negative cells retain a concrete failed family, configuration, or object point.
Object-row presence is then tied to the same primitive object-matching cell.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectMatchingFinite

noncomputable section

universe u v w

open IndependentCorePrimitive IndependentFiniteLawFormula
  ObjectFoundationFinite

variable {U : AtomCarrier.{u}}

def extractionAnchors (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.extraction (.selected .source)) (t (.extraction (.selected .source))))
    (.and (.cell (.extraction (.selected .vocabulary))
        (t (.extraction (.selected .vocabulary))))
      (.and (.cell (.extraction (.selected .semantic))
          (t (.extraction (.selected .semantic))))
        (.and (.cell (.extraction (.selected .resolution))
          (t (.extraction (.selected .resolution)))) body)))

@[simp] theorem extractionAnchors_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) :
    (extractionAnchors t body).evaluate t ↔ body.evaluate t := by
  simp [extractionAnchors, ObjectFormula.evaluate]

def extractedFormula (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) (a : U.Atom) :
    ObjectFormula.{u, v, w} U :=
  extractionAnchors t
    (.and
      (.cell (.extraction (.normalize _
          (Extraction.point (IndependentGeometryPrimitive.extraction t) .source)))
        (ULift.up (ULift.up (some (ObjectFoundationFinite.Finite.normalized t ht)))))
      (.and
        (.cell (.extraction (.vocabulary _
            (Extraction.point (IndependentGeometryPrimitive.extraction t) .vocabulary) a))
          (ULift.up (ULift.up True)))
        (.and
          (.cell (.extraction (.semantic _ _
              (Extraction.point (IndependentGeometryPrimitive.extraction t) .semantic)
              (ObjectFoundationFinite.Finite.normalized t ht) a))
            (ULift.up (ULift.up True)))
          (.and
            (.cell (.extraction (.resolution _ _
                (Extraction.point (IndependentGeometryPrimitive.extraction t) .resolution)
                (ObjectFoundationFinite.Finite.normalized t ht) a))
              (ULift.up (ULift.up True)))
            (.cell (.extraction (.source _
                (ObjectFoundationFinite.Finite.normalized t ht) a))
              (ULift.up (ULift.up True)))))))

theorem extractedFormula_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) (a : U.Atom) :
    (extractedFormula t ht a : ObjectFormula.{u, v, w} U).evaluate t ↔
      IndependentGeneratedObjectMatching.extracted
        (IndependentGeometryPrimitive.extraction t) ht a := by
  simp only [extractedFormula, extractionAnchors_evaluate, ObjectFormula.evaluate,
    ObjectFoundationFinite.Finite.normalized,
    IndependentGeneratedObjectMatching.extracted]
  have hn :
      ((IndependentGeometryPrimitive.extraction t) (.normalize _
        (Extraction.point (IndependentGeometryPrimitive.extraction t) .source))).down =
        some (IndependentGeneratedObjectMatching.normalized
          (IndependentGeometryPrimitive.extraction t) ht) :=
    (Option.some_get _).symm
  simp only [IndependentGeometryPrimitive.extraction] at hn
  constructor
  · rintro ⟨_, hv, hm, hr, hs⟩
    exact ⟨
      (ObjectFoundationFinite.prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hv)),
      (ObjectFoundationFinite.prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hm)),
      (ObjectFoundationFinite.prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hr)),
      (ObjectFoundationFinite.prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hs))⟩
  · rintro ⟨hv, hm, hr, hs⟩
    refine ⟨?_,
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((ObjectFoundationFinite.prop_eq_true_iff _).mpr hv)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((ObjectFoundationFinite.prop_eq_true_iff _).mpr hm)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((ObjectFoundationFinite.prop_eq_true_iff _).mpr hr)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((ObjectFoundationFinite.prop_eq_true_iff _).mpr hs))⟩
    apply ULift.ext
    apply ULift.ext
    exact hn

def matchCell (q : IndependentGeneratedObjectMatching.Query U) (value : Bool) :
    ObjectFormula.{u, v, w} U :=
  .cell (.matching q) (ULift.up value)

@[simp] theorem matchCell_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentGeneratedObjectMatching.Query U) (value : Bool) :
    (matchCell q value : ObjectFormula.{u, v, w} U).evaluate t ↔
      IndependentGeometryPrimitive.matching t q = value := by
  exact IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _

@[simp] theorem compositionCell_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentCorePrimitive.Composition.Query U) :
    (ObjectFormula.cell (.composition q) (ULift.up True) :
      ObjectFormula.{u, v, w} U).evaluate t ↔
      IndependentGeometryPrimitive.composition t q := by
  exact IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _

@[simp] theorem compositionEqTrue_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentCorePrimitive.Composition.Query U) :
    t (.composition q) = ULift.up True ↔
      IndependentGeometryPrimitive.composition t q := by
  exact IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _

@[simp] theorem compositionFalseCell_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentCorePrimitive.Composition.Query U) :
    (ObjectFormula.cell (.composition q) (ULift.up False) :
      ObjectFormula.{u, v, w} U).evaluate t ↔
      ¬ IndependentGeometryPrimitive.composition t q := by
  change t (.composition q) = ULift.up False ↔
    ¬ (t (.composition q)).down
  rw [IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff]
  constructor
  · intro h hp
    exact h ▸ hp
  · intro hn
    exact propext (iff_false_intro hn)

@[simp] theorem formationCell_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentCorePrimitive.ObjectFormation.Query U)
    (value : IndependentCorePrimitive.SelectedValue.{u}) :
    (ObjectFormula.cell (.formation q) (ULift.up value) :
      ObjectFormula.{u, v, w} U).evaluate t ↔
      IndependentGeometryPrimitive.formation t q = value := by
  exact IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _

@[simp] theorem formationEq_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (q : IndependentCorePrimitive.ObjectFormation.Query U)
    (value : IndependentCorePrimitive.SelectedValue.{u}) :
    t (.formation q) = ULift.up value ↔
      IndependentGeometryPrimitive.formation t q = value := by
  exact IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _

namespace Matching

def familyPresent (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t))
    (F : AtomFamily U) (flag : Bool) (a : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.family F) flag) (extractedFormula t ht a)

def familyAbsent (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t))
    (F : AtomFamily U) (flag : Bool) (a : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.family F) flag)
    (.implies (extractedFormula t ht a) .falsity)

def relationPresent
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .cell (.composition (.relation C.family hf a b)) (ULift.up True)

def relationAbsent
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .cell (.composition (.relation C.family hf a b)) (ULift.up False)

def identificationPresent
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .cell (.composition (.identification C.family hf a b)) (ULift.up True)

def identificationAbsent
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .cell (.composition (.identification C.family hf a b)) (ULift.up False)

def configurationFamilyTrue (C : AtomConfiguration U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) true) (matchCell (.family C.family) true)

def configurationFamilyFalse (C : AtomConfiguration U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) false) (matchCell (.family C.family) false)

def objectTrue (_t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A : ArchitectureObject U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.object A) true)
    (.and (matchCell (.configuration A.configuration) true)
      (.and
        (.cell (.formation (.structureMaps A.configuration))
          (ULift.up (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u})))
        (.cell (.formation (.selectedQuantities A.configuration))
          (ULift.up (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u})))))

def objectConfigurationFalse (A : ArchitectureObject U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.object A) false) (matchCell (.configuration A.configuration) false)

def objectStructureMapsValue
    (A : ArchitectureObject U) (value : SelectedValue.{u}) : ObjectFormula.{u, v, u + 1} U :=
  .and (matchCell (.object A) false)
    (.cell (.formation (.structureMaps A.configuration)) (ULift.up value))

def objectSelectedQuantitiesValue
    (A : ArchitectureObject U) (value : SelectedValue.{u}) : ObjectFormula.{u, v, u + 1} U :=
  .and (matchCell (.object A) false)
    (.cell (.formation (.selectedQuantities A.configuration)) (ULift.up value))

def FamilyMismatch (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t))
    (F : AtomFamily U) (a : U.Atom) : Prop :=
  (F.mem a ∧ (familyAbsent t ht F false a).evaluate t) ∨
    (¬ F.mem a ∧ (familyPresent t ht F false a).evaluate t)

def ConfigurationMismatch (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) : Prop :=
  (C.relation a b ∧ (relationAbsent C hf a b).evaluate t) ∨
    (¬ C.relation a b ∧ (relationPresent C hf a b).evaluate t) ∨
    (C.identification a b ∧ (identificationAbsent C hf a b).evaluate t) ∨
    (¬ C.identification a b ∧ (identificationPresent C hf a b).evaluate t)

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) : Prop where
  familyTrue : ∀ F, IndependentGeometryPrimitive.matching t (.family F) = true →
    ∀ a, (F.mem a → (familyPresent t ht F true a).evaluate t) ∧
      (¬ F.mem a → (familyAbsent t ht F true a).evaluate t)
  familyFalse : ∀ F, IndependentGeometryPrimitive.matching t (.family F) = false →
    ∃ a, FamilyMismatch t ht F a
  configurationTrue : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = true →
    ∀ (hf : C.family.ListFinite) a b,
      (C.relation a b → (relationPresent C hf a b).evaluate t) ∧
      (¬ C.relation a b → (relationAbsent C hf a b).evaluate t) ∧
      (C.identification a b → (identificationPresent C hf a b).evaluate t) ∧
      (¬ C.identification a b → (identificationAbsent C hf a b).evaluate t)
  configurationFamilyTrue : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = true →
    (configurationFamilyTrue C).evaluate t
  configurationFalse : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = false →
    (configurationFamilyFalse C).evaluate t ∨
      ∃ (hf : C.family.ListFinite) (a b : U.Atom),
        ConfigurationMismatch t C hf a b
  objectTrue : ∀ A, IndependentGeometryPrimitive.matching t (.object A) = true →
    (objectTrue t A).evaluate t
  objectFalse : ∀ A, IndependentGeometryPrimitive.matching t (.object A) = false →
    (objectConfigurationFalse A).evaluate t ∨
      (∃ value, (objectStructureMapsValue A value).evaluate t ∧
        value ≠ (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u})) ∨
      (∃ value, (objectSelectedQuantitiesValue A value).evaluate t ∧
        value ≠ (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u}))

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) :
    IndependentGeneratedObjectMatching.IsLawful
        (IndependentGeometryPrimitive.extraction t) ht
        (IndependentGeometryPrimitive.composition t)
        (IndependentGeometryPrimitive.formation t)
        (IndependentGeometryPrimitive.matching t) ↔ Instances t ht := by
  constructor
  · intro hl
    refine {
      familyTrue := ?_
      familyFalse := ?_
      configurationTrue := ?_
      configurationFamilyTrue := ?_
      configurationFalse := ?_
      objectTrue := ?_
      objectFalse := ?_ }
    · intro F hF a
      have hp := hl.family_true F hF a
      constructor
      · intro ha
        exact ⟨(matchCell_evaluate t _ _).2 hF,
          (extractedFormula_evaluate_iff t ht a).2 (hp.mp ha)⟩
      · intro ha
        refine ⟨(matchCell_evaluate t _ _).2 hF, ?_⟩
        intro he
        exact ha (hp.mpr ((extractedFormula_evaluate_iff t ht a).1 he))
    · intro F hF
      obtain ⟨a, hm⟩ := hl.family_false F hF
      refine ⟨a, ?_⟩
      by_cases ha : F.mem a
      · left
        refine ⟨ha, (matchCell_evaluate t _ _).2 hF, ?_⟩
        intro he
        exact hm ⟨fun _ => (extractedFormula_evaluate_iff t ht a).1 he, fun _ => ha⟩
      · right
        refine ⟨ha, (matchCell_evaluate t _ _).2 hF, ?_⟩
        apply (extractedFormula_evaluate_iff t ht a).2
        by_contra he
        exact hm ⟨fun h => (ha h).elim, fun h => (he h).elim⟩
    · intro C hC hf a b
      have hp := (hl.configuration_true C hC).2 hf a b
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro hr
        exact (compositionCell_evaluate t _).2 (hp.1.mp hr)
      · intro hr
        exact (compositionFalseCell_evaluate t _).2 (fun ht' => hr (hp.1.mpr ht'))
      · intro hi
        exact (compositionCell_evaluate t _).2 (hp.2.mp hi)
      · intro hi
        exact (compositionFalseCell_evaluate t _).2 (fun ht' => hi (hp.2.mpr ht'))
    · intro C hC
      exact ⟨(matchCell_evaluate t _ _).2 hC,
        (matchCell_evaluate t _ _).2 (hl.configuration_true C hC).1⟩
    · intro C hC
      rcases hl.configuration_false C hC with hF | ⟨hf, a, b, hp⟩
      · left
        exact ⟨(matchCell_evaluate t _ _).2 hC, (matchCell_evaluate t _ _).2 hF⟩
      · right
        refine ⟨hf, a, b, ?_⟩
        by_cases hr : C.relation a b
        · by_cases htr : IndependentGeometryPrimitive.composition t
              (.relation C.family hf a b)
          · have hriff : C.relation a b ↔ IndependentGeometryPrimitive.composition t
                (.relation C.family hf a b) := ⟨fun _ => htr, fun _ => hr⟩
            by_cases hi : C.identification a b
            · by_cases hti : IndependentGeometryPrimitive.composition t
                  (.identification C.family hf a b)
              · exact (hp ⟨hriff, ⟨fun _ => hti, fun _ => hi⟩⟩).elim
              · exact Or.inr (Or.inr (Or.inl
                  ⟨hi, (compositionFalseCell_evaluate t _).2 hti⟩))
            · by_cases hti : IndependentGeometryPrimitive.composition t
                  (.identification C.family hf a b)
              · exact Or.inr (Or.inr (Or.inr
                  ⟨hi, (compositionCell_evaluate t _).2 hti⟩))
              · exact (hp ⟨hriff, ⟨fun h => (hi h).elim, fun h => (hti h).elim⟩⟩).elim
          · exact Or.inl ⟨hr, (compositionFalseCell_evaluate t _).2 htr⟩
        · by_cases htr : IndependentGeometryPrimitive.composition t
              (.relation C.family hf a b)
          · exact Or.inr (Or.inl ⟨hr, (compositionCell_evaluate t _).2 htr⟩)
          · have hriff : C.relation a b ↔ IndependentGeometryPrimitive.composition t
                (.relation C.family hf a b) :=
                ⟨fun h => (hr h).elim, fun h => (htr h).elim⟩
            by_cases hi : C.identification a b
            · by_cases hti : IndependentGeometryPrimitive.composition t
                  (.identification C.family hf a b)
              · exact (hp ⟨hriff, ⟨fun _ => hti, fun _ => hi⟩⟩).elim
              · exact Or.inr (Or.inr (Or.inl
                  ⟨hi, (compositionFalseCell_evaluate t _).2 hti⟩))
            · by_cases hti : IndependentGeometryPrimitive.composition t
                  (.identification C.family hf a b)
              · exact Or.inr (Or.inr (Or.inr
                  ⟨hi, (compositionCell_evaluate t _).2 hti⟩))
              · exact (hp ⟨hriff, ⟨fun h => (hi h).elim, fun h => (hti h).elim⟩⟩).elim
    · intro A hA
      have ha := hl.object_true A hA
      exact ⟨(matchCell_evaluate t _ _).2 hA,
        (matchCell_evaluate t _ _).2 ha.1,
        (formationCell_evaluate t _ _).2 ha.2.1,
        (formationCell_evaluate t _ _).2 ha.2.2⟩
    · intro A hA
      rcases hl.object_false A hA with hC | hS | hQ
      · left
        exact ⟨(matchCell_evaluate t _ _).2 hA, (matchCell_evaluate t _ _).2 hC⟩
      · right; left
        refine ⟨IndependentGeometryPrimitive.formation t
          (.structureMaps A.configuration), ?_, hS⟩
        exact ⟨(matchCell_evaluate t _ _).2 hA,
          (formationCell_evaluate t _ _).2 rfl⟩
      · right; right
        refine ⟨IndependentGeometryPrimitive.formation t
          (.selectedQuantities A.configuration), ?_, hQ⟩
        exact ⟨(matchCell_evaluate t _ _).2 hA,
          (formationCell_evaluate t _ _).2 rfl⟩
  · intro hi
    refine {
      family_true := ?_
      family_false := ?_
      configuration_true := ?_
      configuration_false := ?_
      object_true := ?_
      object_false := ?_ }
    · intro F hF a
      constructor
      · intro ha
        have hp := (hi.familyTrue F hF a).1 ha
        exact (extractedFormula_evaluate_iff t ht a).1 hp.2
      · intro he
        by_contra ha
        have hp := (hi.familyTrue F hF a).2 ha
        exact hp.2 ((extractedFormula_evaluate_iff t ht a).2 he)
    · intro F hF
      obtain ⟨a, hm⟩ := hi.familyFalse F hF
      refine ⟨a, ?_⟩
      rcases hm with ⟨ha, hm⟩ | ⟨ha, hm⟩
      · intro heq
        exact hm.2 ((extractedFormula_evaluate_iff t ht a).2 (heq.mp ha))
      · intro heq
        exact ha (heq.mpr ((extractedFormula_evaluate_iff t ht a).1 hm.2))
    · intro C hC
      refine ⟨?_, ?_⟩
      · exact (matchCell_evaluate t _ _).1 (hi.configurationFamilyTrue C hC).2
      · intro hf a b
        have hp := hi.configurationTrue C hC hf a b
        constructor
        · constructor
          · intro hr
            exact (compositionCell_evaluate t _).1 (hp.1 hr)
          · intro htr
            by_contra hr
            exact (compositionFalseCell_evaluate t _).1 (hp.2.1 hr) htr
        · constructor
          · intro hx
            exact (compositionCell_evaluate t _).1 (hp.2.2.1 hx)
          · intro htx
            by_contra hx
            exact (compositionFalseCell_evaluate t _).1 (hp.2.2.2 hx) htx
    · intro C hC
      rcases hi.configurationFalse C hC with hF | ⟨hf, a, b, hm⟩
      · exact Or.inl ((matchCell_evaluate t _ _).1 hF.2)
      · right
        refine ⟨hf, a, b, ?_⟩
        rcases hm with hm | hm | hm | hm
        · intro hp
          exact (compositionFalseCell_evaluate t _).1 hm.2 (hp.1.mp hm.1)
        · intro hp
          exact hm.1 (hp.1.mpr ((compositionCell_evaluate t _).1 hm.2))
        · intro hp
          exact (compositionFalseCell_evaluate t _).1 hm.2 (hp.2.mp hm.1)
        · intro hp
          exact hm.1 (hp.2.mpr ((compositionCell_evaluate t _).1 hm.2))
    · intro A hA
      have ha := hi.objectTrue A hA
      exact ⟨(matchCell_evaluate t _ _).1 ha.2.1,
        (formationCell_evaluate t _ _).1 ha.2.2.1,
        (formationCell_evaluate t _ _).1 ha.2.2.2⟩
    · intro A hA
      rcases hi.objectFalse A hA with hC | hS | hQ
      · exact Or.inl ((matchCell_evaluate t _ _).1 hC.2)
      · right; left
        obtain ⟨value, hv, hne⟩ := hS
        intro heq
        exact hne ((formationCell_evaluate t _ _).1 hv.2 |>.symm.trans heq)
      · right; right
        obtain ⟨value, hv, hne⟩ := hQ
        intro heq
        exact hne ((formationCell_evaluate t _ _).1 hv.2 |>.symm.trans heq)

end Matching

namespace Active

def someRow (A : ArchitectureObject U) (q : IndependentGeometryPrimitive.DependentQuery.{u, v} A)
    (value : q.Value) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.object A) true) (.cell (.atObject A q) (some value))

def noRow (A : ArchitectureObject U) (q : IndependentGeometryPrimitive.DependentQuery.{u, v} A) :
    ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.object A) false) (.cell (.atObject A q) none)

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  someRow : ∀ A q, IndependentGeometryPrimitive.matching t (.object A) = true →
    ∃ value, (someRow A q value).evaluate t
  noRow : ∀ A q, IndependentGeometryPrimitive.matching t (.object A) = false →
    (noRow A q).evaluate t

theorem activeTyped_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentGeometryPrimitive.IsActiveTyped t ↔ Instances t := by
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · intro A q hA
      have hs := (ht A q).2 hA
      cases ho : t (.atObject A q) with
      | none => simp [ho] at hs
      | some value =>
          refine ⟨value, ?_⟩
          simpa only [someRow, ObjectFormula.evaluate, matchCell_evaluate] using
            And.intro hA ho
    · intro A q hA
      have hn := IndependentGeometryPrimitive.inactive_eq_none t ht A hA q
      simpa only [noRow, ObjectFormula.evaluate, matchCell_evaluate] using
        And.intro hA hn
  · intro hi A q
    constructor
    · intro hs
      by_cases hA : IndependentGeometryPrimitive.matching t (.object A) = true
      · exact hA
      · have hfalse : IndependentGeometryPrimitive.matching t (.object A) = false :=
          Bool.eq_false_of_not_eq_true hA
        have hn := hi.noRow A q hfalse
        simp only [noRow, ObjectFormula.evaluate, matchCell_evaluate] at hn
        rw [hn.2] at hs
        exact Bool.noConfusion hs
    · intro hA
      obtain ⟨value, hv⟩ := hi.someRow A q hA
      simp only [someRow, ObjectFormula.evaluate, matchCell_evaluate] at hv
      rw [hv.2]
      rfl

end Active

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectMatchingFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectMatchingFinite
