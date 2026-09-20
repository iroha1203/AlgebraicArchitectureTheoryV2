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

def familyTrue (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t))
    (F : AtomFamily U) (a : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.family F) true)
    (.iff (.equal (F.mem a) True) (extractedFormula t ht a))

def familyFalse (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t))
    (F : AtomFamily U) (a : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.family F) false)
    (.implies (.iff (.equal (F.mem a) True) (extractedFormula t ht a)) .falsity)

def configurationTrue (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (C : AtomConfiguration U) (hf : C.family.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) true)
    (.and (matchCell (.family C.family) true)
      (.and
        (.iff (.equal (C.relation a b) True)
          (.cell (.composition (.relation C.family hf a b)) (ULift.up True)))
        (.iff (.equal (C.identification a b) True)
          (.cell (.composition (.identification C.family hf a b)) (ULift.up True)))))

def configurationFamilyTrue (C : AtomConfiguration U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) true) (matchCell (.family C.family) true)

def configurationFamilyFalse (C : AtomConfiguration U) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) false) (matchCell (.family C.family) false)

def configurationPointFalse (C : AtomConfiguration U)
    (hf : C.family.ListFinite) (a b : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .and (matchCell (.configuration C) false)
    (.implies
      (.and
        (.iff (.equal (C.relation a b) True)
          (.cell (.composition (.relation C.family hf a b)) (ULift.up True)))
        (.iff (.equal (C.identification a b) True)
          (.cell (.composition (.identification C.family hf a b)) (ULift.up True))))
      .falsity)

def objectTrue (t : IndependentGeometryPrimitive.Table.{u, v} U)
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

def objectStructureMapsFalse (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A : ArchitectureObject U) : ObjectFormula.{u, v, u + 1} U :=
  .and (matchCell (.object A) false)
    (.and (.cell (.formation (.structureMaps A.configuration))
        (t (.formation (.structureMaps A.configuration))))
      (.notEqual (t (.formation (.structureMaps A.configuration))).down
        (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u})))

def objectSelectedQuantitiesFalse (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A : ArchitectureObject U) : ObjectFormula.{u, v, u + 1} U :=
  .and (matchCell (.object A) false)
    (.and (.cell (.formation (.selectedQuantities A.configuration))
        (t (.formation (.selectedQuantities A.configuration))))
      (.notEqual (t (.formation (.selectedQuantities A.configuration))).down
        (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u})))

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) : Prop where
  familyTrue : ∀ F, IndependentGeometryPrimitive.matching t (.family F) = true →
    ∀ a, (familyTrue t ht F a).evaluate t
  familyFalse : ∀ F, IndependentGeometryPrimitive.matching t (.family F) = false →
    ∃ a, (familyFalse t ht F a).evaluate t
  configurationTrue : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = true →
    ∀ (hf : C.family.ListFinite) a b, (configurationTrue t C hf a b).evaluate t
  configurationFamilyTrue : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = true →
    (configurationFamilyTrue C).evaluate t
  configurationFalse : ∀ C,
    IndependentGeometryPrimitive.matching t (.configuration C) = false →
    (configurationFamilyFalse C).evaluate t ∨
      ∃ (hf : C.family.ListFinite) (a b : U.Atom),
        (configurationPointFalse C hf a b).evaluate t
  objectTrue : ∀ A, IndependentGeometryPrimitive.matching t (.object A) = true →
    (objectTrue t A).evaluate t
  objectFalse : ∀ A, IndependentGeometryPrimitive.matching t (.object A) = false →
    (objectConfigurationFalse A).evaluate t ∨
      (objectStructureMapsFalse t A).evaluate t ∨
      (objectSelectedQuantitiesFalse t A).evaluate t

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
      simpa only [familyTrue, ObjectFormula.evaluate, matchCell_evaluate,
        extractedFormula_evaluate_iff, ObjectFoundationFinite.prop_eq_true_iff] using
        And.intro hF (hl.family_true F hF a)
    · intro F hF
      obtain ⟨a, ha⟩ := hl.family_false F hF
      refine ⟨a, ?_⟩
      simpa only [familyFalse, ObjectFormula.evaluate, matchCell_evaluate,
        extractedFormula_evaluate_iff, ObjectFoundationFinite.prop_eq_true_iff] using
        And.intro hF ha
    · intro C hC hf a b
      have hc := hl.configuration_true C hC
      simpa only [configurationTrue, ObjectFormula.evaluate, matchCell_evaluate,
        ObjectFoundationFinite.prop_eq_true_iff,
        compositionCell_evaluate, compositionEqTrue_iff] using
        ⟨hC, hc.1, hc.2 hf a b⟩
    · intro C hC
      simpa only [configurationFamilyTrue, ObjectFormula.evaluate,
        matchCell_evaluate] using And.intro hC (hl.configuration_true C hC).1
    · intro C hC
      rcases hl.configuration_false C hC with hF | ⟨hf, a, b, hp⟩
      · left
        simpa only [configurationFamilyFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using And.intro hC hF
      · right
        refine ⟨hf, a, b, ?_⟩
        simpa only [configurationPointFalse, ObjectFormula.evaluate,
          matchCell_evaluate, ObjectFoundationFinite.prop_eq_true_iff,
          compositionCell_evaluate, compositionEqTrue_iff] using And.intro hC hp
    · intro A hA
      have ha := hl.object_true A hA
      simpa only [objectTrue, ObjectFormula.evaluate, matchCell_evaluate,
        formationCell_evaluate, formationEq_iff] using ⟨hA, ha⟩
    · intro A hA
      rcases hl.object_false A hA with hC | hS | hQ
      · left
        simpa only [objectConfigurationFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using And.intro hA hC
      · right; left
        simpa only [objectStructureMapsFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using ⟨hA, trivial, hS⟩
      · right; right
        simpa only [objectSelectedQuantitiesFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using ⟨hA, trivial, hQ⟩
  · intro hi
    refine {
      family_true := ?_
      family_false := ?_
      configuration_true := ?_
      configuration_false := ?_
      object_true := ?_
      object_false := ?_ }
    · intro F hF a
      have hf := hi.familyTrue F hF a
      simpa only [familyTrue, ObjectFormula.evaluate, matchCell_evaluate,
        extractedFormula_evaluate_iff, ObjectFoundationFinite.prop_eq_true_iff] using hf.2
    · intro F hF
      obtain ⟨a, ha⟩ := hi.familyFalse F hF
      refine ⟨a, ?_⟩
      simpa only [familyFalse, ObjectFormula.evaluate, matchCell_evaluate,
        extractedFormula_evaluate_iff, ObjectFoundationFinite.prop_eq_true_iff] using ha.2
    · intro C hC
      refine ⟨?_, ?_⟩
      · have h := hi.configurationFamilyTrue C hC
        simpa only [configurationFamilyTrue, ObjectFormula.evaluate,
          matchCell_evaluate] using h.2
      · intro hf a b
        have h := hi.configurationTrue C hC hf a b
        simpa only [configurationTrue, ObjectFormula.evaluate, matchCell_evaluate,
          ObjectFoundationFinite.prop_eq_true_iff,
          compositionCell_evaluate, compositionEqTrue_iff] using h.2.2
    · intro C hC
      rcases hi.configurationFalse C hC with hF | ⟨hf, a, b, hp⟩
      · left
        simpa only [configurationFamilyFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using hF.2
      · right
        refine ⟨hf, a, b, ?_⟩
        simpa only [configurationPointFalse, ObjectFormula.evaluate,
          matchCell_evaluate, ObjectFoundationFinite.prop_eq_true_iff,
          compositionCell_evaluate, compositionEqTrue_iff] using hp.2
    · intro A hA
      have ha := hi.objectTrue A hA
      simpa only [objectTrue, ObjectFormula.evaluate, matchCell_evaluate,
        formationCell_evaluate, formationEq_iff] using ha.2
    · intro A hA
      rcases hi.objectFalse A hA with hC | hS | hQ
      · left
        simpa only [objectConfigurationFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using hC.2
      · right; left
        simpa only [objectStructureMapsFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using hS.2.2
      · right; right
        simpa only [objectSelectedQuantitiesFalse, ObjectFormula.evaluate,
          matchCell_evaluate] using hQ.2.2

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
