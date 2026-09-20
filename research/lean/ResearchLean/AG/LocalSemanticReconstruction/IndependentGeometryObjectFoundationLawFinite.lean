import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for primitive object foundation laws

The formula families below expose every primitive object cell used by the
foundation laws.  Carrier references read from the table are anchored by
their own cells before they are used in a static equality or as a query
argument.  No completed object, law certificate, or arbitrary proposition is
a formula constructor.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite

noncomputable section

universe u v

open IndependentCorePrimitive IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

@[simp] theorem prop_eq_true_iff (p : Prop) : p = True ↔ p := by
  constructor
  · intro h
    exact h.symm ▸ trivial
  · exact fun hp => propext (iff_true_intro hp)

theorem ulift_prop_true_iff (left : ULift.{v} Prop) :
    left = ULift.up.{v} True ↔ left.down :=
  (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff left True).trans
    (prop_eq_true_iff left.down)

def extractionAnchors (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) : ObjectFormula.{u, v, u + 1} U :=
  .and (.cell (.extraction (.selected .source)) (t (.extraction (.selected .source))))
    (.and (.cell (.extraction (.selected .vocabulary))
        (t (.extraction (.selected .vocabulary))))
      (.and (.cell (.extraction (.selected .semantic))
          (t (.extraction (.selected .semantic))))
        (.and (.cell (.extraction (.selected .resolution))
          (t (.extraction (.selected .resolution)))) body)))

@[simp] theorem extractionAnchors_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) :
    (extractionAnchors t body).evaluate t ↔ body.evaluate t := by
  simp [extractionAnchors, ObjectFormula.evaluate]

namespace Extraction

def normalizeSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (S : Type u) (s y : S) : ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.cell (.extraction (.normalize S s)) (ULift.up (ULift.up (some y))))

def normalizeNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (S : Type u) (s : S) : ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.cell (.extraction (.normalize S s)) (ULift.up (ULift.up none)))

def vocabularyInactive (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (V : Type u) (x : V) (a : U.Atom) : ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.implies (.notEqual V (IndependentCorePrimitive.Extraction.carrier
        (IndependentGeometryPrimitive.extraction t) .vocabulary))
      (.cell (.extraction (.vocabulary V x a)) (ULift.up (ULift.up False))))

def semanticInactive (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (M S : Type u) (m : M) (s : S) (a : U.Atom) :
    ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.implies
      (.or (.notEqual M (IndependentCorePrimitive.Extraction.carrier
          (IndependentGeometryPrimitive.extraction t) .semantic))
        (.notEqual S (IndependentCorePrimitive.Extraction.carrier
          (IndependentGeometryPrimitive.extraction t) .source)))
      (.cell (.extraction (.semantic M S m s a)) (ULift.up (ULift.up False))))

def resolutionInactive (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (R S : Type u) (r : R) (s : S) (a : U.Atom) :
    ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.implies
      (.or (.notEqual R (IndependentCorePrimitive.Extraction.carrier
          (IndependentGeometryPrimitive.extraction t) .resolution))
        (.notEqual S (IndependentCorePrimitive.Extraction.carrier
          (IndependentGeometryPrimitive.extraction t) .source)))
      (.cell (.extraction (.resolution R S r s a)) (ULift.up (ULift.up False))))

def sourceInactive (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (S : Type u) (s : S) (a : U.Atom) : ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.implies (.notEqual S (IndependentCorePrimitive.Extraction.carrier
        (IndependentGeometryPrimitive.extraction t) .source))
      (.cell (.extraction (.source S s a)) (ULift.up (ULift.up False))))

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  normalizeSome : ∀ S s, S = IndependentCorePrimitive.Extraction.carrier
      (IndependentGeometryPrimitive.extraction t) .source →
    ∃ y, (normalizeSome t S s y).evaluate t
  normalizeNone : ∀ S s, S ≠ IndependentCorePrimitive.Extraction.carrier
      (IndependentGeometryPrimitive.extraction t) .source →
    (normalizeNone t S s).evaluate t
  vocabulary : ∀ V x a, (vocabularyInactive t V x a).evaluate t
  semantic : ∀ M S m s a, (semanticInactive t M S m s a).evaluate t
  resolution : ∀ R S r s a, (resolutionInactive t R S r s a).evaluate t
  source : ∀ S s a, (sourceInactive t S s a).evaluate t

theorem typed_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentCorePrimitive.Extraction.IsTyped
        (IndependentGeometryPrimitive.extraction t) ↔ Instances t := by
  constructor
  · intro hp
    refine {
      normalizeSome := ?_
      normalizeNone := ?_
      vocabulary := ?_
      semantic := ?_
      resolution := ?_
      source := ?_ }
    · intro S s hS
      have hs := (hp.normalize S s).2 hS
      cases hv : ((IndependentGeometryPrimitive.extraction t) (.normalize S s)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [normalizeSome, extractionAnchors_evaluate, ObjectFormula.evaluate,
            IndependentGeometryPrimitive.extraction]
          apply ULift.ext
          apply ULift.ext
          exact hv
    · intro S s hS
      have hs : ¬ ((IndependentGeometryPrimitive.extraction t) (.normalize S s)).down.isSome :=
        mt (hp.normalize S s).1 hS
      have hn : ((IndependentGeometryPrimitive.extraction t) (.normalize S s)).down = none := by
        cases hv : ((IndependentGeometryPrimitive.extraction t) (.normalize S s)).down <;>
          simp_all
      simp only [normalizeNone, extractionAnchors_evaluate, ObjectFormula.evaluate,
        IndependentGeometryPrimitive.extraction]
      apply ULift.ext
      apply ULift.ext
      exact hn
    · intro V x a
      simp only [vocabularyInactive, extractionAnchors_evaluate, ObjectFormula.evaluate]
      intro hV
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (hp.vocabulary V x a hV))
    · intro M S m s a
      simp only [semanticInactive, extractionAnchors_evaluate, ObjectFormula.evaluate]
      intro hwrong
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (hp.semantic M S m s a (by
        exact fun h => hwrong.elim (fun hn => hn h.1) (fun hn => hn h.2))))
    · intro R S r s a
      simp only [resolutionInactive, extractionAnchors_evaluate, ObjectFormula.evaluate]
      intro hwrong
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (hp.resolution R S r s a (by
        exact fun h => hwrong.elim (fun hn => hn h.1) (fun hn => hn h.2))))
    · intro S s a
      simp only [sourceInactive, extractionAnchors_evaluate, ObjectFormula.evaluate]
      intro hS
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (hp.source S s a hS))
  · intro hi
    refine {
      normalize := ?_
      vocabulary := ?_
      semantic := ?_
      resolution := ?_
      source := ?_ }
    · intro S s
      constructor
      · intro hs
        by_contra hS
        have hn := hi.normalizeNone S s hS
        simp only [normalizeNone, extractionAnchors_evaluate, ObjectFormula.evaluate,
          IndependentGeometryPrimitive.extraction] at hn
        have he := congrArg (fun value => value.down.down) hn
        change ((t (.extraction (.normalize S s))).down.down).isSome = true at hs
        change (t (.extraction (.normalize S s))).down.down = none at he
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hS
        obtain ⟨y, hy⟩ := hi.normalizeSome S s hS
        simp only [normalizeSome, extractionAnchors_evaluate, ObjectFormula.evaluate,
          IndependentGeometryPrimitive.extraction] at hy
        have he := congrArg (fun value => value.down.down) hy
        change (t (.extraction (.normalize S s))).down.down = some y at he
        change ((t (.extraction (.normalize S s))).down.down).isSome = true
        rw [he]
        rfl
    · intro V x a hV
      have hi := hi.vocabulary V x a
      simp only [vocabularyInactive, extractionAnchors_evaluate, ObjectFormula.evaluate] at hi
      have he := hi hV
      exact fun hp => by
        have hfalse := congrArg (fun value => value.down.down) he
        change (t (.extraction (.vocabulary V x a))).down.down = False at hfalse
        change (t (.extraction (.vocabulary V x a))).down.down at hp
        rw [hfalse] at hp
        exact hp
    · intro M S m s a hwrong
      have hi := hi.semantic M S m s a
      simp only [semanticInactive, extractionAnchors_evaluate, ObjectFormula.evaluate] at hi
      have he := hi (by
        by_cases hM : M = IndependentCorePrimitive.Extraction.carrier
            (IndependentGeometryPrimitive.extraction t) .semantic
        · exact Or.inr (fun hS => hwrong ⟨hM, hS⟩)
        · exact Or.inl hM)
      exact fun hp => by
        have hfalse := congrArg (fun value => value.down.down) he
        change (t (.extraction (.semantic M S m s a))).down.down = False at hfalse
        change (t (.extraction (.semantic M S m s a))).down.down at hp
        rw [hfalse] at hp
        exact hp
    · intro R S r s a hwrong
      have hi := hi.resolution R S r s a
      simp only [resolutionInactive, extractionAnchors_evaluate, ObjectFormula.evaluate] at hi
      have he := hi (by
        by_cases hR : R = IndependentCorePrimitive.Extraction.carrier
            (IndependentGeometryPrimitive.extraction t) .resolution
        · exact Or.inr (fun hS => hwrong ⟨hR, hS⟩)
        · exact Or.inl hR)
      exact fun hp => by
        have hfalse := congrArg (fun value => value.down.down) he
        change (t (.extraction (.resolution R S r s a))).down.down = False at hfalse
        change (t (.extraction (.resolution R S r s a))).down.down at hp
        rw [hfalse] at hp
        exact hp
    · intro S s a hS
      have hi := hi.source S s a
      simp only [sourceInactive, extractionAnchors_evaluate, ObjectFormula.evaluate] at hi
      have he := hi hS
      exact fun hp => by
        have hfalse := congrArg (fun value => value.down.down) he
        change (t (.extraction (.source S s a))).down.down = False at hfalse
        change (t (.extraction (.source S s a))).down.down at hp
        rw [hfalse] at hp
        exact hp

end Extraction

namespace Composition

def relation (F : AtomFamily U) (hf : F.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .implies (.cell (.composition (.relation F hf a b)) (ULift.up True))
    (.and (.equal (F.mem a) True) (.equal (F.mem b) True))

def identification (F : AtomFamily U) (hf : F.ListFinite) (a b : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .implies (.cell (.composition (.identification F hf a b)) (ULift.up True))
    (.and (.equal (F.mem a) True) (.equal (F.mem b) True))

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  relation : ∀ F hf a b, (relation F hf a b).evaluate t
  identification : ∀ F hf a b, (identification F hf a b).evaluate t

theorem lawful_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentCorePrimitive.Composition.IsLawful
        (IndependentGeometryPrimitive.composition t) ↔ Instances t := by
  constructor
  · intro ht
    exact {
      relation := fun F hf a b hcell => by
        have hab := ht.relation F hf a b ((ulift_prop_true_iff _).mp hcell)
        exact ⟨(prop_eq_true_iff _).mpr hab.1, (prop_eq_true_iff _).mpr hab.2⟩
      identification := fun F hf a b hcell => by
        have hab := ht.identification F hf a b ((ulift_prop_true_iff _).mp hcell)
        exact ⟨(prop_eq_true_iff _).mpr hab.1, (prop_eq_true_iff _).mpr hab.2⟩ }
  · intro hi
    exact {
      relation := fun F hf a b hab => by
        have hi' := hi.relation F hf a b ((ulift_prop_true_iff _).mpr hab)
        exact ⟨(prop_eq_true_iff _).mp hi'.1, (prop_eq_true_iff _).mp hi'.2⟩
      identification := fun F hf a b hab => by
        have hi' := hi.identification F hf a b ((ulift_prop_true_iff _).mpr hab)
        exact ⟨(prop_eq_true_iff _).mp hi'.1, (prop_eq_true_iff _).mp hi'.2⟩ }

end Composition

namespace Atom

def atomEquality (a b : U.Atom) : ObjectFormula.{u, v, u} U :=
  .equal a b

def coordinateTruth (a b : U.Atom) : ObjectFormula.{u, v, 0} U :=
  .equal (SameCoordinates U a b) True

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  inhabited : ∃ a : U.Atom, (ObjectFormula.truth : ObjectFormula.{u, v, 0} U).evaluate t
  coordinates_forward : ∀ a b, SameCoordinates U a b → (atomEquality a b).evaluate t
  coordinates_backward : ∀ a b, a = b → (coordinateTruth a b).evaluate t

theorem laws_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentCoreTableAssembly.AtomLaws U ↔ Instances t := by
  constructor
  · rintro ⟨⟨a⟩, hp⟩
    exact {
      inhabited := ⟨a, trivial⟩
      coordinates_forward := fun x y hxy => (hp x y).mp hxy
      coordinates_backward := fun x y hxy =>
        (prop_eq_true_iff (SameCoordinates U x y)).mpr ((hp x y).mpr hxy) }
  · intro hi
    obtain ⟨a, _⟩ := hi.inhabited
    refine ⟨⟨a⟩, ?_⟩
    intro x y
    constructor
    · exact hi.coordinates_forward x y
    · intro hxy
      exact (prop_eq_true_iff (SameCoordinates U x y)).mp
        (hi.coordinates_backward x y hxy)

end Atom

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite
