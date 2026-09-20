import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for the common core Hom laws

The formulas in this module expose every source, target, and Hom point used by
Atom coherence, extraction, transport matching, generation, and object rows.
They contain no completed map or law certificate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLawFinite

noncomputable section

universe u v w x y

open IndependentCorePrimitive IndependentGeometryTableAssembly
  IndependentFiniteLawFormula IndependentFiniteGraphLawFormula

variable {U : AtomCarrier.{u}} {mode : Mode}

@[simp] private theorem prop_eq_true_iff (p : Prop) : p = True ↔ p := by
  constructor
  · intro h
    exact h.symm ▸ trivial
  · exact fun hp => propext (iff_true_intro hp)

@[simp] private theorem prop_ne_true_iff (p : Prop) : p ≠ True ↔ ¬ p := by
  rw [ne_eq, not_iff_not]
  exact prop_eq_true_iff p

@[simp] private theorem prop_eq_prop_iff (p q : Prop) : p = q ↔ (p ↔ q) :=
  ⟨Iff.of_eq, propext⟩

@[simp] private theorem prop_ne_prop_iff (p q : Prop) : p ≠ q ↔ ¬ (p ↔ q) := by
  exact not_congr (prop_eq_prop_iff p q)

@[simp] theorem double_ulift_eq_iff {alpha : Type w}
    (left : ULift.{x} alpha) (right : alpha) :
    ULift.up.{y} left = ULift.up.{y} (ULift.up.{x} right) ↔ left.down = right := by
  constructor
  · intro h
    exact congrArg (fun value => value.down.down) h
  · intro h
    apply ULift.ext
    apply ULift.ext
    exact h

@[simp] theorem ulift_eq_iff {alpha : Type w}
    (left : ULift.{x} alpha) (right : alpha) :
    left = ULift.up.{x} right ↔ left.down = right := by
  constructor
  · intro h
    exact congrArg ULift.down h
  · intro h
    apply ULift.ext
    exact h

theorem ulift_prop_true_iff (left : ULift.{x} Prop) :
    left = ULift.up.{x} True ↔ left.down :=
  (ulift_eq_iff left True).trans (prop_eq_true_iff left.down)

theorem double_ulift_prop_true_iff (left : ULift.{x} Prop) :
    ULift.up.{y} left = ULift.up.{y} (ULift.up.{x} True) ↔ left.down :=
  (double_ulift_eq_iff left True).trans (prop_eq_true_iff left.down)

/-! ## Atom coherence -/

namespace Atom

inductive Role where
  | pointed
  | upper

def query (role : Role) (direction : Direction) (a b : U.Atom) : Query.{u, v} U mode :=
  match role with
  | .pointed => .pointedAtom direction a b
  | .upper => .atom direction a b

def witness (role : Role) (direction : Direction) (a b : U.Atom) :
    BoolFormula.{max (u + 1) (v + 1), u} (Query.{u, v} U mode) :=
  .cell (query role direction a b) true

def forwardOther (role : Role) (a challenger : U.Atom) :
    BoolFormula.{max (u + 1) (v + 1), u} (Query.{u, v} U mode) :=
  .cell (query role .forward a challenger) false

def backwardOther (role : Role) (b challenger : U.Atom) :
    BoolFormula.{max (u + 1) (v + 1), u} (Query.{u, v} U mode) :=
  .cell (query role .backward challenger b) false

def inverse (role : Role) (a b : U.Atom) :
    BoolFormula.{max (u + 1) (v + 1), 0} (Query.{u, v} U mode) :=
  .iff (.cell (query role .forward a b) true)
    (.cell (query role .backward a b) true)

structure RoleInstances (h : Table.{u, v} U mode) (role : Role) : Prop where
  forward : ∀ a, ∃ b, (witness role .forward a b).evaluate h ∧
    ∀ c, c ≠ b → (forwardOther role a c).evaluate h
  backward : ∀ b, ∃ a, (witness role .backward a b).evaluate h ∧
    ∀ c, c ≠ a → (backwardOther role b c).evaluate h
  inverse : ∀ a b, (inverse role a b).evaluate h

theorem lawful_iff_roleInstances (h : Table.{u, v} U mode) (role : Role) :
    IndependentGeometryHomPrimitive.Atom.IsLawful
      (fun direction a b => h (query role direction a b)) ↔
      RoleInstances h role := by
  constructor
  · intro hp
    refine ⟨?_, ?_, hp.inverse⟩
    · intro a
      obtain ⟨b, hb, hu⟩ := hp.forward a
      refine ⟨b, hb, ?_⟩
      intro c hcb
      cases hq : h (query role .forward a c) with
      | false => exact hq
      | true => exact (hcb (hu c hq)).elim
    · intro b
      obtain ⟨a, ha, hu⟩ := hp.backward b
      refine ⟨a, ha, ?_⟩
      intro c hca
      cases hq : h (query role .backward c b) with
      | false => exact hq
      | true => exact (hca (hu c hq)).elim
  · intro hi
    refine ⟨?_, ?_, hi.inverse⟩
    · intro a
      obtain ⟨b, hb, hu⟩ := hi.forward a
      refine ⟨b, hb, ?_⟩
      intro c hc
      by_contra hcb
      have hf := hu c hcb
      exact Bool.noConfusion (hf.symm.trans hc)
    · intro b
      obtain ⟨a, ha, hu⟩ := hi.backward b
      refine ⟨a, ha, ?_⟩
      intro c hc
      by_contra hca
      have hf := hu c hca
      exact Bool.noConfusion (hf.symm.trans hc)

def agreement (a b : U.Atom) :
    BoolFormula.{max (u + 1) (v + 1), 0} (Query.{u, v} U mode) :=
  .iff (.cell (.pointedAtom .forward a b) true)
    (.cell (.atom .forward a b) true)

structure Instances (h : Table.{u, v} U mode) : Prop where
  pointed : RoleInstances h .pointed
  upper : RoleInstances h .upper
  agree : ∀ a b, (agreement a b).evaluate h

theorem coherent_iff_instances (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Atom.IsCoherent h ↔ Instances h := by
  constructor
  · intro hp
    exact {
      pointed := (lawful_iff_roleInstances h .pointed).mp hp.pointed
      upper := (lawful_iff_roleInstances h .upper).mp hp.upper
      agree := fun a b => Bool.eq_iff_iff.mp (hp.agree a b) }
  · intro hi
    exact {
      pointed := (lawful_iff_roleInstances h .pointed).mpr hi.pointed
      upper := (lawful_iff_roleInstances h .upper).mpr hi.upper
      agree := fun a b => Bool.eq_iff_iff.mpr (hi.agree a b) }

end Atom

/-! ## Directed object rows -/

namespace ObjectRows

def witness (A B : ArchitectureObject U) :
    BoolFormula.{max (u + 1) (v + 1), u + 1} (Query.{u, v} U mode) :=
  .cell (.object A B) true

def other (A challenger : ArchitectureObject U) :
    BoolFormula.{max (u + 1) (v + 1), u + 1} (Query.{u, v} U mode) :=
  .cell (.object A challenger) false

def Instances (h : Table.{u, v} U mode) : Prop :=
  ∀ A, ∃ B, (witness A B).evaluate h ∧ ∀ C, C ≠ B → (other A C).evaluate h

theorem lawful_iff_instances (h : Table.{u, v} U mode) :
    CoreLaws.ObjectRows h ↔ Instances h := by
  constructor
  · intro hp A
    obtain ⟨B, hB, hu⟩ := hp A
    refine ⟨B, hB, ?_⟩
    intro C hCB
    cases hq : h (.object A C) with
    | false => exact hq
    | true => exact (hCB (hu C hq)).elim
  · intro hp A
    obtain ⟨B, hB, hu⟩ := hp A
    refine ⟨B, hB, ?_⟩
    intro C hC
    by_contra hCB
    have hf := hu C hCB
    exact Bool.noConfusion (hf.symm.trans hC)

end ObjectRows

/-! ## Extraction transport -/

namespace Extraction

def sourceQuery (q : IndependentCarrierGraph.Query.{u, u}) : Query.{u, v} U mode :=
  .source q

def sourceAdmitted (s : IndependentCorePrimitive.Extraction.Table U)
    (S : Type u) (x : S) (a : U.Atom) : Formula.{u, v, 0} U mode :=
  .and
    (.source (.extraction (.vocabulary
      (IndependentCorePrimitive.Extraction.carrier s .vocabulary)
      (IndependentCorePrimitive.Extraction.point s .vocabulary) a)) ⟨⟨True⟩⟩)
    (.and
      (.source (.extraction (.semantic
        (IndependentCorePrimitive.Extraction.carrier s .semantic) S
        (IndependentCorePrimitive.Extraction.point s .semantic) x a)) ⟨⟨True⟩⟩)
      (.and
        (.source (.extraction (.resolution
          (IndependentCorePrimitive.Extraction.carrier s .resolution) S
          (IndependentCorePrimitive.Extraction.point s .resolution) x a)) ⟨⟨True⟩⟩)
        (.source (.extraction (.source S x a)) ⟨⟨True⟩⟩)))

def targetAdmitted (t : IndependentCorePrimitive.Extraction.Table U)
    (T : Type u) (y : T) (b : U.Atom) : Formula.{u, v, 0} U mode :=
  .and
    (.target (.extraction (.vocabulary
      (IndependentCorePrimitive.Extraction.carrier t .vocabulary)
      (IndependentCorePrimitive.Extraction.point t .vocabulary) b)) ⟨⟨True⟩⟩)
    (.and
      (.target (.extraction (.semantic
        (IndependentCorePrimitive.Extraction.carrier t .semantic) T
        (IndependentCorePrimitive.Extraction.point t .semantic) y b)) ⟨⟨True⟩⟩)
      (.and
        (.target (.extraction (.resolution
          (IndependentCorePrimitive.Extraction.carrier t .resolution) T
          (IndependentCorePrimitive.Extraction.point t .resolution) y b)) ⟨⟨True⟩⟩)
        (.target (.extraction (.source T y b)) ⟨⟨True⟩⟩)))

def selected (s t : IndependentCorePrimitive.Extraction.Table U) :
    Formula.{u, v, 0} U mode :=
  .hom (.source (.edge
    (IndependentCorePrimitive.Extraction.carrier s .source)
    (IndependentCorePrimitive.Extraction.carrier t .source)
    (IndependentCorePrimitive.Extraction.point s .source)
    (IndependentCorePrimitive.Extraction.point t .source))) true

def normalize (S T : Type u) (x nx : S) (y ny : T) :
    Formula.{u, v, 0} U mode :=
  .implies (.hom (.source (.edge S T x y)) true)
    (.implies (.source (.extraction (.normalize S x)) ⟨⟨some nx⟩⟩)
      (.implies (.target (.extraction (.normalize T y)) ⟨⟨some ny⟩⟩)
        (.hom (.source (.edge S T nx ny)) true)))

def admission (s t : IndependentCorePrimitive.Extraction.Table U)
    (S T : Type u) (x nx : S) (y ny : T) (a b : U.Atom) :
    Formula.{u, v, 0} U mode :=
  .implies (.hom (.source (.edge S T x y)) true)
    (.implies (.hom (.pointedAtom .forward a b) true)
      (.implies (.source (.extraction (.normalize S x)) ⟨⟨some nx⟩⟩)
        (.implies (.target (.extraction (.normalize T y)) ⟨⟨some ny⟩⟩)
          (.iff (sourceAdmitted s S nx a) (targetAdmitted t T ny b)))))

structure Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (s t : IndependentCorePrimitive.Extraction.Table U)
    (h : Table.{u, v} U mode) : Prop where
  source : CarrierRows.Instances h sourceQuery
    (IndependentCorePrimitive.Extraction.carrier s .source)
    (IndependentCorePrimitive.Extraction.carrier t .source)
  selected : (selected (U := U) s t).evaluate sourceTable targetTable h
  normalize : ∀ S T x nx y ny,
    (normalize (U := U) S T x nx y ny).evaluate sourceTable targetTable h
  admission : ∀ S T x nx y ny a b,
    (admission (U := U) s t S T x nx y ny a b).evaluate sourceTable targetTable h

theorem sourceAdmitted_evaluate_iff
    (sourceObject targetObject : ObjectData.{u, v} U)
    (S : Type u) (x : S) (a : U.Atom) (h : Table.{u, v} U mode) :
    (sourceAdmitted sourceObject.1.val.1.1.val.val S x a).evaluate
        (IndependentGeometryPrimitive.flatten sourceObject)
        (IndependentGeometryPrimitive.flatten targetObject) h ↔
      CoreLaws.admitted sourceObject.1.val.1.1.val.val S x a := by
  simp only [sourceAdmitted, Formula.evaluate, IndependentGeometryPrimitive.flatten,
    CoreLaws.admitted]
  exact and_congr (double_ulift_prop_true_iff _)
    (and_congr (double_ulift_prop_true_iff _)
      (and_congr (double_ulift_prop_true_iff _) (double_ulift_prop_true_iff _)))

theorem targetAdmitted_evaluate_iff
    (sourceObject targetObject : ObjectData.{u, v} U)
    (T : Type u) (y : T) (b : U.Atom) (h : Table.{u, v} U mode) :
    (targetAdmitted targetObject.1.val.1.1.val.val T y b).evaluate
        (IndependentGeometryPrimitive.flatten sourceObject)
        (IndependentGeometryPrimitive.flatten targetObject) h ↔
      CoreLaws.admitted targetObject.1.val.1.1.val.val T y b := by
  simp only [targetAdmitted, Formula.evaluate, IndependentGeometryPrimitive.flatten,
    CoreLaws.admitted]
  exact and_congr (double_ulift_prop_true_iff _)
    (and_congr (double_ulift_prop_true_iff _)
      (and_congr (double_ulift_prop_true_iff _) (double_ulift_prop_true_iff _)))

theorem extractionLaws_iff_instances
    (sourceObject targetObject : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    CoreLaws.ExtractionLaws sourceObject.1.val.1.1.val.val
        targetObject.1.val.1.1.val.val h ↔
      Instances (IndependentGeometryPrimitive.flatten sourceObject)
        (IndependentGeometryPrimitive.flatten targetObject)
        sourceObject.1.val.1.1.val.val targetObject.1.val.1.1.val.val h := by
  constructor
  · intro hp
    refine {
      source := (CarrierRows.lawful_iff_instances h sourceQuery _ _).mp (by
        simpa [sourceQuery] using hp.source)
      selected := hp.selected
      normalize := ?_
      admission := ?_ }
    · intro S T x nx y ny
      simp only [normalize, Formula.evaluate, IndependentGeometryPrimitive.flatten]
      intro hxy hs ht
      exact hp.normalize S T x nx y ny hxy
        ((double_ulift_eq_iff _ _).mp hs) ((double_ulift_eq_iff _ _).mp ht)
    · intro S T x nx y ny a b
      simp only [admission, Formula.evaluate, IndependentGeometryPrimitive.flatten]
      intro hxy hab hs ht
      rw [sourceAdmitted_evaluate_iff sourceObject targetObject,
        targetAdmitted_evaluate_iff sourceObject targetObject]
      exact hp.extraction S T x nx y ny a b hxy hab
        ((double_ulift_eq_iff _ _).mp hs) ((double_ulift_eq_iff _ _).mp ht)
  · intro hi
    refine {
      source := by
        simpa [sourceQuery] using
          (CarrierRows.lawful_iff_instances h sourceQuery _ _).mpr hi.source
      selected := hi.selected
      normalize := ?_
      extraction := ?_ }
    · intro S T x nx y ny
      have hf := hi.normalize S T x nx y ny
      simp only [normalize, Formula.evaluate, IndependentGeometryPrimitive.flatten] at hf
      intro hxy hs ht
      exact hf hxy ((double_ulift_eq_iff _ _).mpr hs)
        ((double_ulift_eq_iff _ _).mpr ht)
    · intro S T x nx y ny a b hxy hab hs ht
      have hf := hi.admission S T x nx y ny a b
      simp only [admission, Formula.evaluate, IndependentGeometryPrimitive.flatten] at hf
      rw [sourceAdmitted_evaluate_iff sourceObject targetObject,
        targetAdmitted_evaluate_iff sourceObject targetObject] at hf
      exact hf hxy hab ((double_ulift_eq_iff _ _).mpr hs)
        ((double_ulift_eq_iff _ _).mpr ht)

end Extraction

/-! ## Family and configuration matching -/

namespace TransportMatch

def familyFlag (F F' : AtomFamily U) (value : Bool) : Formula.{u, v, 0} U mode :=
  .hom (.familyTransport F F') value

def configurationFlag (C C' : AtomConfiguration U) (value : Bool) :
    Formula.{u, v, 0} U mode :=
  .hom (.configurationTransport C C') value

def atomPair (a b : U.Atom) : Formula.{u, v, 0} U mode :=
  .hom (.atom .forward a b) true

def Membership (F F' : AtomFamily U) (a b : U.Atom) : Prop :=
  F.mem a ↔ F'.mem b

def MembershipMismatch (F F' : AtomFamily U) (a b : U.Atom) : Prop :=
  ¬ Membership F F' a b

def ConfigurationPoint (C C' : AtomConfiguration U)
    (a a' b b' : U.Atom) : Prop :=
  (C.relation a b ↔ C'.relation a' b') ∧
    (C.identification a b ↔ C'.identification a' b')

def ConfigurationPointMismatch (C C' : AtomConfiguration U)
    (a a' b b' : U.Atom) : Prop :=
  ¬ ConfigurationPoint C C' a a' b b'

structure Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop where
  family_yes : ∀ F F', (familyFlag F F' true).evaluate sourceTable targetTable h →
    ∀ a b, (atomPair a b).evaluate sourceTable targetTable h →
      Membership F F' a b
  family_no : ∀ F F', (familyFlag F F' false).evaluate sourceTable targetTable h →
    ∃ a b, (atomPair a b).evaluate sourceTable targetTable h ∧
      MembershipMismatch F F' a b
  configuration_yes : ∀ C C',
    (configurationFlag C C' true).evaluate sourceTable targetTable h →
      (familyFlag C.family C'.family true).evaluate sourceTable targetTable h ∧
        ∀ a a' b b', (atomPair a a').evaluate sourceTable targetTable h →
          (atomPair b b').evaluate sourceTable targetTable h →
            ConfigurationPoint C C' a a' b b'
  configuration_no : ∀ C C',
    (configurationFlag C C' false).evaluate sourceTable targetTable h →
      (familyFlag C.family C'.family false).evaluate sourceTable targetTable h ∨
        ∃ a a' b b', (atomPair a a').evaluate sourceTable targetTable h ∧
          (atomPair b b').evaluate sourceTable targetTable h ∧
            ConfigurationPointMismatch C C' a a' b b'

theorem lawful_iff_instances
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.TransportMatch.IsLawful h ↔
      Instances sourceTable targetTable h := by
  constructor
  · intro hp
    refine {
      family_yes := ?_
      family_no := ?_
      configuration_yes := ?_
      configuration_no := ?_ }
    · intro F F' hf a b hab
      exact hp.family_yes F F' hf a b hab
    · intro F F' hf
      obtain ⟨a, b, hab, hm⟩ := hp.family_no F F' hf
      exact ⟨a, b, hab, hm⟩
    · intro C C' hc
      obtain ⟨hf, hp⟩ := hp.configuration_yes C C' hc
      refine ⟨hf, ?_⟩
      intro a a' b b' haa hbb
      obtain ⟨hr, hi⟩ := hp a a' b b' haa hbb
      exact ⟨hr, hi⟩
    · intro C C' hc
      rcases hp.configuration_no C C' hc with hf | ⟨a, a', b, b', haa, hbb, hm⟩
      · exact Or.inl hf
      · exact Or.inr ⟨a, a', b, b', haa, hbb,
          hm⟩
  · intro hi
    refine {
      family_yes := ?_
      family_no := ?_
      configuration_yes := ?_
      configuration_no := ?_ }
    · intro F F' hf a b hab
      exact hi.family_yes F F' hf a b hab
    · intro F F' hf
      obtain ⟨a, b, hab, hm⟩ := hi.family_no F F' hf
      exact ⟨a, b, hab, hm⟩
    · intro C C' hc
      obtain ⟨hf, hp⟩ := hi.configuration_yes C C' hc
      refine ⟨hf, ?_⟩
      intro a a' b b' haa hbb
      obtain ⟨hr, hi⟩ := hp a a' b b' haa hbb
      exact ⟨hr, hi⟩
    · intro C C' hc
      rcases hi.configuration_no C C' hc with hf | ⟨a, a', b, b', haa, hbb, hm⟩
      · exact Or.inl hf
      · exact Or.inr ⟨a, a', b, b', haa, hbb,
          hm⟩

end TransportMatch

/-! ## Composition, formation, and configuration generation -/

namespace Generation

def compositionPoint (F F' : AtomFamily U)
    (hf : F.ListFinite) (hf' : F'.ListFinite)
    (a a' b b' : U.Atom) : Formula.{u, v, 0} U mode :=
  .implies (.hom (.familyTransport F F') true)
    (.implies (.hom (.atom .forward a a') true)
      (.implies (.hom (.atom .forward b b') true)
        (.and
          (.iff
            (.source (.composition (.relation F hf a b)) (ULift.up True))
            (.target (.composition (.relation F' hf' a' b')) (ULift.up True)))
          (.iff
            (.source (.composition (.identification F hf a b)) (ULift.up True))
            (.target (.composition (.identification F' hf' a' b')) (ULift.up True))))))

def sourceFormationMatch (C : AtomConfiguration U) (A : ArchitectureObject U) :
    Formula.{u, v, u} U mode :=
  .and
    (.source (.formation (.structureMaps C))
      (ULift.up (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u})))
    (.source (.formation (.selectedQuantities C))
      (ULift.up (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u})))

def targetFormationMatch (C : AtomConfiguration U) (A : ArchitectureObject U) :
    Formula.{u, v, u} U mode :=
  .and
    (.target (.formation (.structureMaps C))
      (ULift.up (⟨A.StructureMaps, A.structureMaps⟩ : SelectedValue.{u})))
    (.target (.formation (.selectedQuantities C))
      (ULift.up (⟨A.SelectedQuantities, A.selectedQuantities⟩ : SelectedValue.{u})))

def formationPoint (C C' : AtomConfiguration U) (A B : ArchitectureObject U) :
    Formula.{u, v, u} U mode :=
  .implies (.hom (.configurationTransport C C') true)
    (.implies (sourceFormationMatch C A)
      (.implies (targetFormationMatch C' B) (.hom (.object A B) true)))

def configurationPoint (A B : ArchitectureObject U) : Formula.{u, v, 0} U mode :=
  .implies (.hom (.object A B) true)
    (.hom (.configurationTransport A.configuration B.configuration) true)

structure Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop where
  composition : ∀ F F' (hf : F.ListFinite) (hf' : F'.ListFinite) a a' b b',
    (compositionPoint F F' hf hf' a a' b b').evaluate sourceTable targetTable h
  formation : ∀ C C' A B, A.configuration = C → B.configuration = C' →
    (formationPoint C C' A B).evaluate sourceTable targetTable h
  configuration : ∀ A B,
    (configurationPoint A B).evaluate sourceTable targetTable h

theorem sourceFormationMatch_evaluate_iff
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hC : A.configuration = C) :
    (sourceFormationMatch C A).evaluate sourceTable targetTable h ↔
      CoreLaws.FormationMatch (IndependentGeometryPrimitive.formation sourceTable) C A := by
  simp only [sourceFormationMatch, Formula.evaluate, CoreLaws.FormationMatch,
    IndependentGeometryPrimitive.formation]
  constructor
  · rintro ⟨hs, hq⟩
    exact ⟨hC, ((ulift_eq_iff _ _).mp hs).symm, ((ulift_eq_iff _ _).mp hq).symm⟩
  · rintro ⟨_, hs, hq⟩
    exact ⟨(ulift_eq_iff _ _).mpr hs.symm, (ulift_eq_iff _ _).mpr hq.symm⟩

theorem targetFormationMatch_evaluate_iff
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (C : AtomConfiguration U) (A : ArchitectureObject U)
    (hC : A.configuration = C) :
    (targetFormationMatch C A).evaluate sourceTable targetTable h ↔
      CoreLaws.FormationMatch (IndependentGeometryPrimitive.formation targetTable) C A := by
  simp only [targetFormationMatch, Formula.evaluate, CoreLaws.FormationMatch,
    IndependentGeometryPrimitive.formation]
  constructor
  · rintro ⟨hs, hq⟩
    exact ⟨hC, ((ulift_eq_iff _ _).mp hs).symm, ((ulift_eq_iff _ _).mp hq).symm⟩
  · rintro ⟨_, hs, hq⟩
    exact ⟨(ulift_eq_iff _ _).mpr hs.symm, (ulift_eq_iff _ _).mpr hq.symm⟩

theorem generationLaws_iff_instances
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    CoreLaws.GenerationLaws (IndependentGeometryPrimitive.composition sourceTable)
        (IndependentGeometryPrimitive.composition targetTable)
        (IndependentGeometryPrimitive.formation sourceTable)
        (IndependentGeometryPrimitive.formation targetTable) h ↔
      Instances sourceTable targetTable h := by
  constructor
  · intro hp
    refine {
      composition := ?_
      formation := ?_
      configuration := ?_ }
    · intro F F' hf hf' a a' b b'
      simp only [compositionPoint, Formula.evaluate]
      intro hF ha hb
      obtain ⟨hr, hi⟩ := hp.composition F F' hf hf' a a' b b' hF ha hb
      exact ⟨(ulift_prop_true_iff _).trans (hr.trans (ulift_prop_true_iff _).symm),
        (ulift_prop_true_iff _).trans (hi.trans (ulift_prop_true_iff _).symm)⟩
    · intro C C' A B hAC hBC
      simp only [formationPoint, Formula.evaluate]
      intro hC hA hB
      exact hp.formation C C' A B hC
        ((sourceFormationMatch_evaluate_iff sourceTable targetTable h C A hAC).mp hA)
        ((targetFormationMatch_evaluate_iff sourceTable targetTable h C' B hBC).mp hB)
    · intro A B
      exact hp.configuration A B
  · intro hi
    refine {
      composition := ?_
      formation := ?_
      configuration := ?_ }
    · intro F F' hf hf' a a' b b' hF ha hb
      have hp := hi.composition F F' hf hf' a a' b b'
      simp only [compositionPoint, Formula.evaluate] at hp
      obtain ⟨hr, hi⟩ := hp hF ha hb
      exact ⟨(ulift_prop_true_iff _).symm.trans (hr.trans (ulift_prop_true_iff _)),
        (ulift_prop_true_iff _).symm.trans (hi.trans (ulift_prop_true_iff _))⟩
    · intro C C' A B hC hA hB
      have hp := hi.formation C C' A B hA.1 hB.1
      simp only [formationPoint, Formula.evaluate] at hp
      exact hp hC
        ((sourceFormationMatch_evaluate_iff sourceTable targetTable h C A hA.1).mpr hA)
        ((targetFormationMatch_evaluate_iff sourceTable targetTable h C' B hB.1).mpr hB)
    · intro A B
      exact hi.configuration A B

end Generation

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.CoreLawFinite
