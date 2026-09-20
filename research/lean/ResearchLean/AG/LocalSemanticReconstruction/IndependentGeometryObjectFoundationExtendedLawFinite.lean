import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectFoundationLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for the remaining object foundation laws

This file continues the object-side audit with the finite extracted family,
invariant and signature typing, operation maps, and coefficient-ring laws.
Every value derived from a table-selected carrier is accompanied by the cell
that selects that carrier.  Formula leaves contain only primitive cells and
equalities.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite

noncomputable section

universe u v w

open IndependentCorePrimitive IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

namespace Finite

abbrev normalized (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) :
    Extraction.carrier (IndependentGeometryPrimitive.extraction t) .source :=
  IndependentGeneratedObjectMatching.normalized (IndependentGeometryPrimitive.extraction t) ht

def member (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) (a : U.Atom) :
    ObjectFormula.{u, v, u + 1} U :=
  extractionAnchors t
    (.and
      (.cell (.extraction (.normalize _
          (Extraction.point (IndependentGeometryPrimitive.extraction t) .source)))
        (ULift.up (ULift.up (some (normalized t ht)))))
      (.and
        (.cell (.extraction (.vocabulary _
            (Extraction.point (IndependentGeometryPrimitive.extraction t) .vocabulary) a))
          (ULift.up (ULift.up True)))
        (.and
          (.cell (.extraction (.semantic _ _
              (Extraction.point (IndependentGeometryPrimitive.extraction t) .semantic)
              (normalized t ht) a))
            (ULift.up (ULift.up True)))
          (.and
            (.cell (.extraction (.resolution _ _
                (Extraction.point (IndependentGeometryPrimitive.extraction t) .resolution)
                (normalized t ht) a))
              (ULift.up (ULift.up True)))
            (.cell (.extraction (.source _ (normalized t ht) a))
              (ULift.up (ULift.up True)))))))

theorem member_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) (a : U.Atom) :
    (member t ht a).evaluate t ↔
      (Generation.family (IndependentGeometryPrimitive.extraction t) ht).mem a := by
  apply Iff.trans ?_ (IndependentGeneratedObjectMatching.extracted_iff_family
    (IndependentGeometryPrimitive.extraction t) ht a)
  simp only [member, extractionAnchors_evaluate, ObjectFormula.evaluate,
    normalized, IndependentGeneratedObjectMatching.extracted]
  have hn :
      ((IndependentGeometryPrimitive.extraction t) (.normalize _
        (Extraction.point (IndependentGeometryPrimitive.extraction t) .source))).down =
        some (IndependentGeneratedObjectMatching.normalized
          (IndependentGeometryPrimitive.extraction t) ht) :=
    (Option.some_get _).symm
  simp only [IndependentGeometryPrimitive.extraction] at hn
  constructor
  · rintro ⟨hnormalize, hv, hm, hr, hs⟩
    exact ⟨
      (prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hv)),
      (prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hm)),
      (prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hr)),
      (prop_eq_true_iff _).mp
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hs))⟩
  · rintro ⟨hv, hm, hr, hs⟩
    refine ⟨?_,
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((prop_eq_true_iff _).mpr hv)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((prop_eq_true_iff _).mpr hm)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((prop_eq_true_iff _).mpr hr)),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr
          ((prop_eq_true_iff _).mpr hs))⟩
    apply ULift.ext
    apply ULift.ext
    exact hn

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) : Prop where
  finite : ∃ atoms : List U.Atom, ∀ a, (member t ht a).evaluate t → a ∈ atoms

theorem listFinite_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : Extraction.IsTyped (IndependentGeometryPrimitive.extraction t)) :
    (Generation.family (IndependentGeometryPrimitive.extraction t) ht).ListFinite ↔
      Instances t ht := by
  constructor
  · rintro ⟨atoms, hmem⟩
    exact ⟨atoms, fun a ha => hmem a ((member_evaluate_iff t ht a).mp ha)⟩
  · rintro ⟨atoms, hmem⟩
    exact ⟨atoms, fun a ha => hmem a ((member_evaluate_iff t ht a).mpr ha)⟩

end Finite

namespace Invariants

def indexAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) : ObjectFormula.{u, v, u + 1} U :=
  .and (.cell (.invariant .index) (t (.invariant .index))) body

def kindAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (body : ObjectFormula.{u, v, u + 1} U) :
    ObjectFormula.{u, v, u + 1} U :=
  indexAnchor t (.and (.cell (.invariant (.kind I i)) (t (.invariant (.kind I i)))) body)

@[simp] theorem indexAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) :
    (indexAnchor t body).evaluate t ↔ body.evaluate t := by
  simp [indexAnchor, ObjectFormula.evaluate]

@[simp] theorem kindAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U) (I : Type u) (i : I)
    (body : ObjectFormula.{u, v, u + 1} U) :
    (kindAnchor t I i body).evaluate t ↔ body.evaluate t := by
  simp [kindAnchor, ObjectFormula.evaluate]

def kindSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (k : IndependentInvariantSignaturePrimitive.Invariants.Kind.{u}) :
    ObjectFormula.{u, v, u + 1} U :=
  indexAnchor t (.cell (.invariant (.kind I i)) (ULift.up (some k)))

def kindNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) : ObjectFormula.{u, v, u + 1} U :=
  indexAnchor t (.cell (.invariant (.kind I i)) (ULift.up none))

def valueSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U) (y : K) :
    ObjectFormula.{u, v, u + 1} U :=
  kindAnchor t I i
    (.cell (.invariant (.value I i K B)) (ULift.up (ULift.up (some y))))

def valueNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U) :
    ObjectFormula.{u, v, u + 1} U :=
  kindAnchor t I i
    (.cell (.invariant (.value I i K B)) (ULift.up (ULift.up none)))

def predicateFalse (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (B : ArchitectureObject U) :
    ObjectFormula.{u, v, u + 1} U :=
  kindAnchor t I i
    (.cell (.invariant (.predicate I i B)) (ULift.up (ULift.up False)))

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  kindSome : ∀ I i,
    I = IndependentInvariantSignaturePrimitive.Invariants.index
      (IndependentGeometryPrimitive.invariant t) →
      ∃ k, (kindSome t I i k).evaluate t
  kindNone : ∀ I i,
    I ≠ IndependentInvariantSignaturePrimitive.Invariants.index
      (IndependentGeometryPrimitive.invariant t) →
      (kindNone t I i).evaluate t
  valueSome : ∀ I i K B,
    (IndependentGeometryPrimitive.invariant t) (.kind I i) =
        some (.function K) →
      ∃ y, (valueSome t I i K B y).evaluate t
  valueNone : ∀ I i K B,
    (IndependentGeometryPrimitive.invariant t) (.kind I i) ≠
        some (.function K) →
      (valueNone t I i K B).evaluate t
  predicate : ∀ I i B,
    (IndependentGeometryPrimitive.invariant t) (.kind I i) ≠ some .predicate →
      (predicateFalse t I i B).evaluate t

theorem typed_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentInvariantSignaturePrimitive.Invariants.IsTyped
        (IndependentGeometryPrimitive.invariant t) ↔ Instances t := by
  constructor
  · intro ht
    refine {
      kindSome := ?_
      kindNone := ?_
      valueSome := ?_
      valueNone := ?_
      predicate := ?_ }
    · intro I i hI
      have hs := (ht.kind I i).2 hI
      cases hk : (IndependentGeometryPrimitive.invariant t) (.kind I i) with
      | none => simp [hk] at hs
      | some k =>
          refine ⟨k, ?_⟩
          simp only [kindSome, indexAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          exact hk
    · intro I i hI
      have hn := IndependentInvariantSignaturePrimitive.option_none _ (mt (ht.kind I i).1 hI)
      simp only [kindNone, indexAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      exact hn
    · intro I i K B hk
      have hs := (ht.value I i K B).2 hk
      cases hv : ((IndependentGeometryPrimitive.invariant t) (.value I i K B)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [valueSome, kindAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          apply ULift.ext
          exact hv
    · intro I i K B hk
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.value I i K B).1 hk)
      simp only [valueNone, kindAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact hn
    · intro I i B hk
      simp only [predicateFalse, kindAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (ht.predicate I i B hk))
  · intro hi
    refine {
      kind := ?_
      value := ?_
      predicate := ?_ }
    · intro I i
      constructor
      · intro hs
        by_contra hI
        have hn := hi.kindNone I i hI
        simp only [kindNone, indexAnchor_evaluate, ObjectFormula.evaluate] at hn
        have he := congrArg ULift.down hn
        change (IndependentGeometryPrimitive.invariant t) (.kind I i) = none at he
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hI
        obtain ⟨k, hk⟩ := hi.kindSome I i hI
        simp only [kindSome, indexAnchor_evaluate, ObjectFormula.evaluate] at hk
        have he := congrArg ULift.down hk
        change (IndependentGeometryPrimitive.invariant t) (.kind I i) = some k at he
        rw [he]
        rfl
    · intro I i K B
      constructor
      · intro hs
        by_contra hk
        have hn := hi.valueNone I i K B hk
        simp only [valueNone, kindAnchor_evaluate, ObjectFormula.evaluate] at hn
        have he := congrArg (fun value => value.down.down) hn
        change ((IndependentGeometryPrimitive.invariant t) (.value I i K B)).down = none at he
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hk
        obtain ⟨y, hy⟩ := hi.valueSome I i K B hk
        simp only [valueSome, kindAnchor_evaluate, ObjectFormula.evaluate] at hy
        have he := congrArg (fun value => value.down.down) hy
        change ((IndependentGeometryPrimitive.invariant t) (.value I i K B)).down = some y at he
        rw [he]
        rfl
    · intro I i B hk
      have hp := hi.predicate I i B hk
      simp only [predicateFalse, kindAnchor_evaluate, ObjectFormula.evaluate] at hp
      intro htrue
      have he := congrArg (fun value => value.down.down) hp
      change ((IndependentGeometryPrimitive.invariant t) (.predicate I i B)).down = False at he
      rw [he] at htrue
      exact htrue

end Invariants

namespace Signature

def axisAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) : ObjectFormula.{u, v, u + 1} U :=
  .and (.cell (.signature .axis) (t (.signature .axis))) body

def coordinateTypeAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (body : ObjectFormula.{u, v, u + 1} U) :
    ObjectFormula.{u, v, u + 1} U :=
  axisAnchor t
    (.and (.cell (.signature (.coordinateType I i))
      (t (.signature (.coordinateType I i)))) body)

@[simp] theorem axisAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, u + 1} U) :
    (axisAnchor t body).evaluate t ↔ body.evaluate t := by
  simp [axisAnchor, ObjectFormula.evaluate]

@[simp] theorem coordinateTypeAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U) (I : Type u) (i : I)
    (body : ObjectFormula.{u, v, u + 1} U) :
    (coordinateTypeAnchor t I i body).evaluate t ↔ body.evaluate t := by
  simp [coordinateTypeAnchor, ObjectFormula.evaluate]

def coordinateTypeSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (K : Type u) : ObjectFormula.{u, v, u + 1} U :=
  axisAnchor t (.cell (.signature (.coordinateType I i)) (ULift.up (some K)))

def coordinateTypeNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) : ObjectFormula.{u, v, u + 1} U :=
  axisAnchor t (.cell (.signature (.coordinateType I i)) (ULift.up none))

def selectedFalse (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) : ObjectFormula.{u, v, u + 1} U :=
  axisAnchor t (.cell (.signature (.selected I i)) (ULift.up (ULift.up False)))

def coordinateSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U) (y : K) :
    ObjectFormula.{u, v, u + 1} U :=
  coordinateTypeAnchor t I i
    (.cell (.signature (.coordinate I i K B)) (ULift.up (ULift.up (some y))))

def coordinateNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (I : Type u) (i : I) (K : Type u) (B : ArchitectureObject U) :
    ObjectFormula.{u, v, u + 1} U :=
  coordinateTypeAnchor t I i
    (.cell (.signature (.coordinate I i K B)) (ULift.up (ULift.up none)))

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  coordinateTypeSome : ∀ I i,
    I = IndependentInvariantSignaturePrimitive.Signature.axis
      (IndependentGeometryPrimitive.signature t) →
      ∃ K, (coordinateTypeSome t I i K).evaluate t
  coordinateTypeNone : ∀ I i,
    I ≠ IndependentInvariantSignaturePrimitive.Signature.axis
      (IndependentGeometryPrimitive.signature t) →
      (coordinateTypeNone t I i).evaluate t
  selected : ∀ I i,
    I ≠ IndependentInvariantSignaturePrimitive.Signature.axis
      (IndependentGeometryPrimitive.signature t) →
      (selectedFalse t I i).evaluate t
  coordinateSome : ∀ I i K B,
    (IndependentGeometryPrimitive.signature t) (.coordinateType I i) = some K →
      ∃ y, (coordinateSome t I i K B y).evaluate t
  coordinateNone : ∀ I i K B,
    (IndependentGeometryPrimitive.signature t) (.coordinateType I i) ≠ some K →
      (coordinateNone t I i K B).evaluate t

theorem typed_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentInvariantSignaturePrimitive.Signature.IsTyped
        (IndependentGeometryPrimitive.signature t) ↔ Instances t := by
  constructor
  · intro ht
    refine {
      coordinateTypeSome := ?_
      coordinateTypeNone := ?_
      selected := ?_
      coordinateSome := ?_
      coordinateNone := ?_ }
    · intro I i hI
      have hs := (ht.coordinateType I i).2 hI
      cases hc : (IndependentGeometryPrimitive.signature t) (.coordinateType I i) with
      | none => simp [hc] at hs
      | some K =>
          refine ⟨K, ?_⟩
          simp only [coordinateTypeSome, axisAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          exact hc
    · intro I i hI
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.coordinateType I i).1 hI)
      simp only [coordinateTypeNone, axisAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      exact hn
    · intro I i hI
      simp only [selectedFalse, axisAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact propext (iff_false_intro (ht.selected I i hI))
    · intro I i K B hK
      have hs := (ht.coordinate I i K B).2 hK
      cases hc : ((IndependentGeometryPrimitive.signature t) (.coordinate I i K B)).down with
      | none => simp [hc] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [coordinateSome, coordinateTypeAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          apply ULift.ext
          exact hc
    · intro I i K B hK
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.coordinate I i K B).1 hK)
      simp only [coordinateNone, coordinateTypeAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact hn
  · intro hi
    refine {
      coordinateType := ?_
      selected := ?_
      coordinate := ?_ }
    · intro I i
      constructor
      · intro hs
        by_contra hI
        have hn := hi.coordinateTypeNone I i hI
        simp only [coordinateTypeNone, axisAnchor_evaluate, ObjectFormula.evaluate] at hn
        have he := congrArg ULift.down hn
        change (IndependentGeometryPrimitive.signature t) (.coordinateType I i) = none at he
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hI
        obtain ⟨K, hK⟩ := hi.coordinateTypeSome I i hI
        simp only [coordinateTypeSome, axisAnchor_evaluate, ObjectFormula.evaluate] at hK
        have he := congrArg ULift.down hK
        change (IndependentGeometryPrimitive.signature t) (.coordinateType I i) = some K at he
        rw [he]
        rfl
    · intro I i hI
      have hs := hi.selected I i hI
      simp only [selectedFalse, axisAnchor_evaluate, ObjectFormula.evaluate] at hs
      intro htrue
      have he := congrArg (fun value => value.down.down) hs
      change ((IndependentGeometryPrimitive.signature t) (.selected I i)).down = False at he
      rw [he] at htrue
      exact htrue
    · intro I i K B
      constructor
      · intro hs
        by_contra hK
        have hn := hi.coordinateNone I i K B hK
        simp only [coordinateNone, coordinateTypeAnchor_evaluate, ObjectFormula.evaluate] at hn
        have he := congrArg (fun value => value.down.down) hn
        change ((IndependentGeometryPrimitive.signature t) (.coordinate I i K B)).down = none at he
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hK
        obtain ⟨y, hy⟩ := hi.coordinateSome I i K B hK
        simp only [coordinateSome, coordinateTypeAnchor_evaluate, ObjectFormula.evaluate] at hy
        have he := congrArg (fun value => value.down.down) hy
        change ((IndependentGeometryPrimitive.signature t) (.coordinate I i K B)).down = some y at he
        rw [he]
        rfl

end Signature

namespace Operations

def carrierAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A B : ArchitectureObject U) (body : ObjectFormula.{u, v, w} U) :
    ObjectFormula.{u, v, w} U :=
  .and (.cell (.operation (.carrier A B)) (t (.operation (.carrier A B)))) body

def actionAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a : U.Atom)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  carrierAnchor t A B
    (.and (.cell (.operation (.action A B _ op a))
      (t (.operation (.action A B _ op a)))) body)

@[simp] theorem carrierAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U) (A B : ArchitectureObject U)
    (body : ObjectFormula.{u, v, w} U) :
    (carrierAnchor t A B body).evaluate t ↔ body.evaluate t := by
  simp [carrierAnchor, ObjectFormula.evaluate]

@[simp] theorem actionAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U) (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a : U.Atom)
    (body : ObjectFormula.{u, v, w} U) :
    (actionAnchor t A B op a body).evaluate t ↔ body.evaluate t := by
  simp [actionAnchor, ObjectFormula.evaluate]

def actionSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A B : ArchitectureObject U) (T : Type u) (op : T) (a y : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  carrierAnchor t A B
    (.cell (.operation (.action A B T op a)) (ULift.up (ULift.up (some y))))

def actionNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (A B : ArchitectureObject U) (T : Type u) (op : T) (a : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  carrierAnchor t A B
    (.cell (.operation (.action A B T op a)) (ULift.up (ULift.up none)))

structure TypedInstances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  actionSome : ∀ A B T op a,
    T = IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B →
      ∃ y, (actionSome t A B T op a y).evaluate t
  actionNone : ∀ A B T op a,
    T ≠ IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B →
      (actionNone t A B T op a).evaluate t

theorem typed_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentCorePrimitive.Operations.IsTyped
        (IndependentGeometryPrimitive.operation t) ↔ TypedInstances t := by
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · intro A B T op a hT
      have hs := (ht A B T op a).2 hT
      cases ha : ((IndependentGeometryPrimitive.operation t) (.action A B T op a)).down with
      | none => simp [ha] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [actionSome, carrierAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          apply ULift.ext
          exact ha
    · intro A B T op a hT
      have hn := IndependentInvariantSignaturePrimitive.option_none _ (mt (ht A B T op a).1 hT)
      simp only [actionNone, carrierAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact hn
  · intro hi A B T op a
    constructor
    · intro hs
      by_contra hT
      have hn := hi.actionNone A B T op a hT
      simp only [actionNone, carrierAnchor_evaluate, ObjectFormula.evaluate] at hn
      have he := congrArg (fun value => value.down.down) hn
      change ((IndependentGeometryPrimitive.operation t) (.action A B T op a)).down = none at he
      rw [he] at hs
      exact Bool.noConfusion hs
    · intro hT
      obtain ⟨y, hy⟩ := hi.actionSome A B T op a hT
      simp only [actionSome, carrierAnchor_evaluate, ObjectFormula.evaluate] at hy
      have he := congrArg (fun value => value.down.down) hy
      change ((IndependentGeometryPrimitive.operation t) (.action A B T op a)).down = some y at he
      rw [he]
      rfl

@[simp] theorem actionSome_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t))
    (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a y : U.Atom) :
    (actionSome t A B _ op a y).evaluate t ↔
      IndependentCorePrimitive.Operations.action
        (IndependentGeometryPrimitive.operation t) ht op a = y := by
  simp only [actionSome, carrierAnchor_evaluate, ObjectFormula.evaluate]
  constructor
  · intro h
    have he := congrArg (fun value => value.down.down) h
    exact Option.some.inj ((Option.some_get _).trans he)
  · intro h
    apply ULift.ext
    apply ULift.ext
    exact (Option.some_get _).symm.trans (congrArg some h)

def familyLaw (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (_ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t))
    (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a y : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  actionSome t A B _ op a y

def relationLaw (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (_ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t))
    (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a b x y : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .and (actionSome t A B _ op a x) (actionSome t A B _ op b y)

def identificationLaw (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (_ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t))
    (A B : ArchitectureObject U)
    (op : IndependentCorePrimitive.Operations.carrier
      (IndependentGeometryPrimitive.operation t) A B) (a b x y : U.Atom) :
    ObjectFormula.{u, v, 0} U :=
  .and (actionSome t A B _ op a x) (actionSome t A B _ op b y)

structure LawInstances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t)) : Prop where
  family : ∀ A B op a, A.configuration.family.mem a →
    ∃ y, (familyLaw t ht A B op a y).evaluate t ∧ B.configuration.family.mem y
  relation : ∀ A B op a b, A.configuration.relation a b →
    ∃ x y, (relationLaw t ht A B op a b x y).evaluate t ∧ B.configuration.relation x y
  identification : ∀ A B op a b, A.configuration.identification a b →
    ∃ x y, (identificationLaw t ht A B op a b x y).evaluate t ∧
      B.configuration.identification x y

theorem lawful_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentCorePrimitive.Operations.IsTyped
      (IndependentGeometryPrimitive.operation t)) :
    IndependentCorePrimitive.Operations.IsLawful
        (IndependentGeometryPrimitive.operation t) ht ↔ LawInstances t ht := by
  constructor
  · intro hl
    refine {
      family := ?_
      relation := ?_
      identification := ?_ }
    · intro A B op a ha
      refine ⟨IndependentCorePrimitive.Operations.action
        (IndependentGeometryPrimitive.operation t) ht op a, ?_, hl.family A B op a ha⟩
      exact (actionSome_evaluate_iff t ht A B op a _).2 rfl
    · intro A B op a b hab
      refine ⟨IndependentCorePrimitive.Operations.action
          (IndependentGeometryPrimitive.operation t) ht op a,
        IndependentCorePrimitive.Operations.action
          (IndependentGeometryPrimitive.operation t) ht op b, ?_,
        hl.relation A B op a b hab⟩
      exact ⟨(actionSome_evaluate_iff t ht A B op a _).2 rfl,
        (actionSome_evaluate_iff t ht A B op b _).2 rfl⟩
    · intro A B op a b hab
      refine ⟨IndependentCorePrimitive.Operations.action
          (IndependentGeometryPrimitive.operation t) ht op a,
        IndependentCorePrimitive.Operations.action
          (IndependentGeometryPrimitive.operation t) ht op b, ?_,
        hl.identification A B op a b hab⟩
      exact ⟨(actionSome_evaluate_iff t ht A B op a _).2 rfl,
        (actionSome_evaluate_iff t ht A B op b _).2 rfl⟩
  · intro hi
    exact {
      family := fun A B op a ha => by
        obtain ⟨y, hy, hm⟩ := hi.family A B op a ha
        have he := (actionSome_evaluate_iff t ht A B op a y).1 hy
        simpa [he] using hm
      relation := fun A B op a b hab => by
        obtain ⟨x, y, hxy, hr⟩ := hi.relation A B op a b hab
        have hx := (actionSome_evaluate_iff t ht A B op a x).1 hxy.1
        have hy := (actionSome_evaluate_iff t ht A B op b y).1 hxy.2
        rw [hx, hy]
        exact hr
      identification := fun A B op a b hab => by
        obtain ⟨x, y, hxy, hi'⟩ := hi.identification A B op a b hab
        have hx := (actionSome_evaluate_iff t ht A B op a x).1 hxy.1
        have hy := (actionSome_evaluate_iff t ht A B op b y).1 hxy.2
        rw [hx, hy]
        exact hi' }

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  typed : TypedInstances t
  lawful : LawInstances t ((typed_iff_instances t).mpr typed)

theorem typedLawful_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    (∃ ht : IndependentCorePrimitive.Operations.IsTyped
        (IndependentGeometryPrimitive.operation t),
      IndependentCorePrimitive.Operations.IsLawful
        (IndependentGeometryPrimitive.operation t) ht) ↔ Instances t := by
  constructor
  · rintro ⟨ht, hl⟩
    let hi := (typed_iff_instances t).mp ht
    refine ⟨hi, ?_⟩
    exact (lawful_iff_instances t ((typed_iff_instances t).mpr hi)).mp
      (by simpa only [Subsingleton.elim ht ((typed_iff_instances t).mpr hi)] using hl)
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t).mpr ht, (lawful_iff_instances t _).mpr hl⟩

end Operations

namespace Coefficient

def carrierAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.coefficient .carrier) (t (.coefficient .carrier))) body

@[simp] theorem carrierAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (body : ObjectFormula.{u, v, w} U) :
    (carrierAnchor t body).evaluate t ↔ body.evaluate t := by
  simp [carrierAnchor, ObjectFormula.evaluate]

def operationSome (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (K : Type v) (q : IndependentRingPrimitive.Query K) (y : K) :
    ObjectFormula.{u, v, 0} U :=
  carrierAnchor t
    (.cell (.coefficient (.operation K q)) (ULift.up (ULift.up (some y))))

def operationNone (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (K : Type v) (q : IndependentRingPrimitive.Query K) :
    ObjectFormula.{u, v, 0} U :=
  carrierAnchor t
    (.cell (.coefficient (.operation K q)) (ULift.up (ULift.up none)))

structure TypedInstances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  operationSome : ∀ K q,
    K = IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t) →
      ∃ y, (operationSome t K q y).evaluate t
  operationNone : ∀ K q,
    K ≠ IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t) →
      (operationNone t K q).evaluate t

theorem typed_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentRingPrimitive.Carrier.IsTyped
        (IndependentGeometryPrimitive.coefficient t) ↔ TypedInstances t := by
  constructor
  · intro ht
    refine ⟨?_, ?_⟩
    · intro K q hK
      have hs := (ht K q).2 hK
      cases ho : ((IndependentGeometryPrimitive.coefficient t) (.operation K q)).down with
      | none => simp [ho] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [operationSome, carrierAnchor_evaluate, ObjectFormula.evaluate]
          apply ULift.ext
          apply ULift.ext
          exact ho
    · intro K q hK
      have hn := IndependentInvariantSignaturePrimitive.option_none _ (mt (ht K q).1 hK)
      simp only [operationNone, carrierAnchor_evaluate, ObjectFormula.evaluate]
      apply ULift.ext
      apply ULift.ext
      exact hn
  · intro hi K q
    constructor
    · intro hs
      by_contra hK
      have hn := hi.operationNone K q hK
      simp only [operationNone, carrierAnchor_evaluate, ObjectFormula.evaluate] at hn
      have he := congrArg (fun value => value.down.down) hn
      change ((IndependentGeometryPrimitive.coefficient t) (.operation K q)).down = none at he
      rw [he] at hs
      exact Bool.noConfusion hs
    · intro hK
      obtain ⟨y, hy⟩ := hi.operationSome K q hK
      simp only [operationSome, carrierAnchor_evaluate, ObjectFormula.evaluate] at hy
      have he := congrArg (fun value => value.down.down) hy
      change ((IndependentGeometryPrimitive.coefficient t) (.operation K q)).down = some y at he
      rw [he]
      rfl

def activeAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (_ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (q : IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t)))
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  carrierAnchor t
    (.and (.cell (.coefficient (.operation _ q))
      (t (.coefficient (.operation _ q)))) body)

def activeAnchors (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t)) :
    List (IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t))) →
      ObjectFormula.{u, v, w} U → ObjectFormula.{u, v, w} U
  | [], body => body
  | q :: qs, body => activeAnchor t ht q (activeAnchors t ht qs body)

@[simp] theorem activeAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (q : IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t)))
    (body : ObjectFormula.{u, v, w} U) :
    (activeAnchor t ht q body).evaluate t ↔ body.evaluate t := by
  simp [activeAnchor, ObjectFormula.evaluate]

@[simp] theorem activeAnchors_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (qs : List (IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t))))
    (body : ObjectFormula.{u, v, w} U) :
    (activeAnchors t ht qs body).evaluate t ↔ body.evaluate t := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [activeAnchors, ih]

abbrev active (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t)) :=
  IndependentRingPrimitive.Carrier.active (IndependentGeometryPrimitive.coefficient t) ht

def activeValue (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (_ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (q : IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t)))
    (value : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  carrierAnchor t
    (.cell (.coefficient (.operation _ q)) (ULift.up (ULift.up (some value))))

@[simp] theorem activeValue_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (q : IndependentRingPrimitive.Query
      (IndependentRingPrimitive.Carrier.carrier
        (IndependentGeometryPrimitive.coefficient t)))
    (value : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) :
    (activeValue t ht q value).evaluate t ↔ active t ht q = value := by
  simp only [activeValue, carrierAnchor_evaluate, ObjectFormula.evaluate]
  constructor
  · intro h
    have he := congrArg (fun result => result.down.down) h
    exact Option.some.inj ((Option.some_get _).trans he)
  · intro h
    apply ULift.ext
    apply ULift.ext
    exact (Option.some_get _).symm.trans (congrArg some h)

def addAssoc (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a b c : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht
    [.add a b, .add ((active t ht) (.add a b)) c, .add b c,
      .add a ((active t ht) (.add b c))]
    (activeValue t ht (.add ((active t ht) (.add a b)) c)
      ((active t ht) (.add a ((active t ht) (.add b c)))))

def zeroAdd (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht [.zero, .add ((active t ht) .zero) a]
    (activeValue t ht (.add ((active t ht) .zero) a) a)

def negAddCancel (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht [.neg a, .add ((active t ht) (.neg a)) a, .zero]
    (activeValue t ht (.add ((active t ht) (.neg a)) a) ((active t ht) .zero))

def mulAssoc (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a b c : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht
    [.mul a b, .mul ((active t ht) (.mul a b)) c, .mul b c,
      .mul a ((active t ht) (.mul b c))]
    (activeValue t ht (.mul ((active t ht) (.mul a b)) c)
      ((active t ht) (.mul a ((active t ht) (.mul b c)))))

def mulComm (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a b : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht [.mul a b, .mul b a]
    (activeValue t ht (.mul a b) ((active t ht) (.mul b a)))

def oneMul (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht [.one, .mul ((active t ht) .one) a]
    (activeValue t ht (.mul ((active t ht) .one) a) a)

def leftDistrib (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t))
    (a b c : IndependentRingPrimitive.Carrier.carrier
      (IndependentGeometryPrimitive.coefficient t)) : ObjectFormula.{u, v, v} U :=
  activeAnchors t ht
    [.add b c, .mul a ((active t ht) (.add b c)), .mul a b, .mul a c,
      .add ((active t ht) (.mul a b)) ((active t ht) (.mul a c))]
    (activeValue t ht (.mul a ((active t ht) (.add b c)))
      ((active t ht) (.add ((active t ht) (.mul a b)) ((active t ht) (.mul a c)))))

structure LawInstances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t)) : Prop where
  addAssoc : ∀ a b c, (addAssoc t ht a b c).evaluate t
  zeroAdd : ∀ a, (zeroAdd t ht a).evaluate t
  negAddCancel : ∀ a, (negAddCancel t ht a).evaluate t
  mulAssoc : ∀ a b c, (mulAssoc t ht a b c).evaluate t
  mulComm : ∀ a b, (mulComm t ht a b).evaluate t
  oneMul : ∀ a, (oneMul t ht a).evaluate t
  leftDistrib : ∀ a b c, (leftDistrib t ht a b c).evaluate t

theorem lawful_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentRingPrimitive.Carrier.IsTyped
      (IndependentGeometryPrimitive.coefficient t)) :
    IndependentRingPrimitive.Carrier.IsLawful
        (IndependentGeometryPrimitive.coefficient t) ht ↔ LawInstances t ht := by
  unfold IndependentRingPrimitive.Carrier.IsLawful
  constructor
  · intro hl
    exact {
      addAssoc := fun a b c => by simpa [addAssoc] using hl.add_assoc a b c
      zeroAdd := fun a => by simpa [zeroAdd] using hl.zero_add a
      negAddCancel := fun a => by simpa [negAddCancel] using hl.neg_add_cancel a
      mulAssoc := fun a b c => by simpa [mulAssoc] using hl.mul_assoc a b c
      mulComm := fun a b => by simpa [mulComm] using hl.mul_comm a b
      oneMul := fun a => by simpa [oneMul] using hl.one_mul a
      leftDistrib := fun a b c => by simpa [leftDistrib] using hl.left_distrib a b c }
  · intro hi
    exact {
      add_assoc := fun a b c => by simpa [addAssoc] using hi.addAssoc a b c
      zero_add := fun a => by simpa [zeroAdd] using hi.zeroAdd a
      neg_add_cancel := fun a => by simpa [negAddCancel] using hi.negAddCancel a
      mul_assoc := fun a b c => by simpa [mulAssoc] using hi.mulAssoc a b c
      mul_comm := fun a b => by simpa [mulComm] using hi.mulComm a b
      one_mul := fun a => by simpa [oneMul] using hi.oneMul a
      left_distrib := fun a b c => by simpa [leftDistrib] using hi.leftDistrib a b c }

structure Instances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  typed : TypedInstances t
  lawful : LawInstances t ((typed_iff_instances t).mpr typed)

theorem typedLawful_iff_instances (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    (∃ ht : IndependentRingPrimitive.Carrier.IsTyped
        (IndependentGeometryPrimitive.coefficient t),
      IndependentRingPrimitive.Carrier.IsLawful
        (IndependentGeometryPrimitive.coefficient t) ht) ↔ Instances t := by
  constructor
  · rintro ⟨ht, hl⟩
    let hi := (typed_iff_instances t).mp ht
    refine ⟨hi, ?_⟩
    exact (lawful_iff_instances t ((typed_iff_instances t).mpr hi)).mp
      (by simpa only [Subsingleton.elim ht ((typed_iff_instances t).mpr hi)] using hl)
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t).mpr ht, (lawful_iff_instances t _).mpr hl⟩

end Coefficient

structure FoundationInstances (t : IndependentGeometryPrimitive.Table.{u, v} U) : Prop where
  extraction : Extraction.Instances t
  finite : Finite.Instances t ((Extraction.typed_iff_instances t).mpr extraction)
  composition : Composition.Instances t
  invariant : Invariants.Instances t
  signature : Signature.Instances t
  operation : Operations.Instances t
  atom : Atom.Instances t
  coefficient : Coefficient.Instances t

theorem foundationLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U) :
    IndependentGeometryPrimitive.FoundationLaws t ↔ FoundationInstances t := by
  constructor
  · intro hl
    let he := (Extraction.typed_iff_instances t).mp hl.extraction
    refine {
      extraction := he
      finite := ?_
      composition := (Composition.lawful_iff_instances t).mp hl.composition
      invariant := (Invariants.typed_iff_instances t).mp hl.invariant
      signature := (Signature.typed_iff_instances t).mp hl.signature
      operation := (Operations.typedLawful_iff_instances t).mp hl.operation
      atom := (Atom.laws_iff_instances t).mp hl.atom
      coefficient := (Coefficient.typedLawful_iff_instances t).mp hl.coefficient }
    exact (Finite.listFinite_iff_instances t ((Extraction.typed_iff_instances t).mpr he)).mp
      hl.finite
  · intro hi
    let he := (Extraction.typed_iff_instances t).mpr hi.extraction
    exact {
      extraction := he
      finite := (Finite.listFinite_iff_instances t he).mpr hi.finite
      composition := (Composition.lawful_iff_instances t).mpr hi.composition
      invariant := (Invariants.typed_iff_instances t).mpr hi.invariant
      signature := (Signature.typed_iff_instances t).mpr hi.signature
      operation := (Operations.typedLawful_iff_instances t).mpr hi.operation
      atom := (Atom.laws_iff_instances t).mpr hi.atom
      coefficient := (Coefficient.typedLawful_iff_instances t).mpr hi.coefficient }

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectFoundationFinite
