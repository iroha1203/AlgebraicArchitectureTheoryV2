import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectMatchingLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object context laws

Every context formula names the active object row that supplies its primitive
value.  Derived support, axis, and observable maps are used only after their
exact row cells have been included in the same formula.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site IndependentFiniteLawFormula
  ObjectMatchingFinite

variable {U : AtomCarrier.{u}}

abbrev rows (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :=
  IndependentGeometryPrimitive.dependent t ha A hA

def contextCell (A : ArchitectureObject U) (q : IndependentContextPrimitive.Query A)
    (value : q.Value) : ObjectFormula.{u, v, w} U :=
  .cell (.atObject A (.context q)) (some (ULift.up value))

@[simp] theorem contextCellEq_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentContextPrimitive.Query A) (value : q.Value) :
    t (.atObject A (.context q)) = some (ULift.up value) ↔
      IndependentGeometryPrimitive.contextTable (rows t ha A hA) q = value := by
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.context q)]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    apply congrArg some
    apply ULift.ext
    exact h

theorem contextCell_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentContextPrimitive.Query A) (value : q.Value) :
    (contextCell A q value : ObjectFormula.{u, v, w} U).evaluate t ↔
      IndependentGeometryPrimitive.contextTable (rows t ha A hA) q = value := by
  exact contextCellEq_iff t ha A hA q value

def contextAnchor (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentContextPrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.and (.cell (.atObject A (.context q))
      (some ((rows t ha A hA) (.context q)))) body)

@[simp] theorem contextAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentContextPrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) :
    (contextAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  simp only [contextAnchor, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and]
  exact and_iff_right (IndependentGeometryPrimitive.some_dependent t ha A hA (.context q)).symm

namespace Context

def supportSome (A : ArchitectureObject U) (W V : ArchCtx A) (s : W.Support)
    (y : V.Support) : ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up True))
    (contextCell A (.support W V s) (ULift.up (some y)))

def supportNone (A : ArchitectureObject U) (W V : ArchCtx A) (s : W.Support) :
    ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up False))
    (contextCell A (.support W V s) (ULift.up none))

def axisSome (A : ArchitectureObject U) (W V : ArchCtx A) (a : W.Axis)
    (y : V.Axis) : ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up True))
    (contextCell A (.axis W V a) (ULift.up (some y)))

def axisNone (A : ArchitectureObject U) (W V : ArchCtx A) (a : W.Axis) :
    ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up False))
    (contextCell A (.axis W V a) (ULift.up none))

def observableSome (A : ArchitectureObject U) (W V : ArchCtx A) (x : V.Observable)
    (y : W.Observable) : ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up True))
    (contextCell A (.observable W V x) (ULift.up (some y)))

def observableNone (A : ArchitectureObject U) (W V : ArchCtx A) (x : V.Observable) :
    ObjectFormula.{u, v, 0} U :=
  .and (contextCell A (.le W V) (ULift.up False))
    (contextCell A (.observable W V x) (ULift.up none))

theorem supportSome_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (s : W.Support) (y : V.Support) :
    (supportSome A W V s y).evaluate t ↔
      IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.support W V s)).down = some y := by
  change (contextCell A (.le W V) (ULift.up True)).evaluate t ∧
    (contextCell A (.support W V s) (ULift.up (some y))).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  exact and_congr
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _)
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _)

theorem supportNone_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (s : W.Support) :
    (supportNone A W V s).evaluate t ↔
      ¬ IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.support W V s)).down = none := by
  change (contextCell A (.le W V) (ULift.up False)).evaluate t ∧
    (contextCell A (.support W V s) (ULift.up none)).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  constructor
  · rintro ⟨hle, hs⟩
    exact ⟨fun h => by
      have he := congrArg ULift.down hle
      change IndependentContextPrimitive.le
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V = False at he
      rw [he] at h
      exact h, (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hs⟩
  · rintro ⟨hle, hs⟩
    exact ⟨by
      apply ULift.ext
      exact propext (iff_false_intro hle),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr hs⟩

theorem axisSome_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (a : W.Axis) (y : V.Axis) :
    (axisSome A W V a y).evaluate t ↔
      IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.axis W V a)).down = some y := by
  change (contextCell A (.le W V) (ULift.up True)).evaluate t ∧
    (contextCell A (.axis W V a) (ULift.up (some y))).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  exact and_congr
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _)
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _)

theorem axisNone_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (a : W.Axis) :
    (axisNone A W V a).evaluate t ↔
      ¬ IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.axis W V a)).down = none := by
  change (contextCell A (.le W V) (ULift.up False)).evaluate t ∧
    (contextCell A (.axis W V a) (ULift.up none)).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  constructor
  · rintro ⟨hle, hs⟩
    exact ⟨fun h => by
      have he := congrArg ULift.down hle
      change IndependentContextPrimitive.le
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V = False at he
      rw [he] at h
      exact h, (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hs⟩
  · rintro ⟨hle, hs⟩
    exact ⟨by
      apply ULift.ext
      exact propext (iff_false_intro hle),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr hs⟩

theorem observableSome_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (x : V.Observable) (y : W.Observable) :
    (observableSome A W V x y).evaluate t ↔
      IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.observable W V x)).down = some y := by
  change (contextCell A (.le W V) (ULift.up True)).evaluate t ∧
    (contextCell A (.observable W V x) (ULift.up (some y))).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  exact and_congr
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _)
    (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _)

theorem observableNone_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (x : V.Observable) :
    (observableNone A W V x).evaluate t ↔
      ¬ IndependentContextPrimitive.le
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)
          (.observable W V x)).down = none := by
  change (contextCell A (.le W V) (ULift.up False)).evaluate t ∧
    (contextCell A (.observable W V x) (ULift.up none)).evaluate t ↔ _
  rw [contextCell_evaluate_iff t ha A hA, contextCell_evaluate_iff t ha A hA]
  constructor
  · rintro ⟨hle, hs⟩
    exact ⟨fun h => by
      have he := congrArg ULift.down hle
      change IndependentContextPrimitive.le
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V = False at he
      rw [he] at h
      exact h, (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mp hs⟩
  · rintro ⟨hle, hs⟩
    exact ⟨by
      apply ULift.ext
      exact propext (iff_false_intro hle),
      (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_eq_iff _ _).mpr hs⟩

structure TypedInstances (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  supportSome : ∀ W V s, IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      ∃ y, (supportSome A W V s y).evaluate t
  supportNone : ∀ W V s, ¬ IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      (supportNone A W V s).evaluate t
  axisSome : ∀ W V a, IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      ∃ y, (axisSome A W V a y).evaluate t
  axisNone : ∀ W V a, ¬ IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      (axisNone A W V a).evaluate t
  observableSome : ∀ W V x, IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      ∃ y, (observableSome A W V x y).evaluate t
  observableNone : ∀ W V x, ¬ IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V →
      (observableNone A W V x).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :
    IndependentContextPrimitive.IsTyped
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ↔
      TypedInstances t ha A hA := by
  let tc := IndependentGeometryPrimitive.contextTable (rows t ha A hA)
  constructor
  · intro ht
    refine {
      supportSome := ?_
      supportNone := ?_
      axisSome := ?_
      axisNone := ?_
      observableSome := ?_
      observableNone := ?_ }
    · intro W V s h
      have hs := (ht.support W V s).2 h
      cases ho : (tc (.support W V s)).down with
      | none =>
          rw [ho] at hs
          exact False.elim (Bool.noConfusion hs)
      | some y =>
          refine ⟨y, ?_⟩
          apply (supportSome_evaluate_iff t ha A hA W V s y).2
          exact ⟨h, by simpa only [tc] using ho⟩
    · intro W V s h
      have hn := IndependentContextPrimitive.option_none _ (mt (ht.support W V s).1 h)
      apply (supportNone_evaluate_iff t ha A hA W V s).2
      exact ⟨h, by simpa only [tc] using hn⟩
    · intro W V a h
      have hs := (ht.axis W V a).2 h
      cases ho : (tc (.axis W V a)).down with
      | none =>
          rw [ho] at hs
          exact False.elim (Bool.noConfusion hs)
      | some y =>
          refine ⟨y, ?_⟩
          apply (axisSome_evaluate_iff t ha A hA W V a y).2
          exact ⟨h, by simpa only [tc] using ho⟩
    · intro W V a h
      have hn := IndependentContextPrimitive.option_none _ (mt (ht.axis W V a).1 h)
      apply (axisNone_evaluate_iff t ha A hA W V a).2
      exact ⟨h, by simpa only [tc] using hn⟩
    · intro W V x h
      have hs := (ht.observable W V x).2 h
      cases ho : (tc (.observable W V x)).down with
      | none =>
          rw [ho] at hs
          exact False.elim (Bool.noConfusion hs)
      | some y =>
          refine ⟨y, ?_⟩
          apply (observableSome_evaluate_iff t ha A hA W V x y).2
          exact ⟨h, by simpa only [tc] using ho⟩
    · intro W V x h
      have hn := IndependentContextPrimitive.option_none _ (mt (ht.observable W V x).1 h)
      apply (observableNone_evaluate_iff t ha A hA W V x).2
      exact ⟨h, by simpa only [tc] using hn⟩
  · intro hi
    refine {
      support := ?_
      axis := ?_
      observable := ?_ }
    · intro W V s
      constructor
      · intro hs
        by_contra h
        have hn := (supportNone_evaluate_iff t ha A hA W V s).1
          (hi.supportNone W V s h)
        rw [hn.2] at hs
        exact Bool.noConfusion hs
      · intro h
        obtain ⟨y, hy⟩ := hi.supportSome W V s h
        have hy := (supportSome_evaluate_iff t ha A hA W V s y).1 hy
        rw [hy.2]
        rfl
    · intro W V a
      constructor
      · intro hs
        by_contra h
        have hn := (axisNone_evaluate_iff t ha A hA W V a).1
          (hi.axisNone W V a h)
        rw [hn.2] at hs
        exact Bool.noConfusion hs
      · intro h
        obtain ⟨y, hy⟩ := hi.axisSome W V a h
        have hy := (axisSome_evaluate_iff t ha A hA W V a y).1 hy
        rw [hy.2]
        rfl
    · intro W V x
      constructor
      · intro hs
        by_contra h
        have hn := (observableNone_evaluate_iff t ha A hA W V x).1
          (hi.observableNone W V x h)
        rw [hn.2] at hs
        exact Bool.noConfusion hs
      · intro h
        obtain ⟨y, hy⟩ := hi.observableSome W V x h
        have hy := (observableSome_evaluate_iff t ha A hA W V x y).1 hy
        rw [hy.2]
        rfl

/-! ## Context preorder and preservation laws -/

def reflFormula (A : ArchitectureObject U) (W : ArchCtx A) :
    ObjectFormula.{u, v, 0} U :=
  contextCell A (.le W W) (ULift.up True)

def transFormula (A : ArchitectureObject U) (W V X : ArchCtx A) :
    ObjectFormula.{u, v, 0} U :=
  .implies (contextCell A (.le W V) (ULift.up True))
    (.implies (contextCell A (.le V X) (ULift.up True))
      (contextCell A (.le W X) (ULift.up True)))

def supportFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (_ht : IndependentContextPrimitive.IsTyped
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)))
    (W V : ArchCtx A)
    (_h : IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V)
    (s : W.Support) (y : V.Support) : ObjectFormula.{u, v, 0} U :=
  supportSome A W V s y

def axisFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (_ht : IndependentContextPrimitive.IsTyped
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)))
    (W V : ArchCtx A)
    (_h : IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V)
    (a : W.Axis) (y : V.Axis) : ObjectFormula.{u, v, 0} U :=
  axisSome A W V a y

def observableFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (_ht : IndependentContextPrimitive.IsTyped
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)))
    (W V : ArchCtx A)
    (_h : IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V)
    (x : V.Observable) (y : W.Observable) : ObjectFormula.{u, v, 0} U :=
  observableSome A W V x y

structure LawInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (ht : IndependentContextPrimitive.IsTyped
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA))) : Prop where
  refl : ∀ W, (reflFormula A W).evaluate t
  trans : ∀ W V X, (transFormula A W V X).evaluate t
  support : ∀ W V h s a, W.minimal.supportReads s a →
    ∃ y, (supportFormula t ha A hA ht W V h s y).evaluate t ∧
      V.minimal.supportReads y a
  axis : ∀ W V h a, W.minimal.axisReads a →
    ∃ y, (axisFormula t ha A hA ht W V h a y).evaluate t ∧ V.minimal.axisReads y
  observable : ∀ W V h x, V.minimal.observableReads x →
    ∃ y, (observableFormula t ha A hA ht W V h x y).evaluate t ∧
      W.minimal.observableReads y

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (ht : IndependentContextPrimitive.IsTyped
      (IndependentGeometryPrimitive.contextTable (rows t ha A hA))) :
    IndependentContextPrimitive.IsLawful
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht ↔
      LawInstances t ha A hA ht := by
  constructor
  · intro hl
    refine {
      refl := ?_
      trans := ?_
      support := ?_
      axis := ?_
      observable := ?_ }
    · intro W
      apply (contextCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact propext ⟨fun _ => True.intro, fun _ => hl.refl W⟩
    · intro W V X
      simp only [transFormula, ObjectFormula.evaluate,
        contextCell_evaluate_iff t ha A hA]
      intro hWV hVX
      apply ULift.ext
      exact propext ⟨fun _ => True.intro, fun _ => hl.trans W V X
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).mp hWV)
        ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).mp hVX)⟩
    · intro W V h s a hs
      let y := IndependentContextPrimitive.supportMap
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h s
      refine ⟨y, ?_, hl.support W V h s a hs⟩
      apply (supportSome_evaluate_iff t ha A hA W V s y).2
      exact ⟨h, (Option.some_get _).symm⟩
    · intro W V h a hread
      let y := IndependentContextPrimitive.axisMap
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h a
      refine ⟨y, ?_, hl.axis W V h a hread⟩
      apply (axisSome_evaluate_iff t ha A hA W V a y).2
      exact ⟨h, (Option.some_get _).symm⟩
    · intro W V h x hread
      let y := IndependentContextPrimitive.observableRestrict
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h x
      refine ⟨y, ?_, hl.observable W V h x hread⟩
      apply (observableSome_evaluate_iff t ha A hA W V x y).2
      exact ⟨h, (Option.some_get _).symm⟩
  · intro hi
    refine {
      refl := ?_
      trans := ?_
      support := ?_
      axis := ?_
      observable := ?_ }
    · intro W
      have h := (contextCell_evaluate_iff t ha A hA _ _).1 (hi.refl W)
      exact (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).1 h
    · intro W V X hWV hVX
      have h := hi.trans W V X
      simp only [transFormula, ObjectFormula.evaluate,
        contextCell_evaluate_iff t ha A hA] at h
      exact (IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).1
        (h ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).2 hWV)
          ((IndependentGeometryHomPrimitive.CoreLawFinite.ulift_prop_true_iff _).2 hVX))
    · intro W V h s a hs
      obtain ⟨y, hy, hread⟩ := hi.support W V h s a hs
      have hy' := (supportSome_evaluate_iff t ha A hA W V s y).1 hy
      have he : IndependentContextPrimitive.supportMap
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h s = y :=
        Option.some.inj ((Option.some_get _).trans hy'.2)
      simpa [he] using hread
    · intro W V h a hread
      obtain ⟨y, hy, hyread⟩ := hi.axis W V h a hread
      have hy' := (axisSome_evaluate_iff t ha A hA W V a y).1 hy
      have he : IndependentContextPrimitive.axisMap
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h a = y :=
        Option.some.inj ((Option.some_get _).trans hy'.2)
      simpa [he] using hyread
    · intro W V h x hread
      obtain ⟨y, hy, hyread⟩ := hi.observable W V h x hread
      have hy' := (observableSome_evaluate_iff t ha A hA W V x y).1 hy
      have he : IndependentContextPrimitive.observableRestrict
          (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) ht h x = y :=
        Option.some.inj ((Option.some_get _).trans hy'.2)
      simpa [he] using hyread

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  typed : TypedInstances t ha A hA
  lawful : LawInstances t ha A hA ((typed_iff_instances t ha A hA).2 typed)

theorem contextLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :
    IndependentGeometryPrimitive.ContextLaws (rows t ha A hA) ↔
      Instances t ha A hA := by
  constructor
  · rintro ⟨ht, hl⟩
    let hi := (typed_iff_instances t ha A hA).1 ht
    refine ⟨hi, ?_⟩
    apply (lawful_iff_instances t ha A hA ((typed_iff_instances t ha A hA).2 hi)).1
    simpa only [Subsingleton.elim ht ((typed_iff_instances t ha A hA).2 hi)] using hl
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t ha A hA).2 ht,
      (lawful_iff_instances t ha A hA _).2 hl⟩

end Context

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
