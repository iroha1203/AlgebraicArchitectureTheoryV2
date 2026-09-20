import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealization
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealization
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryPrimitiveAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for independent realization Hom laws

Every realization law formula below reads only exact cells of the two flattened
endpoint tables and the common Boolean Hom table.  The realization reading
predicates remain quantified conditions outside the finite formula syntax.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RealizationLawFinite

noncomputable section

universe u v

open Site IndependentGeometryTableAssembly IndependentFiniteLawFormula
  IndependentFiniteGraphLawFormula

variable {U : AtomCarrier.{u}}

variable {A B : ArchitectureObject U}

def contextQuery {mode : Mode} (W : ArchCtx A) (V : ArchCtx B) :
    Query.{u, v} U mode :=
  .atObjects A B (.context .forward W V)

def representativeSupportQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeSupport W V x y))

def representativeAxisQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeAxis W V x y))

def representativeObservableQuery (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Query.{u, v} U .representative :=
  .atObjects A B (.realization (.representativeObservable W V x y))

def explicitSupportQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitSupport direction W V x y))

def explicitAxisQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitAxis direction W V x y))

def explicitObservableQuery (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Query.{u, v} U .explicit :=
  .atObjects A B (.realization (.explicitObservable direction W V x y))

theorem representativeSupportRows_iff
    (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Support) (fun V : ArchCtx B => V.Support)
      (RepresentativeRealization.contextPoints h)
      (RepresentativeRealization.support h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Support)
        (T := fun V : ArchCtx B => V.Support) h
        (contextQuery (U := U) (A := A) (B := B))
        (representativeSupportQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeSupportQuery,
    RepresentativeRealization.contextPoints, RepresentativeRealization.support] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeSupportQuery (U := U) (A := A) (B := B)))

theorem representativeAxisRows_iff
    (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Axis) (fun V : ArchCtx B => V.Axis)
      (RepresentativeRealization.contextPoints h)
      (RepresentativeRealization.axis h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Axis)
        (T := fun V : ArchCtx B => V.Axis) h
        (contextQuery (U := U) (A := A) (B := B))
        (representativeAxisQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeAxisQuery,
    RepresentativeRealization.contextPoints, RepresentativeRealization.axis] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeAxisQuery (U := U) (A := A) (B := B)))

theorem representativeObservableRows_iff
    (h : Table.{u, v} U .representative) :
    IndependentFixedIndexedPointGraph.IsLawful
      (fun W : ArchCtx A => W.Observable) (fun V : ArchCtx B => V.Observable)
      (RepresentativeRealization.contextPoints h)
      (RepresentativeRealization.observable h) ↔
      IndexedRows.Instances (S := fun W : ArchCtx A => W.Observable)
        (T := fun V : ArchCtx B => V.Observable) h
        (contextQuery (U := U) (A := A) (B := B))
        (representativeObservableQuery (U := U) (A := A) (B := B)) := by
  simpa [contextQuery, representativeObservableQuery,
    RepresentativeRealization.contextPoints, RepresentativeRealization.observable] using
    (IndexedRows.lawful_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .representative))
      (representativeObservableQuery (U := U) (A := A) (B := B)))

namespace Representative

def supportReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom) :
    Formula.{u, v, 0} U .representative :=
  .and (.hom (contextQuery W V) true)
    (.and (.hom (representativeSupportQuery W V x y) true)
      (.hom (.atom .forward a b) true))

def axisReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) :
    Formula.{u, v, 0} U .representative :=
  .and (.hom (contextQuery W V) true)
    (.hom (representativeAxisQuery W V x y) true)

def observableReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) :
    Formula.{u, v, 0} U .representative :=
  .and (.hom (contextQuery W V) true)
    (.hom (representativeObservableQuery W V x y) true)

def supportNaturality (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : W.Support) (y : V.Support) (xx : X.Support) (yy : Y.Support) :
    Formula.{u, v, 0} U .representative :=
  .implies (.hom (contextQuery W V) true)
    (.implies (.hom (contextQuery X Y) true)
      (.implies (.hom (representativeSupportQuery W V x y) true)
        (.implies
          (.source (.atObject A (.context (.support W X x))) (some ⟨⟨some xx⟩⟩))
          (.implies
            (.target (.atObject B (.context (.support V Y y))) (some ⟨⟨some yy⟩⟩))
            (.hom (representativeSupportQuery X Y xx yy) true)))))

def axisNaturality (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : W.Axis) (y : V.Axis) (xx : X.Axis) (yy : Y.Axis) :
    Formula.{u, v, 0} U .representative :=
  .implies (.hom (contextQuery W V) true)
    (.implies (.hom (contextQuery X Y) true)
      (.implies (.hom (representativeAxisQuery W V x y) true)
        (.implies
          (.source (.atObject A (.context (.axis W X x))) (some ⟨⟨some xx⟩⟩))
          (.implies
            (.target (.atObject B (.context (.axis V Y y))) (some ⟨⟨some yy⟩⟩))
            (.hom (representativeAxisQuery X Y xx yy) true)))))

def observableNaturality (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : X.Observable) (y : Y.Observable) (xx : W.Observable) (yy : V.Observable) :
    Formula.{u, v, 0} U .representative :=
  .implies (.hom (contextQuery W V) true)
    (.implies (.hom (contextQuery X Y) true)
      (.implies (.hom (representativeObservableQuery X Y x y) true)
        (.implies
          (.source (.atObject A (.context (.observable W X x))) (some ⟨⟨some xx⟩⟩))
          (.implies
            (.target (.atObject B (.context (.observable V Y y))) (some ⟨⟨some yy⟩⟩))
            (.hom (representativeObservableQuery W V xx yy) true)))))

structure Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U .representative) : Prop where
  supportRows : IndexedRows.Instances (S := fun W : ArchCtx A => W.Support)
    (T := fun V : ArchCtx B => V.Support) h
      (contextQuery (A := A) (B := B))
      (representativeSupportQuery (A := A) (B := B))
  axisRows : IndexedRows.Instances (S := fun W : ArchCtx A => W.Axis)
    (T := fun V : ArchCtx B => V.Axis) h
      (contextQuery (A := A) (B := B))
      (representativeAxisQuery (A := A) (B := B))
  observableRows : IndexedRows.Instances (S := fun W : ArchCtx A => W.Observable)
    (T := fun V : ArchCtx B => V.Observable) h
      (contextQuery (A := A) (B := B))
      (representativeObservableQuery (A := A) (B := B))
  supportReads : ∀ (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom),
    (supportReads (U := U) (A := A) (B := B) W V x y a b).evaluate
      sourceTable targetTable h → W.minimal.supportReads x a → V.minimal.supportReads y b
  axisReads : ∀ (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis),
    (axisReads (U := U) (A := A) (B := B) W V x y).evaluate sourceTable targetTable h →
      W.minimal.axisReads x → V.minimal.axisReads y
  observableReads : ∀ (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable),
    (observableReads (U := U) (A := A) (B := B) W V x y).evaluate
      sourceTable targetTable h → W.minimal.observableReads x → V.minimal.observableReads y
  supportNaturality : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : W.Support) (y : V.Support) (xx : X.Support) (yy : Y.Support),
    (supportNaturality (U := U) (A := A) (B := B) W X V Y x y xx yy).evaluate
      sourceTable targetTable h
  axisNaturality : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : W.Axis) (y : V.Axis) (xx : X.Axis) (yy : Y.Axis),
    (axisNaturality (U := U) (A := A) (B := B) W X V Y x y xx yy).evaluate
      sourceTable targetTable h
  observableNaturality : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (x : X.Observable) (y : Y.Observable) (xx : W.Observable) (yy : V.Observable),
    (observableNaturality (U := U) (A := A) (B := B) W X V Y x y xx yy).evaluate
      sourceTable targetTable h

theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U .representative) :
    RepresentativeRealization.PointLaws s.1.val.2.1.val t.1.val.2.1.val h ↔
      Instances
        (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  constructor
  · intro hp
    refine {
      supportRows := (representativeSupportRows_iff h).mp hp.supportRows
      axisRows := (representativeAxisRows_iff h).mp hp.axisRows
      observableRows := (representativeObservableRows_iff h).mp hp.observableRows
      supportReads := ?_
      axisReads := ?_
      observableReads := ?_
      supportNaturality := ?_
      axisNaturality := ?_
      observableNaturality := ?_ }
    · intro W V x y a b hcells hread
      exact hp.supportReads W V x y a b hcells.1 hcells.2.1 hcells.2.2 hread
    · intro W V x y hcells hread
      exact hp.axisReads W V x y hcells.1 hcells.2 hread
    · intro W V x y hcells hread
      exact hp.observableReads W V x y hcells.1 hcells.2 hread
    · intro W X V Y x y xx yy
      simp only [supportNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hWV hXY hxy hs ht
      exact hp.supportNaturality W X V Y x y xx yy hWV hXY hxy
        (congrArg (fun z => z.down.down) (Option.some.inj hs))
        (congrArg (fun z => z.down.down) (Option.some.inj ht))
    · intro W X V Y x y xx yy
      simp only [axisNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hWV hXY hxy hs ht
      exact hp.axisNaturality W X V Y x y xx yy hWV hXY hxy
        (congrArg (fun z => z.down.down) (Option.some.inj hs))
        (congrArg (fun z => z.down.down) (Option.some.inj ht))
    · intro W X V Y x y xx yy
      simp only [observableNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hWV hXY hxy hs ht
      exact hp.observableNaturality W X V Y x y xx yy hWV hXY hxy
        (congrArg (fun z => z.down.down) (Option.some.inj hs))
        (congrArg (fun z => z.down.down) (Option.some.inj ht))
  · intro hi
    refine {
      supportRows := (representativeSupportRows_iff h).mpr hi.supportRows
      axisRows := (representativeAxisRows_iff h).mpr hi.axisRows
      observableRows := (representativeObservableRows_iff h).mpr hi.observableRows
      supportReads := ?_
      axisReads := ?_
      observableReads := ?_
      supportNaturality := ?_
      axisNaturality := ?_
      observableNaturality := ?_ }
    · intro W V x y a b hctx hrow hatom hread
      exact hi.supportReads W V x y a b ⟨hctx, hrow, hatom⟩ hread
    · intro W V x y hctx hrow hread
      exact hi.axisReads W V x y ⟨hctx, hrow⟩ hread
    · intro W V x y hctx hrow hread
      exact hi.observableReads W V x y ⟨hctx, hrow⟩ hread
    · intro W X V Y x y xx yy hWV hXY hxy hs ht
      have hf := hi.supportNaturality W X V Y x y xx yy
      simp only [supportNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      exact hf hWV hXY hxy
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ hs)))
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ ht)))
    · intro W X V Y x y xx yy hWV hXY hxy hs ht
      have hf := hi.axisNaturality W X V Y x y xx yy
      simp only [axisNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      exact hf hWV hXY hxy
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ hs)))
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ ht)))
    · intro W X V Y x y xx yy hWV hXY hxy hs ht
      have hf := hi.observableNaturality W X V Y x y xx yy
      simp only [observableNaturality, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      exact hf hWV hXY hxy
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ hs)))
        (congrArg some (ULift.ext _ _ (ULift.ext _ _ ht)))

end Representative

theorem explicitSupportRows_iff (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (ExplicitRealization.contextPoints (A := A) (B := B) h)
      (ExplicitRealization.support (A := A) (B := B) h .forward)
      (ExplicitRealization.support (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Support)
        (T := fun V : ArchCtx B => V.Support) h
        (contextQuery (U := U) (A := A) (B := B))
        (explicitSupportQuery (U := U) (A := A) (B := B) .forward)
        (explicitSupportQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitSupportQuery, ExplicitRealization.contextPoints,
    ExplicitRealization.support] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitSupportQuery (U := U) (A := A) (B := B) .forward)
      (explicitSupportQuery (U := U) (A := A) (B := B) .backward))

theorem explicitAxisRows_iff (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (ExplicitRealization.contextPoints (A := A) (B := B) h)
      (ExplicitRealization.axis (A := A) (B := B) h .forward)
      (ExplicitRealization.axis (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Axis)
        (T := fun V : ArchCtx B => V.Axis) h
        (contextQuery (U := U) (A := A) (B := B))
        (explicitAxisQuery (U := U) (A := A) (B := B) .forward)
        (explicitAxisQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitAxisQuery, ExplicitRealization.contextPoints,
    ExplicitRealization.axis] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitAxisQuery (U := U) (A := A) (B := B) .forward)
      (explicitAxisQuery (U := U) (A := A) (B := B) .backward))

theorem explicitObservableRows_iff (h : Table.{u, v} U .explicit) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (ExplicitRealization.contextPoints (A := A) (B := B) h)
      (ExplicitRealization.observable (A := A) (B := B) h .forward)
      (ExplicitRealization.observable (A := A) (B := B) h .backward) ↔
      IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Observable)
        (T := fun V : ArchCtx B => V.Observable) h
        (contextQuery (U := U) (A := A) (B := B))
        (explicitObservableQuery (U := U) (A := A) (B := B) .forward)
        (explicitObservableQuery (U := U) (A := A) (B := B) .backward) := by
  simpa [contextQuery, explicitObservableQuery, ExplicitRealization.contextPoints,
    ExplicitRealization.observable] using
    (IndexedRows.inverseLaws_iff_instances h
      (contextQuery (U := U) (A := A) (B := B) (mode := .explicit))
      (explicitObservableQuery (U := U) (A := A) (B := B) .forward)
      (explicitObservableQuery (U := U) (A := A) (B := B) .backward))

namespace Explicit

def supportReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom) :
    Formula.{u, v, 0} U .explicit :=
  .and (.hom (contextQuery W V) true)
    (.and (.hom (explicitSupportQuery .forward W V x y) true)
      (.hom (.atom .forward a b) true))

def axisReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Formula.{u, v, 0} U .explicit :=
  .and (.hom (contextQuery W V) true)
    (.hom (explicitAxisQuery .forward W V x y) true)

def observableReads (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Formula.{u, v, 0} U .explicit :=
  .and (.hom (contextQuery W V) true)
    (.hom (explicitObservableQuery .forward W V x y) true)

def inactive (W X : ArchCtx A) (V Y : ArchCtx B)
    (cell : RealizationQuery A B .explicit) : Formula.{u, v, 0} U .explicit :=
  .implies
    (.or (.hom (contextQuery W V) false) (.hom (contextQuery X Y) false))
    (.hom (.atObjects A B (.realization cell)) false)

def action (W X : ArchCtx A) (V Y : ArchCtx B)
    (input actual output : RealizationQuery A B .explicit) :
    Formula.{u, v, 0} U .explicit :=
  .implies (.hom (contextQuery W V) true)
    (.implies (.hom (contextQuery X Y) true)
      (.implies (.hom (.atObjects A B (.realization input)) true)
        (.iff (.hom (.atObjects A B (.realization actual)) true)
          (.hom (.atObjects A B (.realization output)) true))))

structure Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U .explicit) : Prop where
  supportRows : IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Support)
    (T := fun V : ArchCtx B => V.Support) h
      (contextQuery (A := A) (B := B))
      (explicitSupportQuery (A := A) (B := B) .forward)
      (explicitSupportQuery (A := A) (B := B) .backward)
  axisRows : IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Axis)
    (T := fun V : ArchCtx B => V.Axis) h
      (contextQuery (A := A) (B := B))
      (explicitAxisQuery (A := A) (B := B) .forward)
      (explicitAxisQuery (A := A) (B := B) .backward)
  observableRows : IndexedRows.InverseInstances (S := fun W : ArchCtx A => W.Observable)
    (T := fun V : ArchCtx B => V.Observable) h
      (contextQuery (A := A) (B := B))
      (explicitObservableQuery (A := A) (B := B) .forward)
      (explicitObservableQuery (A := A) (B := B) .backward)
  supportReads : ∀ (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) (a b : U.Atom),
    (supportReads (U := U) (A := A) (B := B) W V x y a b).evaluate
      sourceTable targetTable h →
        (W.minimal.supportReads x a ↔ V.minimal.supportReads y b)
  axisReads : ∀ (W : ArchCtx A) (V : ArchCtx B) (x : W.Axis) (y : V.Axis),
    (axisReads (U := U) (A := A) (B := B) W V x y).evaluate sourceTable targetTable h →
      (W.minimal.axisReads x ↔ V.minimal.axisReads y)
  observableReads : ∀ (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable),
    (observableReads (U := U) (A := A) (B := B) W V x y).evaluate
      sourceTable targetTable h →
        (W.minimal.observableReads x ↔ V.minimal.observableReads y)
  supportInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : V.Support) (z : Y.Support),
    (inactive (U := U) W X V Y (.actualSupport W X V Y g y z)).evaluate
      sourceTable targetTable h
  axisInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : V.Axis) (z : Y.Axis),
    (inactive (U := U) W X V Y (.actualAxis W X V Y g y z)).evaluate
      sourceTable targetTable h
  observableInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : Y.Observable) (z : V.Observable),
    (inactive (U := U) W X V Y (.actualObservable W X V Y g y z)).evaluate
      sourceTable targetTable h
  supportAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (x : W.Support) (y : V.Support) (z : Y.Support),
    (action (U := U) W X V Y (.explicitSupport .forward W V x y)
      (.actualSupport W X V Y g y z)
      (.explicitSupport .forward X Y (g.supportMap x) z)).evaluate sourceTable targetTable h
  axisAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (x : W.Axis) (y : V.Axis) (z : Y.Axis),
    (action (U := U) W X V Y (.explicitAxis .forward W V x y)
      (.actualAxis W X V Y g y z)
      (.explicitAxis .forward X Y (g.axisMap x) z)).evaluate sourceTable targetTable h
  observableAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (x : X.Observable) (y : Y.Observable) (z : V.Observable),
    (action (U := U) W X V Y (.explicitObservable .forward X Y x y)
      (.actualObservable W X V Y g y z)
      (.explicitObservable .forward W V (g.observableRestrict x) z)).evaluate
      sourceTable targetTable h

theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U .explicit) :
    ExplicitRealization.PointLaws
        (IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (IndependentCoreTableAssembly.generatedObject t.1.val.1) h ↔
      Instances
        (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  constructor
  · intro hp
    refine {
      supportRows := (explicitSupportRows_iff h).mp hp.supportRows
      axisRows := (explicitAxisRows_iff h).mp hp.axisRows
      observableRows := (explicitObservableRows_iff h).mp hp.observableRows
      supportReads := ?_
      axisReads := ?_
      observableReads := ?_
      supportInactive := ?_
      axisInactive := ?_
      observableInactive := ?_
      supportAction := ?_
      axisAction := ?_
      observableAction := ?_ }
    · intro W V x y a b hcells
      exact hp.supportReads W V x y a b hcells.1 hcells.2.1 hcells.2.2
    · intro W V x y hcells
      exact hp.axisReads W V x y hcells.1 hcells.2
    · intro W V x y hcells
      exact hp.observableReads W V x y hcells.1 hcells.2
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hp.supportInactive W X V Y g y z
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hp.axisInactive W X V Y g y z
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hp.observableInactive W X V Y g y z
    · intro W X V Y g x y z
      simp only [action, Formula.evaluate]
      intro hWV hXY hxy
      exact Bool.eq_iff_iff.mp (hp.supportAction W X V Y g x y z hWV hXY hxy)
    · intro W X V Y g x y z
      simp only [action, Formula.evaluate]
      intro hWV hXY hxy
      exact Bool.eq_iff_iff.mp (hp.axisAction W X V Y g x y z hWV hXY hxy)
    · intro W X V Y g x y z
      simp only [action, Formula.evaluate]
      intro hWV hXY hxy
      exact Bool.eq_iff_iff.mp (hp.observableAction W X V Y g x y z hWV hXY hxy)
  · intro hi
    refine {
      supportRows := (explicitSupportRows_iff h).mpr hi.supportRows
      axisRows := (explicitAxisRows_iff h).mpr hi.axisRows
      observableRows := (explicitObservableRows_iff h).mpr hi.observableRows
      supportReads := ?_
      axisReads := ?_
      observableReads := ?_
      supportInactive := ?_
      axisInactive := ?_
      observableInactive := ?_
      supportAction := ?_
      axisAction := ?_
      observableAction := ?_ }
    · intro W V x y a b hctx hrow hatom
      exact hi.supportReads W V x y a b ⟨hctx, hrow, hatom⟩
    · intro W V x y hctx hrow
      exact hi.axisReads W V x y ⟨hctx, hrow⟩
    · intro W V x y hctx hrow
      exact hi.observableReads W V x y ⟨hctx, hrow⟩
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hi.supportInactive W X V Y g y z
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hi.axisInactive W X V Y g y z
    · intro W X V Y g y z
      simpa only [inactive, Formula.evaluate] using hi.observableInactive W X V Y g y z
    · intro W X V Y g x y z hWV hXY hxy
      apply Bool.eq_iff_iff.mpr
      exact hi.supportAction W X V Y g x y z hWV hXY hxy
    · intro W X V Y g x y z hWV hXY hxy
      apply Bool.eq_iff_iff.mpr
      exact hi.axisAction W X V Y g x y z hWV hXY hxy
    · intro W X V Y g x y z hWV hXY hxy
      apply Bool.eq_iff_iff.mpr
      exact hi.observableAction W X V Y g x y z hWV hXY hxy

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RealizationLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RealizationLawFinite
