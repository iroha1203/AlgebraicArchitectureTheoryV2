import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCoreLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextExpressions
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomEquationExpressions
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableExpressions
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationExpressions
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureExpressions
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomDetectorFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackageAssembly
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for complete package Hom laws

Every field of `PackageAssembly.PointLaws` is represented by quantified
instances of syntax whose leaves name source-object, target-object, or Hom
cells.  Detector matching is expanded recursively over its finite code, and
operation activation names both object-pair guards explicitly.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageLawFinite

noncomputable section

universe u v

open Site IndependentCorePrimitive IndependentCoreTableAssembly
  IndependentGeometryTableAssembly IndependentFiniteLawFormula
  IndependentFiniteGraphLawFormula

variable {U : AtomCarrier.{u}} {mode : Mode}

/-! ## Detector syntax -/

namespace Detector

def queryFormula : CircuitQuery U → CircuitQuery U → Formula.{u, v, 0} U mode
  | .atomPresent a, .atomPresent b => .hom (.atom .forward a b) true
  | .relationPresent a b, .relationPresent c d =>
      .and (.hom (.atom .forward a c) true) (.hom (.atom .forward b d) true)
  | .identificationPresent a b, .identificationPresent c d =>
      .and (.hom (.atom .forward a c) true) (.hom (.atom .forward b d) true)
  | _, _ => .falsity

def listFormula : List (CircuitQuery U × Bool) → List (CircuitQuery U × Bool) →
    Formula.{u, v, 0} U mode
  | [], [] => .truth
  | x :: xs, y :: ys =>
      .and (queryFormula x.1 y.1) (.and (.equal y.2 x.2) (listFormula xs ys))
  | _, _ => .falsity

def codeFormula : CircuitDetectorCode U → CircuitDetectorCode U → Formula.{u, v, 0} U mode
  | .reject, .reject => .truth
  | .exact p, .exact q => listFormula p.queries q.queries
  | .any p q, .any r s => .and (codeFormula p r) (codeFormula q s)
  | _, _ => .falsity

theorem queryFormula_evaluate_iff
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (p q : CircuitQuery U) :
    (queryFormula p q).evaluate sourceTable targetTable h ↔
      IndependentGeometryHomPrimitive.Detector.QueryMatch h p q := by
  cases p <;> cases q <;> rfl

theorem listFormula_evaluate_iff
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode)
    (xs ys : List (CircuitQuery U × Bool)) :
    (listFormula xs ys).evaluate sourceTable targetTable h ↔
      IndependentGeometryHomPrimitive.Detector.ListMatch h xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          simp only [listFormula, Formula.evaluate,
            queryFormula_evaluate_iff sourceTable targetTable h, ih,
            IndependentGeometryHomPrimitive.Detector.ListMatch]

theorem codeFormula_evaluate_iff
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (c d : CircuitDetectorCode U) :
    (codeFormula c d).evaluate sourceTable targetTable h ↔
      IndependentGeometryHomPrimitive.Detector.CodeMatch h c d := by
  induction c generalizing d with
  | reject => cases d <;> rfl
  | exact p =>
      cases d with
      | reject => rfl
      | exact q => exact listFormula_evaluate_iff sourceTable targetTable h _ _
      | any a b => rfl
  | any p q ihp ihq =>
      cases d with
      | reject => rfl
      | exact r => rfl
      | any r s =>
          exact and_congr (ihp r) (ihq s)

def pointFormula (A B : ArchitectureObject U) (I J : Type u)
    (i : I) (j : J) (c d : CircuitDetectorCode U) : Formula.{u, v, 0} U mode :=
  .implies (.hom (.atObjects A B (.equation .forward (.edge I J i j))) true)
    (.implies (.source (.circuit (.code I i)) (ULift.up (some c)))
      (.implies (.target (.circuit (.code J j)) (ULift.up (some d)))
        (codeFormula c d)))

def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (A B : ArchitectureObject U) : Prop :=
  ∀ (I J : Type u) (i : I) (j : J) (c d : CircuitDetectorCode U),
    (pointFormula A B I J i j c d).evaluate sourceTable targetTable h

theorem pointLaws_iff_instances
    (sourceObject targetObject : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    IndependentGeometryHomPrimitive.Detector.PointLaws
        sourceObject.1.val.2.2.2.val targetObject.1.val.2.2.2.val h
        (generatedObject sourceObject.1.val.1) (generatedObject targetObject.1.val.1) ↔
      Instances (IndependentGeometryPrimitive.flatten sourceObject)
        (IndependentGeometryPrimitive.flatten targetObject) h
        (generatedObject sourceObject.1.val.1) (generatedObject targetObject.1.val.1) := by
  constructor
  · intro hp I J i j c d
    simp only [pointFormula, Formula.evaluate, IndependentGeometryPrimitive.flatten,
      codeFormula_evaluate_iff]
    intro hij hs ht
    exact hp I J i j c d hij (congrArg ULift.down hs) (congrArg ULift.down ht)
  · intro hi I J i j c d hij hs ht
    have hp := hi I J i j c d
    simp only [pointFormula, Formula.evaluate, IndependentGeometryPrimitive.flatten,
      codeFormula_evaluate_iff] at hp
    exact hp hij (ULift.ext _ _ hs) (ULift.ext _ _ ht)

end Detector

/-! ## Operation carrier rows with two explicit object guards -/

namespace OperationRows

def inactive (A B A' B' : ArchitectureObject U)
    (q : IndependentCarrierGraph.Query.{u, u}) :
    BoolFormula.{max (u + 1) (v + 1), 0} (Query.{u, v} U mode) :=
  .implies
    (.or (.cell (.object A A') false) (.cell (.object B B') false))
    (.cell (.operation A B A' B' q) false)

def embed (A B A' B' : ArchitectureObject U)
    (q : IndependentCarrierGraph.Query.{u, u}) : Query.{u, v} U mode :=
  .operation A B A' B' q

structure Instances (h : Table.{u, v} U mode)
    (S T : ArchitectureObject U → ArchitectureObject U → Type u) : Prop where
  inactive : ∀ A B A' B' q,
    (inactive A B A' B' q).evaluate h
  active : ∀ A B A' B', h (.object A A') = true → h (.object B B') = true →
    CarrierRows.Instances h (embed A B A' B') (S A B) (T A' B')

theorem lawful_iff_instances (h : Table.{u, v} U mode)
    (S T : ArchitectureObject U → ArchitectureObject U → Type u) :
    Operation.IsLawful h S T ↔ Instances h S T := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · intro A B A' B' q
      simp only [inactive, BoolFormula.evaluate]
      intro hguard
      exact hp.inactive (A, B) (A', B')
        (Bool.and_eq_false_iff.mpr hguard) q
    · intro A B A' B' hA hB
      have hguard : Operation.endpoints h (A, B) (A', B') = true := by
        simp [Operation.endpoints, hA, hB]
      exact (CarrierRows.lawful_iff_instances h (embed A B A' B')
        (S A B) (T A' B')).mp
        (hp.active (A, B) (A', B') hguard)
  · intro hi
    refine ⟨?_, ?_⟩
    · rintro ⟨A, B⟩ ⟨A', B'⟩ hguard q
      have hp := hi.inactive A B A' B' q
      simp only [inactive, BoolFormula.evaluate] at hp
      exact hp (Bool.and_eq_false_iff.mp hguard)
    · rintro ⟨A, B⟩ ⟨A', B'⟩ hguard
      have hAB : h (.object A A') = true ∧ h (.object B B') = true := by
        simpa only [Operation.endpoints, Bool.and_eq_true] using hguard
      obtain ⟨hA, hB⟩ := hAB
      exact (CarrierRows.lawful_iff_instances h (embed A B A' B')
        (S A B) (T A' B')).mpr (hi.active A B A' B' hA hB)

end OperationRows

/-! ## Observable inverse ring rows -/

namespace ObservableRows

def contextIndex (A B : ArchitectureObject U) (W : ArchCtx A) (V : ArchCtx B) :
    Query.{u, v} U mode :=
  .atObjects A B (.context .forward W V)

def observableEmbed (A B : ArchitectureObject U) (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U mode
  | .forward q => .atObjects A B (.observable .forward W V q)
  | .backward q => .atObjects A B (.observable .backward W V (InverseRows.reverse q))

def forwardEmbed (A B : ArchitectureObject U) (W : ArchCtx A) (V : ArchCtx B) :
    IndependentCarrierGraph.Query.{u, u} → Query.{u, v} U mode :=
  fun q => observableEmbed A B W V (.forward q)

structure Instances {A B : ArchitectureObject U} (h : Table.{u, v} U mode)
    (S : ArchCtx A → Type u) (T : ArchCtx B → Type u)
    [∀ W, CommRing (S W)] [∀ V, CommRing (T V)] : Prop where
  graphs : DependentInverseRows.Instances h (contextIndex A B)
    (observableEmbed A B) S T
  ring : ∀ W V, h (contextIndex A B W V) = true →
    RingRows.Instances h (forwardEmbed A B W V)
      (IndependentRingPrimitive.read (inferInstance : CommRing (S W)))
      (IndependentRingPrimitive.read (inferInstance : CommRing (T V)))

theorem lawful_iff_instances {A B : ArchitectureObject U}
    (h : Table.{u, v} U mode) (S : ArchCtx A → Type u) (T : ArchCtx B → Type u)
    [∀ W, CommRing (S W)] [∀ V, CommRing (T V)] :
    Observable.IsLawful h S T ↔ Instances h S T := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · apply (DependentInverseRows.lawful_iff_instances h (contextIndex A B)
        (observableEmbed A B) S T).mp
      have hindex : (fun W V => h (contextIndex A B W V)) =
          Observable.contextPoints h := rfl
      have htable : (fun q => match q with
          | .edge W V r => h (observableEmbed A B W V r)) =
          Observable.points h A B := by
        funext q
        rcases q with ⟨W, V, r⟩
        cases r <;> rfl
      rw [hindex, htable]
      exact hp.graphs
    · intro W V hWV
      simpa [forwardEmbed, observableEmbed, Observable.contextPoints, Observable.points,
        IndependentIndexedInverseGraph.row, IndependentInverseGraph.forward,
        InverseRows.observable, InverseRows.asInverse] using
        (RingRows.preserves_iff_instances h (forwardEmbed A B W V)
          (IndependentRingPrimitive.read (inferInstance : CommRing (S W)))
          (IndependentRingPrimitive.read (inferInstance : CommRing (T V)))).mp
          (hp.ring W V hWV)
  · intro hi
    refine ⟨?_, ?_⟩
    · have hg := (DependentInverseRows.lawful_iff_instances h (contextIndex A B)
        (observableEmbed A B) S T).mpr hi.graphs
      have hindex : (fun W V => h (contextIndex A B W V)) =
          Observable.contextPoints h := rfl
      have htable : (fun q => match q with
          | .edge W V r => h (observableEmbed A B W V r)) =
          Observable.points h A B := by
        funext q
        rcases q with ⟨W, V, r⟩
        cases r <;> rfl
      rw [hindex, htable] at hg
      exact hg
    · intro W V hWV
      simpa [forwardEmbed, observableEmbed, Observable.contextPoints, Observable.points,
        IndependentIndexedInverseGraph.row, IndependentInverseGraph.forward,
        InverseRows.observable, InverseRows.asInverse] using
        (RingRows.preserves_iff_instances h (forwardEmbed A B W V)
          (IndependentRingPrimitive.read (inferInstance : CommRing (S W)))
          (IndependentRingPrimitive.read (inferInstance : CommRing (T V)))).mpr
          (hi.ring W V hWV)

end ObservableRows

/-! ## Remaining graph and expression families -/

def equationEmbed (A B : ArchitectureObject U) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U mode
  | .forward q => .atObjects A B (.equation .forward q)
  | .backward q => .atObjects A B (.equation .backward (InverseRows.reverse q))

def axisEmbed : IndependentCarrierGraph.Query.{u, u} → Query.{u, v} U mode :=
  fun q => .signatureAxis q

def coordinateIndex {I J : Type u} (i : I) (j : J) : Query.{u, v} U mode :=
  .signatureAxis (.edge I J i j)

def coordinateEmbed (K L : Type u) (k : K) (l : L) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U mode
  | .forward q => .signatureCoordinate .forward K L k l q
  | .backward q => .signatureCoordinate .backward K L k l (InverseRows.reverse q)

theorem flatten_generated_active (d : ObjectData.{u, v} U) :
    IndependentGeometryPrimitive.matching (IndependentGeometryPrimitive.flatten d)
      (.object (generatedObject d.1.val.1)) = true := by
  simp [IndependentGeometryPrimitive.matching, IndependentGeometryPrimitive.flatten,
    IndependentGeneratedObjectMatching.read, generatedObject_eq]

theorem contextPointLe_flatten (d : ObjectData.{u, v} U)
    (W X : ArchCtx (generatedObject d.1.val.1)) :
    ContextFinite.pointLe (IndependentGeometryPrimitive.flatten d)
        (generatedObject d.1.val.1) W X ↔
      (context d.1.val.2.1).le W X := by
  have hi := ContextFinite.pointLe_iff
    (IndependentGeometryPrimitive.flatten d)
    (IndependentGeometryPrimitive.flatten_active d)
    (generatedObject d.1.val.1) (flatten_generated_active d) W X
  rw [IndependentGeometryPrimitive.dependent_flatten] at hi
  simpa [IndependentGeometryPrimitive.contextTable,
    IndependentGeometryPrimitive.flattenDependent,
    context, IndependentContextPrimitive.assemble] using hi

theorem equationTable_flatten (d : ObjectData.{u, v} U) :
    IndependentGeometryPrimitive.equationTable
      (IndependentGeometryPrimitive.dependent
        (IndependentGeometryPrimitive.flatten d)
        (IndependentGeometryPrimitive.flatten_active d)
        (generatedObject d.1.val.1) (flatten_generated_active d)) =
      d.1.val.2.2.1.val := by
  rw [IndependentGeometryPrimitive.dependent_flatten]
  rfl

abbrev ContextInstances (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (A B : ArchitectureObject U) : Prop :=
  (∀ W : ArchCtx A, ∃! V : ArchCtx B,
    ContextFinite.evaluate s t h (.edge .forward W V)) ∧
  (∀ V : ArchCtx B, ∃! W : ArchCtx A,
    ContextFinite.evaluate s t h (.edge .backward W V)) ∧
  (∀ (W X : ArchCtx A) (V Y : ArchCtx B),
    ContextFinite.evaluate s t h (ContextFinite.forwardRule W X V Y)) ∧
  (∀ (W X : ArchCtx A) (V Y : ArchCtx B),
    ContextFinite.evaluate s t h (ContextFinite.backwardRule W X V Y)) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) (X : ArchCtx A),
    ContextFinite.evaluate s t h (ContextFinite.unitRule W V X)) ∧
  ∀ (V : ArchCtx B) (W : ArchCtx A) (Y : ArchCtx B),
    ContextFinite.evaluate s t h (ContextFinite.counitRule V W Y)

structure EquationPointInstances
    (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) (A B : ArchitectureObject U) : Prop where
  role : ∀ (I J : Type u) (i : I) (j : J) (r : EquationRole),
    EquationFinite.evaluate s t h (EquationFinite.roleRule (A := A) (B := B) I J i j r)
  naturality : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) (K L K' L' : Type u)
      (x : L) (y : L') (rx : K) (ry : K'),
    ObservableFinite.evaluate s t h
      (ObservableFinite.restrictionRule W X V Y K L K' L' x y rx ry)
  violation : ∀ (W : ArchCtx A) (V : ArchCtx B) (I J K L : Type u)
      (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
    EquationFinite.evaluate s t h
      (EquationFinite.violationRule W V I J K L i j a b x y)
  residual : ∀ (W : ArchCtx A) (V : ArchCtx B) (M N : ArchitectureObject U)
      (I J K L : Type u) (i : I) (j : J) (a b : U.Atom) (x : K) (y : L),
    EquationFinite.evaluate s t h
      (EquationFinite.residualRule W V M N I J K L i j a b x y)

abbrev OperationPointInstances
    (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (A B A' B' : ArchitectureObject U) (K L : Type u)
      (op : K) (op' : L) (a b ax bx : U.Atom),
    OperationFinite.evaluate s t h
      (OperationFinite.actionRule A B A' B' K L op op' a b ax bx)

abbrev SelectedInstances
    (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (I J : Type u) (i : I) (j : J),
    SignatureFinite.evaluate s t h (SignatureFinite.selectedRule I J i j)

abbrev CoordinatePointInstances
    (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) : Prop :=
  ∀ (M N : ArchitectureObject U) (I J K L : Type u)
      (i : I) (j : J) (x : K) (y : L),
    SignatureFinite.evaluate s t h
      (SignatureFinite.coordinateRule M N I J K L i j x y)

/-! ## Aggregate package instances -/

structure Instances (s t : ObjectData.{u, v} U) (h : Table.{u, v} U mode) : Prop where
  atom : CoreLawFinite.Atom.Instances h
  extraction : CoreLawFinite.Extraction.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    s.1.val.1.1.val.val t.1.val.1.1.val.val h
  matching : CoreLawFinite.TransportMatch.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
  generation : CoreLawFinite.Generation.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
  equationRows : InverseRows.Instances h
    (equationEmbed (generatedObject s.1.val.1) (generatedObject t.1.val.1))
    (IndependentEquationPrimitive.index s.1.val.2.2.1.val)
    (IndependentEquationPrimitive.index t.1.val.2.2.1.val)
  contextRows : ContextInstances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
    (generatedObject s.1.val.1) (generatedObject t.1.val.1)
  observableRows : letI := ObservableNatural.rings (s.1.val.2.2.1.val) (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
    letI := ObservableNatural.rings (t.1.val.2.2.1.val) (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
    ObservableRows.Instances h
      (IndependentEquationPrimitive.observableType s.1.val.2.2.1.val)
      (IndependentEquationPrimitive.observableType t.1.val.2.2.1.val)
  equationPoints : EquationPointInstances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
    (generatedObject s.1.val.1) (generatedObject t.1.val.1)
  detector : Detector.Instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
    (generatedObject s.1.val.1) (generatedObject t.1.val.1)
  operationRows : OperationRows.Instances h
    (Operations.carrier s.1.val.1.2.2.2.2.2.val)
    (Operations.carrier t.1.val.1.2.2.2.2.2.val)
  operationPoints : OperationPointInstances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
  axisRows : CarrierRows.Instances h axisEmbed
    (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
    (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val)
  coordinateRows : CandidateDependentInverseRows.Instances h
    (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
    (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val)
    coordinateIndex coordinateEmbed
    (IndependentInvariantSignaturePrimitive.Signature.coordinateType
      s.1.val.1.2.2.2.2.1.val s.1.val.1.2.2.2.2.1.property)
    (IndependentInvariantSignaturePrimitive.Signature.coordinateType
      t.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.property)
  selected : SelectedInstances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
  coordinates : CoordinatePointInstances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h

theorem equationRows_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    IndependentInverseGraph.IsLawful
        (IndependentEquationPrimitive.index s.1.val.2.2.1.val)
        (IndependentEquationPrimitive.index t.1.val.2.2.1.val)
        (IndependentGeometryHomPrimitive.InverseRows.equation h
          (generatedObject s.1.val.1) (generatedObject t.1.val.1)) ↔
      IndependentFiniteGraphLawFormula.InverseRows.Instances h
        (equationEmbed (generatedObject s.1.val.1) (generatedObject t.1.val.1))
        (IndependentEquationPrimitive.index s.1.val.2.2.1.val)
        (IndependentEquationPrimitive.index t.1.val.2.2.1.val) := by
  have hembed : (fun q => h (equationEmbed
      (generatedObject s.1.val.1) (generatedObject t.1.val.1) q)) =
      IndependentGeometryHomPrimitive.InverseRows.equation h
        (generatedObject s.1.val.1) (generatedObject t.1.val.1) := by
    funext q
    cases q <;> rfl
  rw [← hembed]
  exact IndependentFiniteGraphLawFormula.InverseRows.lawful_iff_instances h _ _ _

theorem contextRows_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    Context.IsLawful (context s.1.val.2.1).le (context t.1.val.2.1).le
        (Context.points h (generatedObject s.1.val.1) (generatedObject t.1.val.1)) ↔
      ContextInstances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h
        (generatedObject s.1.val.1) (generatedObject t.1.val.1) := by
  have hs : ContextFinite.pointLe (IndependentGeometryPrimitive.flatten s)
      (generatedObject s.1.val.1) = (context s.1.val.2.1).le := by
    funext W X
    exact propext (contextPointLe_flatten s W X)
  have ht : ContextFinite.pointLe (IndependentGeometryPrimitive.flatten t)
      (generatedObject t.1.val.1) = (context t.1.val.2.1).le := by
    funext W X
    exact propext (contextPointLe_flatten t W X)
  rw [← hs, ← ht]
  exact ContextFinite.lawful_iff_expressions
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h

theorem axisRows_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    IndependentCarrierGraph.IsLawful
        (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val)
        (signatureAxis h) ↔
      CarrierRows.Instances h axisEmbed
        (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val) := by
  exact CarrierRows.lawful_iff_instances h axisEmbed _ _

theorem coordinateRows_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    Signature.IsLawful h
        (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.coordinateType
          s.1.val.1.2.2.2.2.1.val s.1.val.1.2.2.2.2.1.property)
        (IndependentInvariantSignaturePrimitive.Signature.coordinateType
          t.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.property) ↔
      CandidateDependentInverseRows.Instances h
        (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val)
        coordinateIndex coordinateEmbed
        (IndependentInvariantSignaturePrimitive.Signature.coordinateType
          s.1.val.1.2.2.2.2.1.val s.1.val.1.2.2.2.2.1.property)
        (IndependentInvariantSignaturePrimitive.Signature.coordinateType
          t.1.val.1.2.2.2.2.1.val t.1.val.1.2.2.2.2.1.property) := by
  have hindex : (fun i j => h (coordinateIndex i j)) =
      Signature.axisPoints h
        (IndependentInvariantSignaturePrimitive.Signature.axis s.1.val.1.2.2.2.2.1.val)
        (IndependentInvariantSignaturePrimitive.Signature.axis t.1.val.1.2.2.2.2.1.val) := rfl
  have htable : (fun q => match q with
      | .edge K L k l r => h (coordinateEmbed K L k l r)) = Signature.points h := by
    funext q
    rcases q with ⟨K, L, k, l, r⟩
    cases r <;> rfl
  change IndependentCandidateIndexedInverseGraph.IsLawful _ _ _ _ _ _ ↔ _
  rw [← hindex, ← htable]
  exact CandidateDependentInverseRows.lawful_iff_instances h _ _ _ _ _ _

theorem observableRows_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    letI := ObservableNatural.rings (s.1.val.2.2.1.val) (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
    letI := ObservableNatural.rings (t.1.val.2.2.1.val) (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
    Observable.IsLawful h
        (IndependentEquationPrimitive.observableType s.1.val.2.2.1.val)
        (IndependentEquationPrimitive.observableType t.1.val.2.2.1.val) ↔
      ObservableRows.Instances h
        (IndependentEquationPrimitive.observableType s.1.val.2.2.1.val)
        (IndependentEquationPrimitive.observableType t.1.val.2.2.1.val) := by
  letI := ObservableNatural.rings (s.1.val.2.2.1.val)
    (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (t.1.val.2.2.1.val)
    (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
  exact ObservableRows.lawful_iff_instances h _ _

theorem equationPoints_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    EquationAssembly.PointLaws s.1.val.2.2.1.val t.1.val.2.2.1.val h ↔
      EquationPointInstances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h
        (generatedObject s.1.val.1) (generatedObject t.1.val.1) := by
  have hrole := EquationFinite.role_points_iff_expressions
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (IndependentGeometryPrimitive.flatten_active s) (IndependentGeometryPrimitive.flatten_active t)
    (flatten_generated_active s) (flatten_generated_active t) h
  have hnatural := ObservableFinite.pointLaws_iff_expressions
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (IndependentGeometryPrimitive.flatten_active s) (IndependentGeometryPrimitive.flatten_active t)
    (flatten_generated_active s) (flatten_generated_active t) h
  have hviolation := EquationFinite.violation_points_iff_expressions
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (IndependentGeometryPrimitive.flatten_active s) (IndependentGeometryPrimitive.flatten_active t)
    (flatten_generated_active s) (flatten_generated_active t) h
  have hresidual := EquationFinite.residual_points_iff_expressions
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t)
    (IndependentGeometryPrimitive.flatten_active s) (IndependentGeometryPrimitive.flatten_active t)
    (flatten_generated_active s) (flatten_generated_active t) h
  rw [equationTable_flatten s, equationTable_flatten t] at hrole hnatural hviolation hresidual
  constructor
  · intro hp
    exact {
      role := hrole.mp hp.role
      naturality := hnatural.mp hp.naturality
      violation := hviolation.mp hp.violation
      residual := hresidual.mp hp.residual }
  · intro hi
    exact {
      role := hrole.mpr hi.role
      naturality := hnatural.mpr hi.naturality
      violation := hviolation.mpr hi.violation
      residual := hresidual.mpr hi.residual }

theorem operationPoints_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    OperationNatural.PointLaws s.1.val.1.2.2.2.2.2.val
        t.1.val.1.2.2.2.2.2.val h ↔
      OperationPointInstances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  simpa [IndependentGeometryPrimitive.operation, IndependentGeometryPrimitive.flatten] using
    (OperationFinite.pointLaws_iff_expressions
      (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h)

theorem selected_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    SignatureLaws.SelectedPoints s.1.val.1.2.2.2.2.1.val
        t.1.val.1.2.2.2.2.1.val h ↔
      SelectedInstances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  simpa [IndependentGeometryPrimitive.signature, IndependentGeometryPrimitive.flatten] using
    (SignatureFinite.selected_points_iff_expressions
      (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h)

theorem coordinates_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    SignatureLaws.CoordinatePoints s.1.val.1.2.2.2.2.1.val
        t.1.val.1.2.2.2.2.1.val h ↔
      CoordinatePointInstances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  simpa [IndependentGeometryPrimitive.signature, IndependentGeometryPrimitive.flatten] using
    (SignatureFinite.coordinate_points_iff_expressions
      (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h)

theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U mode) :
    PackageAssembly.PointLaws s.1 t.1 h ↔ Instances s t h := by
  have hatom := CoreLawFinite.Atom.coherent_iff_instances h
  have hextraction := CoreLawFinite.Extraction.extractionLaws_iff_instances s t h
  have hmatching := CoreLawFinite.TransportMatch.lawful_iff_instances
    (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h
  have hgeneration : CoreLaws.GenerationLaws s.1.val.1.2.1.val t.1.val.1.2.1.val
      s.1.val.1.2.2.1 t.1.val.1.2.2.1 h ↔
      CoreLawFinite.Generation.Instances (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
    simpa [IndependentGeometryPrimitive.composition, IndependentGeometryPrimitive.formation,
      IndependentGeometryPrimitive.flatten] using
      (CoreLawFinite.Generation.generationLaws_iff_instances
        (IndependentGeometryPrimitive.flatten s) (IndependentGeometryPrimitive.flatten t) h)
  have hequation := equationRows_iff_instances s t h
  have hcontext := contextRows_iff_instances s t h
  have hobservable := observableRows_iff_instances s t h
  have hequationPoints := equationPoints_iff_instances s t h
  have hdetector := Detector.pointLaws_iff_instances s t h
  have hoperation := OperationRows.lawful_iff_instances h
    (Operations.carrier s.1.val.1.2.2.2.2.2.val)
    (Operations.carrier t.1.val.1.2.2.2.2.2.val)
  have hoperationPoints := operationPoints_iff_instances s t h
  have haxis := axisRows_iff_instances s t h
  have hcoordinate := coordinateRows_iff_instances s t h
  have hselected := selected_iff_instances s t h
  have hcoordinates := coordinates_iff_instances s t h
  constructor
  · intro hp
    exact {
      atom := hatom.mp hp.atom
      extraction := hextraction.mp hp.extraction
      matching := hmatching.mp hp.matching
      generation := hgeneration.mp hp.generation
      equationRows := hequation.mp hp.equationRows
      contextRows := hcontext.mp hp.contextRows
      observableRows := hobservable.mp hp.observableRows
      equationPoints := hequationPoints.mp hp.equationPoints
      detector := hdetector.mp hp.detector
      operationRows := hoperation.mp hp.operationRows
      operationPoints := hoperationPoints.mp hp.operationPoints
      axisRows := haxis.mp hp.axisRows
      coordinateRows := hcoordinate.mp hp.coordinateRows
      selected := hselected.mp hp.selected
      coordinates := hcoordinates.mp hp.coordinates }
  · intro hi
    exact {
      atom := hatom.mpr hi.atom
      extraction := hextraction.mpr hi.extraction
      matching := hmatching.mpr hi.matching
      generation := hgeneration.mpr hi.generation
      equationRows := hequation.mpr hi.equationRows
      contextRows := hcontext.mpr hi.contextRows
      observableRows := hobservable.mpr hi.observableRows
      equationPoints := hequationPoints.mpr hi.equationPoints
      detector := hdetector.mpr hi.detector
      operationRows := hoperation.mpr hi.operationRows
      operationPoints := hoperationPoints.mpr hi.operationPoints
      axisRows := haxis.mpr hi.axisRows
      coordinateRows := hcoordinate.mpr hi.coordinateRows
      selected := hselected.mpr hi.selected
      coordinates := hcoordinates.mpr hi.coordinates }

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.PackageLawFinite
