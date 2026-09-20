import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomJointLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawPointLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawLaws
import Formal.Util.AssertStandardAxioms

/-!
# Closed three-table formulas for complete raw Hom laws

The source and target raw responses occur as actual object-table cells in every
formula.  Polynomial instances expand finite monomial matching into finite
conjunctions and disjunctions of coordinate graph cells.  Row laws use the
closed total/inverse graph formulas from `IndependentFiniteGraphLawFormula`.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RawLawFinite

noncomputable section

universe u v

open Site IndependentGeometryTableAssembly IndependentFiniteLawFormula
  IndependentFiniteGraphLawFormula IndependentRawCandidate

variable {U : AtomCarrier.{u}}

abbrev Formula (mode : Mode) :=
  IndependentFiniteLawFormula.Formula.{u, v, 0} U mode

/-! ## Common formula helpers -/

def monomialMatch {A B : ArchitectureObject U}
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u)
    (m : C →₀ ℕ) (n : D →₀ ℕ) : Formula.{u, v} (U := U) .explicit :=
  .and
    (.allList m.support.toList fun c =>
      .anyList n.support.toList fun d =>
        .and
          (.hom (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) true)
          (.equal (m c) (n d)))
    (.allList n.support.toList fun d =>
      .anyList m.support.toList fun c =>
        .and
          (.hom (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) true)
          (.equal (m c) (n d)))

@[simp] theorem evaluate_monomialMatch_iff
    {A B : ArchitectureObject U}
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U .explicit) (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (m : C →₀ ℕ) (n : D →₀ ℕ) :
    (monomialMatch (U := U) W V C D m n).evaluate
        sourceTable targetTable h ↔
      IndependentPolynomialPointTransport.MonomialMatch
        (fun c d => h (.atObjects A B
          (.raw (.coordinate .forward W V (.edge C D c d))))) m n := by
  simp only [monomialMatch, Formula.evaluate, Formula.evaluate_allList,
    Formula.evaluate_anyList, Finset.mem_toList]
  rfl

/-! ## Explicit raw laws -/

namespace Explicit

variable {A B : ArchitectureObject U}

def coordinateQuery (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.coordinate .forward W V q))
  | .backward q => .atObjects A B (.raw (.coordinate .backward W V
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

def relationQuery (W : ArchCtx A) (V : ArchCtx B) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.relation .forward W V q))
  | .backward q => .atObjects A B (.raw (.relation .backward W V
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

def localDataQuery (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) :
    IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
  | .forward q => .atObjects A B (.raw (.localData .forward W V C D c d q))
  | .backward q => .atObjects A B (.raw (.localData .backward W V C D c d
      (IndependentGeometryHomPrimitive.InverseRows.reverse q)))

theorem coordinateRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) :
    IndependentInverseGraph.IsLawful C D
      (IndependentGeometryHomPrimitive.InverseRows.coordinate h A B W V) ↔
      IndependentFiniteGraphLawFormula.InverseRows.Instances h
        (coordinateQuery (U := U) W V) C D := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.coordinate h A B W V =
      fun q => h (coordinateQuery (U := U) W V q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact IndependentFiniteGraphLawFormula.InverseRows.lawful_iff_instances h
    (coordinateQuery (U := U) W V) C D

theorem relationRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (I J : Type u) :
    IndependentInverseGraph.IsLawful I J
      (IndependentGeometryHomPrimitive.InverseRows.relation h A B W V) ↔
      IndependentFiniteGraphLawFormula.InverseRows.Instances h
        (relationQuery (U := U) W V) I J := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.relation h A B W V =
      fun q => h (relationQuery (U := U) W V q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact IndependentFiniteGraphLawFormula.InverseRows.lawful_iff_instances h
    (relationQuery (U := U) W V) I J

theorem localDataRows_iff_instances (h : Table.{u, v} U .explicit)
    (W : ArchCtx A) (V : ArchCtx B) (C D : Type u) (c : C) (d : D)
    (L M : Type u) :
    IndependentInverseGraph.IsLawful L M
      (IndependentGeometryHomPrimitive.InverseRows.localData h A B W V C D c d) ↔
      IndependentFiniteGraphLawFormula.InverseRows.Instances h
        (localDataQuery (U := U) W V C D c d) L M := by
  have hquery : IndependentGeometryHomPrimitive.InverseRows.localData h A B W V C D c d =
      fun q => h (localDataQuery (U := U) W V C D c d q) := by
    funext q
    cases q <;> rfl
  rw [hquery]
  exact IndependentFiniteGraphLawFormula.InverseRows.lawful_iff_instances h
    (localDataQuery (U := U) W V C D c d) L M

def coordinateInactive (W : ArchCtx A) (V : ArchCtx B)
    (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u}) :
    Formula.{u, v} (U := U) .explicit :=
  .implies (.hom (.atObjects A B (.context .backward W V)) false)
    (.hom (.atObjects A B (.raw (.coordinate direction W V q))) false)

def relationInactive (W : ArchCtx A) (V : ArchCtx B)
    (direction : Direction) (q : IndependentCarrierGraph.Query.{u, u}) :
    Formula.{u, v} (U := U) .explicit :=
  .implies (.hom (.atObjects A B (.context .backward W V)) false)
    (.hom (.atObjects A B (.raw (.relation direction W V q))) false)

def localDataInactive (W : ArchCtx A) (V : ArchCtx B)
    (C D : Type u) (c : C) (d : D) (direction : Direction)
    (q : IndependentCarrierGraph.Query.{u, u}) : Formula.{u, v} (U := U) .explicit :=
  .implies
    (.or (.hom (.atObjects A B (.context .backward W V)) false)
      (.hom (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) false))
    (.hom (.atObjects A B (.raw (.localData direction W V C D c d q))) false)

def label (W : ArchCtx A) (V : ArchCtx B) (C D : Type u)
    (c : C) (d : D)
    (sourceLabel targetLabel : Option LawAlgebra.CoordinateLabel) :
    Formula.{u, v} (U := U) .explicit :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and
        (.hom (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) true)
        (.and
          (.source (.atObject A (.raw (.label W C c))) (some ⟨sourceLabel⟩))
          (.target (.atObject B (.raw (.label V D d))) (some ⟨targetLabel⟩)))))
    (.equal sourceLabel targetLabel)

def polynomial (W : ArchCtx A) (V : ArchCtx B)
    (C D I J : Type u) (rk rl : CoefficientRef.{v}) (i : I) (j : J)
    (p : IndependentPolynomialExpressions.Sparse C rk.1 rk.2)
    (p' : IndependentPolynomialExpressions.Sparse D rl.1 rl.2)
    (m : C →₀ ℕ) (n : D →₀ ℕ) : Formula.{u, v} (U := U) .explicit :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and (.hom (.atObjects A B (.raw (.relation .forward W V (.edge I J i j)))) true)
        (.and
          (.source (.atObject A (.raw (.polynomial W C I rk i))) (some ⟨some p⟩))
          (.and
            (.target (.atObject B (.raw (.polynomial V D J rl j))) (some ⟨some p'⟩))
            (monomialMatch (U := U) W V C D m n)))))
    (.hom (.coefficient (.edge rk.1 rl.1
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n))) true)

def image (W X : ArchCtx A) (V Y : ArchCtx B)
    (C D E F : Type u) (rk rl : CoefficientRef.{v}) (x : E) (y : F)
    (p : IndependentPolynomialExpressions.Sparse C rk.1 rk.2)
    (p' : IndependentPolynomialExpressions.Sparse D rl.1 rl.2)
    (m : C →₀ ℕ) (n : D →₀ ℕ) : Formula.{u, v} (U := U) .explicit :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and (.hom (.atObjects A B (.context .backward X Y)) true)
        (.and (.hom (.atObjects A B (.raw (.coordinate .forward X Y (.edge E F x y)))) true)
          (.and
            (.source (.atObject A (.raw (.image W X C E rk x))) (some ⟨some p⟩))
            (.and
              (.target (.atObject B (.raw (.image V Y D F rl y))) (some ⟨some p'⟩))
              (monomialMatch (U := U) W V C D m n))))))
    (.hom (.coefficient (.edge rk.1 rl.1
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient p' n))) true)

def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U .explicit) : Prop :=
  (∀ (W : ArchCtx A) (V : ArchCtx B) direction q,
    (coordinateInactive (U := U) W V direction q).evaluate
    sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) (C D : Type u),
    sourceTable (.atObject A (.raw (.coordinate W))) = some ⟨C⟩ →
    targetTable (.atObject B (.raw (.coordinate V))) = some ⟨D⟩ →
    h (.atObjects A B (.context .backward W V)) = true →
    IndependentFiniteGraphLawFormula.InverseRows.Instances h
      (coordinateQuery (U := U) W V) C D) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) direction q,
    (relationInactive (U := U) W V direction q).evaluate
    sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) (I J : Type u),
    sourceTable (.atObject A (.raw (.relation W))) = some ⟨I⟩ →
    targetTable (.atObject B (.raw (.relation V))) = some ⟨J⟩ →
    h (.atObjects A B (.context .backward W V)) = true →
    IndependentFiniteGraphLawFormula.InverseRows.Instances h
      (relationQuery (U := U) W V) I J) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C D (c : C) (d : D) direction q,
    (localDataInactive (U := U) W V C D c d direction q).evaluate
      sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C D (c : C) (d : D) (L M : Type u),
    sourceTable (.atObject A (.raw (.localData W C c))) = some ⟨some L⟩ →
    targetTable (.atObject B (.raw (.localData V D d))) = some ⟨some M⟩ →
    h (.atObjects A B (.context .backward W V)) = true →
    h (.atObjects A B (.raw (.coordinate .forward W V (.edge C D c d)))) = true →
    IndependentFiniteGraphLawFormula.InverseRows.Instances h
      (localDataQuery (U := U) W V C D c d) L M) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C D (c : C) (d : D)
    (sourceLabel targetLabel : Option LawAlgebra.CoordinateLabel),
    (label (U := U) W V C D c d sourceLabel targetLabel).evaluate
      sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C D I J
    (rk rl : CoefficientRef.{v}) (i : I) (j : J) p p' m n,
    (polynomial (U := U) W V C D I J rk rl i j p p' m n).evaluate
      sourceTable targetTable h) ∧
  (∀ (W X : ArchCtx A) (V Y : ArchCtx B) C D E F (rk rl : CoefficientRef.{v})
    (x : E) (y : F) p p' m n,
    (image (U := U) W X V Y C D E F rk rl x y p p' m n).evaluate
      sourceTable targetTable h)

/-- The nine explicit raw fields are exactly the closed finite instance
families above on the two independently flattened endpoint tables. -/
theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (h : Table.{u, v} U .explicit) :
    ExplicitRaw.PointLaws s.2.2.2.val t.2.2.2.val h ↔
      Instances
        (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h := by
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro W V direction q hctx
      cases direction with
      | forward => exact hp.coordinateInactive W V hctx (.forward q)
      | backward =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.coordinate,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hp.coordinateInactive W V hctx
              (.backward (IndependentGeometryHomPrimitive.InverseRows.reverse q))
    · intro W V C D hs ht hctx
      have hs' : s.2.2.2.val (.coordinate W) = ⟨C⟩ := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at hs
        exact Option.some.inj hs
      have ht' : t.2.2.2.val (.coordinate V) = ⟨D⟩ := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at ht
        exact Option.some.inj ht
      have hC : coord s.2.2.2.val W = C := congrArg ULift.down hs'
      have hD : coord t.2.2.2.val V = D := congrArg ULift.down ht'
      subst C
      subst D
      exact (coordinateRows_iff_instances h W V _ _).mp (hp.coordinateRows W V hctx)
    · intro W V direction q hctx
      cases direction with
      | forward => exact hp.relationInactive W V hctx (.forward q)
      | backward =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.relation,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hp.relationInactive W V hctx
              (.backward (IndependentGeometryHomPrimitive.InverseRows.reverse q))
    · intro W V I J hs ht hctx
      have hs' : s.2.2.2.val (.relation W) = ⟨I⟩ := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at hs
        exact Option.some.inj hs
      have ht' : t.2.2.2.val (.relation V) = ⟨J⟩ := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at ht
        exact Option.some.inj ht
      have hI : rel s.2.2.2.val W = I := congrArg ULift.down hs'
      have hJ : rel t.2.2.2.val V = J := congrArg ULift.down ht'
      subst I
      subst J
      exact (relationRows_iff_instances h W V _ _).mp (hp.relationRows W V hctx)
    · intro W V C D c d direction q hguard
      cases direction with
      | forward => exact hp.localDataInactive W V C D c d hguard (.forward q)
      | backward =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.localData,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hp.localDataInactive W V C D c d hguard
              (.backward (IndependentGeometryHomPrimitive.InverseRows.reverse q))
    · intro W V C D c d L M hs ht hctx hcoord
      have hs' : (s.2.2.2.val (.localData W C c)).down = some L := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at hs
        exact congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.localData V D d)).down = some M := by
        rw [IndependentGeometryPrimitive.flatten_at_generated] at ht
        exact congrArg ULift.down (Option.some.inj ht)
      exact (localDataRows_iff_instances h W V C D c d L M).mp
        (hp.localDataRows W V C D c d L M hctx hcoord hs' ht')
    · intro W V C D c d sourceLabel targetLabel
      simp only [label, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      rintro ⟨hctx, hcoord, hs, ht⟩
      have hs' : (s.2.2.2.val (.label W C c)).down = sourceLabel :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.label V D d)).down = targetLabel :=
        congrArg ULift.down (Option.some.inj ht)
      exact hs'.symm.trans ((hp.label W V C D c d hctx hcoord).trans ht')
    · intro W V C D I J rk rl i j p p' m n
      simp only [polynomial, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent,
        evaluate_monomialMatch_iff]
      rintro ⟨hctx, hrel, hs, ht, hmatch⟩
      have hs' : (s.2.2.2.val (.polynomial W C I rk i)).down = some p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.polynomial V D J rl j)).down = some p' :=
        congrArg ULift.down (Option.some.inj ht)
      exact hp.polynomial W V C D I J rk rl i j p p' hctx hrel hs' ht' m n hmatch
    · intro W X V Y C D E F rk rl x y p p' m n
      simp only [image, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent,
        evaluate_monomialMatch_iff]
      rintro ⟨hWV, hXY, hcoord, hs, ht, hmatch⟩
      have hs' : (s.2.2.2.val (.image W X C E rk x)).down = some p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.image V Y D F rl y)).down = some p' :=
        congrArg ULift.down (Option.some.inj ht)
      exact hp.image W X V Y C D E F rk rl x y p p' hWV hXY hcoord hs' ht' m n hmatch
  · rintro ⟨hci, hcr, hri, hrr, hldi, hldr, hlabel, hpoly, himage⟩
    constructor
    · intro W V hctx q
      cases q with
      | forward q => exact hci W V .forward q hctx
      | backward q =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.coordinate,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hci W V .backward (IndependentGeometryHomPrimitive.InverseRows.reverse q) hctx
    · intro W V hctx
      apply (coordinateRows_iff_instances h W V _ _).mpr
      exact hcr W V _ _
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ rfl))
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ rfl)) hctx
    · intro W V hctx q
      cases q with
      | forward q => exact hri W V .forward q hctx
      | backward q =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.relation,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hri W V .backward (IndependentGeometryHomPrimitive.InverseRows.reverse q) hctx
    · intro W V hctx
      apply (relationRows_iff_instances h W V _ _).mpr
      exact hrr W V _ _
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ rfl))
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ rfl)) hctx
    · intro W V C D c d hguard q
      cases q with
      | forward q => exact hldi W V C D c d .forward q hguard
      | backward q =>
          simpa [IndependentGeometryHomPrimitive.InverseRows.localData,
            IndependentGeometryHomPrimitive.InverseRows.asInverse] using
            hldi W V C D c d .backward
              (IndependentGeometryHomPrimitive.InverseRows.reverse q) hguard
    · intro W V C D c d L M hctx hcoord hs ht
      apply (localDataRows_iff_instances h W V C D c d L M).mpr
      exact hldr W V C D c d L M
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ hs))
        (by rw [IndependentGeometryPrimitive.flatten_at_generated]
            exact congrArg some (ULift.ext _ _ ht))
        hctx hcoord
    · intro W V C D c d hctx hcoord
      have hf := hlabel W V C D c d
        (s.2.2.2.val (.label W C c)).down (t.2.2.2.val (.label V D d)).down
      simp only [label, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      exact hf ⟨hctx, hcoord, rfl, rfl⟩
    · intro W V C D I J rk rl i j p p' hctx hrel hs ht m n hmatch
      have hf := hpoly W V C D I J rk rl i j p p' m n
      simp only [polynomial, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent,
        evaluate_monomialMatch_iff] at hf
      exact hf ⟨hctx, hrel,
        congrArg some (ULift.ext _ _ hs),
        congrArg some (ULift.ext _ _ ht), hmatch⟩
    · intro W X V Y C D E F rk rl x y p p' hWV hXY hcoord hs ht m n hmatch
      have hf := himage W X V Y C D E F rk rl x y p p' m n
      simp only [image, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent,
        evaluate_monomialMatch_iff] at hf
      exact hf ⟨hWV, hXY, hcoord,
        congrArg some (ULift.ext _ _ hs),
        congrArg some (ULift.ext _ _ ht), hmatch⟩

end Explicit

/-! ## Representative raw laws -/

namespace Representative

variable {A B : ArchitectureObject U}

def coordinate (W : ArchCtx A) (V : ArchCtx B) (C : Type u) :
    Formula.{u, v} (U := U) .representative :=
  .implies (.hom (.atObjects A B (.context .backward W V)) true)
    (.implies
      (.source (.atObject A (.raw (.coordinate W))) (some ⟨C⟩))
      (.target (.atObject B (.raw (.coordinate V))) (some ⟨C⟩)))

def relation (W : ArchCtx A) (V : ArchCtx B) (I : Type u) :
    Formula.{u, v} (U := U) .representative :=
  .implies (.hom (.atObjects A B (.context .backward W V)) true)
    (.implies
      (.source (.atObject A (.raw (.relation W))) (some ⟨I⟩))
      (.target (.atObject B (.raw (.relation V))) (some ⟨I⟩)))

def label (W : ArchCtx A) (V : ArchCtx B) (C : Type u) (c : C)
    (value : Option LawAlgebra.CoordinateLabel) :
    Formula.{u, v} (U := U) .representative :=
  .implies (.hom (.atObjects A B (.context .backward W V)) true)
    (.implies
      (.source (.atObject A (.raw (.label W C c))) (some ⟨value⟩))
      (.target (.atObject B (.raw (.label V C c))) (some ⟨value⟩)))

def localData (W : ArchCtx A) (V : ArchCtx B) (C : Type u) (c : C)
    (value : Option (Type u)) : Formula.{u, v} (U := U) .representative :=
  .implies (.hom (.atObjects A B (.context .backward W V)) true)
    (.implies
      (.source (.atObject A (.raw (.localData W C c))) (some ⟨value⟩))
      (.target (.atObject B (.raw (.localData V C c))) (some ⟨value⟩)))

def polynomialPresence (W : ArchCtx A) (V : ArchCtx B)
    (C I : Type u) (rk rl : CoefficientRef.{v}) (i : I)
    (p : Option (IndependentPolynomialExpressions.Sparse C rk.1 rk.2))
    (q : Option (IndependentPolynomialExpressions.Sparse C rl.1 rl.2)) :
    Formula.{u, v} (U := U) .representative :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and
        (.source (.atObject A (.raw (.polynomial W C I rk i))) (some ⟨p⟩))
        (.target (.atObject B (.raw (.polynomial V C I rl i))) (some ⟨q⟩))))
    (.equal p.isSome q.isSome)

def polynomialCoefficient (W : ArchCtx A) (V : ArchCtx B)
    (C I : Type u) (rk rl : CoefficientRef.{v}) (i : I)
    (p : IndependentPolynomialExpressions.Sparse C rk.1 rk.2)
    (q : IndependentPolynomialExpressions.Sparse C rl.1 rl.2) (m : C →₀ ℕ) :
    Formula.{u, v} (U := U) .representative :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and
        (.source (.atObject A (.raw (.polynomial W C I rk i))) (some ⟨some p⟩))
        (.target (.atObject B (.raw (.polynomial V C I rl i))) (some ⟨some q⟩))))
    (.hom (.coefficient (.edge rk.1 rl.1
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient q m))) true)

def targetReadable (V Y : ArchCtx B) : Formula.{u, v} (U := U) .representative :=
  .target (.atObject B (.context (.le V Y))) (some ⟨⟨True⟩⟩)

def imagePresence (W X : ArchCtx A) (V Y : ArchCtx B)
    (C D : Type u) (rk rl : CoefficientRef.{v}) (d : D)
    (p : Option (IndependentPolynomialExpressions.Sparse C rk.1 rk.2))
    (q : Option (IndependentPolynomialExpressions.Sparse C rl.1 rl.2)) :
    Formula.{u, v} (U := U) .representative :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and (.hom (.atObjects A B (.context .backward X Y)) true)
        (.and (targetReadable (U := U) V Y)
          (.and
            (.source (.atObject A (.raw (.image W X C D rk d))) (some ⟨p⟩))
            (.target (.atObject B (.raw (.image V Y C D rl d))) (some ⟨q⟩))))))
    (.equal p.isSome q.isSome)

def imageCoefficient (W X : ArchCtx A) (V Y : ArchCtx B)
    (C D : Type u) (rk rl : CoefficientRef.{v}) (d : D)
    (p : IndependentPolynomialExpressions.Sparse C rk.1 rk.2)
    (q : IndependentPolynomialExpressions.Sparse C rl.1 rl.2) (m : C →₀ ℕ) :
    Formula.{u, v} (U := U) .representative :=
  .implies
    (.and (.hom (.atObjects A B (.context .backward W V)) true)
      (.and (.hom (.atObjects A B (.context .backward X Y)) true)
        (.and (targetReadable (U := U) V Y)
          (.and
            (.source (.atObject A (.raw (.image W X C D rk d))) (some ⟨some p⟩))
            (.target (.atObject B (.raw (.image V Y C D rl d))) (some ⟨some q⟩))))))
    (.hom (.coefficient (.edge rk.1 rl.1
      (IndependentPolynomialPointTransport.sparseCoefficient p m)
      (IndependentPolynomialPointTransport.sparseCoefficient q m))) true)

def Instances (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U .representative)
    (rk rl : CoefficientRef.{v}) : Prop :=
  (∀ (W : ArchCtx A) (V : ArchCtx B) (C : Type u),
    (coordinate (U := U) W V C).evaluate sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) (I : Type u),
    (relation (U := U) W V I).evaluate sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C (c : C) value,
    (label (U := U) W V C c value).evaluate sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C (c : C) value,
    (localData (U := U) W V C c value).evaluate sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C I (i : I) p q,
    (polynomialPresence (U := U) W V C I rk rl i p q).evaluate
      sourceTable targetTable h) ∧
  (∀ (W : ArchCtx A) (V : ArchCtx B) C I (i : I) p q m,
    (polynomialCoefficient (U := U) W V C I rk rl i p q m).evaluate
      sourceTable targetTable h) ∧
  (∀ (W X : ArchCtx A) (V Y : ArchCtx B) C D (d : D) p q,
    (imagePresence (U := U) W X V Y C D rk rl d p q).evaluate
      sourceTable targetTable h) ∧
  (∀ (W X : ArchCtx A) (V Y : ArchCtx B) C D (d : D) p q m,
    (imageCoefficient (U := U) W X V Y C D rk rl d p q m).evaluate
      sourceTable targetTable h)

/-- The representative raw laws are exactly the closed finite instance families
above on the independently flattened endpoint tables. -/
theorem pointLaws_iff_instances (s t : ObjectData.{u, v} U)
    (rk rl : CoefficientRef.{v}) (h : Table.{u, v} U .representative) :
    RepresentativeRaw.PointLaws s.2.2.2.val t.2.2.2.val t.1.val.2.1.val rk rl h ↔
      Instances
        (A := IndependentCoreTableAssembly.generatedObject s.1.val.1)
        (B := IndependentCoreTableAssembly.generatedObject t.1.val.1)
        (IndependentGeometryPrimitive.flatten s)
        (IndependentGeometryPrimitive.flatten t) h rk rl := by
  constructor
  · intro hp
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro W V C
      simp only [coordinate, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hctx hs
      have hs' : IndependentRawCandidate.coord s.2.2.2.val W = C :=
        congrArg ULift.down (Option.some.inj hs)
      apply congrArg some
      apply ULift.ext
      exact (hp.coordinate W V hctx).symm.trans hs'
    · intro W V I
      simp only [relation, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hctx hs
      have hs' : IndependentRawCandidate.rel s.2.2.2.val W = I :=
        congrArg ULift.down (Option.some.inj hs)
      apply congrArg some
      apply ULift.ext
      exact (hp.relation W V hctx).symm.trans hs'
    · intro W V C c value
      simp only [label, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hctx hs
      have hs' : (s.2.2.2.val (.label W C c)).down = value :=
        congrArg ULift.down (Option.some.inj hs)
      apply congrArg some
      apply ULift.ext
      exact (hp.label W V C c hctx).symm.trans hs'
    · intro W V C c value
      simp only [localData, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      intro hctx hs
      have hs' : (s.2.2.2.val (.localData W C c)).down = value :=
        congrArg ULift.down (Option.some.inj hs)
      apply congrArg some
      apply ULift.ext
      exact (hp.localData W V C c hctx).symm.trans hs'
    · intro W V C I i p q
      simp only [polynomialPresence, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      rintro ⟨hctx, hs, ht⟩
      have hs' : (s.2.2.2.val (.polynomial W C I rk i)).down = p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.polynomial V C I rl i)).down = q :=
        congrArg ULift.down (Option.some.inj ht)
      exact (congrArg Option.isSome hs').symm.trans
        ((hp.polynomial W V C I i hctx).1.trans (congrArg Option.isSome ht'))
    · intro W V C I i p q m
      simp only [polynomialCoefficient, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      rintro ⟨hctx, hs, ht⟩
      have hs' : (s.2.2.2.val (.polynomial W C I rk i)).down = some p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.polynomial V C I rl i)).down = some q :=
        congrArg ULift.down (Option.some.inj ht)
      exact (hp.polynomial W V C I i hctx).2 p q hs' ht' m
    · intro W X V Y C D d p q
      simp only [imagePresence, targetReadable, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      rintro ⟨hWV, hXY, hreadable, hs, ht⟩
      have hreadable' : (t.1.val.2.1.val (.le V Y)).down :=
        (JointLawFinite.some_double_ulift_prop_true_iff _).mp hreadable
      have hs' : (s.2.2.2.val (.image W X C D rk d)).down = p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.image V Y C D rl d)).down = q :=
        congrArg ULift.down (Option.some.inj ht)
      exact (congrArg Option.isSome hs').symm.trans
        ((hp.image W X V Y C D d hWV hXY hreadable').1.trans
          (congrArg Option.isSome ht'))
    · intro W X V Y C D d p q m
      simp only [imageCoefficient, targetReadable, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent]
      rintro ⟨hWV, hXY, hreadable, hs, ht⟩
      have hreadable' : (t.1.val.2.1.val (.le V Y)).down :=
        (JointLawFinite.some_double_ulift_prop_true_iff _).mp hreadable
      have hs' : (s.2.2.2.val (.image W X C D rk d)).down = some p :=
        congrArg ULift.down (Option.some.inj hs)
      have ht' : (t.2.2.2.val (.image V Y C D rl d)).down = some q :=
        congrArg ULift.down (Option.some.inj ht)
      exact (hp.image W X V Y C D d hWV hXY hreadable').2 p q hs' ht' m
  · rintro ⟨hcoord, hrel, hlabel, hlocal, hpp, hpc, hip, hic⟩
    constructor
    · intro W V hctx
      have hf := hcoord W V (IndependentRawCandidate.coord s.2.2.2.val W)
      simp only [coordinate, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      have ht := hf hctx (congrArg some (ULift.ext _ _ rfl))
      exact (congrArg ULift.down (Option.some.inj ht)).symm
    · intro W V hctx
      have hf := hrel W V (IndependentRawCandidate.rel s.2.2.2.val W)
      simp only [relation, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      have ht := hf hctx (congrArg some (ULift.ext _ _ rfl))
      exact (congrArg ULift.down (Option.some.inj ht)).symm
    · intro W V C c hctx
      have hf := hlabel W V C c (s.2.2.2.val (.label W C c)).down
      simp only [label, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      have ht := hf hctx (congrArg some (ULift.ext _ _ rfl))
      exact (congrArg ULift.down (Option.some.inj ht)).symm
    · intro W V C c hctx
      have hf := hlocal W V C c (s.2.2.2.val (.localData W C c)).down
      simp only [localData, Formula.evaluate,
        IndependentGeometryPrimitive.flatten_at_generated,
        IndependentGeometryPrimitive.flattenDependent] at hf
      have ht := hf hctx (congrArg some (ULift.ext _ _ rfl))
      exact (congrArg ULift.down (Option.some.inj ht)).symm
    · intro W V C I i hctx
      constructor
      · have hf := hpp W V C I i
          (s.2.2.2.val (.polynomial W C I rk i)).down
          (t.2.2.2.val (.polynomial V C I rl i)).down
        simp only [polynomialPresence, Formula.evaluate,
          IndependentGeometryPrimitive.flatten_at_generated,
          IndependentGeometryPrimitive.flattenDependent] at hf
        exact hf ⟨hctx, congrArg some (ULift.ext _ _ rfl),
          congrArg some (ULift.ext _ _ rfl)⟩
      · intro p q hs ht m
        have hf := hpc W V C I i p q m
        simp only [polynomialCoefficient, Formula.evaluate,
          IndependentGeometryPrimitive.flatten_at_generated,
          IndependentGeometryPrimitive.flattenDependent] at hf
        exact hf ⟨hctx, congrArg some (ULift.ext _ _ hs),
          congrArg some (ULift.ext _ _ ht)⟩
    · intro W X V Y C D d hWV hXY hreadable
      constructor
      · have hf := hip W X V Y C D d
          (s.2.2.2.val (.image W X C D rk d)).down
          (t.2.2.2.val (.image V Y C D rl d)).down
        simp only [imagePresence, targetReadable, Formula.evaluate,
          IndependentGeometryPrimitive.flatten_at_generated,
          IndependentGeometryPrimitive.flattenDependent] at hf
        have hreadable' :=
          (JointLawFinite.some_double_ulift_prop_true_iff _).mpr hreadable
        exact hf ⟨hWV, hXY, hreadable', congrArg some (ULift.ext _ _ rfl),
          congrArg some (ULift.ext _ _ rfl)⟩
      · intro p q hs ht m
        have hf := hic W X V Y C D d p q m
        simp only [imageCoefficient, targetReadable, Formula.evaluate,
          IndependentGeometryPrimitive.flatten_at_generated,
          IndependentGeometryPrimitive.flattenDependent] at hf
        have hreadable' :=
          (JointLawFinite.some_double_ulift_prop_true_iff _).mpr hreadable
        exact hf ⟨hWV, hXY, hreadable',
          congrArg some (ULift.ext _ _ hs), congrArg some (ULift.ext _ _ ht)⟩

end Representative

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RawLawFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RawLawFinite
