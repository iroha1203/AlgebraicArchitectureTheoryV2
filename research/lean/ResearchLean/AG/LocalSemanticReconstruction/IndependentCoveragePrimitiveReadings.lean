import Formal.AG.Site.Coverage
import Formal.Util.AssertStandardAxioms

/-!
# The nine primitive coverage predicates

Queries retain the original predicate roles and point arguments. Equation
indices and signature axes use candidate carriers; required coordinates also
check the original equation role. Inactive candidates are uniformly false.

## Implementation notes

All nine roles are retained separately because required equation coordinates
and symbolic violation coordinates have different native domains. A single
untyped predicate or a completed requirements record would erase that domain
check. Only original role guards restrict the independently supplied predicates.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentCoveragePrimitive

universe u

open Site

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {C : ContextPreorderCategory A}

/-- Coverage query roles, declared independently of the equation and signature readings. -/
inductive Query (A : ArchitectureObject U) where
  /-- Required Atom support. -/
  | requiredSupport (a : U.Atom)
  /-- Required-role equation coordinate. -/
  | requiredEquation (I : Type u) (i : I) (a : U.Atom)
  /-- Selected symbolic violation witness. -/
  | selectedWitness (I : Type u) (i : I) (a : U.Atom)
  /-- Required signature axis. -/
  | requiredAxis (I : Type u) (i : I)
  /-- Support visibility at a context. -/
  | supportVisible (W : ArchCtx A) (a : U.Atom)
  /-- Required equation-coordinate visibility at a context. -/
  | equationVisible (W : ArchCtx A) (I : Type u) (i : I) (a : U.Atom)
  /-- Symbolic violation-witness visibility at a context. -/
  | witnessVisible (W : ArchCtx A) (I : Type u) (i : I) (a : U.Atom)
  /-- Signature-axis readability at a context. -/
  | axisReadable (W : ArchCtx A) (I : Type u) (i : I)
  /-- Visibility of one context from another. -/
  | boundaryVisible (W V : ArchCtx A)

/-- Every coverage response is one native predicate evaluation. -/
abbrev Table (A : ArchitectureObject U) := Query A → Prop

/-- The original index roles determine exactly which candidate queries are active. -/
def Active (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U) : Query A → Prop
  | .requiredEquation I i _ => ∃ h : I = E.Index, E.Required (h ▸ i)
  | .equationVisible _ I i _ => ∃ h : I = E.Index, E.Required (h ▸ i)
  | .selectedWitness I _ _ => I = E.Index
  | .witnessVisible _ I _ _ => I = E.Index
  | .requiredAxis I _ => I = S.Axis
  | .axisReadable _ I _ => I = S.Axis
  | _ => True

/-- Inactive carrier or role candidates have the unique false response. -/
def IsTyped (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U) (t : Table A) : Prop :=
  ∀ q, t q → Active E S q

/-- Assemble all nine native coverage fields from their individual point evaluations. -/
def assemble (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U) (t : Table A) :
    CoverageRequirements A E S where
  requiredSupport a := t (.requiredSupport a)
  requiredEquationCoordinate x := t (.requiredEquation E.Index x.1.val x.2)
  selectedViolationWitness x := t (.selectedWitness E.Index x.1 x.2)
  requiredAxis i := t (.requiredAxis S.Axis i)
  supportVisibleOn W a := t (.supportVisible W a)
  equationCoordinateVisibleOn W x := t (.equationVisible W E.Index x.1.val x.2)
  violationWitnessVisibleOn W x := t (.witnessVisible W E.Index x.1 x.2)
  axisReadableOn W i := t (.axisReadable W S.Axis i)
  boundaryVisibleOn W V := t (.boundaryVisible W V)

/-- Read native coverage predicates with exact role and carrier guards. -/
noncomputable def read {E : ArchitecturalEquationSystem C} {S : ArchitectureSignature U}
    (R : CoverageRequirements A E S) : Table A := by
  classical
  intro q
  cases q with
  | requiredSupport a => exact R.requiredSupport a
  | requiredEquation I i a =>
    exact if h : I = E.Index then
      if hr : (E.Required (h ▸ i)) then R.requiredEquationCoordinate (⟨h ▸ i, hr⟩, a)
      else False
    else False
  | selectedWitness I i a => exact if h : I = E.Index then R.selectedViolationWitness (h ▸ i, a) else False
  | requiredAxis I i => exact if h : I = S.Axis then R.requiredAxis (h ▸ i) else False
  | supportVisible W a => exact R.supportVisibleOn W a
  | equationVisible W I i a =>
    exact if h : I = E.Index then
      if hr : (E.Required (h ▸ i)) then R.equationCoordinateVisibleOn W (⟨h ▸ i, hr⟩, a)
      else False
    else False
  | witnessVisible W I i a => exact if h : I = E.Index then R.violationWitnessVisibleOn W (h ▸ i, a) else False
  | axisReadable W I i => exact if h : I = S.Axis then R.axisReadableOn W (h ▸ i) else False
  | boundaryVisible W V => exact R.boundaryVisibleOn W V

/-- Each native coverage predicate belongs to its original carrier and role. -/
theorem read_isTyped {E : ArchitecturalEquationSystem C} {S : ArchitectureSignature U}
    (R : CoverageRequirements A E S) : IsTyped E S (read R) := by
  classical
  intro q hq
  cases q with
  | requiredEquation I i a =>
    by_cases h : I = E.Index
    · subst I
      by_cases hr : E.Required i
      · exact ⟨rfl, hr⟩
      · simp [read, hr] at hq
    · simp [read, h] at hq
  | equationVisible W I i a =>
    by_cases h : I = E.Index
    · subst I
      by_cases hr : E.Required i
      · exact ⟨rfl, hr⟩
      · simp [read, hr] at hq
    · simp [read, h] at hq
  | selectedWitness I i a =>
    by_cases h : I = E.Index
    · exact h
    · simp [read, h] at hq
  | witnessVisible W I i a =>
    by_cases h : I = E.Index
    · exact h
    · simp [read, h] at hq
  | requiredAxis I i =>
    by_cases h : I = S.Axis
    · exact h
    · simp [read, h] at hq
  | axisReadable W I i =>
    by_cases h : I = S.Axis
    · exact h
    · simp [read, h] at hq
  | requiredSupport _ => trivial
  | supportVisible _ _ => trivial
  | boundaryVisible _ _ => trivial

/-- All nine computational fields determine native coverage requirements. -/
theorem coverage_ext {E : ArchitecturalEquationSystem C} {S : ArchitectureSignature U}
    {R T : CoverageRequirements A E S}
    (h1 : R.requiredSupport = T.requiredSupport)
    (h2 : R.requiredEquationCoordinate = T.requiredEquationCoordinate)
    (h3 : R.selectedViolationWitness = T.selectedViolationWitness)
    (h4 : R.requiredAxis = T.requiredAxis)
    (h5 : R.supportVisibleOn = T.supportVisibleOn)
    (h6 : R.equationCoordinateVisibleOn = T.equationCoordinateVisibleOn)
    (h7 : R.violationWitnessVisibleOn = T.violationWitnessVisibleOn)
    (h8 : R.axisReadableOn = T.axisReadableOn)
    (h9 : R.boundaryVisibleOn = T.boundaryVisibleOn) : R = T := by
  cases R
  cases T
  cases h1
  cases h2
  cases h3
  cases h4
  cases h5
  cases h6
  cases h7
  cases h8
  cases h9
  rfl

/-- Native coverage requirements are recovered including the required-role subtype. -/
theorem assemble_read {E : ArchitecturalEquationSystem C} {S : ArchitectureSignature U}
    (R : CoverageRequirements A E S) : assemble E S (read R) = R := by
  apply coverage_ext (R := assemble E S (read R)) (T := R)
  · rfl
  · funext ⟨⟨i, hi⟩, a⟩
    simp [assemble, read, hi]
  · funext ⟨i, a⟩
    simp [assemble, read]
  · funext i
    simp [assemble, read]
  · rfl
  · funext W ⟨⟨i, hi⟩, a⟩
    simp [assemble, read, hi]
  · funext W ⟨i, a⟩
    simp [assemble, read]
  · funext W i
    simp [assemble, read]
  · rfl

/-- Typed tables cannot assign a true response to an inactive query. -/
theorem inactive {E : ArchitecturalEquationSystem C} {S : ArchitectureSignature U}
    {t : Table A} (ht : IsTyped E S t) (q : Query A) (h : ¬ Active E S q) : ¬ t q :=
  mt (ht q) h

/-- Re-reading the assembled requirements also restores all inactive candidate queries. -/
theorem read_assemble (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U)
    (t : Table A) (ht : IsTyped E S t) : read (assemble E S t) = t := by
  classical
  funext q
  cases q with
  | requiredSupport _ => rfl
  | supportVisible _ _ => rfl
  | boundaryVisible _ _ => rfl
  | requiredEquation I i a =>
    by_cases h : I = E.Index
    · subst I
      by_cases hr : E.Required i
      · simp [read, assemble, hr]
      · have hn := inactive ht (.requiredEquation E.Index i a) (by simpa [Active] using hr)
        simp [read, hr, hn]
    · have hn := inactive ht (.requiredEquation I i a) (by simp [Active, h])
      simp [read, h, hn]
  | equationVisible W I i a =>
    by_cases h : I = E.Index
    · subst I
      by_cases hr : E.Required i
      · simp [read, assemble, hr]
      · have hn := inactive ht (.equationVisible W E.Index i a) (by simpa [Active] using hr)
        simp [read, hr, hn]
    · have hn := inactive ht (.equationVisible W I i a) (by simp [Active, h])
      simp [read, h, hn]
  | selectedWitness I i a =>
    by_cases h : I = E.Index
    · subst I
      simp [read, assemble]
    · have hn := inactive ht (.selectedWitness I i a) h
      simp [read, h, hn]
  | witnessVisible W I i a =>
    by_cases h : I = E.Index
    · subst I
      simp [read, assemble]
    · have hn := inactive ht (.witnessVisible W I i a) h
      simp [read, h, hn]
  | requiredAxis I i =>
    by_cases h : I = S.Axis
    · subst I
      simp [read, assemble]
    · have hn := inactive ht (.requiredAxis I i) h
      simp [read, h, hn]
  | axisReadable W I i =>
    by_cases h : I = S.Axis
    · subst I
      simp [read, assemble]
    · have hn := inactive ht (.axisReadable W I i) h
      simp [read, h, hn]

/-- All native requirements correspond to exactly role-correct primitive tables. -/
noncomputable def readingEquiv (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U) :
    CoverageRequirements A E S ≃ {t : Table A // IsTyped E S t} where
  toFun R := ⟨read R, read_isTyped R⟩
  invFun t := assemble E S t.val
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble E S t.val t.property)

/-- A true required-coordinate response at a nonrequired equation is rejected. -/
theorem nonrequired_rejected (E : ArchitecturalEquationSystem C) (S : ArchitectureSignature U)
    (t : Table A) (i : E.Index) (a : U.Atom) (hi : ¬ E.Required i)
    (ht : t (.requiredEquation E.Index i a)) : ¬ IsTyped E S t := by
  intro h
  obtain ⟨e, he⟩ := h (.requiredEquation E.Index i a) ht
  exact hi he

end AAT.AG.LocalSemanticReconstruction.IndependentCoveragePrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentCoveragePrimitive
