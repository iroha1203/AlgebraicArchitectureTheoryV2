import ResearchLean.AG.UniformInvariance.ASubnerveReduction
import Formal.Util.AssertStandardAxioms

/-!
# Indicator law families for arbitrary target subsets

This module proves the third reduction conjunct in U0 of
`G-107-aat-uniform-invariance-characterization`.  Every nonempty subset `A`
of a coarse reading target is realized as the true-value fiber of a canonical
singleton Boolean law family.  The family is adequate for the coarse reading
and for every finer reading, where the latter descent is generated through the
canonical comparison factor.

No decidable-membership assumption, selected factor, adequacy certificate, or
preselected law-value label is supplied.  Classical decidability is used only
inside this semantic construction; it is not the executable presentation-level
decider required by the later U1 obligation.
-/

noncomputable section

namespace AAT.AG.ResolutionInvariance

open CanonicalResolution

universe u

variable {Source : Type u}

/-! ## The canonical singleton Boolean family -/

/-- The Boolean indicator of an arbitrary target subset. -/
noncomputable def targetSubsetIndicator {q : Reading Source}
    (A : Set q.Target) : q.Target → ULift.{u} Bool := by
  classical
  exact fun target =>
    if target ∈ A then ULift.up true else ULift.up false

/-- The singleton law family whose source evaluation is the indicator of `A`
after applying the coarse reading. -/
noncomputable def indicatorLawFamily (q : Reading Source)
    (A : Set q.Target) : FiniteLawFamily Source := by
  classical
  exact {
    Law := PUnit
    lawFintype := inferInstance
    Value := fun _ => ULift.{u} Bool
    valueDecidableEq := fun _ => inferInstance
    eval := fun _ source => targetSubsetIndicator A (q.read source)
  }

/-- Evaluation of the generated family normalizes to the target-subset
indicator after applying the coarse reading. -/
@[simp]
theorem indicatorLawFamily_eval (q : Reading Source) (A : Set q.Target)
    (law : (indicatorLawFamily q A).Law) (source : Source) :
    (indicatorLawFamily q A).eval law source =
      targetSubsetIndicator A (q.read source) := by
  rfl

/-- The indicator family is adequate for the reading from which it was
constructed. -/
theorem indicatorLawFamily_adequate (q : Reading Source)
    (A : Set q.Target) :
    (indicatorLawFamily q A).Adequate q := by
  intro law
  refine ⟨targetSubsetIndicator A, ?_⟩
  intro source
  rfl

/-- The same indicator family is adequate for every finer reading.  Its
descent is the target indicator composed with the canonical comparison
factor. -/
theorem indicatorLawFamily_adequate_of_coarserThan
    (coarseReading fineReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (A : Set coarseReading.Target) :
    (indicatorLawFamily coarseReading A).Adequate fineReading := by
  intro law
  refine ⟨fun target => targetSubsetIndicator A
    (comparisonFactor coarseReading fineReading hcoarser target), ?_⟩
  intro source
  change targetSubsetIndicator A
      (comparisonFactor coarseReading fineReading hcoarser
        (fineReading.read source)) =
    targetSubsetIndicator A (coarseReading.read source)
  rw [comparisonFactor_commutes]

/-- Both adequacy proofs are generated from the coarse reading, the subset,
and the coarse-order witness. -/
theorem indicatorLawFamily_adequate_both
    (coarseReading fineReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (A : Set coarseReading.Target) :
    (indicatorLawFamily coarseReading A).Adequate coarseReading ∧
      (indicatorLawFamily coarseReading A).Adequate fineReading :=
  ⟨indicatorLawFamily_adequate coarseReading A,
    indicatorLawFamily_adequate_of_coarserThan coarseReading fineReading
      hcoarser A⟩

/-! ## Canonical descent and the generated true label -/

/-- The canonical descent selected from coarse adequacy is extensionally the
original target indicator. -/
theorem indicatorLawFamily_lawDescend_eq (q : Reading Source)
    (A : Set q.Target) :
    lawDescend (indicatorLawFamily q A) q
        (indicatorLawFamily_adequate q A) PUnit.unit =
      targetSubsetIndicator A := by
  exact (lawDescend_unique (indicatorLawFamily q A) q
    (indicatorLawFamily_adequate q A) PUnit.unit
    (targetSubsetIndicator A) (fun _ => rfl)).symm

/-- For nonempty `A`, the true Boolean value is source-generated.  A source
witness is obtained by lifting a point of `A` through reading surjectivity. -/
noncomputable def indicatorLawFamilyTrueLabel (q : Reading Source)
    (A : Set q.Target) (hA : A.Nonempty) :
    LawValueLabel (indicatorLawFamily q A) := by
  classical
  let target := Classical.choose hA
  have htarget : target ∈ A := Classical.choose_spec hA
  let source := Classical.choose (q.surjective target)
  have hsource : q.read source = target :=
    Classical.choose_spec (q.surjective target)
  refine ⟨PUnit.unit, ULift.up true, source, ?_⟩
  change targetSubsetIndicator A (q.read source) = ULift.up true
  rw [hsource]
  simp [targetSubsetIndicator, htarget]

/-- The law projection of the generated true label normalizes to the unique
singleton law. -/
@[simp]
theorem indicatorLawFamilyTrueLabel_law (q : Reading Source)
    (A : Set q.Target) (hA : A.Nonempty) :
    (indicatorLawFamilyTrueLabel q A hA).law = PUnit.unit := by
  rfl

/-- The value projection of the generated true label normalizes to lifted
Boolean truth. -/
@[simp]
theorem indicatorLawFamilyTrueLabel_value (q : Reading Source)
    (A : Set q.Target) (hA : A.Nonempty) :
    (indicatorLawFamilyTrueLabel q A hA).value = ULift.up true := by
  rfl

/-! ## Exact realization of the coarse and fine fibers -/

/-- The canonical coarse law-value fiber of the generated true label is
exactly the originally selected subset `A`. -/
theorem indicatorLawFamily_trueFiber_eq (q : Reading Source)
    (A : Set q.Target) (hA : A.Nonempty) :
    labelValueFiber (indicatorLawFamily q A) q
        (indicatorLawFamily_adequate q A)
        (indicatorLawFamilyTrueLabel q A hA) = A := by
  ext target
  change lawDescend (indicatorLawFamily q A) q
      (indicatorLawFamily_adequate q A) PUnit.unit target = ULift.up true ↔
    target ∈ A
  rw [indicatorLawFamily_lawDescend_eq]
  unfold targetSubsetIndicator
  by_cases htarget : target ∈ A
  · rw [if_pos htarget]
    exact ⟨fun _ => htarget, fun _ => rfl⟩
  · rw [if_neg htarget]
    constructor
    · intro hequal
      have : false = true := congrArg ULift.down hequal
      exact (Bool.false_ne_true this).elim
    · intro hmem
      exact (htarget hmem).elim

/-- The fine true-label fiber is exactly the inverse image of `A` under the
canonical comparison factor. -/
theorem indicatorLawFamily_trueFineFiber_eq_preimage
    (coarseReading fineReading : Reading Source)
    (hcoarser : coarseReading.CoarserThan fineReading)
    (A : Set coarseReading.Target) (hA : A.Nonempty) :
    labelValueFiber (indicatorLawFamily coarseReading A) fineReading
        (indicatorLawFamily_adequate_of_coarserThan coarseReading fineReading
          hcoarser A)
        (indicatorLawFamilyTrueLabel coarseReading A hA) =
      comparisonFactor coarseReading fineReading hcoarser ⁻¹' A := by
  calc
    labelValueFiber (indicatorLawFamily coarseReading A) fineReading
        (indicatorLawFamily_adequate_of_coarserThan coarseReading fineReading
          hcoarser A)
        (indicatorLawFamilyTrueLabel coarseReading A hA) =
      comparisonFactor coarseReading fineReading hcoarser ⁻¹'
        labelValueFiber (indicatorLawFamily coarseReading A) coarseReading
          (indicatorLawFamily_adequate coarseReading A)
          (indicatorLawFamilyTrueLabel coarseReading A hA) :=
        labelValueFiber_eq_preimage
          (indicatorLawFamily coarseReading A) coarseReading fineReading
          (indicatorLawFamily_adequate coarseReading A)
          (indicatorLawFamily_adequate_of_coarserThan coarseReading fineReading
            hcoarser A)
          hcoarser (indicatorLawFamilyTrueLabel coarseReading A hA)
    _ = comparisonFactor coarseReading fineReading hcoarser ⁻¹' A :=
      congrArg
        (fun subset : Set coarseReading.Target =>
          comparisonFactor coarseReading fineReading hcoarser ⁻¹' subset)
        (indicatorLawFamily_trueFiber_eq coarseReading A hA)

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
