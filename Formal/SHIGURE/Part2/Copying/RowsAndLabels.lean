import Formal.SHIGURE.Part2.AffineFoundations
import Formal.SHIGURE.Part2.Copying.Coalgebra
import Formal.SHIGURE.Part2.Copying.ConstantScheme

/-!
# Finite rows and locally constant labels

Theorem 4.3 identifies one row of a copying morphism with a locally constant
label on an affine base. Compactness of the affine spectrum makes the range
finite, so the clopen fibres determine a finitely supported row.

## Implementation notes

Compactness supplies the finite range of each label function. The fibres give
the indexed partition for Lemma B.1. On the coefficient side `IsCopyRow` allows
arbitrary output sets, and `complete_on_support` recovers mathlib's
`CompleteOrthogonalIdempotents` on the finite support of that row.
-/

open AlgebraicGeometry TopologicalSpace
open scoped BigOperators

noncomputable section

namespace SHIGURE.Copying

universe u

variable {R : Type u} [CommRing R] {Y : Type u}

/-- The idempotent of a label fibre is the inverse of the clopen correspondence in Lemma B.1. -/
def labelIdempotent (l : LocallyConstant (Spec (CommRingCat.of R)) Y) (y : Y) :
    {e : R // IsIdempotentElem e} :=
  clopenOfIdempotent.symm ⟨{p | l p = y}, l.isLocallyConstant.isClopen_fiber y⟩

/-- Identifying the labels in Theorem 4.3 with idempotents sends each fibre to its basic open. -/
theorem mem_basicOpen_labelIdempotent (l : LocallyConstant (Spec (CommRingCat.of R)) Y)
    (y : Y) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (labelIdempotent l y).val ↔ l p = y := by
  have h := clopenOfIdempotent.apply_symm_apply
    (⟨{p | l p = y}, l.isLocallyConstant.isClopen_fiber y⟩ :
      Clopens (Spec (CommRingCat.of R)))
  have hp := SetLike.ext_iff.mp h p
  change p ∈ (clopenOfIdempotent (labelIdempotent l y) : Set (Spec (CommRingCat.of R))) ↔
    l p = y at hp
  rw [coe_clopenOfIdempotent] at hp
  exact hp

/-- Fibres outside the finite range give zero coefficients in Theorem 4.3. -/
theorem labelIdempotent_eq_zero {l : LocallyConstant (Spec (CommRingCat.of R)) Y}
    {y : Y} (h : y ∉ Set.range l) : (labelIdempotent l y).val = 0 := by
  have hz : (⟨{p | l p = y}, l.isLocallyConstant.isClopen_fiber y⟩ :
      Clopens (Spec (CommRingCat.of R))) = ⊥ := by
    apply SetLike.ext
    intro p
    change l p = y ↔ False
    exact ⟨fun hp => h ⟨p, hp⟩, False.elim⟩
  unfold labelIdempotent
  rw [hz]
  exact congrArg Subtype.val (PrimeSpectrum.isIdempotentElemEquivClopens_symm_bot (R := R))

/-- The finite range of the label supports the coefficients in Theorem 4.3. -/
def labelCoefficients (l : LocallyConstant (Spec (CommRingCat.of R)) Y) : CopyCoalgebra R Y :=
  Finsupp.onFinset l.range_finite.toFinset (fun y => (labelIdempotent l y).val)
    fun _ hn => l.range_finite.mem_toFinset.mpr (Classical.byContradiction fun h =>
      hn (labelIdempotent_eq_zero h))

/-- Simplify the coefficient belonging to a label to the idempotent of its fibre. -/
@[simp]
theorem labelCoefficients_apply (l : LocallyConstant (Spec (CommRingCat.of R)) Y) (y : Y) :
    labelCoefficients l y = (labelIdempotent l y).val :=
  rfl

/-- The clopen fibres over the finite range form the partition to which Lemma B.1 applies. -/
private theorem labelIdempotent_complete (l : LocallyConstant (Spec (CommRingCat.of R)) Y) :
    CompleteOrthogonalIdempotents (fun i : l.range_finite.toFinset => (labelIdempotent l i.val).val) := by
  classical
  let U (i : l.range_finite.toFinset) : Clopens (Spec (CommRingCat.of R)) :=
    ⟨{p | l p = i.val}, l.isLocallyConstant.isClopen_fiber i.val⟩
  have hor : Pairwise (fun i j => Disjoint (U i) (U j)) := by
    intro i j h
    rw [disjoint_iff, ← le_bot_iff]
    rintro p ⟨hp, hq⟩
    apply h
    exact Subtype.ext (hp.symm.trans hq)
  have hcov (p : PrimeSpectrum R) : ∃ i, p ∈ U i :=
    ⟨⟨l p, l.range_finite.mem_toFinset.mpr ⟨p, rfl⟩⟩, rfl⟩
  exact (clopenPartitionEquiv.symm ⟨U, hor, hcov⟩).property

/-- The coefficients of all label fibres satisfy the three equations of Theorem 4.3. -/
theorem isCopyRow_labelCoefficients (l : LocallyConstant (Spec (CommRingCat.of R)) Y) :
    IsCopyRow (labelCoefficients l) := by
  classical
  have h := labelIdempotent_complete l
  refine ⟨fun y => (labelIdempotent l y).property, fun y z hyz => ?_, ?_⟩
  · simp only [labelCoefficients_apply]
    by_cases hy : y ∈ l.range_finite.toFinset
    · by_cases hz : z ∈ l.range_finite.toFinset
      · exact h.ortho (i := ⟨y, hy⟩) (j := ⟨z, hz⟩) (fun he => hyz (congrArg Subtype.val he))
      · rw [labelIdempotent_eq_zero (fun hz' => hz (l.range_finite.mem_toFinset.mpr hz')), mul_zero]
    · rw [labelIdempotent_eq_zero (fun hy' => hy (l.range_finite.mem_toFinset.mpr hy')), zero_mul]
  · have hs : (labelCoefficients l).support ⊆ l.range_finite.toFinset := Finsupp.support_onFinset_subset
    rw [Finsupp.sum_of_support_subset _ hs _ (fun _ _ => rfl)]
    simp only [labelCoefficients_apply]
    rw [← Finset.sum_coe_sort l.range_finite.toFinset (fun y : Y => (labelIdempotent l y).val)]
    exact h.complete

/-- The nonzero coefficients of a copy row form a finite complete family on its support. -/
private theorem complete_on_support {a : CopyCoalgebra R Y} (ha : IsCopyRow a) :
    CompleteOrthogonalIdempotents (fun y : a.support => a y.val) := by
  classical
  refine ⟨⟨fun y => ha.1 y.val, fun y z h => ha.2.1 (fun e => h (Subtype.ext e))⟩, ?_⟩
  simpa only [Finset.sum_coe_sort, Finsupp.sum] using ha.2.2

/-- At each point of the affine scheme, the basic opens of a copy row give exactly one label. -/
private theorem exists_unique_row_label {a : CopyCoalgebra R Y} (ha : IsCopyRow a)
    (p : PrimeSpectrum R) : ∃! y, p ∈ PrimeSpectrum.basicOpen (a y) := by
  classical
  let e := clopenPartitionEquiv ⟨fun y : a.support => a y.val, complete_on_support ha⟩
  obtain ⟨y, hy⟩ := e.property.2 p
  have hb : p ∈ PrimeSpectrum.basicOpen (a y.val) := by
    have hs := coe_clopenPartitionEquiv
      ⟨fun y : a.support => a y.val, complete_on_support ha⟩ y
    change p ∈ (e.val y : Set (Spec (CommRingCat.of R))) at hy
    rw [hs] at hy
    exact hy
  refine ⟨y.val, hb, ?_⟩
  intro z hz
  by_contra hzy
  exact (p.isPrime.mem_or_mem_of_mul_eq_zero (ha.2.1 hzy)).elim hz hb

/-- The label of a row in Theorem 4.3. The basic opens of its coefficients are the fibres. -/
def labelOfRow (a : {a : CopyCoalgebra R Y // IsCopyRow a}) :
    LocallyConstant (Spec (CommRingCat.of R)) Y where
  toFun p := Classical.choose (exists_unique_row_label a.property p)
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.mpr fun y => by
    have h : {p | Classical.choose (exists_unique_row_label a.property p) = y} =
        (PrimeSpectrum.basicOpen (a.val y) : Set (PrimeSpectrum R)) := by
      ext p
      have hx := Classical.choose_spec (exists_unique_row_label a.property p)
      exact ⟨fun he => he ▸ hx.1, fun hp => (hx.2 y hp).symm⟩
    change IsOpen {p | Classical.choose (exists_unique_row_label a.property p) = y}
    rw [h]
    exact (PrimeSpectrum.basicOpen (a.val y)).isOpen

/-- The basic-open characterization of the label of a coefficient row in Theorem 4.3. -/
theorem labelOfRow_eq_iff (a : {a : CopyCoalgebra R Y // IsCopyRow a})
    (p : PrimeSpectrum R) (y : Y) : labelOfRow a p = y ↔ p ∈ PrimeSpectrum.basicOpen (a.val y) := by
  have h := Classical.choose_spec (exists_unique_row_label a.property p)
  exact ⟨fun he => he ▸ h.1, fun hy => (h.2 y hy).symm⟩

/-- The row and label identification in Theorem 4.3. The basic-open characterization
of each fibre proves both inverse equations. -/
def affineLabelsRowsEquiv :
    LocallyConstant (Spec (CommRingCat.of R)) Y ≃ {a : CopyCoalgebra R Y // IsCopyRow a} where
  toFun l := ⟨labelCoefficients l, isCopyRow_labelCoefficients l⟩
  invFun := labelOfRow
  left_inv l := by
    ext p
    exact (labelOfRow_eq_iff _ p (l p)).mpr ((mem_basicOpen_labelIdempotent l (l p) p).mpr rfl)
  right_inv a := by
    apply Subtype.ext
    apply Finsupp.ext
    intro y
    change (labelIdempotent (labelOfRow a) y).val = a.val y
    have h : labelIdempotent (labelOfRow a) y = ⟨a.val y, a.property.1 y⟩ := by
      apply clopenOfIdempotent.injective
      apply SetLike.ext
      intro p
      change p ∈ (clopenOfIdempotent (labelIdempotent (labelOfRow a) y) :
          Set (Spec (CommRingCat.of R))) ↔
        p ∈ (clopenOfIdempotent (⟨a.val y, a.property.1 y⟩ : {e : R // IsIdempotentElem e}) :
          Set (Spec (CommRingCat.of R)))
      rw [coe_clopenOfIdempotent, coe_clopenOfIdempotent]
      exact (mem_basicOpen_labelIdempotent (labelOfRow a) y p).trans (labelOfRow_eq_iff a p y)
    exact congrArg Subtype.val h

/-- Idempotents in Theorem 4.3 are recovered from pointwise agreement of their basic opens. -/
theorem idempotent_eq_of_basicOpen_iff {e f : R} (he : IsIdempotentElem e)
    (hf : IsIdempotentElem f)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.basicOpen e ↔ p ∈ PrimeSpectrum.basicOpen f) :
    e = f := by
  have h' : clopenOfIdempotent ⟨e, he⟩ = clopenOfIdempotent ⟨f, hf⟩ := by
    apply SetLike.ext
    intro p
    change p ∈ (clopenOfIdempotent ⟨e, he⟩ : Set (Spec (CommRingCat.of R))) ↔
      p ∈ (clopenOfIdempotent ⟨f, hf⟩ : Set (Spec (CommRingCat.of R)))
    rw [coe_clopenOfIdempotent, coe_clopenOfIdempotent]
    exact h p
  exact congrArg Subtype.val (clopenOfIdempotent.injective h')

/-- To evaluate the row-composition formula of Theorem 4.3 at a prime, only the summand
selected by the first row survives. -/
theorem mem_basicOpen_row_sum (a : {a : CopyCoalgebra R Y // IsCopyRow a})
    (b : Y → R) (p : PrimeSpectrum R) :
    p ∈ PrimeSpectrum.basicOpen (a.val.sum (fun y r => r * b y)) ↔
      p ∈ PrimeSpectrum.basicOpen (b (labelOfRow a p)) := by
  classical
  let y := labelOfRow a p
  have hy : a.val y ∉ p.asIdeal := (labelOfRow_eq_iff a p y).mp rfl
  have hys : y ∈ a.val.support :=
    Finsupp.mem_support_iff.mpr fun hz => hy (hz.symm ▸ p.asIdeal.zero_mem)
  have hrest : ∑ j ∈ a.val.support.erase y, a.val j * b j ∈ p.asIdeal := by
    apply p.asIdeal.sum_mem
    intro j hj
    have hne := (Finset.mem_erase.mp hj).1
    have hp : a.val j ∈ p.asIdeal := by
      by_contra hnot
      exact hne (((labelOfRow_eq_iff a p j).mpr hnot).symm)
    exact p.asIdeal.mul_mem_right _ hp
  change a.val.sum (fun y r => r * b y) ∉ p.asIdeal ↔ b y ∉ p.asIdeal
  rw [Finsupp.sum, ← Finset.sum_erase_add _ _ hys, p.asIdeal.add_mem_iff_right hrest,
    p.isPrime.mul_mem_iff_mem_or_mem]
  simp [hy]

end SHIGURE.Copying
