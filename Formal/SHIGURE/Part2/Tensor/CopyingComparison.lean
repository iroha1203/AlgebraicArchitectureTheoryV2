import Formal.SHIGURE.Part2.CopyingCoalgebra
import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension
import Formal.SHIGURE.Part2.Tensor.CoefficientPoints

/-!
# Comparing copying and tensor realizations

Theorem 4.9. A copying point has the finite row of orthogonal idempotents
from Theorem 4.3. Its comparison with the scalar-extended module is the
linear combination of the native states with those coefficients.

## Implementation notes

The indexed row retains the actual labels read from the relative scheme.
The product of its finite supports gives the common refinement for several
arguments. The coefficient map on the resulting tensors is the semilinear
map of Construction 4.8.

A separate computation of the clopen fibers of relative points would repeat
the classification and coefficient-change arguments of Theorem 4.3. The
label equivalence lets this construction reuse those arguments. The product
of the supports keeps a coefficient for each input tuple until the operation
merges equal outputs. An output-indexed refinement would need those merges
during the construction of the tuple itself.
-/

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped BigOperators TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

open Copying

variable {k R S M N : Type u} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S]
variable [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The linear combination of native points on a formal coefficient row. -/
def compareCoefficients : CopyCoalgebra R M →ₗ[R] R ⊗[k] M :=
  Finsupp.linearCombination R (fun m => (1 : R) ⊗ₜ[k] m)

/-- Equation (4.4), written with the coefficient on the left of the tensor. -/
theorem compareCoefficients_apply (a : CopyCoalgebra R M) :
    compareCoefficients (k := k) a = a.sum (fun m r => r ⊗ₜ[k] m) := by
  simp [compareCoefficients, Finsupp.linearCombination_apply, TensorProduct.smul_tmul']

/-- The point of a constant state scheme is read using Theorem 4.3 with one source state. -/
def compareCopyingPoint (p : CopyScheme R PUnit ⟶ CopyScheme R M) : R ⊗[k] M :=
  compareCoefficients (((schemeRowsEquiv PUnit M) p).val PUnit.unit)

/-- A constant row goes to the unit tensor of its native state. -/
@[simp]
theorem compareCoefficients_stateBasis (m : M) :
    compareCoefficients (k := k) (stateBasis R M m) = (1 : R) ⊗ₜ[k] m := by
  simp [compareCoefficients]

/-- The comparison takes a constant scheme point to the unit tensor of its native state. -/
@[simp]
theorem compareCopyingPoint_constant (m : M) :
    compareCopyingPoint (k := k)
      (mapStateSchemes (Spec (CommRingCat.of R)) (fun _ : PUnit => m)) = (1 : R) ⊗ₜ[k] m := by
  rw [compareCopyingPoint, ← copyingHomEquiv_mapStates, schemeRowsEquiv_copyingHomEquiv,
    coalgebraRowsEquiv_apply, mapStates_stateBasis, compareCoefficients_stateBasis]

/-- Arbitrary coefficient homomorphisms commute with the finite sum (4.4). -/
theorem compareCoefficients_map (f : R →ₐ[k] S) (a : CopyCoalgebra R M) :
    compareCoefficients (k := k) (mapRowCoefficients f.toRingHom a) =
      mapCoefficients f (compareCoefficients (k := k) a) := by
  rw [compareCoefficients_apply, compareCoefficients_apply, map_finsuppSum]
  unfold mapRowCoefficients
  rw [Finsupp.sum_mapRange_index (fun m => zero_tmul S m)]
  exact congrArg (fun evaluate => a.sum evaluate)
    (funext fun m => funext fun r => (mapCoefficients_tmul f r m).symm)

/-- Theorem 4.9 is natural in the affine coefficient algebra on copying points. -/
theorem compareCopyingPoint_changeBase (f : R →ₐ[k] S)
    (p : CopyScheme R PUnit ⟶ CopyScheme R M) :
    compareCopyingPoint (k := k) (changeConstantMapBase (Spec.map (CommRingCat.ofHom f.toRingHom)) p) =
      mapCoefficients f (compareCopyingPoint (k := k) p) := by
  rw [compareCopyingPoint, schemeRowsEquiv_changeBase]
  exact compareCoefficients_map f _

/-- Relative points of the native constant scheme use the same labels as points over the
affine coefficient spectrum. The single source state identifies that spectrum. -/
def relativeCopyingPointEquiv (f : k →+* R) (X : Type u) :
    (Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ CopyScheme k X) ≃
      (CopyScheme R PUnit ⟶ CopyScheme R X) :=
  (constantPointLabelsEquiv (Over.mk (Spec.map (CommRingCat.ofHom f))) X).trans
    ((constantPointLabelsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of R)))) X).symm.trans
      ((Equiv.funUnique PUnit _).symm.trans (constantMapsPointsEquiv (Spec (CommRingCat.of R)) PUnit X).symm))

/-- Equation (4.4) on the relative `R`-points of the constant native scheme over `k`. -/
def compareRelativeCopyingPoint
    (p : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k R))) ⟶ CopyScheme k M) : R ⊗[k] M :=
  compareCopyingPoint (relativeCopyingPointEquiv (algebraMap k R) M p)

/-- Equation (4.4) computes the relative comparison by summing the actual row of the point. -/
theorem compareRelativeCopyingPoint_apply (p : specOver (k := k) R ⟶ CopyScheme k M) :
    compareRelativeCopyingPoint p =
      (((schemeRowsEquiv PUnit M) (relativeCopyingPointEquiv (algebraMap k R) M p)).val PUnit.unit).sum
        (fun m r => r ⊗ₜ[k] m) :=
  compareCoefficients_apply _

/-- The scalar case of (4.4) uses the canonical identification of the scalar tensor with `R`. -/
def compareScalarPoint (p : CopyScheme R PUnit ⟶ CopyScheme R k) : R :=
  extendScalarSort R (compareCopyingPoint p)

/-- The scalar comparison sends a constant scalar to its image in the coefficient algebra. -/
@[simp]
theorem compareScalarPoint_constant (a : k) :
    compareScalarPoint (mapStateSchemes (Spec (CommRingCat.of R)) (fun _ : PUnit => a)) =
      algebraMap k R a := by
  rw [compareScalarPoint, compareCopyingPoint_constant, extendScalarSort_tmul, Algebra.smul_def,
    mul_one]

/-- The scalar comparison also commutes with every coefficient homomorphism. -/
theorem compareScalarPoint_changeBase (f : R →ₐ[k] S)
    (p : CopyScheme R PUnit ⟶ CopyScheme R k) :
    compareScalarPoint (changeConstantMapBase (Spec.map (CommRingCat.ofHom f.toRingHom)) p) =
      f (compareScalarPoint p) := by
  rw [compareScalarPoint, compareCopyingPoint_changeBase, compareScalarPoint]
  exact extendScalarSort_mapCoefficients f _

/-- The scalar comparison is the idempotent-weighted sum of the native scalars. -/
theorem compareScalarPoint_sum (p : CopyScheme R PUnit ⟶ CopyScheme R k) :
    compareScalarPoint p = (((schemeRowsEquiv PUnit k) p).val PUnit.unit).sum
      (fun a r => r * algebraMap k R a) := by
  rw [compareScalarPoint, compareCopyingPoint, compareCoefficients_apply, map_finsuppSum]
  simp [extendScalarSort_tmul, Algebra.smul_def, mul_comm]

/-- Pushing the row along a native linear operation commutes with its scalar extension. -/
theorem compareCoefficients_mapStates (f : M →ₗ[k] N) (a : CopyCoalgebra R M) :
    compareCoefficients (k := k) ((mapStates R f) a) =
      f.baseChange R (compareCoefficients (k := k) a) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single m r =>
    have h : Finsupp.single m r = r • stateBasis R M m := by
      rw [stateBasis_apply, Finsupp.smul_single_one]
    rw [h, map_smul, mapStates_stateBasis, map_smul, compareCoefficients_stateBasis,
      map_smul, compareCoefficients_stateBasis, map_smul, LinearMap.baseChange_tmul]

/-- Pushing a row along a function merges the fibres of that function in the finite sum. -/
theorem compareCoefficients_mapStates_sum {X : Type u} (f : X → M) (a : CopyCoalgebra R X) :
    compareCoefficients (k := k) ((mapStates R f) a) = a.sum (fun x r => r ⊗ₜ[k] f x) := by
  rw [compareCoefficients_apply]
  change (a.mapDomain f).sum (fun m r => r ⊗ₜ[k] m) = _
  exact Finsupp.sum_mapDomain_index (h := fun m (r : R) => r ⊗ₜ[k] m)
    (fun m => zero_tmul R m) (fun m r s => add_tmul r s m)

/-- A copying point followed by the scheme map of a native function has the row
obtained by pushing its coefficients along that function. -/
theorem schemeRowsEquiv_comp_mapStates {X Y : Type u}
    (f : X → Y) (p : CopyScheme R PUnit ⟶ CopyScheme R X) :
    ((schemeRowsEquiv PUnit Y) (p ≫ mapStateSchemes (Spec (CommRingCat.of R)) f)).val PUnit.unit =
      (mapStates R f) (((schemeRowsEquiv PUnit X) p).val PUnit.unit) := by
  let g := (copyingHomEquiv PUnit X).symm p
  have hg : copyingHomEquiv PUnit X g = p := (copyingHomEquiv PUnit X).apply_symm_apply p
  rw [← hg, ← copyingHomEquiv_mapStates, ← copyingHomEquiv_comp,
    schemeRowsEquiv_copyingHomEquiv, schemeRowsEquiv_copyingHomEquiv,
    coalgebraRowsEquiv_apply, coalgebraRowsEquiv_apply]
  rfl

/-- The comparison of geometric points commutes with any native linear operation. -/
theorem compareCopyingPoint_linear (f : M →ₗ[k] N)
    (p : CopyScheme R PUnit ⟶ CopyScheme R M) :
    compareCopyingPoint (k := k) (p ≫ mapStateSchemes (Spec (CommRingCat.of R)) f) =
      f.baseChange R (compareCopyingPoint (k := k) p) := by
  simp only [compareCopyingPoint, schemeRowsEquiv_comp_mapStates, compareCoefficients_mapStates]

section Refinement

variable {I : Type u} [Fintype I] {X : I → Type u}

/-- The common refinement of finitely many copying rows. Each tuple is
weighted by the product of the coefficients of its entries. -/
def refineCopyRows (a : ∀ i, CopyCoalgebra R (X i)) : CopyCoalgebra R (∀ i, X i) := by
  classical
  refine Finsupp.onFinset (Fintype.piFinset fun i => (a i).support) (fun x => ∏ i, a i (x i)) ?_
  intro x hx
  rw [Fintype.mem_piFinset]
  intro i
  exact Finsupp.mem_support_iff.mpr fun hi => hx (Finset.prod_eq_zero (Finset.mem_univ i) hi)

/-- The coefficients of the common refinement are the indicated products. -/
@[simp]
theorem refineCopyRows_apply (a : ∀ i, CopyCoalgebra R (X i)) (x : ∀ i, X i) :
    refineCopyRows a x = ∏ i, a i (x i) := rfl

/-- A sum over the common refinement can use the full product of the given supports. -/
theorem refineCopyRows_sum {A : Type*} [AddCommMonoid A]
    (a : ∀ i, CopyCoalgebra R (X i)) (f : (∀ i, X i) → R → A) (hf : ∀ x, f x 0 = 0) :
    letI := Classical.decEq I
    (refineCopyRows a).sum f = ∑ x ∈ Fintype.piFinset (fun i => (a i).support), f x (∏ i, a i (x i)) := by
  classical
  exact (refineCopyRows a).sum_of_support_subset Finsupp.support_onFinset_subset f (fun x _ => hf x)

/-- Products of finitely many partitions of unity give another partition of unity. -/
theorem isCopyRow_refineCopyRows (a : ∀ i, CopyCoalgebra R (X i))
    (ha : ∀ i, IsCopyRow (a i)) : IsCopyRow (refineCopyRows a) := by
  classical
  refine ⟨fun x => ?_, fun x y hne => ?_, ?_⟩
  · rw [IsIdempotentElem, refineCopyRows_apply, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => (ha i).1 (x i)
  · have h : ¬ ∀ i, x i = y i := fun hi => hne (funext hi)
    obtain ⟨i, hi⟩ := not_forall.mp h
    change refineCopyRows a x * refineCopyRows a y = 0
    rw [refineCopyRows_apply, refineCopyRows_apply, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((ha i).2.1 hi)
  · rw [refineCopyRows_sum a (fun _ r => r) (fun _ => rfl), ← Finset.prod_univ_sum]
    exact (Finset.prod_congr rfl fun i _ => (ha i).2.2).trans Finset.prod_const_one

/-- In two occurrences of the same input row, unequal selected states have zero coefficient. -/
theorem refineCopyRows_repeated_zero {Y : Type u} (a : I → CopyCoalgebra R Y)
    {i j : I} (different : i ≠ j) (repeated : a i = a j) (ha : IsCopyRow (a i))
    (x : I → Y) (differentStates : x i ≠ x j) : refineCopyRows a x = 0 := by
  classical
  have hz : a i (x i) * a j (x j) = 0 := by
    rw [← repeated]
    exact ha.2.1 differentStates
  rw [refineCopyRows_apply, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨different.symm, Finset.mem_univ j⟩),
    ← mul_assoc, hz, zero_mul]

/-- At a prime, the selected tuple of a common refinement is the tuple of the selected
states. This identifies the refinement with the actual pointwise tuple of scheme labels. -/
theorem labelOfRow_refineCopyRows (a : ∀ i, CopyCoalgebra R (X i))
    (ha : ∀ i, IsCopyRow (a i)) (p : PrimeSpectrum R) :
    labelOfRow ⟨refineCopyRows a, isCopyRow_refineCopyRows a ha⟩ p =
      fun i => labelOfRow ⟨a i, ha i⟩ p := by
  classical
  apply (labelOfRow_eq_iff ⟨refineCopyRows a, isCopyRow_refineCopyRows a ha⟩ p _).mpr
  change (∏ i, a i (labelOfRow ⟨a i, ha i⟩ p)) ∉ p.asIdeal
  rw [Ideal.IsPrime.prod_mem_iff]
  rintro ⟨i, _, hi⟩
  exact (labelOfRow_eq_iff ⟨a i, ha i⟩ p _).mp rfl hi

/-- Combine the points of the constant schemes using their common row refinement. -/
def tupleCopyingPoints (p : ∀ i, CopyScheme R PUnit ⟶ CopyScheme R (X i)) :
    CopyScheme R PUnit ⟶ CopyScheme R (∀ i, X i) :=
  (schemeRowsEquiv PUnit (∀ i, X i)).symm
    ⟨fun _ => refineCopyRows (fun i => ((schemeRowsEquiv PUnit (X i)) (p i)).val PUnit.unit),
      fun _ => isCopyRow_refineCopyRows _ (fun i => ((schemeRowsEquiv PUnit (X i)) (p i)).property PUnit.unit)⟩

/-- The tuple of copying points reads the common refinement in Theorem 4.3. -/
@[simp]
theorem tupleCopyingPoints_row (p : ∀ i, CopyScheme R PUnit ⟶ CopyScheme R (X i)) :
    ((schemeRowsEquiv PUnit (∀ i, X i)) (tupleCopyingPoints p)).val PUnit.unit =
      refineCopyRows (fun i => ((schemeRowsEquiv PUnit (X i)) (p i)).val PUnit.unit) := by
  simp [tupleCopyingPoints]

/-- The scheme labels of the combined point are exactly the tuple of labels of the given points. -/
theorem tupleCopyingPoints_label (p : ∀ i, CopyScheme R PUnit ⟶ CopyScheme R (X i))
    (q : PrimeSpectrum R) : sourceLabels (tupleCopyingPoints p) PUnit.unit q =
      fun i => sourceLabels (p i) PUnit.unit q := by
  let a (i : I) := ((schemeRowsEquiv PUnit (X i)) (p i)).val PUnit.unit
  have ha (i : I) : IsCopyRow (a i) := ((schemeRowsEquiv PUnit (X i)) (p i)).property PUnit.unit
  have htuple := labelOfRow_refineCopyRows a ha q
  have hl {Y : Type u} (point : CopyScheme R PUnit ⟶ CopyScheme R Y) :
      labelOfRow ⟨((schemeRowsEquiv PUnit Y) point).val PUnit.unit,
        ((schemeRowsEquiv PUnit Y) point).property PUnit.unit⟩ q = sourceLabels point PUnit.unit q := by
    exact congrArg (fun f : LocallyConstant (Spec (CommRingCat.of R)) Y => f q)
      (affineLabelsRowsEquiv.symm_apply_apply (sourceLabels point PUnit.unit))
  rw [← hl]
  rw [← show (⟨_, _⟩ : {a : CopyCoalgebra R (∀ i, X i) // IsCopyRow a}) =
    ⟨((schemeRowsEquiv PUnit (∀ i, X i)) (tupleCopyingPoints p)).val PUnit.unit,
      ((schemeRowsEquiv PUnit (∀ i, X i)) (tupleCopyingPoints p)).property PUnit.unit⟩ from
    Subtype.ext (tupleCopyingPoints_row p).symm]
  exact htuple.trans (funext fun i => hl (p i))

/-- A copying point is determined by its state label at every prime. -/
private theorem sourceLabels_point_ext {Y : Type u} {p q : CopyScheme R PUnit ⟶ CopyScheme R Y}
    (h : ∀ z : PrimeSpectrum R, sourceLabels p PUnit.unit z = sourceLabels q PUnit.unit z) : p = q := by
  apply (constantMapsPointsEquiv (Spec (CommRingCat.of R)) PUnit Y).injective
  funext i
  cases i
  apply (constantPointLabelsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of R)))) Y).injective
  ext z
  exact h z

/-- A map of states acts on each label of the geometric copying point. -/
private theorem sourceLabels_comp_states {Y Z : Type u} (f : Y → Z)
    (p : CopyScheme R PUnit ⟶ CopyScheme R Y) (z : PrimeSpectrum R) :
    sourceLabels (p ≫ mapStateSchemes (Spec (CommRingCat.of R)) f) PUnit.unit z =
      f (sourceLabels p PUnit.unit z) := by
  change stateLabel ((mapStateSchemes (Spec (CommRingCat.of R)) f).left
    (p.left (stateInclusion (Spec (CommRingCat.of R)) PUnit PUnit.unit z))) = _
  rw [stateLabel_mapStateSchemes]
  rfl

/-- The actual state projection of a tuple of copying points recovers its specified factor. -/
@[simp]
theorem tupleCopyingPoints_projection (p : ∀ i, CopyScheme R PUnit ⟶ CopyScheme R (X i)) (i : I) :
    tupleCopyingPoints p ≫ mapStateSchemes (Spec (CommRingCat.of R)) (fun x => x i) = p i := by
  apply sourceLabels_point_ext
  intro z
  rw [sourceLabels_comp_states, tupleCopyingPoints_label]

/-- Applying a native operation to affine copying points evaluates its values on the
common label refinement, with the product coefficient for each tuple. -/
theorem compareCopyingPoint_operation_sum (f : (∀ i, X i) → M)
    (p : ∀ i, CopyScheme R PUnit ⟶ CopyScheme R (X i)) :
    letI := Classical.decEq I
    let a (i : I) := ((schemeRowsEquiv PUnit (X i)) (p i)).val PUnit.unit
    compareCopyingPoint (k := k) (tupleCopyingPoints p ≫ mapStateSchemes (Spec (CommRingCat.of R)) f) =
      ∑ x ∈ Fintype.piFinset (fun i => (a i).support), (∏ i, a i (x i)) ⊗ₜ[k] f x := by
  intro a
  simp only [compareCopyingPoint, schemeRowsEquiv_comp_mapStates, tupleCopyingPoints_row,
    compareCoefficients_mapStates_sum]
  exact refineCopyRows_sum a (fun x r => r ⊗ₜ[k] f x) (fun x => zero_tmul R (f x))

end Refinement

omit [Algebra k R] in
/-- The point comparison between two relative presentations retains each label. -/
private theorem sourceLabels_relativeCopyingPointEquiv (f : k →+* R) {Y : Type u}
    (p : Over.mk (Spec.map (CommRingCat.ofHom f)) ⟶ CopyScheme k Y) :
    sourceLabels (relativeCopyingPointEquiv f Y p) PUnit.unit = labelOfPoint p := by
  simp only [sourceLabels, relativeCopyingPointEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  let e := constantPointLabelsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of R)))) Y
  let l := labelOfPoint (T := Over.mk (Spec.map (CommRingCat.ofHom f))) p
  change e (e.symm l) = l
  exact e.apply_symm_apply _

/-- After scalar change the label at a prime is the original label at its inverse image. -/
private theorem sourceLabels_changeBase {Y : Type u} (f : R →+* S)
    (p : CopyScheme R PUnit ⟶ CopyScheme R Y) (z : PrimeSpectrum S) :
    sourceLabels (changeConstantMapBase (Spec.map (CommRingCat.ofHom f)) p) PUnit.unit z =
      sourceLabels p PUnit.unit (PrimeSpectrum.comap f z) := by
  let y := sourceLabels p PUnit.unit (PrimeSpectrum.comap f z)
  have hp : PrimeSpectrum.comap f z ∈
      PrimeSpectrum.basicOpen (((schemeRowsEquiv PUnit Y) p).val PUnit.unit y) :=
    (mem_basicOpen_labelIdempotent (sourceLabels p PUnit.unit) y (PrimeSpectrum.comap f z)).mpr rfl
  have hs : z ∈ PrimeSpectrum.basicOpen (((mapRows f ((schemeRowsEquiv PUnit Y) p)).val PUnit.unit) y) := hp
  rw [← schemeRowsEquiv_changeBase] at hs
  exact (mem_basicOpen_labelIdempotent _ y z).mp hs

/-- Construct the relative affine point whose label is the chosen native state everywhere. -/
def relativeConstantCopyingPoint (m : M) : specOver (k := k) R ⟶ CopyScheme k M :=
  let T := specOver (k := k) R
  (constantPointLabelsEquiv T M).symm (LocallyConstant.const T.left m)

/-- On the relative constant point, equation (4.4) returns the unit tensor of the native state. -/
theorem compareRelativeCopyingPoint_constant (m : M) :
    compareRelativeCopyingPoint (relativeConstantCopyingPoint (k := k) (R := R) m) = (1 : R) ⊗ₜ[k] m := by
  let T := specOver (k := k) R
  let p := relativeConstantCopyingPoint (k := k) (R := R) m
  let q := mapStateSchemes (Spec (CommRingCat.of R)) (fun _ : PUnit => m)
  have he : relativeCopyingPointEquiv (algebraMap k R) M p = q := by
    apply sourceLabels_point_ext
    intro z
    rw [sourceLabels_relativeCopyingPointEquiv]
    have hp : labelOfPoint p z = m :=
      congrArg (fun l : LocallyConstant T.left M => l z)
        ((constantPointLabelsEquiv T M).apply_symm_apply (LocallyConstant.const T.left m))
    have hq : sourceLabels q PUnit.unit z = m :=
      stateLabel_mapStateSchemes (fun _ : PUnit => m)
        (stateInclusion (Spec (CommRingCat.of R)) PUnit PUnit.unit z)
    exact hp.trans hq.symm
  change compareCopyingPoint (relativeCopyingPointEquiv (algebraMap k R) M p) = _
  rw [he]
  exact compareCopyingPoint_constant m

/-- The comparison is natural on relative affine points by precomposition with the
actual coefficient morphism of schemes. -/
theorem compareRelativeCopyingPoint_changeBase (f : R →ₐ[k] S)
    (p : specOver (k := k) R ⟶ CopyScheme k M) :
    compareRelativeCopyingPoint (specOverMap f ≫ p) =
      mapCoefficients f (compareRelativeCopyingPoint p) := by
  have he : relativeCopyingPointEquiv (algebraMap k S) M (specOverMap f ≫ p) =
      changeConstantMapBase (Spec.map (CommRingCat.ofHom f.toRingHom))
        (relativeCopyingPointEquiv (algebraMap k R) M p) := by
    apply sourceLabels_point_ext
    intro z
    rw [sourceLabels_changeBase, sourceLabels_relativeCopyingPointEquiv, sourceLabels_relativeCopyingPointEquiv]
    rfl
  rw [compareRelativeCopyingPoint, he, compareCopyingPoint_changeBase]
  rfl

/-- The scalar comparison of Theorem 4.9 on a relative affine point of the native scheme. -/
def compareRelativeScalarPoint (p : specOver (k := k) R ⟶ CopyScheme k k) : R :=
  extendScalarSort R (compareRelativeCopyingPoint p)

/-- The relative scalar comparison is the sum of the scalar images weighted by the point's row. -/
theorem compareRelativeScalarPoint_apply (p : specOver (k := k) R ⟶ CopyScheme k k) :
    compareRelativeScalarPoint p =
      (((schemeRowsEquiv PUnit k) (relativeCopyingPointEquiv (algebraMap k R) k p)).val PUnit.unit).sum
        (fun a r => r * algebraMap k R a) :=
  compareScalarPoint_sum _

/-- The relative scalar comparison takes a constant scalar to its coefficient image. -/
theorem compareRelativeScalarPoint_constant (a : k) :
    compareRelativeScalarPoint (relativeConstantCopyingPoint (k := k) (R := R) a) = algebraMap k R a := by
  rw [compareRelativeScalarPoint, compareRelativeCopyingPoint_constant, extendScalarSort_tmul,
    Algebra.smul_def, mul_one]

/-- The scalar comparison commutes with precomposing by the actual morphism of coefficient schemes. -/
theorem compareRelativeScalarPoint_changeBase (f : R →ₐ[k] S)
    (p : specOver (k := k) R ⟶ CopyScheme k k) :
    compareRelativeScalarPoint (specOverMap f ≫ p) = f (compareRelativeScalarPoint p) := by
  rw [compareRelativeScalarPoint, compareRelativeCopyingPoint_changeBase, compareRelativeScalarPoint]
  exact extendScalarSort_mapCoefficients f _

/-- Changing the affine presentation of a point commutes with the scheme map of a state function. -/
theorem relativeCopyingPointEquiv_comp_states {Y Z : Type u} (f : Y → Z)
    (p : specOver (k := k) R ⟶ CopyScheme k Y) :
    relativeCopyingPointEquiv (algebraMap k R) Z (p ≫ mapStateSchemes (Spec (CommRingCat.of k)) f) =
      relativeCopyingPointEquiv (algebraMap k R) Y p ≫ mapStateSchemes (Spec (CommRingCat.of R)) f := by
  apply sourceLabels_point_ext
  intro z
  rw [sourceLabels_relativeCopyingPointEquiv, sourceLabels_comp_states, sourceLabels_relativeCopyingPointEquiv]
  change stateLabel ((mapStateSchemes (Spec (CommRingCat.of k)) f).left (p.left z)) =
    f (stateLabel (p.left z))
  exact stateLabel_mapStateSchemes f (p.left z)

/-- A finite family of relative points gives the point of the native tuple scheme. -/
def tupleRelativeCopyingPoints {I : Type u} [Fintype I] {X : I → Type u}
    (p : ∀ i, specOver (k := k) R ⟶ CopyScheme k (X i)) : specOver (k := k) R ⟶ CopyScheme k (∀ i, X i) :=
  (relativeCopyingPointEquiv (algebraMap k R) (∀ i, X i)).symm
    (tupleCopyingPoints (fun i => relativeCopyingPointEquiv (algebraMap k R) (X i) (p i)))

/-- The chosen relative tuple point has exactly the given tuple at the coefficient scheme. -/
@[simp]
theorem relativeCopyingPointEquiv_tuple {I : Type u} [Fintype I] {X : I → Type u}
    (p : ∀ i, specOver (k := k) R ⟶ CopyScheme k (X i)) :
    relativeCopyingPointEquiv (algebraMap k R) (∀ i, X i) (tupleRelativeCopyingPoints p) =
      tupleCopyingPoints (fun i => relativeCopyingPointEquiv (algebraMap k R) (X i) (p i)) :=
  (relativeCopyingPointEquiv (algebraMap k R) (∀ i, X i)).apply_symm_apply _

/-- The native scheme projection of the relative tuple recovers the corresponding point. -/
theorem tupleRelativeCopyingPoints_projection {I : Type u} [Fintype I] {X : I → Type u}
    (p : ∀ i, specOver (k := k) R ⟶ CopyScheme k (X i)) (i : I) :
    tupleRelativeCopyingPoints p ≫ mapStateSchemes (Spec (CommRingCat.of k)) (fun x => x i) = p i := by
  apply (relativeCopyingPointEquiv (algebraMap k R) (X i)).injective
  rw [relativeCopyingPointEquiv_comp_states, relativeCopyingPointEquiv_tuple, tupleCopyingPoints_projection]

/-- The comparison on relative affine points commutes with a native linear map. -/
theorem compareRelativeCopyingPoint_linear (f : M →ₗ[k] N) (p : specOver (k := k) R ⟶ CopyScheme k M) :
    compareRelativeCopyingPoint (p ≫ mapStateSchemes (Spec (CommRingCat.of k)) f) =
      f.baseChange R (compareRelativeCopyingPoint p) := by
  rw [compareRelativeCopyingPoint, relativeCopyingPointEquiv_comp_states]
  exact compareCopyingPoint_linear f _

/-- The comparison commutes with the addition of two copying points, using
their actual statewise sum on the common refinement. -/
theorem compareCopyingPoint_add (p q : CopyScheme R PUnit ⟶ CopyScheme R M) :
    let pair (i : ULift.{u} Bool) := if i.down then q else p
    compareCopyingPoint (k := k)
      (tupleCopyingPoints pair ≫ mapStateSchemes (Spec (CommRingCat.of R))
        (fun x => x (ULift.up false) + x (ULift.up true))) =
      compareCopyingPoint (k := k) p + compareCopyingPoint (k := k) q := by
  intro pair
  change _ = compareCopyingPoint (k := k) (pair (ULift.up false)) + compareCopyingPoint (k := k) (pair (ULift.up true))
  rw [← tupleCopyingPoints_projection pair (ULift.up false), ← tupleCopyingPoints_projection pair (ULift.up true)]
  simp only [compareCopyingPoint, schemeRowsEquiv_comp_mapStates, compareCoefficients_mapStates_sum,
    Finsupp.sum, tmul_add, Finset.sum_add_distrib]

/-- Use one scalar argument and one module argument in the scalar-action test. -/
private abbrev scalarInputs (k M : Type u) (i : ULift.{u} Bool) : Type u :=
  if i.down then M else k

/-- Place the scalar and the module point in their respective typed positions. -/
private def scalarCopyingInputs (p : CopyScheme R PUnit ⟶ CopyScheme R k)
    (q : CopyScheme R PUnit ⟶ CopyScheme R M) :
    (i : ULift.{u} Bool) → CopyScheme R PUnit ⟶ CopyScheme R (scalarInputs k M i)
  | ⟨false⟩ => p
  | ⟨true⟩ => q

/-- Read a typed tuple as the pair of scalar and module arguments. -/
private def scalarInputEquiv : ((i : ULift.{u} Bool) → scalarInputs k M i) ≃ k × M where
  toFun x := (x ⟨false⟩, x ⟨true⟩)
  invFun x
    | ⟨false⟩ => x.1
    | ⟨true⟩ => x.2
  left_inv x := funext fun ⟨i⟩ => by cases i <;> rfl
  right_inv _ := rfl

/-- Statewise multiplication by a native scalar becomes scalar multiplication
by its compared value on the extended module. -/
theorem compareCopyingPoint_smul (p : CopyScheme R PUnit ⟶ CopyScheme R k)
    (q : CopyScheme R PUnit ⟶ CopyScheme R M) :
    compareCopyingPoint (k := k) (tupleCopyingPoints (scalarCopyingInputs p q) ≫
      mapStateSchemes (Spec (CommRingCat.of R))
        (fun x => (show k from x ⟨false⟩) • (show M from x ⟨true⟩))) =
      compareScalarPoint p • compareCopyingPoint (k := k) q := by
  classical
  letI : DecidableEq (ULift.{u} Bool) := Classical.decEq _
  let a := ((schemeRowsEquiv PUnit k) p).val PUnit.unit
  let b := ((schemeRowsEquiv PUnit M) q).val PUnit.unit
  rw [compareCopyingPoint_operation_sum, compareScalarPoint_sum, compareCopyingPoint, compareCoefficients_apply]
  change _ = (∑ x ∈ a.support, a x * algebraMap k R x) • ∑ y ∈ b.support, b y ⊗ₜ[k] y
  rw [Finset.sum_smul]
  simp_rw [Finset.smul_sum]
  rw [← Finset.sum_product a.support b.support
    (fun z => (a z.1 * algebraMap k R z.1) • (b z.2 ⊗ₜ[k] z.2))]
  refine Finset.sum_equiv scalarInputEquiv (fun x => ?_) (fun x _ => ?_)
  · rw [Fintype.mem_piFinset, Finset.mem_product]
    refine ⟨fun h => ⟨h ⟨false⟩, h ⟨true⟩⟩, fun h ⟨i⟩ => ?_⟩
    cases i
    · exact h.1
    · exact h.2
  · let f (i : ULift.{u} Bool) := ((schemeRowsEquiv PUnit (scalarInputs k M i))
      (scalarCopyingInputs p q i)).val PUnit.unit (x i)
    let v : k := x ⟨false⟩
    let y : M := x ⟨true⟩
    have hprod : (∏ i, f i) = f ⟨true⟩ * f ⟨false⟩ :=
      (Fintype.prod_equiv Equiv.ulift f (fun i => f ⟨i⟩) (fun _ => rfl)).trans (Fintype.prod_bool _)
    change (∏ i, f i) ⊗ₜ[k] (v • y) = (a v * algebraMap k R v) • (b y ⊗ₜ[k] y)
    rw [hprod, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def, smul_eq_mul]
    change (algebraMap k R v * (b y * a v)) ⊗ₜ[k] y = (a v * algebraMap k R v * b y) ⊗ₜ[k] y
    rw [← mul_assoc]
    exact congrArg (fun r : R => r ⊗ₜ[k] y)
      ((mul_right_comm _ _ _).trans (congrArg (· * b y) (mul_comm _ _)))

/-- The comparison commutes with arbitrary finite typed multilinear operations, including
repeated sorts and repeated occurrences of a single point among the arguments. -/
theorem compareCopyingPoint_multilinear {K : Type u} (A : K → ModuleCat.{u} k)
    {Γ : List K} {B : ModuleCat.{u} k}
    (op : MultilinearMap k (fun i : TensorPosition Γ => A i.1) B)
    (p : ∀ i : TensorPosition Γ, CopyScheme R PUnit ⟶ CopyScheme R (A i.1)) :
    letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
    compareCopyingPoint (k := k) (tupleCopyingPoints p ≫ mapStateSchemes (Spec (CommRingCat.of R)) op) =
      extendOperation k A R op (fun i => compareCopyingPoint (k := k) (p i)) := by
  classical
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  let a (i : TensorPosition Γ) := ((schemeRowsEquiv PUnit (A i.1)) (p i)).val PUnit.unit
  let x (i : TensorPosition Γ) (m : A i.1) : extendCarriers k A R i.1 := a i m ⊗ₜ[k] m
  have hx (i : TensorPosition Γ) : compareCopyingPoint (k := k) (p i) = ∑ m ∈ (a i).support, x i m :=
    compareCoefficients_apply (a i)
  rw [compareCopyingPoint_operation_sum]
  simp only [hx]
  rw [MultilinearMap.map_sum_finset]
  apply Finset.sum_congr
  · ext y
    simp only [Fintype.mem_piFinset, a]
  · intro y _
    exact (extendOperation_tprod k A R op y (fun i => a i (y i))).symm

/-- Theorem 4.9 for the native geometric operation on a tuple of relative affine points. -/
theorem compareRelativeCopyingPoint_multilinear {K : Type u} (A : K → ModuleCat.{u} k)
    {Γ : List K} {B : ModuleCat.{u} k}
    (op : MultilinearMap k (fun i : TensorPosition Γ => A i.1) B)
    (p : ∀ i : TensorPosition Γ, specOver (k := k) R ⟶ CopyScheme k (A i.1)) :
    letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
    compareRelativeCopyingPoint (tupleRelativeCopyingPoints p ≫ mapStateSchemes (Spec (CommRingCat.of k)) op) =
      extendOperation k A R op (fun i => compareRelativeCopyingPoint (p i)) := by
  letI : Fintype (TensorPosition Γ) := Fintype.ofFinite _
  rw [compareRelativeCopyingPoint, relativeCopyingPointEquiv_comp_states, relativeCopyingPointEquiv_tuple]
  exact compareCopyingPoint_multilinear A op _

/-- The comparison takes the native geometric sum of two relative points to their tensor sum. -/
theorem compareRelativeCopyingPoint_add (p q : specOver (k := k) R ⟶ CopyScheme k M) :
    let pair (i : ULift.{u} Bool) := if i.down then q else p
    compareRelativeCopyingPoint
      (tupleRelativeCopyingPoints pair ≫ mapStateSchemes (Spec (CommRingCat.of k))
        (fun x => x (ULift.up false) + x (ULift.up true))) =
      compareRelativeCopyingPoint p + compareRelativeCopyingPoint q := by
  intro pair
  rw [compareRelativeCopyingPoint, relativeCopyingPointEquiv_comp_states, relativeCopyingPointEquiv_tuple]
  let e := relativeCopyingPointEquiv (algebraMap k R) M
  have h : (fun i : ULift.{u} Bool => e (pair i)) = fun i => if i.down then e q else e p := by
    funext i
    cases hi : i.down <;> simp [pair, hi]
  rw [h]
  exact compareCopyingPoint_add (e p) (e q)

/-- The comparison takes the native scalar action on relative points to the extended scalar action. -/
theorem compareRelativeCopyingPoint_smul (p : specOver (k := k) R ⟶ CopyScheme k k)
    (q : specOver (k := k) R ⟶ CopyScheme k M) :
    let args : (i : ULift.{u} Bool) → specOver (k := k) R ⟶ CopyScheme k (scalarInputs k M i)
      | ⟨false⟩ => p
      | ⟨true⟩ => q
    compareRelativeCopyingPoint
      (tupleRelativeCopyingPoints args ≫ mapStateSchemes (Spec (CommRingCat.of k))
        (fun xs => (scalarInputEquiv xs).1 • (scalarInputEquiv xs).2)) =
      compareRelativeScalarPoint p • compareRelativeCopyingPoint q := by
  intro args
  rw [compareRelativeCopyingPoint, relativeCopyingPointEquiv_comp_states, relativeCopyingPointEquiv_tuple]
  let p' := relativeCopyingPointEquiv (algebraMap k R) k p
  let q' := relativeCopyingPointEquiv (algebraMap k R) M q
  have h : (fun i => relativeCopyingPointEquiv (algebraMap k R) (scalarInputs k M i) (args i)) =
      scalarCopyingInputs p' q' := by
    funext i
    obtain ⟨b⟩ := i
    cases b <;> rfl
  rw [h]
  exact compareCopyingPoint_smul p' q'

/-- Apply the geometric scalar action to a pair of copying points over the coefficient scheme. -/
def smulCopyingPoints (p : CopyScheme R PUnit ⟶ CopyScheme R k)
    (q : CopyScheme R PUnit ⟶ CopyScheme R M) : CopyScheme R PUnit ⟶ CopyScheme R M :=
  tupleCopyingPoints (scalarCopyingInputs p q) ≫ mapStateSchemes (Spec (CommRingCat.of R))
    (fun xs => (scalarInputEquiv xs).1 • (scalarInputEquiv xs).2)

/-- The comparison of the scalar-action point is the scalar action on the compared states. -/
theorem compareCopyingPoint_smulCopyingPoints (p : CopyScheme R PUnit ⟶ CopyScheme R k)
    (q : CopyScheme R PUnit ⟶ CopyScheme R M) :
    compareCopyingPoint (k := k) (smulCopyingPoints p q) = compareScalarPoint p • compareCopyingPoint (k := k) q :=
  compareCopyingPoint_smul p q

/-- Apply the geometric scalar action on the native schemes to two relative affine points. -/
def smulRelativeCopyingPoints (p : specOver (k := k) R ⟶ CopyScheme k k)
    (q : specOver (k := k) R ⟶ CopyScheme k M) : specOver (k := k) R ⟶ CopyScheme k M :=
  let args : (i : ULift.{u} Bool) → specOver (k := k) R ⟶ CopyScheme k (scalarInputs k M i)
    | ⟨false⟩ => p
    | ⟨true⟩ => q
  tupleRelativeCopyingPoints args ≫ mapStateSchemes (Spec (CommRingCat.of k))
    (fun xs => (scalarInputEquiv xs).1 • (scalarInputEquiv xs).2)

/-- The relative scalar-action point computes the scalar action in the tensor realization. -/
theorem compareRelativeCopyingPoint_smulRelativeCopyingPoints
    (p : specOver (k := k) R ⟶ CopyScheme k k) (q : specOver (k := k) R ⟶ CopyScheme k M) :
    compareRelativeCopyingPoint (smulRelativeCopyingPoints p q) =
      compareRelativeScalarPoint p • compareRelativeCopyingPoint q :=
  compareRelativeCopyingPoint_smul p q

end SHIGURE.TensorRealization
