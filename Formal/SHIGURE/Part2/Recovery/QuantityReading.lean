import Formal.SHIGURE.Part2.Tensor.CopyingComparison
import Mathlib.FieldTheory.Finite.Basic

/-!
# Reading a copied quantity as a coefficient

A native value sort remains a constant scheme. Its scalar reading first
applies the native quantity and then compares the copied scalar with its
tensor realization.
-/

open AlgebraicGeometry CategoryTheory SHIGURE.Copying

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S] {X : Type u}

/-- Apply the native quantity through its actual constant-scheme morphism. -/
def readQuantityScalar (q : X → k) (a : specOver (k := k) R ⟶ CopyScheme k X) : R :=
  compareRelativeScalarPoint (a ≫ mapStateSchemes (Spec (CommRingCat.of k)) q)

/-- The scalar reading is the finite sum of the native quantity values weighted by the original row. -/
theorem readQuantityScalar_sum (q : X → k) (a : specOver (k := k) R ⟶ CopyScheme k X) :
    readQuantityScalar q a =
      (((schemeRowsEquiv PUnit X) (relativeCopyingPointEquiv (algebraMap k R) X a)).val PUnit.unit).sum
        (fun x r => r * algebraMap k R (q x)) := by
  change compareScalarPoint
    (relativeCopyingPointEquiv (algebraMap k R) k (a ≫ mapStateSchemes (Spec (CommRingCat.of k)) q)) = _
  rw [relativeCopyingPointEquiv_comp_states, compareScalarPoint, compareCopyingPoint,
    schemeRowsEquiv_comp_mapStates, compareCoefficients_mapStates_sum, map_finsuppSum]
  simp [extendScalarSort_tmul, Algebra.smul_def, mul_comm]

/-- Reading a quantity as a scalar is natural along coefficient maps. -/
theorem readQuantityScalar_changeBase (f : R →ₐ[k] S) (q : X → k)
    (a : specOver (k := k) R ⟶ CopyScheme k X) :
    readQuantityScalar q (specOverMap f ≫ a) = f (readQuantityScalar q a) := by
  simp only [readQuantityScalar, Category.assoc, compareRelativeScalarPoint_changeBase]

/-- Distinct native integer values remain distinct copied states even when
their scalar readings agree in the prime residue field. -/
theorem integerValues_distinct_scalarReadings_equal (p : ℕ) [Fact p.Prime] :
    let x := relativeConstantCopyingPoint (k := ℤ) (R := ZMod p) (0 : ℤ)
    let y := relativeConstantCopyingPoint (k := ℤ) (R := ZMod p) (p : ℤ)
    x ≠ y ∧ compareRelativeScalarPoint x = compareRelativeScalarPoint y := by
  dsimp only
  constructor
  · intro h
    let e := constantPointLabelsEquiv (specOver (k := ℤ) (ZMod p)) ℤ
    let z : PrimeSpectrum (ZMod p) := ⟨⊥, Ideal.isPrime_bot⟩
    change e.symm (LocallyConstant.const _ (0 : ℤ)) = e.symm (LocallyConstant.const _ (p : ℤ)) at h
    have he := DFunLike.congr_fun (e.symm.injective h) z
    change (0 : ℤ) = (p : ℤ) at he
    exact (Nat.ne_of_gt (Fact.out : Nat.Prime p).pos) (Int.ofNat.inj he.symm)
  · rw [compareRelativeScalarPoint_constant, compareRelativeScalarPoint_constant, map_zero, map_natCast]
    exact (ZMod.natCast_self p).symm

end SHIGURE.TensorRealization
