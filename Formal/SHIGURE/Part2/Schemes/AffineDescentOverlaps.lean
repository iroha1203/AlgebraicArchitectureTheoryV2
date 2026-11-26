import Formal.SHIGURE.Part2.Schemes.FppfDescentData
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Affine double and triple overlaps for faithfully flat maps -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open TensorProduct

noncomputable section

universe u

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

/-- The scalar map of the singleton affine cover. -/
abbrev affineScalarMap : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The two coefficient embeddings on the affine double overlap. -/
def affineDoubleEmbedding : Fin 2 → (B →ₐ[A] B ⊗[A] B) :=
  ![Algebra.TensorProduct.includeLeft, Algebra.TensorProduct.includeRight]

/-- The three coefficient embeddings on the affine triple overlap. -/
def affineTripleEmbedding : Fin 3 → (B →ₐ[A] B ⊗[A] (B ⊗[A] B)) :=
  ![Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeLeft,
    Algebra.TensorProduct.includeRight.comp Algebra.TensorProduct.includeRight]

/-- Include the double-overlap coordinates at two of the three positions. -/
def affinePairEmbedding (i j : Fin 3) : (B ⊗[A] B) →ₐ[A] B ⊗[A] (B ⊗[A] B) :=
  Algebra.TensorProduct.lift (affineTripleEmbedding A B i) (affineTripleEmbedding A B j)
    (fun x y => mul_comm (affineTripleEmbedding A B i x) (affineTripleEmbedding A B j y))

@[simp]
theorem affinePairEmbedding_comp_left (i j : Fin 3) :
    (affinePairEmbedding A B i j).comp (affineDoubleEmbedding A B 0) = affineTripleEmbedding A B i := by
  ext x
  simp [affinePairEmbedding, affineDoubleEmbedding]

@[simp]
theorem affinePairEmbedding_comp_right (i j : Fin 3) :
    (affinePairEmbedding A B i j).comp (affineDoubleEmbedding A B 1) = affineTripleEmbedding A B j := by
  ext x
  simp [affinePairEmbedding, affineDoubleEmbedding]

/-- The two projections from the spectrum of the double tensor algebra. -/
def affineDoubleProjection (i : Fin 2) :
    Spec (CommRingCat.of (B ⊗[A] B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom)

/-- The three projections from the spectrum of the triple tensor algebra. -/
def affineTripleProjection (i : Fin 3) :
    Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B))) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (affineTripleEmbedding A B i).toRingHom)

/-- The pair projections from the triple tensor spectrum. -/
def affinePairProjection (i j : Fin 3) :
    Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B))) ⟶ Spec (CommRingCat.of (B ⊗[A] B)) :=
  Spec.map (CommRingCat.ofHom (affinePairEmbedding A B i j).toRingHom)

@[reassoc]
theorem affineDoubleProjection_base (i : Fin 2) :
    affineDoubleProjection A B i ≫ affineScalarMap A B =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  rw [affineDoubleProjection, affineScalarMap, ← Spec.map_comp]
  congr 1
  ext a
  exact (affineDoubleEmbedding A B i).commutes a

@[reassoc]
theorem affineTripleProjection_base (i : Fin 3) :
    affineTripleProjection A B i ≫ affineScalarMap A B =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B)))) := by
  rw [affineTripleProjection, affineScalarMap, ← Spec.map_comp]
  congr 1
  ext a
  exact (affineTripleEmbedding A B i).commutes a

@[reassoc]
theorem affinePairProjection_left (i j : Fin 3) :
    affinePairProjection A B i j ≫ affineDoubleProjection A B 0 = affineTripleProjection A B i := by
  rw [affinePairProjection, affineDoubleProjection, affineTripleProjection, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : B →ₐ[A] B ⊗[A] (B ⊗[A] B) => CommRingCat.ofHom (R := B) (S := B ⊗[A] (B ⊗[A] B)) f.toRingHom)
    (affinePairEmbedding_comp_left A B i j)

@[reassoc]
theorem affinePairProjection_right (i j : Fin 3) :
    affinePairProjection A B i j ≫ affineDoubleProjection A B 1 = affineTripleProjection A B j := by
  rw [affinePairProjection, affineDoubleProjection, affineTripleProjection, ← Spec.map_comp]
  congr 1
  exact congrArg (fun f : B →ₐ[A] B ⊗[A] (B ⊗[A] B) => CommRingCat.ofHom (R := B) (S := B ⊗[A] (B ⊗[A] B)) f.toRingHom)
    (affinePairEmbedding_comp_right A B i j)

/-- The affine double tensor square is the pullback of the original map. -/
theorem affineDouble_isPullback :
    IsPullback (affineDoubleProjection A B 0) (affineDoubleProjection A B 1)
      (affineScalarMap A B) (affineScalarMap A B) := by
  let iso := pullbackSpecIso (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of B)
  refine IsPullback.of_iso_pullback ?_ iso.symm ?_ ?_
  · constructor
    rw [affineDoubleProjection_base, affineDoubleProjection_base]
  · simpa only [Iso.symm_hom, affineDoubleProjection, affineDoubleEmbedding] using
      pullbackSpecIso_inv_fst (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of B)
  · simpa only [Iso.symm_hom, affineDoubleProjection, affineDoubleEmbedding] using
      pullbackSpecIso_inv_snd (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of B)

/-- The last two positions are the right tensor factor. -/
theorem affinePairEmbedding_one_two :
    affinePairEmbedding A B 1 2 =
      (Algebra.TensorProduct.includeRight : (B ⊗[A] B) →ₐ[A] B ⊗[A] (B ⊗[A] B)) := by
  apply Algebra.TensorProduct.ext'
  intro b c
  change ((1 : B) ⊗ₜ[A] (b ⊗ₜ[A] (1 : B))) *
      ((1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] c)) = (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]

/-- The tensor cube spectrum is the actual triple overlap, formed by
pulling back the original map against its geometric double overlap. -/
theorem affineTriple_isPullback :
    IsPullback (affineTripleProjection A B 0) (affinePairProjection A B 1 2)
      (affineScalarMap A B) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B)))) := by
  let iso := pullbackSpecIso (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of (B ⊗[A] B))
  refine IsPullback.of_iso_pullback ?_ iso.symm ?_ ?_
  · constructor
    rw [affineTripleProjection_base, ← affineDoubleProjection_base A B 0, ← Category.assoc,
      affinePairProjection_left, affineTripleProjection_base]
  · simpa only [Iso.symm_hom, affineTripleProjection, affineTripleEmbedding] using
      pullbackSpecIso_inv_fst (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of (B ⊗[A] B))
  · simpa only [Iso.symm_hom, affinePairProjection, affinePairEmbedding_one_two] using
      pullbackSpecIso_inv_snd (CommRingCat.of A) (CommRingCat.of B) (CommRingCat.of (B ⊗[A] B))

/-- The first two positions are the left tensor factor before applying the algebra associator. -/
theorem affinePairEmbedding_zero_one :
    affinePairEmbedding A B 0 1 =
      (Algebra.TensorProduct.assoc A A A B B B).toAlgHom.comp
        (Algebra.TensorProduct.includeLeft :
          (B ⊗[A] B) →ₐ[A] (B ⊗[A] B) ⊗[A] B) := by
  apply Algebra.TensorProduct.ext'
  intro b c
  change (b ⊗ₜ[A] (1 : B ⊗[A] B)) * ((1 : B) ⊗ₜ[A] (c ⊗ₜ[A] (1 : B))) =
    b ⊗ₜ[A] (c ⊗ₜ[A] (1 : B))
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- Exchange the last two coefficient positions of the triple tensor algebra. -/
def affineTripleSwapLastTwo : (B ⊗[A] (B ⊗[A] B)) ≃ₐ[A] (B ⊗[A] (B ⊗[A] B)) :=
  Algebra.TensorProduct.congr AlgEquiv.refl (Algebra.TensorProduct.comm A B B)

/-- The first and third positions are the first two followed by interchanging the last slots. -/
theorem affinePairEmbedding_zero_two :
    affinePairEmbedding A B 0 2 =
      (affineTripleSwapLastTwo A B).toAlgHom.comp (affinePairEmbedding A B 0 1) := by
  rw [affinePairEmbedding_zero_one A B]
  apply Algebra.TensorProduct.ext'
  intro b c
  change (b ⊗ₜ[A] (1 : B ⊗[A] B)) * ((1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] c)) =
    b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] c)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]


/-- Descent data for one actual affine morphism. -/
abbrev AffineSingletonDescentData :=
  quasiCoherentModulesPseudofunctor.DescentData (fun _ : Unit => affineScalarMap A B)

set_option maxHeartbeats 500000 in
/-- The transition on the spectrum of the double tensor algebra is the
comparison on the geometric double overlap. -/
def affineDoubleTransition (data : AffineSingletonDescentData A B) :=
  data.iso (i₁ := ()) (i₂ := ()) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))))
    (affineDoubleProjection A B 0) (affineDoubleProjection A B 1)
    (affineDoubleProjection_base A B 0) (affineDoubleProjection_base A B 1)

set_option maxHeartbeats 650000 in
/-- Pull a pair transition to the triple tensor spectrum. -/
theorem affineTripleTransition (data : AffineSingletonDescentData A B) (i j : Fin 3) :
    pullHom (affineDoubleTransition A B data).hom (affinePairProjection A B i j)
      (affineTripleProjection A B i) (affineTripleProjection A B j)
      (affinePairProjection_left A B i j) (affinePairProjection_right A B i j) =
    data.hom (i₁ := ()) (i₂ := ()) (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B)))))
      (affineTripleProjection A B i) (affineTripleProjection A B j)
      (affineTripleProjection_base A B i) (affineTripleProjection_base A B j) := by
  let p := affineDoubleProjection A B 0
  let q := affineDoubleProjection A B 1
  let r := affinePairProjection A B i j
  let x := affineTripleProjection A B i
  let y := affineTripleProjection A B j
  have over : r ≫ Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] (B ⊗[A] B)))) := calc
    _ = r ≫ (p ≫ affineScalarMap A B) := congrArg (r ≫ ·) (affineDoubleProjection_base A B 0).symm
    _ = (r ≫ p) ≫ affineScalarMap A B := (Category.assoc _ _ _).symm
    _ = x ≫ affineScalarMap A B := congrArg (· ≫ affineScalarMap A B) (affinePairProjection_left A B i j)
    _ = _ := affineTripleProjection_base A B i
  exact data.pullHom_hom r _ _ over (i₁ := ()) (i₂ := ()) p q (affineDoubleProjection_base A B 0)
    (affineDoubleProjection_base A B 1) x y
    (affinePairProjection_left A B i j) (affinePairProjection_right A B i j)

set_option maxHeartbeats 650000 in
/-- The three pair comparisons obey the actual geometric Čech cocycle on
the spectrum of the triple tensor algebra. -/
theorem affineTensorCocycle (data : AffineSingletonDescentData A B) (i j k : Fin 3) :
    pullHom (affineDoubleTransition A B data).hom (affinePairProjection A B i j)
      (affineTripleProjection A B i) (affineTripleProjection A B j)
      (affinePairProjection_left A B i j) (affinePairProjection_right A B i j) ≫
    pullHom (affineDoubleTransition A B data).hom (affinePairProjection A B j k)
      (affineTripleProjection A B j) (affineTripleProjection A B k)
      (affinePairProjection_left A B j k) (affinePairProjection_right A B j k) =
    pullHom (affineDoubleTransition A B data).hom (affinePairProjection A B i k)
      (affineTripleProjection A B i) (affineTripleProjection A B k)
      (affinePairProjection_left A B i k) (affinePairProjection_right A B i k) := by
  rw [affineTripleTransition, affineTripleTransition, affineTripleTransition]
  exact data.hom_comp (i₁ := ()) (i₂ := ()) (i₃ := ()) _ _ _ _ (affineTripleProjection_base A B i)
    (affineTripleProjection_base A B j) (affineTripleProjection_base A B k)

end

end SHIGURE.SchemeDescent
