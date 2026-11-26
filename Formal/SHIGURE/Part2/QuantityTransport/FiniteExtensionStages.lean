import Formal.SHIGURE.Part2.QuantityTransport.ScalarOperations
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite stages of the regular extension functor

For a fixed finite set of monomials, the coefficients are coordinates
on an affine scheme. Equation (5.6) imposes one linear equation for
each native input, with the original monomials evaluated there.
-/

open AlgebraicGeometry CategoryTheory
open scoped BigOperators

universe u

noncomputable section

namespace SHIGURE.Quantities

variable {k X D : Type u} [CommRing k]
variable (q : D → X → k) (ε : D → k) (F : Finset (X →₀ ℕ))

/-- The numerical value of the monomial at a given tuple of native quantities. -/
def nativeMonomialValue (x : X → k) (m : X →₀ ℕ) : k :=
  MvPolynomial.eval x (MvPolynomial.monomial m 1)

/-- Equation (5.6) in the universal coefficient of each monomial of the finite stage. -/
def stageResidual (d : D) : MvPolynomial ↥F k :=
  (∑ m : ↥F, MvPolynomial.X m * MvPolynomial.C (nativeMonomialValue (q d) m.val)) -
    MvPolynomial.C (ε d)

/-- The ideal imposing agreement at all native inputs in this stage. -/
def stageIdeal : Ideal (MvPolynomial ↥F k) :=
  Ideal.span (Set.range (stageResidual q ε F))

/-- The coefficient algebra of one finite stage of the extension functor. -/
abbrev StageAlgebra := MvPolynomial ↥F k ⧸ stageIdeal q ε F

/-- The affine scheme associated to this finite set of monomials. -/
def extensionStage : Over (Spec (CommRingCat.of k)) := specOver (StageAlgebra q ε F)

variable {C : Type u} [CommRing C] [Algebra k C]

/-- Coefficients on the specified monomials satisfying all required equations. -/
abbrev StagePoint :=
  {b : ↥F → C // ∀ d,
    (∑ m : ↥F, b m * algebraMap k C (nativeMonomialValue (q d) m.val)) = algebraMap k C (ε d)}

/-- The universal residual has exactly the asserted linear value at any choice of coefficients. -/
theorem stageResidual_aeval (b : ↥F → C) (d : D) :
    MvPolynomial.aeval b (stageResidual q ε F d) =
      (∑ m : ↥F, b m * algebraMap k C (nativeMonomialValue (q d) m.val)) - algebraMap k C (ε d) := by
  simp only [stageResidual, map_sub, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]

/-- The assignments satisfying (5.6) are exactly the algebra maps out of the finite stage. -/
def stagePointAlgHomEquiv : StagePoint (C := C) q ε F ≃ (StageAlgebra q ε F →ₐ[k] C) where
  toFun b := Ideal.Quotient.liftₐ (stageIdeal q ε F) (MvPolynomial.aeval b.val) (by
    change stageIdeal q ε F ≤ RingHom.ker (MvPolynomial.aeval b.val).toRingHom
    rw [stageIdeal, Ideal.span_le]
    rintro a ⟨d, rfl⟩
    change MvPolynomial.aeval b.val (stageResidual q ε F d) = 0
    rw [stageResidual_aeval, b.property, sub_self])
  invFun f := ⟨fun m => f (Ideal.Quotient.mk (stageIdeal q ε F) (MvPolynomial.X m)), fun d => by
    let a := f.comp (Ideal.Quotient.mkₐ k (stageIdeal q ε F))
    have ha : a = MvPolynomial.aeval (fun m => a (MvPolynomial.X m)) := MvPolynomial.aeval_unique a
    have hzero : a (stageResidual q ε F d) = 0 := by
      change f (Ideal.Quotient.mk (stageIdeal q ε F) (stageResidual q ε F d)) = 0
      have hm : stageResidual q ε F d ∈ stageIdeal q ε F :=
        Ideal.subset_span (Set.mem_range_self d)
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hm, map_zero]
    have eval_eq := AlgHom.congr_fun ha (stageResidual q ε F d)
    rw [hzero, stageResidual_aeval] at eval_eq
    exact sub_eq_zero.mp eval_eq.symm⟩
  left_inv b := by
    apply Subtype.ext
    funext m
    exact MvPolynomial.aeval_X b.val m
  right_inv f := by
    apply AlgHom.ext
    intro s
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
    exact (AlgHom.congr_fun (MvPolynomial.aeval_unique
      (f.comp (Ideal.Quotient.mkₐ k (stageIdeal q ε F)))) a).symm

/-- The finite-stage scheme represents its solutions over the global sections of every test scheme. -/
def stagePointSchemeEquiv (T : Over (Spec (CommRingCat.of k))) :
    letI := globalSectionsAlgebra T
    StagePoint (C := Γ(T.left, ⊤)) q ε F ≃ (T ⟶ extensionStage q ε F) := by
  letI := globalSectionsAlgebra T
  exact (stagePointAlgHomEquiv q ε F).trans (specOverPointEquiv T (StageAlgebra q ε F)).symm

/-- The polynomial with the chosen stage coefficients and zero coefficients elsewhere. -/
def stagePolynomial (b : ↥F → C) : MvPolynomial X C :=
  ∑ m : ↥F, MvPolynomial.monomial m.val (b m)

open Classical in
/-- Reading a coefficient recovers the stage value on its specified monomials and zero outside. -/
theorem stagePolynomial_coeff (b : ↥F → C) (m : X →₀ ℕ) :
    (stagePolynomial F b).coeff m =
      if hm : m ∈ F then b ⟨m, hm⟩ else 0 := by
  classical
  rw [stagePolynomial, MvPolynomial.coeff_sum]
  by_cases hm : m ∈ F
  · rw [dif_pos hm, Fintype.sum_eq_single ⟨m, hm⟩]
    · simp only [MvPolynomial.coeff_monomial, if_true]
    · intro n hne
      rw [MvPolynomial.coeff_monomial, if_neg]
      exact fun he => hne (Subtype.ext he)
  · rw [dif_neg hm]
    apply Finset.sum_eq_zero
    intro n _
    rw [MvPolynomial.coeff_monomial, if_neg]
    exact fun he => hm (he ▸ n.property)

/-- Each stage polynomial is supported on the chosen monomials. -/
theorem stagePolynomial_support (b : ↥F → C) : (stagePolynomial F b).support ⊆ F := by
  classical
  intro m hm
  by_contra hout
  exact (MvPolynomial.mem_support_iff.mp hm) (by rw [stagePolynomial_coeff, dif_neg hout])

/-- A polynomial supported on the stage is recovered from its coefficients there. -/
theorem stagePolynomial_read (p : MvPolynomial X C) (hp : p.support ⊆ F) :
    stagePolynomial F (fun m => p.coeff m.val) = p := by
  classical
  ext m
  rw [stagePolynomial_coeff]
  by_cases hm : m ∈ F
  · rw [dif_pos hm]
  · rw [dif_neg hm]
    exact (MvPolynomial.notMem_support_iff.mp (fun hs => hm (hp hs))).symm

/-- Evaluating the stage polynomial at a native input gives the left side of (5.6). -/
theorem stagePolynomial_eval (b : ↥F → C) (d : D) :
    MvPolynomial.eval (fun x => algebraMap k C (q d x)) (stagePolynomial F b) =
      ∑ m : ↥F, b m * algebraMap k C (nativeMonomialValue (q d) m.val) := by
  rw [stagePolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [MvPolynomial.eval_monomial]
  congr 1
  simp only [nativeMonomialValue, MvPolynomial.eval_monomial, one_mul, Finsupp.prod, map_prod, map_pow]

/-- The finite stage classifies exactly the extending polynomials supported on its monomial set. -/
def stagePointPolynomialEquiv :
    StagePoint (C := C) q ε F ≃
      {p : ExtensionPolynomial (C := C) q ε // p.val.support ⊆ F} where
  toFun b := ⟨⟨stagePolynomial F b.val, fun d => (stagePolynomial_eval q F b.val d).trans (b.property d)⟩,
    stagePolynomial_support F b.val⟩
  invFun p := ⟨fun m => p.val.val.coeff m.val, fun d => by
    rw [← stagePolynomial_eval, stagePolynomial_read F p.val.val p.property]
    exact p.val.property d⟩
  left_inv b := by
    apply Subtype.ext
    funext m
    classical
    change (stagePolynomial F b.val).coeff m.val = b.val m
    rw [stagePolynomial_coeff, dif_pos m.property]
  right_inv p := Subtype.ext (Subtype.ext (stagePolynomial_read F p.val.val p.property))

/-- Enlarging the stage preserves the polynomial and inserts zero for each added coefficient. -/
def extendStagePoint {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') (b : StagePoint (C := C) q ε F) :
    StagePoint (C := C) q ε F' :=
  let p := stagePointPolynomialEquiv q ε F b
  (stagePointPolynomialEquiv q ε F').symm ⟨p.val, p.property.trans h⟩

open Classical in
/-- The stage inclusion acts on coefficients by extension by zero. -/
theorem extendStagePoint_coeff {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') (b : StagePoint (C := C) q ε F)
    (m : ↥F') :
    (extendStagePoint q ε F h b).val m = if hm : m.val ∈ F then b.val ⟨m.val, hm⟩ else 0 :=
  stagePolynomial_coeff F b.val m.val

/-- The universal coefficient point of a finite stage. -/
def universalStagePoint : StagePoint (C := StageAlgebra q ε F) q ε F :=
  (stagePointAlgHomEquiv q ε F).symm (AlgHom.id k (StageAlgebra q ε F))

/-- The inclusion of stages on coefficients is represented by a map of their coordinate algebras. -/
def extensionStageAlgebraMap {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') :
    StageAlgebra q ε F' →ₐ[k] StageAlgebra q ε F :=
  stagePointAlgHomEquiv q ε F' (extendStagePoint q ε F h (universalStagePoint q ε F))

open Classical in
/-- Each surviving universal coordinate maps to the matching generator, and the others map to zero. -/
theorem extensionStageAlgebraMap_generator {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') (m : ↥F') :
    extensionStageAlgebraMap q ε F h (Ideal.Quotient.mk (stageIdeal q ε F') (MvPolynomial.X m)) =
      if hm : m.val ∈ F then Ideal.Quotient.mk (stageIdeal q ε F) (MvPolynomial.X ⟨m.val, hm⟩) else 0 := by
  change MvPolynomial.aeval (extendStagePoint q ε F h (universalStagePoint q ε F)).val (MvPolynomial.X m) = _
  rw [MvPolynomial.aeval_X, extendStagePoint_coeff]
  rfl

/-- Every surviving coordinate lifts to the larger stage. -/
theorem extensionStageAlgebraMap_surjective {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') :
    Function.Surjective (extensionStageAlgebraMap q ε F h) := by
  let intoTarget : ↥F → ↥F' := fun m => ⟨m.val, h m.property⟩
  have same : ((extensionStageAlgebraMap q ε F h).comp (Ideal.Quotient.mkₐ k (stageIdeal q ε F'))).comp
      (MvPolynomial.rename intoTarget) = Ideal.Quotient.mkₐ k (stageIdeal q ε F) := by
    apply MvPolynomial.algHom_ext
    intro m
    simp only [AlgHom.comp_apply, MvPolynomial.rename_X, Ideal.Quotient.mkₐ_eq_mk]
    rw [extensionStageAlgebraMap_generator, dif_pos m.property]
  intro b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨Ideal.Quotient.mk (stageIdeal q ε F') (MvPolynomial.rename intoTarget p), AlgHom.congr_fun same p⟩

/-- The actual inclusion of the finite-stage schemes in Theorem 5.11. -/
def extensionStageMap {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') :
    extensionStage q ε F ⟶ extensionStage q ε F' :=
  specOverMap (extensionStageAlgebraMap q ε F h)

/-- Each stage inclusion is a closed immersion. -/
theorem extensionStageMap_closed {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') :
    IsClosedImmersion (extensionStageMap q ε F h).left :=
  IsClosedImmersion.spec_of_surjective _ (extensionStageAlgebraMap_surjective q ε F h)

/-- Extending a finite-stage point precomposes its algebra map with the coordinate restriction. -/
theorem stagePointAlgHomEquiv_extend {F' : Finset (X →₀ ℕ)} (h : F ⊆ F')
    (b : StagePoint (C := C) q ε F) :
    stagePointAlgHomEquiv q ε F' (extendStagePoint q ε F h b) =
      (stagePointAlgHomEquiv q ε F b).comp (extensionStageAlgebraMap q ε F h) := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro m
  change (stagePointAlgHomEquiv q ε F' (extendStagePoint q ε F h b))
      (Ideal.Quotient.mk (stageIdeal q ε F') (MvPolynomial.X m)) =
    (stagePointAlgHomEquiv q ε F b)
      (extensionStageAlgebraMap q ε F h (Ideal.Quotient.mk (stageIdeal q ε F') (MvPolynomial.X m)))
  rw [extensionStageAlgebraMap_generator]
  change MvPolynomial.aeval (extendStagePoint q ε F h b).val (MvPolynomial.X m) = _
  rw [MvPolynomial.aeval_X, extendStagePoint_coeff]
  by_cases hm : m.val ∈ F
  · rw [dif_pos hm, dif_pos hm]
    exact (MvPolynomial.aeval_X (R := k) b.val ⟨m.val, hm⟩).symm
  · rw [dif_neg hm, dif_neg hm, map_zero]

/-- The geometric stage inclusion sends every test-scheme point to its zero-extended coefficients. -/
theorem stagePointSchemeEquiv_extend (T : Over (Spec (CommRingCat.of k)))
    {F' : Finset (X →₀ ℕ)} (h : F ⊆ F') :
    letI := globalSectionsAlgebra T
    ∀ b : StagePoint (C := Γ(T.left, ⊤)) q ε F,
      stagePointSchemeEquiv q ε F' T (extendStagePoint q ε F h b) =
        stagePointSchemeEquiv q ε F T b ≫ extensionStageMap q ε F h := by
  letI := globalSectionsAlgebra T
  intro b
  apply (specOverPointEquiv T (StageAlgebra q ε F')).injective
  unfold extensionStageMap
  rw [specOverPointEquiv_postcomp]
  change (specOverPointEquiv T (StageAlgebra q ε F'))
      ((specOverPointEquiv T (StageAlgebra q ε F')).symm
        (stagePointAlgHomEquiv q ε F' (extendStagePoint q ε F h b))) =
    ((specOverPointEquiv T (StageAlgebra q ε F))
      ((specOverPointEquiv T (StageAlgebra q ε F)).symm (stagePointAlgHomEquiv q ε F b))).comp _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, stagePointAlgHomEquiv_extend]

/-- The finite-stage algebra maps compose along successive inclusions. -/
theorem extensionStageAlgebraMap_comp {F' F'' : Finset (X →₀ ℕ)}
    (h : F ⊆ F') (h' : F' ⊆ F'') :
    extensionStageAlgebraMap q ε F (h.trans h') =
      (extensionStageAlgebraMap q ε F h).comp (extensionStageAlgebraMap q ε F' h') := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro m
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, extensionStageAlgebraMap_generator]
  by_cases larger : m.val ∈ F'
  · rw [dif_pos larger, extensionStageAlgebraMap_generator]
  · rw [dif_neg larger, dif_neg (fun smaller => larger (h smaller)), map_zero]

/-- The finite-stage coordinate map of an identity inclusion is the identity. -/
theorem extensionStageAlgebraMap_id :
    extensionStageAlgebraMap q ε F (Finset.Subset.refl _) = AlgHom.id k (StageAlgebra q ε F) := by
  classical
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro m
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, extensionStageAlgebraMap_generator,
    dif_pos m.property, AlgHom.id_apply]

/-- The closed immersions of stages compose along successive inclusions. -/
theorem extensionStageMap_comp {F' F'' : Finset (X →₀ ℕ)} (h : F ⊆ F') (h' : F' ⊆ F'') :
    extensionStageMap q ε F (h.trans h') = extensionStageMap q ε F h ≫ extensionStageMap q ε F' h' := by
  apply Over.OverMorphism.ext
  simp only [extensionStageMap, specOverMap_left, Over.comp_left]
  rw [extensionStageAlgebraMap_comp q ε F h h']
  exact Spec.map_comp (CommRingCat.ofHom (extensionStageAlgebraMap q ε F' h').toRingHom)
    (CommRingCat.ofHom (extensionStageAlgebraMap q ε F h).toRingHom)

/-- The closed immersion for an identity inclusion is the identity. -/
theorem extensionStageMap_id :
    extensionStageMap q ε F (Finset.Subset.refl _) = 𝟙 (extensionStage q ε F) := by
  apply Over.OverMorphism.ext
  simp only [extensionStageMap, specOverMap_left, Over.id_left, extensionStageAlgebraMap_id]
  exact Spec.map_id _

end SHIGURE.Quantities
