import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Polynomial transport from coordinate and coefficient graph points

Implementation notes: raw coordinate maps are equivalences, so distinct
monomials remain distinct under renaming. Preservation can therefore compare
one coefficient point after matching the two finite exponent supports. This
avoids a second arithmetic evaluator for raw Hom preservation. Coefficient
maps remain directed and may annihilate nonzero coefficients; every monomial,
including those outside a polynomial's support, is tested.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport

noncomputable section

universe u v w z

open IndependentPolynomialExpressions

variable {C : Type u} {D : Type v} {k : Type w} {l : Type z}

/-- Read one coefficient of raw sparse data using only its declared zero. -/
def sparseCoefficient {zk : k} (p : Sparse C k zk) (m : C →₀ ℕ) : k := by
  letI : Zero k := ⟨zk⟩
  exact (show (C →₀ ℕ) →₀ k from p) m

/-- Match finite exponent supports using only coordinate graph cells and natural-number equality. -/
def MonomialMatch (q : C → D → Bool) (m : C →₀ ℕ) (n : D →₀ ℕ) : Prop :=
  (∀ c ∈ m.support, ∃ d ∈ n.support, q c d = true ∧ m c = n d) ∧
  (∀ d ∈ n.support, ∃ c ∈ m.support, q c d = true ∧ m c = n d)

/-- Polynomial preservation tests one coefficient graph point for each matching exponent pair. -/
def PointLaws {zk : k} {zl : l} (q : C → D → Bool) (r : k → l → Bool)
    (p : Sparse C k zk) (p' : Sparse D l zl) : Prop :=
  ∀ m n, MonomialMatch q m n → r (sparseCoefficient p m) (sparseCoefficient p' n) = true

/-- Exponent matching depends only on the finite Cartesian product of the two exponent supports. -/
theorem monomialMatch_iff_of_points (q q' : C → D → Bool) (m : C →₀ ℕ) (n : D →₀ ℕ)
    (hq : ∀ c ∈ m.support, ∀ d ∈ n.support, q c d = q' c d) :
    MonomialMatch q m n ↔ MonomialMatch q' m n := by
  constructor
  · rintro ⟨hm, hn⟩
    constructor
    · intro c hc
      obtain ⟨d, hd, hedge, hexp⟩ := hm c hc
      exact ⟨d, hd, (hq c hc d hd).symm.trans hedge, hexp⟩
    · intro d hd
      obtain ⟨c, hc, hedge, hexp⟩ := hn d hd
      exact ⟨c, hc, (hq c hc d hd).symm.trans hedge, hexp⟩
  · rintro ⟨hm, hn⟩
    constructor
    · intro c hc
      obtain ⟨d, hd, hedge, hexp⟩ := hm c hc
      exact ⟨d, hd, (hq c hc d hd).trans hedge, hexp⟩
    · intro d hd
      obtain ⟨c, hc, hedge, hexp⟩ := hn d hd
      exact ⟨c, hc, (hq c hc d hd).trans hedge, hexp⟩

/-- Each polynomial-law instance uses finitely many coordinate cells and one coefficient cell. -/
theorem point_instance_iff_of_cells {zk : k} {zl : l}
    (q q' : C → D → Bool) (r r' : k → l → Bool)
    (p : Sparse C k zk) (p' : Sparse D l zl) (m : C →₀ ℕ) (n : D →₀ ℕ)
    (hq : ∀ c ∈ m.support, ∀ d ∈ n.support, q c d = q' c d)
    (hr : r (sparseCoefficient p m) (sparseCoefficient p' n) = r' (sparseCoefficient p m) (sparseCoefficient p' n)) :
    (MonomialMatch q m n → r (sparseCoefficient p m) (sparseCoefficient p' n) = true) ↔
      (MonomialMatch q' m n → r' (sparseCoefficient p m) (sparseCoefficient p' n) = true) := by
  rw [monomialMatch_iff_of_points q q' m n hq, hr]

/-- Under the comparison graph, finite exponent matching is exactly native bijective renaming. -/
theorem monomialMatch_iff (e : C ≃ D) (q : C → D → Bool)
    (hq : ∀ c d, q c d = true ↔ e c = d) (m : C →₀ ℕ) (n : D →₀ ℕ) :
    MonomialMatch q m n ↔ Finsupp.equivMapDomain e m = n := by
  classical
  constructor
  · rintro ⟨hm, hn⟩
    ext d
    change m (e.symm d) = n d
    by_cases hd : n d = 0
    · rw [hd]
      by_contra hc
      obtain ⟨d', hd', he, _⟩ := hm (e.symm d) (Finsupp.mem_support_iff.mpr hc)
      have hed : d = d' := by simpa using (hq _ _).1 he
      subst d'
      exact (Finsupp.mem_support_iff.mp hd') hd
    · obtain ⟨c, _, he, hexp⟩ := hn d (Finsupp.mem_support_iff.mpr hd)
      obtain rfl := (hq c d).1 he
      simpa using hexp
  · intro he
    have values : ∀ c, m c = n (e c) := by
      intro c
      have hc := congrArg (fun a : D →₀ ℕ => a (e c)) he
      simpa using hc
    constructor
    · intro c hc
      refine ⟨e c, ?_, (hq c (e c)).2 rfl, values c⟩
      exact Finsupp.mem_support_iff.mpr (fun hz => (Finsupp.mem_support_iff.mp hc) ((values c).trans hz))
    · intro d hd
      have hv : m (e.symm d) = n d := by simpa using values (e.symm d)
      refine ⟨e.symm d, ?_, (hq _ _).2 (e.apply_symm_apply d), hv⟩
      exact Finsupp.mem_support_iff.mpr (fun hz => (Finsupp.mem_support_iff.mp hd) (hv.symm.trans hz))

/-- All primitive polynomial points are equivalent to native coefficient change followed by coordinate renaming. -/
theorem points_iff_rename_map [CommRing k] [CommRing l]
    (e : C ≃ D) (f : k →+* l) (q : C → D → Bool) (r : k → l → Bool)
    (hq : ∀ c d, q c d = true ↔ e c = d) (hr : ∀ a b, r a b = true ↔ f a = b)
    (p : MvPolynomial C k) (p' : MvPolynomial D l) :
    PointLaws q r (sparseEquiv p) (sparseEquiv p') ↔
      MvPolynomial.rename e (MvPolynomial.map f p) = p' := by
  constructor
  · intro hp
    ext n
    let m := (Finsupp.equivCongrLeft e).symm n
    have hmn : Finsupp.equivMapDomain e m = n := (Finsupp.equivCongrLeft e).apply_symm_apply n
    have hc : f (p.coeff m) = p'.coeff n :=
      (hr _ _).1 (hp m n ((monomialMatch_iff e q hq m n).2 hmn))
    have hcoeff : (MvPolynomial.rename e (MvPolynomial.map f p)).coeff n = f (p.coeff m) := by
      rw [← hmn, Finsupp.equivMapDomain_eq_mapDomain, MvPolynomial.coeff_rename_mapDomain _ e.injective,
        MvPolynomial.coeff_map]
    exact hcoeff.trans hc
  · intro hp m n hmn
    apply (hr _ _).2
    obtain rfl := (monomialMatch_iff e q hq m n).1 hmn
    change f (p.coeff m) = p'.coeff (Finsupp.equivMapDomain e m)
    rw [← hp, Finsupp.equivMapDomain_eq_mapDomain, MvPolynomial.coeff_rename_mapDomain _ e.injective,
      MvPolynomial.coeff_map]

end

end AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport
