import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialPointTransport
import Formal.Util.AssertStandardAxioms

/-!
# Strict-coordinate polynomial preservation by coefficient points

Implementation notes: representative raw transport keeps coordinate names
literally equal. Each exponent therefore needs just one coefficient graph
cell. Optional responses additionally compare their presence flags, so
inactive candidate carriers are preserved without selecting fallback values.
The native ring hom appears only in the comparison theorem.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentPolynomialCoefficientPoints

noncomputable section

universe u v w

open IndependentPolynomialExpressions IndependentPolynomialPointTransport

variable {C : Type u} {k : Type v} {l : Type w}

/-- A strict-coordinate polynomial comparison reads one graph cell at each exponent. -/
def PointLaws {zk : k} {zl : l} (r : k → l → Bool) (p : Sparse C k zk) (q : Sparse C l zl) : Prop :=
  ∀ m, r (sparseCoefficient p m) (sparseCoefficient q m) = true

/-- Optional primitive responses have equal presence flags and preserve all active coefficient points. -/
def OptionalPoints {zk : k} {zl : l} (r : k → l → Bool)
    (p : Option (Sparse C k zk)) (q : Option (Sparse C l zl)) : Prop :=
  p.isSome = q.isSome ∧ ∀ x y, p = some x → q = some y → PointLaws r x y

/-- Point preservation is exactly native coefficient change with the coordinate names fixed. -/
theorem points_iff_map [CommRing k] [CommRing l] (f : k →+* l) (r : k → l → Bool)
    (hr : ∀ a b, r a b = true ↔ f a = b) (p : MvPolynomial C k) (q : MvPolynomial C l) :
    PointLaws r (sparseEquiv p) (sparseEquiv q) ↔ MvPolynomial.map f p = q := by
  constructor
  · intro hp
    ext m
    exact (MvPolynomial.coeff_map f p m).trans ((hr _ _).1 (hp m))
  · intro hp m
    apply (hr _ _).2
    change f (p.coeff m) = q.coeff m
    rw [← hp, MvPolynomial.coeff_map]

/-- The whole optional response is recovered from its presence flag and primitive coefficient points. -/
theorem optional_points_iff_map [CommRing k] [CommRing l] (f : k →+* l) (r : k → l → Bool)
    (hr : ∀ a b, r a b = true ↔ f a = b)
    (p : Option (MvPolynomial C k)) (q : Option (MvPolynomial C l)) :
    OptionalPoints r p q ↔ q = p.map (MvPolynomial.map f) := by
  constructor
  · rintro ⟨hpresence, hpoints⟩
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some y => simp at hpresence
    | some x =>
      cases q with
      | none => simp at hpresence
      | some y =>
        exact congrArg some ((points_iff_map f r hr x y).1 (hpoints x y rfl rfl)).symm
  · intro he
    subst q
    constructor
    · simp
    · intro x y hx hy
      cases hx
      have hp : MvPolynomial.map f x = y := Option.some.inj hy
      exact (points_iff_map f r hr x y).2 hp

end

end AAT.AG.LocalSemanticReconstruction.IndependentPolynomialCoefficientPoints

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentPolynomialCoefficientPoints
