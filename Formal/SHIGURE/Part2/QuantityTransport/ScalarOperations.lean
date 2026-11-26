import Formal.SHIGURE.Part2.AffineFoundations

/-!
# Natural scalar operations and regular extensions

Theorem 5.11. A scalar operation natural in the test algebra is
determined by its value at the universal tuple of indeterminates.
The extension equations can therefore be imposed directly on a
polynomial's coefficients.

## Implementation notes

A natural transformation between the tuple functor and the underlying ring
functor also presents these operations. The explicit family lets a caller
choose the test algebra and its algebra structure directly, as in the
quantification of Theorem 5.11. The universal tuple provides its polynomial
on that same interface.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

/-- A scalar operation on the given tuple of variables, natural over all coefficient algebras. -/
@[ext]
structure ScalarOperation (C : Type u) [CommRing C] (X : Type u) where
  /-- The value at a tuple in any test algebra. -/
  run {R : Type u} [CommRing R] [Algebra C R] : (X → R) → R
  /-- Algebra maps commute with the operation on all tuples. -/
  natural {R S : Type u} [CommRing R] [CommRing S] [Algebra C R] [Algebra C S]
    (f : R →ₐ[C] S) (x : X → R) : f (run x) = run (fun i => f (x i))

variable {C X : Type u} [CommRing C]

/-- Evaluation of a polynomial gives its natural scalar operation. -/
def polynomialOperation (p : MvPolynomial X C) : ScalarOperation C X where
  run x := MvPolynomial.aeval x p
  natural f x := MvPolynomial.comp_aeval_apply x f p

/-- The universal tuple gives a polynomial for every natural scalar operation. -/
def operationPolynomial (f : ScalarOperation C X) : MvPolynomial X C :=
  f.run MvPolynomial.X

/-- Natural operations of all the indicated arities are exactly the ordinary finite polynomials. -/
def polynomialOperationEquiv : MvPolynomial X C ≃ ScalarOperation C X where
  toFun := polynomialOperation
  invFun := operationPolynomial
  left_inv := MvPolynomial.aeval_X_left_apply
  right_inv f := by
    apply ScalarOperation.ext
    funext R hR hCR x
    change MvPolynomial.aeval x (f.run MvPolynomial.X) = f.run x
    simpa only [MvPolynomial.aeval_X] using f.natural (MvPolynomial.aeval x) MvPolynomial.X

variable {k D : Type u} [CommRing k] [Algebra k C]
variable (q : D → X → k) (ε : D → k)

/-- Polynomials which agree with the required native value on each given input. -/
abbrev ExtensionPolynomial :=
  {p : MvPolynomial X C // ∀ d,
    MvPolynomial.eval (fun x => algebraMap k C (q d x)) p = algebraMap k C (ε d)}

/-- Natural scalar operations which agree on the required inputs in the coefficient algebra. -/
abbrev ScalarExtension :=
  {f : ScalarOperation C X // ∀ d,
    f.run (fun x => algebraMap k C (q d x)) = algebraMap k C (ε d)}

/-- The polynomial classification of Theorem 5.11 restricted to the required native values. -/
def extensionPolynomialEquiv : ExtensionPolynomial (C := C) q ε ≃ ScalarExtension (C := C) q ε :=
  Equiv.subtypeEquiv polynomialOperationEquiv (fun _ => Iff.rfl)

variable {C' : Type u} [CommRing C'] [Algebra k C']

/-- Extending coefficients sends every prescribed value to the same prescribed value in the new algebra. -/
def mapExtensionPolynomial (f : C →ₐ[k] C') (p : ExtensionPolynomial (C := C) q ε) :
    ExtensionPolynomial (C := C') q ε :=
  ⟨MvPolynomial.map f.toRingHom p.val, fun d => by
    have h := MvPolynomial.map_eval f.toRingHom (fun x => algebraMap k C (q d x)) p.val
    rw [p.property d] at h
    change f (algebraMap k C (ε d)) =
      MvPolynomial.eval (fun x => f (algebraMap k C (q d x))) (MvPolynomial.map f.toRingHom p.val) at h
    simpa only [AlgHom.commutes] using h.symm⟩

/-- A natural operation can be evaluated on algebras over the new coefficient ring by
viewing each test algebra as an algebra over the old coefficients. -/
def ScalarOperation.changeBase (f : C →+* C') (a : ScalarOperation C X) : ScalarOperation C' X where
  run {R} _ _ x :=
    letI : Algebra C R := ((algebraMap C' R).comp f).toAlgebra
    a.run x
  natural := by
    intro R S _ _ _ _ g x
    letI : Algebra C R := ((algebraMap C' R).comp f).toAlgebra
    letI : Algebra C S := ((algebraMap C' S).comp f).toAlgebra
    let g' : R →ₐ[C] S := ⟨g.toRingHom, fun c => g.commutes (f c)⟩
    exact a.natural g' x

/-- Polynomial coefficients change by the coefficient map when the test category is restricted. -/
theorem changeBase_polynomialOperation (f : C →+* C') (p : MvPolynomial X C) :
    (polynomialOperation p).changeBase f = polynomialOperation (MvPolynomial.map f p) := by
  apply ScalarOperation.ext
  funext R _ _ x
  change MvPolynomial.eval₂ ((algebraMap C' R).comp f) x p =
    MvPolynomial.eval₂ (algebraMap C' R) x (MvPolynomial.map f p)
  exact (MvPolynomial.eval₂_map f x (algebraMap C' R) p).symm

/-- Restriction of scalars on the test algebras changes the prescribed extension accordingly. -/
def mapScalarExtension (f : C →ₐ[k] C') (a : ScalarExtension (C := C) q ε) :
    ScalarExtension (C := C') q ε :=
  ⟨a.val.changeBase f.toRingHom, by
    obtain ⟨p, rfl⟩ := (extensionPolynomialEquiv q ε).surjective a
    change ∀ d, ((polynomialOperation p.val).changeBase f.toRingHom).run
      (fun x => algebraMap k C' (q d x)) = algebraMap k C' (ε d)
    rw [changeBase_polynomialOperation]
    exact (mapExtensionPolynomial q ε f p).property⟩

end SHIGURE.Quantities
