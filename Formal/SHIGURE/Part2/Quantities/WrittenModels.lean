import Formal.SHIGURE.Part1.Substitution
import Formal.SHIGURE.Part2.Quantities.Representation

/-!
# Fixed models of written quantity Laws

Definition 5.1, Construction 5.2 and Lemma 5.3. A Law has two finite
expressions over its written applications. Each application names its
quantity and gives typed argument terms that must evaluate in that
quantity's domain at the specified Law inputs.

## Implementation notes

A quantity domain is a subset of its typed tuples. The argument terms
form a substitution into that context. Using the existing evaluated
substitution fixes the tag independently of the input and makes the
coordinate's argument exactly the term value. The coordinate-only
presentation is obtained by compiling the written sides.
-/

universe u

noncomputable section

namespace SHIGURE.Quantities

/-- The same written quantity applications and equations are used across the state structures. -/
structure WrittenLaws (k : Type u) (sig : Signature.{u}) where
  /-- The quantity names. -/
  Quantity : Type u
  /-- The typed context of arguments accepted by each quantity. -/
  domainContext : Quantity → List sig.SortType
  /-- The named required Laws. -/
  Law : Type u
  /-- The typed context of parameters of each Law. -/
  inputContext : Law → List sig.SortType
  /-- The names of the quantity applications occurring in each Law. -/
  Occurrence : Law → Type u
  /-- An application specifies a quantity and its tuple of typed argument terms. -/
  application (l : Law) : Occurrence l → Σ j, Substitution sig (domainContext j) (inputContext l)
  /-- The left side as a finite expression in the named applications. -/
  left (l : Law) : Expression k (Occurrence l)
  /-- The right side as a finite expression in the named applications. -/
  right (l : Law) : Expression k (Occurrence l)

namespace WrittenLaws

variable {k : Type u} {sig : Signature.{u}} (L : WrittenLaws k sig)
variable {A : Structure sig}

/-- A fixed admissible domain and fixed Law input set for a state structure. The required
applications are defined at these inputs and return arguments in the corresponding domains. -/
structure Interpretation (A : Structure sig) where
  /-- Inputs of each quantity are a subset of its typed tuples. -/
  domain (j : L.Quantity) : Set (Assignment A.carrier (L.domainContext j))
  /-- Law applicability is a subset of the typed Law context. -/
  input (l : L.Law) : Set (Assignment A.carrier (L.inputContext l))
  /-- Every named application can evaluate its tuple on every mandated input. -/
  defined (l : L.Law) (e : input l) (a : L.Occurrence l) :
    e.val ∈ (L.application l a).2.domain A
  /-- The evaluated argument is in the fixed domain of that quantity. -/
  inDomain (l : L.Law) (e : input l) (a : L.Occurrence l) :
    (L.application l a).2.value A ⟨e.val, defined l e a⟩ ∈ domain (L.application l a).1

namespace Interpretation

variable {L} (I : L.Interpretation A)

/-- Read the quantity tag and its defined tuple at a specific Law input. -/
def applicationCoordinate (l : L.Law) (e : I.input l) (a : L.Occurrence l) :
    Σ j, I.domain j :=
  ⟨(L.application l a).1,
    ⟨(L.application l a).2.value A ⟨e.val, I.defined l e a⟩, I.inDomain l e a⟩⟩

/-- Interpret the written equations in the coordinate system of a fixed structure. -/
def presentation : Presentation k A where
  Quantity := L.Quantity
  Domain := fun j => I.domain j
  Law := L.Law
  Input := fun l => I.input l
  left l e := (L.left l).rename (I.applicationCoordinate l e)
  right l e := (L.right l).rename (I.applicationCoordinate l e)

variable [CommRing k] {R : Type u} [CommRing R] [Algebra k R]

/-- Evaluate the original written expression in the fixed structure and at the supplied quantities. -/
def evaluate (l : L.Law) (e : I.input l) (term : Expression k (L.Occurrence l))
    (q : I.presentation.Candidate R) : R :=
  term.eval (fun a => q (I.applicationCoordinate l e a).1 (I.applicationCoordinate l e a).2)

/-- Lawfulness in Definition 5.1 is equality of the original written sides at every prescribed input. -/
theorem holds_iff_written (q : I.presentation.Candidate R) :
    I.presentation.Holds q ↔
      ∀ l e, I.evaluate l e (L.left l) q = I.evaluate l e (L.right l) q := by
  simp only [Presentation.Holds, presentation, evaluate, Expression.eval_rename]
  rfl

/-- Quantity assignments satisfying the original written Laws. -/
abbrev Model (R : Type u) [CommRing R] [Algebra k R] :=
  {q : I.presentation.Candidate R // ∀ l e, I.evaluate l e (L.left l) q = I.evaluate l e (L.right l) q}

/-- The coordinate presentation has exactly the models of the original written Laws. -/
def modelEquiv : I.Model R ≃ I.presentation.Model R where
  toFun q := ⟨q.val, (I.holds_iff_written q.val).mpr q.property⟩
  invFun q := ⟨q.val, (I.holds_iff_written q.val).mp q.property⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The original written Law models are represented by the named residuals' quotient algebra. -/
def modelAlgHomEquiv : I.Model R ≃ (I.presentation.LawAlgebra →ₐ[k] R) :=
  I.modelEquiv.trans I.presentation.modelAlgHomEquiv

/-- Lemma 5.3 evaluates the named universal residual using the original state terms. -/
theorem evaluate_residual (q : I.presentation.Candidate R) (l : L.Law) (e : I.input l) :
    I.presentation.evaluate q (I.presentation.residual l e) =
      I.evaluate l e (L.left l) q - I.evaluate l e (L.right l) q := by
  rw [I.presentation.evaluate_residual]
  simp only [presentation, evaluate, Expression.eval_rename]
  rfl

omit [CommRing k] in
private def substitutedArgument {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) (a : L.Occurrence l) :
    Assignment A.carrier (L.domainContext (L.application l a).1) where
  get i :=
    let t := (L.application l a).2 i
    let h := (t.mem_domain_iff A (θ.value A e)).1 (I.defined l ⟨θ.value A e, he⟩ a i)
    ((t.substitute θ).eval A e.val).get ((congrArg Part.Dom (t.eval_substitute θ A e)).mpr h)

omit [CommRing k] in
private theorem substitutedArgument_eq {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) (a : L.Occurrence l) :
    I.substitutedArgument θ e he a =
      (L.application l a).2.value A ⟨θ.value A e, I.defined l ⟨θ.value A e, he⟩ a⟩ := by
  apply Assignment.ext
  intro s i
  let t := (L.application l a).2 i
  let h := (t.mem_domain_iff A (θ.value A e)).1 (I.defined l ⟨θ.value A e, he⟩ a i)
  let y := (t.eval A (θ.value A e)).get h
  have hy : y ∈ (t.substitute θ).eval A e.val :=
    Eq.mpr (congrArg (fun p => y ∈ p) (t.eval_substitute θ A e)) (Part.get_mem h)
  exact Part.get_eq_of_mem hy _

omit [CommRing k] in
/-- Read the written application after syntactically substituting state terms into its argument.
The evaluated tuple belongs to the domain because the original Law input does. -/
def substitutedCoordinate {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) (a : L.Occurrence l) : I.presentation.Coordinate :=
  ⟨(L.application l a).1,
    ⟨I.substitutedArgument θ e he a, I.substitutedArgument_eq θ e he a ▸ I.inDomain l ⟨θ.value A e, he⟩ a⟩⟩

omit [CommRing k] in
/-- Substitution retains the named quantity and returns the same actual typed argument. -/
theorem substitutedCoordinate_eq {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) (a : L.Occurrence l) :
    I.substitutedCoordinate θ e he a = I.applicationCoordinate l ⟨θ.value A e, he⟩ a := by
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  apply Subtype.ext
  exact I.substitutedArgument_eq θ e he a

/-- The named residual itself is computed by the substituted written sides at universal quantities. -/
theorem residual_substitute {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) :
    I.presentation.residual l ⟨θ.value A e, he⟩ =
      (L.left l).eval (fun a => MvPolynomial.X (I.substitutedCoordinate θ e he a)) -
        (L.right l).eval (fun a => MvPolynomial.X (I.substitutedCoordinate θ e he a)) := by
  simp only [Presentation.residual, presentation, Expression.eval_rename,
    Presentation.universalQuantity, substitutedCoordinate_eq]
  rfl

/-- The specialization of that residual evaluates the substituted written sides in the given model. -/
theorem evaluate_residual_substitute {l : L.Law} {Δ : List sig.SortType}
    (θ : Substitution sig (L.inputContext l) Δ) (e : θ.domain A)
    (he : θ.value A e ∈ I.input l) (q : I.presentation.Candidate R) :
    I.presentation.evaluate q (I.presentation.residual l ⟨θ.value A e, he⟩) =
      (L.left l).eval (fun a => q (I.substitutedCoordinate θ e he a).1 (I.substitutedCoordinate θ e he a).2) -
        (L.right l).eval (fun a => q (I.substitutedCoordinate θ e he a).1 (I.substitutedCoordinate θ e he a).2) := by
  rw [I.evaluate_residual, funext (I.substitutedCoordinate_eq θ e he)]
  rfl

end Interpretation
end WrittenLaws
end SHIGURE.Quantities
