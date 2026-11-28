import Formal.SHIGURE.Part2.StackQuantities.ChartRankOne
import Mathlib.Tactic.FinCases

/-! # The rank-two quantity as a typed polynomial Law

The two components of a vector in `R²` are the two input positions.  The
written term applies the linear functional `q(x₀,x₁) = t₀*x₀ + t₁*x₁`, and
the primitive binary operation is multiplication in `R`.
-/

open CategoryTheory Module MvPolynomial SHIGURE.TensorRealization SHIGURE.RealizationFamilies
open SHIGURE.StackQuantities.RankOneChart
open scoped BigOperators

universe u

noncomputable section
namespace SHIGURE.StackQuantities.RankTwoChart

variable {R : Type u} [CommRing R]

/-- The first coordinate of the formal vector. -/
def firstIndex : PolynomialInputCoordinates (sig := signature.{u}) scalarRank.{u}
    [PUnit.unit, PUnit.unit] := ⟨⟨PUnit.unit, .here⟩, 0⟩

/-- The second coordinate of the same formal vector. -/
def secondIndex : PolynomialInputCoordinates (sig := signature.{u}) scalarRank.{u}
    [PUnit.unit, PUnit.unit] := ⟨⟨PUnit.unit, .there .here⟩, 0⟩

/-- The original linear quantity expressed in the two typed input positions. -/
def quantityTerm (t₀ t₁ : R) :
    PolynomialTerm R signature.{u} [PUnit.unit, PUnit.unit] PUnit.unit :=
  .add (.smul t₀ (.var .here)) (.smul t₁ (.var (.there .here)))

/-- The linear quantity on the rank-two free module. -/
def linearQuantity (t₀ t₁ : R) : (Fin 2 → R) →ₗ[R] R :=
  t₀ • (LinearMap.proj (R := R) (φ := fun _ : Fin 2 => R) 0) +
    t₁ • (LinearMap.proj (R := R) (φ := fun _ : Fin 2 => R) 1)

/-- Present a rank-two vector as the two typed scalar inputs. -/
def vectorInputs (x : Fin 2 → R) :
    ∀ i : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}),
      (scalarStructure (R := R) 1).carrier i.1
  | ⟨⟨⟩, .here⟩ => x 0
  | ⟨⟨⟩, .there .here⟩ => x 1

/-- The written term evaluates to the actual linear quantity on the vector. -/
theorem quantityTerm_eval (t₀ t₁ : R) (x : Fin 2 → R) :
    (quantityTerm t₀ t₁).eval (RingHom.id R) (scalarStructure 1) (vectorInputs x) =
      linearQuantity t₀ t₁ x := by
  simp [quantityTerm, PolynomialTerm.eval, vectorInputs, linearQuantity,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- A single vector in `R²` and the two typed input components are
canonically equivalent, with both directions on actual inputs. -/
def vectorInputsEquiv : (Fin 2 → R) ≃
    (∀ i : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}),
      (scalarStructure (R := R) 1).carrier i.1) where
  toFun := vectorInputs
  invFun x i := Fin.cases (x ⟨PUnit.unit, .here⟩)
    (fun _ => x ⟨PUnit.unit, .there .here⟩) i
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv x := by
    funext i
    rcases i with ⟨⟨⟩, _ | _ | h⟩
    · rfl
    · rfl
    · exact nomatch h

/-- The correspondence with the typed input tuple preserves addition and
scalar multiplication, so it is an isomorphism of the actual input modules. -/
def vectorInputsLinearEquiv : (Fin 2 → R) ≃ₗ[R]
    (∀ i : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}),
      (scalarStructure (R := R) 1).carrier i.1) :=
  { vectorInputsEquiv with
    map_add' := by
      intro x y
      funext i
      rcases i with ⟨⟨⟩, _ | _ | h⟩
      · rfl
      · rfl
      · exact nomatch h
    map_smul' := by
      intro a x
      funext i
      rcases i with ⟨⟨⟩, _ | _ | h⟩
      · rfl
      · rfl
      · exact nomatch h }

/-- Supply the same quantity term to both positions of multiplication. -/
def squareArguments (t₀ t₁ : R) :
    (i : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) →
      PolynomialTerm R signature.{u} [PUnit.unit, PUnit.unit] i.1
  | ⟨⟨⟩, .here⟩ => quantityTerm t₀ t₁
  | ⟨⟨⟩, .there .here⟩ => quantityTerm t₀ t₁

/-- The written equation `q(v)^2 = 0`. -/
def law (t₀ t₁ : R) :
    PolynomialLaw R signature.{u} [PUnit.unit, PUnit.unit] PUnit.unit :=
  ⟨.total PUnit.unit (squareArguments t₀ t₁),
    PolynomialTerm.zero (sig := signature.{u}) (Γ := [PUnit.unit, PUnit.unit]) PUnit.unit⟩

/-- The multiplication primitive squares a repeated scalar input. -/
private theorem product_repeated (x : R) :
    scalarProduct [PUnit.unit, PUnit.unit] (fun _ => x) = x ^ 2 := by
  classical
  letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
  have cardTwo : Fintype.card (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) = 2 :=
    twoPositions_card
  rw [scalarProduct, MultilinearMap.mkPiRing_apply]
  simp [Finset.prod_const, cardTwo, smul_eq_mul]

/-- Evaluating the original written Law's left side on the two components
is the square of the actual linear quantity on the single vector. -/
theorem law_left_eval (t₀ t₁ : R) (x : Fin 2 → R) :
    (law t₀ t₁).left.eval (RingHom.id R) (scalarStructure 1) (vectorInputs x) =
      (linearQuantity t₀ t₁ x) ^ 2 := by
  change scalarProduct [PUnit.unit, PUnit.unit] (fun i =>
    (squareArguments t₀ t₁ i).eval (RingHom.id R) (scalarStructure 1) (vectorInputs x)) = _
  have args : (fun i : TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1}) =>
      (squareArguments t₀ t₁ i).eval (RingHom.id R) (scalarStructure 1) (vectorInputs x)) =
        fun _ => linearQuantity t₀ t₁ x := by
    funext i
    rcases i with ⟨⟨⟩, _ | _ | h⟩
    · exact quantityTerm_eval t₀ t₁ x
    · exact quantityTerm_eval t₀ t₁ x
    · exact nomatch h
  rw [args, product_repeated]

/-- On every actual vector, the written Law is equivalent to `q(v)^2 = 0`. -/
theorem law_eval_iff (t₀ t₁ : R) (x : Fin 2 → R) :
    (law t₀ t₁).left.eval (RingHom.id R) (scalarStructure 1) (vectorInputs x) =
      (law t₀ t₁).right.eval (RingHom.id R) (scalarStructure 1) (vectorInputs x) ↔
        (linearQuantity t₀ t₁ x) ^ 2 = 0 := by
  rw [law_left_eval]
  rfl

/-- The actual chart residual of the typed equation at the universal vector. -/
theorem chartResidual_eq (t₀ t₁ : R) :
    (law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
        (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit) 0 =
      (C t₀ * X firstIndex.{u} + C t₁ * X secondIndex.{u}) ^ 2 := by
  classical
  have reduction :
      (law t₀ t₁).chartResidual (rank := scalarRank.{u})
          (RingHom.id R) (scalarStructure 1) (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit) =
        (law t₀ t₁).residual (rank := scalarRank.{u})
          (RingHom.id R) (scalarStructure 1) (by
            intro s
            change Basis (Fin (scalarRank s)) R ((scalarStructure (R := R) 1).carrier s)
            exact basisFor 1 s) := by
    apply PolynomialLaw.chartResidual_sortwise
  rw [reduction]
  letI : Fintype (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) := Fintype.ofFinite _
  have cardTwo : Fintype.card (TensorPosition ([PUnit.unit, PUnit.unit] : List PUnit.{u + 1})) = 2 :=
    twoPositions_card
  simp [PolynomialLaw.residual, law, squareArguments, quantityTerm, PolynomialTerm.expand,
    operationPolynomial, scalarStructure, scalarProduct, basisFor, scalarRank, signature, firstIndex, secondIndex,
    Basis.singleton_apply, Basis.singleton_repr, MultilinearMap.mkPiRing_apply,
    Fintype.sum_unique, Finset.prod_const, cardTwo, smul_eq_mul, prod_twoPositions, pow_two]

/-- Read each typed input coordinate as the corresponding component of `R²`. -/
def inputPosition : PolynomialInputCoordinates (sig := signature.{u}) scalarRank.{u}
    [PUnit.unit, PUnit.unit] → Fin 2 :=
  fun i => if twoPositions i.1 then 1 else 0

/-- Embed the two vector coordinates into the actual typed input-index type. -/
def inputEmbedding : Fin 2 ↪ PolynomialInputCoordinates (sig := signature.{u}) scalarRank.{u}
    [PUnit.unit, PUnit.unit] where
  toFun i := if i = 0 then firstIndex else secondIndex
  inj' := by
    intro i j h
    have back (a : Fin 2) :
        inputPosition (if a = 0 then firstIndex else secondIndex) = a := by
      fin_cases a <;> rfl
    exact (back i).symm.trans ((congrArg inputPosition h).trans (back j))

/-- The actual chart polynomial is the canonical rank-two residual with its
variables renamed to the original typed input positions. -/
theorem chartResidual_rename_forward (t₀ t₁ : R) :
    (law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
        (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit) 0 =
      MvPolynomial.rename inputEmbedding.{u} (squareZeroResidual t₀ t₁ ()) := by
  rw [chartResidual_eq]
  simp [squareZeroResidual, rankTwoInput, inputEmbedding, firstIndex, secondIndex,
    MvPolynomial.rename_C]

/-- The actual mixed monomial coefficient is `2*t₀*t₁`, including over
rings where this coefficient is zero. -/
theorem chartResidual_mixed_coefficient (t₀ t₁ : R) :
    coeff ((Finsupp.single (0 : Fin 2) 1 + Finsupp.single 1 1).mapDomain inputEmbedding.{u})
      ((law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
        (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit) 0) = 2 * t₀ * t₁ := by
  rw [chartResidual_rename_forward, MvPolynomial.coeff_rename_mapDomain _ inputEmbedding.injective]
  exact squareZeroResidual_mixed_coefficient t₀ t₁

/-- Renaming the actual chart polynomial yields the polynomial obtained by
applying the rank-two linear quantity to its universal vector. -/
theorem chartResidual_rename (t₀ t₁ : R) :
    MvPolynomial.rename inputPosition
      ((law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
        (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit) 0) =
      squareZeroResidual t₀ t₁ () := by
  rw [chartResidual_eq]
  simp [inputPosition, firstIndex, secondIndex, twoPositions, squareZeroResidual,
    rankTwoInput, MvPolynomial.rename_C]

/-- The mixed coefficient is in the ideal of all actual chart residual
coefficients.  The substitution reads both independent input positions. -/
theorem chartResidual_mixed_mem (t₀ t₁ : R) :
    2 * t₀ * t₁ ∈ polynomialResidualIdeal
      ((law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
        (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit)) := by
  let r := (law t₀ t₁).chartResidual (rank := scalarRank.{u}) (RingHom.id R) (scalarStructure (R := R) 1)
    (fun i => basisFor 1 i.1) (basisFor 1 PUnit.unit)
  have renamed : (fun j => MvPolynomial.rename inputPosition (r j)) =
      (fun _ : Fin 1 => squareZeroResidual t₀ t₁ ()) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact chartResidual_rename t₀ t₁
  have contained := polynomialResidualIdeal_reparameterize_le (MvPolynomial.rename inputPosition) r
  rw [renamed] at contained
  apply contained
  have comparison : polynomialResidualIdeal (squareZeroResidual t₀ t₁) ≤
      polynomialResidualIdeal (fun _ : Fin 1 => squareZeroResidual t₀ t₁ ()) := by
    apply (polynomialResidualIdeal_le_iff _ _).2
    intro _ m
    exact (polynomialResidualIdeal_le_iff _ _).1 le_rfl 0 m
  exact comparison (squareZeroResidual_mixed_mem t₀ t₁)

end SHIGURE.StackQuantities.RankTwoChart
end
