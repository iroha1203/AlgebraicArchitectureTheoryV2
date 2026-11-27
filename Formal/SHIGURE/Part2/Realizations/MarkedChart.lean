import Formal.SHIGURE.Part2.Quantities.Representation
import Formal.SHIGURE.Part2.Realizations.PolynomialCoordinates
import Formal.SHIGURE.Part2.Realizations.PrimitiveCoordinates

/-! # The affine equations of a chosen marking basis -/

namespace SHIGURE.RealizationFamilies

open Module

noncomputable section

universe u

variable {R : Type u} [CommRing R]

section MarkedChart

open SHIGURE.TensorRealization MvPolynomial AlgebraicGeometry CategoryTheory

variable (sig : Signature.{u}) (rank generators : sig.SortType → ℕ)

/-- Choose the generating columns in their original order at each sort. -/
abbrev MarkedBasisChoice :=
  ∀ s : sig.SortType, Fin (rank s) ↪o Fin (generators s)

variable (choice : MarkedBasisChoice sig rank generators)

/-- A nonselected marking column has one free entry per output row. -/
abbrev MarkingCoordinate :=
  Σ s : sig.SortType, Fin (rank s) × {j : Fin (generators s) // j ∉ Set.range (choice s)}

/-- The variables of (6.2) index the primitive coefficients and the nonselected marking entries. -/
abbrev MarkedChartVariable :=
  Sum (PrimitiveCoordinate sig rank) (MarkingCoordinate sig rank generators choice)

open Classical in
/-- Form the marking matrix with the selected columns fixed to the identity. -/
def markingMatrix (values : MarkingCoordinate sig rank generators choice → R) (s : sig.SortType) :
    Matrix (Fin (rank s)) (Fin (generators s)) R :=
  fun i j => if h : j ∈ Set.range (choice s) then
    if i = Classical.choose h then 1 else 0
  else values ⟨s, i, ⟨j, h⟩⟩

/-- A selected column is the corresponding coordinate vector. -/
theorem markingMatrix_selected (values : MarkingCoordinate sig rank generators choice → R)
    (s : sig.SortType) (i j : Fin (rank s)) :
    markingMatrix sig rank generators choice values s i (choice s j) = if i = j then 1 else 0 := by
  classical
  have selected : choice s j ∈ Set.range (choice s) := ⟨j, rfl⟩
  have equal : Classical.choose selected = j := (choice s).injective (Classical.choose_spec selected)
  rw [markingMatrix, dif_pos selected, equal]

/-- A nonselected column reads the given free entries. -/
theorem markingMatrix_nonselected (values : MarkingCoordinate sig rank generators choice → R)
    (s : sig.SortType) (i : Fin (rank s)) (j : Fin (generators s))
    (h : j ∉ Set.range (choice s)) :
    markingMatrix sig rank generators choice values s i j = values ⟨s, i, ⟨j, h⟩⟩ := by
  rw [markingMatrix, dif_neg h]

/-- The marking homomorphism sends the standard generators to the matrix columns. -/
def markingMap (values : MarkingCoordinate sig rank generators choice → R) (s : sig.SortType) :
    (Fin (generators s) → R) →ₗ[R] (Fin (rank s) → R) :=
  (markingMatrix sig rank generators choice values s).mulVecLin

/-- The chosen generators give the actual coordinate basis of the target. -/
theorem markingMap_selected (values : MarkingCoordinate sig rank generators choice → R)
    (s : sig.SortType) (j : Fin (rank s)) :
    markingMap sig rank generators choice values s (Pi.single (choice s j) 1) =
      Pi.basisFun R (Fin (rank s)) j := by
  rw [markingMap, Matrix.mulVecLin_apply, Matrix.mulVec_single_one, Pi.basisFun_apply]
  funext i
  change markingMatrix sig rank generators choice values s i (choice s j) = (Pi.single j (1 : R) : Fin (rank s) → R) i
  rw [markingMatrix_selected]
  by_cases same : i = j
  · subst i
    simp only [if_true, Pi.single_eq_same]
  · simp only [if_neg same, Pi.single_eq_of_ne same]

/-- The actual marking map is surjective because the selected columns give a basis. -/
theorem markingMap_surjective (values : MarkingCoordinate sig rank generators choice → R)
    (s : sig.SortType) : Function.Surjective (markingMap sig rank generators choice values s) := by
  rw [← LinearMap.range_eq_top, ← (Pi.basisFun R (Fin (rank s))).span_eq]
  apply le_antisymm
  · rw [(Pi.basisFun R (Fin (rank s))).span_eq]
    exact le_top
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨Pi.single (choice s j) 1, markingMap_selected sig rank generators choice values s j⟩

/-- The universal primitive coefficients in the ambient ring of a marked chart. -/
def universalPrimitiveCoefficients :
    PrimitiveCoefficients sig rank (MvPolynomial (MarkedChartVariable sig rank generators choice) R) :=
  (PrimitiveCoefficients.valuesEquiv sig rank).symm (fun c => X (.inl c))

/-- The universal marking matrices in the same ambient ring. -/
def universalMarkingMatrix (s : sig.SortType) :
    Matrix (Fin (rank s)) (Fin (generators s))
      (MvPolynomial (MarkedChartVariable sig rank generators choice) R) :=
  markingMatrix sig rank generators choice (fun c => X (.inr c)) s

/-- The universal primitive structure uses the original free carrier modules. -/
def universalMarkedTensor :
    TensorStructure (MvPolynomial (MarkedChartVariable sig rank generators choice) R) sig :=
  (universalPrimitiveCoefficients sig rank generators choice).toTensor sig rank

/-- Evaluation of the ambient variables uses the designated marking and operation data. -/
def markedChartEvaluator {S : Type u} [CommRing S] [Algebra R S]
    (coefficients : PrimitiveCoefficients sig rank S) (marking : MarkingCoordinate sig rank generators choice → S) :
    MvPolynomial (MarkedChartVariable sig rank generators choice) R →ₐ[R] S :=
  aeval (Sum.elim (PrimitiveCoefficients.valuesEquiv sig rank coefficients) marking)

/-- Reading the evaluated marking recovers the input entries in the chosen chart. -/
theorem universalMarkingMatrix_eval {S : Type u} [CommRing S] [Algebra R S]
    (c : PrimitiveCoefficients sig rank S) (v : MarkingCoordinate sig rank generators choice → S)
    (s : sig.SortType) :
    (universalMarkingMatrix (R := R) sig rank generators choice s).map
        (markedChartEvaluator sig rank generators choice c v).toRingHom =
      markingMatrix sig rank generators choice v s := by
  classical
  ext i j
  rw [Matrix.map_apply]
  by_cases chosen : j ∈ Set.range (choice s)
  · obtain ⟨k, rfl⟩ := chosen
    change markedChartEvaluator sig rank generators choice c v
        (markingMatrix sig rank generators choice (fun z => X (.inr z)) s i (choice s k)) = _
    rw [markingMatrix_selected, markingMatrix_selected]
    split_ifs with eq
    · exact map_one _
    · exact map_zero _
  · change markedChartEvaluator sig rank generators choice c v
        (markingMatrix sig rank generators choice (fun z => X (.inr z)) s i j) = _
    rw [markingMatrix_nonselected _ _ _ _ _ _ _ _ chosen, markingMatrix_nonselected _ _ _ _ _ _ _ _ chosen]
    exact aeval_X _ _


/-- Evaluation sends each universal primitive coefficient to its designated value. -/
theorem universalPrimitiveCoefficients_eval {S : Type u} [CommRing S] [Algebra R S]
    (c : PrimitiveCoefficients sig rank S) (v : MarkingCoordinate sig rank generators choice → S)
    (z : PrimitiveCoordinate sig rank) :
    markedChartEvaluator sig rank generators choice c v
      (PrimitiveCoefficients.valuesEquiv sig rank
        (universalPrimitiveCoefficients (R := R) sig rank generators choice) z) =
      PrimitiveCoefficients.valuesEquiv sig rank c z := by
  rw [universalPrimitiveCoefficients, Equiv.apply_symm_apply]
  exact aeval_X _ _


/-- Each law supplies its own finite arity and output sort. -/
structure MarkedPolynomialLaws (J : Type u) where
  inputs : J → List sig.SortType
  output : J → sig.SortType
  law (j : J) : PolynomialLaw R sig (inputs j) (output j)

section LawEquations

variable {J : Type u} (laws : MarkedPolynomialLaws (R := R) sig J)

/-- Equation (6.2) uses every residual coefficient of every written Law in
the actual universal free realization. -/
def markedResidualIdeal : Ideal (MvPolynomial (MarkedChartVariable sig rank generators choice) R) :=
  ⨆ j, polynomialResidualIdeal ((laws.law j).residual (algebraMap R _)
    (universalMarkedTensor sig rank generators choice) (fun _ => Pi.basisFun _ _))

/-- Quotient the ambient primitive and marking coordinates by precisely the Law relations. -/
abbrev markedChartAlgebra :=
  MvPolynomial (MarkedChartVariable sig rank generators choice) R ⧸
    markedResidualIdeal sig rank generators choice laws

/-- The equations after arbitrary specialization are exactly the original
residual ideals evaluated by the specialization, using the extended bases. -/
theorem markedResidualIdeal_map {S : Type u} [CommRing S] [Algebra R S]
    (q : MvPolynomial (MarkedChartVariable sig rank generators choice) R →ₐ[R] S) :
    let A := MvPolynomial (MarkedChartVariable sig rank generators choice) R
    letI : Algebra A S := q.toRingHom.toAlgebra
    (markedResidualIdeal sig rank generators choice laws).map q.toRingHom =
      ⨆ j, polynomialResidualIdeal ((laws.law j).residual (algebraMap R S)
        (extendStructure A S (universalMarkedTensor sig rank generators choice))
        (extendedBasis (universalMarkedTensor sig rank generators choice) (fun _ => Pi.basisFun _ _))) := by
  let A := MvPolynomial (MarkedChartVariable sig rank generators choice) R
  letI : Algebra A S := q.toRingHom.toAlgebra
  have factors : (algebraMap A S).comp (algebraMap R A) = algebraMap R S :=
    RingHom.ext q.commutes
  change (markedResidualIdeal sig rank generators choice laws).map q.toRingHom = _
  rw [markedResidualIdeal, Ideal.map_iSup]
  congr 1
  funext j
  rw [← factors]
  exact ((laws.law j).residualIdeal_baseChange
    (algebraMap R A) (universalMarkedTensor sig rank generators choice) (fun _ => Pi.basisFun _ _)).symm

/-- A specialization factors through the chart equations exactly when the
extended universal realization satisfies every written Law. -/
theorem markedResidualIdeal_le_ker_iff {S : Type u} [CommRing S] [Algebra R S]
    (q : MvPolynomial (MarkedChartVariable sig rank generators choice) R →ₐ[R] S) :
    let A := MvPolynomial (MarkedChartVariable sig rank generators choice) R
    letI : Algebra A S := q.toRingHom.toAlgebra
    markedResidualIdeal sig rank generators choice laws ≤ RingHom.ker q.toRingHom ↔
      ∀ j, (laws.law j).Holds (algebraMap R S)
        (extendStructure A S (universalMarkedTensor sig rank generators choice)) := by
  let A := MvPolynomial (MarkedChartVariable sig rank generators choice) R
  letI : Algebra A S := q.toRingHom.toAlgebra
  let U := universalMarkedTensor (R := R) sig rank generators choice
  change markedResidualIdeal sig rank generators choice laws ≤ RingHom.ker q.toRingHom ↔ _
  rw [RingHom.ker_eq_comap_bot, ← Ideal.map_le_iff_le_comap, markedResidualIdeal_map]
  rw [iSup_le_iff]
  exact forall_congr' fun j => le_bot_iff.trans
    ((laws.law j).holds_iff_residualIdeal_eq_bot (algebraMap R S) (extendStructure A S U)
      (extendedBasis U (fun _ => Pi.basisFun _ _))).symm


/-- Algebra maps on a chart are exactly ambient points annihilating the
coefficients of the universal residuals. -/
def markedChartAlgHomEquiv (S : Type u) [CommRing S] [Algebra R S] :
    (markedChartAlgebra sig rank generators choice laws →ₐ[R] S) ≃
      {q : MvPolynomial (MarkedChartVariable sig rank generators choice) R →ₐ[R] S //
        markedResidualIdeal sig rank generators choice laws ≤ RingHom.ker q.toRingHom} := by
  let I := markedResidualIdeal sig rank generators choice laws
  let p := Ideal.Quotient.mkₐ R I
  refine
    { toFun := fun f => ⟨f.comp p, ?_⟩
      invFun := fun q => Ideal.Quotient.liftₐ I q.1 (fun x h => q.2 h)
      left_inv := ?_
      right_inv := ?_ }
  · intro x hx
    change f (p x) = 0
    rw [show p x = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · intro f
    apply Ideal.Quotient.algHom_ext
    exact Ideal.Quotient.liftₐ_comp _ _ _
  · intro q
    apply Subtype.ext
    exact Ideal.Quotient.liftₐ_comp _ _ _

/-- The affine marked chart of Equation (6.2), with its map to the base. -/
def markedChartScheme : Over (Spec (CommRingCat.of R)) :=
  specOver (markedChartAlgebra sig rank generators choice laws)

/-- On arbitrary test schemes, chart maps are the lawful specializations
of the ambient polynomial ring in the global structure-ring sections. -/
def markedChartSchemePointEquiv (T : Over (Spec (CommRingCat.of R))) :
    letI := globalSectionsAlgebra T
    (T ⟶ markedChartScheme sig rank generators choice laws) ≃
      {q : MvPolynomial (MarkedChartVariable sig rank generators choice) R →ₐ[R] Γ(T.left, ⊤) //
        let A := MvPolynomial (MarkedChartVariable sig rank generators choice) R
        letI : Algebra A Γ(T.left, ⊤) := q.toRingHom.toAlgebra
        ∀ j, (laws.law j).Holds (algebraMap R Γ(T.left, ⊤))
          (extendStructure A Γ(T.left, ⊤) (universalMarkedTensor sig rank generators choice))} := by
  letI := globalSectionsAlgebra T
  refine (specOverPointEquiv T (markedChartAlgebra sig rank generators choice laws)).trans
    ((markedChartAlgHomEquiv sig rank generators choice laws Γ(T.left, ⊤)).trans ?_)
  exact Equiv.subtypeEquivRight (markedResidualIdeal_le_ker_iff sig rank generators choice laws)

end LawEquations

end MarkedChart

end

end SHIGURE.RealizationFamilies
