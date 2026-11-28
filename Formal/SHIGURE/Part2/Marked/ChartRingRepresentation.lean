import Formal.SHIGURE.Part2.Marked.ChartLaws
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Affine representation of normalized marked free realizations

Construction 6.4 represents the chart where the selected generating columns
are a basis. A normalized realization keeps an actual `TensorStructure`
and actual marking linear maps. Its carrier identifications only specify
the standard free modules used for the chart. Laws are evaluated by the
original tensor and polynomial semantics.

## Implementation notes

The data type is independent of polynomial coordinates: its primitive
operations are arbitrary mathlib multilinear maps and its markings are
arbitrary linear maps. Coordinates are read afterwards on basis vectors.
Carrier equalities describe the normalized chart; the comparison with an
arbitrary carrier having a chosen basis belongs to the marked groupoid
construction. The scalar-extension comparison below retains the actual
tensor extension rather than asserting naturality only for coordinate arrays.
-/

universe u

namespace SHIGURE.RealizationFamilies.Marked

open Module CategoryTheory SHIGURE.TensorRealization SHIGURE.CoefficientDescent
open scoped TensorProduct

noncomputable section

variable {sig : Signature.{u}} {generators rank : sig.SortType → ℕ}

/-- Independent primitive operations and linear markings on standard free
carriers. No Law or normalization condition is stored in the data. -/
structure FreeMarkedData (R : Type u) [CommRing R] (generators rank : sig.SortType → ℕ) where
  /-- The original module-valued structure, with actual multilinear operations. -/
  realization : TensorStructure R sig
  /-- Normalized coordinates use these specific standard free carriers. -/
  carrier_eq (s : sig.SortType) : realization.carrier s = ModuleCat.of R (Fin (rank s) → R)
  /-- The original marking is an actual linear map, before any equation is tested. -/
  marking (s : sig.SortType) : (Fin (generators s) → R) →ₗ[R] realization.carrier s

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]

namespace FreeMarkedData

variable (D : FreeMarkedData (sig := sig) R generators rank)

/-- Read the standard free coordinates of the actual carrier. -/
def carrierEquiv (s : sig.SortType) : D.realization.carrier s ≃ₗ[R] (Fin (rank s) → R) := by
  rw [D.carrier_eq s]
  exact LinearEquiv.refl R _

/-- The actual carrier basis obtained from its standard free coordinates. -/
def carrierBasis (s : sig.SortType) : Basis (Fin (rank s)) R (D.realization.carrier s) :=
  (freeBasis rank R s).map (D.carrierEquiv s).symm

open Classical in
/-- Selected generating columns are exactly the carrier basis vectors. -/
def IsNormalized (I : ChartIndex (sig := sig) generators rank) : Prop :=
  ∀ (s : sig.SortType) (a : Fin (rank s)),
    D.marking s (Pi.single (I s a) 1) = D.carrierBasis s a

/-- Original tensor equations and universally interpreted polynomial Laws. -/
def Satisfies (P : AffineLawPresentation k sig) (c : k →+* R) : Prop :=
  (∀ l, ((P.tensorLaw l).mapScalars c).holds D.realization) ∧
    (∀ l, (P.polynomialLaw l).Holds c D.realization)

open Classical in
/-- Read the independent marking and primitive entries from actual basis values. -/
def coordinates (I : ChartIndex (sig := sig) generators rank) : ChartVariable I → R
  | .inl ⟨s, a, j⟩ => (D.carrierBasis s).repr (D.marking s (Pi.single j.1 1)) a
  | .inr ⟨.inl f, b, v⟩ => (D.carrierBasis _).repr
      (D.realization.total f (fun i => D.carrierBasis i.1 (v i))) b
  | .inr ⟨.inr q, b, v⟩ => (D.carrierBasis _).repr
      (D.realization.quantity q (fun i => D.carrierBasis i.1 (v i))) b

/-- Normalization supplies preimages of every basis vector, hence the marking is onto. -/
theorem IsNormalized.surjective {I : ChartIndex (sig := sig) generators rank}
    (h : D.IsNormalized I) (s : sig.SortType) : Function.Surjective (D.marking s) := by
  classical
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← (D.carrierBasis s).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨a, rfl⟩
  exact ⟨Pi.single (I s a) 1, h s a⟩

end FreeMarkedData

variable (k) [Algebra k R]
variable (I : ChartIndex (sig := sig) generators rank)

/-- Specialize universal entries to actual independent multilinear operations
and the linear map defined by the specialized marking matrix. -/
def dataOfAssignment (v : ChartVariable I → R) : FreeMarkedData (sig := sig) R generators rank where
  realization := freeStructure rank R (fun z => v (Sum.inr z))
  carrier_eq _ := rfl
  marking s := Matrix.mulVecLin (fun a j => MvPolynomial.aeval v (markingEntry k I s a j))

/-- The specialized identity columns give the required normalization. -/
theorem dataOfAssignment_normalized (v : ChartVariable I → R) :
    (dataOfAssignment k I v).IsNormalized I := by
  classical
  intro s a
  change (Matrix.mulVecLin (fun a j => MvPolynomial.aeval v (markingEntry k I s a j)))
      (Pi.single (I s a) 1) = _
  simp only [FreeMarkedData.carrierBasis, FreeMarkedData.carrierEquiv, dataOfAssignment,
    Basis.map_apply, Matrix.mulVecLin_apply,
    Matrix.mulVec_single_one]
  funext b
  change MvPolynomial.aeval v (markingEntry k I s b (I s a)) = (freeBasis rank R s a) b
  simp [markingEntry_selected, freeBasis, Pi.single_apply, eq_comm]

/-- Reading actual multilinear and marking entries recovers each assignment. -/
theorem coordinates_dataOfAssignment (v : ChartVariable I → R) :
    (dataOfAssignment k I v).coordinates I = v := by
  classical
  funext z
  cases z with
  | inl z =>
    obtain ⟨s, a, j, outside⟩ := z
    change ((Matrix.mulVecLin (fun a j => MvPolynomial.aeval v (markingEntry k I s a j)))
      (Pi.single j 1)) a = v (Sum.inl ⟨s, a, ⟨j, outside⟩⟩)
    simp [markingEntry_unselected, outside]
  | inr z =>
    obtain ⟨e, b, v'⟩ := z
    cases e with
    | inl f =>
      simpa [FreeMarkedData.coordinates, dataOfAssignment, FreeMarkedData.carrierBasis,
        FreeMarkedData.carrierEquiv, freeStructure] using
        operationOfCoefficients_basis rank R (sig.totalArity f)
          (fun b v' => v (Sum.inr ⟨Sum.inl f, b, v'⟩)) b v'
    | inr q =>
      simpa [FreeMarkedData.coordinates, dataOfAssignment, FreeMarkedData.carrierBasis,
        FreeMarkedData.carrierEquiv, freeStructure] using
        operationOfCoefficients_basis rank R (sig.quantityArity q)
          (fun b v' => v (Sum.inr ⟨Sum.inr q, b, v'⟩)) b v'

/-- A normalized datum is reconstructed from its actual primitive and marking
entries; no coordinate condition is built into the datum type. -/
theorem dataOfAssignment_coordinates (D : FreeMarkedData (sig := sig) R generators rank)
    (h : D.IsNormalized I) : dataOfAssignment k I (D.coordinates I) = D := by
  classical
  obtain ⟨⟨carrier, total, quantity⟩, carrier_eq, marking⟩ := D
  have carriers : carrier = fun s => ModuleCat.of R (Fin (rank s) → R) :=
    funext carrier_eq
  subst carrier
  have proof_eq : carrier_eq = fun _ => rfl := Subsingleton.elim _ _
  subst carrier_eq
  have totals : ∀ f, operationOfCoefficients rank R (sig.totalArity f)
      (fun b v => total f (fun i => freeBasis rank R i.1 (v i)) b) = total f :=
    fun f => operationOfCoefficients_reconstruct rank R (sig.totalArity f) (total f)
  have quantities : ∀ q, operationOfCoefficients rank R (sig.quantityArity q)
      (fun b v => quantity q (fun i => freeBasis rank R i.1 (v i)) b) = quantity q :=
    fun q => operationOfCoefficients_reconstruct rank R (sig.quantityArity q) (quantity q)
  have marks : ∀ s, Matrix.mulVecLin
      (fun a j => MvPolynomial.aeval
        (FreeMarkedData.coordinates
          ⟨⟨_, total, quantity⟩, fun _ => rfl, marking⟩ I) (markingEntry k I s a j)) = marking s := by
    intro s
    apply (freeBasis generators R s).ext
    intro j
    funext a
    simp only [freeBasis, Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one]
    change MvPolynomial.aeval _ (markingEntry k I s a j) = (marking s (Pi.single j 1)) a
    by_cases selected : ∃ b, I s b = j
    · obtain ⟨b, rfl⟩ := selected
      rw [markingEntry_selected]
      have normalized := congrFun (h s b) a
      simpa [FreeMarkedData.carrierBasis, FreeMarkedData.carrierEquiv,
        freeBasis, Pi.single_apply, eq_comm] using normalized.symm
    · rw [markingEntry_unselected k I s a j selected]
      rw [MvPolynomial.aeval_X]
      rfl
  simp only [dataOfAssignment, freeStructure, FreeMarkedData.coordinates,
    FreeMarkedData.carrierBasis, FreeMarkedData.carrierEquiv]
  congr 1
  · congr 1
    · exact funext totals
    · exact funext quantities
  · exact funext marks

/-- Arbitrary assignments correspond to all independent normalized free data. -/
def normalizedDataEquiv : (ChartVariable I → R) ≃
    {D : FreeMarkedData (sig := sig) R generators rank // D.IsNormalized I} where
  toFun v := ⟨dataOfAssignment k I v, dataOfAssignment_normalized k I v⟩
  invFun D := D.val.coordinates I
  left_inv := coordinates_dataOfAssignment k I
  right_inv D := Subtype.ext (dataOfAssignment_coordinates k I D.val D.property)

omit [Algebra k R] in
/-- The actual coefficient expansion of a typed polynomial term specializes
on free carriers by the given assignment. API for the Law quotient comparison. -/
private theorem freeTerm_expand_map {A : Type u} [CommRing A]
    (q : k →+* A) (c : OperationCoordinate sig rank → A) (f : A →+* R)
    {Γ : List sig.SortType} {s : sig.SortType} (t : PolynomialTerm k sig Γ s) :
    ∀ j, MvPolynomial.map f (t.expand q (freeStructure rank A c) (freeBasis rank A) j) =
      t.expand (f.comp q) (freeStructure rank R (fun z => f (c z))) (freeBasis rank R) j := by
  classical
  induction t with
  | var i => intro j; exact MvPolynomial.map_X f _
  | total op args ih =>
    intro j
    simp only [PolynomialTerm.expand, operationPolynomial, map_sum, map_mul,
      MvPolynomial.map_C, map_prod]
    apply Finset.sum_congr rfl
    intro idx _
    congr 1
    · change MvPolynomial.C (f ((operationOfCoefficients rank A (sig.totalArity op)
          (fun b v => c ⟨Sum.inl op, b, v⟩)) (fun i => freeBasis rank A i.1 (idx i)) j)) =
        MvPolynomial.C ((operationOfCoefficients rank R (sig.totalArity op)
          (fun b v => f (c ⟨Sum.inl op, b, v⟩))) (fun i => freeBasis rank R i.1 (idx i)) j)
      rw [operationOfCoefficients_basis, operationOfCoefficients_basis]
    · exact Finset.prod_congr rfl (fun i _ => ih i (idx i))
  | quantity op args ih =>
    intro j
    simp only [PolynomialTerm.expand, operationPolynomial, map_sum, map_mul,
      MvPolynomial.map_C, map_prod]
    apply Finset.sum_congr rfl
    intro idx _
    congr 1
    · change MvPolynomial.C (f ((operationOfCoefficients rank A (sig.quantityArity op)
          (fun b v => c ⟨Sum.inr op, b, v⟩)) (fun i => freeBasis rank A i.1 (idx i)) j)) =
        MvPolynomial.C ((operationOfCoefficients rank R (sig.quantityArity op)
          (fun b v => f (c ⟨Sum.inr op, b, v⟩))) (fun i => freeBasis rank R i.1 (idx i)) j)
      rw [operationOfCoefficients_basis, operationOfCoefficients_basis]
    · exact Finset.prod_congr rfl (fun i _ => ih i (idx i))
  | zero s => intro j; exact map_zero _
  | add a b ha hb =>
    intro j
    simp only [PolynomialTerm.expand, map_add, ha j, hb j]
  | smul a b hb =>
    intro j
    simp only [PolynomialTerm.expand, map_mul, MvPolynomial.map_C, RingHom.comp_apply, hb j]

/-- Each monomial coefficient of the original universal polynomial Law
specializes to the coefficient of that Law on the assigned actual operations. -/
private theorem polynomialResidual_aeval (v : ChartVariable I → R)
    {Γ : List sig.SortType} {s : sig.SortType} (law : PolynomialLaw k sig Γ s)
    (j : Fin (rank s)) (m : PolynomialInputCoordinates rank Γ →₀ ℕ) :
    MvPolynomial.aeval v (MvPolynomial.coeff m (universalPolynomialResidual rank k I law j)) =
      MvPolynomial.coeff m (law.residual (algebraMap k R)
        (freeStructure rank R (fun z => v (Sum.inr z))) (freeBasis rank R) j) := by
  let f : ChartAmbient k I →+* R := (MvPolynomial.aeval v).toRingHom
  have scalars : f.comp (algebraMap k (ChartAmbient k I)) = algebraMap k R := by
    ext a
    exact (MvPolynomial.aeval v).commutes a
  have coordinates : (fun z => f (operationEntry k I z)) = fun z => v (Sum.inr z) := by
    funext z
    exact MvPolynomial.aeval_X v _
  have expand (t : PolynomialTerm k sig Γ s) :=
    freeTerm_expand_map k (algebraMap k (ChartAmbient k I)) (operationEntry k I) f t j
  rw [scalars, coordinates] at expand
  change f (MvPolynomial.coeff m (universalPolynomialResidual rank k I law j)) = _
  rw [← MvPolynomial.coeff_map]
  change MvPolynomial.coeff m (MvPolynomial.map f
    (law.residual (algebraMap k (ChartAmbient k I)) (universalStructure rank k I)
      (freeBasis rank (ChartAmbient k I)) j)) = _
  simp only [universalStructure]
  rw [PolynomialLaw.residual_apply, map_sub, expand law.left, expand law.right]
  rfl

/-- All original Laws hold after specialization exactly when the entire
universal residual ideal vanishes under that assignment. -/
theorem dataOfAssignment_satisfies_iff (P : AffineLawPresentation k sig)
    (v : ChartVariable I → R) :
    (dataOfAssignment k I v).Satisfies P (algebraMap k R) ↔
      chartLawIdeal rank I P ≤ RingHom.ker (MvPolynomial.aeval v).toRingHom := by
  rw [chartLawIdeal_le_iff]
  change ((∀ l, ((P.tensorLaw l).mapScalars (algebraMap k R)).holds
      (freeStructure rank R (fun z => v (Sum.inr z)))) ∧
    (∀ l, (P.polynomialLaw l).Holds (algebraMap k R)
      (freeStructure rank R (fun z => v (Sum.inr z))))) ↔ _
  constructor
  · rintro ⟨tensor, polynomial⟩ z
    cases z with
    | inl z =>
      obtain ⟨l, i, j⟩ := z
      change MvPolynomial.aeval v _ = 0
      rw [chartResidual, tensorResidual_aeval]
      exact (tensorLaw_holds_iff_residual_zero rank _ _ _ _).mp (tensor l) i j
    | inr z =>
      obtain ⟨l, j, m⟩ := z
      change MvPolynomial.aeval v _ = 0
      rw [chartResidual, polynomialResidual_aeval]
      exact ((P.polynomialLaw l).holds_iff_all_monomial_coefficients_zero _ _ _).mp
        (polynomial l) j m
  · intro vanish
    constructor
    · intro l
      apply (tensorLaw_holds_iff_residual_zero rank _ _ (freeBasis rank R) _).mpr
      intro i j
      have zero := vanish (Sum.inl ⟨l, i, j⟩)
      change MvPolynomial.aeval v _ = 0 at zero
      rw [chartResidual, tensorResidual_aeval] at zero
      exact zero
    · intro l
      apply ((P.polynomialLaw l).holds_iff_all_monomial_coefficients_zero
        _ _ (freeBasis rank R)).mpr
      intro j m
      have zero := vanish (Sum.inr ⟨l, j, m⟩)
      change MvPolynomial.aeval v _ = 0 at zero
      rw [chartResidual, polynomialResidual_aeval] at zero
      exact zero

/-- The actual normalized free realizations satisfying the original Laws. -/
abbrev NormalizedMarkedFreeRealization (P : AffineLawPresentation k sig) :=
  {D : FreeMarkedData (sig := sig) R generators rank //
    D.IsNormalized I ∧ D.Satisfies P (algebraMap k R)}

variable {k I}

/-- A normalized Lawful datum is a realization in the existing affine category;
finite local freeness and the prescribed ranks follow from its carrier bases. -/
theorem normalized_affineProperty (P : AffineLawPresentation k sig)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    affineProperty P rank (algebraMap k R) D.val.realization := by
  refine ⟨?_, ?_, D.property.2⟩
  · intro s
    rw [D.val.carrier_eq s]
    exact finiteLocallyFree_iff_finite_projective.mpr ⟨inferInstance, inferInstance⟩
  · intro s p
    letI : Nontrivial R := p.nontrivial
    rw [D.val.carrier_eq s]
    simp [Module.rankAtStalk_eq_finrank_of_free]

/-- Forget normalization and marking into the existing full realization category. -/
def normalizedToAffine (P : AffineLawPresentation k sig)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    AffineRealization P rank (algebraMap k R) :=
  ⟨D.val.realization, normalized_affineProperty P D⟩

variable (k I)

/-- A quotient-algebra point reads the images of the original independent variables. -/
def assignmentOfChartHom (P : AffineLawPresentation k sig)
    (f : ChartRing rank I P →ₐ[k] R) : ChartVariable I → R :=
  fun z => f (chartGenerator rank I P z)

/-- Evaluation at these variable images is exactly composition with the quotient map. -/
theorem aeval_assignmentOfChartHom (P : AffineLawPresentation k sig)
    (f : ChartRing rank I P →ₐ[k] R) :
    MvPolynomial.aeval (assignmentOfChartHom k I P f) = f.comp (chartQuotient rank I P) := by
  apply MvPolynomial.algHom_ext
  intro z
  exact MvPolynomial.aeval_X _ z

/-- The quotient point kills every element of the universal residual ideal. -/
theorem assignmentOfChartHom_vanishes (P : AffineLawPresentation k sig)
    (f : ChartRing rank I P →ₐ[k] R) :
    chartLawIdeal rank I P ≤
      RingHom.ker (MvPolynomial.aeval (assignmentOfChartHom k I P f)).toRingHom := by
  intro a ha
  change MvPolynomial.aeval (assignmentOfChartHom k I P f) a = 0
  rw [aeval_assignmentOfChartHom, AlgHom.comp_apply]
  rw [show chartQuotient rank I P a = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]

/-- Read an actual normalized marked free realization from a point of `B_I`. -/
def realizationOfChartHom (P : AffineLawPresentation k sig)
    (f : ChartRing rank I P →ₐ[k] R) : NormalizedMarkedFreeRealization (R := R) k I P :=
  ⟨dataOfAssignment k I (assignmentOfChartHom k I P f),
    dataOfAssignment_normalized k I _,
    (dataOfAssignment_satisfies_iff k I P _).mpr (assignmentOfChartHom_vanishes k I P f)⟩

/-- The independent coordinates of a Lawful normalized realization kill `J_I`. -/
theorem realization_coordinates_vanish (P : AffineLawPresentation k sig)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    chartLawIdeal rank I P ≤ RingHom.ker (MvPolynomial.aeval (D.val.coordinates I)).toRingHom := by
  apply (dataOfAssignment_satisfies_iff k I P _).mp
  rw [dataOfAssignment_coordinates k I D.val D.property.1]
  exact D.property.2

/-- Actual primitive and marking coordinates give a map out of the Law quotient. -/
def chartHomOfRealization (P : AffineLawPresentation k sig)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) : ChartRing rank I P →ₐ[k] R :=
  Ideal.Quotient.liftₐ (chartLawIdeal rank I P) (MvPolynomial.aeval (D.val.coordinates I))
    (realization_coordinates_vanish k I P D)

/-- The quotient map built from a realization returns its independently read entries. -/
theorem assignmentOfChartHom_chartHomOfRealization (P : AffineLawPresentation k sig)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    assignmentOfChartHom k I P (chartHomOfRealization k I P D) = D.val.coordinates I := by
  funext z
  change MvPolynomial.aeval (D.val.coordinates I) (MvPolynomial.X z) = _
  exact MvPolynomial.aeval_X _ z

/-- The coordinate-ring representation in Construction 6.4, on every algebra,
including the zero algebra and all zero-rank sorts. -/
def chartPointEquiv (P : AffineLawPresentation k sig) :
    (ChartRing rank I P →ₐ[k] R) ≃ NormalizedMarkedFreeRealization (R := R) k I P where
  toFun := realizationOfChartHom k I P
  invFun := chartHomOfRealization k I P
  left_inv := by
    intro f
    apply AlgHom.ext
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    change MvPolynomial.aeval
      ((dataOfAssignment k I (assignmentOfChartHom k I P f)).coordinates I) p = _
    rw [coordinates_dataOfAssignment, aeval_assignmentOfChartHom]
    rfl
  right_inv := by
    intro D
    apply Subtype.ext
    change dataOfAssignment k I
      (assignmentOfChartHom k I P (chartHomOfRealization k I P D)) = D.val
    rw [assignmentOfChartHom_chartHomOfRealization, dataOfAssignment_coordinates k I D.val D.property.1]

variable [Algebra k S]

/-- Scalar change in the normalized chart is computed on independently read
primitive and marking entries. Its tensor comparison is stated separately below. -/
def normalizedMap (P : AffineLawPresentation k sig) (f : R →ₐ[k] S)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    NormalizedMarkedFreeRealization (R := S) k I P :=
  realizationOfChartHom k I P (f.comp (chartHomOfRealization k I P D))

/-- The coordinate representation is natural in every coefficient algebra map. -/
theorem chartPointEquiv_natural (P : AffineLawPresentation k sig) (f : R →ₐ[k] S)
    (g : ChartRing rank I P →ₐ[k] R) :
    chartPointEquiv k I P (f.comp g) = normalizedMap k I P f (chartPointEquiv k I P g) := by
  simp only [normalizedMap]
  change realizationOfChartHom k I P (f.comp g) =
    realizationOfChartHom k I P (f.comp ((chartPointEquiv k I P).symm (chartPointEquiv k I P g)))
  rw [Equiv.symm_apply_apply]

/-- Scalar change reads exactly the scalar images of all independent entries.
API for the actual tensor comparison, rather than a replacement definition. -/
private theorem normalizedMap_data (P : AffineLawPresentation k sig) (f : R →ₐ[k] S)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    (normalizedMap k I P f D).val =
      dataOfAssignment k I (fun z => f (D.val.coordinates I z)) := by
  change dataOfAssignment k I
    (assignmentOfChartHom k I P (f.comp (chartHomOfRealization k I P D))) = _
  congr 1
  funext z
  change f (MvPolynomial.aeval (D.val.coordinates I) (MvPolynomial.X z)) = _
  rw [MvPolynomial.aeval_X]

/-- Scalar extension of the independently specialized operations and markings
agrees with coefficient specialization, including every marking vector. -/
private theorem dataOfAssignment_tensorComparison (f : R →ₐ[k] S) (v : ChartVariable I → R) :
    letI : Algebra R S := f.toRingHom.toAlgebra
    ∃ e : extendStructure R S (dataOfAssignment k I v).realization ≅
        (dataOfAssignment k I (fun z => f (v z))).realization,
      ∀ (s : sig.SortType) (x : Fin (generators s) → R),
        e.hom.onSort s ((1 : S) ⊗ₜ[R] (dataOfAssignment k I v).marking s x) =
          (dataOfAssignment k I (fun z => f (v z))).marking s (fun j => f (x j)) := by
  classical
  letI : Algebra R S := f.toRingHom.toAlgebra
  refine ⟨freeStructureBaseChangeIso rank (fun z => v (Sum.inr z)), ?_⟩
  intro s x
  change freeCarrierBaseChange rank s
    ((1 : S) ⊗ₜ[R] (dataOfAssignment k I v).marking s x) = _
  rw [freeCarrierBaseChange_unit]
  have evaluation : f.comp (MvPolynomial.aeval v) =
      MvPolynomial.aeval (fun z => f (v z)) := by
    apply MvPolynomial.algHom_ext
    intro z
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  funext a
  change f ((Matrix.mulVecLin (fun a j => MvPolynomial.aeval v (markingEntry k I s a j))) x a) =
    (Matrix.mulVecLin
      (fun a j => MvPolynomial.aeval (fun z => f (v z)) (markingEntry k I s a j)))
        (fun j => f (x j)) a
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun r => r * f (x j)) (AlgHom.congr_fun evaluation (markingEntry k I s a j))

/-- Naturality uses actual module scalar extension: there is a structured
comparison isomorphism, preserving the extended marking on unit tensors. -/
theorem normalizedMap_tensorComparison (P : AffineLawPresentation k sig) (f : R →ₐ[k] S)
    (D : NormalizedMarkedFreeRealization (R := R) k I P) :
    letI : Algebra R S := f.toRingHom.toAlgebra
    ∃ e : extendStructure R S D.val.realization ≅ (normalizedMap k I P f D).val.realization,
      ∀ (s : sig.SortType) (x : Fin (generators s) → R),
        e.hom.onSort s ((1 : S) ⊗ₜ[R] D.val.marking s x) =
          (normalizedMap k I P f D).val.marking s (fun j => f (x j)) := by
  obtain ⟨v, recovered⟩ := (normalizedDataEquiv (R := R) k I).surjective
    ⟨D.val, D.property.1⟩
  have data_eq : dataOfAssignment k I v = D.val := congrArg Subtype.val recovered
  let E : NormalizedMarkedFreeRealization (R := R) k I P :=
    ⟨dataOfAssignment k I v, dataOfAssignment_normalized k I v, by rw [data_eq]; exact D.property.2⟩
  have same : E = D := Subtype.ext data_eq
  rw [← same]
  have target : (normalizedMap k I P f E).val = dataOfAssignment k I (fun z => f (v z)) := by
    rw [normalizedMap_data]
    change dataOfAssignment k I (fun z => f ((dataOfAssignment k I v).coordinates I z)) = _
    rw [coordinates_dataOfAssignment]
  rw [target]
  exact dataOfAssignment_tensorComparison k I f v

end

end SHIGURE.RealizationFamilies.Marked
