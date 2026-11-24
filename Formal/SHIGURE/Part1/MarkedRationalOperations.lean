import Formal.SHIGURE.Part1.MarkedInterpretation
import Formal.SHIGURE.Part1.MarkedRationalPresentation
import Formal.SHIGURE.Part1.MarkedRationalQuotients

/-! # The concrete operations of Example 3.7

The coordinate isomorphisms identify p and r with the single rational
coordinate and q with either of the two specified quotient coordinates.
The four named operations are actual linear maps in these coordinates.

## Implementation notes

Build each unary multilinear map directly on its dependent argument
family. Mathlib's constant-family unary comparison would first require
an equality of that family with a constant type. The written position
already determines the one input to the given linear map.
-/

namespace SHIGURE.Marked.RationalExample

open Vocabulary DeclarationContext

/-- The selected presentation's kernel at each module, with either kernel allowed at q. -/
def kernels (K : Kernel ℚ 2) : (s : SortName) → Kernel ℚ (generatorCount s)
  | .p | .r => unitKernel
  | .q => K

/-- The indicated coordinate isomorphism at each declared module. -/
noncomputable def coordinates {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) :
    (s : SortName) → Quotient (kernels K s) ≃ₗ[ℚ] ℚ
  | .p | .r => unitEquiv
  | .q => coord

/-- The written factors for f, g, u and v in rational coordinates. -/
def factor : Op → ℚ
  | .f => 2
  | .g => 1 / 2
  | .u => 3
  | .v => 1 / 3

/-- The linear operation obtained by the written coordinate multiplier. -/
noncomputable def linearOperation {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) (name : Op) :
    Quotient (kernels K name.source) →ₗ[ℚ] Quotient (kernels K name.target) :=
  factor name • ((coordinates coord name.source).trans (coordinates coord name.target).symm).toLinearMap

/-- The coordinates give the written scalar action of each named operation. -/
theorem coordinate_linearOperation {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ)
    (name : Op) (x : Quotient (kernels K name.source)) :
    coordinates coord name.target (linearOperation coord name x) =
      factor name * coordinates coord name.source x := by
  simp [linearOperation, smul_eq_mul]

/-- For the positive q quotient, f(a) = 2ae in the coefficient coordinate of p. -/
theorem f_formula (a : Quotient unitKernel) :
    linearOperation phi .f a = (2 * unitEquiv a : ℚ) • e := by
  apply phi.injective
  simpa [coordinates, factor, smul_eq_mul] using coordinate_linearOperation phi .f a

/-- For the positive q quotient, g(z) has coordinate phi(z) / 2. -/
theorem g_formula (z : Quotient sharedKernel) :
    unitEquiv (linearOperation phi .g z) = phi z / 2 := by
  exact (coordinate_linearOperation phi .g z).trans (by
    change (1 / 2 : ℚ) * phi z = phi z / 2
    ring)

/-- The right u has coordinate 3 phi(z) on either written q quotient. -/
theorem u_formula {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) (z : Quotient K) :
    unitEquiv (linearOperation coord .u z) = 3 * coord z :=
  coordinate_linearOperation coord .u z

/-- The right v is a multiple of the written basis point for either q quotient. -/
theorem v_formula {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) (basis : Quotient K)
    (basisCoord : coord basis = 1) (a : Quotient unitKernel) :
    linearOperation coord .v a = (unitEquiv a / 3 : ℚ) • basis := by
  apply coord.injective
  exact (coordinate_linearOperation coord .v a).trans (by
    change (1 / 3 : ℚ) * unitEquiv a = coord ((unitEquiv a / 3 : ℚ) • basis)
    rw [map_smul, basisCoord, smul_eq_mul, mul_one]
    ring)

/-- The typed unary linear operation is multilinear on the one declared position. -/
noncomputable def multilinearOperation {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) (name : Op) :
    (kernelsOf (V := vocabulary) (kernels K) name).Map where
  toFun inputs := linearOperation coord name (inputs (argument name))
  map_update_add' inputs i x y := by
    obtain rfl := argument_eq name i
    simp
  map_update_smul' inputs i r x := by
    obtain rfl := argument_eq name i
    simp

/-- Evaluation of a typed unary map reads its linear map at its one argument. -/
theorem multilinearOperation_apply {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ)
    (name : Op) (inputs : ∀ i,
      SortCarrier ℚ ((kernelsOf (V := vocabulary) (kernels K) name).inputs i)) :
    multilinearOperation coord name inputs = linearOperation coord name (inputs (argument name)) :=
  rfl

/-- The ordinary values of the written linear operations in their full signature. -/
noncomputable def coordinateStructure {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) :
    Structure vocabulary.signature :=
  quotientStructure (V := vocabulary) (kernels K) (multilinearOperation coord)

/-- The unary term evaluates to the chosen linear map on the argument's evaluated value. -/
theorem unary_totalValue {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ)
    {Γ : List (Option SortName)} (name : Op)
    (t : Term vocabulary.signature Γ (some name.source))
    (xs : Assignment (coordinateStructure coord).carrier Γ) :
    (unary name t).totalValue (coordinateStructure coord) xs =
      linearOperation coord name (t.totalValue (coordinateStructure coord) xs) :=
  rfl

/-- Both left round trips and both right round trips are the identity on their full carriers. -/
theorem all_roundTrips {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) (name : Op) :
    (roundTrip name).Holds (coordinateStructure coord) := by
  cases name with
  | f =>
    simp only [roundTrip_f, Law.holds_equality_totalValue_iff, unary_totalValue, Term.totalValue_var]
    intro xs
    apply (coordinates coord .q).injective
    exact (coordinate_linearOperation coord .f _).trans
      ((congrArg (factor .f * ·) (coordinate_linearOperation coord .g (xs .here))).trans (by
        change 2 * ((1 / 2 : ℚ) * coord (xs .here)) = coord (xs .here)
        ring))
  | g =>
    simp only [roundTrip_g, Law.holds_equality_totalValue_iff, unary_totalValue, Term.totalValue_var]
    intro xs
    apply (coordinates coord .p).injective
    exact (coordinate_linearOperation coord .g _).trans
      ((congrArg (factor .g * ·) (coordinate_linearOperation coord .f (xs .here))).trans (by
        change (1 / 2 : ℚ) * (2 * unitEquiv (xs .here)) = unitEquiv (xs .here)
        ring))
  | u =>
    simp only [roundTrip_u, Law.holds_equality_totalValue_iff, unary_totalValue, Term.totalValue_var]
    intro xs
    apply (coordinates coord .r).injective
    exact (coordinate_linearOperation coord .u _).trans
      ((congrArg (factor .u * ·) (coordinate_linearOperation coord .v (xs .here))).trans (by
        change 3 * ((1 / 3 : ℚ) * unitEquiv (xs .here)) = unitEquiv (xs .here)
        ring))
  | v =>
    simp only [roundTrip_v, Law.holds_equality_totalValue_iff, unary_totalValue, Term.totalValue_var]
    intro xs
    apply (coordinates coord .q).injective
    exact (coordinate_linearOperation coord .v _).trans
      ((congrArg (factor .v * ·) (coordinate_linearOperation coord .u (xs .here))).trans (by
        change (1 / 3 : ℚ) * (3 * coord (xs .here)) = coord (xs .here)
        ring))

/-- The marked data are defined directly on the retained sorts and symbols of each piece. -/
noncomputable def coordinateData (C : DeclarationContext presentation) {K : Kernel ℚ 2}
    (coord : Quotient K ≃ₗ[ℚ] ℚ) : Data ℚ C where
  kernel s _ := kernels K s
  operation name keep := cast (congrArg OperationKernels.Map (operationKernels_complete (kernels K) keep).symm)
    (multilinearOperation coord name)

/-- Interpreting one retained symbol uses the indicated linear map. -/
theorem coordinateData_operation (C : DeclarationContext presentation) {K : Kernel ℚ 2}
    (coord : Quotient K ≃ₗ[ℚ] ℚ) (name : Op) (keep : vocabulary.multilinearDecl laws name ∈ C.declarations) :
    HEq ((coordinateData C coord).operation name keep) (multilinearOperation coord name) :=
  cast_heq _ _

/-- The full-context calculation agrees with the explicit numerical interpretations. -/
theorem coordinateData_full_structure {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) :
    (coordinateData (DeclarationContext.full presentation) coord).structureData = coordinateStructure coord := by
  apply quotientStructure_congr
  · funext s
    exact (coordinateData (DeclarationContext.full presentation) coord).ambientKernel_kept (Set.mem_univ _)
  · intro name
    exact ((coordinateData (DeclarationContext.full presentation) coord).ambientOperation_kept (Set.mem_univ _)).trans
      (coordinateData_operation _ coord name (Set.mem_univ _))

/-- Restricting these written data keeps exactly the interpretations of the smaller context. -/
theorem coordinateData_restrict {C D : DeclarationContext presentation} (inside : D ≤ C)
    {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) :
    (coordinateData C coord).restrict inside = coordinateData D coord := by
  apply Data.ext
  · intro s keep
    rfl
  · intro name keep
    exact ((coordinateData C coord).restrict_operation inside name keep).trans
      ((coordinateData_operation C coord name (inside keep)).trans (coordinateData_operation D coord name keep).symm)

/-- The same indicated coordinate on two pieces gives actual overlap agreement. -/
theorem coordinateData_agree (C D : DeclarationContext presentation)
    {K : Kernel ℚ 2} (coord : Quotient K ≃ₗ[ℚ] ℚ) : (coordinateData C coord).Agree (coordinateData D coord) where
  kernel _ _ _ := rfl
  operation name left right :=
    (coordinateData_operation C coord name left).trans (coordinateData_operation D coord name right).symm

end SHIGURE.Marked.RationalExample
