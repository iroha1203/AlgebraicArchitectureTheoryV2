import ResearchLean.AG.RepairObservationDuality.ActualAffineFamily
import ResearchLean.AG.RepairObservationDuality.FullCorrectionCoordinates
import ResearchLean.AG.RepairObservationDuality.EquationCoordinates
import ResearchLean.AG.RepairObservationDuality.PrimitiveInputQueries

/-!
# Actual repairs in the prescribed complete numerical bases

## Implementation notes

G-131 A/C / n1017 §3.5, §6 uses the same primitive-generated physical
input family as Cycle 5. Complete source and face basis equivalences produce
the same affine numerical equation. Inverting the whole correction basis
then the actual native coefficient transport restores the original repair.
-/
namespace AAT.AG.RepairObservationDuality.ActualFamilyCoordinates
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction RelativeRepairComposition PrimitiveAffineDefect
set_option autoImplicit false
universe uk uV uF uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {F : Type uF}
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)
variable [∀ v, Module k ((T.localCoefficients).A v)]
variable (edgeChange : V →ₗ[k] (C1 (T.localCoefficients)))
variable (comparisonChange : V →ₗ[k] (C2 (T.localCoefficients)))
variable (input : F → OriginalTowerPresentation K p q) (ν : F → V)
variable (hdata : ∀ X : F, (input X).toTower.toTransportData =
  data T (edgeChange (ν X)) (comparisonChange (ν X)))

variable (realize : V → F) (hrealize : ∀ v, ν (realize v) = v)
variable (P : ClosedRegion K)
variable (hfixed : ∀ X : F, ∀ f ∈ P.faces,
  (input X).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((input X).comparator f) =
  (input X).toTower.upper.pathLift (K.twoRight f))
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.localCoefficients).A i),
  (T.localCoefficients).edge e (t • x) = t • (T.localCoefficients).edge e x)
variable (bases : FiniteFamily.Bases (k := k) T.localCoefficients.A)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
attribute [local instance] Classical.propDecidable
local notation "D₀" => OriginalColumns.D (k := k) T.localCoefficients P candidates hlinear
local notation "C" => OriginalColumns.column (k := k) T.localCoefficients P candidates houtside hlinear
local notation "fixed" => ActualAffineFamily.model_fixed T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
local notation "b₀" => RelativeAffineDefect.baseRhs T edgeChange comparisonChange P fixed
local notation "B₀" => RelativeAffineDefect.rhsLinear T hlinear edgeChange comparisonChange P fixed
local notation "eH" => FullCorrectionCoordinates.coordinate (k := k) T.localCoefficients bases P candidates
local notation "eW" => FiniteNative.coordinate2 (k := k) T.localCoefficients bases ClosedRegion.all P
include hdata hrealize hfixed

/-- G-131 A/C / n1017 §3.5, §6 constructor: the complete original D_S
expressed in the prescribed whole vertex-kernel bases. -/
noncomputable def numericalD (S : Set candidates) :=
  EquationCoordinates.differential (eH S) eW (SelectedCokernel.differential D₀ C S)

/-- G-131 A/C / n1017 §3.5, §6 constructor: complete prescribed face
coordinates of the primitive-generated linear RHS contribution. -/
noncomputable def numericalB := EquationCoordinates.parameter eW B₀

/-- G-131 A/C / n1017 §3.5, §6 constructor: the negative actual defect's
constant in the same complete prescribed face coordinates. -/
noncomputable def numericalBase := eW b₀

omit [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))] in
/-- G-131 A/C / n1017 §3.5, §6 API: complete numerical face coordinates
preserve the same original parameter kernel used by numerical sufficiency. -/
theorem numerical_parameter_ker :
    LinearMap.ker (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases) =
      LinearMap.ker B₀ :=
  EquationCoordinates.parameter_ker eW B₀

/-- G-131 A/C / n1017 §3.5, §6 API: complete source and face coordinates
preserve the same original residual kernel used by decision sufficiency. -/
theorem numerical_obstruction_ker (S : Set candidates) :
    LinearMap.ker ((LinearMap.range (numericalD T P hlinear bases candidates houtside S)).mkQ.comp
      (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)) =
    LinearMap.ker ((LinearMap.range (SelectedCokernel.differential D₀ C S)).mkQ.comp B₀) :=
  EquationCoordinates.obstruction_ker (eH S) eW (SelectedCokernel.differential D₀ C S) B₀

/-- G-131 A/C / n1017 §3.5, §6: every actual independent repair exists
exactly when the same complete numerical affine equation has a solution. -/
theorem actual_numerical_equation_iff (X : F) (S : Set candidates) :
    Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
    ∃ h, numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X) := by
  rw [numericalB, numericalBase, EquationCoordinates.affine_rhs]
  exact (ActualAffineFamily.actual_affine_equation_iff T edgeChange comparisonChange input ν hdata
    realize hrealize P hfixed hlinear candidates houtside X S).trans
      (EquationCoordinates.equation_iff (eH S) eW
        (SelectedCokernel.differential D₀ C S) (affineRhs B₀ b₀ (ν X))).symm

/-- G-131 A/C / n1017 §3.5, §6: the complete numerical solution restores
all the original correction values in the same shared whole coefficient system. -/
theorem solution_restore (X : F) (S : Set candidates)
    (h : FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S)
    (hh : numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X)) :
    SelectedCokernel.differential D₀ C S ((eH S).symm h) = b₀ + B₀ (ν X) := by
  rw [numericalB, numericalBase, EquationCoordinates.affine_rhs] at hh
  exact (EquationCoordinates.solution_iff (eH S) eW
    (SelectedCokernel.differential D₀ C S) (affineRhs B₀ b₀ (ν X)) h).mp hh

/-- G-131 A/C / n1017 §3.5, §6 constructor: a complete numerical answer
restores the actual original arrows, with every forbidden correction zero. -/
noncomputable def restore (X : F) (S : Set candidates)
    (h : FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S)
    (hh : numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X)) :
    SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :=
  ActualAffineFamily.restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
    hlinear candidates houtside X S ((eH S).symm h)
    (solution_restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates houtside X S h hh)


/-- G-131 A/C / n1017 §3.5, §6 API: every restored original correction
has the whole always and selected values obtained by both inverse basis maps. -/
theorem restore_value (X : F) (S : Set candidates)
    (h : FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S)
    (hh : numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X))
    (e : EdgeName (K := K)) :
    letI := ActualAffineFamily.inputModules T edgeChange comparisonChange input ν hdata X
    let a := CoefficientTransport.values (k := k) T.localCoefficients
      (input X).toTower.localCoefficients P candidates
      (ActualAffineFamily.input_coefficients T edgeChange comparisonChange input ν hdata X).symm S
      ((eH S).symm h)
    (input X).solutionCorrection (restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh).1 e =
      a.1.1.1 ⟨e,Set.mem_univ e⟩ +
      (OriginalRanges.selectedCorrection (k := k) (input X).toTower.localCoefficients P candidates houtside S a.2).1
        ⟨e,Set.mem_univ e⟩ :=
  ActualAffineFamily.restore_value T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear candidates houtside X S ((eH S).symm h) (solution_restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh) e

/-- G-131 A/C / n1017 §3.5, §6 API: complete numerical restoration returns
zero for each original forbidden candidate, preserving its original name. -/
theorem restore_forbidden_zero (X : F) (S : Set candidates)
    (h : FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S)
    (hh : numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X))
    (e : candidates) (he : e ∉ S) :
    (input X).solutionCorrection (restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh).1 e.1 = 0 :=
  ActualAffineFamily.restore_forbidden_zero T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear candidates houtside X S ((eH S).symm h) (solution_restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh) e he

/-- G-131 A/C / n1017 §3.5, §6 API: complete numerical restoration preserves
every original input's actual fixed arrow, including forbidden candidates. -/
theorem restore_fixed_arrow (X : F) (S : Set candidates)
    (h : FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S)
    (hh : numericalD T P hlinear bases candidates houtside S h =
      affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases) (ν X))
    (e : EdgeName (K := K))
    (he : e ∈ fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S)) :
    (selectedUpper K p q (input X).original (restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh).1.choice).edgeLift e.2.2 =
      (input X).toTower.upper.edgeLift e.2.2 :=
  ActualAffineFamily.restore_fixed_arrow T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear candidates houtside X S ((eH S).symm h) (solution_restore T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases candidates houtside X S h hh) e he

/-- G-131 A/C / n1017 §3.5, §6: `none` for the complete numerical equation
certifies nonexistence of the independently defined actual original repair. -/
theorem valid_none_actual_iff (X : F) (S : Set candidates) :
    ValidOutput (numericalD T P hlinear bases candidates houtside S)
      (affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
        (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases)) (ν X) none ↔
    ¬ Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) :=
  (EquationCoordinates.valid_none _ _ _).trans
    (not_congr (actual_numerical_equation_iff T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates houtside X S).symm)

variable {J : Type*} (primitive : J → V →ₗ[k] k) (evalActual : F → J → k)
variable (heval : ∀ X j, evalActual X j = primitive j (ν X))
include heval

/-- G-131 A/C / n1017 §3.5, §6: full numerical correctness of a history-only
primitive procedure is equivalent on the actual original fiber and parameters. -/
theorem primitive_correct_iff (S : Set candidates) (fiber : Set V)
    (next : PrimitiveQueries.Procedure J k
      (Option (FullCorrectionCoordinates.NumericalValues (k := k) T.localCoefficients bases P candidates S))) :
    PrimitiveQueries.Correct evalActual (ν ⁻¹' fiber)
      (fun X out => ValidOutput (numericalD T P hlinear bases candidates houtside S)
        (affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
          (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases)) (ν X) out) next ↔
    PrimitiveQueries.Correct (fun v j => primitive j v) fiber
      (ValidOutput (numericalD T P hlinear bases candidates houtside S)
        (affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
          (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases))) next :=
  PrimitiveInputQueries.correct_iff ν realize hrealize evalActual (fun v j => primitive j v)
    heval fiber _ next

/-- G-131 A/C / n1017 §3.5, §6: actual primitive query optimum for the complete
original numerical correction equals the same parameter-model optimum. -/
theorem primitive_optimum_eq (S : Set candidates) (fiber : Set V) :
    PrimitiveQueries.optimum evalActual (ν ⁻¹' fiber)
      (fun X out => ValidOutput (numericalD T P hlinear bases candidates houtside S)
        (affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
          (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases)) (ν X) out) =
    PrimitiveQueries.optimum (fun v j => primitive j v) fiber
      (ValidOutput (numericalD T P hlinear bases candidates houtside S)
        (affineRhs (numericalB T edgeChange comparisonChange input ν hdata realize hrealize P hfixed hlinear bases)
          (numericalBase T edgeChange comparisonChange input ν hdata realize hrealize P hfixed bases))) :=
  PrimitiveInputQueries.optimum_eq ν realize hrealize evalActual (fun v j => primitive j v)
    heval fiber _

end AAT.AG.RepairObservationDuality.ActualFamilyCoordinates
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.ActualFamilyCoordinates
