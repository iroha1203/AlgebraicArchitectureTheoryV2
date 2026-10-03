import ResearchLean.AG.RepairObservationDuality.FiberSufficiency

/-!
# Complete basis changes of the same correction equation

## Implementation notes

G-131 A/C / n1017 §3.5, §6: both maps are full linear equivalences of the
original correction and face spaces. The numerical equation retains the
whole solution, its independent impossibility predicate and its affine RHS.
No basis of an image or of a quotient replaces the prescribed full bases.
-/
namespace AAT.AG.RepairObservationDuality.EquationCoordinates
set_option autoImplicit false
variable {k V H H' W W' : Type*} [Field k]
variable [AddCommGroup V] [Module k V]
variable [AddCommGroup H] [Module k H] [AddCommGroup H'] [Module k H']
variable [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']
variable (eH : H ≃ₗ[k] H') (eW : W ≃ₗ[k] W') (D : H →ₗ[k] W)

/-- G-131 A/C / n1017 §3.5, §6 constructor: the same full correction map in
the supplied complete source and face bases. -/
def differential : H' →ₗ[k] W' := eW.toLinearMap.comp (D.comp eH.symm.toLinearMap)

/-- G-131 A/C / n1017 §3.5, §6 API: coordinate evaluation preserves the same
whole original correction and whole original face value. -/
theorem differential_apply (h : H') :
    differential eH eW D h = eW (D (eH.symm h)) := rfl

/-- G-131 A/C / n1017 §3.5, §6: a numerical solution restores the same full
original equation, in both directions. -/
theorem solution_iff (r : W) (h : H') :
    differential eH eW D h = eW r ↔ D (eH.symm h) = r := by
  rw [differential_apply, eW.injective.eq_iff]

/-- G-131 A/C / n1017 §3.5, §6: numerical feasibility is exactly feasibility
of the original full equation, including impossibility. -/
theorem equation_iff (r : W) :
    (∃ h, differential eH eW D h = eW r) ↔ ∃ h, D h = r := by
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨eH.symm h, (solution_iff eH eW D r h).mp hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨eH h, (solution_iff eH eW D r (eH h)).mpr (by simpa using hh)⟩

/-- G-131 A/C / n1017 §3.5, §6 constructor: the variable RHS contribution
uses the same complete face coordinates as the differential. -/
def parameter (B : V →ₗ[k] W) : V →ₗ[k] W' := eW.toLinearMap.comp B

/-- G-131 A/C / n1017 §3.5, §6 API: the numerical parameter contribution is
the full original face contribution in its prescribed basis. -/
theorem parameter_apply (B : V →ₗ[k] W) (v : V) :
    parameter eW B v = eW (B v) := rfl

/-- G-131 A/C / n1017 §3.5, §6: the numerical affine RHS is obtained by
coordinate evaluation of the same original affine RHS, with its sign intact. -/
theorem affine_rhs (B : V →ₗ[k] W) (b₀ : W) (v : V) :
    affineRhs (parameter eW B) (eW b₀) v = eW (affineRhs B b₀ v) := by
  change eW b₀ + eW (B v) = eW (b₀ + B v)
  exact (eW.map_add _ _).symm

/-- G-131 A/C / n1017 §3.5, §6: full coordinate evaluation preserves the
numerical-information kernel without replacing it by a residual quotient. -/
theorem parameter_ker (B : V →ₗ[k] W) :
    LinearMap.ker (parameter eW B) = LinearMap.ker B := by
  ext v
  rw [LinearMap.mem_ker, LinearMap.mem_ker, parameter_apply]
  exact eW.map_eq_zero_iff

/-- G-131 A/C / n1017 §3.5, §6: the success-shift kernel is unchanged by
complete correction and face coordinates. -/
theorem obstruction_ker (B : V →ₗ[k] W) :
    LinearMap.ker ((LinearMap.range (differential eH eW D)).mkQ.comp (parameter eW B)) =
      LinearMap.ker ((LinearMap.range D).mkQ.comp B) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, parameter_apply]
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range (differential eH eW D))).trans
    ((equation_iff eH eW D (B v)).trans
      (Submodule.Quotient.mk_eq_zero (LinearMap.range D)).symm)

/-- G-131 C / n1017 §6 constructor API: a complete returned correction is
valid exactly when it satisfies the specified equation. -/
theorem valid_some {U : Type*} (rhs : U → W) (v : U) (h : H) :
    ValidOutput D rhs v (some h) ↔ D h = rhs v := Iff.rfl

/-- G-131 C / n1017 §6 constructor API: `none` asserts impossibility of the
same independently defined correction equation. -/
theorem valid_none {U : Type*} (rhs : U → W) (v : U) :
    ValidOutput D rhs v none ↔ ¬ ∃ h, D h = rhs v := Iff.rfl

/-- G-131 A/C / n1017 §3.5, §6: restoration of a full numerical answer
preserves both complete successful outputs and independent impossibility. -/
theorem valid_output_iff {U : Type*} (rhs : U → W) (v : U) (out : Option H') :
    ValidOutput (differential eH eW D) (fun u => eW (rhs u)) v out ↔
      ValidOutput D rhs v (out.map eH.symm) := by
  cases out with
  | none =>
    rw [Option.map_none, valid_none, valid_none, equation_iff]
  | some h =>
    rw [Option.map_some, valid_some, valid_some, solution_iff]

end AAT.AG.RepairObservationDuality.EquationCoordinates
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.EquationCoordinates
