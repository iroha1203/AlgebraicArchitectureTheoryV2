import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.FullBasisComparison
import ResearchLean.AG.RelativeRepairComposition.NativeLocalInterface
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Complete generated local basis and section comparisons

## Implementation notes

Both local generators use the same independently defined original affine
solution and full original vertex labels. Each uses its own complete input
basis and finite enumerations; generated regularity is discharged by the
original matrix construction. Every kernel vector and every actual local
value is reconstructed before reading the new generated coordinates.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA
namespace FiniteNative
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v,Module k (M.A v)]
variable (B B' B'' : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)] [DecidablePred (· ∈ U.faces)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek ek' ek'' : FiniteElimination.Enumeration k)
variable (ee ee' ee'' : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef ef' ef'' : FiniteElimination.Enumeration K.TwoCell)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Complete generated local functors have exact inverse composites on the independent original equation. -/
theorem generated_equation_functor_inverse :
    (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef).functor ⋙
      (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef).inverse =
        𝟭 (CoverEquation.Groupoid M P δ U) :=
  changed_label_functor_inverse (MulEquiv.refl (Multiplicative (RelativeCover.C0 M U P)))
    (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef)
    (generated_solution_equivariant M B U P internalEdges hlinear δ ek ee ef)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Complete generated local functors retain every private kernel vector and full original arrow. -/
theorem generated_equation_inverse_functor :
    (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef).inverse ⋙
      (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef).functor =
        𝟭 (GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef) :=
  changed_label_inverse_functor (MulEquiv.refl (Multiplicative (RelativeCover.C0 M U P)))
    (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef)
    (generated_solution_equivariant M B U P internalEdges hlinear δ ek ee ef)

/-- Complete basis and section comparison is computed through the same independent original local equation. -/
def localObjectComparison : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef ≃
    GeneratedObjects M B' U P internalEdges hlinear δ ek' ee' ef' :=
  (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef).symm.trans
    (generatedSolutionEquiv M B' U P internalEdges hlinear δ ek' ee' ef')

omit [DecidablePred (· ∈ P.vertices)] in
/-- Reconstruction preserves the complete original edge cochain and every free private value. -/
theorem local_object_rec (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) :
    (generatedSolutionEquiv M B' U P internalEdges hlinear δ ek' ee' ef').symm
      (localObjectComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef' y) =
        (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef).symm y :=
  (generatedSolutionEquiv M B' U P internalEdges hlinear δ ek' ee' ef').symm_apply_apply _

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every original local edge name preserves its whole full-kernel coefficient value. -/
theorem local_object_value (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) (e : U.edges) :
    ((generatedSolutionEquiv M B' U P internalEdges hlinear δ ek' ee' ef').symm
      (localObjectComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef' y)).1.1 e =
        ((generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef).symm y).1.1 e := by
  rw [local_object_rec]

/-- The full local native comparison retains every original vertex label and transported arrow. -/
noncomputable def localComparison : GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef ≌
    GeneratedGroupoid M B' U P internalEdges hlinear δ ek' ee' ef' :=
  strictComparison (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef)
    (generatedEquationEquivalence M B' U P internalEdges hlinear δ ek' ee' ef')

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every full local comparison preserves reconstruction of the independent original groupoid. -/
theorem local_comparison_rec :
    (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor ⋙
      (generatedEquationEquivalence M B' U P internalEdges hlinear δ ek' ee' ef').inverse =
        (generatedEquationEquivalence M B U P internalEdges hlinear δ ek ee ef).inverse :=
  strict_comparison_rec _ _ (generated_equation_functor_inverse M B' U P internalEdges hlinear δ ek' ee' ef')

omit [DecidablePred (· ∈ P.vertices)] in
/-- Three complete local basis/section changes compose on all coordinates and all original arrows. -/
theorem local_comparison_comp :
    (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor ⋙
      (localComparison M B' B'' U P internalEdges hlinear δ ek' ek'' ee' ee'' ef' ef'').functor =
        (localComparison M B B'' U P internalEdges hlinear δ ek ek'' ee ee'' ef ef'').functor :=
  strict_comparison_comp _ _ _ (generated_equation_functor_inverse M B' U P internalEdges hlinear δ ek' ee' ef')

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every local comparison has a whole inverse on the old full generated groupoid. -/
theorem local_comparison_inverse :
    (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor ⋙
      (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').inverse =
        𝟭 (GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef) :=
  strict_comparison_inverse _ _ (generated_equation_functor_inverse M B' U P internalEdges hlinear δ ek' ee' ef')
    (generated_equation_inverse_functor M B U P internalEdges hlinear δ ek ee ef)

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every local comparison has a whole inverse on the new full generated groupoid. -/
theorem local_inverse_comparison :
    (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').inverse ⋙
      (localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor =
        𝟭 (GeneratedGroupoid M B' U P internalEdges hlinear δ ek' ee' ef') :=
  strict_inverse_comparison _ _ (generated_equation_functor_inverse M B U P internalEdges hlinear δ ek ee ef)
    (generated_equation_inverse_functor M B' U P internalEdges hlinear δ ek' ee' ef')

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every local comparison arrow keeps its entire original vertex label, including stabilizers. -/
theorem local_comparison_label
    {x y : GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef} (b : x ⟶ y) :
    ((localComparison M B B' U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor.map b).1 = b.1 := rfl

end FiniteNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
