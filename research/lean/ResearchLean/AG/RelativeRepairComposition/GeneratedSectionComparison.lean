import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.SectionComparison
import ResearchLean.AG.RelativeRepairComposition.NativeLocalInterface

/-!
# Section comparisons computed from complete original matrices

## Implementation notes

Each section is computed from a complete enumeration of the same original
private differential. The generator discharges both regularity laws. The
comparison retains the entire kernel and every original local gauge label.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uk uG uA
namespace FiniteNative
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (B : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.vertices)] [DecidablePred (· ∈ U.edges)] [DecidablePred (· ∈ U.faces)]
variable (internalEdges : Set (EdgeName (K := K))) [DecidablePred (· ∈ internalEdges)]
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k) (x : M.A i),
  M.edge e (t • x) = t • M.edge e x)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek ek' : FiniteElimination.Enumeration k)
variable (ee ee' : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef ef' : FiniteElimination.Enumeration K.TwoCell)
local notation "D₀" => D M B U P internalEdges hlinear
local notation "F₀" => F M B U P internalEdges hlinear
local notation "σ" => generatedSection M B U P internalEdges hlinear ek ee ef
local notation "τ" => generatedSection M B U P internalEdges hlinear ek' ee' ef'
local notation "hs" => generatedSection_regular M B U P internalEdges hlinear ek ee ef
local notation "ht" => generatedSection_regular M B U P internalEdges hlinear ek' ee' ef'
local notation "r" => rhs M B U P δ
local notation "a₀" => a M B U P internalEdges hlinear
local notation "c₀" => c M B U P internalEdges hlinear
local notation "hz" => D_a_add_F_c M B U P internalEdges hlinear

/-- Compare two sections generated from complete original input enumerations. -/
def generatedSectionComparison :
    GeneratedObjects M B U P internalEdges hlinear δ ek ee ef ≃
      GeneratedObjects M B U P internalEdges hlinear δ ek' ee' ef' :=
  LinearInterface.sectionComparison D₀ F₀ σ τ hs ht r

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every public original coordinate is fixed by the computed section comparison. -/
theorem generated_section_public
    (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) :
    (generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef' y).1.1 = y.1.1 :=
  LinearInterface.section_comparison_public D₀ F₀ σ τ hs ht r y

omit [DecidablePred (· ∈ P.vertices)] in
/-- The whole private kernel changes by the computed difference of section preimages. -/
theorem generated_section_kernel
    (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) :
    (generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef' y).2.1 =
      y.2.1 + (σ - τ) (r - F₀ y.1.1) :=
  LinearInterface.section_comparison_kernel D₀ F₀ σ τ hs ht r y

omit [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ U.vertices)] in
/-- Original input generation proves membership in the full original internal kernel. -/
theorem generated_section_difference_mem (z : ↥(LinearInterface.Relation D₀ F₀ σ r)) :
    (σ - τ) (r - F₀ z.1) ∈ LinearMap.ker D₀ :=
  LinearInterface.section_difference_mem D₀ F₀ σ τ hs ht r z

omit [DecidablePred (· ∈ P.vertices)] in
/-- Reading the independent original equation gives exactly this computed comparison. -/
theorem generated_section_coord (h : CoverEquation.Solution M P δ U) :
    generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef'
      (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef h) =
      generatedSolutionEquiv M B U P internalEdges hlinear δ ek' ee' ef' h :=
  LinearInterface.coord_section_comparison D₀ F₀ σ τ hs ht r
    ⟨(solutionCoordinateEquiv M B U P internalEdges hlinear δ h).1,
      (solutionCoordinateEquiv M B U P internalEdges hlinear δ h).2⟩

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every independent original edge cochain is restored unchanged. -/
theorem generated_section_rec
    (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) :
    (generatedSolutionEquiv M B U P internalEdges hlinear δ ek' ee' ef').symm
      (generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef' y) =
        (generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef).symm y := by
  apply (generatedSolutionEquiv M B U P internalEdges hlinear δ ek' ee' ef').injective
  rw [Equiv.apply_symm_apply]
  rw [← generated_section_coord M B U P internalEdges hlinear δ ek ek' ee ee' ef ef']
  rw [Equiv.apply_symm_apply]

omit [DecidablePred (· ∈ P.vertices)] in
/-- Every original edge name keeps its complete original coefficient value. -/
theorem generated_section_edge
    (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) (e : U.edges) :
    ((generatedSolutionEquiv M B U P internalEdges hlinear δ ek' ee' ef').symm
      (generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef' y)).1.1 e =
        ((generatedSolutionEquiv M B U P internalEdges hlinear δ ek ee ef).symm y).1.1 e := by
  rw [generated_section_rec]

omit [DecidablePred (· ∈ P.vertices)] in
/-- The computed section comparison commutes with all original vertex gauges. -/
theorem generated_section_gauge (b : RelativeCover.C0 M U P)
    (y : GeneratedObjects M B U P internalEdges hlinear δ ek ee ef) :
    generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef'
      (LinearInterface.gauge D₀ F₀ σ hs a₀ c₀ hz r b y) =
      LinearInterface.gauge D₀ F₀ τ ht a₀ c₀ hz r b
        (generatedSectionComparison M B U P internalEdges hlinear δ ek ek' ee ee' ef ef' y) :=
  LinearInterface.section_comparison_gauge D₀ F₀ σ τ hs ht r a₀ c₀ hz b y

/-- The native computed comparison retains all original gauge arrows. -/
def generatedSectionEquivalence :
    GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef ≌
      GeneratedGroupoid M B U P internalEdges hlinear δ ek' ee' ef' :=
  LinearInterface.sectionEquivalence D₀ F₀ σ τ hs ht r a₀ c₀ hz

omit [DecidablePred (· ∈ P.vertices)] in
/-- Its whole forward-inverse composite is the identity on all objects and arrows. -/
theorem generated_section_functor_inverse :
    (generatedSectionEquivalence M B U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor ⋙
      (generatedSectionEquivalence M B U P internalEdges hlinear δ ek ek' ee ee' ef ef').inverse =
        𝟭 (GeneratedGroupoid M B U P internalEdges hlinear δ ek ee ef) :=
  LinearInterface.section_functor_inverse D₀ F₀ σ τ hs ht r a₀ c₀ hz

omit [DecidablePred (· ∈ P.vertices)] in
/-- Its whole inverse-forward composite retains every new coordinate and full label. -/
theorem generated_section_inverse_functor :
    (generatedSectionEquivalence M B U P internalEdges hlinear δ ek ek' ee ee' ef ef').inverse ⋙
      (generatedSectionEquivalence M B U P internalEdges hlinear δ ek ek' ee ee' ef ef').functor =
        𝟭 (GeneratedGroupoid M B U P internalEdges hlinear δ ek' ee' ef') :=
  LinearInterface.section_inverse_functor D₀ F₀ σ τ hs ht r a₀ c₀ hz

end FiniteNative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
