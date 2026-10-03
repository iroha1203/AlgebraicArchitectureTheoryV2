import ResearchLean.AG.RelativeRepairComposition.W3GaugeAction
import Mathlib.CategoryTheory.IsomorphismClasses

/-! # W3's complete actual arrow equations

These equations compare arbitrary independent actual repairs on both original
edges. Every morphism keeps its entire original vertex label, including labels
that act trivially on all repair objects.
-/
namespace AAT.AG.RelativeRepairComposition.W3ActualArrows
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W3LinearAction W3AffineInput W3Regions W3AuthoredOperations
open W3ActualRepairs W3GaugeLabels W3GaugeAction

/-- The actual full-label action for each original permission set. -/
noncomputable local instance actualAction (sheared : Bool) (S : Set (EdgeName (K := geometry))) :
    AddAction (GlobalLabels sheared S) (RealRepairs sheared S) :=
  gaugeAddAction geometry (reference sheared) (reference sheared) comparison
    (linear_faces sheared) fixedRegion.vertices (fixedEdges S)

/-- Both full correction vectors determine an arbitrary independent actual repair. -/
theorem parameters_injective {sheared : Bool} {S : Set (EdgeName (K := geometry))} :
    Function.Injective (parameters (sheared := sheared) (S := S)) := by
  intro R Q h
  apply (actualParametersEquiv sheared S).injective
  exact Subtype.ext h

/-- The two complete affine correction equations characterize the actual gauge equality. -/
theorem gauge_eq_iff_parameters (sheared : Bool) (S : Set (EdgeName (K := geometry)))
    (b : GlobalLabels sheared S) (R Q : RealRepairs sheared S) :
    b +ᵥ R = Q ↔
      (parameters R).1 + b.1 vertexT - b.1 vertexS = (parameters Q).1 ∧
      (parameters R).2 + b.1 vertexS - linearAction sheared (b.1 vertexT) =
        (parameters Q).2 := by
  constructor
  · intro h
    exact ⟨(gauge_first sheared S b R).symm.trans (congrArg (fun X => (parameters X).1) h),
      (gauge_second sheared S b R).symm.trans (congrArg (fun X => (parameters X).2) h)⟩
  · intro h
    apply parameters_injective
    apply Prod.ext
    · exact (gauge_first sheared S b R).trans h.1
    · exact (gauge_second sheared S b R).trans h.2

/-- Every actual arrow satisfies the entire original e equation. -/
theorem hom_first {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    {R Q : ActualCategory sheared S} (f : R ⟶ Q) :
    (parameters R.back).1 + f.1.toAdd.1 vertexT - f.1.toAdd.1 vertexS =
      (parameters Q.back).1 :=
  ((gauge_eq_iff_parameters sheared S f.1.toAdd R.back Q.back).mp f.2).1

/-- Every actual arrow satisfies the entire original f equation with full T. -/
theorem hom_second {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    {R Q : ActualCategory sheared S} (f : R ⟶ Q) :
    (parameters R.back).2 + f.1.toAdd.1 vertexS - linearAction sheared (f.1.toAdd.1 vertexT) =
      (parameters Q.back).2 :=
  ((gauge_eq_iff_parameters sheared S f.1.toAdd R.back Q.back).mp f.2).2

/-- Every actual arrow changes the same original loop by its full (I-T)b_s. -/
theorem hom_loop {sheared : Bool} {S : Set (EdgeName (K := geometry))}
    {R Q : ActualCategory sheared S} (f : R ⟶ Q) :
    loopValue sheared (parameters Q.back).1 (parameters Q.back).2 =
      loopValue sheared (parameters R.back).1 (parameters R.back).2 +
        (f.1.toAdd.1 vertexS - linearAction sheared (f.1.toAdd.1 vertexS)) := by
  have h := gauge_loop sheared S f.1.toAdd R.back
  change loopValue sheared (parameters (f.1.toAdd +ᵥ R.back)).1
    (parameters (f.1.toAdd +ᵥ R.back)).2 = _ at h
  have hf : f.1.toAdd +ᵥ R.back = Q.back := f.2
  rw [hf] at h
  exact h

end AAT.AG.RelativeRepairComposition.W3ActualArrows
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W3ActualArrows
