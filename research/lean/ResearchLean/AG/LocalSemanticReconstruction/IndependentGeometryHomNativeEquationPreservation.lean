import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRecovery
import Formal.Util.AssertStandardAxioms

/-!
# Native equation preservation on independent primitive stages

The recovered context and observable family are compared together before
transporting native naturality, violation, and residual equations. This avoids
changing any dependent carrier or adding a preservation certificate to local
data. The existing primitive/native comparison theorems then give the original
point conditions on every candidate row, including inactive candidates.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t : ObjectData.{u, v} U) (mode : Mode)
variable (f : PackageTotalHom (assemble s).core (assemble t).core)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)
variable (raw : RawQuery (assemble s).core.object (assemble t).core.object mode → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object mode → Bool)

/-- The original native role equation supplies every primitive candidate-index role comparison. -/
theorem readWith_role_preservation : EquationLaws.RolePoints s.1.val.2.2.1.val t.1.val.2.2.1.val
    (readWith mode f a raw realization) := by
  have he : EquationLaws.equationEquiv s.1.val.2.2.1.val t.1.val.2.2.1.val
      (readWith mode f a raw realization) (readWith_equation_rows mode f a raw realization) = f.upper.equationEquiv :=
    readWith_equation_assemble mode f a raw realization
  apply EquationLaws.role_points_of_eq s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose (readWith mode f a raw realization)
    (readWith_equation_rows mode f a raw realization)
  rw [he]
  exact f.upper.equationTransport.role_eq

/-- Native observable restriction naturality supplies every primitive restriction-square instance. -/
theorem readWith_observable_naturality : ObservableNatural.PointLaws s.1.val.2.2.1.val t.1.val.2.2.1.val
    (readWith mode f a raw realization) := by
  have he := congrArg
    (fun d : (Σ E : ContextCategoryObject (assemble s).core.contextPreorder ≌
        ContextCategoryObject (assemble t).core.contextPreorder,
        ∀ W, (assemble s).core.equationSystem.Observable W ≃+*
          (assemble t).core.equationSystem.Observable (E.functor.obj W)) =>
      ∀ (W V : ContextCategoryObject (assemble s).core.contextPreorder) (g : W ⟶ V)
        (x : (assemble s).core.equationSystem.Observable V),
        d.2 W ((assemble s).core.equationSystem.restrict g x) =
          (assemble t).core.equationSystem.restrict (d.1.functor.map g) (d.2 V x))
    (readWith_contextObservable_eq mode f a raw realization)
  have hn := Eq.mpr he (fun W V g x => f.upper.equationTransport.observable_naturality (W := W) (V := V) g x)
  apply (ObservableNatural.points_iff_nativeNaturality s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose
    s.1.val.2.2.1.property.choose_spec t.1.val.2.2.1.property.choose_spec
    (readWith mode f a raw realization) (readWith_context_rows mode f a raw realization)
    (readWith_observable_rows mode f a raw realization)).2
  intro ho W V g x
  exact hn W V g x

/-- Native symbolic-violation preservation yields every primitive candidate-context and carrier comparison. -/
theorem readWith_violation_preservation : EquationLaws.ViolationPoints s.1.val.2.2.1.val t.1.val.2.2.1.val
    (readWith mode f a raw realization) := by
  have he := congrArg
    (fun d : (Σ E : ContextCategoryObject (assemble s).core.contextPreorder ≌
        ContextCategoryObject (assemble t).core.contextPreorder,
        ∀ W, (assemble s).core.equationSystem.Observable W ≃+*
          (assemble t).core.equationSystem.Observable (E.functor.obj W)) =>
      ∀ W i x, d.2 W ((assemble s).core.equationSystem.violationCoordinate W i x) =
        (assemble t).core.equationSystem.violationCoordinate (d.1.functor.obj W)
          (f.upper.equationEquiv i) (f.upper.atomEquiv x))
    (readWith_contextObservable_eq mode f a raw realization)
  have hn := Eq.mpr he f.upper.equationTransport.violationCoordinate_eq
  have hi : EquationLaws.equationEquiv s.1.val.2.2.1.val t.1.val.2.2.1.val
      (readWith mode f a raw realization) (readWith_equation_rows mode f a raw realization) = f.upper.equationEquiv :=
    readWith_equation_assemble mode f a raw realization
  apply EquationLaws.violation_points_of_native s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose (readWith mode f a raw realization)
    (readWith_equation_rows mode f a raw realization)
    s.1.val.2.2.1.property.choose_spec t.1.val.2.2.1.property.choose_spec
    (readWith_context_rows mode f a raw realization) (readWith_atom_rows mode f a raw realization).upper
    (readWith_observable_rows mode f a raw realization)
  intro W i x
  rw [hi, readWith_atom_assemble mode f a raw realization]
  exact hn W i x

/-- Native residual preservation supplies the primitive square including the original directed object action. -/
theorem readWith_residual_preservation : EquationLaws.ResidualPoints s.1.val.2.2.1.val t.1.val.2.2.1.val
    (readWith mode f a raw realization) := by
  have he := congrArg
    (fun d : (Σ E : ContextCategoryObject (assemble s).core.contextPreorder ≌
        ContextCategoryObject (assemble t).core.contextPreorder,
        ∀ W, (assemble s).core.equationSystem.Observable W ≃+*
          (assemble t).core.equationSystem.Observable (E.functor.obj W)) =>
      ∀ W M i x, d.2 W ((assemble s).core.equationSystem.equationResidual W M i x) =
        (assemble t).core.equationSystem.equationResidual (d.1.functor.obj W)
          (f.upper.objectMap M) (f.upper.equationEquiv i) (f.upper.atomEquiv x))
    (readWith_contextObservable_eq mode f a raw realization)
  have hn := Eq.mpr he f.upper.equationTransport.equationResidual_eq
  have hi : EquationLaws.equationEquiv s.1.val.2.2.1.val t.1.val.2.2.1.val
      (readWith mode f a raw realization) (readWith_equation_rows mode f a raw realization) = f.upper.equationEquiv :=
    readWith_equation_assemble mode f a raw realization
  apply EquationLaws.residual_points_of_native s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.1.property.choose t.1.val.2.2.1.property.choose (readWith mode f a raw realization)
    (readWith_equation_rows mode f a raw realization)
    s.1.val.2.2.1.property.choose_spec t.1.val.2.2.1.property.choose_spec
    (readWith_context_rows mode f a raw realization) (readWith_atom_rows mode f a raw realization).upper
    (readWith_observable_rows mode f a raw realization) (readWith_object_rows mode f a raw realization)
  intro W M i x
  rw [hi, readWith_atom_assemble mode f a raw realization, readWith_object_assemble mode f a raw realization]
  exact hn W M i x

/-- Native finite detector-code transport gives every primitive detector query comparison. -/
theorem readWith_detector_preservation : Detector.PointLaws s.1.val.2.2.2.val t.1.val.2.2.2.val
    (readWith mode f a raw realization) (assemble s).core.object (assemble t).core.object := by
  have hi : EquationLaws.equationEquiv s.1.val.2.2.1.val t.1.val.2.2.1.val
      (readWith mode f a raw realization) (readWith_equation_rows mode f a raw realization) = f.upper.equationEquiv :=
    readWith_equation_assemble mode f a raw realization
  apply Detector.points_of_native (readWith mode f a raw realization)
    (readWith_atom_rows mode f a raw realization).upper s.1.val.2.2.1.val t.1.val.2.2.1.val
    s.1.val.2.2.2.val t.1.val.2.2.2.val s.1.val.2.2.2.property.choose t.1.val.2.2.2.property.choose
    (readWith_equation_rows mode f a raw realization)
  rw [hi, readWith_atom_assemble mode f a raw realization]
  exact f.upper.detectorCode_eq

/-- All four native equation-preservation fields imply the independent primitive equation point laws together. -/
theorem readWith_equation_preservation : EquationAssembly.PointLaws s.1.val.2.2.1.val t.1.val.2.2.1.val
    (readWith mode f a raw realization) where
  role := readWith_role_preservation s t mode f a raw realization
  naturality := readWith_observable_naturality s t mode f a raw realization
  violation := readWith_violation_preservation s t mode f a raw realization
  residual := readWith_residual_preservation s t mode f a raw realization

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
