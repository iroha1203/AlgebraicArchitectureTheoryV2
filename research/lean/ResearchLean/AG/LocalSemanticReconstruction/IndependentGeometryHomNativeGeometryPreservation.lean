import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativePackage
import Formal.Util.AssertStandardAxioms

/-!
# Native coverage, overlap, and coefficient laws on the local quotient

Core-package recovery identifies the base used by the existing geometry
comparison APIs with the original native base. Those APIs supply the primitive
coverage and overlap laws. The coefficient reader is the original directed ring
hom graph and supplies its operation laws without an invertibility requirement.
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

/-- Every native coverage field supplies the original independent coverage laws on the retained local table. -/
theorem localWith_coverage (c : CoverageTransport (assemble s) (assemble t) f) :
    GeometryComponents.CoveragePoints s t (localWith mode f a raw realization) := by
  have hm := GeometryComponents.coverage_maps s t (localWith mode f a raw realization)
    (localWith_package s t mode f a raw realization)
  have hb : GeometryComponents.base s t (localWith mode f a raw realization)
      (localWith_package s t mode f a raw realization) = f := localWith_package_assemble s t mode f a raw realization
  rw [hb] at hm
  exact (GeometryComponents.coverage_points_iff s t (localWith mode f a raw realization)).1
    (Coverage.points_of_native f _ hm c)

/-- The original native overlap comparison supplies both primitive refinement directions on the local table. -/
theorem localWith_overlap (o : OverlapTransport (assemble s) (assemble t) f) :
    GeometryComponents.OverlapPoints s t (localWith mode f a raw realization) := by
  have hm := GeometryComponents.overlap_maps s t (localWith mode f a raw realization)
    (localWith_package s t mode f a raw realization)
  have hb : GeometryComponents.base s t (localWith mode f a raw realization)
      (localWith_package s t mode f a raw realization) = f := localWith_package_assemble s t mode f a raw realization
  rw [hb] at hm
  exact (GeometryComponents.overlap_points_iff s t (localWith mode f a raw realization)).1
    (Overlap.points_of_native f _ hm o)

/-- An arbitrary original directed coefficient hom supplies every primitive ring-operation law. -/
theorem localWith_coefficient : GeometryComponents.CoefficientPoints s t (localWith mode f a raw realization) :=
  Coefficient.pointLaws_of_native s.2.2.1.val t.2.2.1.val s.2.2.1.property.choose t.2.2.1.property.choose
    s.2.2.1.property.choose_spec t.2.2.1.property.choose_spec
    (PackageAssembly.retained s.1 t.1 (localWith mode f a raw realization)).table a
    (readWith_coefficient mode f a raw realization)

/-- Coefficient assembly on the actual local quotient restores the original ring hom in full. -/
theorem localWith_coefficient_assemble : GeometryComponents.coefficientMap s t (localWith mode f a raw realization)
    (localWith_coefficient s t mode f a raw realization) = a :=
  Coefficient.assemble_eq_native s.2.2.1.val t.2.2.1.val s.2.2.1.property.choose t.2.2.1.property.choose
    s.2.2.1.property.choose_spec t.2.2.1.property.choose_spec
    (PackageAssembly.retained s.1 t.1 (localWith mode f a raw realization)).table a
    (readWith_coefficient mode f a raw realization)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
