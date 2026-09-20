import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativePackage
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRealizationReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationComponents
import Formal.Util.AssertStandardAxioms

/-!
# Native realization recovery on the independent local quotient

The common reader satisfies the stage realization laws. Recovery of the core
map identifies the parameter of each actual stage assembler with the original
map, so the whole native realization supply is recovered in both modes.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Equal core maps identify representative realization assembly independently of proof witnesses. -/
theorem representativeRealization_assemble_heq {P Q : AATCorePackage U}
    (f g : PackageTotalHom P Q) (hf : f = g) (h : Table.{u, v} U .representative)
    (hm : RepresentativeRealization.Maps f h) (hn : RepresentativeRealization.Maps g h)
    (hp : RepresentativeRealization.NativePoints P Q h) :
    HEq (RepresentativeRealization.assemble f h hm hp) (RepresentativeRealization.assemble g h hn hp) := by
  cases hf
  rfl

/-- Equal core maps identify explicit realization assembly independently of proof witnesses. -/
theorem explicitRealization_assemble_heq {P Q : AATCorePackage U}
    (f g : PackageTotalHom P Q) (hf : f = g) (h : Table.{u, v} U .explicit)
    (hm : ExplicitRealization.Maps f h) (hn : ExplicitRealization.Maps g h)
    (hp : ExplicitRealization.PointLaws P.object Q.object h) :
    HEq (ExplicitRealization.assemble f h hm hp) (ExplicitRealization.assemble g h hn hp) := by
  cases hf
  rfl

variable (s t : ObjectData.{u, v} U)
variable (f : PackageTotalHom (assemble s).core (assemble t).core)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)

section Representative

variable (raw : RawQuery (assemble s).core.object (assemble t).core.object .representative → Bool)
variable (R : RealizationTransportSupply (assemble s).core (assemble t).core f)

/-- Every original directed realization satisfies the primitive stage rules on the actual invariant quotient. -/
theorem localWith_representativeRealization : GeometryComponents.RepresentativePoints s t
    (localWith .representative f a raw (representativeRealizationRead f R)) :=
  (GeometryComponents.representative_points_iff s t
    (localWith .representative f a raw (representativeRealizationRead f R))).1
      (readWith_representativeRealization_points f a raw R)

/-- The actual representative stage assembler restores the original directed supply after core recovery. -/
theorem localWith_representativeRealization_assemble_heq : HEq
    (GeometryComponents.representativeRealization s t
      (localWith .representative f a raw (representativeRealizationRead f R))
      (localWith_package s t .representative f a raw (representativeRealizationRead f R))
      (localWith_representativeRealization s t f a raw R)) R := by
  let p := localWith .representative f a raw (representativeRealizationRead f R)
  let hp := localWith_package s t .representative f a raw (representativeRealizationRead f R)
  have hb : GeometryComponents.base s t p hp = f :=
    localWith_package_assemble s t .representative f a raw (representativeRealizationRead f R)
  exact (representativeRealization_assemble_heq (GeometryComponents.base s t p hp) f hb
    (PackageAssembly.retained s.1 t.1 p).table (GeometryComponents.representative_maps s t p hp)
    (readWith_representativeRealization_maps f a raw R) (readWith_representativeRealization_points f a raw R)).trans
      (heq_of_eq (readWith_representativeRealization_assemble f a raw R))

end Representative

section Explicit

variable (raw : RawQuery (assemble s).core.object (assemble t).core.object .explicit → Bool)
variable (R : ExplicitRealizationTransportSupply (assemble s).core (assemble t).core f)

/-- Every original explicit realization satisfies all primitive stage rules on the same local quotient. -/
theorem localWith_explicitRealization : GeometryComponents.ExplicitPoints s t
    (localWith .explicit f a raw (explicitRealizationRead f R)) :=
  readWith_explicitRealization_points f a raw R

/-- The actual explicit stage assembler restores the whole original supply after core recovery. -/
theorem localWith_explicitRealization_assemble_heq : HEq
    (GeometryComponents.explicitRealization s t
      (localWith .explicit f a raw (explicitRealizationRead f R))
      (localWith_package s t .explicit f a raw (explicitRealizationRead f R))
      (localWith_explicitRealization s t f a raw R)) R := by
  let p := localWith .explicit f a raw (explicitRealizationRead f R)
  let hp := localWith_package s t .explicit f a raw (explicitRealizationRead f R)
  have hb : GeometryComponents.base s t p hp = f :=
    localWith_package_assemble s t .explicit f a raw (explicitRealizationRead f R)
  exact (explicitRealization_assemble_heq (GeometryComponents.base s t p hp) f hb
    (PackageAssembly.retained s.1 t.1 p).table (GeometryComponents.explicit_maps s t p hp)
    (readWith_explicitRealization_maps f a raw R) (readWith_explicitRealization_points f a raw R)).trans
      (heq_of_eq (readWith_explicitRealization_assemble f a raw R))

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
