import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeGeometryPreservation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRawReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawComponents
import Formal.Util.AssertStandardAxioms

/-!
# Both native raw meanings on the actual independent local quotient

Explicit raw point laws and recovery use the original candidate readings.
Core and coefficient recovery identify the parameters of the actual raw
assembler; the parameter comparison below changes only proved equal inputs.
Representative raw data retain their original strict equality, recovered from
the separate primitive representative laws rather than an explicit raw map.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Equal native base and coefficient parameters give the same raw assembly, independently of proof witnesses. -/
theorem explicitRaw_assemble_heq {G H : GeometryPackage.{u, v} U}
    (f g : PackageTotalHom G.core H.core) (a b : G.Coefficient →+* H.Coefficient)
    (hf : f = g) (ha : a = b) (h : Table.{u, v} U .explicit)
    (hm : ExplicitRaw.Maps f a h) (hn : ExplicitRaw.Maps g b h) (hp : ExplicitRaw.NativePoints G H h) :
    HEq (ExplicitRaw.assemble f a h hm hp) (ExplicitRaw.assemble g b h hn hp) := by
  cases hf
  cases ha
  rfl

variable (s t : ObjectData.{u, v} U)
variable (f : PackageTotalHom (assemble s).core (assemble t).core)
variable (a : (assemble s).Coefficient →+* (assemble t).Coefficient)

section Explicit

variable (R : RawAmbientRestrictionSystemExactMapAgainst (assemble s).site (assemble t).site
  (coreContextInverse f) a (assemble s).raw (assemble t).raw)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object .explicit → Bool)

/-- The original explicit raw map satisfies every primitive stage law on the actual invariant quotient. -/
theorem localWith_explicitRaw : GeometryComponents.ExplicitRawPoints s t
    (localWith .explicit f a (ExplicitRaw.readRaw f a R) realization) :=
  (GeometryComponents.explicitRaw_points_iff s t
    (localWith .explicit f a (ExplicitRaw.readRaw f a R) realization)).1
      (readWith_explicitRaw_points f a realization R)

/-- The actual stage assembler restores the whole native explicit raw map after core and coefficient recovery. -/
theorem localWith_explicitRaw_assemble_heq : HEq
    (GeometryComponents.explicitRaw s t (localWith .explicit f a (ExplicitRaw.readRaw f a R) realization)
      (localWith_package s t .explicit f a (ExplicitRaw.readRaw f a R) realization)
      (localWith_coefficient s t .explicit f a (ExplicitRaw.readRaw f a R) realization)
      (localWith_explicitRaw s t f a R realization)) R := by
  let p := localWith .explicit f a (ExplicitRaw.readRaw f a R) realization
  let hp := localWith_package s t .explicit f a (ExplicitRaw.readRaw f a R) realization
  let hc := localWith_coefficient s t .explicit f a (ExplicitRaw.readRaw f a R) realization
  have hb : GeometryComponents.base s t p hp = f :=
    localWith_package_assemble s t .explicit f a (ExplicitRaw.readRaw f a R) realization
  have ha : GeometryComponents.coefficientMap s t p hc = a :=
    localWith_coefficient_assemble s t .explicit f a (ExplicitRaw.readRaw f a R) realization
  exact (explicitRaw_assemble_heq (GeometryComponents.base s t p hp) f
    (GeometryComponents.coefficientMap s t p hc) a hb ha (PackageAssembly.retained s.1 t.1 p).table
    (GeometryComponents.explicitRaw_maps s t p hp hc) (readWith_explicitRaw_maps f a _ realization)
    (readWith_explicitRaw_points f a realization R)).trans
      (heq_of_eq (readWith_explicitRaw_assemble f a realization R))

end Explicit

section Representative

variable (raw : RawQuery (assemble s).core.object (assemble t).core.object .representative → Bool)
variable (realization : RealizationQuery (assemble s).core.object (assemble t).core.object .representative → Bool)

/-- The original representative raw equality supplies all primitive stage conditions on the same local quotient. -/
theorem localWith_representativeRaw (hr : (assemble t).raw = rawTransport f a) :
    GeometryComponents.RepresentativeRawPoints s t (localWith .representative f a raw realization) := by
  have hm : RepresentativeRaw.Maps f a
      (PackageAssembly.retained s.1 t.1 (localWith .representative f a raw realization)).table :=
    { context := readWith_context_backward_point_iff .representative f a raw realization
      coefficient := readWith_coefficient_point_iff .representative f a raw realization }
  exact (GeometryComponents.representativeRaw_points_iff s t (localWith .representative f a raw realization)).1
    (RepresentativeRaw.points_of_native f a _ hm hr)

end Representative

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
