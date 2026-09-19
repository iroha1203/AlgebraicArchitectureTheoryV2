import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoreTableAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentOverlapCandidateReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentCoveragePrimitiveReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidateReadings
import Formal.Util.AssertStandardAxioms

/-!
# Complete geometry objects assembled from dependent primitive tables

Implementation notes: native dependent sigma views are comparison devices,
not local data fields. The output table stages contain primitive core readings,
coverage predicates, primitive overlap contexts, primitive coefficient rings,
and the previously verified raw point tables. Reindexing the stages along their
component equivalences retains all native dependencies and both round trips.

This is the dependent object-assembly bridge for the independent verification.
IndependentGeometryPrimitiveAssembly connects the common realization-independent
query declaration to these stages with both inverse laws. The candidate raw
and overlap indices are fixed before their site and preorder are assembled.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryTableAssembly

universe u v

open Site LawAlgebra

variable {U : AtomCarrier.{u}}

/-- Primitive coverage and overlap tables on a complete generated native core. -/
abbrev GeometryData (P : AATCorePackage U) :=
  {t : IndependentCoveragePrimitive.Table P.object //
    IndependentCoveragePrimitive.IsTyped P.equationSystem P.algebra.signatureReading t} ×
  {t : IndependentOverlapCandidate.Table P.object //
    IndependentOverlapCandidate.IsTyped t ∧
      IndependentOverlapCandidate.IsLawful P.contextPreorder t}

/-- Source-only view of the two dependent native geometry fields. -/
def geometryNativeEquiv (P : AATCorePackage U) :
    SelectedGeometryReading P ≃
      CoverageRequirements P.object P.equationSystem P.algebra.signatureReading ×
        ContextOverlapPullback P.contextPreorder where
  toFun g := ⟨g.requirements, g.overlap⟩
  invFun g := ⟨g.1, g.2⟩
  left_inv g := by cases g; rfl
  right_inv g := by cases g; rfl

/-- Every native geometry selection is assembled from coverage points and primitive overlap contexts. -/
noncomputable def geometryEquiv (P : AATCorePackage U) : SelectedGeometryReading P ≃ GeometryData P :=
  (geometryNativeEquiv P).trans
    (Equiv.prodCongr
      (IndependentCoveragePrimitive.readingEquiv P.equationSystem P.algebra.signatureReading)
      (IndependentOverlapCandidate.readingEquiv P.contextPreorder))

/-- Construct the native selected geometry from its two primitive table families. -/
noncomputable def geometry {P : AATCorePackage U} (g : GeometryData P) : SelectedGeometryReading P :=
  (geometryEquiv P).symm g

/-- The native site is generated from the assembled core and primitive selected geometry. -/
noncomputable def site {P : AATCorePackage U} (g : GeometryData P) : AATSite P.object :=
  (geometry g).toAATSite

/-- Primitive coefficient carrier and ring-operation table, at the original coefficient universe. -/
abbrev CoefficientData :=
  {t : IndependentRingPrimitive.Carrier.Table.{v} //
    ∃ ht : IndependentRingPrimitive.Carrier.IsTyped t,
      IndependentRingPrimitive.Carrier.IsLawful t ht}

/-- Construct the coefficient carrier and complete native ring from primitive operations. -/
noncomputable def coefficient (r : CoefficientData.{v}) : IndependentRingPrimitive.Carrier.Native.{v} :=
  IndependentRingPrimitive.Carrier.assemble r.val r.property.choose r.property.choose_spec

/-- Raw candidate indices precede site/ring selection; their local laws use the generated stages. -/
abbrev RawData {A : ArchitectureObject U} (S : AATSite A) (r : CoefficientData.{v}) :=
  letI := (coefficient r).2
  IndependentRawCandidate.LawfulTable S (coefficient r).1

/-- Primitive coefficient and raw stages at one generated site. -/
abbrev RingRawData {A : ArchitectureObject U} (S : AATSite A) :=
  (r : CoefficientData.{v}) × RawData S r

/-- Source-only native ring and raw-system dependent view. -/
abbrev NativeRingRawData {A : ArchitectureObject U} (S : AATSite A) :=
  (r : IndependentRingPrimitive.Carrier.Native.{v}) ×
    (letI := r.2; RawAmbientRestrictionSystem S r.1)

/-- Native ring and raw systems are both constructed, including all dependent coordinate carriers. -/
noncomputable def ringRawEquiv {A : ArchitectureObject U} (S : AATSite A) :
    NativeRingRawData.{u, v} S ≃ RingRawData.{u, v} S :=
  (Equiv.sigmaCongrRight fun (r : IndependentRingPrimitive.Carrier.Native.{v}) =>
    letI : CommRing r.1 := r.2
    IndependentRawCandidate.rawTableEquiv S r.1).trans
      (Equiv.sigmaCongrLeft' IndependentRingPrimitive.Carrier.readingEquiv)

/-- Primitive selected geometry, coefficient, and raw stages on one native generated core. -/
abbrev GeometryTailData (P : AATCorePackage U) :=
  (g : GeometryData P) × RingRawData.{u, v} (site g)

/-- Complete dependent object tables, with no native core, geometry, ring, or raw system as a field. -/
abbrev ObjectData (U : AtomCarrier.{u}) :=
  (p : IndependentCoreTableAssembly.PackageData U) ×
    GeometryTailData.{u, v} (IndependentCoreTableAssembly.assemblePackage p)

/-- Source-only view exposing the native dependencies of the full ReadingCore. -/
def nativeEquiv : ReadingCore.{u, v} U ≃
    (p : AATCorePackage U) × (g : SelectedGeometryReading p) × NativeRingRawData.{u, v} g.toAATSite where
  toFun G := ⟨G.core, G.geometry, ⟨G.Coefficient, G.coefficientCommRing⟩, G.raw⟩
  invFun d :=
    { core := d.1
      geometry := d.2.1
      Coefficient := d.2.2.1.1
      coefficientCommRing := d.2.2.1.2
      raw := d.2.2.2 }
  left_inv G := by cases G; rfl
  right_inv d := by rcases d with ⟨p, g, ⟨k, r⟩, raw⟩; rfl

/-- All native geometry-tail fields are reconstructed from their dependent primitive tables. -/
noncomputable def geometryTailEquiv (P : AATCorePackage U) :
    ((g : SelectedGeometryReading P) × NativeRingRawData.{u, v} g.toAATSite) ≃
      GeometryTailData.{u, v} P :=
  (Equiv.sigmaCongrRight fun g => ringRawEquiv g.toAATSite).trans
    (Equiv.sigmaCongrLeft' (geometryEquiv P))

/-- Complete native geometry objects, including raw, have exact dependent primitive-table presentations. -/
noncomputable def objectEquiv : ReadingCore.{u, v} U ≃ ObjectData.{u, v} U :=
  nativeEquiv.trans
    ((Equiv.sigmaCongrRight fun P => geometryTailEquiv P).trans
      (Equiv.sigmaCongrLeft' IndependentCoreTableAssembly.packageEquiv))

/-- Assemble every field of a complete native geometry object from the primitive stages. -/
noncomputable def assemble (d : ObjectData.{u, v} U) : ReadingCore.{u, v} U := objectEquiv.symm d

/-- Read all fields of a complete native geometry object into their primitive stages. -/
noncomputable def read (G : ReadingCore.{u, v} U) : ObjectData.{u, v} U := objectEquiv G

/-- Complete native objects, including all raw data, are recovered exactly. -/
theorem assemble_read (G : ReadingCore.{u, v} U) : assemble (read G) = G := objectEquiv.left_inv G

/-- Every primitive table is restored after complete object assembly. -/
theorem read_assemble (d : ObjectData.{u, v} U) : read (assemble d) = d := objectEquiv.right_inv d

/-- Full object readings separate every native field and every dependent raw presentation. -/
theorem read_injective : Function.Injective (read.{u, v} (U := U)) := objectEquiv.injective

/-- The assembled object's core is the actual primitive core assembly of its first stage. -/
theorem core_assemble (d : ObjectData.{u, v} U) :
    (assemble d).core = IndependentCoreTableAssembly.assemblePackage d.1 := rfl

/-- The assembled object's selected geometry is generated from its primitive geometry stage. -/
theorem geometry_assemble (d : ObjectData.{u, v} U) : (assemble d).geometry = geometry d.2.1 := rfl

/-- The assembled coefficient carrier is the selected primitive carrier reference. -/
theorem coefficient_assemble (d : ObjectData.{u, v} U) :
    (assemble d).Coefficient = (coefficient d.2.2.1).1 := rfl

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryTableAssembly

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryTableAssembly
