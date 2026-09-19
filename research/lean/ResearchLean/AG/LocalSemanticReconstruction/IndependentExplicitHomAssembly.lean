import ResearchLean.AG.LocalSemanticReconstruction.IndependentExplicitRawReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentExplicitRealizationReadings
import ResearchLean.AG.LocalSemanticReconstruction.CompleteGeometryDirectCategory
import Formal.Util.AssertStandardAxioms

/-!
# All explicit geometry Homs from primitive graph and point families

Implementation notes: the base and coefficient maps are constructed from the
reviewed primitive graph APIs. Raw coordinate/local-data/relation graphs obey
point polynomial and variable-image equations. Realization tables retain the
actual context-morphism actions. Coverage is pointwise and overlap uses two
order comparisons. Native dependent sigma views occur only in the comparison
proof; no completed Hom is stored in the primitive data.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentExplicitHom

noncomputable section

universe u v

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction
open CompleteGeometryGraphAssembly AlgebraicGraphCoherence

variable {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}

/-- The accepted complete package graph assembler as an equivalence of all base maps. -/
def packageEquiv : PackageTotalHom G.core H.core ≃ PackageGraphCode G H where
  toFun := PackageGraphCode.read
  invFun := PackageGraphCode.assemble
  left_inv := PackageGraphCode.assemble_read
  right_inv := PackageGraphCode.read_assemble

/-- Raw coordinate and relation graph data with their point equations. -/
abbrev RawData (f : PackageTotalHom G.core H.core) (h : G.Coefficient →+* H.Coefficient) :=
  {d : IndependentExplicitRaw.Data (coreContextInverse f) G.raw H.raw //
    IndependentExplicitRaw.IsLawful h d}

/-- Actual-context realization points with local inverse, reading, and naturality laws. -/
abbrev RealizationData (f : PackageTotalHom G.core H.core) :=
  {t : IndependentExplicitRealization.Table f // IndependentExplicitRealization.IsLawful t}

/-- Primitive dependent graph and point families for every computational Hom component. -/
abbrev Data (G H : GeometryPackage.{u, v} U) :=
  (f : PackageGraphCode G H) × (h : RingHomGraphCode G.Coefficient H.Coefficient) ×
    RawData f.assemble h.assemble × RealizationData f.assemble

/-- Source-only view of the native computational components, used to prove both inverses. -/
abbrev NativeData (G H : GeometryPackage.{u, v} U) :=
  (f : PackageTotalHom G.core H.core) × (h : G.Coefficient →+* H.Coefficient) ×
    RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) h G.raw H.raw ×
      ExplicitRealizationTransportSupply G.core H.core f

/-- Componentwise primitive reconstruction respects the original dependent indices. -/
def dataEquiv : NativeData G H ≃ Data G H :=
  (Equiv.sigmaCongrRight fun f =>
    (Equiv.sigmaCongrRight fun h =>
      Equiv.prodCongr (IndependentExplicitRaw.readingEquiv h)
        (IndependentExplicitRealization.readingEquiv f)).trans
          (Equiv.sigmaCongrLeft' RingHomGraphCode.equivRingHom.symm)).trans
    (Equiv.sigmaCongrLeft' packageEquiv)

/-- Decoding the first primitive stage recovers the actual native base map. -/
theorem base_dataEquiv (d : NativeData G H) : (dataEquiv d).1.assemble = d.1 :=
  PackageGraphCode.assemble_read d.1

/-- Decoding the coefficient graph recovers the native directed ring map. -/
theorem coefficient_dataEquiv (d : NativeData G H) : (dataEquiv d).2.1.assemble = d.2.1 := by
  exact congrArg (fun x : NativeData G H => x.2.1) (dataEquiv.symm_apply_apply d)

/-- The remaining laws are the nine coverage implications and the two overlap order comparisons. -/
structure GeometryLaws (f : PackageTotalHom G.core H.core) : Prop where
  /-- Preserve every native coverage predicate at its original arguments. -/
  coverage : CoverageTransport G H f
  /-- The transported source overlap refines the target overlap. -/
  overlapForward : ∀ base left right,
    overlapSource f base left right ≤ overlapTarget base left right
  /-- The target overlap refines the transported source overlap. -/
  overlapBackward : ∀ base left right,
    overlapTarget base left right ≤ overlapSource f base left right

/-- Native full Homs expose computational components and exactly the remaining point laws. -/
def nativeEquiv : ExplicitExactGeometryHom G H ≃
    {d : NativeData G H // GeometryLaws d.1} where
  toFun f := ⟨⟨f.base, f.coefficientHom, f.raw, f.realization⟩,
    ⟨f.coverage, (fun b l r => (f.overlap.overlapIso b l r).hom.le),
      (fun b l r => (f.overlap.overlapIso b l r).inv.le)⟩⟩
  invFun d :=
    { base := d.val.1
      coverage := d.property.coverage
      overlap := assembleOverlap d.property.overlapForward d.property.overlapBackward
      coefficientHom := d.val.2.1
      raw := d.val.2.2.1
      realization := d.val.2.2.2 }
  left_inv _ := ExplicitExactGeometryHom.ext rfl rfl HEq.rfl HEq.rfl
  right_inv _ := Subtype.ext rfl

/-- Lawful primitive data for all explicit geometry Homs. -/
abbrev Code (G H : GeometryPackage.{u, v} U) :=
  {d : Data G H // GeometryLaws d.1.assemble}

/-- Every native explicit Hom corresponds to exactly one lawful primitive graph and point family. -/
def homEquiv : ExplicitExactGeometryHom G H ≃ Code G H :=
  nativeEquiv.trans (Equiv.subtypeEquiv dataEquiv (fun d => by
    change GeometryLaws d.1 ↔ GeometryLaws (dataEquiv d).1.assemble
    rw [base_dataEquiv]))

/-- Assemble every native explicit Hom component from its primitive data and point laws. -/
def assemble (d : Code G H) : ExplicitExactGeometryHom G H := homEquiv.symm d

/-- Read all components, including raw transport and every actual context-morphism action. -/
def read (f : ExplicitExactGeometryHom G H) : Code G H := homEquiv f

/-- Assembly recovers all native explicit Homs, without any invertibility assumption on coefficients. -/
theorem assemble_read (f : ExplicitExactGeometryHom G H) : assemble (read f) = f :=
  homEquiv.left_inv f

/-- Re-reading recovers every primitive graph and every realization point. -/
theorem read_assemble (d : Code G H) : read (assemble d) = d := homEquiv.right_inv d

/-- Equal primitive readings imply equality of the complete Hom, including non-object components. -/
theorem read_injective : Function.Injective (read (G := G) (H := H)) := homEquiv.injective

/-- The assembled base is the reviewed package graph assembly. -/
theorem base_assemble (d : Code G H) : (assemble d).base = d.val.1.assemble := rfl

/-- The assembled coefficient action is exactly the directed primitive graph action. -/
theorem coefficient_assemble (d : Code G H) :
    (assemble d).coefficientHom = d.val.2.1.assemble := rfl

/-- The raw component is built from the coordinate/relation graphs and variable equations. -/
theorem raw_assemble (d : Code G H) :
    (assemble d).raw = IndependentExplicitRaw.assemble d.val.2.1.assemble
      d.val.2.2.1.val d.val.2.2.1.property := rfl

/-- The realization component is built from the actual-context point table and its local laws. -/
theorem realization_assemble (d : Code G H) :
    (assemble d).realization = IndependentExplicitRealization.assemble
      d.val.2.2.2.val d.val.2.2.2.property := rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentExplicitHom

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentExplicitHom
