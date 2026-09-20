import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomInvariantLocalComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullCompositionNative
import Formal.Util.AssertStandardAxioms

/-!
# Primitive composition of complete local Hom classes

Each constructor first builds the complete primitive point table, then
constructs coherent auxiliary rows and erases their choices. Comparison with
the original full Hom composite proves every remaining primitive law. Native
composition is used only after the local constructor is fixed.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)

section Representative

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .representative)
variable (hp : FullRepresentative.PointLaws s t p)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative)
variable (hq : FullRepresentative.PointLaws t r q)

/-- Compose complete representative local classes from primitive points and coherent auxiliary rows. -/
def representativeLocal : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading (assemble r).core.reading.invariantReading .representative :=
  InvariantWitness.composeLocal p q (composeRepresentative s t r p hp.package q hq.package hp.realization hp.coefficient)
    (fun _ _ => rfl) rfl

/-- The composed representative local class retains every directly composed original query. -/
theorem representativeLocal_table : (PackageAssembly.retained s.1 r.1 (representativeLocal s t r p hp q hq)).table =
    composeRepresentative s t r p hp.package q hq.package hp.realization hp.coefficient :=
  InvariantWitness.composeLocal_table p q _ _ _

/-- Every finite fragment of the representative composite is its original primitive table restricted to that fragment. -/
theorem representativeLocal_fragment (S : Finset (Query.{u, v} U .representative)) :
    InvariantWitness.fragment _ _ (representativeLocal s t r p hp q hq) S =
      TagChange.LocalTagTable.read (composeRepresentative s t r p hp.package q hq.package hp.realization hp.coefficient) S :=
  InvariantWitness.composeLocal_fragment p q _ _ _ S

/-- Primitive coherent composition gives exactly the reading of the original complete representative Hom composite. -/
theorem representativeLocal_eq_native : representativeLocal s t r p hp q hq =
    NativeReader.localRepresentative
      (GeometryTotalHom.comp (FullRepresentative.assembleHom s t p hp) (FullRepresentative.assembleHom t r q hq)) := by
  apply InvariantWitness.point_ext
  intro a
  exact (congrFun (representativeLocal_table s t r p hp q hq) a).trans
    ((congrFun (composeRepresentative_eq_full_native s t r p hp q hq) a).trans
      (NativeReader.point_localRepresentative _ a).symm)

/-- Complete representative primitive composition preserves every original object, core, and geometry law. -/
theorem representativeLocal_points : FullRepresentative.PointLaws s r (representativeLocal s t r p hp q hq) := by
  rw [representativeLocal_eq_native s t r p hp q hq]
  exact NativeReader.localRepresentative_points s r _

/-- Assembly of the primitive representative local composite restores the complete native Hom composite. -/
theorem representativeLocal_assemble :
    FullRepresentative.assembleHom s r (representativeLocal s t r p hp q hq) (representativeLocal_points s t r p hp q hq) =
      GeometryTotalHom.comp (FullRepresentative.assembleHom s t p hp) (FullRepresentative.assembleHom t r q hq) := by
  apply (NativeReader.representativeHomReadingEquiv s r).injective
  apply Subtype.ext
  exact (NativeReader.localRepresentative_read_assemble s r _ _).trans
    (representativeLocal_eq_native s t r p hp q hq)

end Representative

section Explicit

variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hp : FullExplicit.PointLaws s t p)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : FullExplicit.PointLaws t r q)

/-- Compose complete explicit local classes from primitive points and coherent auxiliary rows. -/
def explicitLocal : InvariantWitness.Local.{u, v}
    (assemble s).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit :=
  InvariantWitness.composeLocal p q (composeExplicit s t r p hp.package q hq.package hp.raw hq.raw hp.realization hq.realization hp.coefficient)
    (fun _ _ => rfl) rfl

/-- The composed explicit local class retains every directly composed original query. -/
theorem explicitLocal_table : (PackageAssembly.retained s.1 r.1 (explicitLocal s t r p hp q hq)).table =
    composeExplicit s t r p hp.package q hq.package hp.raw hq.raw hp.realization hq.realization hp.coefficient :=
  InvariantWitness.composeLocal_table p q _ _ _

/-- Every finite fragment of the explicit composite is its original primitive table restricted to that fragment. -/
theorem explicitLocal_fragment (S : Finset (Query.{u, v} U .explicit)) :
    InvariantWitness.fragment _ _ (explicitLocal s t r p hp q hq) S =
      TagChange.LocalTagTable.read (composeExplicit s t r p hp.package q hq.package hp.raw hq.raw hp.realization hq.realization hp.coefficient) S :=
  InvariantWitness.composeLocal_fragment p q _ _ _ S

/-- Primitive coherent composition gives exactly the reading of the original complete explicit Hom composite. -/
theorem explicitLocal_eq_native : explicitLocal s t r p hp q hq =
    NativeReader.localExplicit
      (ExplicitExactGeometryHom.comp (FullExplicit.assembleHom s t p hp) (FullExplicit.assembleHom t r q hq)) := by
  apply InvariantWitness.point_ext
  intro a
  exact (congrFun (explicitLocal_table s t r p hp q hq) a).trans
    ((congrFun (composeExplicit_eq_full_native s t r p hp q hq) a).trans
      (NativeReader.point_localExplicit _ a).symm)

/-- Complete explicit primitive composition preserves every original object, core, and geometry law. -/
theorem explicitLocal_points : FullExplicit.PointLaws s r (explicitLocal s t r p hp q hq) := by
  rw [explicitLocal_eq_native s t r p hp q hq]
  exact NativeReader.localExplicit_points s r _

/-- Assembly of the primitive explicit local composite restores the complete native Hom composite. -/
theorem explicitLocal_assemble :
    FullExplicit.assembleHom s r (explicitLocal s t r p hp q hq) (explicitLocal_points s t r p hp q hq) =
      ExplicitExactGeometryHom.comp (FullExplicit.assembleHom s t p hp) (FullExplicit.assembleHom t r q hq) := by
  apply (NativeReader.explicitHomReadingEquiv s r).injective
  apply Subtype.ext
  exact (NativeReader.localExplicit_read_assemble s r _ _).trans
    (explicitLocal_eq_native s t r p hp q hq)

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
