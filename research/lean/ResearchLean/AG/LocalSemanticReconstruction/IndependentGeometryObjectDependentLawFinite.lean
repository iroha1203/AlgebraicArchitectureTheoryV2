import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentRawLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for one active object's dependent laws

The six dependent stages are collected only after each stage has been replaced
by its exact family of closed finite formula instances.  Later stages use the
law proofs reconstructed from earlier instance families; no completed
dependent-law certificate is stored in the aggregate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v

variable {U : AtomCarrier.{u}}

abbrev contextFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hi : Context.Instances t ha A hA) :
    IndependentGeometryPrimitive.ContextLaws (rows t ha A hA) :=
  (Context.contextLaws_iff_instances t ha A hA).2 hi

abbrev equationFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hi : Context.Instances t ha A hA)
    (hj : Equation.Instances t ha A hA (contextFromInstances t ha A hA hi)) :
    IndependentGeometryPrimitive.EquationLaws (rows t ha A hA)
      (contextFromInstances t ha A hA hi) :=
  (Equation.equationLaws_iff_instances t ha A hA
    (contextFromInstances t ha A hA hi)).2 hj

abbrev coverageFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hi : Context.Instances t ha A hA)
    (hj : Equation.Instances t ha A hA (contextFromInstances t ha A hA hi))
    (hv : Coverage.Instances t ha A hA hf (contextFromInstances t ha A hA hi)
      (equationFromInstances t ha A hA hi hj)) :
    IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA)
      (contextFromInstances t ha A hA hi)
      (equationFromInstances t ha A hA hi hj) :=
  (Coverage.coverageLaws_iff_instances t ha A hA hf
    (contextFromInstances t ha A hA hi)
    (equationFromInstances t ha A hA hi hj)).2 hv

abbrev overlapFromInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hi : Context.Instances t ha A hA)
    (ho : Overlap.Instances t ha A hA) :
    IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA)
      (contextFromInstances t ha A hA hi) :=
  (Overlap.overlapLaws_iff_instances t ha A hA
    (contextFromInstances t ha A hA hi)).2 ho

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) : Prop where
  context : Context.Instances t ha A hA
  equation : Equation.Instances t ha A hA
    (contextFromInstances t ha A hA context)
  circuit : Circuit.Instances t ha A hA
    (contextFromInstances t ha A hA context)
    (equationFromInstances t ha A hA context equation).choose
  coverage : Coverage.Instances t ha A hA hf
    (contextFromInstances t ha A hA context)
    (equationFromInstances t ha A hA context equation)
  overlap : Overlap.Instances t ha A hA
  raw : Raw.Instances t ha A hA hf
    (contextFromInstances t ha A hA context)
    (equationFromInstances t ha A hA context equation)
    (coverageFromInstances t ha A hA hf context equation coverage)
    (overlapFromInstances t ha A hA context overlap)

theorem dependentLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :
    IndependentGeometryPrimitive.DependentLaws t hf (rows t ha A hA) ↔
      Instances t ha A hA hf := by
  constructor
  · intro hd
    let hi : Context.Instances t ha A hA :=
      (Context.contextLaws_iff_instances t ha A hA).1 hd.context
    let hc := contextFromInstances t ha A hA hi
    let hj : Equation.Instances t ha A hA hc :=
      (Equation.equationLaws_iff_instances t ha A hA hc).1
        (by simpa only [Subsingleton.elim hd.context hc] using hd.equation)
    let he := equationFromInstances t ha A hA hi hj
    let hk : Circuit.Instances t ha A hA hc he.choose :=
      (Circuit.typedLawful_iff_instances t ha A hA hc he.choose).1
        (by simpa only [Subsingleton.elim hd.context hc,
          Subsingleton.elim hd.equation he] using hd.circuit)
    let hv : Coverage.Instances t ha A hA hf hc he :=
      (Coverage.coverageLaws_iff_instances t ha A hA hf hc he).1
        (by simpa only [Subsingleton.elim hd.context hc,
          Subsingleton.elim hd.equation he] using hd.coverage)
    let ho : Overlap.Instances t ha A hA :=
      (Overlap.overlapLaws_iff_instances t ha A hA hc).1
        (by simpa only [Subsingleton.elim hd.context hc] using hd.overlap)
    refine ⟨hi, hj, hk, hv, ho, ?_⟩
    apply (Raw.rawLaws_iff_instances t ha A hA hf hc he
      (coverageFromInstances t ha A hA hf hi hj hv)
      (overlapFromInstances t ha A hA hi ho)).1
    simpa only [Subsingleton.elim hd.context hc,
      Subsingleton.elim hd.equation he,
      Subsingleton.elim hd.coverage (coverageFromInstances t ha A hA hf hi hj hv),
      Subsingleton.elim hd.overlap (overlapFromInstances t ha A hA hi ho)] using hd.raw
  · intro hi
    let hc := contextFromInstances t ha A hA hi.context
    let he := equationFromInstances t ha A hA hi.context hi.equation
    let hv := coverageFromInstances t ha A hA hf hi.context hi.equation hi.coverage
    let ho := overlapFromInstances t ha A hA hi.context hi.overlap
    exact {
      context := hc
      equation := he
      circuit := (Circuit.typedLawful_iff_instances t ha A hA hc he.choose).2 hi.circuit
      coverage := hv
      overlap := ho
      raw := (Raw.rawLaws_iff_instances t ha A hA hf hc he hv ho).2 hi.raw }

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
