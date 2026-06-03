import Formal.Arch.AAT.GeneratedSignature
import Formal.Arch.Signature.AnalyticRepresentation

namespace Formal.Arch
namespace AAT

universe u v

/--
Witness type for the generated analytic representation.

The current generated representation aggregates the selected required Signature
axis failure.  It intentionally does not claim to cover every possible
semantic, runtime, empirical, or extractor-side witness.
-/
inductive GeneratedAnalyticWitness where
  | requiredSignatureAxes
  deriving DecidableEq, Repr

namespace GeneratedArchitectureLawModel

/--
Analytic representation generated from Atom-generated law models.

The state space is `GeneratedArchitectureLawModel object`, so the representation
map cannot be supplied from a hand-authored `ArchitectureLawModel`.  It sends
each generated model to `signatureOfGenerated`.
-/
noncomputable def generatedAnalyticRepresentation
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)] :
    AnalyticRepresentation
      (GeneratedArchitectureLawModel object)
      ArchitectureSignature.ArchitectureSignatureV1
      GeneratedAnalyticWitness where
  represent := fun model => model.signatureOfGenerated
  structuralZero := fun model =>
    ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel
  analyticZero := fun sig =>
    ArchitectureSignature.RequiredSignatureAxesZero sig
  structuralObstruction := fun model _ =>
    ¬ ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel
  analyticObstruction := fun sig _ =>
    ¬ ArchitectureSignature.RequiredSignatureAxesZero sig
  coverageAssumptions := True
  witnessCompleteness := True
  semanticContractCoverage := True
  nonConclusions := True

/-- The generated analytic representation records its non-conclusion boundary. -/
theorem generatedAnalyticRepresentation_nonConclusions
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    (generatedAnalyticRepresentation (object := object)).nonConclusions := by
  trivial

/-- Generated lawfulness is preserved as generated analytic zero. -/
theorem generatedAnalyticRepresentation_zeroPreserving
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    AnalyticRepresentation.ZeroPreserving
      (generatedAnalyticRepresentation (object := object)) := by
  intro model hLawful
  exact
    (model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mp
      hLawful

/-- Generated analytic zero reflects generated lawfulness under the recorded
coverage fields of the generated representation. -/
theorem generatedAnalyticRepresentation_zeroReflecting
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    AnalyticRepresentation.ZeroReflecting
      (generatedAnalyticRepresentation (object := object)) := by
  intro _hCoverage _hWitness _hSemantic model hZero
  exact
    (model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mpr
      hZero

/-- Generated structural obstruction is preserved as generated analytic obstruction. -/
theorem generatedAnalyticRepresentation_obstructionPreserving
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    AnalyticRepresentation.ObstructionPreserving
      (generatedAnalyticRepresentation (object := object)) := by
  intro model _witness hObstruction hZero
  exact hObstruction
    ((model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mpr
      hZero)

/-- Generated analytic obstruction reflects generated structural obstruction. -/
theorem generatedAnalyticRepresentation_obstructionReflecting
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    AnalyticRepresentation.ObstructionReflecting
      (generatedAnalyticRepresentation (object := object)) := by
  intro _hCoverage _hWitness _hSemantic model _witness hObstruction hLawful
  exact hObstruction
    ((model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mp
      hLawful)

/--
Selected obstruction valuation generated from the generated Signature reading.

The selected witness is the required Signature axis package exposed by
`GeneratedAnalyticWitness.requiredSignatureAxes`.  A generated law model has
value `0` exactly because its generated required Signature axes are zero; a
nonzero value is reserved for the selected generated Signature obstruction.
-/
noncomputable def generatedRequiredSignatureObstructionValuation
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    ObstructionValuation
      (GeneratedArchitectureLawModel object)
      GeneratedAnalyticWitness where
  obstruction := fun model _ =>
    ¬ ArchitectureSignature.RequiredSignatureAxesZero
      model.signatureOfGenerated
  value := fun model _ => by
    classical
    exact
      if ArchitectureSignature.RequiredSignatureAxesZero
          model.signatureOfGenerated then 0 else 1
  zeroReflectsAbsence := by
    intro model witness hZero hObstruction
    classical
    by_cases hRequired :
      ArchitectureSignature.RequiredSignatureAxesZero
        model.signatureOfGenerated
    · exact hObstruction hRequired
    · simp [hRequired] at hZero
  obstructionGivesPositive := by
    intro model witness hObstruction
    classical
    by_cases hRequired :
      ArchitectureSignature.RequiredSignatureAxesZero
        model.signatureOfGenerated
    · exact False.elim (hObstruction hRequired)
    · simp [hRequired]
  coverageAssumptions := True
  nonConclusions := True

/-- Generated obstruction valuation records its non-conclusion boundary. -/
theorem generatedRequiredSignatureObstructionValuation_recordsNonConclusions
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)] :
    (generatedRequiredSignatureObstructionValuation
      (object := object)).RecordsNonConclusions := by
  trivial

/--
Every generated law model has zero selected generated analytic obstruction
value, because the value is computed from generated required Signature axes.
-/
theorem generatedRequiredSignatureObstructionValuation_value_zero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    (witness : GeneratedAnalyticWitness) :
    (generatedRequiredSignatureObstructionValuation
      (object := object)).value model witness = 0 := by
  classical
  have hRequired :
      ArchitectureSignature.RequiredSignatureAxesZero
        model.signatureOfGenerated :=
    (model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mp
      model.generatedArchitectureLawful
  simp [generatedRequiredSignatureObstructionValuation, hRequired]

/--
Generated law models have no selected generated analytic obstruction witness.
-/
theorem generatedRequiredSignatureObstructionValuation_noSelectedObstruction
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object) :
    (generatedRequiredSignatureObstructionValuation
      (object := object)).NoSelectedObstruction model := by
  intro witness
  exact
    ObstructionValuation.no_obstruction_of_value_zero
      (generatedRequiredSignatureObstructionValuation
        (object := object))
      (generatedRequiredSignatureObstructionValuation_value_zero
        (object := object) model witness)

end GeneratedArchitectureLawModel

end AAT
end Formal.Arch
