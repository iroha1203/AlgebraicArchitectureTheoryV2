import Formal.Arch.AAT.GeneratedLawModel

namespace Formal.Arch
namespace AAT

universe u v

namespace GeneratedArchitectureLawModel

/--
Signature generated from an Atom-generated law model.

This is the public `signatureOfGenerated` surface requested by the
Atom-generated reconstruction plan.  It delegates to the generated law-model
projection and does not accept a hand-authored `ArchitectureLawModel`.
-/
def signatureOfGenerated
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object) :
    ArchitectureSignature.ArchitectureSignatureV1 :=
  model.generatedSignatureOf

/--
Generated Signature lawfulness is equivalent to required generated Signature
axes being zero.

The equivalence is over the law model produced from the generated object.  The
statement does not take an `architectureLawfulFromAAT` bridge field and does not
take a hand-authored graph or law model as an input.
-/
theorem generatedArchitectureLawful_iff_requiredSignatureAxesZero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object) :
    ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel ↔
      ArchitectureSignature.RequiredSignatureAxesZero
        (model.signatureOfGenerated) := by
  letI : DecidableRel model.toArchitectureLawModel.G.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.GA.edge := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.boundaryAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  letI : DecidableRel model.toArchitectureLawModel.abstractionAllowed := by
    intro source target
    change Decidable (GeneratedRelation object source target)
    exact hRelation source target
  exact ArchitectureSignature.architectureLawful_iff_requiredSignatureAxesZero
    model.toArchitectureLawModel

/-- Generated law models are lawful because their required generated axes are zero. -/
theorem generatedArchitectureLawful_of_requiredSignatureAxesZero
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    [DecidableEq system.Atom]
    [hRelation : DecidableRel (GeneratedRelation object)]
    (model : GeneratedArchitectureLawModel object)
    (hZero :
      ArchitectureSignature.RequiredSignatureAxesZero
        (model.signatureOfGenerated)) :
    ArchitectureSignature.ArchitectureLawful model.toArchitectureLawModel :=
  (model.generatedArchitectureLawful_iff_requiredSignatureAxesZero).mpr hZero

end GeneratedArchitectureLawModel

end AAT
end Formal.Arch
