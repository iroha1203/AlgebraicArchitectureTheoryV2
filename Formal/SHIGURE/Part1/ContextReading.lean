import Formal.SHIGURE.Part1.Reading
import Formal.SHIGURE.Part1.ContextOrdinaryDescent

/-! # A reading on its chosen declarations

A reading uses the declaration context and cover it already specifies.
Its restriction lives over the actual selected presentation. An attached
residual uses the original proof names and equations when the reading has
their support, even when those names declare additional Laws.

## Implementation notes

`Reading.restrict` accepts a caller-supplied presentation with an exact
`ReadingOrigin` certificate for the named attachments. The computed
selection here uses the declaration names, context and cover already present
in the reading. This lets a context retain a written Law and its ordered
terms when some references of its optional ring certificate are outside the
context. Requiring full attachment equality for this computation would ask
the context to retain those references as well.
-/

universe u v w x

namespace SHIGURE.Reading

open DeclarationContext

variable (reading : Reading.{u, v, w, x})

/-- The presentation of the reading's selected declarations. -/
noncomputable abbrev selectedPresentation : PrimitivePresentation.{u} :=
  Selected.presentation reading.context

/-- Interpret the selected signature in the structure carried by the reading. -/
noncomputable def selectedStructure : Structure reading.selectedPresentation.signature :=
  Selected.readStructure (ContextStructure.ofStructure reading.context reading.structureData)

/-- A retained Law's exact selected text holds precisely when its original text holds in the reading. -/
theorem selectedLaw_iff (name : reading.context.RetainedLaw) :
    (reading.selectedPresentation.laws.statement name).Holds reading.selectedStructure ↔
      (reading.presentation.laws.statement name.val).Holds reading.structureData := by
  let original := reading.presentation.laws.statement name.val
  let kept := Declaration.lawBody_subset_of_mem name.property
  let A := ContextStructure.ofStructure reading.context reading.structureData
  exact ((Selected.readStructure_matches A).law_iff original kept).trans
    (ContextStructure.ofStructure_satisfies_iff reading.context reading.structureData original kept)

/-- The selected model condition tests the original Laws that are both retained and required. -/
theorem selectedTheory_holds_iff :
    reading.selectedPresentation.theory.Holds reading.selectedStructure ↔
      ∀ name : reading.selectedPresentation.theory.LawName,
        (reading.presentation.laws.statement name.val.val).Holds reading.structureData := by
  constructor
  · exact fun model name => (reading.selectedLaw_iff name.val).1 (model name)
  · exact fun model name => (reading.selectedLaw_iff name.val).2 (model name)

/-- The reading determines its ordinary model when the retained required Laws hold. -/
noncomputable def selectedModel (model : reading.selectedPresentation.theory.Holds reading.selectedStructure) :
    Model reading.selectedPresentation.theory :=
  ⟨reading.selectedStructure, model⟩

/-- The reading's actual cover restricts the selected model to all its ordinary local models. -/
noncomputable def selectedLocalModels
    (model : reading.selectedPresentation.theory.Holds reading.selectedStructure) :
    OrdinaryMatch reading.cover.piece :=
  reading.cover.ordinaryRead.obj (reading.selectedModel model)

/-- A supported ring is registered on the actual presentation used by the reading. -/
theorem selectedRing_attached (name : reading.context.RetainedLaw)
    (equation : NamedRingEquation reading.presentation.laws name.val)
    (attached : reading.presentation.ringEquation name.val = some equation)
    (keep : reading.context.RetainsRingSupport name.val) :
    reading.selectedPresentation.ringEquation name =
      some (Selected.selectNamedRingEquation name equation attached keep) :=
  Selected.ringEquation_of_supported name equation attached keep

/-- Selecting an attached ring in a reading keeps the name of each of its axioms. -/
theorem selectedRing_axiomsHold (name : reading.context.RetainedLaw)
    (equation : NamedRingEquation reading.presentation.laws name.val)
    (attached : reading.presentation.ringEquation name.val = some equation)
    (keep : reading.context.RetainsRingSupport name.val)
    (held : equation.AxiomsHold reading.structureData) :
    (Selected.selectNamedRingEquation name equation attached keep).AxiomsHold reading.selectedStructure := by
  intro i selected
  exact (reading.selectedLaw_iff i).2 (held i.val selected)

/-- The retained proof trees supply all the ring Laws for a reading of the selected residual. -/
theorem selectedRing_axioms (name : reading.context.RetainedLaw)
    (equation : NamedRingEquation reading.presentation.laws name.val)
    (attached : reading.presentation.ringEquation name.val = some equation)
    (keep : reading.context.RetainsRingSupport name.val)
    (held : equation.AxiomsHold reading.structureData) :
    let selected := Selected.selectNamedRingEquation name equation attached keep
    ∀ i, (selected.written.equation.ring.law i).Holds reading.selectedStructure :=
  (Selected.selectNamedRingEquation name equation attached keep).axioms_imply reading.selectedStructure
    (reading.selectedRing_axiomsHold name equation attached keep held)

/-- The selected reading tests the retained Law using the actual ordered residual and ring proofs. -/
theorem selectedRing_residual_iff (name : reading.context.RetainedLaw)
    (equation : NamedRingEquation reading.presentation.laws name.val)
    (attached : reading.presentation.ringEquation name.val = some equation)
    (keep : reading.context.RetainsRingSupport name.val)
    (held : equation.AxiomsHold reading.structureData) :
    let selected := Selected.selectNamedRingEquation name equation attached keep
    let eqn := selected.written.equation
    let ringLaws := reading.selectedRing_axioms name equation attached keep held
    (reading.selectedPresentation.laws.statement name).Holds reading.selectedStructure ↔
      eqn.jointInputs reading.selectedStructure = selected.written.toLaw.inputSet reading.selectedStructure ∧
      ∀ e : eqn.jointInputs reading.selectedStructure,
        eqn.residual reading.selectedStructure ringLaws e = eqn.ring.zeroValue reading.selectedStructure :=
  (Selected.selectNamedRingEquation name equation attached keep).holds_iff_residual_zero reading.selectedStructure
    (reading.selectedRing_axiomsHold name equation attached keep held)

end SHIGURE.Reading
