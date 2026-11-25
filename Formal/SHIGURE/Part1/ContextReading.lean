import Formal.SHIGURE.Part1.Reading
import Formal.SHIGURE.Part1.ContextOrdinaryDescent

/-! # A reading on its chosen declarations

A reading uses the declaration context and cover it already specifies.
Its restriction lives over the actual selected presentation. An attached
residual uses the original proof names and equations when the reading has
their support, even when those names declare additional Laws.

## Implementation notes

`Reading.restrict` accepts a caller-supplied presentation with a
`ReadingOrigin` certificate. The certificate compares the literal text and
derivation and accounts for the support of optional ring data. The computed
selection here directly uses the context and cover already present in the
reading. Both can retain a written Law and its ordered terms when some
references of its optional ring certificate are outside the context.
-/

universe u v w x

namespace SHIGURE.Reading

open DeclarationContext

/-- Transporting the interpreted structure instead of the Law preserves its truth. -/
private theorem holds_cast_structure {S Q : Signature.{u}} (same : S = Q)
    (law : Law S) (A : Structure Q) :
    law.Holds (cast (congrArg Structure same.symm) A) ↔ (cast (congrArg Law same) law).Holds A := by
  cases same
  rfl

variable (reading : Reading.{u, v, w, x})

/-- The presentation of the reading's selected declarations. -/
noncomputable abbrev selectedPresentation : PrimitivePresentation.{u} :=
  Selected.presentation reading.context

/-- Interpret the selected signature in the structure carried by the reading. -/
noncomputable def selectedStructure : Structure reading.selectedPresentation.signature :=
  cast (congrArg Structure (Selected.presentation_signature (U := reading.context)).symm)
    (Selected.readStructure (ContextStructure.ofStructure reading.context reading.structureData))

/-- The structure of the selected reading is the restriction along its selected signature. -/
theorem selectedStructure_eq :
    reading.selectedStructure =
      cast (congrArg Structure (Selected.presentation_signature (U := reading.context)).symm)
        (Selected.readStructure (ContextStructure.ofStructure reading.context reading.structureData)) :=
  rfl

attribute [local irreducible] Selected.presentation in
/-- Compare the selected reading using the actual Law name of the selected presentation. -/
theorem selectedLaw_iff_ofName (name : reading.context.RetainedLaw) :
    (reading.selectedPresentation.laws.statement (Selected.presentationLawName name)).Holds reading.selectedStructure ↔
      (reading.presentation.laws.statement name.val).Holds reading.structureData := by
  let original := reading.presentation.laws.statement name.val
  let kept := Declaration.lawBody_subset_of_mem name.property
  let A := ContextStructure.ofStructure reading.context reading.structureData
  rw [selectedStructure_eq, holds_cast_structure (Selected.presentation_signature (U := reading.context)),
    Selected.presentation_law_cast]
  exact ((Selected.readStructure_matches A).law_iff original kept).trans
    (ContextStructure.ofStructure_satisfies_iff reading.context reading.structureData original kept)

/-- A retained Law's exact selected text holds precisely when its original text holds in the reading. -/
theorem selectedLaw_iff (name : reading.context.RetainedLaw) :
    (reading.selectedPresentation.laws.statement name).Holds reading.selectedStructure ↔
      (reading.presentation.laws.statement name.val).Holds reading.structureData :=
  reading.selectedLaw_iff_ofName name

/-- The selected model condition tests the original Laws that are both retained and required. -/
theorem selectedTheory_holds_iff :
    reading.selectedPresentation.theory.Holds reading.selectedStructure ↔
      ∀ name : reading.selectedPresentation.theory.LawName,
        (reading.presentation.laws.statement name.val.val).Holds reading.structureData := by
  rw [Theory.holds_iff]
  constructor
  · intro model name
    have held := model name
    rw [Selected.presentation_theory_law] at held
    exact (reading.selectedLaw_iff_ofName (Selected.retainedTheoryName name)).1 held
  · intro model name
    rw [Selected.presentation_theory_law]
    exact (reading.selectedLaw_iff_ofName (Selected.retainedTheoryName name)).2 (model name)

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
  (Selected.presentation_ringEquation name).trans (Selected.ringEquation_of_supported name equation attached keep)

/-- Selecting an attached ring in a reading keeps the name of each of its axioms. -/
theorem selectedRing_axiomsHold (name : reading.context.RetainedLaw)
    (equation : NamedRingEquation reading.presentation.laws name.val)
    (attached : reading.presentation.ringEquation name.val = some equation)
    (keep : reading.context.RetainsRingSupport name.val)
    (held : equation.AxiomsHold reading.structureData) :
    (Selected.selectNamedRingEquation name equation attached keep).AxiomsHold reading.selectedStructure := by
  apply (NamedRingEquation.axiomsHold_iff _ _).2
  intro i selected
  have original : i.val ∈ equation.axiomNames := by
    rw [← Selected.selectNamedRingEquation_axiomNames name equation attached keep]
    exact ⟨i, selected, rfl⟩
  exact (reading.selectedLaw_iff i).2 ((equation.axiomsHold_iff _).1 held i.val original)

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
        eqn.residual reading.selectedStructure ringLaws e = eqn.ring.zeroValue reading.selectedStructure := by
  rw [Selected.presentation_law_eq_selected]
  exact (Selected.selectNamedRingEquation name equation attached keep).holds_iff_residual_zero reading.selectedStructure
    (reading.selectedRing_axiomsHold name equation attached keep held)

end SHIGURE.Reading
