import Formal.Arch.AAT.GeneratedPath
import Formal.Arch.Evolution.DiagramFiller

namespace Formal.Arch
namespace AAT

universe u v w x

/--
Architecture diagram whose paths are generated from relation-backed generated
architecture steps.
-/
abbrev GeneratedArchitectureDiagram {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation)
    {source target : GeneratedCarrier object} :=
  ArchitectureDiagram (GeneratedArchitectureStep object) source target

namespace GeneratedArchitectureDiagram

/-- Build a generated diagram from two generated paths with the same endpoints. -/
def ofPaths {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {source target : GeneratedCarrier object}
    (lhs rhs : GeneratedArchitecturePath object source target) :
    GeneratedArchitectureDiagram object
      (source := source) (target := target) := by
  exact { lhs := lhs, rhs := rhs }

/-- Reflexive generated diagram for a generated path. -/
def reflexive {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {source target : GeneratedCarrier object}
    (path : GeneratedArchitecturePath object source target) :
    GeneratedArchitectureDiagram object
      (source := source) (target := target) :=
  ofPaths path path

end GeneratedArchitectureDiagram

/-- Selected finite family of generated diagrams over a generated object. -/
structure GeneratedDiagramFamily {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    (object : GeneratedArchitectureObject presentation) where
  selected :
    {source target : GeneratedCarrier object} ->
      GeneratedArchitectureDiagram object
        (source := source) (target := target) -> Prop
  coverageBoundary : Prop
  exactnessBoundary : Prop
  nonConclusions : Prop

/-- Fillability for generated diagrams via generated path homotopy. -/
abbrev GeneratedDiagramFiller {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop)
    (SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop)
    (RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop)
    {source target : GeneratedCarrier object}
    (diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target)) : Prop :=
  DiagramFiller IndependentSquare SameExternalContract RepairFill diagram

/-- Non-fillability witness restricted to generated diagrams. -/
abbrev GeneratedNonFillabilityWitness {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop)
    (SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop)
    (RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop)
    {source target : GeneratedCarrier object}
    (diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target))
    (Witness : Type w) :=
  NonFillabilityWitness
    IndependentSquare SameExternalContract RepairFill diagram Witness

/-- Predicate form for a generated non-fillability witness value. -/
abbrev GeneratedNonFillabilityWitnessFor {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    (IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop)
    (SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop)
    (RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop)
    {source target : GeneratedCarrier object}
    (diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target))
    {Witness : Type w} (witness : Witness) : Prop :=
  NonFillabilityWitnessFor
    IndependentSquare SameExternalContract RepairFill diagram witness

/-- A generated path always fills the reflexive generated diagram over itself. -/
theorem generatedDiagramFiller_refl {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop}
    {source target : GeneratedCarrier object}
    (path : GeneratedArchitecturePath object source target) :
    GeneratedDiagramFiller
      IndependentSquare SameExternalContract RepairFill
      (GeneratedArchitectureDiagram.reflexive path) :=
  ArchitecturePath.PathHomotopy.refl path

/-- Generated non-fillability witnesses soundly refute generated fillers. -/
theorem generated_obstructionAsNonFillability_sound
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop}
    {source target : GeneratedCarrier object}
    {diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target)}
    {Witness : Type w} {witness : Witness}
    (hWitness :
      GeneratedNonFillabilityWitnessFor
        IndependentSquare SameExternalContract RepairFill diagram witness) :
    ¬ GeneratedDiagramFiller
      IndependentSquare SameExternalContract RepairFill diagram :=
  obstructionAsNonFillability_sound hWitness

/-- Generated diagram fillers preserve selected generated path observations. -/
theorem generatedDiagramFiller_observation_eq
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {α : Type x}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop}
    {Obs :
      {X Y : GeneratedCarrier object} ->
        GeneratedArchitecturePath object X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : GeneratedCarrier object}
        (a : GeneratedArchitectureStep object W X)
        (b : GeneratedArchitectureStep object X Z)
        (c : GeneratedArchitectureStep object W Y)
        (d : GeneratedArchitectureStep object Y Z)
        (rest : GeneratedArchitecturePath object Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : GeneratedCarrier object}
        (s t : GeneratedArchitectureStep object X Y)
        (rest : GeneratedArchitecturePath object Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : GeneratedCarrier object}
        {p q : GeneratedArchitecturePath object X Y},
        RepairFill X Y p q ->
          (suffix : GeneratedArchitecturePath object Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : GeneratedCarrier object}
        (step : GeneratedArchitectureStep object X Y)
        {p q : GeneratedArchitecturePath object Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {source target : GeneratedCarrier object}
    {diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target)}
    (hFiller :
      GeneratedDiagramFiller
        IndependentSquare SameExternalContract RepairFill diagram) :
    Obs diagram.lhs = Obs diagram.rhs := by
  exact
    diagramFiller_observation_eq
      (Step := GeneratedArchitectureStep object) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      hFiller

/--
An observation difference refutes generated diagram filling under
observation-preserving generated homotopy generators.
-/
theorem generatedObservationDifference_refutesDiagramFiller
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {α : Type x}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop}
    {Obs :
      {X Y : GeneratedCarrier object} ->
        GeneratedArchitecturePath object X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : GeneratedCarrier object}
        (a : GeneratedArchitectureStep object W X)
        (b : GeneratedArchitectureStep object X Z)
        (c : GeneratedArchitectureStep object W Y)
        (d : GeneratedArchitectureStep object Y Z)
        (rest : GeneratedArchitecturePath object Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : GeneratedCarrier object}
        (s t : GeneratedArchitectureStep object X Y)
        (rest : GeneratedArchitecturePath object Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : GeneratedCarrier object}
        {p q : GeneratedArchitecturePath object X Y},
        RepairFill X Y p q ->
          (suffix : GeneratedArchitecturePath object Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : GeneratedCarrier object}
        (step : GeneratedArchitectureStep object X Y)
        {p q : GeneratedArchitecturePath object Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {source target : GeneratedCarrier object}
    {diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target)}
    (hDifference : Obs diagram.lhs ≠ Obs diagram.rhs) :
    ¬ GeneratedDiagramFiller
      IndependentSquare SameExternalContract RepairFill diagram := by
  exact
    observationDifference_refutesDiagramFiller
      (Step := GeneratedArchitectureStep object) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      hDifference

/--
Generated observation difference packages a generated non-fillability witness
for a selected witness value.
-/
theorem generatedObservationDifference_nonFillabilityWitnessFor
    {system : AtomAxiomSystem.{u, v}}
    {presentation : AtomShapePresentation system}
    {object : GeneratedArchitectureObject presentation}
    {α : Type x}
    {IndependentSquare :
      (W X Y Z : GeneratedCarrier object) ->
        GeneratedArchitectureStep object W X ->
        GeneratedArchitectureStep object X Z ->
        GeneratedArchitectureStep object W Y ->
        GeneratedArchitectureStep object Y Z -> Prop}
    {SameExternalContract :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitectureStep object X Y ->
        GeneratedArchitectureStep object X Y -> Prop}
    {RepairFill :
      (X Y : GeneratedCarrier object) ->
        GeneratedArchitecturePath object X Y ->
        GeneratedArchitecturePath object X Y -> Prop}
    {Obs :
      {X Y : GeneratedCarrier object} ->
        GeneratedArchitecturePath object X Y -> α}
    (hIndependentSquare :
      ∀ {W X Y Z T : GeneratedCarrier object}
        (a : GeneratedArchitectureStep object W X)
        (b : GeneratedArchitectureStep object X Z)
        (c : GeneratedArchitectureStep object W Y)
        (d : GeneratedArchitectureStep object Y Z)
        (rest : GeneratedArchitecturePath object Z T),
          IndependentSquare W X Y Z a b c d ->
            Obs (ArchitecturePath.cons a (ArchitecturePath.cons b rest)) =
              Obs (ArchitecturePath.cons c (ArchitecturePath.cons d rest)))
    (hSameExternalContract :
      ∀ {X Y Z : GeneratedCarrier object}
        (s t : GeneratedArchitectureStep object X Y)
        (rest : GeneratedArchitecturePath object Y Z),
          SameExternalContract X Y s t ->
            Obs (ArchitecturePath.cons s rest) =
              Obs (ArchitecturePath.cons t rest))
    (hRepairFill :
      ∀ {X Y Z : GeneratedCarrier object}
        {p q : GeneratedArchitecturePath object X Y},
        RepairFill X Y p q ->
          (suffix : GeneratedArchitecturePath object Y Z) ->
            Obs (ArchitecturePath.append p suffix) =
              Obs (ArchitecturePath.append q suffix))
    (hConsContext :
      ∀ {X Y Z : GeneratedCarrier object}
        (step : GeneratedArchitectureStep object X Y)
        {p q : GeneratedArchitecturePath object Y Z},
          Obs p = Obs q ->
            Obs (ArchitecturePath.cons step p) =
              Obs (ArchitecturePath.cons step q))
    {source target : GeneratedCarrier object}
    {diagram : GeneratedArchitectureDiagram object
      (source := source) (target := target)}
    {Witness : Type w} (witness : Witness)
    (hDifference : Obs diagram.lhs ≠ Obs diagram.rhs) :
    GeneratedNonFillabilityWitnessFor
      IndependentSquare SameExternalContract RepairFill diagram witness := by
  exact
    observationDifference_nonFillabilityWitnessFor
      (Step := GeneratedArchitectureStep object) (Obs := Obs)
      hIndependentSquare hSameExternalContract hRepairFill hConsContext
      witness hDifference

end AAT
end Formal.Arch
