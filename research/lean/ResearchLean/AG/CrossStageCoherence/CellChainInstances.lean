import ResearchLean.AG.CrossStageCoherence.CellChain
import ResearchLean.AG.CrossStageCoherence.CompatiblePairRefutation

/-!
# Cell-chain coherence instance matrix

This module connects the general cell-chain API to the reviewed finite G-109
fixtures.  The canonical diagram supplies a positive instance through the
general necessity theorem.  The old compatible-pair refutation supplies a
negative parallel two-chain whose holonomy is the ratio of its two genuinely
different authored comparators.

## Implementation notes

The negative chain reuses the same semantic left and right nodes for both cell
labels.  Duplicating path nodes by label was rejected because it would erase
the exact parallel interference that motivated the revised target.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

namespace CellChainRefutation

open FiniteCrossStageWitness
open CompatiblePairRefutation

/-- The shared empty-path node of the two active refutation cells. -/
noncomputable def leftNode : CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.left presentation WitnessTwoCell.activeFirst

/-- The shared active-edge node of the two active refutation cells. -/
noncomputable def rightNode : CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.right presentation WitnessTwoCell.activeFirst

/-- The first active cell as an arrow between the shared semantic nodes. -/
noncomputable def firstStep : CellChainStep presentation leftNode rightNode :=
  { cell := WitnessTwoCell.activeFirst
    source_eq := rfl
    target_eq := rfl
    orientation := .forward
    before_eq := rfl
    after_eq := rfl }

/-- The second label has exactly the same semantic source and target paths. -/
noncomputable def secondStep : CellChainStep presentation leftNode rightNode where
  cell := WitnessTwoCell.activeSecond
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- The old counterexample is the parallel two-chain of its active cells. -/
noncomputable def twoChain : CellChain presentation rightNode rightNode :=
  parallelCellTwoChain firstStep secondStep

/-- Its holonomy is the fixed authored-comparator ratio. -/
theorem twoChain_holonomy :
    CellChainHolonomy data twoChain =
      visibleComposite * shiftedVisibleComposite⁻¹ := by
  rw [twoChain, parallelCellTwoChain_holonomy]
  simp only [firstStep, secondStep, cellAuthoredFactor,
    castCompositeFiberAut, data]

/-- The parallel two-chain has genuinely nonidentity holonomy. -/
theorem twoChain_holonomy_ne_one :
    CellChainHolonomy data twoChain ≠ 1 := by
  rw [twoChain_holonomy]
  intro ratioIdentity
  have comparatorEquality : visibleComposite = shiftedVisibleComposite := by
    calc
      visibleComposite =
          (visibleComposite * shiftedVisibleComposite⁻¹) *
            shiftedVisibleComposite := by group
      _ = shiftedVisibleComposite := by rw [ratioIdentity]; simp
  exact shiftedVisibleComposite_ne_visible comparatorEquality.symm

/-- The reviewed compatible-pair fixture is not cell-chain coherent. -/
theorem not_cellChainCoherent : ¬ CellChainCoherent data := by
  intro coherent
  have holonomyIdentity :=
    (cellChainCoherent_iff_holonomy_eq_one data).1 coherent
      PUnit.unit PUnit.unit rightNode twoChain
  exact twoChain_holonomy_ne_one holonomyIdentity

end CellChainRefutation

namespace QualityInstances

open FiniteCrossStageWitness

/-- Cell-chain coherence has direct satisfying and non-satisfying finite data. -/
theorem cellChainCoherent_instances :
    CellChainCoherent canonicalWitnessData ∧
      ¬ CellChainCoherent CompatiblePairRefutation.data :=
  ⟨jointVanishes_cellChainCoherent canonicalWitnessData
      canonicalWitness_joint_vanishes,
    CellChainRefutation.not_cellChainCoherent⟩

end QualityInstances

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
