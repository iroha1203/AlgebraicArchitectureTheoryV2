import Formal.SHIGURE.Part1.MarkedRationalOperations
import Formal.SHIGURE.Part1.MarkedRealizations

/-! # Strict gluing and failure for the rational marked modules

Example 3.7 supplies each piece with its own marked data and Laws. With
the kernel of Equation (3.5) on both pieces there is a unique assembly.
Replacing the right q kernel preserves both right Laws, but rules out
a mark-preserving identification and hence a shared marked realization.
-/

namespace SHIGURE.Marked.RationalExample

open Vocabulary DeclarationContext

/-- Each piece is a local realization with its own chosen q coordinate and required Laws. -/
noncomputable def localRealization (right : Bool) {K : Kernel ℚ 2}
    (coord : Quotient K ≃ₗ[ℚ] ℚ) : Realization ℚ (cover.piece right) where
  blocks := piece_blockClosed right
  data := coordinateData (cover.piece right) coord
  fixedRank s _ := fixedRank_one (coordinates coord s)
  satisfiesRequired name := by
    let whole := DeclarationContext.full presentation
    let fullData := coordinateData whole coord
    let law : Law vocabulary.signature := (cover.piece right).scopedTheory.law name
    have localSupport := Declaration.lawBody_subset_of_mem name.property
    have fullSupport : Declaration.lawBody (P := presentation) law ⊆ whole.declarations := Set.subset_univ _
    have primitiveHolds : law.Holds fullData.structureData := by
      change (roundTrip name.val.val).Holds (coordinateData whole coord).structureData
      rw [coordinateData_full_structure]
      exact all_roundTrips coord name.val.val
    have fullHolds := (fullData.contextStructure_satisfies_iff law fullSupport).2 primitiveHolds
    have localHolds := (fullData.contextStructure.restrict_satisfies_iff (cover.subset right) law localSupport).2 fullHolds
    rw [fullData.contextStructure_restrict, coordinateData_restrict] at localHolds
    exact localHolds

/-- Both pieces independently use the concrete positive marked data. -/
noncomputable def positiveFamily : MatchingRealizations ℚ cover where
  piece right := localRealization right phi
  overlap _ _ := ⟨fun _ _ _ => rfl, fun _ _ _ => HEq.rfl⟩

/-- The positive gluing is the actual result of Proposition 3.6. -/
noncomputable def assembled : Realization ℚ (DeclarationContext.full presentation) :=
  positiveFamily.glue

/-- The assembly restricts to both of the specified rational local realizations. -/
theorem assembled_restricts (right : Bool) :
    assembled.restrict (cover.subset right) (piece_blockClosed right) = localRealization right phi :=
  positiveFamily.glue_restrict right

/-- All four written round-trip Laws hold in the assembled global marked structure. -/
theorem assembled_all_laws (name : Op) : (roundTrip name).Holds assembled.data.structureData :=
  assembled.holds ⟨⟨name, rfl⟩, Set.mem_univ _⟩

/-- Equation (3.5) is the shared kernel of the actual positive assembly. -/
theorem assembled_q_kernel (kept : Declaration.sort (some SortName.q) ∈
    (DeclarationContext.full presentation).declarations) :
    assembled.data.kernel SortName.q kept = Submodule.span ℚ {(![3, -2] : Coordinates ℚ 2)} :=
  (positiveFamily.data.glueKernel_eq_piece false SortName.q True.intro).trans sharedKernel_eq_span

/-- The specified positive realization is unique with these exact local restrictions. -/
theorem positive_existsUnique :
    ∃! G : Realization ℚ (DeclarationContext.full presentation), ∀ right : Bool,
      G.restrict (cover.subset right) (piece_blockClosed right) = localRealization right phi :=
  positiveFamily.existsUnique_glue

/-- Changing only the right kernel leaves its two named inverse Laws valid. -/
theorem changed_right_laws :
    (roundTrip .u).Holds (localRealization true phiChanged).data.structureData ∧
      (roundTrip .v).Holds (localRealization true phiChanged).data.structureData :=
  ⟨(localRealization true phiChanged).holds ⟨⟨.u, rfl⟩, rfl⟩,
    (localRealization true phiChanged).holds ⟨⟨.v, rfl⟩, rfl⟩⟩

/-- The changed right piece cannot be glued to the original left piece. -/
theorem no_glue_changed :
    ¬ ∃ G : Realization ℚ (DeclarationContext.full presentation),
      G.restrict (cover.subset false) (piece_blockClosed false) = localRealization false phi ∧
      G.restrict (cover.subset true) (piece_blockClosed true) = localRealization true phiChanged :=
  MatchingRealizations.no_glue_of_kernel_ne (cover := cover)
    (localRealization false phi) (localRealization true phiChanged) SortName.q
    True.intro True.intro sharedKernel_ne_changedKernel

/-- A context can be dependency-closed while omitting the mandatory module block. -/
def qSortAlone : DeclarationContext presentation where
  declarations := {Declaration.sort (some SortName.q)}
  closed kept := by
    have same := Set.mem_singleton_iff.mp kept
    subst same
    exact Set.empty_subset _

/-- Such a context fails the extra module block condition of Proposition 3.6. -/
theorem qSortAlone_not_blockClosed : ¬ BlockClosed qSortAlone := by
  intro h
  have existsZero := h.moduleOp SortName.q (Set.mem_singleton _) .zero
  have impossible := Set.mem_singleton_iff.mp existsZero
  cases impossible

end SHIGURE.Marked.RationalExample
