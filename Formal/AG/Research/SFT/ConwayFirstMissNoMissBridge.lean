import Formal.AG.Research.SFT.ConwaySelectedMissScanner

/-!
Cycle 36 evidence for `G-sft-conway-01`.

Cycle 33 proved that a selected first miss exists exactly when some selected
miss exists.  This file records the direct negative-side bridge: no selected
first miss is equivalent to pointwise absence of selected misses for the bounded
reorg/refactor edit shapes.

This remains selected finite Conway vocabulary.  It is not an arbitrary
conflict enumeration algorithm or a general repair calculus.
-/

namespace Formal.AG.Research
namespace SFT
namespace ConwayTwoTopology

/-! ## Negative bridge from first-miss absence to pointwise no-miss -/

/--
For selected reorg edits, absence of a selected first miss is equivalent to
pointwise absence of selected misses.
-/
theorem reorgNoFirstSelectedMiss_iff_noSelectedMiss
    (edit : ReorgCoverEdit) :
    Not
        (exists conflict : ReorgSelectedConflict,
          ReorgCoverEditFirstSelectedMiss edit conflict) ↔
      forall conflict : ReorgSelectedConflict,
        Not (ReorgCoverEditMissesSelectedConflict edit conflict) := by
  rw [reorgFirstSelectedMiss_exists_iff_hasSelectedMiss]
  constructor
  · intro hnoFirst conflict hmiss
    exact hnoFirst ⟨conflict, hmiss⟩
  · intro hnoMiss hmiss
    rcases hmiss with ⟨conflict, hconflict⟩
    exact hnoMiss conflict hconflict

/--
For selected refactor edits, absence of a selected first miss is equivalent to
pointwise absence of selected misses.
-/
theorem refactorNoFirstSelectedMiss_iff_noSelectedMiss
    (edit : RefactorOwnershipEdit) :
    Not
        (exists conflict : RefactorSelectedConflict,
          RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
      forall conflict : RefactorSelectedConflict,
        Not (RefactorOwnershipEditMissesSelectedConflict edit conflict) := by
  rw [refactorFirstSelectedMiss_exists_iff_hasSelectedMiss]
  constructor
  · intro hnoFirst conflict hmiss
    exact hnoFirst ⟨conflict, hmiss⟩
  · intro hnoMiss hmiss
    rcases hmiss with ⟨conflict, hconflict⟩
    exact hnoMiss conflict hconflict

/--
The selected Cycle 36 package: first-miss absence and pointwise no-selected-miss
are the same criterion for both bounded edit shapes.
-/
theorem selectedFirstMissNoMissBridgePackage :
    (forall edit : ReorgCoverEdit,
      Not
          (exists conflict : ReorgSelectedConflict,
            ReorgCoverEditFirstSelectedMiss edit conflict) ↔
        forall conflict : ReorgSelectedConflict,
          Not (ReorgCoverEditMissesSelectedConflict edit conflict)) /\
      (forall edit : RefactorOwnershipEdit,
        Not
            (exists conflict : RefactorSelectedConflict,
              RefactorOwnershipEditFirstSelectedMiss edit conflict) ↔
          forall conflict : RefactorSelectedConflict,
            Not (RefactorOwnershipEditMissesSelectedConflict edit conflict)) := by
  exact
    ⟨reorgNoFirstSelectedMiss_iff_noSelectedMiss,
      refactorNoFirstSelectedMiss_iff_noSelectedMiss⟩

end ConwayTwoTopology
end SFT
end Formal.AG.Research
