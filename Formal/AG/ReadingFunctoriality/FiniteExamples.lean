import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample

/-!
# Reading-functoriality reference models

This module owns the positive and negative firing declarations fixed by Part 4
SD9.
-/

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

open CategoryTheory

/-! ## R3: nonidentity selected-cover refinement -/

/-- Finite two-patch site used by the Part 4 refinement reference model. -/
noncomputable def finiteSite :
    Site.AATSite FiniteModel.corePackage.object :=
  FiniteModel.twoPatchSite

/-- Selected base of the finite refinement reference model. -/
noncomputable def finiteBase : finiteSite.category :=
  FiniteModel.twoPatchBase

/-- Coarse selected cover of the finite refinement reference model. -/
noncomputable def coarseCover :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase :=
  FiniteModel.twoPatchCover

/--
Fine selected cover obtained by retaining two labelled copies of every coarse
chart.

Implementation notes: duplicating chart labels preserves the underlying
presieve while giving an actual refinement whose index map is not injective.
-/
noncomputable def fineCover :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase where
  Index := coarseCover.Index × Bool
  patch i := coarseCover.patch i.1
  inclusion i := coarseCover.inclusion i.1
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases coarseCover.admissible.atomSupportCoverage atom hreq with ⟨i, hi⟩
      exact ⟨(i, false), hi⟩
    lawWitnessCoverage := by
      intro witness hreq
      rcases coarseCover.admissible.lawWitnessCoverage witness hreq with h | h
      · rcases h with ⟨i, hi⟩
        exact Or.inl ⟨(i, false), hi⟩
      · rcases h with ⟨i, j, hij⟩
        exact Or.inr ⟨(i, false), (j, false), hij⟩
    signatureAxisCoverage := by
      intro axis hreq
      rcases coarseCover.admissible.signatureAxisCoverage axis hreq with ⟨i, hi⟩
      exact ⟨(i, false), hi⟩
    boundaryCoverage := by
      intro i j
      exact coarseCover.admissible.boundaryCoverage i.1 j.1
    nonGeneration := by
      intro i support atom hselected
      exact coarseCover.admissible.nonGeneration i.1 hselected
  }

/-- Actual fine-to-coarse chart refinement of the duplicated finite cover. -/
noncomputable def coarseToFineCover :
    Site.AATCoverageFamily.Refinement coarseCover fineCover where
  indexMap i := i.1
  factor i := finiteSite.contextPreorder.refl (fineCover.patch i)
  factor_triangle _ := Subsingleton.elim _ _

/-- The finite refinement genuinely duplicates indices and is not bijective. -/
theorem coarseToFineCover_not_bijective :
    ¬ Function.Bijective coarseToFineCover.indexMap := by
  intro h
  let i : coarseCover.Index := FiniteModel.TwoPatchCoverIndex.left
  have hp : (i, false) = (i, true) := h.1 rfl
  exact Bool.false_ne_true (congrArg Prod.snd hp)

end AAT.AG.ReadingFunctorialityFinite
