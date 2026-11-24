import Formal.SHIGURE.Part1.MarkedCompatibility
import Formal.SHIGURE.Part1.MarkedDataAssembly
import Formal.SHIGURE.Part1.ContextOrdinaryDescent

/-! # Assembly of marked finite locally free realizations

Proposition 3.6 fixes a coefficient ring and requires a specified stalk
rank for each retained canonical quotient. The data assembled from
the cover give the ordinary SHIGURE model glued from the local models.

## Implementation notes

Rank and projectivity are conditions on the canonical quotient, separate
from the required positive Laws. Each assembled quotient has the same
kernel as a local quotient and gets these conditions from that piece.
Required Law satisfaction is transferred from a piece covering the Law
using the existing support-sensitive restriction theorem. The exact
ordinary gluing theorem then identifies the resulting model with the
assembly of the independently supplied local models.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary DeclarationContext CategoryTheory

variable {V : Vocabulary.{u}} {L : V.Laws} {R : Type u} [CommRing R]
variable {U W : DeclarationContext (V.presentation L)} {cover : DeclarationCover U}

/-- A marked finite locally free realization of Proposition 3.6 on a declaration context. -/
structure Realization (R : Type u) [CommRing R] (U : DeclarationContext (V.presentation L)) where
  /-- Retained module sorts have the full block of coefficient and module symbols. -/
  blocks : BlockClosed U
  /-- Kernel and multilinear data on exactly the retained declarations. -/
  data : Data R U
  /-- The prescribed rank and local freeness of each retained quotient. -/
  fixedRank (s : V.SortName) (keep : Declaration.sort (some s) ∈ U.declarations) :
    FixedRank (data.kernel s keep) (V.rank s)
  /-- The selected marked structure verifies each retained required Law. -/
  satisfiesRequired (name : U.scopedTheory.LawName) :
    data.contextStructure.evaluation.satisfies (U.scopedTheory.law name)
      (Declaration.lawBody_subset_of_mem name.property)

namespace Realization

/-- The selected structure of a realization is an ordinary SHIGURE context model. -/
noncomputable def model (A : Realization R U) : Models U :=
  ⟨A.data.contextStructure, A.satisfiesRequired⟩

/-- The model uses the actual restricted signature of the marked presentation. -/
noncomputable def ordinaryModel (A : Realization R U) : Model (Selected.theory U) :=
  Selected.readModel A.model

/-- Writing the ordinary marked model gives its original context interpretation. -/
theorem writeModel_ordinaryModel (A : Realization R U) : Selected.writeModel A.ordinaryModel = A.model :=
  Selected.write_read_model A.model

/-- An existing realization satisfies its retained Laws on the given marked values. -/
theorem holds (A : Realization R U) (name : U.scopedTheory.LawName) :
    (U.scopedTheory.law name).Holds A.data.structureData :=
  (A.data.contextStructure_satisfies_iff (U.scopedTheory.law name)
    (Declaration.lawBody_subset_of_mem name.property)).1 (A.satisfiesRequired name)

/-- Restriction retains the original quotient data and all conditions on the smaller context. -/
noncomputable def restrict (A : Realization R U) (inside : W ≤ U) (blocks : BlockClosed W) :
    Realization R W where
  blocks := blocks
  data := A.data.restrict inside
  fixedRank s keep := A.fixedRank s (inside keep)
  satisfiesRequired name := by
    rw [← A.data.contextStructure_restrict inside]
    exact (A.model.restrict inside).satisfies_required name

/-- The interpreted context model commutes with restriction of marked realizations. -/
theorem restrict_model (A : Realization R U) (inside : W ≤ U) (blocks : BlockClosed W) :
    (A.restrict inside blocks).model = A.model.restrict inside :=
  ObjectProperty.FullSubcategory.ext (A.data.contextStructure_restrict inside).symm

/-- The block, rank and Law proofs are determined up to proof irrelevance by the marked data. -/
@[ext] theorem ext {A B : Realization R U} (same : A.data = B.data) : A = B := by
  cases A
  cases B
  cases same
  rfl

end Realization

/-- The independently specified realization on each piece and the two shared agreements. -/
structure MatchingRealizations (R : Type u) [CommRing R] (cover : DeclarationCover U) where
  /-- Each local realization includes its own ranks and Law satisfaction. -/
  piece (i : cover.Index) : Realization R (cover.piece i)
  /-- The assembly hypothesis compares only kernels and actual multilinear interpretations. -/
  overlap (i j : cover.Index) : (piece i).data.Agree (piece j).data

namespace MatchingRealizations

variable (A : MatchingRealizations R cover)

/-- The matching underlying kernel and multilinear data. -/
def data : MatchingData R cover :=
  ⟨fun i => (A.piece i).data, A.overlap⟩

/-- Shared kernels and maps imply strict semantic agreement on the intersections. -/
noncomputable def contextMatch : Match cover.piece where
  pieceModel i := (A.piece i).model
  overlap_eq i j := by
    apply ObjectProperty.FullSubcategory.ext
    have same := (A.overlap i j).restrict_eq_restrict
      (overlapLeft cover.piece i j) (overlapRight cover.piece i j)
    exact ((A.piece i).data.contextStructure_restrict (overlapLeft cover.piece i j)).trans
      ((congrArg Data.contextStructure same).trans
        ((A.piece j).data.contextStructure_restrict (overlapRight cover.piece i j)).symm)

/-- The local realizations form the ordinary strict matching family of Theorem 3.4. -/
noncomputable def ordinaryMatch : OrdinaryMatch cover.piece :=
  OrdinaryMatch.readObj A.contextMatch

/-- Proposition 3.6 constructs the marked realization with the assembled data. -/
noncomputable def glue : Realization R U where
  blocks := BlockClosed.of_cover cover (fun i => (A.piece i).blocks)
  data := A.data.glue
  fixedRank s keep := by
    let i := cover.index keep
    have localKeep := cover.mem_index keep
    rw [show A.data.glue.kernel s keep = (A.piece i).data.kernel s localKeep from
      A.data.glueKernel_eq_piece i s localKeep]
    exact (A.piece i).fixedRank s localKeep
  satisfiesRequired name := by
    let i := cover.index name.property
    let localName : (cover.piece i).scopedTheory.LawName := ⟨name.val, cover.mem_index name.property⟩
    have held := (A.piece i).satisfiesRequired localName
    have restruct := (A.data.glue_agree i).contextStructure_restrict_eq (cover.subset i)
    apply (A.data.glue.contextStructure.restrict_satisfies_iff (cover.subset i)
      ((cover.piece i).scopedTheory.law localName)
      (Declaration.lawBody_subset_of_mem localName.property)).1
    rwa [restruct]

/-- The marked assembly restricts exactly to the independently given piece. -/
theorem glue_restrict (i : cover.Index) :
    A.glue.restrict (cover.subset i) (A.piece i).blocks = A.piece i :=
  Realization.ext (A.data.glue_restrict i)

/-- Proposition 3.6 gives a unique marked realization with the specified local restrictions. -/
theorem existsUnique_glue : ∃! G : Realization R U, ∀ i,
    G.restrict (cover.subset i) (A.piece i).blocks = A.piece i := by
  refine ⟨A.glue, A.glue_restrict, fun G localEq => Realization.ext ?_⟩
  exact MatchingData.eq_of_restrict_eq (cover := cover)
    (fun i => (congrArg Realization.data (localEq i)).trans (A.data.glue_restrict i).symm)

/-- The ordinary model of the marked assembly is the strict assembly of Theorem 3.4. -/
theorem glue_ordinaryModel :
    A.glue.ordinaryModel = (cover.ordinaryGlue).obj A.ordinaryMatch := by
  apply (cover.existsUnique_ordinary_glue A.ordinaryMatch).unique
  · intro i
    have localEq := congrArg Realization.model (A.glue_restrict i)
    rw [Realization.restrict_model] at localEq
    rw [Selected.modelRestriction_obj, Realization.writeModel_ordinaryModel, localEq]
    rfl
  · intro i
    exact congrArg (fun B => B.pieceModel i) (cover.ordinaryGlue_read A.ordinaryMatch)

/-- Incoherent shared kernels preclude any realization with the two given restrictions. -/
theorem no_glue_of_kernel_ne {i j : cover.Index}
    (a : Realization R (cover.piece i)) (b : Realization R (cover.piece j))
    (s : V.SortName) (hi : Declaration.sort (some s) ∈ (cover.piece i).declarations)
    (hj : Declaration.sort (some s) ∈ (cover.piece j).declarations)
    (different : a.data.kernel s hi ≠ b.data.kernel s hj) :
    ¬ ∃ G : Realization R U, G.restrict (cover.subset i) a.blocks = a ∧
      G.restrict (cover.subset j) b.blocks = b := by
  rintro ⟨G, left, right⟩
  apply different
  have li := congrArg (fun X : Realization R (cover.piece i) => X.data.kernel s hi) left
  have rj := congrArg (fun X : Realization R (cover.piece j) => X.data.kernel s hj) right
  exact li.symm.trans rj

end MatchingRealizations
end SHIGURE.Marked
