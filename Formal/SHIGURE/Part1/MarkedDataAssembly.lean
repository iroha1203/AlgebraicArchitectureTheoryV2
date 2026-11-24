import Formal.SHIGURE.Part1.MarkedData

/-! # Assembly of the marked quotient data

Proposition 3.6 first selects an actual kernel and multilinear map per
declaration. Every retained choice is compared with the local datum
through the overlap agreement.

## Implementation notes

The cover supplies a piece per sort and per operation independently. The
choice for an operation can differ from that of its input sorts. Therefore
the operation is transported using equality of its input and result
kernels. An equality of ambient kernel families would be stronger than
the overlap hypothesis, since either piece can omit unrelated sorts.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary

variable {V : Vocabulary.{u}} {L : V.Laws} {R : Type u} [CommRing R]
variable {U : DeclarationContext (V.presentation L)} {cover : DeclarationCover U}

/-- The data of the local marked presentations and their actual shared agreement. -/
structure MatchingData (R : Type u) [CommRing R] (cover : DeclarationCover U) where
  /-- Kernels and multilinear maps independently supplied in each piece. -/
  piece (i : cover.Index) : Data R (cover.piece i)
  /-- Agreement requires only shared kernels and shared interpretations. -/
  overlap (i j : cover.Index) : (piece i).Agree (piece j)

namespace MatchingData

variable (A : MatchingData R cover)

/-- The global kernel at each retained sort is read from a piece containing its declaration. -/
noncomputable def glueKernel : KernelFamily R U :=
  fun _ keep => (A.piece (cover.index keep)).kernel _ (cover.mem_index keep)

/-- The global kernel agrees with the kernel in any piece which retains that sort. -/
theorem glueKernel_eq_piece (i : cover.Index) (s : V.SortName)
    (keep : Declaration.sort (some s) ∈ (cover.piece i).declarations) :
    A.glueKernel s (cover.subset i keep) = (A.piece i).kernel s keep :=
  (A.overlap (cover.index (cover.subset i keep)) i).kernel s (cover.mem_index (cover.subset i keep)) keep

/-- A retained local operation has the same input and output kernels after assembly. -/
theorem glueOperationKernels_eq_piece (i : cover.Index) {f : V.Multilinear}
    (keep : V.multilinearDecl L f ∈ (cover.piece i).declarations) :
    operationKernels A.glueKernel (cover.subset i keep) = operationKernels (A.piece i).kernel keep :=
  OperationKernels.ext (fun p => A.glueKernel_eq_piece i p.1 (V.multilinear_input_kept keep p))
    (A.glueKernel_eq_piece i (V.output f) (V.multilinear_output_kept keep))

/-- Assemble the canonical marked carriers and operation interpretations on the cover. -/
noncomputable def glue : Data R U where
  kernel := A.glueKernel
  operation f keep :=
    let i := cover.index keep
    let localKeep := cover.mem_index keep
    cast (congrArg OperationKernels.Map (A.glueOperationKernels_eq_piece i localKeep).symm)
      ((A.piece i).operation f localKeep)

/-- The assembled data agree with their local input on every shared declaration. -/
theorem glue_agree (i : cover.Index) : A.glue.Agree (A.piece i) where
  kernel s _ keep := A.glueKernel_eq_piece i s keep
  operation f globalKeep localKeep :=
    (cast_heq _ _).trans
      ((A.overlap (cover.index globalKeep) i).operation f (cover.mem_index globalKeep) localKeep)

/-- The assembled kernel and map data restrict exactly to the local inputs. -/
theorem glue_restrict (i : cover.Index) : A.glue.restrict (cover.subset i) = A.piece i :=
  (A.glue_agree i).restrict_eq (cover.subset i)

/-- Restriction to covering pieces determines all kernel and map data. -/
theorem eq_of_restrict_eq {a b : Data R U}
    (same : ∀ i, a.restrict (cover.subset i) = b.restrict (cover.subset i)) : a = b := by
  apply Data.ext
  · intro s keep
    let i := cover.index keep
    let localKeep := cover.mem_index keep
    exact congrArg (fun d => d.kernel s localKeep) (same i)
  · intro f keep
    let i := cover.index keep
    let localKeep := cover.mem_index keep
    have agree : HEq ((a.restrict (cover.subset i)).operation f localKeep)
        ((b.restrict (cover.subset i)).operation f localKeep) := by rw [same i]
    exact (a.restrict_operation (cover.subset i) f localKeep).symm.trans
      (agree.trans (b.restrict_operation (cover.subset i) f localKeep))

/-- The marked data have a unique global assembly before checking Laws and rank. -/
theorem existsUnique_glue : ∃! d : Data R U, ∀ i, d.restrict (cover.subset i) = A.piece i :=
  ⟨A.glue, A.glue_restrict, fun _ h => eq_of_restrict_eq (fun i => (h i).trans (A.glue_restrict i).symm)⟩

end MatchingData
end SHIGURE.Marked
