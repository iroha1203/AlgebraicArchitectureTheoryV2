import Formal.SHIGURE.Part1.ContextMatching

/-! # Strict assembly of matching objects

For each retained declaration, the cover supplies a piece interpreting that
name. The assembled carrier keeps the entire local carrier. The primitive
evaluations are read from that piece with the inputs and outputs transported
along the carrier equalities from intersections.
-/

universe u

namespace SHIGURE
namespace DeclarationContext
namespace Match

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
  (cover : DeclarationCover U) (A : Match cover.piece)

/-- Strict overlap agreement identifies each shared sort's full carriers. -/
theorem pieceCarrier_eq (i j : cover.Index) (s : P.signature.SortType)
    (left : Declaration.sort s ∈ (cover.piece i).declarations)
    (right : Declaration.sort s ∈ (cover.piece j).declarations) :
    (A.pieceModel i).obj.carrier s = (A.pieceModel j).obj.carrier s := by
  have shared : Declaration.sort s ∈ (inter (cover.piece i) (cover.piece j)).declarations := ⟨left, right⟩
  exact ((A.pieceModel i).obj.restrict_carrier (overlapLeft cover.piece i j) shared).symm.trans
    ((congrArg (fun M => M.obj.carrier s) (A.overlap_eq i j)).trans
      ((A.pieceModel j).obj.restrict_carrier (overlapRight cover.piece i j) shared))

/-- Choose the carrier in a covering piece for each retained sort. -/
noncomputable def glueCarrier (s : P.signature.SortType) : Type u := by
  classical
  exact if kept : Declaration.sort s ∈ U.declarations then
    (A.pieceModel (cover.index kept)).obj.carrier s else PUnit

/-- The glued carrier matches the carrier from any piece keeping that sort. -/
theorem glueCarrier_eq_piece (i : cover.Index) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ (cover.piece i).declarations) :
    A.glueCarrier cover s = (A.pieceModel i).obj.carrier s := by
  classical
  rw [glueCarrier, dif_pos (cover.subset i kept)]
  exact A.pieceCarrier_eq cover (cover.index (cover.subset i kept)) i s (cover.mem_index _) kept

/-- Non-selected sorts introduce no extra global data. -/
theorem glueCarrier_omitted (s : P.signature.SortType) (omitted : Declaration.sort s ∉ U.declarations) :
    A.glueCarrier cover s = PUnit := by
  classical
  simp only [glueCarrier, dif_neg omitted]

/-- For each piece, identify the glued carriers with its retained carriers. -/
noncomputable def toPieceCarrier (i : cover.Index) :
    CarrierMap (cover.piece i) (A.glueCarrier cover) (A.pieceModel i).obj.carrier :=
  fun s kept => cast (A.glueCarrier_eq_piece cover i s kept)

/-- The carrier comparison used in Theorems 3.4–3.5 sends a value to a piece
by the carrier equality supplied by that piece's retained sort. -/
theorem toPieceCarrier_apply (i : cover.Index) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ (cover.piece i).declarations) (x : A.glueCarrier cover s) :
    A.toPieceCarrier cover i s kept x = cast (A.glueCarrier_eq_piece cover i s kept) x :=
  rfl

/-- Each identification with a local carrier has an inverse. -/
theorem toPieceCarrier_bijective (i : cover.Index) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ (cover.piece i).declarations) :
    Function.Bijective (A.toPieceCarrier cover i s kept) :=
  (Equiv.cast (A.glueCarrier_eq_piece cover i s kept)).bijective

/-- Read the retained primitives of a piece on the common glued carrier family. -/
noncomputable def localView (i : cover.Index) : RestrictedEvaluation (cover.piece i) (A.glueCarrier cover) :=
  (A.pieceModel i).obj.evaluation.pullback (le_refl _) (A.toPieceCarrier cover i)

/-- For Theorem 3.4 the local view is the pullback along the carrier
identification for the chosen piece. The selected declarations stay fixed. -/
theorem localView_eq_pullback (i : cover.Index) :
    A.localView cover i =
      (A.pieceModel i).obj.evaluation.pullback (le_refl _) (A.toPieceCarrier cover i) :=
  rfl

/-- The local views agree on every overlap as evaluations on the same carrier family. -/
theorem localView_overlap (i j : cover.Index) :
    (A.localView cover i).pullback (overlapLeft cover.piece i j) (fun _ _ x => x) =
      (A.localView cover j).pullback (overlapRight cover.piece i j) (fun _ _ x => x) := by
  let left := overlapLeft cover.piece i j
  let right := overlapRight cover.piece i j
  let X := (A.pieceModel i).obj
  let Y := (A.pieceModel j).obj
  let f : CarrierMap _ (A.glueCarrier cover) X.carrier := fun s keep => A.toPieceCarrier cover i s (left keep)
  let g : CarrierMap _ (A.glueCarrier cover) Y.carrier := fun s keep => A.toPieceCarrier cover j s (right keep)
  have same : X.restrict left = Y.restrict right := congrArg (fun M => M.obj) (A.overlap_eq i j)
  have views := ContextStructure.pullback_along_eq same (le_refl _)
    (fun s keep x => cast (X.restrict_carrier left (s := s) keep).symm (f s keep x))
    (fun s keep x => cast (Y.restrict_carrier right (s := s) keep).symm (g s keep x)) (by
      intro s keep x
      simp only [f, g, toPieceCarrier_apply, cast_cast])
  rw [ContextStructure.restrict_evaluation_view X left f, ContextStructure.restrict_evaluation_view Y right g]
    at views
  simpa only [localView_eq_pullback, RestrictedEvaluation.pullback_comp] using views

/-- Assemble primitive facts from a covering piece for each symbol. -/
noncomputable def glueEvaluation : RestrictedEvaluation U (A.glueCarrier cover) where
  relation r kept e := (A.localView cover (cover.index kept)).relation r (cover.mem_index kept) e
  domain p kept e := (A.localView cover (cover.index kept)).domain p (cover.mem_index kept) e
  graph op kept e y := (A.localView cover (cover.index kept)).graph op (cover.mem_index kept) e y

/-- The assembled interpretation is independent of the chosen piece for each retained primitive. -/
theorem glueEvaluation_view (i : cover.Index) :
    (A.glueEvaluation cover).pullback (cover.subset i) (fun _ _ x => x) = A.localView cover i := by
  apply RestrictedEvaluation.ext
  · intro r kept e
    let j := cover.index (cover.subset i kept)
    have shared : Declaration.relation r ∈ (inter (cover.piece j) (cover.piece i)).declarations :=
      ⟨cover.mem_index (cover.subset i kept), kept⟩
    have same := congrArg (fun (E : RestrictedEvaluation _ _) => E.relation r shared e) (A.localView_overlap cover j i)
    simpa only [RestrictedEvaluation.pullback_relation, mapAssignment_id, glueEvaluation] using Iff.of_eq same
  · intro p kept e
    let j := cover.index (cover.subset i kept)
    have shared : Declaration.partialOp p ∈ (inter (cover.piece j) (cover.piece i)).declarations :=
      ⟨cover.mem_index (cover.subset i kept), kept⟩
    have same := congrArg (fun (E : RestrictedEvaluation _ _) => E.domain p shared e) (A.localView_overlap cover j i)
    simpa only [RestrictedEvaluation.pullback_domain, mapAssignment_id, glueEvaluation] using Iff.of_eq same
  · intro op kept e y
    let j := cover.index (cover.subset i kept)
    have shared : Declaration.ofOperation op ∈ (inter (cover.piece j) (cover.piece i)).declarations :=
      ⟨cover.mem_index (cover.subset i kept), kept⟩
    have same := congrArg (fun (E : RestrictedEvaluation _ _) => E.graph op shared e y) (A.localView_overlap cover j i)
    simpa only [RestrictedEvaluation.pullback_graph, mapAssignment_id, glueEvaluation] using Iff.of_eq same

/-- Validity of a Law in a covering piece implies validity in the assembled evaluation. -/
theorem glueEvaluation_satisfies (i : cover.Index) (law : Law P.signature)
    (support : Declaration.lawBody law ⊆ (cover.piece i).declarations)
    (localHolds : (A.pieceModel i).obj.evaluation.satisfies law support) :
    (A.glueEvaluation cover).satisfies law (fun _ used => cover.subset i (support used)) := by
  have held : (A.localView cover i).satisfies law support := by
    rw [localView_eq_pullback]
    exact ((A.pieceModel i).obj.evaluation.satisfies_pullback_iff (le_refl _) (A.toPieceCarrier cover i)
        (A.toPieceCarrier_bijective cover i) law support).2 localHolds
  rw [← A.glueEvaluation_view cover i] at held
  exact ((A.glueEvaluation cover).satisfies_pullback_iff (cover.subset i) (fun _ _ x => x)
    (fun _ _ => Function.bijective_id) law support).1 held

/-- Structural validity of the glued primitive data follows from covering each primitive symbol. -/
theorem glueEvaluation_structural : (A.glueEvaluation cover).Structural := by
  intro rule kept
  let i := cover.index kept
  have localKept : Declaration.graphRuleName rule ∈ (cover.piece i).declarations := cover.mem_index kept
  exact A.glueEvaluation_satisfies cover i rule.toLaw (graphRuleSupport rule localKept)
    ((A.pieceModel i).obj.structural rule localKept)

/-- The combined carriers and graphs form a structure of the restricted presentation. -/
noncomputable def glueStructure : ContextStructure U where
  carrier := A.glueCarrier cover
  omitted := A.glueCarrier_omitted cover
  evaluation := A.glueEvaluation cover
  structural := A.glueEvaluation_structural cover

/-- Each required Law of the glued structure is obtained from a piece covering its declaration. -/
noncomputable def glue : Models U :=
  ⟨A.glueStructure cover, fun name => by
    let i := cover.index name.property
    have localKept : Declaration.law name.val.val ∈ (cover.piece i).declarations := cover.mem_index name.property
    exact A.glueEvaluation_satisfies cover i (U.scopedTheory.law name)
      (Declaration.lawBody_subset_of_mem localKept)
      ((A.pieceModel i).satisfies_required ⟨name.val, localKept⟩)⟩

/-- The assembled model restricts to the original model in every piece. -/
@[simp] theorem glue_restrict (i : cover.Index) : (A.glue cover).restrict (cover.subset i) = A.pieceModel i :=
  ObjectProperty.FullSubcategory.ext ((A.glueStructure cover).restrict_eq_of_view (A.pieceModel i).obj
    (cover.subset i) (A.glueCarrier_eq_piece cover i) (A.glueEvaluation_view cover i))

end Match
end DeclarationContext

namespace DeclarationCover

open CategoryTheory DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P} (cover : DeclarationCover U)

/-- Restricting a global model gives a strictly matching family in every declaration cover. -/
noncomputable def read (A : Models U) : Match cover.piece where
  pieceModel i := A.restrict (cover.subset i)
  overlap_eq i j :=
    (A.restrict_comp (cover.subset i) (overlapLeft cover.piece i j)).trans
      (A.restrict_comp (cover.subset j) (overlapRight cover.piece i j)).symm

/-- The local entry in a global model's matching family is exactly its reduct. -/
@[simp] theorem read_pieceModel (A : Models U) (i : cover.Index) :
    (cover.read A).pieceModel i = A.restrict (cover.subset i) :=
  rfl

/-- Agreement of the reducts on the whole cover forces agreement of the global models. -/
theorem models_eq_of_restrict_eq {A B : Models U}
    (same : ∀ i, A.restrict (cover.subset i) = B.restrict (cover.subset i)) : A = B := by
  have sameStructure (i : cover.Index) : A.obj.restrict (cover.subset i) = B.obj.restrict (cover.subset i) :=
    congrArg (fun M => M.obj) (same i)
  have carrierEq : A.obj.carrier = B.obj.carrier := ContextStructure.carrier_ext (fun s kept => by
    let i := cover.index kept
    have keepLocal : Declaration.sort s ∈ (cover.piece i).declarations := cover.mem_index kept
    exact (A.obj.restrict_carrier (cover.subset i) keepLocal).symm.trans
      ((congrArg (fun X => X.carrier s) (sameStructure i)).trans
        (B.obj.restrict_carrier (cover.subset i) keepLocal)))
  have localViews (i : cover.Index) :
      A.obj.evaluation.pullback (cover.subset i) (fun s _ => cast (congrFun carrierEq.symm s)) =
        B.obj.evaluation.pullback (cover.subset i) (fun _ _ x => x) := by
    let f : CarrierMap (cover.piece i) B.obj.carrier A.obj.carrier :=
      fun s _ => cast (congrFun carrierEq.symm s)
    let g : CarrierMap (cover.piece i) B.obj.carrier B.obj.carrier := fun _ _ x => x
    have views := ContextStructure.pullback_along_eq (sameStructure i) (le_refl _)
      (fun s keep x => cast (A.obj.restrict_carrier (cover.subset i) (s := s) keep).symm (f s keep x))
      (fun s keep x => cast (B.obj.restrict_carrier (cover.subset i) (s := s) keep).symm (g s keep x)) (by
        intro s keep x
        simp only [f, g, cast_cast])
    rw [ContextStructure.restrict_evaluation_view A.obj (cover.subset i) f,
      ContextStructure.restrict_evaluation_view B.obj (cover.subset i) g] at views
    exact views
  apply ObjectProperty.FullSubcategory.ext
  apply ContextStructure.ext carrierEq
  rw [RestrictedEvaluation.cast_evaluation _ carrierEq]
  apply RestrictedEvaluation.ext
  · intro r kept e
    let i := cover.index kept
    have keepLocal : Declaration.relation r ∈ (cover.piece i).declarations := cover.mem_index kept
    have fact := congrArg (fun (R : RestrictedEvaluation _ _) => R.relation r keepLocal e) (localViews i)
    simpa only [RestrictedEvaluation.pullback_relation, mapAssignment_id] using Iff.of_eq fact
  · intro p kept e
    let i := cover.index kept
    have keepLocal : Declaration.partialOp p ∈ (cover.piece i).declarations := cover.mem_index kept
    have fact := congrArg (fun (R : RestrictedEvaluation _ _) => R.domain p keepLocal e) (localViews i)
    simpa only [RestrictedEvaluation.pullback_domain, mapAssignment_id] using Iff.of_eq fact
  · intro op kept e y
    let i := cover.index kept
    have keepLocal : Declaration.ofOperation op ∈ (cover.piece i).declarations := cover.mem_index kept
    have fact := congrArg (fun (R : RestrictedEvaluation _ _) => R.graph op keepLocal e y) (localViews i)
    simpa only [RestrictedEvaluation.pullback_graph, mapAssignment_id] using Iff.of_eq fact

/-- Theorem 3.4: a strict matching family has exactly one global model restricting to it. -/
theorem existsUnique_glue (A : Match cover.piece) :
    ∃! X : Models U, ∀ i, X.restrict (cover.subset i) = A.pieceModel i :=
  ⟨A.glue cover, A.glue_restrict cover, fun _ same =>
    cover.models_eq_of_restrict_eq (fun i => (same i).trans (A.glue_restrict cover i).symm)⟩

/-- Gluing globally restricted models recovers the whole original model. -/
@[simp] theorem glue_read (A : Models U) : (cover.read A).glue cover = A :=
  cover.models_eq_of_restrict_eq fun i => (cover.read A).glue_restrict cover i

/-- Reading the glued model recovers the entire matching family. -/
@[simp] theorem read_glue (A : Match cover.piece) : cover.read (A.glue cover) = A :=
  Match.ext (A.glue_restrict cover)

end DeclarationCover
end SHIGURE
