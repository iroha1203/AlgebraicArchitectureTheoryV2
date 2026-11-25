import Formal.SHIGURE.Part1.ContextGluing

/-! # Strict assembly of matching arrows

At each sort a covering piece supplies the component of the assembled map.
The overlap equations make this independent of that piece. A covering piece
for each primitive then supplies the relevant preservation law.
-/

universe u

namespace SHIGURE
namespace DeclarationContext
namespace Match

open CategoryTheory

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
  (cover : DeclarationCover U) {A B : Match cover.piece} (f : Hom A B)

/-- Read a local arrow on the two glued carrier families. -/
noncomputable def arrowView (i : cover.Index) : CarrierMap (cover.piece i) (A.glueCarrier cover) (B.glueCarrier cover) :=
  fun s keep x => cast (B.glueCarrier_eq_piece cover i s keep).symm
    (Models.onSort (f.pieceMap i) s keep (A.toPieceCarrier cover i s keep x))

/-- The local component in Theorem 3.5 acts by the piece arrow between the
carrier identifications for the retained sort at each endpoint. -/
theorem arrowView_apply (i : cover.Index) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ (cover.piece i).declarations) (x : A.glueCarrier cover s) :
    arrowView cover f i s keep x = cast (B.glueCarrier_eq_piece cover i s keep).symm
      (Models.onSort (f.pieceMap i) s keep (A.toPieceCarrier cover i s keep x)) :=
  rfl

/-- The two local arrow views have identical values at each shared sort. -/
theorem arrowView_overlap (i j : cover.Index) (s : P.signature.SortType)
    (left : Declaration.sort s ∈ (cover.piece i).declarations)
    (right : Declaration.sort s ∈ (cover.piece j).declarations) (x : A.glueCarrier cover s) :
    arrowView cover f i s left x = arrowView cover f j s right x := by
  let L := overlapLeft cover.piece i j
  let R := overlapRight cover.piece i j
  have shared : Declaration.sort s ∈ (inter (cover.piece i) (cover.piece j)).declarations := ⟨left, right⟩
  let a := A.toPieceCarrier cover i s left x
  let localX : ((A.pieceModel i).restrict L).obj.carrier s :=
    cast ((A.pieceModel i).obj.restrict_carrier L (s := s) shared).symm a
  have agree := congrArg (fun h => Models.onSort h s shared localX) (f.overlap_comm i j)
  have transported := congrArg (fun z : ((B.pieceModel j).restrict R).obj.carrier s =>
    cast (B.glueCarrier_eq_piece cover j s right).symm
      (cast ((B.pieceModel j).obj.restrict_carrier R (s := s) shared) z)) agree
  simpa only [arrowView_apply, res_onSort, Models.comp_onSort, Models.eqToHom_onSort, selectedMap_apply, toPieceCarrier_apply,
    localX, a, cast_cast] using transported

/-- Each retained sort supplies one covering piece for its global component map. -/
noncomputable def glueOnSort : CarrierMap U (A.glueCarrier cover) (B.glueCarrier cover) :=
  fun s kept => arrowView cover f (cover.index kept) s (cover.mem_index kept)

/-- The assembled component agrees with the view from any piece keeping the sort. -/
theorem glueOnSort_eq_piece (i : cover.Index) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ (cover.piece i).declarations) (x : A.glueCarrier cover s) :
    glueOnSort cover f s (cover.subset i kept) x = arrowView cover f i s kept x :=
  arrowView_overlap cover f (cover.index (cover.subset i kept)) i s (cover.mem_index _) kept x

/-- Mapping a tuple globally gives its image under the arrow view on any piece supporting it. -/
theorem glueAssignment_eq_piece (i : cover.Index) {Γ : List P.signature.SortType}
    (kept : Declaration.sorts Γ ⊆ (cover.piece i).declarations) (e : Assignment (A.glueCarrier cover) Γ) :
    mapAssignment (glueOnSort cover f) (fun _ hd => cover.subset i (kept hd)) e =
      mapAssignment (arrowView cover f i) kept e := by
  apply Assignment.ext
  intro s var
  rw [mapAssignment_apply, mapAssignment_apply]
  exact glueOnSort_eq_piece cover f i s (varKept kept var) (e var)

/-- The local view of an assembled component commutes with transport to the target piece. -/
theorem toPieceCarrier_arrowView (i : cover.Index) (s : P.signature.SortType)
    (kept : Declaration.sort s ∈ (cover.piece i).declarations) (x : A.glueCarrier cover s) :
    B.toPieceCarrier cover i s kept (arrowView cover f i s kept x) =
      Models.onSort (f.pieceMap i) s kept (A.toPieceCarrier cover i s kept x) := by
  simp only [arrowView_apply, toPieceCarrier_apply, cast_cast]
  rfl

/-- Identifying an image tuple with the target piece agrees with mapping it there. -/
theorem arrowView_assignment (i : cover.Index) {Γ : List P.signature.SortType}
    (kept : Declaration.sorts Γ ⊆ (cover.piece i).declarations) (e : Assignment (A.glueCarrier cover) Γ) :
    mapAssignment (B.toPieceCarrier cover i) kept (mapAssignment (arrowView cover f i) kept e) =
      mapAssignment (Models.onSort (f.pieceMap i)) kept (mapAssignment (A.toPieceCarrier cover i) kept e) := by
  apply Assignment.ext
  intro s var
  simp only [mapAssignment_apply, toPieceCarrier_arrowView]

/-- Assembly preserves every retained relation using its covering piece. -/
theorem glue_relation (r : P.signature.Rel) (keep : Declaration.relation r ∈ U.declarations)
    (e : Assignment (A.glueCarrier cover) (P.signature.relInputs r))
    (held : (A.glueEvaluation cover).relation r keep e) :
    (B.glueEvaluation cover).relation r keep (mapAssignment (glueOnSort cover f) (relationInputs r keep) e) := by
  let i := cover.index keep
  have localKept : Declaration.relation r ∈ (cover.piece i).declarations := cover.mem_index keep
  have input : (A.localView cover i).relation r localKept e := by
    rw [← A.glueEvaluation_view cover i, RestrictedEvaluation.pullback_relation, mapAssignment_id]
    exact held
  have preserved : (B.localView cover i).relation r localKept
      (mapAssignment (arrowView cover f i) (relationInputs r localKept) e) := by
    simp only [localView_eq_pullback, RestrictedEvaluation.pullback_relation, arrowView_assignment] at input ⊢
    exact (show ContextStructure.Hom _ _ from (f.pieceMap i).hom).relation_mem r localKept _ input
  rw [← B.glueEvaluation_view cover i, RestrictedEvaluation.pullback_relation, mapAssignment_id,
    ← glueAssignment_eq_piece cover f i] at preserved
  exact preserved

/-- Assembly preserves every retained partial domain using its covering piece. -/
theorem glue_domain (p : P.signature.Partial) (keep : Declaration.partialOp p ∈ U.declarations)
    (e : Assignment (A.glueCarrier cover) (P.signature.partialArity p).inputs)
    (held : (A.glueEvaluation cover).domain p keep e) :
    (B.glueEvaluation cover).domain p keep
      (mapAssignment (glueOnSort cover f)
        (operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p keep)) e) := by
  let i := cover.index keep
  have localKept : Declaration.partialOp p ∈ (cover.piece i).declarations := cover.mem_index keep
  have input : (A.localView cover i).domain p localKept e := by
    rw [← A.glueEvaluation_view cover i, RestrictedEvaluation.pullback_domain, mapAssignment_id]
    exact held
  have preserved : (B.localView cover i).domain p localKept
      (mapAssignment (arrowView cover f i)
        (operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p localKept)) e) := by
    simp only [localView_eq_pullback, RestrictedEvaluation.pullback_domain, arrowView_assignment] at input ⊢
    exact (show ContextStructure.Hom _ _ from (f.pieceMap i).hom).domain_mem p localKept _ input
  rw [← B.glueEvaluation_view cover i, RestrictedEvaluation.pullback_domain, mapAssignment_id,
    ← glueAssignment_eq_piece cover f i] at preserved
  exact preserved

/-- Assembly preserves every retained operation graph using its covering piece. -/
theorem glue_graph (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (e : Assignment (A.glueCarrier cover) op.arity.inputs) (y : A.glueCarrier cover op.arity.output)
    (held : (A.glueEvaluation cover).graph op keep e y) :
    (B.glueEvaluation cover).graph op keep (mapAssignment (glueOnSort cover f) (operationInputs op keep) e)
      (glueOnSort cover f op.arity.output (operationOutput op keep) y) := by
  let i := cover.index keep
  have localKept : Declaration.ofOperation op ∈ (cover.piece i).declarations := cover.mem_index keep
  have input : (A.localView cover i).graph op localKept e y := by
    rw [← A.glueEvaluation_view cover i, RestrictedEvaluation.pullback_graph, mapAssignment_id]
    exact held
  have preserved : (B.localView cover i).graph op localKept
      (mapAssignment (arrowView cover f i) (operationInputs op localKept) e)
      (arrowView cover f i op.arity.output (operationOutput op localKept) y) := by
    simp only [localView_eq_pullback, RestrictedEvaluation.pullback_graph, arrowView_assignment, toPieceCarrier_arrowView]
      at input ⊢
    exact (show ContextStructure.Hom _ _ from (f.pieceMap i).hom).graph_mem op localKept _ _ input
  rw [← B.glueEvaluation_view cover i, RestrictedEvaluation.pullback_graph, mapAssignment_id,
    ← glueAssignment_eq_piece cover f i, ← glueOnSort_eq_piece cover f i] at preserved
  exact preserved

/-- The assembled arrow is a structure-preserving map between the two glued models. -/
noncomputable def glueMap : A.glue cover ⟶ B.glue cover := by
  let mapped : ContextStructure.Hom
      ⟨A.glueCarrier cover, A.glueCarrier_omitted cover, A.glueEvaluation cover, A.glueEvaluation_structural cover⟩
      ⟨B.glueCarrier cover, B.glueCarrier_omitted cover, B.glueEvaluation cover, B.glueEvaluation_structural cover⟩ := {
    onSort := glueOnSort cover f
    relation_mem := glue_relation cover f
    domain_mem := glue_domain cover f
    graph_mem := glue_graph cover f }
  exact ObjectProperty.homMk (cast (congrArg₂ ContextStructure.Hom (A.glue_obj_eq cover).symm
    (B.glue_obj_eq cover).symm) mapped)

/-- The categorical arrow assembled from local maps has the expected retained components. -/
theorem glueMap_onSort (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations)
    (x : (A.glue cover).obj.carrier s) : Models.onSort (glueMap cover f) s kept x =
      cast (congrFun (B.glue_carrier_eq cover).symm s)
        (glueOnSort cover f s kept (cast (congrFun (A.glue_carrier_eq cover) s) x)) := by
  rw [glueMap, Models.onSort_homMk,
    ContextStructure.Hom.cast_onSort (A.glue_obj_eq cover).symm (B.glue_obj_eq cover).symm]

/-- Restricting an assembled arrow recovers the local map after identifying the endpoints. -/
theorem glueMap_restrict (i : cover.Index) :
    (res (cover.subset i)).map (glueMap cover f) ≫ eqToHom (B.glue_restrict cover i) =
      eqToHom (A.glue_restrict cover i) ≫ f.pieceMap i := by
  apply Models.hom_ext
  intro s keep x
  simp only [Models.comp_onSort, Models.eqToHom_onSort, res_onSort, glueMap_onSort,
    glueOnSort_eq_piece cover f i s keep, arrowView_apply, toPieceCarrier_apply, selectedMap_apply, cast_cast]
  rfl

end Match
end DeclarationContext
end SHIGURE
