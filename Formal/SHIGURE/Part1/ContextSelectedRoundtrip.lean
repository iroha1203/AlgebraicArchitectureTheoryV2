import Formal.SHIGURE.Part1.ContextSelectedStructures

/-! # Exact round trips on the two structure representations -/

universe u

namespace SHIGURE
namespace Structure

/-- The full carriers and all relation, domain and graph facts determine a structure. -/
theorem eq_of_graphs {S : Signature.{u}} {A B : Structure S} (carriers : A.carrier = B.carrier)
    (relations : ∀ r (x : Assignment B.carrier (S.relInputs r)),
      x.map (fun s => cast (congrFun carriers.symm s)) ∈ A.relation r ↔ x ∈ B.relation r)
    (domains : ∀ p (x : Assignment B.carrier (S.partialArity p).inputs),
      x.map (fun s => cast (congrFun carriers.symm s)) ∈ A.partialDomain p ↔ x ∈ B.partialDomain p)
    (graphs : ∀ (op : Operation S) (x : Assignment B.carrier op.arity.inputs) (y : B.carrier op.arity.output),
      A.Graph op (x.map (fun s => cast (congrFun carriers.symm s))) (cast (congrFun carriers.symm _) y) ↔
      B.Graph op x y) : A = B := by
  cases A with
  | mk X af ar ad ap aq =>
    cases B with
    | mk Y bf br bd bp bq =>
      cases carriers
      let old : Structure S := ⟨X, af, ar, ad, ap, aq⟩
      let new : Structure S := ⟨X, bf, br, bd, bp, bq⟩
      change ∀ op x y, old.Graph op x y ↔ new.Graph op x y at graphs
      have sameR : ar = br := funext fun r => Set.ext (relations r)
      have sameD : ad = bd := funext fun p => Set.ext (domains p)
      have sameF : af = bf := funext fun f => funext fun x => by
        have truth := (graphs (.total f) x (af f x)).1 ((old.graph_total_iff f x _).2 rfl)
        exact ((new.graph_total_iff f x _).1 truth).symm
      have sameQ : aq = bq := funext fun q => funext fun x => by
        have truth := (graphs (.quantity q) x (aq q x)).1 ((old.graph_quantity_iff q x _).2 rfl)
        exact ((new.graph_quantity_iff q x _).1 truth).symm
      cases sameD
      have sameP : ap = bp := funext fun p => funext fun x => by
        have truth := (graphs (.partialOp p) x.val (ap p x)).1
          ((old.graph_partial_iff p x.val _).2 ⟨x.property, rfl⟩)
        obtain ⟨_, same⟩ := (new.graph_partial_iff p x.val _).1 truth
        exact same.symm
      cases sameR
      cases sameF
      cases sameQ
      cases sameP
      rfl

end Structure

namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- The round trip through an ordinary structure keeps every context carrier type. -/
theorem write_read_carriers (A : ContextStructure U) : (writeStructure (readStructure A)).carrier = A.carrier :=
  ContextStructure.carrier_ext fun s keep =>
    (congrFun (writeStructure_carrier_eq (readStructure A)) s).trans
      ((extendedCarrier_kept (readStructure A) s keep).trans (readStructure_carrier_eq A ⟨s, keep⟩))

/-- Recover the given context structure by reading and writing it, as used
in the model comparison for Proposition 3.2. The carrier identification comes
from the retained sorts, and the retained facts determine the structure. -/
@[simp] theorem write_read_structure (A : ContextStructure U) : writeStructure (readStructure A) = A := by
  let B := readStructure A
  let h := write_read_carriers A
  let carriers := (writeStructure_carrier_eq B).symm.trans h
  let f : CarrierMap U A.carrier (extendedCarrier B) := fun s _ => cast (congrFun carriers.symm s)
  have component : ∀ s keep x, extendedEquiv B s keep (f s keep x) = readCarrierEquiv A s keep x := by
    intro s keep x
    simp only [extendedEquiv_eq_cast, Equiv.cast_apply, f, readCarrierEquiv_eq_cast, cast_cast]
  apply ContextStructure.ext h
  rw [writeStructure_cast_evaluation B h, RestrictedEvaluation.cast_evaluation (extendedEvaluation B) carriers]
  apply RestrictedEvaluation.ext
  · intro r keep a
    rw [RestrictedEvaluation.pullback_relation, ← (extendedEvaluation_matches B).relation r keep]
    rw [selectAssignment_mapCarrier _ _ _ component]
    exact (readStructure_matches A).relation r keep a
  · intro p keep a
    rw [RestrictedEvaluation.pullback_domain, ← (extendedEvaluation_matches B).domain p keep]
    rw [selectAssignment_mapCarrier _ _ _ component]
    exact (readStructure_matches A).domain p keep a
  · intro op keep a y
    rw [RestrictedEvaluation.pullback_graph, ← (extendedEvaluation_matches B).graph op keep]
    rw [selectArgs_mapCarrier _ _ _ component, selectResult_mapCarrier _ _ _ component]
    exact (readStructure_matches A).graph op keep a y

/-- Writing then reading keeps every actual selected carrier type. -/
theorem read_write_carriers (B : Structure (signature U)) : (readStructure (writeStructure B)).carrier = B.carrier :=
  funext fun s => ((readStructure_carrier_eq (writeStructure B) s).trans
    (congrFun (writeStructure_carrier_eq B) s.val)).trans (extendedCarrier_kept B s.val s.property)

/-- The inverse carrier casts take a selected tuple back to its tuple of original values. -/
theorem read_write_args (B : Structure (signature U)) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (x : Assignment B.carrier (context Γ keep)) :
    x.map (fun s => cast (congrFun (read_write_carriers B).symm s)) =
      selectAssignment (readCarrierEquiv (writeStructure B)) keep (ambientAssignment (writeCarrierEquiv B) keep x) := by
  apply Assignment.ext
  intro s i
  simp only [Assignment.map_apply, selectAssignment_apply, ambientAssignment_apply, selectVar_ambientVar,
    readCarrierEquiv_eq_cast, writeCarrierEquiv_eq_cast, ← Equiv.cast_symm, Equiv.cast_apply, cast_cast]

/-- The inverse carrier cast on an output identifies the written value in the read structure. -/
theorem read_write_value (B : Structure (signature U)) (s : SortName U) (y : B.carrier s) :
    cast (congrFun (read_write_carriers B).symm s) y =
      readCarrierEquiv (writeStructure B) s.val s.property ((writeCarrierEquiv B s.val s.property).symm y) := by
  simp only [readCarrierEquiv_eq_cast, writeCarrierEquiv_eq_cast, ← Equiv.cast_symm, Equiv.cast_apply, cast_cast]

/-- Carrier transport at an actual selected input list uses the corresponding ambient tuple. -/
private theorem read_write_args_cast (B : Structure (signature U)) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) {Δ : List (SortName U)}
    (shape : Δ = context Γ keep) (x : Assignment B.carrier Δ) :
    x.map (fun s => cast (congrFun (read_write_carriers B).symm s)) =
      cast (congrArg (Assignment (readStructure (writeStructure B)).carrier) shape.symm)
        (selectAssignment (readCarrierEquiv (writeStructure B)) keep
          (ambientAssignment (writeCarrierEquiv B) keep (cast (congrArg (Assignment B.carrier) shape) x))) := by
  subst Δ
  exact read_write_args B keep x

/-- Reading and selecting an actual tuple in the same structure cancels both transports. -/
private theorem written_args_inverse (B : Structure (signature U)) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) {Δ : List (SortName U)}
    (shape : Δ = context Γ keep) (x : Assignment B.carrier Δ) :
    cast (congrArg (Assignment B.carrier) shape.symm)
      (selectAssignment (writeCarrierEquiv B) keep
        (ambientAssignment (writeCarrierEquiv B) keep (cast (congrArg (Assignment B.carrier) shape) x))) = x := by
  rw [selectAssignment_ambientAssignment, cast_cast, cast_eq]

/-- The output carrier transport uses the corresponding retained original sort. -/
private theorem read_write_value_cast (B : Structure (signature U)) {s t : SortName U}
    (shape : s = t) (y : B.carrier s) :
    cast (congrFun (read_write_carriers B).symm s) y =
      cast (congrArg (readStructure (writeStructure B)).carrier shape.symm)
        (readCarrierEquiv (writeStructure B) t.val t.property
          ((writeCarrierEquiv B t.val t.property).symm (cast (congrArg B.carrier shape) y))) := by
  cases shape
  exact read_write_value B s y

attribute [local irreducible] arity in
/-- The compared structures have the same graph at the actual selected operation profile. -/
private theorem read_write_graph (B : Structure (signature U))
    (op : Operation P.signature) (keep : Declaration.ofOperation op ∈ U.declarations)
    (selected : Operation (signature U)) (same : operation op keep = selected)
    (x : Assignment B.carrier selected.arity.inputs) (y : B.carrier selected.arity.output) :
    (readStructure (writeStructure B)).Graph selected
      (x.map (fun s => cast (congrFun (read_write_carriers B).symm s)))
      (cast (congrFun (read_write_carriers B).symm selected.arity.output) y) ↔ B.Graph selected x y := by
  let A := writeStructure B
  let shape := operation_selectedInputs same
  let output := operation_selectedOutput same
  let a := ambientAssignment (writeCarrierEquiv B) (operationInputs op keep)
    (cast (congrArg (Assignment B.carrier) shape) x)
  let z := (writeCarrierEquiv B _ (operationOutput op keep)).symm (cast (congrArg B.carrier output) y)
  rw [read_write_args_cast B (operationInputs op keep) shape x, read_write_value_cast B output y]
  have left := (graph_select_congr (readStructure A) (readCarrierEquiv A) op keep selected same a z).symm.trans
    ((readStructure_matches A).graph op keep a z)
  have right := (graph_select_congr B (writeCarrierEquiv B) op keep selected same a z).symm.trans
    ((writeStructure_matches B).graph op keep a z)
  rw [written_args_inverse B (operationInputs op keep) shape x] at right
  have inverse : cast (congrArg B.carrier output.symm)
      (writeCarrierEquiv B _ (operationOutput op keep) z) = y := by
    rw [show z = _ from rfl, Equiv.apply_symm_apply, cast_cast, cast_eq]
  rw [inverse] at right
  exact left.trans right.symm

attribute [local irreducible] arity in
/-- Recover the given ordinary selected structure by writing and reading it,
as used in the model comparison for Proposition 3.2. Its retained relations,
domains and graphs determine the structure after the carrier identification. -/
@[simp] theorem read_write_structure (B : Structure (signature U)) : readStructure (writeStructure B) = B := by
  let A := writeStructure B
  let h := read_write_carriers B
  apply Structure.eq_of_graphs h
  · intro r x
    let keep := relationInputs r.val r.property
    let shape := signature_relInputs r
    let a := ambientAssignment (writeCarrierEquiv B) keep (cast (congrArg (Assignment B.carrier) shape) x)
    change (readStructure A).relation r (x.map (fun s => cast (congrFun h.symm s))) ↔ B.relation r x
    rw [read_write_args_cast B keep shape x]
    have left := (readStructure_matches A).relation_cast r a
    have right := (writeStructure_matches B).relation_cast r a
    rw [written_args_inverse B keep shape x] at right
    exact left.trans right.symm
  · intro p x
    let keep := operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)
    let shape := signature_partialInputs p
    let a := ambientAssignment (writeCarrierEquiv B) keep (cast (congrArg (Assignment B.carrier) shape) x)
    change (readStructure A).partialDomain p (x.map (fun s => cast (congrFun h.symm s))) ↔ B.partialDomain p x
    rw [read_write_args_cast B keep shape x]
    have left := (readStructure_matches A).domain_cast p a
    have right := (writeStructure_matches B).domain_cast p a
    rw [written_args_inverse B keep shape x] at right
    exact left.trans right.symm
  · intro op x y
    cases op with
    | total f =>
      let kept := Declaration.ofOperation_total_mem f.val f.property
      exact read_write_graph B (.total f.val) kept (.total f) (operation_total f.val kept) x y
    | partialOp p =>
      let kept := Declaration.ofOperation_partialOp_mem p.val p.property
      exact read_write_graph B (.partialOp p.val) kept (.partialOp p) (operation_partialOp p.val kept) x y
    | quantity q =>
      let kept := Declaration.ofOperation_quantity_mem q.val q.property
      exact read_write_graph B (.quantity q.val) kept (.quantity q) (operation_quantity q.val kept) x y

/-- The model readings are strictly inverse on ordinary model objects. -/
@[simp] theorem read_write_model (A : Model (theory U)) : readModel (writeModel A) = A := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  rw [readModel_obj, writeModel_obj]
  exact read_write_structure A.obj

/-- The model readings are strictly inverse on context model objects. -/
@[simp] theorem write_read_model (A : Models U) : writeModel (readModel A) = A := by
  apply CategoryTheory.ObjectProperty.FullSubcategory.ext
  rw [writeModel_obj, readModel_obj]
  exact write_read_structure A.obj

end DeclarationContext.Selected
end SHIGURE
