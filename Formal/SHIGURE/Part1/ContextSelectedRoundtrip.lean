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
  ContextStructure.carrier_ext (fun s keep => extendedCarrier_kept (readStructure A) s keep)

/-- Recover the given context structure by reading and writing it, as used
in the model comparison for Proposition 3.2. The carrier identification comes
from the retained sorts, and the retained facts determine the structure. -/
@[simp] theorem write_read_structure (A : ContextStructure U) : writeStructure (readStructure A) = A := by
  let B := readStructure A
  let h := write_read_carriers A
  let f : CarrierMap U A.carrier (writeStructure B).carrier := fun s _ => cast (congrFun h.symm s)
  have component : ∀ s keep x, extendedEquiv B s keep (f s keep x) = readCarrierEquiv A s keep x := by
    intro s keep x
    simp only [extendedEquiv_eq_cast, Equiv.cast_apply, f, readCarrierEquiv_eq_refl, Equiv.refl_apply, cast_cast]
    rfl
  apply ContextStructure.ext h
  rw [RestrictedEvaluation.cast_evaluation _ h]
  apply RestrictedEvaluation.ext
  · intro r keep a
    rw [RestrictedEvaluation.pullback_relation]
    change B.relation ⟨r, keep⟩ (selectAssignment (extendedEquiv B) (relationInputs r keep)
      (mapAssignment f (relationInputs r keep) a)) ↔ A.evaluation.relation r keep a
    rw [selectAssignment_mapCarrier _ _ _ component]
    exact (readStructure_matches A).relation r keep a
  · intro p keep a
    rw [RestrictedEvaluation.pullback_domain]
    change B.partialDomain ⟨p, keep⟩ (selectAssignment (extendedEquiv B) (operationInputs (.partialOp p) keep)
      (mapAssignment f (operationInputs (.partialOp p) keep) a)) ↔ A.evaluation.domain p keep a
    rw [selectAssignment_mapCarrier _ _ _ component]
    exact (readStructure_matches A).domain p keep a
  · intro op keep a y
    rw [RestrictedEvaluation.pullback_graph]
    change B.Graph (operation op keep) (selectArgs (extendedEquiv B) op keep
      (mapAssignment f (operationInputs op keep) a)) (selectResult (extendedEquiv B) op keep
        (f op.arity.output (operationOutput op keep) y)) ↔ _
    rw [selectArgs_mapCarrier _ _ _ component, selectResult_mapCarrier _ _ _ component]
    exact (readStructure_matches A).graph op keep a y

/-- Writing then reading keeps every actual selected carrier type. -/
theorem read_write_carriers (B : Structure (signature U)) : (readStructure (writeStructure B)).carrier = B.carrier :=
  funext fun s => extendedCarrier_kept B s.val s.property

/-- The inverse carrier casts take a selected tuple back to its tuple of original values. -/
theorem read_write_args (B : Structure (signature U)) {Γ : List P.signature.SortType}
    (keep : Declaration.sorts Γ ⊆ U.declarations) (x : Assignment B.carrier (context Γ keep)) :
    x.map (fun s => cast (congrFun (read_write_carriers B).symm s)) =
      selectAssignment (readCarrierEquiv (writeStructure B)) keep (ambientAssignment (extendedEquiv B) keep x) := by
  apply Assignment.ext
  intro s i
  change cast (congrFun (read_write_carriers B).symm s) (x i) =
    (extendedEquiv B s.val s.property).symm (x (selectVar keep (ambientVar keep i)))
  rw [selectVar_ambientVar keep i]
  rfl

/-- Recover the given ordinary selected structure by writing and reading it,
as used in the model comparison for Proposition 3.2. Its retained relations,
domains and graphs determine the structure after the carrier identification. -/
@[simp] theorem read_write_structure (B : Structure (signature U)) : readStructure (writeStructure B) = B := by
  let A := writeStructure B
  let h := read_write_carriers B
  apply Structure.eq_of_graphs h
  · intro r x
    let keep := relationInputs r.val r.property
    let a := ambientAssignment (extendedEquiv B) keep x
    change (readStructure A).relation r (x.map (fun s => cast (congrFun h.symm s))) ↔ B.relation r x
    rw [read_write_args B keep x]
    have left := (readStructure_matches A).relation r.val r.property a
    have right := (extendedEvaluation_matches B).relation r.val r.property a
    rw [selectAssignment_ambientAssignment (extendedEquiv B) keep x] at right
    exact left.trans right.symm
  · intro p x
    let keep := operationInputs (.partialOp p.val) p.property
    let a := ambientAssignment (extendedEquiv B) keep x
    change (readStructure A).partialDomain p (x.map (fun s => cast (congrFun h.symm s))) ↔ B.partialDomain p x
    rw [read_write_args B keep x]
    have left := (readStructure_matches A).domain p.val p.property a
    have right := (extendedEvaluation_matches B).domain p.val p.property a
    rw [selectAssignment_ambientAssignment (extendedEquiv B) keep x] at right
    exact left.trans right.symm
  · intro op x y
    cases op with
    | total f =>
      let keep := operationInputs (.total f.val) f.property
      let a := ambientAssignment (extendedEquiv B) keep x
      let z := (extendedEquiv B _ (operationOutput (.total f.val) f.property)).symm y
      rw [read_write_args B keep x]
      have left := (readStructure_matches A).graph (.total f.val) f.property a z
      have right := (extendedEvaluation_matches B).graph (.total f.val) f.property a z
      simp only [selectArgs_eq_cast, selectResult_eq_cast, cast_eq] at left right
      rw [selectAssignment_ambientAssignment (extendedEquiv B) keep x, Equiv.apply_symm_apply] at right
      exact left.trans right.symm
    | partialOp p =>
      let keep := operationInputs (.partialOp p.val) p.property
      let a := ambientAssignment (extendedEquiv B) keep x
      let z := (extendedEquiv B _ (operationOutput (.partialOp p.val) p.property)).symm y
      rw [read_write_args B keep x]
      have left := (readStructure_matches A).graph (.partialOp p.val) p.property a z
      have right := (extendedEvaluation_matches B).graph (.partialOp p.val) p.property a z
      simp only [selectArgs_eq_cast, selectResult_eq_cast, cast_eq] at left right
      rw [selectAssignment_ambientAssignment (extendedEquiv B) keep x, Equiv.apply_symm_apply] at right
      exact left.trans right.symm
    | quantity q =>
      let keep := operationInputs (.quantity q.val) q.property
      let a := ambientAssignment (extendedEquiv B) keep x
      let z := (extendedEquiv B _ (operationOutput (.quantity q.val) q.property)).symm y
      rw [read_write_args B keep x]
      have left := (readStructure_matches A).graph (.quantity q.val) q.property a z
      have right := (extendedEvaluation_matches B).graph (.quantity q.val) q.property a z
      simp only [selectArgs_eq_cast, selectResult_eq_cast, cast_eq] at left right
      rw [selectAssignment_ambientAssignment (extendedEquiv B) keep x, Equiv.apply_symm_apply] at right
      exact left.trans right.symm

/-- The model readings are strictly inverse on ordinary model objects. -/
@[simp] theorem read_write_model (A : Model (theory U)) : readModel (writeModel A) = A :=
  CategoryTheory.ObjectProperty.FullSubcategory.ext (read_write_structure A.obj)

/-- The model readings are strictly inverse on context model objects. -/
@[simp] theorem write_read_model (A : Models U) : writeModel (readModel A) = A :=
  CategoryTheory.ObjectProperty.FullSubcategory.ext (write_read_structure A.obj)

end DeclarationContext.Selected
end SHIGURE
