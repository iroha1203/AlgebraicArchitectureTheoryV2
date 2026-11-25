import Formal.SHIGURE.Part2.Recovery.SelectedLaws

/-!
# Native reducts for a declaration inclusion

The typed reduct takes the same primitive facts on the same underlying
tuples as the Part I restriction of the original-name structure.
-/

universe u

noncomputable section

namespace SHIGURE.DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U V : DeclarationContext P}

private theorem namesOfLE_selectAssignment (inside : V ≤ U)
    {X : P.signature.SortType → Type u} {Y : SortName U → Type u} (e : CarrierEquiv U X Y)
    {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ V.declarations) (xs : Assignment X Γ) :
    cast (congrArg (Assignment Y) (namesOfLE_context inside Γ keep))
        ((selectAssignment (fun s hs => e s (inside hs)) keep xs).mapSorts (namesOfLE inside).onSort) =
      selectAssignment e (keep.trans inside) xs := by
  let h := namesOfLE_context inside Γ keep
  let a := (selectAssignment (fun s hs => e s (inside hs)) keep xs).mapSorts (namesOfLE inside).onSort
  let b := selectAssignment e (keep.trans inside) xs
  change cast (congrArg (Assignment Y) h) a = b
  apply (Equiv.cast (congrArg (Assignment Y) h.symm)).injective
  change cast (congrArg (Assignment Y) h.symm) (cast (congrArg (Assignment Y) h) a) = _
  simp only [cast_cast, cast_eq]
  apply Assignment.ext_mapSorts (namesOfLE inside).onSort
  intro s i
  obtain ⟨j, rfl⟩ : ∃ j : Var Γ s.val, selectVar keep j = i :=
    ⟨ambientVar keep i, selectVar_ambientVar keep i⟩
  rw [Equiv.cast_apply, Assignment.cast_context_apply h.symm]
  change a (Var.mapSorts (namesOfLE inside).onSort (selectVar keep j)) =
    b (Renaming.castContext h (Var.mapSorts (namesOfLE inside).onSort (selectVar keep j)))
  rw [namesOfLE_selectVar inside keep j]
  simp only [a, b, Assignment.mapSorts_apply, selectAssignment_apply, ambientVar_selectVar]
  rfl

private theorem assignment_ndrec {K : Type u} (Y : K → Type u) {Γ Δ : List K}
    (h : Γ = Δ) (a : Assignment Y Γ) : (h ▸ a : Assignment Y Δ) = cast (congrArg (Assignment Y) h) a := by
  cases h
  rfl

private theorem mapSorts_castContext {K L : Type u} (g : K → L) (Y : L → Type u)
    {Γ Δ : List K} (h : Γ = Δ) (a : Assignment (Y ∘ g) Γ) :
    (cast (congrArg (Assignment (Y ∘ g)) h) a).mapSorts g =
      cast (congrArg (Assignment Y) (congrArg (List.map g) h)) (a.mapSorts g) := by
  cases h
  rfl

private theorem namedReduct_matches (inside : V ≤ U) (M : Structure (signature U)) :
    EvaluationMatches ((writeStructure M).evaluation.pullback inside (fun _ _ x => x))
      ((namesOfLE inside).restrict M) (fun s keep => writeCarrierEquiv M s (inside keep)) := by
  let n := namesOfLE inside
  let e := writeCarrierEquiv M
  let e' : CarrierEquiv V (writeStructure M).carrier (n.restrict M).carrier := fun s keep => e s (inside keep)
  have retype {Γ : List P.signature.SortType} (keep : Declaration.sorts Γ ⊆ V.declarations)
      (a : Assignment (writeStructure M).carrier Γ) := namesOfLE_selectAssignment inside e keep a
  constructor
  · intro r keep a
    change _ ∈ (n.restrict M).relation ⟨r, keep⟩ ↔ _
    rw [n.restrict_relation_mem_iff, RestrictedEvaluation.pullback_relation, mapAssignment_id]
    rw [assignment_ndrec M.carrier,
      mapSorts_castContext n.onSort M.carrier (signature_relInputs ⟨r, keep⟩).symm, cast_cast]
    change M.relation ⟨r, inside keep⟩
      (cast (congrArg (Assignment M.carrier) (namesOfLE_context inside _ (relationInputs r keep)))
        ((selectAssignment e' (relationInputs r keep) a).mapSorts n.onSort)) ↔ _
    rw [retype]
    exact (writeStructure_matches M).relation r (inside keep) a
  · intro p keep a
    let kept := operationInputs (.partialOp p) (Declaration.ofOperation_partialOp_mem p keep)
    change _ ∈ (n.restrict M).partialDomain ⟨p, keep⟩ ↔ _
    rw [n.restrict_partialDomain_mem_iff, RestrictedEvaluation.pullback_domain, mapAssignment_id]
    rw [assignment_ndrec M.carrier,
      mapSorts_castContext n.onSort M.carrier (signature_partialInputs ⟨p, keep⟩).symm, cast_cast]
    change M.partialDomain ⟨p, inside keep⟩
      (cast (congrArg (Assignment M.carrier) (namesOfLE_context inside _ kept))
        ((selectAssignment e' kept a).mapSorts n.onSort)) ↔ _
    rw [retype]
    exact (writeStructure_matches M).domain p (inside keep) a
  · intro op keep a y
    let kept := operationInputs op keep
    rw [n.restrict_graph_iff, RestrictedEvaluation.pullback_graph, mapAssignment_id]
    rw [selectArgs_eq_inputs_cast, selectResult_eq_output_cast, assignment_ndrec M.carrier,
      mapSorts_castContext n.onSort M.carrier (operation_selectedInputs (keep := keep) rfl).symm,
      cast_cast, cast_cast]
    have args := retype kept a
    have fact := (writeStructure_matches M).graph op (inside keep) a y
    cases op <;>
      change M.Graph (operation _ (inside keep))
        (cast (congrArg (Assignment M.carrier) (namesOfLE_context inside _ kept))
          ((selectAssignment e' kept a).mapSorts n.onSort))
        (e _ (inside (operationOutput _ keep)) y) ↔ _ <;>
      rw [args] <;> exact fact

/-- Writing the typed native reduct yields exactly the original-name Part I restriction. -/
theorem writeStructure_namesOfLE_restrict (inside : V ≤ U) (M : Structure (signature U)) :
    (writeStructure M).restrict inside = writeStructure ((namesOfLE inside).restrict M) := by
  let M' := (namesOfLE inside).restrict M
  let A := writeStructure M
  let B := writeStructure M'
  have carriers (s : P.signature.SortType) (keep : Declaration.sort s ∈ V.declarations) :
      A.carrier s = B.carrier s :=
    (congrFun (writeStructure_carrier_eq M) s).trans
      ((extendedCarrier_kept M s (inside keep)).trans
        ((extendedCarrier_kept M' s keep).symm.trans
          (congrFun (writeStructure_carrier_eq M') s).symm))
  let f : CarrierMap V A.carrier B.carrier := fun s keep => cast (carriers s keep)
  let e : CarrierEquiv V A.carrier M'.carrier := fun s keep => writeCarrierEquiv M s (inside keep)
  have align : ∀ s keep x, writeCarrierEquiv M' s keep (f s keep x) = e s keep x := by
    intro s keep x
    rw [show e s keep x = writeCarrierEquiv M s (inside keep) x from rfl, writeCarrierEquiv_eq_cast,
      writeCarrierEquiv_eq_cast]
    simp only [f, Equiv.cast_apply, cast_cast]
  have source := namedReduct_matches inside M
  have target := writeStructure_matches M'
  apply ContextStructure.restrict_eq_of_view A B inside carriers
  apply RestrictedEvaluation.ext
  · intro r keep a
    rw [RestrictedEvaluation.pullback_relation B.evaluation, ← target.relation,
      selectAssignment_mapCarrier _ f e align]
    exact (source.relation r keep a).symm
  · intro p keep a
    rw [RestrictedEvaluation.pullback_domain B.evaluation, ← target.domain,
      selectAssignment_mapCarrier _ f e align]
    exact (source.domain p keep a).symm
  · intro op keep a y
    rw [RestrictedEvaluation.pullback_graph B.evaluation, ← target.graph,
      selectArgs_mapCarrier _ f e align, selectResult_mapCarrier _ f e align]
    exact (source.graph op keep a y).symm

end SHIGURE.DeclarationContext.Selected
