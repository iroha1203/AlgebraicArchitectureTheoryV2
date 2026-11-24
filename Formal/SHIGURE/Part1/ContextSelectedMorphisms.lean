import Formal.SHIGURE.Part1.ContextSelectedStructures

/-! # The same structural arrows in the two presentations -/

universe u

namespace SHIGURE
namespace StructureMap

/-- Preserving primitive relations, domains and operation graphs is precisely enough for a structure map. -/
def ofGraphs {S : Signature.{u}} {A B : Structure S} (f : ∀ s, A.carrier s → B.carrier s)
    (rel : ∀ r (x : Assignment A.carrier (S.relInputs r)), x ∈ A.relation r → x.map f ∈ B.relation r)
    (dom : ∀ p (x : Assignment A.carrier (S.partialArity p).inputs),
      x ∈ A.partialDomain p → x.map f ∈ B.partialDomain p)
    (graph : ∀ (op : Operation S) (x : Assignment A.carrier op.arity.inputs) (y : A.carrier op.arity.output),
      A.Graph op x y → B.Graph op (x.map f) (f _ y)) : StructureMap A B where
  onSort := f
  relation_mem := rel
  partial_mem := dom
  total_comm t x := ((B.graph_total_iff t (x.map f) _).1
    (graph (.total t) x (A.total t x) ((A.graph_total_iff t x _).2 rfl))).symm
  partial_comm p x := by
    have reached := graph (.partialOp p) x.val (A.partialValue p x)
      ((A.graph_partial_iff p x.val _).2 ⟨x.property, rfl⟩)
    exact ((B.graph_partial_iff p _ _).1 reached).choose_spec.symm
  quantity_comm q x := ((B.graph_quantity_iff q (x.map f) _).1
    (graph (.quantity q) x (A.quantity q x) ((A.graph_quantity_iff q x _).2 rfl))).symm

end StructureMap

namespace DeclarationContext.Selected

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}
  {X X' : P.signature.SortType → Type u} {Y Y' : SortName U → Type u}

/-- Moving all tuple values by a structural arrow commutes with the reindexing of positions. -/
theorem map_selectAssignment (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    {Γ : List P.signature.SortType} (kept : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) :
    (selectAssignment e kept a).map g = selectAssignment e' kept (mapAssignment f kept a) := by
  apply Assignment.ext
  intro s i
  exact same s.val s.property (a (ambientVar kept i))

/-- Moving all input values of an operation agrees before and after selecting its arity. -/
theorem map_selectArgs (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations)
    (a : Assignment X op.arity.inputs) :
    (selectArgs e op kept a).map g = selectArgs e' op kept (mapAssignment f (operationInputs op kept) a) := by
  rw [selectArgs_eq_cast, selectArgs_eq_cast]
  cases op <;> simpa only [cast_eq] using map_selectAssignment e e' f g same _ a

/-- Moving the output value of an operation agrees before and after selecting its arity. -/
theorem map_selectResult (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    g _ (selectResult e op kept x) = selectResult e' op kept (f _ (operationOutput op kept) x) := by
  rw [selectResult_eq_cast, selectResult_eq_cast]
  cases op <;> simpa only [cast_eq] using same _ _ x

/-- Every tuple of the selected arity comes from a unique ambient tuple of the retained carriers. -/
def argsEquiv (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (kept : Declaration.ofOperation op ∈ U.declarations) :
    Assignment X op.arity.inputs ≃ Assignment Y (operation op kept).arity.inputs :=
  (assignmentEquiv e (operationInputs op kept)).trans
    (Equiv.cast (congrArg (fun profile => Assignment Y profile.inputs) (operation_arity op kept).symm))

/-- Every value of the selected result sort comes from a unique value of the retained carrier. -/
def resultEquiv (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (kept : Declaration.ofOperation op ∈ U.declarations) : X op.arity.output ≃ Y (operation op kept).arity.output :=
  (e _ (operationOutput op kept)).trans
    (Equiv.cast (congrArg (fun profile => Y profile.output) (operation_arity op kept).symm))

/-- The input equivalence for a retained operation acts by the input selection
of Proposition 3.2. Use it to obtain ambient preimages in the graph comparison. -/
theorem argsEquiv_apply (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (a : Assignment X op.arity.inputs) :
    argsEquiv e op keep a = selectArgs e op keep a :=
  rfl

/-- The outcome equivalence for a retained operation acts by the output selection
of Proposition 3.2. Use it to obtain ambient preimages in the graph comparison. -/
theorem resultEquiv_apply (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    resultEquiv e op keep x = selectResult e op keep x :=
  rfl

variable {A B : ContextStructure U}

/-- The same point map can be indexed by the actual retained sort names. -/
def readOnSort (f : ContextStructure.Hom A B) (s : SortName U) :
    (readStructure A).carrier s → (readStructure B).carrier s :=
  f.onSort s.val s.property

/-- An ambient-indexed context arrow preserves graphs read in the actual selected signature. -/
theorem readGraph (f : ContextStructure.Hom A B) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations)
    (xs : Assignment (readStructure A).carrier (operation op keep).arity.inputs)
    (y : (readStructure A).carrier (operation op keep).arity.output)
    (held : (readStructure A).Graph (operation op keep) xs y) :
    (readStructure B).Graph (operation op keep) (xs.map (readOnSort f)) (readOnSort f _ y) := by
  obtain ⟨x, hx⟩ := (argsEquiv (readCarrierEquiv A) op keep).surjective xs
  obtain ⟨z, hz⟩ := (resultEquiv (readCarrierEquiv A) op keep).surjective y
  rw [← hx, ← hz, argsEquiv_apply, resultEquiv_apply] at held ⊢
  rw [map_selectArgs (readCarrierEquiv A) (readCarrierEquiv B) f.onSort (readOnSort f)
      (fun _ _ _ => rfl) op keep x,
    map_selectResult (readCarrierEquiv A) (readCarrierEquiv B) f.onSort (readOnSort f)
      (fun _ _ _ => rfl) op keep z]
  exact ((readStructure_matches B).graph op keep _ _).2
    (f.graph_mem op keep x z (((readStructure_matches A).graph op keep x z).1 held))

/-- A context arrow reads as an ordinary structure map, with the same carrier components. -/
noncomputable def readStructureMap (f : ContextStructure.Hom A B) : StructureMap (readStructure A) (readStructure B) :=
  StructureMap.ofGraphs (readOnSort f) (by
    intro r xs held
    let keep := relationInputs r.val r.property
    obtain ⟨x, rfl⟩ := (assignmentEquiv (readCarrierEquiv A) keep).surjective xs
    change (readStructure A).relation r (selectAssignment (readCarrierEquiv A) keep x) at held
    change (readStructure B).relation r ((selectAssignment (readCarrierEquiv A) keep x).map _)
    rw [map_selectAssignment _ (readCarrierEquiv B) f.onSort _ (fun _ _ _ => rfl)]
    exact ((readStructure_matches B).relation r.val r.property _).2
      (f.relation_mem r.val r.property x (((readStructure_matches A).relation r.val r.property x).1 held))) (by
    intro p xs held
    let keep := operationInputs (.partialOp p.val) p.property
    obtain ⟨x, rfl⟩ := (assignmentEquiv (readCarrierEquiv A) keep).surjective xs
    change (readStructure A).partialDomain p (selectAssignment (readCarrierEquiv A) keep x) at held
    change (readStructure B).partialDomain p ((selectAssignment (readCarrierEquiv A) keep x).map _)
    rw [map_selectAssignment _ (readCarrierEquiv B) f.onSort _ (fun _ _ _ => rfl)]
    exact ((readStructure_matches B).domain p.val p.property _).2
      (f.domain_mem p.val p.property x (((readStructure_matches A).domain p.val p.property x).1 held))) (by
    intro op xs y held
    cases op with
    | total f' => exact readGraph f (.total f'.val) f'.property xs y held
    | partialOp p => exact readGraph f (.partialOp p.val) p.property xs y held
    | quantity q => exact readGraph f (.quantity q.val) q.property xs y held)

/-- The read ordinary arrow preserves the same point map at each retained sort. -/
theorem readStructureMap_onSort (f : ContextStructure.Hom A B) (s : SortName U) (x : A.carrier s.val) :
    (readStructureMap f).onSort s x = f.onSort s.val s.property x :=
  rfl

variable {C D : Structure (signature U)}

/-- Write the ordinary sort maps under the original sort names. -/
noncomputable def writeOnSort (f : StructureMap C D) : CarrierMap U (extendedCarrier C) (extendedCarrier D) :=
  fun s keep x => (extendedEquiv D s keep).symm (f.onSort ⟨s, keep⟩ (extendedEquiv C s keep x))

/-- The square of corresponding sort maps commutes. -/
theorem writeOnSort_comm (f : StructureMap C D) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : extendedCarrier C s) :
    f.onSort ⟨s, keep⟩ (extendedEquiv C s keep x) = extendedEquiv D s keep (writeOnSort f s keep x) :=
  ((extendedEquiv D s keep).apply_symm_apply _).symm

/-- An ordinary structure map gives the original-name structural arrow. -/
noncomputable def writeStructureMap (f : StructureMap C D) : ContextStructure.Hom (writeStructure C) (writeStructure D) where
  onSort := writeOnSort f
  relation_mem r keep a held := by
    have mapped := f.relation_mem ⟨r, keep⟩ _ (((extendedEvaluation_matches C).relation r keep a).2 held)
    rw [map_selectAssignment _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((extendedEvaluation_matches D).relation r keep _).1 mapped
  domain_mem p keep a held := by
    have mapped := f.partial_mem ⟨p, keep⟩ _ (((extendedEvaluation_matches C).domain p keep a).2 held)
    rw [map_selectAssignment _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((extendedEvaluation_matches D).domain p keep _).1 mapped
  graph_mem op keep a x held := by
    have mapped := f.map_graph (operation op keep) _ _ (((extendedEvaluation_matches C).graph op keep a x).2 held)
    rw [map_selectArgs _ _ _ _ (writeOnSort_comm f), map_selectResult _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((extendedEvaluation_matches D).graph op keep _ _).1 mapped

/-- The written arrow acts by the transported ordinary component. -/
theorem writeStructureMap_onSort (f : StructureMap C D) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : extendedCarrier C s) :
    (writeStructureMap f).onSort s keep x = writeOnSort f s keep x :=
  rfl

end DeclarationContext.Selected
end SHIGURE
