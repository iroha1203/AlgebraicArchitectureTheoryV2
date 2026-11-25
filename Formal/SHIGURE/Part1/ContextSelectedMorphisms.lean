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

/-- Reindex the assignments in the graph comparison of Proposition 3.2
when the structural arrow commutes with the carrier identifications pointwise. -/
theorem map_selectAssignment (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    {Γ : List P.signature.SortType} (kept : Declaration.sorts Γ ⊆ U.declarations) (a : Assignment X Γ) :
    (selectAssignment e kept a).map g = selectAssignment e' kept (mapAssignment f kept a) := by
  apply Assignment.ext
  intro s i
  rw [Assignment.map_apply, ← selectVar_ambientVar kept i,
    selectAssignment_selectVar, selectAssignment_selectVar, mapAssignment_apply]
  exact same s.val s.property (a (ambientVar kept i))

/-- Mapping the values of an assignment commutes with a change of its context index. -/
private theorem cast_assignment_map {left right : List (SortName U)} (same : left = right)
    (g : ∀ s, Y s → Y' s) (a : Assignment Y left) :
    (cast (congrArg (Assignment Y) same) a).map g =
      cast (congrArg (Assignment Y') same) (a.map g) := by
  cases same
  rfl

/-- Mapping a carrier element commutes with a change of its sort index. -/
private theorem cast_carrier_map {left right : Arity (SortName U)} (same : left = right)
    (g : ∀ i, Y i → Y' i) (x : Y left.output) :
    g right.output (cast (congrArg (fun profile => Y profile.output) same) x) =
      cast (congrArg (fun profile => Y' profile.output) same) (g left.output x) := by
  cases same
  rfl

/-- Transport the input tuple in the graph comparison of Proposition 3.2.
The pointwise square `same` is definitional for the read structural arrow
and is proved by `writeOnSort_comm` for the written arrow. -/
theorem map_selectArgs (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations)
    (a : Assignment X op.arity.inputs) :
    (selectArgs e op kept a).map g = selectArgs e' op kept (mapAssignment f (operationInputs op kept) a) := by
  rw [selectArgs_eq_cast, selectArgs_eq_cast]
  let h := (operation_arity op kept).symm
  exact (cast_assignment_map (congrArg Arity.inputs h) g (selectAssignment e (operationInputs op kept) a)).trans
    (congrArg (cast (congrArg (fun profile => Assignment Y' profile.inputs) h))
      (map_selectAssignment e e' f g same (operationInputs op kept) a))

/-- Transport the output in the graph comparison of Proposition 3.2.
The pointwise square `same` is definitional for the read structural arrow
and is proved by `writeOnSort_comm` for the written arrow. -/
theorem map_selectResult (e : CarrierEquiv U X Y) (e' : CarrierEquiv U X' Y')
    (f : CarrierMap U X X') (g : ∀ s, Y s → Y' s)
    (same : ∀ s keep x, g ⟨s, keep⟩ (e s keep x) = e' s keep (f s keep x))
    (op : Operation P.signature) (kept : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    g _ (selectResult e op kept x) = selectResult e' op kept (f _ (operationOutput op kept) x) := by
  rw [selectResult_eq_cast, selectResult_eq_cast]
  let h := (operation_arity op kept).symm
  exact (cast_carrier_map h g (e op.arity.output (operationOutput op kept) x)).trans
    (congrArg (cast (congrArg (fun profile => Y' profile.output) h)) (same _ _ x))

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
    argsEquiv e op keep a = selectArgs e op keep a := by
  simp only [argsEquiv, Equiv.trans_apply, assignmentEquiv_apply, Equiv.cast_apply, selectArgs_eq_cast]

/-- The outcome equivalence for a retained operation acts by the output selection
of Proposition 3.2. Use it to obtain ambient preimages in the graph comparison. -/
theorem resultEquiv_apply (e : CarrierEquiv U X Y) (op : Operation P.signature)
    (keep : Declaration.ofOperation op ∈ U.declarations) (x : X op.arity.output) :
    resultEquiv e op keep x = selectResult e op keep x := by
  rw [selectResult_eq_cast]
  rfl

variable {A B : ContextStructure U}

/-- The same point map can be indexed by the actual retained sort names. -/
def readOnSort (f : ContextStructure.Hom A B) (s : SortName U) :
    (readStructure A).carrier s → (readStructure B).carrier s :=
  fun x => readCarrierEquiv B s.val s.property (f.onSort s.val s.property
    ((readCarrierEquiv A s.val s.property).symm x))

/-- A read point map uses the two retained carrier equivalences and the original point map. -/
theorem readOnSort_apply (f : ContextStructure.Hom A B) (s : SortName U) (x : (readStructure A).carrier s) :
    readOnSort f s x = readCarrierEquiv B s.val s.property (f.onSort s.val s.property
      ((readCarrierEquiv A s.val s.property).symm x)) :=
  rfl

/-- Reading a carrier commutes with the map at every retained sort. -/
private theorem readOnSort_equiv (f : ContextStructure.Hom A B) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : A.carrier s) :
    readOnSort f ⟨s, keep⟩ (readCarrierEquiv A s keep x) = readCarrierEquiv B s keep (f.onSort s keep x) := by
  rw [readOnSort_apply, Equiv.symm_apply_apply]

/-- Transport the graph-preservation component of a context arrow to the
selected signature for Proposition 3.2. The retained operation supplies the
input and output support for the two carrier comparisons. -/
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
      (readOnSort_equiv f) op keep x,
    map_selectResult (readCarrierEquiv A) (readCarrierEquiv B) f.onSort (readOnSort f)
      (readOnSort_equiv f) op keep z]
  exact ((readStructure_matches B).graph op keep _ _).2
    (f.graph_mem op keep x z (((readStructure_matches A).graph op keep x z).1 held))

/-- A context arrow reads as an ordinary structure map, with the same carrier components. -/
noncomputable def readStructureMap (f : ContextStructure.Hom A B) : StructureMap (readStructure A) (readStructure B) :=
  StructureMap.ofGraphs (readOnSort f) (by
    intro r xs held
    let keep := relationInputs r.val r.property
    let shape := (signature_relInputs r).symm
    let inputs := (assignmentEquiv (readCarrierEquiv A) keep).trans
      (Equiv.cast (congrArg (Assignment (readStructure A).carrier) shape))
    obtain ⟨x, hx⟩ := inputs.surjective xs
    rw [← hx] at held ⊢
    simp only [inputs, Equiv.trans_apply, Equiv.cast_apply, assignmentEquiv_apply] at held ⊢
    rw [cast_assignment_map shape, map_selectAssignment _ (readCarrierEquiv B) f.onSort _ (readOnSort_equiv f)]
    exact ((readStructure_matches B).relation_cast r _).2
      (f.relation_mem r.val r.property x (((readStructure_matches A).relation_cast r x).1 held))) (by
    intro p xs held
    let keep := operationInputs (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)
    let shape := (signature_partialInputs p).symm
    let inputs := (assignmentEquiv (readCarrierEquiv A) keep).trans
      (Equiv.cast (congrArg (Assignment (readStructure A).carrier) shape))
    obtain ⟨x, hx⟩ := inputs.surjective xs
    rw [← hx] at held ⊢
    simp only [inputs, Equiv.trans_apply, Equiv.cast_apply, assignmentEquiv_apply] at held ⊢
    rw [cast_assignment_map shape, map_selectAssignment _ (readCarrierEquiv B) f.onSort _ (readOnSort_equiv f)]
    exact ((readStructure_matches B).domain_cast p _).2
      (f.domain_mem p.val p.property x (((readStructure_matches A).domain_cast p x).1 held))) (by
    intro op xs y held
    cases op with
    | total f' =>
      have preserved := readGraph f (.total f'.val) (Declaration.ofOperation_total_mem f'.val f'.property)
      rw [operation_total] at preserved
      exact preserved xs y held
    | partialOp p =>
      have preserved := readGraph f (.partialOp p.val) (Declaration.ofOperation_partialOp_mem p.val p.property)
      rw [operation_partialOp] at preserved
      exact preserved xs y held
    | quantity q =>
      have preserved := readGraph f (.quantity q.val) (Declaration.ofOperation_quantity_mem q.val q.property)
      rw [operation_quantity] at preserved
      exact preserved xs y held)

/-- The read ordinary arrow preserves the same point map at each retained sort. -/
theorem readStructureMap_onSort (f : ContextStructure.Hom A B) (s : SortName U) (x : (readStructure A).carrier s) :
    (readStructureMap f).onSort s x = readOnSort f s x :=
  rfl

variable {C D : Structure (signature U)}

/-- Write the ordinary sort maps under the original sort names. -/
noncomputable def writeOnSort (f : StructureMap C D) :
    CarrierMap U (writeStructure C).carrier (writeStructure D).carrier :=
  fun s keep x => (writeCarrierEquiv D s keep).symm (f.onSort ⟨s, keep⟩ (writeCarrierEquiv C s keep x))

/-- The written map in the comparison of Proposition 3.2 transports an
original value through the two retained carrier equivalences and the original arrow. -/
theorem writeOnSort_apply (f : StructureMap C D) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : (writeStructure C).carrier s) :
    writeOnSort f s keep x = (writeCarrierEquiv D s keep).symm
      (f.onSort ⟨s, keep⟩ (writeCarrierEquiv C s keep x)) :=
  rfl

/-- The square of corresponding sort maps commutes. -/
theorem writeOnSort_comm (f : StructureMap C D) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : (writeStructure C).carrier s) :
    f.onSort ⟨s, keep⟩ (writeCarrierEquiv C s keep x) = writeCarrierEquiv D s keep (writeOnSort f s keep x) := by
  rw [writeOnSort_apply, Equiv.apply_symm_apply]

/-- An ordinary structure map gives the original-name structural arrow. -/
noncomputable def writeStructureMap (f : StructureMap C D) : ContextStructure.Hom (writeStructure C) (writeStructure D) where
  onSort := writeOnSort f
  relation_mem r keep a held := by
    have mapped := f.relation_mem ⟨r, keep⟩ _ (((writeStructure_matches C).relation r keep a).2 held)
    rw [map_selectAssignment _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((writeStructure_matches D).relation r keep _).1 mapped
  domain_mem p keep a held := by
    have mapped := f.partial_mem ⟨p, keep⟩ _ (((writeStructure_matches C).domain p keep a).2 held)
    rw [map_selectAssignment _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((writeStructure_matches D).domain p keep _).1 mapped
  graph_mem op keep a x held := by
    have mapped := f.map_graph (operation op keep) _ _ (((writeStructure_matches C).graph op keep a x).2 held)
    rw [map_selectArgs _ _ _ _ (writeOnSort_comm f), map_selectResult _ _ _ _ (writeOnSort_comm f)] at mapped
    exact ((writeStructure_matches D).graph op keep _ _).1 mapped

/-- The written arrow acts by the transported ordinary component. -/
theorem writeStructureMap_onSort (f : StructureMap C D) (s : P.signature.SortType)
    (keep : Declaration.sort s ∈ U.declarations) (x : (writeStructure C).carrier s) :
    (writeStructureMap f).onSort s keep x = writeOnSort f s keep x :=
  rfl

end DeclarationContext.Selected
end SHIGURE
