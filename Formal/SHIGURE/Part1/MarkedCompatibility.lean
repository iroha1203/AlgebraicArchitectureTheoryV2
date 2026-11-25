import Formal.SHIGURE.Part1.MarkedInterpretation

/-! # Compatibility of marked structure restrictions

Agreeing kernels and shared multilinear interpretations induce equal
restricted SHIGURE structures. This is the semantic compatibility
needed to apply Theorem 3.4 in Proposition 3.6.
-/

universe u

namespace SHIGURE.Marked

open Vocabulary DeclarationContext

variable {V : Vocabulary.{u}} {L : V.Laws} {R : Type u} [CommRing R]
variable {U W : DeclarationContext (V.presentation L)}

namespace Data

variable {a : Data R U} {b : Data R W}

/-- Identifying kernels identifies the zero classes of the standard quotients. -/
private theorem cast_zero {m : ℕ} {K J : Kernel R m} (h : K = J) :
    cast (congrArg Quotient h) (0 : Quotient K) = 0 := by
  subst J
  rfl

/-- Addition of quotient classes commutes with equality transport of the kernel. -/
private theorem cast_add {m : ℕ} {K J : Kernel R m} (h : K = J) (x y : Quotient K) :
    cast (congrArg Quotient h) (x + y) =
      cast (congrArg Quotient h) x + cast (congrArg Quotient h) y := by
  subst J
  rfl

/-- Negation of quotient classes commutes with equality transport of the kernel. -/
private theorem cast_neg {m : ℕ} {K J : Kernel R m} (h : K = J) (x : Quotient K) :
    cast (congrArg Quotient h) (-x) = -cast (congrArg Quotient h) x := by
  subst J
  rfl

/-- Scalar multiplication commutes with equality transport of the kernel. -/
private theorem cast_smul {m : ℕ} {K J : Kernel R m} (h : K = J) (r : R) (x : Quotient K) :
    cast (congrArg Quotient h) (r • x) = r • cast (congrArg Quotient h) x := by
  subst J
  rfl

/-- The named basis image is preserved under equality transport of the quotient kernel. -/
private theorem cast_generator {m : ℕ} {K J : Kernel R m} (h : K = J) (i : Fin m) :
    cast (congrArg Quotient h) (generator K i) = generator J i := by
  subst J
  rfl

/-- Transporting a multilinear map and its arguments transports the evaluated value. -/
private theorem cast_map_apply {f : V.Multilinear}
    {p q : OperationKernels (V := V) R f}
    (same : p = q) {F : p.Map} {G : q.Map} (maps : HEq F G)
    (xs : ∀ i, SortCarrier R (p.inputs i)) :
    cast (congrArg (fun k : OperationKernels (V := V) R f => SortCarrier R k.output) same) (F xs) =
      G (fun i : V.Position f => cast
        (congrArg (fun k : OperationKernels (V := V) R f => SortCarrier R (k.inputs i)) same) (xs i)) := by
  subst q
  cases eq_of_heq maps
  rfl

/-- On shared sorts the ambient kernels of agreeing data are equal. -/
theorem Agree.ambientKernel_eq (same : a.Agree b) {s : V.SortName}
    (left : Declaration.sort (some s) ∈ U.declarations)
    (right : Declaration.sort (some s) ∈ W.declarations) :
    a.ambientKernel s = b.ambientKernel s :=
  (a.ambientKernel_kept left).trans ((same.kernel s left right).trans (b.ambientKernel_kept right).symm)

/-- Shared marked data give the same coefficient and module carriers. -/
theorem Agree.carrier_eq (same : a.Agree b) (s : Option V.SortName)
    (left : Declaration.sort s ∈ U.declarations) (right : Declaration.sort s ∈ W.declarations) :
    a.carrier s = b.carrier s :=
  match s, left, right with
  | none, _, _ => rfl
  | some _, left, right => congrArg Quotient (same.ambientKernel_eq left right)

/-- Agreement on shared sorts identifies the ambient input and output kernel profiles. -/
private theorem Agree.ambientOperationKernels_eq (same : a.Agree b) {f : V.Multilinear}
    (left : V.multilinearDecl L f ∈ U.declarations) (right : V.multilinearDecl L f ∈ W.declarations) :
    a.ambientOperationKernels f = b.ambientOperationKernels f :=
  (a.ambientOperationKernels_kept left).trans
    ((same.operationKernels_eq left right).trans (b.ambientOperationKernels_kept right).symm)

/-- Agreement on a retained multilinear operation identifies its two ambient readings along the shared kernels. -/
private theorem Agree.ambientOperation_heq (same : a.Agree b) {f : V.Multilinear}
    (left : V.multilinearDecl L f ∈ U.declarations) (right : V.multilinearDecl L f ∈ W.declarations) :
    HEq (a.ambientOperation f) (b.ambientOperation f) :=
  (a.ambientOperation_kept left).trans
    ((same.operation f left right).trans (b.ambientOperation_kept right).symm)

attribute [local irreducible] Declaration.ofOperation in
/-- A retained operation preserves its value across the identification of shared quotients. -/
theorem Agree.totalValue_cast (same : a.Agree b) (inside : W ≤ U)
    (f : V.Symbol) (keep : Declaration.total (P := V.presentation L) f ∈ W.declarations)
    (xs : Assignment a.carrier (V.arity f).inputs) :
    let op : Operation V.signature := .total f
    let operationKept : Declaration.ofOperation (P := V.presentation L) op ∈ W.declarations :=
      Declaration.ofOperation_total_mem (P := V.presentation L) (kept := W.declarations) f keep
    let h (s : Option V.SortName) (hs : Declaration.sort s ∈ W.declarations) :=
      same.carrier_eq s (inside hs) hs
    cast (h _ (operationOutput (P := V.presentation L) (U := W) op operationKept)) (a.totalValue f xs) =
      b.totalValue f (mapAssignment (P := V.presentation L) (U := W)
        (fun s hs => cast (h s hs)) (operationInputs (P := V.presentation L) (U := W) op operationKept) xs) := by
  cases f with
  | coefficient f =>
    cases f <;> rfl
  | moduleOp s f =>
    have out : Declaration.sort (some s) ∈ W.declarations := by
      cases f <;> exact operationOutput (P := V.presentation L) (U := W) (.total (Symbol.moduleOp s _))
        (Declaration.ofOperation_total_mem _ keep)
    let eq := same.ambientKernel_eq (inside out) out
    cases f with
    | zero => exact cast_zero eq
    | add => exact cast_add eq (xs .here) (xs (.there .here))
    | neg => exact cast_neg eq (xs .here)
    | smul => exact cast_smul eq (xs .here) (xs (.there .here))
    | generator i => exact cast_generator eq i
  | multilinear f =>
    exact cast_map_apply (same.ambientOperationKernels_eq (inside keep) keep)
      (same.ambientOperation_heq (inside keep) keep) (fun i => xs i.2)

attribute [local irreducible] Declaration.ofOperation in
/-- The ordinary graphs of shared operations are the same after identifying their carriers. -/
theorem Agree.graph_iff (same : a.Agree b) (inside : W ≤ U)
    (op : Operation V.signature) (keep : Declaration.ofOperation (P := V.presentation L) op ∈ W.declarations)
    (xs : Assignment a.carrier op.arity.inputs) (y : a.carrier op.arity.output) :
    let c : CarrierMap W a.carrier b.carrier := fun s hs =>
      cast (same.carrier_eq s (inside hs) hs)
    a.structureData.Graph op xs y ↔
      b.structureData.Graph op (mapAssignment c (operationInputs (P := V.presentation L) (U := W) op keep) xs)
        (c _ (operationOutput (P := V.presentation L) (U := W) op keep) y) := by
  cases op with
  | total f =>
    have retained : Declaration.total (P := V.presentation L) f ∈ W.declarations := by
      simpa only [Declaration.ofOperation_total] using keep
    dsimp only
    rw [Structure.graph_total_iff, Structure.graph_total_iff, structure_total, structure_total,
      ← same.totalValue_cast inside f retained xs]
    refine ⟨congrArg _, fun equal => ?_⟩
    have outputKeep := operationOutput (P := V.presentation L) (U := W) (.total f) keep
    have back := congrArg (cast (same.carrier_eq (V.arity f).output (inside outputKeep) outputKeep).symm) equal
    simpa only [cast_cast, cast_eq] using back
  | partialOp p => exact nomatch p
  | quantity q => exact nomatch q

/-- Agreement of marked data implies strict equality with the ordinary context restriction. -/
theorem Agree.contextStructure_restrict_eq (same : a.Agree b) (inside : W ≤ U) :
    a.contextStructure.restrict inside = b.contextStructure := by
  let c (s : Option V.SortName) (hs : Declaration.sort s ∈ W.declarations) :=
    same.carrier_eq s (inside hs) hs
  let compare (s : Option V.SortName) (hs : Declaration.sort s ∈ W.declarations) :
      a.contextStructure.carrier s = b.contextStructure.carrier s := by
    rw [a.contextStructure_carrier s, b.contextStructure_carrier s]
    exact (selectedCarrier_kept (P := V.presentation L) (U := U) a.carrier (s := s) (inside hs)).trans
      ((c s hs).trans (selectedCarrier_kept (P := V.presentation L) (U := W) b.carrier (s := s) hs).symm)
  apply ContextStructure.restrict_eq_of_view a.contextStructure b.contextStructure inside compare
  apply RestrictedEvaluation.ext
  · intro r
    exact nomatch r
  · intro p
    exact nomatch p
  · intro op keep xs y
    rw [RestrictedEvaluation.pullback_graph, RestrictedEvaluation.pullback_graph,
      mapAssignment_id]
    simp only [contextStructure_graph_iff]
    have align (s : Option V.SortName) (hs : Declaration.sort s ∈ W.declarations)
        (x : a.contextStructure.carrier s) :
        selectedMap W b.carrier s hs (cast (compare s hs) x) =
          cast (c s hs) (selectedMap U a.carrier s (inside hs) x) := by
      simp only [selectedMap_apply, cast_cast]
    rw [mapAssignment_comp _ _ (le_refl W)]
    have output := align op.arity.output (operationOutput op keep) y
    rw [show selectedMap W b.structureData.carrier op.arity.output _ _ = _ from output]
    have tuple := mapAssignment_congr (P := V.presentation L) (U := W)
      (f := fun s hs x => selectedMap W b.structureData.carrier s hs (cast (compare s hs) x))
      (g := fun s hs x => cast (c s hs) (selectedMap U a.carrier s (inside hs) x))
      align (operationInputs op keep) xs
    change a.structureData.Graph op _ _ ↔ b.structureData.Graph op
      (mapAssignment (P := V.presentation L) (U := W)
        (X := a.contextStructure.carrier) (Y := b.structureData.carrier)
        (fun s hs x => selectedMap W b.structureData.carrier s hs (cast (compare s hs) x))
        (operationInputs op keep) xs) _
    have composition := mapAssignment_comp (P := V.presentation L)
      (fun s hs => selectedMap U a.carrier s (inside hs))
      (fun s hs => cast (c s hs)) (le_refl W) (operationInputs op keep) xs
    rw [tuple]
    have equivalent := same.graph_iff inside op keep
      (mapAssignment (selectedMap U a.carrier) (operationInputs op (inside keep)) xs)
      (selectedMap U a.carrier _ (operationOutput op (inside keep)) y)
    exact equivalent.trans (Iff.of_eq (congrArg (fun args => b.structureData.Graph op args _) composition))

/-- Restriction of the data is one such agreement, with terms interpreted on the same values. -/
theorem restrict_agree (a : Data R U) (inside : W ≤ U) : a.Agree (a.restrict inside) :=
  ⟨fun _ _ _ => rfl, fun f _ keep => (a.restrict_operation inside f keep).symm⟩

/-- Interpreting and restricting the retained marked data commute strictly. -/
theorem contextStructure_restrict (a : Data R U) (inside : W ≤ U) :
    a.contextStructure.restrict inside = (a.restrict inside).contextStructure :=
  (a.restrict_agree inside).contextStructure_restrict_eq inside

end Data
end SHIGURE.Marked
