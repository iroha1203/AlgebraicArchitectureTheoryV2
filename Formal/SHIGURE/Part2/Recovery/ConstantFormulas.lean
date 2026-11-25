import Formal.SHIGURE.Part2.Realizations.ConstantStructures
import Mathlib.AlgebraicGeometry.Restrict

/-!
# The native semantics of globally split copying realizations

An assignment of copied states is locally constant in the underlying
topological space. A positive formula defines the subsheaf obtained by
requiring the native formula on each state of that assignment.
-/

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {sig : Signature.{u}} {Γ : List sig.SortType}
variable {T : Over S} (A : Structure sig)

local notation "Split" => constantStructure S A

/-- Evaluate each variable at the same point to obtain a native assignment. -/
def nativeAssignmentAt (a : (sheafTuple (Split).carrier Γ).val.obj (op T))
    (x : T.left) : Assignment A.carrier Γ :=
  ⟨fun {s} i =>
    let b : LocallyConstant T.left (A.carrier s) := a.get i
    b x⟩

/-- Reading the native assignment commutes with restricting a relative section. -/
theorem nativeAssignmentAt_restrict {U : Over S} (f : U ⟶ T)
    (a : (sheafTuple (Split).carrier Γ).val.obj (op T)) (x : U.left) :
    nativeAssignmentAt A ((sheafTuple (Split).carrier Γ).val.map f.op a) x =
      nativeAssignmentAt A a (f.left x) :=
  rfl

/-- Atomic formulas use the original relation, graph and domain at every point. -/
theorem mem_constantAtom_iff (p : Atomic sig Γ)
    (a : (sheafTuple (Split).carrier Γ).val.obj (op T)) :
    a ∈ ((Split).interpretAtom p).carrier.obj (op T) ↔
      ∀ x : T.left, p.Holds A (nativeAssignmentAt A a x) := by
  cases p with
  | @eq s y z =>
    rw [SheafStructure.interpretAtom, SheafPredicate.mem_equal_iff]
    let b : LocallyConstant T.left (A.carrier s) := a.get y
    let c : LocallyConstant T.left (A.carrier s) := a.get z
    change b = c ↔ ∀ x, b x = c x
    exact ⟨DFunLike.congr_fun, fun h => LocallyConstant.ext h⟩
  | rel r vars =>
    exact mem_constantPredicate S (A.relation r) (op T)
      ((constantTupleMap S A.carrier _).val.app (op T)
        ((sheafTupleRename (Split).carrier vars).val.app (op T) a))
  | domain p vars =>
    exact mem_constantPredicate S (A.partialDomain p) (op T)
      ((constantTupleMap S A.carrier _).val.app (op T)
        ((sheafTupleRename (Split).carrier vars).val.app (op T) a))
  | graph o vars y =>
    cases o with
    | total f =>
      rw [SheafStructure.interpretAtom, SheafPredicate.mem_equal_iff]
      simp only [Atomic.holds_graph, Structure.graph_total_iff]
      let b : LocallyConstant T.left (A.carrier (sig.totalArity f).output) :=
        ((sheafTupleRename (Split).carrier vars ≫ (Split).total f).val.app (op T)) a
      let c : LocallyConstant T.left (A.carrier (sig.totalArity f).output) := a.get y
      change b = c ↔ ∀ x, b x = c x
      exact ⟨DFunLike.congr_fun, fun h => LocallyConstant.ext h⟩
    | quantity q =>
      rw [SheafStructure.interpretAtom, SheafPredicate.mem_equal_iff]
      simp only [Atomic.holds_graph, Structure.graph_quantity_iff]
      let b : LocallyConstant T.left (A.carrier (sig.quantityArity q).output) :=
        ((sheafTupleRename (Split).carrier vars ≫ (Split).quantity q).val.app (op T)) a
      let c : LocallyConstant T.left (A.carrier (sig.quantityArity q).output) := a.get y
      change b = c ↔ ∀ x, b x = c x
      exact ⟨DFunLike.congr_fun, fun h => LocallyConstant.ext h⟩
    | partialOp p =>
      have hg := SheafStructure.mem_partialGraph_iff (Split) p vars y (op T) a
      dsimp only at hg
      rw [SheafStructure.interpretAtom, hg]
      simp only [Atomic.holds_graph, Structure.graph_partial_iff]
      let tuple := (constantTupleMap S A.carrier (sig.partialArity p).inputs).val.app (op T)
        ((sheafTupleRename (Split).carrier vars).val.app (op T) a)
      have hd : a ∈ (((Split).partialDomain p).preimage (sheafTupleRename (Split).carrier vars)).carrier.obj (op T)
          ↔ ∀ x : T.left, (nativeAssignmentAt A a x).pull vars ∈ A.partialDomain p :=
        mem_constantPredicate S (A.partialDomain p) (op T) tuple
      constructor
      · rintro ⟨ha, he⟩ x
        exact ⟨hd.mp ha x,
          congrArg (fun b : LocallyConstant T.left (A.carrier (sig.partialArity p).output) => b x) he⟩
      · intro h
        let ha := hd.mpr fun x => (h x).choose
        exact ⟨ha, LocallyConstant.ext fun x => (h x).choose_spec⟩

/-- A relative Zariski covering sieve supplies a lift of every point. -/
private theorem relativeCover_lifts (Q : Sieve T) (hQ : Q ∈ (Scheme.zariskiTopology.over S) T)
    (x : T.left) : ∃ (U : Over S) (f : U ⟶ T) (y : U.left), Q f ∧ f.left y = x := by
  rw [GrothendieckTopology.mem_over_iff] at hQ
  obtain ⟨C, hC⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hQ
  obtain ⟨i, y, hy⟩ := C.exists_eq x
  let U := Over.mk (C.f i ≫ T.hom)
  let f : U ⟶ T := Over.homMk (C.f i)
  exact ⟨U, f, y, (Sieve.overEquiv_iff Q (C.f i)).mp (hC _ (Presieve.ofArrows.mk i)), hy⟩

/-- An open subscheme inclusion considered in the relative test site. -/
private def relativeOpenInclusion (O : T.left.Opens) : Over.mk (O.ι ≫ T.hom) ⟶ T :=
  Over.homMk O.ι

/-- A sieve containing the inclusions of an open cover is covering. -/
private theorem relativeCover_of_opens {I : Type u} (O : I → T.left.Opens)
    (hO : IsOpenCover O) (Q : Sieve T) (hQ : ∀ i, Q (relativeOpenInclusion (O i))) :
    Q ∈ (Scheme.zariskiTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff]
  apply Scheme.mem_grothendieckTopology_iff.mpr
  let C := T.left.openCoverOfIsOpenCover O hO
  refine ⟨C, ?_⟩
  rintro _ _ ⟨i⟩
  exact (Sieve.overEquiv_iff Q (O i).ι).mpr (hQ i)

/-- The open fiber on which every variable has the value that it has at the chosen point. -/
private def assignmentNeighborhood (a : (sheafTuple (Split).carrier Γ).val.obj (op T))
    (x : T.left) : T.left.Opens :=
  let f : LocallyConstant T.left (Assignment A.carrier Γ) := (constantTupleMap S A.carrier Γ).val.app (op T) a
  ⟨f ⁻¹' {f x}, f.isLocallyConstant {f x}⟩

/-- Restricting to each fiber of a tuple gives a cover on which all variables are fixed. -/
private theorem assignmentNeighborhood_isOpenCover
    (a : (sheafTuple (Split).carrier Γ).val.obj (op T)) :
    IsOpenCover (assignmentNeighborhood A a) := by
  apply top_unique
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, rfl⟩

/-- On the fiber at a point the restricted tuple has that point's native values. -/
private theorem nativeAssignmentAt_neighborhood
    (a : (sheafTuple (Split).carrier Γ).val.obj (op T)) (x : T.left)
    (y : (assignmentNeighborhood A a x).toScheme) :
    let f := relativeOpenInclusion (assignmentNeighborhood A a x)
    nativeAssignmentAt A ((sheafTuple (Split).carrier Γ).val.map f.op a) y =
      nativeAssignmentAt A a x := by
  dsimp only
  rw [nativeAssignmentAt_restrict]
  exact y.property

/-- A positive formula in the constant realization holds exactly at the points
where the native tuple satisfies it. Disjunction and existence use the relative
Zariski topology, with the open fibers of the tuple providing local witnesses. -/
theorem mem_constantFormula_iff (p : Formula sig Γ)
    (a : (sheafTuple (Split).carrier Γ).val.obj (op T)) :
    a ∈ ((Split).interpretFormula p).carrier.obj (op T) ↔
      ∀ x : T.left, p.Holds A (nativeAssignmentAt A a x) := by
  induction p generalizing T with
  | atom p => exact mem_constantAtom_iff A p a
  | truth =>
    exact ⟨fun _ _ => trivial, fun _ => SheafPredicate.mem_truth _ _⟩
  | falsehood =>
    rw [SheafStructure.interpretFormula, SheafPredicate.falsehood, SheafPredicate.mem_ofLocal_iff]
    constructor
    · intro h x
      obtain ⟨U, f, y, hf, _⟩ := relativeCover_lifts _ h x
      exact hf
    · intro h
      apply relativeCover_of_opens (assignmentNeighborhood A a) (assignmentNeighborhood_isOpenCover A a)
      intro x
      exact (h x).elim
  | conj p q hp hq =>
    rw [SheafStructure.interpretFormula, SheafPredicate.mem_conj_iff, hp, hq]
    exact forall_and.symm
  | disj p q hp hq =>
    rw [SheafStructure.interpretFormula, SheafPredicate.mem_disj_iff]
    constructor
    · intro h x
      obtain ⟨U, f, y, hf, rfl⟩ := relativeCover_lifts _ h x
      let b := (sheafTuple (Split).carrier _).val.map f.op a
      change b ∈ ((Split).interpretFormula p).carrier.obj (op U) ∨
        b ∈ ((Split).interpretFormula q).carrier.obj (op U) at hf
      rw [← nativeAssignmentAt_restrict A f a y]
      exact hf.elim (fun h' => Or.inl ((hp b).mp h' y)) (fun h' => Or.inr ((hq b).mp h' y))
    · intro h
      apply relativeCover_of_opens (assignmentNeighborhood A a) (assignmentNeighborhood_isOpenCover A a)
      intro x
      let f := relativeOpenInclusion (assignmentNeighborhood A a x)
      let b := (sheafTuple (Split).carrier _).val.map f.op a
      change b ∈ ((Split).interpretFormula p).carrier.obj _ ∨
        b ∈ ((Split).interpretFormula q).carrier.obj _
      rcases h x with hx | hx
      · exact Or.inl ((hp b).mpr (fun y => nativeAssignmentAt_neighborhood A a x y ▸ hx))
      · exact Or.inr ((hq b).mpr (fun y => nativeAssignmentAt_neighborhood A a x y ▸ hx))
  | @ex Γ s p ih =>
    rw [SheafStructure.interpretFormula, SheafPredicate.mem_existsAlong_iff]
    let project : sheafTuple (Split).carrier (s :: Γ) ⟶ sheafTuple (Split).carrier Γ :=
      sheafTupleRename (Split).carrier (fun i => .there i)
    constructor
    · intro h x
      obtain ⟨U, f, y, hf, rfl⟩ := relativeCover_lifts _ h x
      obtain ⟨⟨b, hb⟩, he⟩ := hf
      change project.val.app (op U) b = (sheafTuple (Split).carrier Γ).val.map f.op a at he
      have ht : (nativeAssignmentAt A b y).tail = nativeAssignmentAt A a (f.left y) := by
        rw [← nativeAssignmentAt_restrict A f a y, ← he]
        rfl
      refine ⟨(nativeAssignmentAt A b y).head, ?_⟩
      rw [← ht, Assignment.cons_head_tail]
      exact (ih b).mp hb y
    · intro h
      apply relativeCover_of_opens (assignmentNeighborhood A a) (assignmentNeighborhood_isOpenCover A a)
      intro x
      let U := Over.mk ((assignmentNeighborhood A a x).ι ≫ T.hom)
      let f : U ⟶ T := relativeOpenInclusion (assignmentNeighborhood A a x)
      let b := (sheafTuple (Split).carrier Γ).val.map f.op a
      obtain ⟨y, hy⟩ := h x
      let c : (sheafTuple (Split).carrier (s :: Γ)).val.obj (op U) :=
        Assignment.cons (nativeState S U y) b
      have hc : c ∈ ((Split).interpretFormula p).carrier.obj (op U) := by
        apply (ih c).mpr
        intro z
        have hcarg : nativeAssignmentAt A c z = Assignment.cons y (nativeAssignmentAt A b z) := by
          apply Assignment.ext
          intro s i
          cases i <;> rfl
        rw [hcarg, nativeAssignmentAt_neighborhood A a x z]
        exact hy
      exact ⟨⟨c, hc⟩, rfl⟩

/-- A subsheaf predicate is determined by its subfunctor of satisfying sections. -/
private theorem predicate_ext {F : ZariskiSheaf S} {P Q : SheafPredicate F}
    (h : P.carrier = Q.carrier) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- A finite tuple of constant section sheaves is the constant sheaf of native tuples. -/
def constantTupleIso {K : Type u} (S : Scheme.{u}) (M : K → Type u) (Γ : List K) :
    sheafTuple (fun s => constantCarrier S (M s)) Γ ≅ constantCarrier S (Assignment M Γ) where
  hom := constantTupleMap S M Γ
  inv :=
    ⟨{ app := fun U => ↾fun a =>
         ⟨fun {s} i => LocallyConstant.map (fun v : Assignment M Γ => v.get i) a⟩
       naturality := by
         intro U V f
         ext a
         apply Assignment.ext
         intro s i
         rfl }⟩
  hom_inv_id := by
    ext U a
    apply Assignment.ext
    intro s i
    apply LocallyConstant.ext
    intro x
    rfl
  inv_hom_id := by
    ext U a
    apply LocallyConstant.ext
    intro x
    apply Assignment.ext
    intro s i
    rfl

/-- The constant predicate on a subset is the constant carrier of its subtype. -/
def constantPredicateIso {X : Type u} (S : Scheme.{u}) (P : Set X) :
    (constantPredicate S P).toSheaf ≅ constantCarrier S P where
  hom := constantSubtypeMap S P
  inv :=
    ⟨{ app := fun U => ↾fun a =>
         let c : LocallyConstant U.unop.left P := a
         let b : LocallyConstant U.unop.left X := LocallyConstant.map Subtype.val c
         ⟨b, (mem_constantPredicate S P U b).mpr fun x => (c x).property⟩
       naturality := by
         intro U V f
         ext a
         apply Subtype.ext
         rfl }⟩
  hom_inv_id := by
    ext U a
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    rfl
  inv_hom_id := by
    ext U a
    apply LocallyConstant.ext
    intro x
    apply Subtype.ext
    rfl

/-- The subtype identification intertwines the predicate inclusion with the native injection. -/
theorem constantPredicateIso_inclusion {X : Type u} (S : Scheme.{u}) (P : Set X) :
    (constantPredicateIso S P).inv ≫ (constantPredicate S P).inclusion =
      constantCarrierMap S (Subtype.val : P → X) := by
  ext U a
  rfl

/-- The interpreted positive formula is the constant subset of native satisfying assignments. -/
theorem constantFormula_eq (p : Formula sig Γ) :
    (Split).interpretFormula p =
      (constantPredicate S {a : Assignment A.carrier Γ | p.Holds A a}).preimage
        (constantTupleMap S A.carrier Γ) := by
  apply predicate_ext
  ext U a
  exact (mem_constantFormula_iff A p a).trans
    (mem_constantPredicate S _ U ((constantTupleMap S A.carrier Γ).val.app U a)).symm

/-- The domain of an arbitrary native term becomes its constant subobject. -/
theorem constantTermDomain_eq {s : sig.SortType} (t : Term sig Γ s) :
    (Split).interpretFormula t.defined =
      (constantPredicate S (t.domain A)).preimage (constantTupleMap S A.carrier Γ) := by
  rw [constantFormula_eq, t.defined_locus]

/-- The value graph is the constant subobject of the native graph,
including the original definedness condition for partial terms. -/
theorem constantTermGraph_eq {s : sig.SortType} (t : Term sig Γ s) :
    (Split).interpretFormula t.graph =
      (constantPredicate S {e : Assignment A.carrier (s :: Γ) | e.head ∈ t.eval A e.tail}).preimage
        (constantTupleMap S A.carrier (s :: Γ)) := by
  rw [constantFormula_eq]
  congr 2
  ext e
  have h := t.holds_graph_iff A e.tail e.head
  rw [Assignment.cons_head_tail] at h
  exact h

/-- Every native Law holds on the constant realization over any base scheme. -/
theorem constantStructure_holdsLaw (law : Law sig) (h : law.Holds A) :
    (Split).holdsLaw law := by
  intro U a ha
  exact (mem_constantFormula_iff A law.conclusion a).mpr (fun x =>
    h (nativeAssignmentAt A a x) ((mem_constantFormula_iff A law.input a).mp ha x))

/-- A nonempty base detects each native assignment and hence reflects the Laws. -/
theorem constantStructure_holdsLaw_iff [Nonempty S] (law : Law sig) :
    (Split).holdsLaw law ↔ law.Holds A := by
  constructor
  · intro h e he
    let T : Over S := Over.mk (𝟙 S)
    let a : (sheafTuple (Split).carrier law.context).val.obj (op T) :=
      ⟨fun i => nativeState S T (e.get i)⟩
    have ha (x : T.left) : nativeAssignmentAt A a x = e := rfl
    have hinput := (mem_constantFormula_iff A law.input a).mpr (fun x => (ha x).symm ▸ he)
    obtain ⟨x⟩ := (inferInstance : Nonempty S)
    have hx := (mem_constantFormula_iff A law.conclusion a).mp (h (op T) hinput) x
    exact ha x ▸ hx
  · exact constantStructure_holdsLaw A law

end SHIGURE.Copying
