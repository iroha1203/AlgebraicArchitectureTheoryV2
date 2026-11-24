import Formal.SHIGURE.Part1.DeclarationFragments

/-! # Finite dependency closure of primitive syntax

Each primitive declaration has finitely many immediate dependencies.
Their height decreases from derived Laws to written Laws, from Laws to
symbols, and from symbols through their arities to their sorts. This gives
finite declaration closure for the basic signatures and finite Law syntax.
-/

universe u

namespace SHIGURE.Declaration

variable {P : PrimitivePresentation.{u}} {Γ : List P.signature.SortType}

private theorem sorts_finite (Γ : List P.signature.SortType) : (sorts (P := P) Γ).Finite :=
  Γ.finite_toSet.image _

private theorem atomic_finite (a : Atomic P.signature Γ) : (atomic a).Finite := by
  cases a
  · exact Set.finite_empty
  · exact Set.finite_singleton _
  · exact Set.finite_singleton _
  · exact Set.finite_singleton _

private theorem formula_finite (p : Formula P.signature Γ) : (formula p).Finite := by
  induction p with
  | atom a => exact atomic_finite a
  | truth | falsehood => exact Set.finite_empty
  | conj _ _ p q | disj _ _ p q => exact p.union q
  | ex _ h => exact (Set.finite_singleton _).union h

private theorem lawBody_finite (law : Law P.signature) : (lawBody law).Finite :=
  ((sorts_finite law.context).union (formula_finite law.input)).union (formula_finite law.conclusion)

private theorem derivation_finite {Γ : List P.theory.signature.SortType}
    {p q : Formula P.theory.signature Γ}
    (proof : Derivation P.theory p q) : (derivation proof).Finite := by
  unfold derivation
  induction proof <;> rw [derivationOf]
  all_goals
    refine (((sorts_finite _).union (formula_finite _)).union (formula_finite _)).union ?_
    first
    | exact Set.finite_empty
    | exact Set.finite_singleton _
    | exact Set.Finite.union (by assumption) (by assumption)
    | assumption

private theorem position_lt_length {s : P.signature.SortType} (i : Var Γ s) :
    i.position < Γ.length := by
  induction i with
  | here => exact Nat.succ_pos _
  | there _ ih => exact Nat.succ_lt_succ ih

private theorem finite_positions (Γ : List P.signature.SortType) : Finite (Σ s, Var Γ s) :=
  Finite.of_injective (fun i => (⟨i.2.position, position_lt_length i.2⟩ : Fin Γ.length))
    fun _ _ eq => Var.position_injective Γ (congrArg Fin.val eq)

private theorem inclusions_finite (p : P.signature.Partial) (data : DomainInclusions p) :
    {a | ∃ (s : P.signature.SortType) (i : Var (P.signature.partialArity p).inputs s),
      a = (ofOperation (data.symbol i).operation : Declaration P)}.Finite := by
  letI := finite_positions (P := P) (P.signature.partialArity p).inputs
  have same : {a | ∃ (s : P.signature.SortType) (i : Var (P.signature.partialArity p).inputs s),
      a = (ofOperation (data.symbol i).operation : Declaration P)} =
      Set.range (fun i : Σ s, Var (P.signature.partialArity p).inputs s =>
        ofOperation (data.symbol i.2).operation) := by
    ext a
    constructor
    · rintro ⟨s, i, rfl⟩
      exact ⟨⟨s, i⟩, rfl⟩
    · rintro ⟨⟨s, i⟩, rfl⟩
      exact ⟨s, i, rfl⟩
  rw [same]
  exact Set.finite_range _

/-- A primitive declaration has only finitely many immediate dependency names. -/
theorem dependsOn_finite (d : Declaration P) : (dependsOn P d).Finite := by
  cases d with
  | sort => exact Set.finite_empty
  | total | relation | quantity => exact sorts_finite _
  | partialOp p =>
    rw [dependsOn]
    apply Set.Finite.union (sorts_finite _)
    split
    · exact Set.finite_empty
    · exact (Set.finite_singleton _).union (inclusions_finite p _)
  | law name =>
    rw [dependsOn]
    apply Set.Finite.union (lawBody_finite _)
    split
    · exact derivation_finite _
    · exact Set.finite_empty
    · exact Set.finite_empty

private def height : Declaration P → ℕ
  | .sort _ => 0
  | .total _ | .relation _ | .quantity _ => 1
  | .partialOp _ => 2
  | .law n => match P.laws.role n with
    | .derived => 4
    | .required | .additional => 3

private theorem law_notMem_sequent (name : P.laws.LawName) (p q : Formula P.signature Γ) :
    Declaration.law name ∉ sorts Γ ∪ formula p ∪ formula q := by
  have notSort : Declaration.law name ∉ sorts (P := P) Γ := by
    rintro ⟨s, _, eq⟩
    cases eq
  simp only [Set.mem_union, not_or, notSort, law_notMem_formula, and_self, not_false_eq_true]

private theorem derivation_law_required {Γ : List P.theory.signature.SortType}
    {p q : Formula P.theory.signature Γ}
    (proof : Derivation P.theory p q) (name : P.laws.LawName) :
    Declaration.law name ∈ derivation proof → P.laws.role name = .required := by
  unfold derivation
  induction proof <;> intro uses <;> rw [derivationOf, Set.mem_union] at uses
  all_goals
    rcases uses with written | uses
    · exact (law_notMem_sequent name _ _ written).elim
    · first
      | exact (Set.notMem_empty _ uses).elim
      | exact uses.elim (by assumption) (by assumption)
      | exact (by assumption : _ → _) uses
      | rename_i requiredName
        have eq := Declaration.law.inj (Set.mem_singleton_iff.mp uses)
        rw [eq]
        exact requiredName.property

private theorem lawBody_height {d : Declaration P} {law : Law P.signature}
    (uses : d ∈ lawBody law) : d.height < 3 := by
  cases d <;> try simp only [height, Nat.reduceLT]
  exact (law_notMem_lawBody _ _ uses).elim

private theorem derivation_height {p q : Formula P.signature Γ}
    (proof : Derivation P.theory p q) {d : Declaration P}
    (uses : d ∈ derivation proof) : d.height < 4 := by
  cases d <;> try simp only [height, Nat.reduceLT]
  have role := derivation_law_required proof _ uses
  simp [role]

private theorem sort_height {d : Declaration P} {Γ : List P.signature.SortType}
    (uses : d ∈ sorts Γ) : d.height = 0 := by
  rcases uses with ⟨_, _, rfl⟩
  rfl

private theorem height_lt {d e : Declaration P} (uses : d ∈ dependsOn P e) :
    d.height < e.height := by
  cases e with
  | sort => exact (Set.notMem_empty _ uses).elim
  | total | relation | quantity =>
    rw [sort_height uses]
    simp [height]
  | partialOp p =>
    rw [dependsOn, Set.mem_union] at uses
    rcases uses with arity | included
    · rw [sort_height arity]
      simp [height]
    · split at included
      · exact (Set.notMem_empty _ included).elim
      · rename_i data _
        rcases included with s | ⟨s, i, rfl⟩
        · obtain rfl := Set.mem_singleton_iff.mp s
          simp [height]
        · cases data.symbol i <;> simp [TotalSymbol.operation, ofOperation, height]
  | law name =>
    rw [dependsOn, Set.mem_union] at uses
    rcases uses with written | derived
    · have lower := lawBody_height written
      cases role : P.laws.role name
      · simpa [height, role] using lower
      · simpa [height, role] using lower
      · simpa [height, role] using Nat.lt_trans lower (by decide : 3 < 4)
    · split at derived
      · rename_i role
        simpa [height, role] using derivation_height _ derived
      · exact (Set.notMem_empty _ derived).elim
      · exact (Set.notMem_empty _ derived).elim

end SHIGURE.Declaration

namespace SHIGURE.DeclarationContext.FiniteFragment

variable {P : PrimitivePresentation.{u}}

/-- In a primitive presentation every retained declaration belongs to a finite closed fragment. -/
theorem hasFiniteClosure (U : DeclarationContext P) : HasFiniteClosure U := by
  classical
  intro d
  induction d using (measure (Declaration.height (P := P))).wf.induction with
  | h d ih =>
    intro keep
    letI : Finite (Declaration.dependsOn P d) := Declaration.dependsOn_finite d
    have inFragment (e : Declaration.dependsOn P d) :
        ∃ F : FiniteFragment U, e.val ∈ F.context.declarations :=
      ih e.val (Declaration.height_lt e.property) (U.closed keep e.property)
    choose F contains using inFragment
    let children := union F
    let enlarged : DeclarationContext P :=
      ⟨insert d children.context.declarations, by
        intro a ha e uses
        rcases Set.mem_insert_iff.mp ha with same | inChildren
        · subst a
          let index : Declaration.dependsOn P d := ⟨e, uses⟩
          exact Set.mem_insert_of_mem _ (le_union F index (contains index))
        · exact Set.mem_insert_of_mem _ (children.context.closed inChildren uses)⟩
    refine ⟨⟨enlarged, ?_, children.finite.insert d⟩, Set.mem_insert _ _⟩
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | inChildren
    · exact keep
    · exact children.inside inChildren

/-- All finite fragments give a directed cover for primitive declaration syntax. -/
def primitiveCover (U : DeclarationContext P) : DeclarationCover U :=
  cover U (hasFiniteClosure U)

end SHIGURE.DeclarationContext.FiniteFragment
