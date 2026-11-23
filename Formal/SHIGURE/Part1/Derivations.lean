import Formal.SHIGURE.Part1.Laws

/-! # Positive sequent derivations

The rules of Appendix A.1 needed by the primitive presentation and theory
interpretation in Definitions 1.7 and 1.9. Soundness is proved by induction
on these rules and is used for the negative interpretation in Example 1.10.

## Implementation notes

A derivation is a finite tree indexed by its two end formulas. Taking
semantic implication as the type of a proof would not retain the rules
or the premises used in the tree. Typed renaming gives both the general
variable rule and weakening. Existence elimination uses the head binder
and renames the other formulas into the tail, enforcing freshness in
the types.
-/

universe u

namespace SHIGURE

namespace Renaming

variable {S : Type u} {Γ : List S} {s : S}

/-- Instantiate a fresh head position with an existing variable and leave older positions fixed. -/
def openHead (x : Var Γ s) : Renaming (s :: Γ) Γ
  | _, .here => x
  | _, .there i => i

/-- Reading an assignment along head instantiation inserts the supplied value. -/
@[simp] theorem pull_openHead {C : S → Type u} (e : Assignment C Γ) (x : Var Γ s) :
    e.pull (openHead x) = Assignment.cons (e x) e := by
  apply Assignment.ext
  intro t i
  cases i <;> rfl

end Renaming

/-- The seven groups of positive rules in Appendix A.1. -/
inductive Derivation (T : Theory.{u}) : {Γ : List T.signature.SortType} →
    Formula T.signature Γ → Formula T.signature Γ → Type u
  | refl {Γ} (p : Formula T.signature Γ) : Derivation T p p
  | cut {Γ} {p q r : Formula T.signature Γ} : Derivation T p q → Derivation T q r → Derivation T p r
  | required (name : T.LawName) : Derivation T (T.law name).input (T.law name).conclusion
  | graph (ax : GraphAxiom T.signature) : Derivation T ax.toLaw.input ax.toLaw.conclusion
  | rename {Γ Δ} {p q : Formula T.signature Γ} (ρ : Renaming Γ Δ) :
      Derivation T p q → Derivation T (p.rename ρ) (q.rename ρ)
  | truth {Γ} (p : Formula T.signature Γ) : Derivation T p .truth
  | falsehood {Γ} (p : Formula T.signature Γ) : Derivation T .falsehood p
  | andLeft {Γ} (p q : Formula T.signature Γ) : Derivation T (p.conj q) p
  | andRight {Γ} (p q : Formula T.signature Γ) : Derivation T (p.conj q) q
  | andIntro {Γ} {p q r : Formula T.signature Γ} :
      Derivation T r p → Derivation T r q → Derivation T r (p.conj q)
  | orLeft {Γ} (p q : Formula T.signature Γ) : Derivation T p (p.disj q)
  | orRight {Γ} (p q : Formula T.signature Γ) : Derivation T q (p.disj q)
  | orElim {Γ} {p q r c : Formula T.signature Γ} :
      Derivation T (c.conj p) r → Derivation T (c.conj q) r → Derivation T (c.conj (p.disj q)) r
  | existsIntro {Γ s} (body : Formula T.signature (s :: Γ)) (x : Var Γ s) :
      Derivation T (body.rename (Renaming.openHead x)) body.ex
  | existsElim {Γ s} {p : Formula T.signature (s :: Γ)} {c q : Formula T.signature Γ} :
      Derivation T ((c.rename (fun i => .there i)).conj p) (q.rename (fun i => .there i)) →
      Derivation T (c.conj p.ex) q
  | eqRefl {Γ s} (x : Var Γ s) : Derivation T .truth (.atom (.eq x x))
  | eqSubst {Γ s} (p : Formula T.signature (s :: Γ)) (x y : Var Γ s) :
      Derivation T ((Formula.atom (.eq x y)).conj (p.rename (Renaming.openHead x)))
        (p.rename (Renaming.openHead y))

namespace Derivation

variable {T : Theory.{u}} {Γ : List T.signature.SortType} {p q : Formula T.signature Γ}

/-- Weaken by adding an unused variable to the context. -/
def weaken {s : T.signature.SortType} (d : Derivation T p q) :
    Derivation T (p.rename (fun i => Var.there (t := s) i)) (q.rename (fun i => .there i)) :=
  .rename (fun i => .there i) d

/-- Proposition A.1: a derivation preserves truth at every assignment in every model. -/
theorem sound (d : Derivation T p q) (A : Structure T.signature) (model : T.Holds A) :
    ∀ e : Assignment A.carrier Γ, p.Holds A e → q.Holds A e := by
  induction d with
  | refl _ => exact fun _ h => h
  | cut _ _ hp hq => exact fun e h => hq e (hp e h)
  | required name => exact fun e h => Law.holds_at (model name) (e := e) h
  | graph ax => exact fun e h => Law.holds_at (ax.holds_toLaw A) (e := e) h
  | rename ρ _ h =>
    intro e he
    exact (Formula.holds_rename A _ ρ e).2 (h (e.pull ρ) ((Formula.holds_rename A _ ρ e).1 he))
  | truth _ => exact fun _ _ => True.intro
  | falsehood _ => exact fun _ h => h.elim
  | andLeft _ _ => exact fun e h => ((Formula.holds_conj _ _ _ e).1 h).1
  | andRight _ _ => exact fun e h => ((Formula.holds_conj _ _ _ e).1 h).2
  | andIntro _ _ hp hq =>
    exact fun e h => (Formula.holds_conj _ _ _ e).2 ⟨hp e h, hq e h⟩
  | orLeft _ _ => exact fun e h => (Formula.holds_disj _ _ _ e).2 (.inl h)
  | orRight _ _ => exact fun e h => (Formula.holds_disj _ _ _ e).2 (.inr h)
  | orElim _ _ hp hq =>
    intro e h
    obtain ⟨hc, hbranches⟩ := (Formula.holds_conj _ _ _ e).1 h
    rcases (Formula.holds_disj _ _ _ e).1 hbranches with hl | hr
    · exact hp e ((Formula.holds_conj _ _ _ e).2 ⟨hc, hl⟩)
    · exact hq e ((Formula.holds_conj _ _ _ e).2 ⟨hc, hr⟩)
  | existsIntro body x =>
    intro e h
    refine (Formula.holds_ex _ _ e).2 ⟨e x, ?_⟩
    simpa only [Renaming.pull_openHead] using (Formula.holds_rename A body _ e).1 h
  | @existsElim _ _ _ c q _ h =>
    intro e he
    obtain ⟨hc, hex⟩ := (Formula.holds_conj _ _ _ e).1 he
    obtain ⟨x, hx⟩ := (Formula.holds_ex _ _ e).1 hex
    let e' := Assignment.cons x e
    have hc' : (c.rename (fun i => .there i)).Holds A e' := by
      apply (Formula.holds_rename A c _ e').2
      simpa only [e', Assignment.pull_cons_there, Assignment.pull_id] using hc
    have hq := (Formula.holds_rename A q _ e').1 (h e' ((Formula.holds_conj _ _ _ e').2 ⟨hc', hx⟩))
    simpa only [e', Assignment.pull_cons_there, Assignment.pull_id] using hq
  | eqRefl x => exact fun e _ => rfl
  | eqSubst body x y =>
    intro e he
    obtain ⟨heq, hp⟩ := (Formula.holds_conj _ _ _ e).1 he
    have hv : e x = e y := heq
    apply (Formula.holds_rename A body _ e).2
    rw [Renaming.pull_openHead, ← hv, ← Renaming.pull_openHead e x]
    exact (Formula.holds_rename A body _ e).1 hp

end Derivation

/-- A primitive presentation also retains the derivation of each declaration marked derived. -/
structure PrimitivePresentation where
  /-- The named sort, operation and relation families. -/
  signature : Signature.{u}
  /-- The written Law declarations and their roles. -/
  laws : LawDeclarations signature
  /-- An inclusion presentation for a partial domain, when the declaration provides one. -/
  domainInclusions (p : signature.Partial) : Option (DomainInclusions p) := none
  /-- Each derived Law has a proof from the required Laws and structural graph axioms. -/
  derived (i : laws.LawName) : laws.role i = .derived →
    Derivation laws.toTheory (laws.statement i).input (laws.statement i).conclusion

/-- The theory presented by the required declarations, as in Definition 1.7. -/
def PrimitivePresentation.theory (P : PrimitivePresentation.{u}) : Theory.{u} :=
  P.laws.toTheory

end SHIGURE
