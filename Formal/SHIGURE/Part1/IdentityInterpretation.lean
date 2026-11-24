import Formal.SHIGURE.Part1.Interpretation
import Formal.SHIGURE.Part1.DerivationLemmas

/-! # The identity interpretation

The raw identity sends each primitive to its own symbol. Definition 1.9
also requires derivations for totality, partial domains, and the required
Laws. The finite argument block in each value graph is discharged using
the derived rules for graph atoms.
-/

universe u

namespace SHIGURE

namespace Translation

variable (T : Theory.{u}) {Γ : List T.signature.SortType}

/-- Translation by the identity changes only the type's presentation of a context. -/
private def retype : Renaming Γ (Γ.map id) :=
  fun i => i.mapSorts id

/-- Retyping an extended context keeps the bound variable and retypes its tail. -/
private theorem retype_lift {s : T.signature.SortType} :
    @retype T (s :: Γ) = @Renaming.lift T.signature.SortType Γ (Γ.map id) s (@retype T Γ) := by
  funext t i
  cases i <;> rfl

/-- Compare the identity replacement's value graph with the graph of the original symbol. -/
def identityGraph (op : Operation T.signature) :
    let replacement := (identity T.signature).operation op
    let atom : Formula T.signature (op.arity.output :: op.arity.inputs.map id) :=
      .atom (.graph op (fun i => .there (i.mapSorts id)) .here)
    Derivation T replacement.graph atom × Derivation T atom replacement.graph :=
  Derivation.primitiveGraph op (fun i => .there (i.mapSorts id)) .here

/-- At identity, translated atoms are mutually derivable with the original retyped atoms. -/
def identityAtomic (a : Atomic T.signature Γ) :
    Derivation T ((identity T.signature).atomic a) ((Formula.atom a).rename (retype T)) ×
    Derivation T ((Formula.atom a).rename (retype T)) ((identity T.signature).atomic a) := by
  cases a with
  | eq x y => exact ⟨.refl _, .refl _⟩
  | rel r inputs =>
    have same : (identity T.signature).atomic (.rel r inputs) =
        (Formula.atom (.rel r inputs)).rename (retype T) := by
      simp only [atomic_rel, identity_relation, Formula.rename_atom, Atomic.rename_rel, retype,
        Renaming.mapSorts_apply]
    rw [same]
    exact ⟨.refl _, .refl _⟩
  | domain p inputs =>
    have same : (identity T.signature).atomic (.domain p inputs) =
        (Formula.atom (.domain p inputs)).rename (retype T) := by
      simp only [atomic_domain, identity_domain, Formula.rename_atom, Atomic.rename_domain, retype,
        Renaming.mapSorts_apply]
    rw [same]
    exact ⟨.refl _, .refl _⟩
  | graph op inputs y =>
    let ρ : Renaming (op.arity.output :: op.arity.inputs.map id) (Γ.map id) :=
      Renaming.cons (y.mapSorts id) (inputs.mapSorts id)
    have forward := Derivation.rename ρ (identityGraph T op).1
    have backward := Derivation.rename ρ (identityGraph T op).2
    exact ⟨by
      simpa only [atomic_graph, ρ, Formula.rename_atom, Atomic.rename_graph, Renaming.cons_here,
        Renaming.cons_there, Renaming.mapSorts_apply, retype] using forward,
      by simpa only [atomic_graph, ρ, Formula.rename_atom, Atomic.rename_graph, Renaming.cons_here,
        Renaming.cons_there, Renaming.mapSorts_apply, retype] using backward⟩

/-- Identity translation is mutually derivable with the retyped original formula. -/
def identityFormula : {Γ : List T.signature.SortType} → (p : Formula T.signature Γ) →
    Derivation T ((identity T.signature).formula p) (p.rename (retype T)) ×
    Derivation T (p.rename (retype T)) ((identity T.signature).formula p)
  | _, .atom a => identityAtomic T a
  | _, .truth => ⟨.refl _, .refl _⟩
  | _, .falsehood => ⟨.refl _, .refl _⟩
  | _, .conj p q =>
    let hp := identityFormula p
    let hq := identityFormula q
    ⟨hp.1.andMono hq.1, hp.2.andMono hq.2⟩
  | _, .disj p q =>
    let hp := identityFormula p
    let hq := identityFormula q
    ⟨hp.1.orMono hq.1, hp.2.orMono hq.2⟩
  | _, .ex p =>
    let hp := identityFormula p
    ⟨by simpa only [formula_ex, Formula.rename_ex, retype_lift] using hp.1.existsMono,
      by simpa only [formula_ex, Formula.rename_ex, retype_lift] using hp.2.existsMono⟩

/-- Compare the replacement's definedness with existence of a primitive graph output. -/
def identityDefined (op : Operation T.signature) :
    let defined := ((identity T.signature).operation op).defined
    let hasOutput := (GraphAxiom.hasOutput op).rename (retype T)
    Derivation T defined hasOutput × Derivation T hasOutput defined :=
  ⟨(identityGraph T op).1.existsMono, (identityGraph T op).2.existsMono⟩

end Translation

namespace Interpretation

/-- The identity interpretation discharges all clauses using the original theory and graph Law data. -/
def identity (T : Theory.{u}) : Interpretation T T where
  onSort := id
  translation := Translation.identity T.signature
  total f :=
    .cut (.rename (Translation.retype T) (.graph (.totality f)))
      (Translation.identityDefined T (.total f)).2
  quantity q :=
    .cut (.rename (Translation.retype T) (.graph (.quantityTotality q)))
      (Translation.identityDefined T (.quantity q)).2
  partialDefined p :=
    .cut (.rename (Translation.retype T) (.graph (.domainImpliesGraph p)))
      (Translation.identityDefined T (.partialOp p)).2
  definedPartial p := by
    refine .cut (Translation.identityDefined T (.partialOp p)).1 ?_
    apply Derivation.existsElimPlain
    let ax := GraphAxiom.graphImpliesDomain p
    have d := Derivation.rename (fun i => i.mapSorts id) (Derivation.graph (T := T) ax)
    exact d
  preserves name :=
    .cut (Translation.identityFormula T (T.law name).input).1
      (.cut (.rename (Translation.retype T) (.required name))
        (Translation.identityFormula T (T.law name).conclusion).2)

/-- An identity interpretation retains the original name of each sort. -/
theorem identity_onSort (T : Theory.{u}) (s : T.signature.SortType) : (identity T).onSort s = s :=
  rfl

/-- The raw translation of an identity interpretation is the identity translation. -/
theorem identity_translation (T : Theory.{u}) :
    (identity T).translation = Translation.identity T.signature :=
  rfl

end Interpretation

end SHIGURE
