import Formal.SHIGURE.Part1.CompositionComparison
import Mathlib.CategoryTheory.Category.Basic

/-! # The positive logic of theories

Appendix A develops syntactic substitution, soundness, and translation.
Interpretations compose by translating their proof trees. The morphisms
of the category of theories are quotients by mutual derivability of the
primitive replacements, with the sort maps kept as part of the data.

## Implementation notes

Composition uses proof-tree transport and the comparisons of translated
formulas to satisfy every field of an interpretation. The hom quotient
identifies representatives using their primitive replacements and sort maps.
The category laws then follow from mutual derivability.
-/

universe u

namespace SHIGURE.Derivation

variable {T : Theory.{u}} {Γ Δ : List T.signature.SortType}

/-- The witness form and guarded substitution of Appendix A.1 are mutually derivable. -/
theorem bindFormula_equivalent (θ : Substitution T.signature Γ Δ) (p : Formula T.signature Γ) :
    Equivalent T (θ.bindFormula p) (θ.defined.conj (p.substitute θ)) :=
  .ofDerivations (bindFormulaDerivations θ p).1 (bindFormulaDerivations θ p).2

end SHIGURE.Derivation

namespace SHIGURE.Interpretation

variable {S T U V : Theory.{u}}

/-- The translation of mutually derivable formulas again gives mutual derivability. -/
theorem translateEquivalent (v : Interpretation S T) {Γ : List S.signature.SortType}
    {p q : Formula S.signature Γ} (same : Derivation.Equivalent S p q) :
    Derivation.Equivalent T (v.translation.formula p) (v.translation.formula q) := by
  obtain ⟨⟨forward⟩, ⟨backward⟩⟩ := same
  exact .ofDerivations (v.translateDerivation forward) (v.translateDerivation backward)

/-- A proof of totality translates to a proof of the replacement's totality. -/
private noncomputable def translateTotal (v : Interpretation T U)
    {Γ : List T.signature.SortType} {s : T.signature.SortType} (t : Term T.signature Γ s)
    (total : Derivation T .truth t.defined) :
    Derivation U .truth (v.translation.term t).defined :=
  .cut (v.translateDerivation total) (Classical.choice (v.translation.defined_equivalent t).2)

/-- Proposition A.4: the composite candidate is an interpretation. -/
noncomputable def comp (v : Interpretation T U) (u : Interpretation S T) :
    Interpretation S U where
  onSort := v.onSort ∘ u.onSort
  translation := v.compCandidate u
  total f := by
    simpa only [compCandidate, Translation.comp_operation, Term.castContext_defined, Formula.castContext_truth] using
      ((v.translateTotal _ (u.total f)).castContext List.map_map)
  quantity q := by
    simpa only [compCandidate, Translation.comp_operation, Term.castContext_defined, Formula.castContext_truth] using
      ((v.translateTotal _ (u.quantity q)).castContext List.map_map)
  partialDefined p := by
    have transported := Derivation.cut (v.translateDerivation (u.partialDefined p))
      (Classical.choice (v.translation.defined_equivalent (u.translation.operation (.partialOp p))).2)
    simpa only [compCandidate, Translation.comp_partialDomain, Translation.comp_operation,
      Term.castContext_defined] using transported.castContext List.map_map
  definedPartial p := by
    have transported := Derivation.cut
      (Classical.choice (v.translation.defined_equivalent (u.translation.operation (.partialOp p))).1)
      (v.translateDerivation (u.definedPartial p))
    simpa only [compCandidate, Translation.comp_partialDomain, Translation.comp_operation,
      Term.castContext_defined] using transported.castContext List.map_map
  preserves name := by
    have input := v.translation.comp_formula_equivalent u.translation (S.law name).input
    have output := v.translation.comp_formula_equivalent u.translation (S.law name).conclusion
    exact .cut (Classical.choice input.1)
      (.cut ((v.translateDerivation (u.preserves name)).castContext List.map_map) (Classical.choice output.2))

end SHIGURE.Interpretation

namespace SHIGURE.Translation

variable {S T U V : Theory.{u}}
  {f : S.signature.SortType → T.signature.SortType} {g : T.signature.SortType → U.signature.SortType}

/-- Comparing all positive formulas in particular compares every primitive replacement. -/
theorem Equivalent.ofFormula {left right : Translation S.signature T.signature f}
    (all : ∀ {Γ : List S.signature.SortType} (p : Formula S.signature Γ),
      Derivation.Equivalent T (left.formula p) (right.formula p)) : Equivalent left right := by
  refine ⟨?_, ?_, ?_⟩
  · intro op
    let p : Formula S.signature (op.arity.output :: op.arity.inputs) :=
      .atom (.graph op (fun i => .there i) .here)
    simpa only [p, formula_atom, atomic_graphAt, Renaming.mapSorts_there, Var.mapSorts, Term.graph] using all p
  · intro r
    let p : Formula S.signature (S.signature.relInputs r) := .atom (.rel r (fun i => i))
    simpa only [p, formula_atom, atomic_rel, Renaming.mapSorts_id, Formula.rename_id] using all p
  · intro p'
    let p : Formula S.signature (S.signature.partialArity p').inputs := .atom (.domain p' (fun i => i))
    simpa only [p, formula_atom, atomic_domain, Renaming.mapSorts_id, Formula.rename_id] using all p

/-- Identity translation agrees with transport along the identity sort map. -/
theorem identityFormula_cast_equivalent {Γ : List T.signature.SortType} (p : Formula T.signature Γ) :
    Derivation.Equivalent T ((identity T.signature).formula p) (p.castContext (List.map_id Γ).symm) := by
  simpa only [Renaming.mapSorts_id_eq_castContext, ← Formula.castContext_eq_rename] using
    identityFormula_equivalent p

end SHIGURE.Translation

namespace SHIGURE.Translation

variable {S T U : Theory.{u}}
  {f : S.signature.SortType → T.signature.SortType} {g : T.signature.SortType → U.signature.SortType}

/-- A common outer interpretation transports both directions of the inner equivalence. -/
theorem Equivalent.comp_inner (w : Interpretation T U) {left right : Translation S.signature T.signature f}
    (same : Equivalent left right) :
    Equivalent (w.translation.comp left) (w.translation.comp right) := by
  apply Equivalent.ofFormula
  intro Γ p
  exact (w.translation.comp_formula_equivalent left p).trans
    (((w.translateEquivalent (same.formula p)).castContext _).trans
      (w.translation.comp_formula_equivalent right p).symm)

/-- Equivalent outer replacements preserve a common inner translation. -/
theorem Equivalent.comp_outer {left right : Translation T.signature U.signature g}
    (same : Equivalent left right) (u : Translation S.signature T.signature f) :
    Equivalent (left.comp u) (right.comp u) := by
  apply Equivalent.ofFormula
  intro Γ p
  exact (left.comp_formula_equivalent u p).trans
    (((same.formula (u.formula p)).castContext _).trans (right.comp_formula_equivalent u p).symm)

end SHIGURE.Translation

namespace SHIGURE.Formula

variable {sig : Signature.{u}} {Γ : List sig.SortType}

/-- Transport along any equality from a context to itself leaves the formula fixed. -/
theorem castContext_self (same : Γ = Γ) (p : Formula sig Γ) : p.castContext same = p := rfl

end SHIGURE.Formula

namespace SHIGURE.Interpretation

variable {S T U V : Theory.{u}}

/-- Equivalent inner interpretations yield equivalent composites with a fixed outer interpretation. -/
theorem comp_congr_inner (w : Interpretation T U) {l r : Interpretation S T} (h : l.Equivalent r) :
    (w.comp l).Equivalent (w.comp r) := by
  obtain ⟨same, replacements⟩ := h
  cases l
  cases r
  cases same
  exact ⟨rfl, replacements.comp_inner w⟩

/-- Equivalent outer interpretations yield equivalent composites with a fixed inner interpretation. -/
theorem comp_congr_outer {l r : Interpretation T U} (h : l.Equivalent r) (w : Interpretation S T) :
    (l.comp w).Equivalent (r.comp w) := by
  obtain ⟨same, replacements⟩ := h
  cases l
  cases r
  cases same
  exact ⟨rfl, replacements.comp_outer w.translation⟩

/-- Composition respects equivalence of representatives at both ends. -/
theorem comp_congr {l r : Interpretation S T} {l' r' : Interpretation T U}
    (h : l.Equivalent r) (h' : l'.Equivalent r') :
    (l'.comp l).Equivalent (r'.comp r) :=
  (l'.comp_congr_inner h).trans (comp_congr_outer h' r)

/-- The identity at the source is a unit for composition of interpretations. -/
theorem comp_id (u : Interpretation S T) : (u.comp (identity S)).Equivalent u := by
  refine ⟨rfl, Translation.Equivalent.ofFormula ?_⟩
  intro Γ p
  refine (u.translation.comp_formula_equivalent (identity S).translation p).trans ?_
  have preservesIdentity := u.translateEquivalent (Translation.identityFormula_cast_equivalent (T := S) p)
  simpa only [Translation.formula_castContext, Formula.castContext_trans, Formula.castContext_self] using
    (preservesIdentity.castContext (List.map_map (l := Γ) (g := u.onSort) (f := id)))

/-- The identity at the target is a unit for composition of interpretations. -/
theorem id_comp (u : Interpretation S T) : ((identity T).comp u).Equivalent u := by
  refine ⟨rfl, Translation.Equivalent.ofFormula ?_⟩
  intro Γ p
  refine ((identity T).translation.comp_formula_equivalent u.translation p).trans ?_
  have compareIdentity := Translation.identityFormula_cast_equivalent (u.translation.formula p)
  simpa only [Formula.castContext_trans, Formula.castContext_self] using
    (compareIdentity.castContext (List.map_map (l := Γ) (g := id) (f := u.onSort)))

/-- Both composites of three interpretations translate to the same formula up to mutual derivability. -/
theorem comp_assoc (w : Interpretation U V) (v : Interpretation T U) (u : Interpretation S T) :
    (w.comp (v.comp u)).Equivalent ((w.comp v).comp u) := by
  refine ⟨rfl, Translation.Equivalent.ofFormula ?_⟩
  intro Γ p
  let nested := w.translation.formula (v.translation.formula (u.translation.formula p))
  let flatten : Formula V.signature (Γ.map (w.onSort ∘ v.onSort ∘ u.onSort)) :=
    nested.castContext ((List.map_map (l := Γ.map u.onSort) (g := w.onSort) (f := v.onSort)).trans
      (List.map_map (l := Γ) (g := w.onSort ∘ v.onSort) (f := u.onSort)))
  have rightNested := w.translateEquivalent (v.translation.comp_formula_equivalent u.translation p)
  have leftSide : Derivation.Equivalent V ((w.comp (v.comp u)).translation.formula p) flatten :=
    (w.translation.comp_formula_equivalent (v.comp u).translation p).trans (by
      simpa only [flatten, nested, Translation.formula_castContext, Formula.castContext_trans] using
        (rightNested.castContext (List.map_map (l := Γ) (g := w.onSort) (f := v.onSort ∘ u.onSort))))
  have leftNested := w.translation.comp_formula_equivalent v.translation (u.translation.formula p)
  have rightSide : Derivation.Equivalent V (((w.comp v).comp u).translation.formula p) flatten :=
    ((w.comp v).translation.comp_formula_equivalent u.translation p).trans (by
      simpa only [flatten, nested, Formula.castContext_trans] using
        (leftNested.castContext (List.map_map (l := Γ) (g := w.onSort ∘ v.onSort) (f := u.onSort))))
  exact leftSide.trans rightSide.symm

end SHIGURE.Interpretation

namespace SHIGURE.Theory

/-- Definition 1.9 gives the equivalence relation on representative interpretations. -/
def interpretationSetoid (S T : Theory.{u}) : Setoid (Interpretation S T) where
  r := Interpretation.Equivalent
  iseqv := ⟨Interpretation.Equivalent.refl, Interpretation.Equivalent.symm, Interpretation.Equivalent.trans⟩

/-- Morphisms of theories are classes of equivalent interpretations. -/
abbrev Hom (S T : Theory.{u}) := Quotient (interpretationSetoid S T)

/-- Composition of interpretations descends to the quotient by mutual derivability. -/
noncomputable def compose {S T U : Theory.{u}} : Hom S T → Hom T U → Hom S U :=
  Quotient.map₂ (fun u v => v.comp u) (fun _ _ hu _ _ hv => Interpretation.comp_congr hu hv)

/-- Proposition A.4: theories and equivalence classes of interpretations form a category. -/
noncomputable instance category : CategoryTheory.Category.{u} Theory.{u} where
  Hom := Hom
  id S := Quotient.mk _ (Interpretation.identity S)
  comp := compose
  id_comp map := Quotient.inductionOn map fun u => Quotient.sound u.comp_id
  comp_id map := Quotient.inductionOn map fun u => Quotient.sound u.id_comp
  assoc first second third := Quotient.inductionOn₃ first second third fun u v w =>
    Quotient.sound (Interpretation.comp_assoc w v u)

open CategoryTheory

/-- Use an interpretation as a morphism of theories. -/
def ofInterpretation {S T : Theory.{u}} (u : Interpretation S T) : S ⟶ T :=
  Quotient.mk (interpretationSetoid S T) u

/-- Two representatives define the same categorical morphism exactly when they are equivalent. -/
theorem ofInterpretation_eq_iff {S T : Theory.{u}} (u v : Interpretation S T) :
    ofInterpretation u = ofInterpretation v ↔ u.Equivalent v :=
  Quotient.eq

/-- The identity morphism is represented by the identity interpretation. -/
theorem ofInterpretation_id (T : Theory.{u}) : ofInterpretation (Interpretation.identity T) = 𝟙 T :=
  rfl

/-- Composition in the installed category uses the proved composite on representatives. -/
theorem ofInterpretation_comp {S T U : Theory.{u}} (u : Interpretation S T) (v : Interpretation T U) :
    ofInterpretation u ≫ ofInterpretation v = ofInterpretation (v.comp u) :=
  rfl

end SHIGURE.Theory
