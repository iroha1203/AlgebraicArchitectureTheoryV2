import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawLocalValidation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Raw queries declared before the site and coefficient ring

The query indices use native context references, candidate coordinate/relation
carriers, and a raw coefficient-carrier/zero pair. They contain no selected
site, preorder arrow, or completed coefficient ring. A variable-image address
is a pair of contexts; readability is an activation condition. Polynomial
values use finite sparse data, whose type is available before a ring exists.

The bridge below retains all point responses of the verified raw assembler.
Its site and coefficient ring are used only after the common query and value
types have been declared, to specify activation and the local raw equations.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate

noncomputable section

universe u v

open CategoryTheory Site LawAlgebra IndependentPolynomialExpressions

variable {U : AtomCarrier.{u}}

/-- A raw coefficient carrier and a candidate zero, with no algebraic structure. -/
abbrev CoefficientRef := (K : Type v) × K

/-- The reference selected by a native coefficient ring's primitive zero. -/
def coefficientRef (k : Type v) [Zero k] : CoefficientRef.{v} := ⟨k, 0⟩

/-- Raw query roles use only context references, raw carrier candidates, and primitive arguments. -/
inductive Query (A : ArchitectureObject U) where
  /-- Coordinate carrier at a context, before choosing a site. -/
  | coordinate (W : ArchCtx A)
  /-- Label at a candidate coordinate. -/
  | label (W : ArchCtx A) (C : Type u) (c : C)
  /-- Local-data carrier at a candidate coordinate. -/
  | localData (W : ArchCtx A) (C : Type u) (c : C)
  /-- Relation-index carrier at a context. -/
  | relation (W : ArchCtx A)
  /-- One finite relation polynomial at candidate variable, relation, and coefficient carriers. -/
  | polynomial (W : ArchCtx A) (C J : Type u) (r : CoefficientRef.{v}) (j : J)
  /-- One variable image at a context pair; no preorder arrow is part of the address. -/
  | image (W V : ArchCtx A) (C D : Type u) (r : CoefficientRef.{v}) (d : D)

/-- Each response is a type reference, a label, or finite sparse polynomial data. -/
def Query.Value {A : ArchitectureObject U} : Query.{u, v} A → Type (max (u + 1) (v + 1))
  | .coordinate _ => ULift.{max (u + 1) (v + 1)} (Type u)
  | .label _ _ _ => ULift.{max (u + 1) (v + 1)} (Option CoordinateLabel)
  | .localData _ _ _ => ULift.{max (u + 1) (v + 1)} (Option (Type u))
  | .relation _ => ULift.{max (u + 1) (v + 1)} (Type u)
  | .polynomial _ C _ r _ => ULift.{max (u + 1) (v + 1)} (Option (Sparse C r.1 r.2))
  | .image _ _ C _ r _ => ULift.{max (u + 1) (v + 1)} (Option (Sparse C r.1 r.2))

/-- A primitive table whose index and value types precede site and ring selection. -/
abbrev Table (A : ArchitectureObject U) := (q : Query.{u, v} A) → q.Value

variable {A : ArchitectureObject U}

/-- Read the coordinate declaration of a context. -/
abbrev coord (t : Table.{u, v} A) (W : ArchCtx A) : Type u := (t (.coordinate W)).down

/-- Read the relation declaration of a context. -/
abbrev rel (t : Table.{u, v} A) (W : ArchCtx A) : Type u := (t (.relation W)).down

/-- Sparse values transport only across equality of the primitive coefficient reference. -/
def transportPolynomial {C : Type u} {r s : CoefficientRef.{v}} (h : r = s)
    (p : Option (Sparse C s.1 s.2)) : Option (Sparse C r.1 r.2) := h.symm ▸ p

variable (S : AATSite A) (k : Type v) [CommRing k]

/-- Candidate activation compares primitive declarations and the refinement predicate. -/
structure IsTyped (t : Table.{u, v} A) : Prop where
  /-- Labels are present exactly at the selected coordinate carrier. -/
  label : ∀ W C c, (t (.label W C c)).down.isSome ↔ C = coord t W
  /-- Local-data type references have the same activation rule. -/
  localData : ∀ W C c, (t (.localData W C c)).down.isSome ↔ C = coord t W
  /-- Relation polynomials match all three declared carriers and the primitive zero. -/
  polynomial : ∀ W C J r j, (t (.polynomial W C J r j)).down.isSome ↔
    C = coord t W ∧ J = rel t W ∧ r = coefficientRef k
  /-- Variable images also require readability of the source/target context pair. -/
  image : ∀ W V C D r d, (t (.image W V C D r d)).down.isSome ↔
    S.contextPreorder.le W V ∧ C = coord t W ∧ D = coord t V ∧ r = coefficientRef k

/-- Restrict candidate queries to the actual coefficient reference and actual site arrows. -/
def lower (t : Table.{u, v} A) : IndependentRawLocal.Table S k
  | .coordinate W => ⟨(t (.coordinate W.ctx)).down⟩
  | .label W C c => ⟨(t (.label W.ctx C c)).down⟩
  | .localData W C c => ⟨(t (.localData W.ctx C c)).down⟩
  | .relation W => ⟨(t (.relation W.ctx)).down⟩
  | .polynomial W C J j => ⟨(t (.polynomial W.ctx C J (coefficientRef k) j)).down⟩
  | @IndependentRawLocal.Query.image _ _ _ W V _ C D d =>
    ⟨(t (.image W.ctx V.ctx C D (coefficientRef k) d)).down⟩

/-- Actual arrows discharge readability and select exactly the active coefficient reference. -/
theorem lower_isTyped (t : Table.{u, v} A) (ht : IsTyped S k t) :
    IndependentRawLocal.IsTyped (lower S k t) where
  label W C c := ht.label W.ctx C c
  localData W C c := ht.localData W.ctx C c
  polynomial W C J j := by
    simpa [lower, IndependentRawLocal.coord, IndependentRawLocal.rel]
      using ht.polynomial W.ctx C J (coefficientRef k) j
  image {X Y} f C D d := by
    have hf : S.contextPreorder.le X.ctx Y.ctx := leOfHom f
    simpa [lower, IndependentRawLocal.coord, hf]
      using ht.image X.ctx Y.ctx C D (coefficientRef k) d

/-- Extend the site-indexed point table to all raw coefficient and context-pair candidates. -/
def raise (t : IndependentRawLocal.Table S k) : Table.{u, v} A := by
  classical
  intro q
  cases q with
  | coordinate W => exact ⟨(t (.coordinate ⟨W⟩)).down⟩
  | label W C c => exact ⟨(t (.label ⟨W⟩ C c)).down⟩
  | localData W C c => exact ⟨(t (.localData ⟨W⟩ C c)).down⟩
  | relation W => exact ⟨(t (.relation ⟨W⟩)).down⟩
  | polynomial W C J r j =>
    exact ⟨if hr : r = coefficientRef k then
      transportPolynomial hr (t (.polynomial ⟨W⟩ C J j)).down else none⟩
  | image W V C D r d =>
    exact ⟨if h : S.contextPreorder.le W V then
      if hr : r = coefficientRef k then
        transportPolynomial hr (t (.image (homOfLE h : (⟨W⟩ : S.category) ⟶ ⟨V⟩) C D d)).down
      else none else none⟩

/-- Extension marks exactly the readable, carrier-matching candidates as active. -/
theorem raise_isTyped (t : IndependentRawLocal.Table S k) (ht : IndependentRawLocal.IsTyped t) :
    IsTyped S k (raise S k t) where
  label W C c := ht.label ⟨W⟩ C c
  localData W C c := ht.localData ⟨W⟩ C c
  polynomial W C J r j := by
    classical
    by_cases hr : r = coefficientRef k
    · subst r
      simpa [raise, transportPolynomial, coord, rel] using ht.polynomial ⟨W⟩ C J j
    · simp [raise, hr]
  image W V C D r d := by
    classical
    by_cases h : S.contextPreorder.le W V
    · by_cases hr : r = coefficientRef k
      · subst r
        simpa [raise, transportPolynomial, coord, h] using
          ht.image (homOfLE h : (⟨W⟩ : S.category) ⟶ ⟨V⟩) C D d
      · simp [raise, hr]
    · simp [raise, h]

/-- Lowering the extended table recovers every original arrow and coefficient query. -/
theorem lower_raise (t : IndependentRawLocal.Table S k) : lower S k (raise S k t) = t := by
  classical
  funext q
  cases q with
  | coordinate | label | localData | relation => rfl
  | polynomial =>
    simp only [lower, raise, transportPolynomial]
    rfl
  | @image X Y f C D d =>
    have hf : S.contextPreorder.le X.ctx Y.ctx := leOfHom f
    simp only [lower, raise, dif_pos hf, transportPolynomial]
    rfl

/-- No additional freedom remains at unreadable or nonmatching coefficient candidates. -/
theorem raise_lower (t : Table.{u, v} A) (ht : IsTyped S k t) : raise S k (lower S k t) = t := by
  classical
  funext q
  cases q with
  | coordinate | label | localData | relation => rfl
  | polynomial W C J r j =>
    apply ULift.ext
    by_cases hr : r = coefficientRef k
    · subst r
      simp [lower, raise, transportPolynomial]
    · have hn := IndependentRawLocal.option_eq_none_of_inactive
        (fun h => hr ((ht.polynomial W C J r j).1 h).2.2)
      simp [raise, hr, hn]
  | image W V C D r d =>
    apply ULift.ext
    by_cases h : S.contextPreorder.le W V
    · by_cases hr : r = coefficientRef k
      · subst r
        simp [lower, raise, transportPolynomial, h]
      · have hn := IndependentRawLocal.option_eq_none_of_inactive
          (fun hh => hr ((ht.image W V C D r d).1 hh).2.2.2)
        simp [raise, h, hr, hn]
    · have hn := IndependentRawLocal.option_eq_none_of_inactive
        (fun hh => h ((ht.image W V C D r d).1 hh).1)
      simp [raise, h, hn]

/-- Generator, identity, and composition equations use the selected primitive point responses. -/
abbrev IsLawful (t : Table.{u, v} A) (ht : IsTyped S k t) : Prop :=
  IndependentRawLocal.IsLawful (lower S k t) (lower_isTyped S k t ht)

/-- Lawful raw candidate tables have the common index type declared before site and ring selection. -/
abbrev LawfulTable := {t : Table.{u, v} A // ∃ ht : IsTyped S k t, IsLawful S k t ht}

/-- Extending a lawful table preserves all independent generator and variable equations. -/
theorem raise_isLawful (t : IndependentRawLocal.Table S k)
    (ht : IndependentRawLocal.IsTyped t) (hl : IndependentRawLocal.IsLawful t ht) :
    IsLawful S k (raise S k t) (raise_isTyped S k t ht) := by
  unfold IsLawful
  simpa only [lower_raise] using hl

/-- The candidate and site-indexed lawful tables have exactly the same computational data. -/
def tableEquiv : IndependentRawLocal.LawfulTable S k ≃ LawfulTable S k where
  toFun t := ⟨raise S k t.val, raise_isTyped S k t.val t.property.choose,
    raise_isLawful S k t.val t.property.choose t.property.choose_spec⟩
  invFun t := ⟨lower S k t.val, lower_isTyped S k t.val t.property.choose, t.property.choose_spec⟩
  left_inv t := Subtype.ext (lower_raise S k t.val)
  right_inv t := Subtype.ext (raise_lower S k t.val t.property.choose)

/-- Complete raw objects correspond to lawful tables with site-independent query and value types. -/
def rawTableEquiv : RawAmbientRestrictionSystem S k ≃ LawfulTable S k :=
  IndependentRawLocal.rawTableEquiv.trans (tableEquiv S k)

/-- Read every native raw field and normalize every inactive candidate. -/
def read (B : RawAmbientRestrictionSystem S k) : Table.{u, v} A :=
  raise S k (IndependentRawLocal.read B)

/-- Native raw data satisfies the complete candidate activation rules. -/
theorem read_isTyped (B : RawAmbientRestrictionSystem S k) : IsTyped S k (read S k B) :=
  raise_isTyped S k _ (IndependentRawLocal.read_isTyped B)

/-- Native raw data satisfies the independently stated generator and variable equations. -/
theorem read_isLawful (B : RawAmbientRestrictionSystem S k) :
    IsLawful S k (read S k B) (read_isTyped S k B) :=
  raise_isLawful S k _ (IndependentRawLocal.read_isTyped B) (IndependentRawLocal.read_isLawful B)

/-- Assemble the native raw system after selecting its readable pairs and primitive coefficient reference. -/
def assemble (t : Table.{u, v} A) (ht : IsTyped S k t) (hl : IsLawful S k t ht) :
    RawAmbientRestrictionSystem S k :=
  IndependentRawLocal.assemble (lower S k t) (lower_isTyped S k t ht) hl

/-- Native assembly recovers every original raw field exactly. -/
theorem assemble_read (B : RawAmbientRestrictionSystem S k) :
    assemble S k (read S k B) (read_isTyped S k B) (read_isLawful S k B) = B :=
  (rawTableEquiv S k).left_inv B

/-- Re-reading recovers every candidate response, including unreadable pairs and wrong zero references. -/
theorem read_assemble (t : Table.{u, v} A) (ht : IsTyped S k t) (hl : IsLawful S k t ht) :
    read S k (assemble S k t ht hl) = t := by
  unfold read assemble
  rw [IndependentRawLocal.read_assemble]
  exact raise_lower S k t ht

/-- The common raw candidate reading separates all complete native raw systems. -/
theorem read_injective : Function.Injective (read S k) := by
  intro B B' h
  exact (rawTableEquiv S k).injective (Subtype.ext h)

end

end AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentRawCandidate
