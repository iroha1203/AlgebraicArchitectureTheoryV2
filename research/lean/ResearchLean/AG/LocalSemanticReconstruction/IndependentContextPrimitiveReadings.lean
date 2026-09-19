import Formal.AG.Site.ContextCategory
import Formal.Util.AssertStandardAxioms

/-!
# Primitive context-preorder readings for the independent G-124 verification

The query type depends on the architecture object and its native context
carrier, before any preorder or selected context morphism is chosen. A response
contains a refinement predicate or one support, axis, or observable value.
The three component functions and the native restriction law are assembled
from these point readings. The architecture object is supplied by the preceding
core-generation construction.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentContextPrimitive

universe u

open Site

variable {U : AtomCarrier.{u}}

/-- Independent context queries for refinement and the three native map roles. -/
inductive Query (A : ArchitectureObject U) where
  /-- Read whether one context is a refinement of another. -/
  | le (W V : ArchCtx A)
  /-- Read one support image of the selected readable morphism. -/
  | support (W V : ArchCtx A) (s : W.Support)
  /-- Read one axis image of the selected readable morphism. -/
  | axis (W V : ArchCtx A) (a : W.Axis)
  /-- Read one observable restriction in the native contravariant direction. -/
  | observable (W V : ArchCtx A) (x : V.Observable)

/-- The value type records the native direction of each point evaluation. -/
def Query.Value {A : ArchitectureObject U} : Query A → Type (u + 1)
  | .le _ _ => ULift.{u + 1} Prop
  | .support _ V _ => ULift.{u + 1} (Option V.Support)
  | .axis _ V _ => ULift.{u + 1} (Option V.Axis)
  | .observable W _ _ => ULift.{u + 1} (Option W.Observable)

/-- A dependent point table with no chosen preorder in its index type. -/
abbrev Table (A : ArchitectureObject U) := (q : Query A) → q.Value

variable {A : ArchitectureObject U}

/-- Recover the selected refinement relation from predicate readings. -/
abbrev le (t : Table A) (W V : ArchCtx A) : Prop := (t (.le W V)).down

/-- Map responses are present exactly on refinement pairs. -/
structure IsTyped (t : Table A) : Prop where
  /-- Support images are active exactly when the pair is readable. -/
  support : ∀ W V s, (t (.support W V s)).down.isSome ↔ le t W V
  /-- Axis images have the same activation condition. -/
  axis : ∀ W V a, (t (.axis W V a)).down.isSome ↔ le t W V
  /-- Observable restrictions have the same activation condition. -/
  observable : ∀ W V x, (t (.observable W V x)).down.isSome ↔ le t W V

/-- Collect active support images into the native forward support map. -/
def supportMap (t : Table A) (ht : IsTyped t) {W V : ArchCtx A}
    (h : le t W V) (s : W.Support) : V.Support :=
  (t (.support W V s)).down.get ((ht.support W V s).2 h)

/-- Collect active axis images into the native forward axis map. -/
def axisMap (t : Table A) (ht : IsTyped t) {W V : ArchCtx A}
    (h : le t W V) (a : W.Axis) : V.Axis :=
  (t (.axis W V a)).down.get ((ht.axis W V a).2 h)

/-- Collect active observable values into the native restriction map. -/
def observableRestrict (t : Table A) (ht : IsTyped t) {W V : ArchCtx A}
    (h : le t W V) (x : V.Observable) : W.Observable :=
  (t (.observable W V x)).down.get ((ht.observable W V x).2 h)

/-- Build the complete context morphism from its three independent point families. -/
def morphism (t : Table A) (ht : IsTyped t) {W V : ArchCtx A}
    (h : le t W V) : ContextMorphism W V :=
  ⟨supportMap t ht h, axisMap t ht h, observableRestrict t ht h⟩

/-- Local preorder laws and preservation of the native point readings. -/
structure IsLawful (t : Table A) (ht : IsTyped t) : Prop where
  /-- Every context refines itself. -/
  refl : ∀ W, le t W W
  /-- Refinement composes on each triple of contexts. -/
  trans : ∀ W V X, le t W V → le t V X → le t W X
  /-- The support image preserves each Atom reading. -/
  support : ∀ W V (h : le t W V) s a, W.minimal.supportReads s a →
    V.minimal.supportReads (supportMap t ht h s) a
  /-- The axis image preserves each readable axis. -/
  axis : ∀ W V (h : le t W V) a, W.minimal.axisReads a →
    V.minimal.axisReads (axisMap t ht h a)
  /-- The reverse observable map preserves each readable observable. -/
  observable : ∀ W V (h : le t W V) x, V.minimal.observableReads x →
    W.minimal.observableReads (observableRestrict t ht h x)

/-- Derive all four native restriction clauses from the three point preservation rules. -/
theorem morphism_isRestriction (t : Table A) (ht : IsTyped t) (hl : IsLawful t ht)
    {W V : ArchCtx A} (h : le t W V) : (morphism t ht h).IsRestriction :=
  ⟨hl.support W V h _ _, hl.axis W V h _, hl.observable W V h _,
    fun hx => V.minimal.supportReads_objectFamily hx⟩

/-- Assemble the native context preorder and all selected readable morphisms. -/
def assemble (t : Table A) (ht : IsTyped t) (hl : IsLawful t ht) :
    ContextPreorderCategory A where
  le := le t
  refl := hl.refl
  trans := hl.trans _ _ _
  readableMorphism := morphism t ht
  readableMorphism_isRestriction := morphism_isRestriction t ht hl

/-- Read the selected native morphism at one application, with inactive responses set to none. -/
noncomputable def read (C : ContextPreorderCategory A) : Table A := by
  classical
  intro q
  cases q with
  | le W V => exact ⟨C.le W V⟩
  | support W V s =>
    exact ⟨if h : C.le W V then some ((C.readableMorphism h).supportMap s) else none⟩
  | axis W V a =>
    exact ⟨if h : C.le W V then some ((C.readableMorphism h).axisMap a) else none⟩
  | observable W V x =>
    exact ⟨if h : C.le W V then some ((C.readableMorphism h).observableRestrict x) else none⟩

/-- Native refinement activates precisely its three selected component maps. -/
theorem read_isTyped (C : ContextPreorderCategory A) : IsTyped (read C) where
  support W V s := by
    classical
    by_cases h : C.le W V <;> simp [read, le, h]
  axis W V a := by
    classical
    by_cases h : C.le W V <;> simp [read, le, h]
  observable W V x := by
    classical
    by_cases h : C.le W V <;> simp [read, le, h]

/-- A collected support image equals the original selected support image. -/
theorem supportMap_read (C : ContextPreorderCategory A) {W V : ArchCtx A}
    (h : C.le W V) (s : W.Support) :
    supportMap (read C) (read_isTyped C) (W := W) (V := V) h s =
      (C.readableMorphism h).supportMap s := by
  simp [supportMap, read, h]

/-- A collected axis image equals the original selected axis image. -/
theorem axisMap_read (C : ContextPreorderCategory A) {W V : ArchCtx A}
    (h : C.le W V) (a : W.Axis) :
    axisMap (read C) (read_isTyped C) (W := W) (V := V) h a =
      (C.readableMorphism h).axisMap a := by
  simp [axisMap, read, h]

/-- A collected observable restriction equals its native evaluation. -/
theorem observableRestrict_read (C : ContextPreorderCategory A) {W V : ArchCtx A}
    (h : C.le W V) (x : V.Observable) :
    observableRestrict (read C) (read_isTyped C) (W := W) (V := V) h x =
      (C.readableMorphism h).observableRestrict x := by
  simp [observableRestrict, read, h]

/-- Native preorder and restriction laws generate all local laws. -/
theorem read_isLawful (C : ContextPreorderCategory A) : IsLawful (read C) (read_isTyped C) where
  refl := C.refl
  trans _ _ _ := C.trans
  support W V h s a ha := by
    simpa [supportMap_read] using (C.readableMorphism_isRestriction h).1 ha
  axis W V h a ha := by
    simpa [axisMap_read] using (C.readableMorphism_isRestriction h).2.1 ha
  observable W V h x hx := by
    simpa [observableRestrict_read] using (C.readableMorphism_isRestriction h).2.2.1 hx

/-- Context morphisms agree exactly when their three computational maps agree. -/
theorem morphism_ext {W V : ArchCtx A} {f g : ContextMorphism W V}
    (hs : f.supportMap = g.supportMap) (ha : f.axisMap = g.axisMap)
    (ho : f.observableRestrict = g.observableRestrict) : f = g := by
  cases f
  cases g
  cases hs
  cases ha
  cases ho
  rfl

/-- Refinement and the complete family of readable maps determine a context preorder. -/
theorem preorder_ext {C D : ContextPreorderCategory A}
    (hl : C.le = D.le) (hm : HEq (@C.readableMorphism) (@D.readableMorphism)) : C = D := by
  cases C
  cases D
  cases hl
  cases hm
  rfl

/-- Every native context preorder is recovered, including all three selected map components. -/
theorem assemble_read (C : ContextPreorderCategory A) :
    assemble (read C) (read_isTyped C) (read_isLawful C) = C := by
  apply preorder_ext (C := assemble (read C) (read_isTyped C) (read_isLawful C)) (D := C) rfl
  apply heq_of_eq
  funext W V h
  apply morphism_ext
  · funext s
    exact supportMap_read C h s
  · funext a
    exact axisMap_read C h a
  · funext x
    exact observableRestrict_read C h x

/-- Inactive optional responses are uniquely none. -/
theorem option_none {T : Type u} (x : Option T) (hx : ¬ x.isSome) : x = none := by
  cases x <;> simp_all

/-- The complete independent table is recovered after native assembly. -/
theorem read_assemble (t : Table A) (ht : IsTyped t) (hl : IsLawful t ht) :
    read (assemble t ht hl) = t := by
  classical
  funext q
  cases q with
  | le W V => rfl
  | support W V s =>
    apply ULift.ext
    by_cases h : le t W V
    · simp [read, assemble, morphism, supportMap, h, Option.some_get]
    · have hn := option_none _ (mt (ht.support W V s).1 h)
      simp [read, assemble, h, hn]
  | axis W V a =>
    apply ULift.ext
    by_cases h : le t W V
    · simp [read, assemble, morphism, axisMap, h, Option.some_get]
    · have hn := option_none _ (mt (ht.axis W V a).1 h)
      simp [read, assemble, h, hn]
  | observable W V x =>
    apply ULift.ext
    by_cases h : le t W V
    · simp [read, assemble, morphism, observableRestrict, h, Option.some_get]
    · have hn := option_none _ (mt (ht.observable W V x).1 h)
      simp [read, assemble, h, hn]

/-- The full native context-preorder type is equivalent to independent lawful point tables. -/
noncomputable def readingEquiv :
    ContextPreorderCategory A ≃ {t : Table A // ∃ ht : IsTyped t, IsLawful t ht} where
  toFun C := ⟨read C, read_isTyped C, read_isLawful C⟩
  invFun t := assemble t.val t.property.choose t.property.choose_spec
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property.choose t.property.choose_spec)

/-- An all-false refinement table with no map responses. -/
def noRefinement : Table A
  | .le _ _ => ⟨False⟩
  | .support _ _ _ => ⟨none⟩
  | .axis _ _ _ => ⟨none⟩
  | .observable _ _ _ => ⟨none⟩

/-- The all-false table satisfies activation, independently of the preorder laws. -/
theorem noRefinement_isTyped : IsTyped (noRefinement (A := A)) where
  support _ _ _ := by simp [noRefinement, le]
  axis _ _ _ := by simp [noRefinement, le]
  observable _ _ _ := by simp [noRefinement, le]

/-- Reflexivity rejects the all-false table at any native context. -/
theorem noRefinement_not_lawful (W : ArchCtx A) :
    ¬ IsLawful (noRefinement (A := A)) noRefinement_isTyped := fun h => h.refl W

/-- Remove all support images, retaining refinement, axes, and observables. -/
def eraseSupport (t : Table A) : Table A
  | .support _ _ _ => ⟨none⟩
  | q => t q

/-- Missing a support image on a reflexive pair is rejected by totality. -/
theorem eraseSupport_not_typed (C : ContextPreorderCategory A) (W : ArchCtx A) (s : W.Support) :
    ¬ IsTyped (eraseSupport (read C)) := by
  intro ht
  have h := (ht.support W W s).2 (C.refl W)
  simp [eraseSupport] at h

end AAT.AG.LocalSemanticReconstruction.IndependentContextPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentContextPrimitive
