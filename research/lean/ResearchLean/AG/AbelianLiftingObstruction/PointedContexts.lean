import Formal.AG.Site.ContextCategory
import Formal.Util.AssertStandardAxioms

/-!
# Point-detecting choices of readable context maps

G-129 completion condition 4 permits choosing a concrete geometry input.
This module keeps every architecture context and the full restriction-existence
preorder, and specifies its selected readable maps using pointed contexts.

## Implementation notes

The extension of a probe records the point being tested. On a probe arrow the
relevant selected map is constant at that point; the other components use an
existing restriction witness. Thus naturality detects every component of a
geometry automorphism. Choosing an arbitrary restriction witness would not
justify identifying it with a prescribed probe map. No morphisms of the
geometry category are restricted, and no rigidity assertion is an input field.
-/

namespace AAT.AG.AbelianLiftingObstruction.PointedContexts

open Site CategoryTheory Classical

universe u
variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}

/-- A support probe records one original support point in its extension. -/
def supportProbe (W : ArchCtx A) (x : W.Support) : ArchCtx A where
  minimal := {
    Support := PUnit
    Axis := W.Axis
    Observable := W.Observable
    supportReads := fun _ a => W.minimal.supportReads x a
    supportReads_objectFamily := W.supportReads_objectFamily
    axisReads := W.minimal.axisReads
    observableReads := W.minimal.observableReads }
  Extension := W.Support
  extension := x

/-- An axis probe records one original axis point in its extension. -/
def axisProbe (W : ArchCtx A) (x : W.Axis) : ArchCtx A where
  minimal := {
    Support := W.Support
    Axis := PUnit
    Observable := W.Observable
    supportReads := W.minimal.supportReads
    supportReads_objectFamily := W.supportReads_objectFamily
    axisReads := fun _ => W.minimal.axisReads x
    observableReads := W.minimal.observableReads }
  Extension := W.Axis
  extension := x

/-- An observable probe is a target for the contravariant point restriction. -/
def observableProbe (W : ArchCtx A) (x : W.Observable) : ArchCtx A where
  minimal := {
    Support := W.Support
    Axis := W.Axis
    Observable := PUnit
    supportReads := W.minimal.supportReads
    supportReads_objectFamily := W.supportReads_objectFamily
    axisReads := W.minimal.axisReads
    observableReads := fun _ => W.minimal.observableReads x }
  Extension := W.Observable
  extension := x

/-- API: equality of extensions of the same type preserves their points. -/
theorem extension_heq {W V : ArchCtx A} (h : W = V) : HEq W.extension V.extension := by
  cases h
  rfl

/-- API: a support probe retains its designated point injectively. -/
theorem supportProbe_injective (W : ArchCtx A) : Function.Injective (supportProbe W) := by
  intro x y h
  exact eq_of_heq (extension_heq h)

/-- API: an axis probe retains its designated point injectively. -/
theorem axisProbe_injective (W : ArchCtx A) : Function.Injective (axisProbe W) := by
  intro x y h
  exact eq_of_heq (extension_heq h)

/-- API: an observable probe retains its designated point injectively. -/
theorem observableProbe_injective (W : ArchCtx A) :
    Function.Injective (observableProbe W) := by
  intro x y h
  exact eq_of_heq (extension_heq h)

/-- The full restriction-existence relation, unchanged from the canonical reading. -/
abbrev Readable (W V : ArchCtx A) :=
  (contextMorphismPreorderCategory A).le W V

/-- API: every support point yields a readable arrow from its probe. -/
theorem supportProbe_readable (W : ArchCtx A) (x : W.Support) :
    Readable (supportProbe W x) W :=
  ⟨⟨fun _ => x, id, id⟩, ⟨fun h => h, fun h => h, fun h => h,
    fun h => W.supportReads_objectFamily h⟩⟩

/-- API: every axis point yields a readable arrow from its probe. -/
theorem axisProbe_readable (W : ArchCtx A) (x : W.Axis) :
    Readable (axisProbe W x) W :=
  ⟨⟨id, fun _ => x, id⟩, ⟨fun h => h, fun h => h, fun h => h,
    fun h => W.supportReads_objectFamily h⟩⟩

/-- API: every observable point yields a readable arrow to its probe. -/
theorem observableProbe_readable (W : ArchCtx A) (x : W.Observable) :
    Readable W (observableProbe W x) :=
  ⟨⟨id, id, fun _ => x⟩, ⟨fun h => h, fun h => h, fun h => h,
    fun h => W.supportReads_objectFamily h⟩⟩

/-- Select a support map that evaluates designated point probes. -/
noncomputable def supportMap {W V : ArchCtx A} (h : Readable W V) : W.Support → V.Support :=
  if hp : ∃ x, W = supportProbe V x then fun _ => hp.choose
  else h.choose.supportMap

/-- Select an axis map that evaluates designated point probes. -/
noncomputable def axisMap {W V : ArchCtx A} (h : Readable W V) : W.Axis → V.Axis :=
  if hp : ∃ x, W = axisProbe V x then fun _ => hp.choose
  else h.choose.axisMap

/-- Select an observable restriction that evaluates designated point probes. -/
noncomputable def observableRestrict {W V : ArchCtx A} (h : Readable W V) :
    V.Observable → W.Observable :=
  if hp : ∃ x, V = observableProbe W x then fun _ => hp.choose
  else h.choose.observableRestrict

/-- The three independently selected components form the actual readable map. -/
noncomputable def readableMorphism {W V : ArchCtx A} (h : Readable W V) :
    ContextMorphism W V := ⟨supportMap h, axisMap h, observableRestrict h⟩

/-- Each selected component preserves the readings required of a restriction. -/
theorem readableMorphism_isRestriction {W V : ArchCtx A} (h : Readable W V) :
    (readableMorphism h).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s a ha
    change V.minimal.supportReads (supportMap h s) a
    unfold supportMap
    split
    · rename_i hp
      have aux : ∀ (Z : ArchCtx A) (x : V.Support), Z = supportProbe V x →
          ∀ (s : Z.Support), Z.minimal.supportReads s a → V.minimal.supportReads x a := by
        intro Z x he
        subst Z
        exact fun _ hx => hx
      exact aux W hp.choose hp.choose_spec s ha
    · exact h.choose_spec.1 ha
  · intro x hx
    change V.minimal.axisReads (axisMap h x)
    unfold axisMap
    split
    · rename_i hp
      have aux : ∀ (Z : ArchCtx A) (y : V.Axis), Z = axisProbe V y →
          ∀ (x : Z.Axis), Z.minimal.axisReads x → V.minimal.axisReads y := by
        intro Z y he
        subst Z
        exact fun _ hx => hx
      exact aux W hp.choose hp.choose_spec x hx
    · exact h.choose_spec.2.1 hx
  · intro x hx
    change W.minimal.observableReads (observableRestrict h x)
    unfold observableRestrict
    split
    · rename_i hp
      have aux : ∀ (Z : ArchCtx A) (y : W.Observable), Z = observableProbe W y →
          ∀ (x : Z.Observable), Z.minimal.observableReads x → W.minimal.observableReads y := by
        intro Z y he
        subst Z
        exact fun _ hx => hx
      exact aux V hp.choose hp.choose_spec x hx
    · exact h.choose_spec.2.2.1 hx
  · intro s a ha
    exact V.supportReads_objectFamily ha

/-- The canonical full preorder with explicit point-detecting selected maps. -/
noncomputable def contextPreorder (A : ArchitectureObject U) : ContextPreorderCategory A where
  le := Readable
  refl := (contextMorphismPreorderCategory A).refl
  trans := (contextMorphismPreorderCategory A).trans
  readableMorphism := readableMorphism
  readableMorphism_isRestriction := readableMorphism_isRestriction

/-- API: the selected relation has all and only the original readable arrows. -/
theorem contextPreorder_le_iff (W V : ArchCtx A) :
    (contextPreorder A).le W V ↔ (contextMorphismPreorderCategory A).le W V := Iff.rfl

/-- The unchanged relation retains its original product-context finite meets. -/
noncomputable def finiteMeet (A : ArchitectureObject U) :
    ContextFiniteMeet (contextPreorder A) where
  meet := productContext
  meet_le_left := productContextFiniteMeet.meet_le_left
  meet_le_right := productContextFiniteMeet.meet_le_right
  le_meet := productContextFiniteMeet.le_meet

/-- API: every selected support probe map has the designated constant value. -/
theorem supportMap_probe (W : ArchCtx A) (x : W.Support)
    (h : Readable (supportProbe W x) W) (s : (supportProbe W x).Support) :
    supportMap h s = x := by
  unfold supportMap
  rw [dif_pos ⟨x, rfl⟩]
  apply supportProbe_injective W
  exact (Exists.choose_spec (show ∃ y, supportProbe W x = supportProbe W y from ⟨x, rfl⟩)).symm

/-- API: every selected axis probe map has the designated constant value. -/
theorem axisMap_probe (W : ArchCtx A) (x : W.Axis)
    (h : Readable (axisProbe W x) W) (s : (axisProbe W x).Axis) : axisMap h s = x := by
  unfold axisMap
  rw [dif_pos ⟨x, rfl⟩]
  apply axisProbe_injective W
  exact (Exists.choose_spec (show ∃ y, axisProbe W x = axisProbe W y from ⟨x, rfl⟩)).symm

/-- API: every selected observable probe restriction has the designated value. -/
theorem observableRestrict_probe (W : ArchCtx A) (x : W.Observable)
    (h : Readable W (observableProbe W x)) (s : (observableProbe W x).Observable) :
    observableRestrict h s = x := by
  unfold observableRestrict
  rw [dif_pos ⟨x, rfl⟩]
  apply observableProbe_injective W
  exact (Exists.choose_spec
    (show ∃ y, observableProbe W x = observableProbe W y from ⟨x, rfl⟩)).symm

/-- G-129 geometry API: natural support endomorphisms fix every support point. -/
theorem support_family_eq_id
    (F : ∀ W : ContextCategoryObject (contextPreorder A), W.ctx.Support → W.ctx.Support)
    (hnat : ∀ {W V : ContextCategoryObject (contextPreorder A)} (w : W ⟶ V) x,
      supportMap (leOfHom w) (F W x) = F V (supportMap (leOfHom w) x))
    (W : ContextCategoryObject (contextPreorder A)) (x : W.ctx.Support) : F W x = x := by
  let P : ContextCategoryObject (contextPreorder A) := ⟨supportProbe W.ctx x⟩
  let w : P ⟶ W := homOfLE (supportProbe_readable W.ctx x)
  have h := hnat w PUnit.unit
  rw [supportMap_probe W.ctx x, supportMap_probe W.ctx x] at h
  exact h.symm

/-- G-129 geometry API: natural axis endomorphisms fix every axis point. -/
theorem axis_family_eq_id
    (F : ∀ W : ContextCategoryObject (contextPreorder A), W.ctx.Axis → W.ctx.Axis)
    (hnat : ∀ {W V : ContextCategoryObject (contextPreorder A)} (w : W ⟶ V) x,
      axisMap (leOfHom w) (F W x) = F V (axisMap (leOfHom w) x))
    (W : ContextCategoryObject (contextPreorder A)) (x : W.ctx.Axis) : F W x = x := by
  let P : ContextCategoryObject (contextPreorder A) := ⟨axisProbe W.ctx x⟩
  let w : P ⟶ W := homOfLE (axisProbe_readable W.ctx x)
  have h := hnat w PUnit.unit
  rw [axisMap_probe W.ctx x, axisMap_probe W.ctx x] at h
  exact h.symm

/-- G-129 geometry API: natural observable endomorphisms fix every observable point. -/
theorem observable_family_eq_id
    (F : ∀ W : ContextCategoryObject (contextPreorder A), W.ctx.Observable → W.ctx.Observable)
    (hnat : ∀ {W V : ContextCategoryObject (contextPreorder A)} (w : W ⟶ V) x,
      observableRestrict (leOfHom w) (F V x) = F W (observableRestrict (leOfHom w) x))
    (W : ContextCategoryObject (contextPreorder A)) (x : W.ctx.Observable) : F W x = x := by
  let P : ContextCategoryObject (contextPreorder A) := ⟨observableProbe W.ctx x⟩
  let w : W ⟶ P := homOfLE (observableProbe_readable W.ctx x)
  have h := hnat w PUnit.unit
  rw [observableRestrict_probe W.ctx x, observableRestrict_probe W.ctx x] at h
  exact h.symm

end AAT.AG.AbelianLiftingObstruction.PointedContexts

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction.PointedContexts
