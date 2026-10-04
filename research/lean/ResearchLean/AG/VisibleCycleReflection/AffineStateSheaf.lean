import ResearchLean.AG.VisibleCycleReflection.AffineFibers
import Mathlib.Topology.Sheaves.LocalPredicate
import Formal.Util.AssertStandardAxioms

/-!
# The sheaf of locally constant affine states

## Implementation notes

Sections are dependent functions into the generated affine fibers, locally
constant in an atlas chart. Mathlib's local-predicate construction proves
the sheaf condition from locality of this definition. No gluing or global
nonemptiness is supplied as input. On each open contained in a chart,
translation between coordinates is constant, so local constancy in another
chart implies local constancy in the selected chart. This gives genuine
local trivializations with both inverses and the original restrictions.
-/

noncomputable section
open CategoryTheory TopologicalSpace Opposite
namespace AAT.AG.VisibleCycleReflection.AffineAtlas
universe u
variable {X I M : Type u} [TopologicalSpace X] [AddCommGroup M]
variable (A : AffineAtlas X I M)

/-- Coordinates of a dependent fiber function on an open contained in one chart. -/
def coordinates {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (f : ∀ x : U, A.Fiber x.1) : U → M :=
  fun x => A.coordinate x.1 i (hU x.2) (f x)

/-- The affine coordinate equation for dependent functions in two containing charts. -/
theorem coordinates_change {U : Opens X} (i j : I)
    (hi : U ≤ A.patch i) (hj : U ≤ A.patch j) (f : ∀ x : U, A.Fiber x.1) (x : U) :
    A.coordinates i hi f x = A.transition i j + A.coordinates j hj f x :=
  A.coordinate_change x.1 i j (hi x.2) (hj x.2) (f x)

/-- Coordinate-local constancy before taking its local closure. -/
def statePrelocal : TopCat.PrelocalPredicate (X := TopCat.of X) (fun x => A.Fiber x) where
  pred {U} f := ∃ i, ∃ hU : U ≤ A.patch i, IsLocallyConstant (A.coordinates i hU f)
  res {U V} k f hf := by
    obtain ⟨i,hi,hf⟩ := hf
    refine ⟨i,le_trans k.le hi,?_⟩
    exact hf.comp_continuous (Opens.isOpenEmbedding_of_le k.le).continuous

/-- The local closure of coordinate-local constancy is an actual local predicate. -/
def stateLocal : TopCat.LocalPredicate (X := TopCat.of X) (fun x => A.Fiber x) :=
  A.statePrelocal.sheafify

/-- Public neighborhood description of the locally constant affine-state predicate. -/
theorem stateLocal_pred {U : Opens X} (f : ∀ x : U, A.Fiber x.1) :
    A.stateLocal.pred f ↔ ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (k : V ⟶ U),
      ∃ i, ∃ hV : V ≤ A.patch i,
        IsLocallyConstant (A.coordinates i hV (fun y => f ⟨y.1,k.le y.2⟩)) := Iff.rfl

/-- The actual type-valued affine state sheaf on the geometric space. -/
def stateSheaf : TopCat.Sheaf (Type u) (TopCat.of X) :=
  TopCat.subsheafToTypes A.stateLocal

/-- Affine sections on an arbitrary open, retaining their fiber values. -/
abbrev StateSection (U : Opens X) :=
  {f : ∀ x : U, A.Fiber x.1 // A.stateLocal.pred f}

/-- The state sheaf's objects are precisely the locally constant affine sections. -/
theorem stateSheaf_obj (U : Opens X) :
    A.stateSheaf.presheaf.obj (op U) = A.StateSection U := rfl

/-- The affine presheaf satisfies the sheaf condition, with no supplied gluing field. -/
theorem stateSheaf_isSheaf : A.stateSheaf.presheaf.IsSheaf :=
  A.stateSheaf.cond

/-- Restriction of affine states is restriction of their actual fiber functions. -/
def restrict {U V : Opens X} (h : V ≤ U) (s : A.StateSection U) : A.StateSection V :=
  ⟨fun x => s.1 ⟨x.1,h x.2⟩, A.stateLocal.res (homOfLE h) s.1 s.2⟩

/-- Public fiber value of the restriction. -/
@[simp] theorem restrict_value {U V : Opens X} (h : V ≤ U)
    (s : A.StateSection U) (x : V) :
    (A.restrict h s).1 x = s.1 ⟨x.1,h x.2⟩ := rfl

/-- The geometric sheaf uses the same restriction constructor. -/
theorem stateSheaf_map {U V : Opens X} (h : V ≤ U) (s : A.StateSection U) :
    A.stateSheaf.presheaf.map (homOfLE h).op s = A.restrict h s := rfl

/-- Equal original open supports give the same state sections, with explicit transport. -/
def sectionEquivOfEq {U V : Opens X} (h : U = V) : A.StateSection U ≃ A.StateSection V :=
  h ▸ Equiv.refl (A.StateSection U)

/-- Support transport retains every actual affine fiber value. -/
theorem sectionEquivOfEq_value {U V : Opens X} (h : U = V) (s : A.StateSection U) (x : U) :
    (A.sectionEquivOfEq h s).1 ⟨x.1,h ▸ x.2⟩ = s.1 x := by
  subst V
  rfl

/-- Support transport commutes with restriction of the same affine sections. -/
theorem sectionEquivOfEq_restrict {U V U' V' : Opens X}
    (hU : U = U') (hV : V = V') (h : V ≤ U) (s : A.StateSection U) :
    A.sectionEquivOfEq hV (A.restrict h s) =
      A.restrict (hU ▸ hV ▸ h) (A.sectionEquivOfEq hU s) := by
  subst U'
  subst V'
  rfl

/-- Locally constant affine states have locally constant coordinates in any containing chart. -/
theorem coordinates_locallyConstant {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (s : A.StateSection U) : IsLocallyConstant (A.coordinates i hU s.1) := by
  letI : TopologicalSpace M := ⊥
  letI : DiscreteTopology M := ⟨rfl⟩
  apply (IsLocallyConstant.iff_continuous _).2
  apply continuous_iff_continuousAt.2
  intro x
  obtain ⟨V,hx,k,j,hj,hjlc⟩ := (A.stateLocal_pred s.1).mp s.2 x
  have hi : V ≤ A.patch i := le_trans k.le hU
  have hlc : IsLocallyConstant (A.coordinates i hi (fun y => s.1 ⟨y.1,k.le y.2⟩)) := by
    convert hjlc.comp (fun m => A.transition i j + m) using 1
    funext y
    exact A.coordinates_change i j hi hj (fun y => s.1 ⟨y.1,k.le y.2⟩) y
  have hc := hlc.continuous.continuousAt (x := (⟨x.1,hx⟩ : V))
  change ContinuousAt ((A.coordinates i hU s.1) ∘ Set.inclusion k.le) ⟨x.1,hx⟩ at hc
  exact (Opens.isOpenEmbedding_of_le k.le).continuousAt_iff.mp hc

/-- Construct a locally constant affine section from a chart coefficient section. -/
def sectionFromCoordinates {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (g : LocallyConstant U M) : A.StateSection U :=
  ⟨fun x => A.fiberFromCoordinate x.1 i (hU x.2) (g x), by
    apply TopCat.PrelocalPredicate.sheafifyOf
    refine ⟨i,hU,?_⟩
    convert g.isLocallyConstant using 1
    funext x
    rw [coordinates,coordinate_fiberFromCoordinate,A.self,zero_add]
    rfl⟩

/-- Public fiber formula for sections constructed from chart coordinates. -/
@[simp] theorem sectionFromCoordinates_value {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (g : LocallyConstant U M) (x : U) :
    (A.sectionFromCoordinates i hU g).1 x = A.fiberFromCoordinate x.1 i (hU x.2) (g x) := rfl

/-- Every containing chart locally trivializes the state sheaf into the primitive coefficient sheaf. -/
def localTrivialization {U : Opens X} (i : I) (hU : U ≤ A.patch i) :
    A.StateSection U ≃ LocallyConstant U M where
  toFun s := ⟨A.coordinates i hU s.1,A.coordinates_locallyConstant i hU s⟩
  invFun := A.sectionFromCoordinates i hU
  left_inv s := by
    apply Subtype.ext
    funext x
    apply A.fiber_ext x.1 i (hU x.2)
    rw [sectionFromCoordinates_value,coordinate_fiberFromCoordinate,A.self,zero_add]
    rfl
  right_inv g := by
    apply LocallyConstant.ext
    intro x
    change A.coordinate x.1 i (hU x.2) ((A.sectionFromCoordinates i hU g).1 x) = g x
    rw [sectionFromCoordinates_value,coordinate_fiberFromCoordinate,A.self,zero_add]

/-- Public chart value of a locally trivialized actual state. -/
@[simp] theorem localTrivialization_apply {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (s : A.StateSection U) (x : U) :
    A.localTrivialization i hU s x = A.coordinate x.1 i (hU x.2) (s.1 x) := rfl

/-- Public inverse of local trivialization. -/
@[simp] theorem localTrivialization_symm {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (g : LocallyConstant U M) :
    (A.localTrivialization i hU).symm g = A.sectionFromCoordinates i hU g := rfl

/-- Original affine transitions relate the local trivializations on every overlap. -/
theorem localTrivialization_change {U : Opens X} (i j : I)
    (hi : U ≤ A.patch i) (hj : U ≤ A.patch j) (s : A.StateSection U) (x : U) :
    A.localTrivialization i hi s x =
      A.transition i j + A.localTrivialization j hj s x :=
  A.coordinate_change x.1 i j (hi x.2) (hj x.2) (s.1 x)

/-- Local trivializations commute with the original open-set restrictions. -/
theorem localTrivialization_restrict {U V : Opens X} (i : I) (hU : U ≤ A.patch i)
    (h : V ≤ U) (s : A.StateSection U) :
    A.localTrivialization i (le_trans h hU) (A.restrict h s) =
      LocallyConstant.comap
        ⟨fun x : V => (⟨x.1,h x.2⟩ : U),(Opens.isOpenEmbedding_of_le h).continuous⟩
        (A.localTrivialization i hU s) := by
  rfl

/-- The coefficient sheaf acts by pointwise primitive translation on affine states. -/
def translateSection {U : Opens X} (g : LocallyConstant U M) (s : A.StateSection U) :
    A.StateSection U :=
  ⟨fun x => A.translateFiber x.1 (g x) (s.1 x), by
    apply (A.stateLocal_pred _).mpr
    intro x
    obtain ⟨V,hx,k,j,hj,hlc⟩ := (A.stateLocal_pred s.1).mp s.2 x
    refine ⟨V,hx,k,j,hj,?_⟩
    have hg := g.isLocallyConstant.comp_continuous
      (Opens.isOpenEmbedding_of_le k.le).continuous
    simpa only [coordinates,coordinate_translateFiber,Function.comp_apply] using
      hlc.comp₂ hg (fun a b => a+b)⟩

/-- Public fiber value of the coefficient action. -/
@[simp] theorem translateSection_value {U : Opens X} (g : LocallyConstant U M)
    (s : A.StateSection U) (x : U) :
    (A.translateSection g s).1 x = A.translateFiber x.1 (g x) (s.1 x) := rfl

/-- Local trivialization intertwines the actual action and coefficient addition. -/
theorem localTrivialization_translate {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (g : LocallyConstant U M) (s : A.StateSection U) :
    A.localTrivialization i hU (A.translateSection g s) = A.localTrivialization i hU s + g := by
  apply LocallyConstant.ext
  intro x
  rw [localTrivialization_apply,translateSection_value,coordinate_translateFiber]
  rfl

/-- The zero coefficient acts as the identity on every open. -/
@[simp] theorem translateSection_zero {U : Opens X} (s : A.StateSection U) :
    A.translateSection (0 : LocallyConstant U M) s = s := by
  apply Subtype.ext
  funext x
  rw [translateSection_value]
  exact A.translateFiber_zero x.1 (s.1 x)

/-- Composition of translations is coefficient addition on every open. -/
theorem translateSection_add {U : Opens X} (g h : LocallyConstant U M) (s : A.StateSection U) :
    A.translateSection (g+h) s = A.translateSection g (A.translateSection h s) := by
  apply Subtype.ext
  funext x
  rw [translateSection_value,translateSection_value,translateSection_value]
  exact A.translateFiber_add x.1 (g x) (h x) (s.1 x)

/-- The actual coefficient translation is a Mathlib additive group action. -/
instance sectionAddAction (U : Opens X) : AddAction (LocallyConstant U M) (A.StateSection U) where
  vadd := A.translateSection
  zero_vadd := A.translateSection_zero
  add_vadd := A.translateSection_add

/-- The standard additive action uses the specified primitive translation. -/
theorem section_vadd {U : Opens X} (g : LocallyConstant U M) (s : A.StateSection U) :
    g +ᵥ s = A.translateSection g s := rfl

/-- In a chart the coefficient sheaf acts freely and transitively on actual state sections. -/
theorem existsUnique_translateSection {U : Opens X} (i : I) (hU : U ≤ A.patch i)
    (s t : A.StateSection U) :
    ∃! g : LocallyConstant U M, A.translateSection g s = t := by
  refine ⟨A.localTrivialization i hU t - A.localTrivialization i hU s, ?_, ?_⟩
  · apply (A.localTrivialization i hU).injective
    rw [localTrivialization_translate]
    abel
  · intro g hg
    have h := congrArg (A.localTrivialization i hU) hg
    rw [localTrivialization_translate] at h
    exact eq_sub_of_add_eq' h

/-- The coefficient action commutes with the original restriction maps. -/
theorem translateSection_restrict {U V : Opens X} (h : V ≤ U) (g : LocallyConstant U M)
    (s : A.StateSection U) :
    A.restrict h (A.translateSection g s) =
      A.translateSection
        (LocallyConstant.comap
          ⟨Set.inclusion h,(Opens.isOpenEmbedding_of_le h).continuous⟩ g) (A.restrict h s) := by
  apply Subtype.ext
  funext x
  rfl

end AAT.AG.VisibleCycleReflection.AffineAtlas
#assert_standard_axioms_only AAT.AG.VisibleCycleReflection
