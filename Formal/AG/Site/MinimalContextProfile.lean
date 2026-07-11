import Formal.AG.Site.ContextCategory
import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Minimal context finite-meet profile

This module gives the theorem-grade Part II proposition 4.2 route.  A selected
minimal context is represented extensionally by readable support, axis, and
observable sets over fixed carrier types.  Readable homs are componentwise
inclusions, with the observable component reversed because observable
restriction is contravariant.

Implementation notes:

- `Set` fields make mutual readable refinement coincide with extensional
  equality; this is the normalized presentation of the readable-identity
  quotient required by proposition 4.2.
- The meet and top objects are constructed componentwise.  They induce
  Mathlib `SemilatticeInf` and `OrderTop` instances, hence finite limits in the
  associated thin category.
- The existing `ArchitectureContext` remains the general carrier.  The
  comparison below maps each selected profile and readable hom into that API,
  rather than changing the legacy context representation.
- The rejected alternative was to truncate arbitrary `ContextMorphism`
  existence to a `Prop`; that makes homs proof-irrelevant without proving
  uniqueness of the selected readable morphisms.
-/

namespace AAT.AG
namespace Site

open CategoryTheory
open CategoryTheory.Limits

universe u w

/--
II.命題4.2: an extensional selected minimal context over fixed axis and
observable carriers.

The support premise is the proposition's requirement that a context read only
Atoms of the selected architecture object.  No finite-meet or categorical law
is stored in this data.
-/
structure MinimalContextProfile {U : AtomCarrier.{u}} (A : ArchitectureObject U)
    (Axis Observable : Type u) where
  support : Set U.Atom
  support_le_object : support ⊆ { atom | A.configuration.family.mem atom }
  axis : Set Axis
  observable : Set Observable

namespace MinimalContextProfile

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {Axis Observable : Type u}

/--
II.命題4.2: selected readability is covariant on support and axes and
contravariant on observables.
-/
instance : LE (MinimalContextProfile A Axis Observable) where
  le W V := W.support ⊆ V.support ∧ W.axis ⊆ V.axis ∧ V.observable ⊆ W.observable

/-- II.命題4.2 API lemma: profiles are equal when their three readings agree. -/
@[ext]
theorem ext {W V : MinimalContextProfile A Axis Observable}
    (hs : W.support = V.support) (ha : W.axis = V.axis)
    (ho : W.observable = V.observable) : W = V := by
  cases W
  cases V
  cases hs
  cases ha
  cases ho
  rfl

/--
II.命題4.2: readable identity has already been quotiented by extensional
equality, producing an antisymmetric selected context order.
-/
instance : PartialOrder (MinimalContextProfile A Axis Observable) where
  le_refl W := ⟨Set.Subset.rfl, Set.Subset.rfl, Set.Subset.rfl⟩
  le_trans _W _V _X hWV hVX :=
    ⟨Set.Subset.trans hWV.1 hVX.1,
      Set.Subset.trans hWV.2.1 hVX.2.1,
      Set.Subset.trans hVX.2.2 hWV.2.2⟩
  le_antisymm W V hWV hVW := by
    apply ext
    · exact Set.Subset.antisymm hWV.1 hVW.1
    · exact Set.Subset.antisymm hWV.2.1 hVW.2.1
    · exact Set.Subset.antisymm hVW.2.2 hWV.2.2

/--
II.命題4.2: mutual readable refinement is exactly equality in the
extensional quotient presentation.
-/
theorem readableEquivalence_iff_eq
    (W V : MinimalContextProfile A Axis Observable) :
    (W ≤ V ∧ V ≤ W) ↔ W = V := by
  constructor
  · exact fun h => le_antisymm h.1 h.2
  · intro h
    cases h
    exact ⟨le_rfl, le_rfl⟩

/--
II.命題4.2: componentwise meet of selected minimal contexts.

Observable readings use union because their readable order is contravariant.
-/
def inf (W V : MinimalContextProfile A Axis Observable) :
    MinimalContextProfile A Axis Observable where
  support := W.support ∩ V.support
  support_le_object := fun {_atom} h => W.support_le_object h.1
  axis := W.axis ∩ V.axis
  observable := W.observable ∪ V.observable

/-- II.命題4.2 API lemma: support of the meet is intersection. -/
theorem inf_support (W V : MinimalContextProfile A Axis Observable) :
    (inf W V).support = W.support ∩ V.support :=
  rfl

/-- II.命題4.2 API lemma: axes of the meet are intersection. -/
theorem inf_axis (W V : MinimalContextProfile A Axis Observable) :
    (inf W V).axis = W.axis ∩ V.axis :=
  rfl

/-- II.命題4.2 API lemma: observables of the meet are union. -/
theorem inf_observable (W V : MinimalContextProfile A Axis Observable) :
    (inf W V).observable = W.observable ∪ V.observable :=
  rfl

/--
II.命題4.2: the constructed componentwise meet is the Mathlib infimum.
-/
instance : SemilatticeInf (MinimalContextProfile A Axis Observable) where
  inf := inf
  inf_le_left W V := ⟨Set.inter_subset_left, Set.inter_subset_left, Set.subset_union_left⟩
  inf_le_right W V := ⟨Set.inter_subset_right, Set.inter_subset_right, Set.subset_union_right⟩
  le_inf X W V hXW hXV :=
    ⟨fun _atom h => ⟨hXW.1 h, hXV.1 h⟩,
      fun _axis h => ⟨hXW.2.1 h, hXV.2.1 h⟩,
      fun _observable h => by
        rcases h with h | h
        · exact hXW.2.2 h
        · exact hXV.2.2 h⟩

/--
II.命題4.2: the nullary meet reads the full object support, all selected
axes, and no required observable.
-/
def top : MinimalContextProfile A Axis Observable where
  support := { atom | A.configuration.family.mem atom }
  support_le_object := Set.Subset.rfl
  axis := Set.univ
  observable := ∅

/-- II.命題4.2 API lemma: top support is the selected object family. -/
theorem top_support :
    (top : MinimalContextProfile A Axis Observable).support =
      { atom | A.configuration.family.mem atom } :=
  rfl

/-- II.命題4.2 API lemma: top contains every selected axis. -/
theorem top_axis :
    (top : MinimalContextProfile A Axis Observable).axis = Set.univ :=
  rfl

/-- II.命題4.2 API lemma: top requires no observable. -/
theorem top_observable :
    (top : MinimalContextProfile A Axis Observable).observable = ∅ :=
  rfl

/-- II.命題4.2: the constructed nullary meet is the Mathlib top object. -/
instance : OrderTop (MinimalContextProfile A Axis Observable) where
  top := top
  le_top W := ⟨W.support_le_object, Set.subset_univ _, Set.empty_subset _⟩

/--
II.命題4.2: a presentation-level minimal context before readable-identity
quotienting.  The three index types and reading maps retain presentation data;
different presentations may have the same extensional readings.
-/
structure RawMinimalContextProfile {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) (Axis Observable : Type u) where
  SupportIndex : Type u
  supportRead : SupportIndex -> U.Atom
  supportRead_objectFamily : ∀ support, A.configuration.family.mem (supportRead support)
  AxisIndex : Type u
  axisRead : AxisIndex -> Axis
  ObservableIndex : Type u
  observableRead : ObservableIndex -> Observable

namespace RawMinimalContextProfile

/-- Extensional reading of a presentation-level minimal context. -/
def normalize (W : RawMinimalContextProfile A Axis Observable) :
    MinimalContextProfile A Axis Observable where
  support := Set.range W.supportRead
  support_le_object := by
    rintro _atom ⟨support, rfl⟩
    exact W.supportRead_objectFamily support
  axis := Set.range W.axisRead
  observable := Set.range W.observableRead

/-- Presentation-level readability is a preorder, not a partial order. -/
instance : Preorder (RawMinimalContextProfile A Axis Observable) where
  le W V := normalize W ≤ normalize V
  le_refl W := _root_.le_rfl
  le_trans W V X hWV hVX := by
    change normalize W ≤ normalize V at hWV
    change normalize V ≤ normalize X at hVX
    exact _root_.le_trans hWV hVX

/-- II.命題4.2: presentation-level homs form a thin preorder category. -/
theorem hom_subsingleton (W V : RawMinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V) :=
  inferInstance

/-- Componentwise finite meet before quotienting. -/
def inf (W V : RawMinimalContextProfile A Axis Observable) :
    RawMinimalContextProfile A Axis Observable where
  SupportIndex :=
    { pair : W.SupportIndex × V.SupportIndex //
      W.supportRead pair.1 = V.supportRead pair.2 }
  supportRead := fun pair => W.supportRead pair.1.1
  supportRead_objectFamily := fun pair => W.supportRead_objectFamily pair.1.1
  AxisIndex :=
    { pair : W.AxisIndex × V.AxisIndex //
      W.axisRead pair.1 = V.axisRead pair.2 }
  axisRead := fun pair => W.axisRead pair.1.1
  ObservableIndex := W.ObservableIndex ⊕ V.ObservableIndex
  observableRead := Sum.elim W.observableRead V.observableRead

/-- Normalization sends the presentation-level meet to the extensional meet. -/
theorem normalize_inf (W V : RawMinimalContextProfile A Axis Observable) :
    normalize (inf W V) = normalize W ⊓ normalize V := by
  apply MinimalContextProfile.ext
  · ext atom
    constructor
    · rintro ⟨pair, rfl⟩
      exact ⟨⟨pair.1.1, rfl⟩, ⟨pair.1.2, pair.2.symm⟩⟩
    · rintro ⟨⟨supportW, hW⟩, ⟨supportV, hV⟩⟩
      exact ⟨⟨(supportW, supportV), hW.trans hV.symm⟩, hW⟩
  · ext axis
    constructor
    · rintro ⟨pair, rfl⟩
      exact ⟨⟨pair.1.1, rfl⟩, ⟨pair.1.2, pair.2.symm⟩⟩
    · rintro ⟨⟨axisW, hW⟩, ⟨axisV, hV⟩⟩
      exact ⟨⟨(axisW, axisV), hW.trans hV.symm⟩, hW⟩
  · ext observable
    constructor
    · rintro ⟨index, rfl⟩
      cases index with
      | inl index => exact Or.inl ⟨index, rfl⟩
      | inr index => exact Or.inr ⟨index, rfl⟩
    · rintro (⟨index, h⟩ | ⟨index, h⟩)
      · exact ⟨Sum.inl index, h⟩
      · exact ⟨Sum.inr index, h⟩

/-- Presentation-level meet is below its left input. -/
theorem inf_le_left (W V : RawMinimalContextProfile A Axis Observable) :
    inf W V ≤ W := by
  change normalize (inf W V) ≤ normalize W
  rw [normalize_inf]
  exact _root_.inf_le_left

/-- Presentation-level meet is below its right input. -/
theorem inf_le_right (W V : RawMinimalContextProfile A Axis Observable) :
    inf W V ≤ V := by
  change normalize (inf W V) ≤ normalize V
  rw [normalize_inf]
  exact _root_.inf_le_right

/-- Presentation-level meet has the expected greatest-lower-bound law. -/
theorem le_inf {X W V : RawMinimalContextProfile A Axis Observable}
    (hXW : X ≤ W) (hXV : X ≤ V) : X ≤ inf W V := by
  change normalize X ≤ normalize (inf W V)
  rw [normalize_inf]
  exact _root_.le_inf hXW hXV

/-- Nullary presentation-level meet. -/
def top : RawMinimalContextProfile A Axis Observable where
  SupportIndex := { atom // A.configuration.family.mem atom }
  supportRead := Subtype.val
  supportRead_objectFamily := Subtype.property
  AxisIndex := Axis
  axisRead := id
  ObservableIndex := ULift.{u} Empty
  observableRead := fun index => nomatch index.down

/-- Normalization sends the presentation-level top to the extensional top. -/
theorem normalize_top :
    normalize (top : RawMinimalContextProfile A Axis Observable) = ⊤ := by
  apply MinimalContextProfile.ext
  · change Set.range (fun support : { atom // A.configuration.family.mem atom } =>
      support.1) = { atom | A.configuration.family.mem atom }
    ext atom
    exact ⟨fun ⟨support, h⟩ => h ▸ support.2,
      fun h => ⟨⟨atom, h⟩, rfl⟩⟩
  · change Set.range (fun axis : Axis => axis) = Set.univ
    ext axis
    exact ⟨fun _ => trivial, fun _ => ⟨axis, rfl⟩⟩
  · change Set.range (fun index : ULift.{u} Empty => nomatch index.down) = ∅
    ext observable
    constructor
    · rintro ⟨index, _⟩
      exact Empty.elim index.down
    · exact False.elim

/-- Every presentation-level context is below the nullary meet. -/
theorem le_top (W : RawMinimalContextProfile A Axis Observable) : W ≤ top := by
  change normalize W ≤ normalize top
  rw [normalize_top]
  exact _root_.le_top

/-- Binary fan whose apex is the presentation-level meet. -/
def infBinaryFan (W V : RawMinimalContextProfile A Axis Observable) :
    BinaryFan W V :=
  BinaryFan.mk (homOfLE (inf_le_left W V)) (homOfLE (inf_le_right W V))

/-- The presentation-level meet is a categorical binary product. -/
def infBinaryFanIsLimit (W V : RawMinimalContextProfile A Axis Observable) :
    IsLimit (infBinaryFan W V) :=
  BinaryFan.isLimitMk
    (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

/-- Mutual readability is the equivalence relation removed by quotienting. -/
def readableSetoid : Setoid (RawMinimalContextProfile A Axis Observable) where
  r W V := W ≤ V ∧ V ≤ W
  iseqv := {
    refl := fun W => ⟨_root_.le_rfl, _root_.le_rfl⟩
    symm := fun h => ⟨h.2, h.1⟩
    trans := by
      intro W V X hWV hVX
      exact ⟨_root_.le_trans hWV.1 hVX.1, _root_.le_trans hVX.2 hWV.2⟩ }

/-- Quotient of presentations by mutual readability. -/
abbrev QuotientProfile :=
  Quotient (readableSetoid (A := A) (Axis := Axis) (Observable := Observable))

/-- Mutual readability is exactly equality of extensional normalizations. -/
theorem readableEquivalent_iff_normalize_eq
    (W V : RawMinimalContextProfile A Axis Observable) :
    readableSetoid (A := A) (Axis := Axis) (Observable := Observable) W V ↔
      normalize W = normalize V := by
  simp only [readableSetoid]
  constructor
  · intro h
    exact le_antisymm h.1 h.2
  · intro h
    change normalize W = normalize V at h
    constructor
    · change normalize W ≤ normalize V
      exact le_of_eq h
    · change normalize V ≤ normalize W
      exact le_of_eq h.symm

/-- Normalize a readable-equivalence quotient. -/
def quotientNormalize : QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) ->
    MinimalContextProfile A Axis Observable :=
  Quotient.lift normalize (fun W V h =>
    (readableEquivalent_iff_normalize_eq W V).mp h)

/-- Canonical presentation of an extensional profile. -/
def ofNormalized (W : MinimalContextProfile A Axis Observable) :
    RawMinimalContextProfile A Axis Observable where
  SupportIndex := W.support
  supportRead := Subtype.val
  supportRead_objectFamily := fun support => W.support_le_object support.2
  AxisIndex := W.axis
  axisRead := Subtype.val
  ObservableIndex := W.observable
  observableRead := Subtype.val

/-- Canonical presentation normalizes back to the original profile. -/
theorem normalize_ofNormalized (W : MinimalContextProfile A Axis Observable) :
    normalize (ofNormalized W) = W := by
  apply MinimalContextProfile.ext
  · ext atom
    exact ⟨fun ⟨support, h⟩ => h ▸ support.2, fun h => ⟨⟨atom, h⟩, rfl⟩⟩
  · ext axis
    exact ⟨fun ⟨index, h⟩ => h ▸ index.2, fun h => ⟨⟨axis, h⟩, rfl⟩⟩
  · ext observable
    exact ⟨fun ⟨index, h⟩ => h ▸ index.2,
      fun h => ⟨⟨observable, h⟩, rfl⟩⟩

/--
Finite limit cone in the raw preorder category.  Its apex uses the canonical
presentation of the finite infimum of the diagram's extensional readings;
the cone and universal arrow live in the raw preorder itself.
-/
@[simps]
def finiteLimitCone {J : Type w} [SmallCategory J] [FinCategory J]
    (F : J ⥤ RawMinimalContextProfile A Axis Observable) : LimitCone F where
  cone := {
    pt := ofNormalized (Finset.univ.inf fun j => normalize (F.obj j))
    π := { app := fun j => homOfLE (by
      change normalize (ofNormalized (Finset.univ.inf fun j => normalize (F.obj j))) ≤
        normalize (F.obj j)
      rw [normalize_ofNormalized]
      exact Finset.inf_le (Fintype.complete j)) } }
  isLimit := { lift := fun s => homOfLE (by
    change normalize s.pt ≤
      normalize (ofNormalized (Finset.univ.inf fun j => normalize (F.obj j)))
    rw [normalize_ofNormalized]
    exact Finset.le_inf fun j _ => (s.π.app j).down.down) }

/-- The presentation-level finite-meet preorder category has all finite limits. -/
instance (priority := 90) :
    HasFiniteLimits (RawMinimalContextProfile A Axis Observable) := ⟨by
  intro J _ _
  exact { has_limit := fun F => HasLimit.mk (finiteLimitCone F) }⟩

/-- Named theorem surface for finite limits before quotienting. -/
theorem hasFiniteLimits :
    HasFiniteLimits (RawMinimalContextProfile A Axis Observable) :=
  inferInstance

/-- Put an extensional profile into the readable-equivalence quotient. -/
def quotientOfNormalized (W : MinimalContextProfile A Axis Observable) :
    QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) :=
  Quotient.mk _ (ofNormalized W)

/-- The readable-equivalence quotient is equivalent to the extensional normal form. -/
def quotientEquiv :
    QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) ≃
      MinimalContextProfile A Axis Observable where
  toFun := quotientNormalize
  invFun := quotientOfNormalized
  left_inv q := by
    refine Quotient.inductionOn q ?_
    intro W
    apply Quotient.sound
    apply (readableEquivalent_iff_normalize_eq (ofNormalized (normalize W)) W).mpr
    rw [normalize_ofNormalized]
  right_inv W := normalize_ofNormalized W

/-- Presentation-level meet descends to the readable quotient. -/
def quotientInf :
    QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) ->
      QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) ->
        QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) :=
  Quotient.lift₂ (fun W V => Quotient.mk _ (inf W V)) (by
    intro W V W' V' hW hV
    apply Quotient.sound
    apply (readableEquivalent_iff_normalize_eq (inf W V) (inf W' V')).mpr
    rw [normalize_inf, normalize_inf,
      (readableEquivalent_iff_normalize_eq W W').mp hW,
      (readableEquivalent_iff_normalize_eq V V').mp hV])

/-- Quotient normalization preserves the descended meet. -/
theorem quotientNormalize_inf
    (W V : QuotientProfile (A := A) (Axis := Axis) (Observable := Observable)) :
    quotientNormalize (quotientInf W V) = quotientNormalize W ⊓ quotientNormalize V := by
  refine Quotient.inductionOn₂ W V ?_
  intro rawW rawV
  exact normalize_inf rawW rawV

/-- The descended meet equips the readable quotient with a meet semilattice. -/
instance : SemilatticeInf
    (QuotientProfile (A := A) (Axis := Axis) (Observable := Observable)) where
  le W V := quotientNormalize W ≤ quotientNormalize V
  le_refl W := _root_.le_rfl
  le_trans _W _V _X hWV hVX := _root_.le_trans hWV hVX
  le_antisymm W V hWV hVW :=
    quotientEquiv.injective (le_antisymm hWV hVW)
  inf := quotientInf
  inf_le_left W V := by
    rw [quotientNormalize_inf]
    exact _root_.inf_le_left
  inf_le_right W V := by
    rw [quotientNormalize_inf]
    exact _root_.inf_le_right
  le_inf X W V hXW hXV := by
    rw [quotientNormalize_inf]
    exact _root_.le_inf hXW hXV

/-- Order equivalence between the quotient and extensional normal form. -/
def quotientOrderIso :
    QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) ≃o
      MinimalContextProfile A Axis Observable where
  toEquiv := quotientEquiv
  map_rel_iff' := Iff.rfl

/-- Presentation-level top descends to the readable quotient. -/
def quotientTop :
    QuotientProfile (A := A) (Axis := Axis) (Observable := Observable) :=
  Quotient.mk _ top

/-- Quotient normalization preserves top. -/
theorem quotientNormalize_top : quotientNormalize
    (quotientTop : QuotientProfile (A := A) (Axis := Axis) (Observable := Observable)) = ⊤ :=
  normalize_top

/-- The readable quotient has the descended nullary meet. -/
instance : OrderTop
    (QuotientProfile (A := A) (Axis := Axis) (Observable := Observable)) where
  top := quotientTop
  le_top W := by
    change quotientNormalize W ≤ quotientNormalize quotientTop
    rw [quotientNormalize_top]
    exact _root_.le_top

/-- The readable quotient is itself a finite-limit poset category. -/
theorem quotient_hasFiniteLimits :
    HasFiniteLimits
      (QuotientProfile (A := A) (Axis := Axis) (Observable := Observable)) :=
  inferInstance

end RawMinimalContextProfile

/--
II.命題4.2: an actual selected readable morphism is a triple of maps between
the selected reading subtypes.  Each map preserves its underlying support,
axis, or observable value.

Unlike the rejected equality-subtype encoding, no field states that the whole
morphism is equal to a preselected canonical morphism.  Thinness is proved
below from value preservation and subtype extensionality.
-/
structure ReadableContextHom
    (W V : MinimalContextProfile A Axis Observable) where
  supportMap : W.support -> V.support
  supportMap_val : ∀ support, (supportMap support).1 = support.1
  axisMap : W.axis -> V.axis
  axisMap_val : ∀ axis, (axisMap axis).1 = axis.1
  observableRestrict : V.observable -> W.observable
  observableRestrict_val :
    ∀ observable, (observableRestrict observable).1 = observable.1

/-- II.命題4.2: construct an actual selected readable morphism from order. -/
def readableContextHomOfLE {W V : MinimalContextProfile A Axis Observable}
    (h : W ≤ V) : ReadableContextHom W V where
  supportMap := fun support => ⟨support.1, h.1 support.2⟩
  supportMap_val := fun _ => rfl
  axisMap := fun axis => ⟨axis.1, h.2.1 axis.2⟩
  axisMap_val := fun _ => rfl
  observableRestrict := fun observable => ⟨observable.1, h.2.2 observable.2⟩
  observableRestrict_val := fun _ => rfl

/-- II.命題4.2: recover order from an actual selected readable morphism. -/
theorem leOfReadableContextHom
    {W V : MinimalContextProfile A Axis Observable}
    (f : ReadableContextHom W V) : W ≤ V := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom hAtom
    have h := (f.supportMap ⟨atom, hAtom⟩).2
    simpa [f.supportMap_val ⟨atom, hAtom⟩] using h
  · intro axis hAxis
    have h := (f.axisMap ⟨axis, hAxis⟩).2
    simpa [f.axisMap_val ⟨axis, hAxis⟩] using h
  · intro observable hObservable
    have h := (f.observableRestrict ⟨observable, hObservable⟩).2
    simpa [f.observableRestrict_val ⟨observable, hObservable⟩] using h

/--
II.命題4.2: actual selected readable morphisms are subsingleton as
function-valued data.  The proof derives equality of each map from preservation
of the underlying value; it does not read a morphism-equals-canonical field.
-/
theorem readableContextHom_subsingleton
    (W V : MinimalContextProfile A Axis Observable) :
    Subsingleton (ReadableContextHom W V) := by
  constructor
  intro f g
  cases f with
  | mk fs hfs fa hfa fo hfo =>
      cases g with
      | mk gs hgs ga hga go hgo =>
          have hs : fs = gs := by
            funext support
            apply Subtype.ext
            exact (hfs support).trans (hgs support).symm
          have ha : fa = ga := by
            funext axis
            apply Subtype.ext
            exact (hfa axis).trans (hga axis).symm
          have ho : fo = go := by
            funext observable
            apply Subtype.ext
            exact (hfo observable).trans (hgo observable).symm
          cases hs
          cases ha
          cases ho
          rfl

/--
II.命題4.2: Mathlib thin-category homs are exactly the actual selected
readable context morphisms.
-/
def homEquivReadableContextHom
    (W V : MinimalContextProfile A Axis Observable) :
    (W ⟶ V) ≃ ReadableContextHom W V where
  toFun f := readableContextHomOfLE f.le
  invFun f := homOfLE (leOfReadableContextHom f)
  left_inv f := Subsingleton.elim _ f
  right_inv f := (readableContextHom_subsingleton W V).elim _ f

/--
II.命題4.2 comparison map: read a selected profile through the existing
`ArchitectureContext` API.  Its carrier types are the selected reading
subtypes, so a selected readable hom supplies the actual legacy maps.
-/
def toArchitectureContext (W : MinimalContextProfile A Axis Observable) :
    ArchitectureContext A where
  minimal := {
    Support := W.support
    Axis := W.axis
    Observable := W.observable
    supportReads := fun support atom => support.1 = atom
    supportReads_objectFamily := fun {support _atom} h =>
      h ▸ W.support_le_object support.2
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := PUnit
  extension := PUnit.unit

/-- Extensionality helper for the legacy three-map context morphism. -/
theorem legacyContextMorphism_ext
    {source target : ArchitectureContext A}
    (f g : ContextMorphism source target)
    (hs : f.supportMap = g.supportMap)
    (ha : f.axisMap = g.axisMap)
    (ho : f.observableRestrict = g.observableRestrict) : f = g := by
  cases f
  cases g
  cases hs
  cases ha
  cases ho
  rfl

/--
II.命題4.2: convert an actual selected hom of the Mathlib thin category
to the existing context-morphism data.
-/
def homToContextMorphism {W V : MinimalContextProfile A Axis Observable}
    (f : W ⟶ V) : ContextMorphism W.toArchitectureContext V.toArchitectureContext :=
  let selected := homEquivReadableContextHom W V f
  { supportMap := selected.supportMap
    axisMap := selected.axisMap
    observableRestrict := selected.observableRestrict }

/--
II.命題4.2: every actual selected hom maps to a legacy restriction
morphism; the proof uses the order content of that hom.
-/
theorem homToContextMorphism_isRestriction
    {W V : MinimalContextProfile A Axis Observable} (f : W ⟶ V) :
    (homToContextMorphism f).IsRestriction :=
  by
    let selected := homEquivReadableContextHom W V f
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro support atom hReads
      change (selected.supportMap support).1 = atom
      exact (selected.supportMap_val support).trans hReads
    · intro _axis _hReads
      trivial
    · intro _observable _hReads
      trivial
    · intro support atom hReads
      change (selected.supportMap support).1 = atom at hReads
      exact hReads ▸ V.support_le_object (selected.supportMap support).2

/--
II.命題4.2 comparison theorem: the selected identity hom maps to the
existing identity context morphism.
-/
theorem homToContextMorphism_id
    (W : MinimalContextProfile A Axis Observable) :
    homToContextMorphism (𝟙 W) = identityContextMorphism W.toArchitectureContext :=
  by
    apply legacyContextMorphism_ext
    · funext support
      apply Subtype.ext
      exact (homEquivReadableContextHom W W (𝟙 W)).supportMap_val support
    · funext axis
      apply Subtype.ext
      exact (homEquivReadableContextHom W W (𝟙 W)).axisMap_val axis
    · funext observable
      apply Subtype.ext
      exact (homEquivReadableContextHom W W (𝟙 W)).observableRestrict_val observable

/--
II.命題4.2 comparison theorem: conversion of selected homs preserves
composition in the existing context-morphism API.
-/
theorem homToContextMorphism_comp
    {W V X : MinimalContextProfile A Axis Observable}
    (f : W ⟶ V) (g : V ⟶ X) :
    homToContextMorphism (f ≫ g) =
      contextMorphismComp (homToContextMorphism f) (homToContextMorphism g) :=
  by
    apply legacyContextMorphism_ext
    · funext support
      apply Subtype.ext
      exact (homEquivReadableContextHom W X (f ≫ g)).supportMap_val support
    · funext axis
      apply Subtype.ext
      exact (homEquivReadableContextHom W X (f ≫ g)).axisMap_val axis
    · funext observable
      apply Subtype.ext
      exact (homEquivReadableContextHom W X (f ≫ g)).observableRestrict_val observable

/--
II.命題4.2: actual selected homs are subsingleton in the Mathlib
preorder category.
-/
theorem hom_subsingleton (W V : MinimalContextProfile A Axis Observable) :
    Subsingleton (W ⟶ V) :=
  inferInstance

/--
II.命題4.2: the constructed top and binary meet give every finite limit
in the selected minimal-context category.
-/
theorem hasFiniteLimits :
    HasFiniteLimits (MinimalContextProfile A Axis Observable) :=
  inferInstance

/--
II.仮定4.3 / 命題4.2: the categorical pullback of two selected
readable morphisms is their constructed context meet.
-/
theorem pullback_eq_inf
    {base left right : MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    pullback hl hr = left ⊓ right :=
  CategoryTheory.Limits.CompleteLattice.pullback_eq_inf hl hr

/--
II.仮定4.3 / 命題4.2 comparison theorem: the categorical pullback
square remains commutative after conversion to the existing context-morphism
API.
-/
theorem pullback_contextMorphism_commutes
    {base left right : MinimalContextProfile A Axis Observable}
    (hl : left ⟶ base) (hr : right ⟶ base) :
    contextMorphismComp
        (homToContextMorphism (pullback.fst hl hr))
        (homToContextMorphism hl) =
      contextMorphismComp
        (homToContextMorphism (pullback.snd hl hr))
        (homToContextMorphism hr) :=
  rfl

/--
II.命題4.2: meet is independent of mutually readable representatives in
the extensional quotient presentation.
-/
theorem inf_eq_inf_of_mutual_readability
    {W W' V V' : MinimalContextProfile A Axis Observable}
    (hW : W ≤ W' ∧ W' ≤ W) (hV : V ≤ V' ∧ V' ≤ V) :
    W ⊓ V = W' ⊓ V' := by
  rw [(readableEquivalence_iff_eq W W').mp hW,
    (readableEquivalence_iff_eq V V').mp hV]

end MinimalContextProfile
end Site
end AAT.AG
