import Formal.AG.Site.Context

namespace AAT.AG
namespace Site

universe u

/-- II.定義4.1: the objects of `ArchCtx(A)` are architecture contexts over `A`. -/
abbrev ArchCtx {U : AtomCarrier.{u}} (A : ArchitectureObject U) :=
  ArchitectureContext A

/--
II.定義4.1 / 命題4.2: preorder-category data for the minimal context model.

The relation `le source target` reads "the source context is a local/refined
readable context of the target context". Without antisymmetry this is only the
preorder-category reading.
-/
structure ContextPreorderCategory {U : AtomCarrier.{u}} (A : ArchitectureObject U) where
  le : ArchCtx A -> ArchCtx A -> Prop
  refl : ∀ W : ArchCtx A, le W W
  trans : ∀ {W V X : ArchCtx A}, le W V -> le V X -> le W X
  readableMorphism :
    ∀ {source target : ArchCtx A}, le source target -> ContextMorphism source target
  readableMorphism_isRestriction :
    ∀ {source target : ArchCtx A} (h : le source target),
      (readableMorphism h).IsRestriction

namespace ContextPreorderCategory

/-- II.定義4.1: readable homs in the thin preorder-category reading. -/
def Hom {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (source target : ArchCtx A) : Prop :=
  C.le source target

/-- II.命題4.2: preorder homs are propositions, hence thin. -/
theorem hom_subsingleton {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (source target : ArchCtx A) :
    Subsingleton (C.Hom source target) :=
  inferInstance

/-- II.命題4.2: identity readable morphism in the preorder-category reading. -/
theorem id {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (W : ArchCtx A) :
    C.Hom W W :=
  C.refl W

/-- II.命題4.2: composition is transitivity of readable refinement. -/
theorem comp {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) {W V X : ArchCtx A}
    (f : C.Hom W V) (g : C.Hom V X) :
    C.Hom W X :=
  C.trans f g

/-- II.定義4.1: preorder homs expose the selected context morphism data. -/
def morphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) {source target : ArchCtx A}
    (h : C.Hom source target) : ContextMorphism source target :=
  C.readableMorphism h

/-- II.定義4.1: readable homs are restriction morphisms in the minimal model. -/
theorem morphism_isRestriction {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) {source target : ArchCtx A}
    (h : C.Hom source target) :
    (C.morphism h).IsRestriction :=
  C.readableMorphism_isRestriction h

end ContextPreorderCategory

/--
II.命題4.2: finite-meet structure on the minimal context preorder.

`meet W V` is the overlap context before a base object is fixed. Later cover
base-change packages read this same meet as `W x_base V`.
-/
structure ContextFiniteMeet {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) where
  meet : ArchCtx A -> ArchCtx A -> ArchCtx A
  meet_le_left : ∀ W V : ArchCtx A, C.le (meet W V) W
  meet_le_right : ∀ W V : ArchCtx A, C.le (meet W V) V
  le_meet :
    ∀ {X W V : ArchCtx A}, C.le X W -> C.le X V -> C.le X (meet W V)

/-- II.命題4.2: identity context morphism for the minimal context model. -/
def identityContextMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W : ArchCtx A) : ContextMorphism W W where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- II.命題4.2: composition of selected restriction context morphisms. -/
def contextMorphismComp {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W V X : ArchCtx A} (f : ContextMorphism W V) (g : ContextMorphism V X) :
    ContextMorphism W X where
  supportMap := g.supportMap ∘ f.supportMap
  axisMap := g.axisMap ∘ f.axisMap
  observableRestrict := f.observableRestrict ∘ g.observableRestrict

/-- II.命題4.2: composition preserves the selected restriction role. -/
theorem contextMorphismComp_isRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {W V X : ArchCtx A}
    {f : ContextMorphism W V} {g : ContextMorphism V X}
    (hf : f.IsRestriction) (hg : g.IsRestriction) :
    (contextMorphismComp f g).IsRestriction :=
  ⟨fun h => hg.1 (hf.1 h),
    fun h => hg.2.1 (hf.2.1 h),
    fun h => hf.2.2.1 (hg.2.2.1 h),
    fun h => X.supportReads_objectFamily h⟩

/-- II.命題4.2: componentwise product context used as a concrete meet. -/
def productContext {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W V : ArchCtx A) : ArchCtx A where
  minimal := {
    Support := W.Support × V.Support
    Axis := W.Axis × V.Axis
    Observable := W.Observable ⊕ V.Observable
    supportReads := fun support atom =>
      W.minimal.supportReads support.1 atom ∧ V.minimal.supportReads support.2 atom
    supportReads_objectFamily := fun h =>
      W.supportReads_objectFamily h.1
    axisReads := fun axis =>
      W.minimal.axisReads axis.1 ∧ V.minimal.axisReads axis.2
    observableReads := fun
      | Sum.inl observable => W.minimal.observableReads observable
      | Sum.inr observable => V.minimal.observableReads observable
  }
  Extension := W.Extension × V.Extension
  extension := (W.extension, V.extension)

/-- II.命題4.2: product context projection to the left component. -/
def productContextLeftMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W V : ArchCtx A) : ContextMorphism (productContext W V) W where
  supportMap := Prod.fst
  axisMap := Prod.fst
  observableRestrict := Sum.inl

/-- II.命題4.2: product context projection to the right component. -/
def productContextRightMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (W V : ArchCtx A) : ContextMorphism (productContext W V) V where
  supportMap := Prod.snd
  axisMap := Prod.snd
  observableRestrict := Sum.inr

/-- II.命題4.2: product context projections are selected restrictions. -/
theorem productContextLeft_isRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (W V : ArchCtx A) :
    (productContextLeftMorphism W V).IsRestriction :=
  ⟨fun h => h.1, fun h => h.1, fun h => h,
    fun h => W.supportReads_objectFamily h⟩

/-- II.命題4.2: product context projections are selected restrictions. -/
theorem productContextRight_isRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (W V : ArchCtx A) :
    (productContextRightMorphism W V).IsRestriction :=
  ⟨fun h => h.2, fun h => h.2, fun h => h,
    fun h => V.supportReads_objectFamily h⟩

/-- II.命題4.2: lift a pair of readable restrictions into the product context. -/
def productContextLiftMorphism {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {X W V : ArchCtx A} (f : ContextMorphism X W) (g : ContextMorphism X V) :
    ContextMorphism X (productContext W V) where
  supportMap := fun support => (f.supportMap support, g.supportMap support)
  axisMap := fun axis => (f.axisMap axis, g.axisMap axis)
  observableRestrict := fun
    | Sum.inl observable => f.observableRestrict observable
    | Sum.inr observable => g.observableRestrict observable

/-- II.命題4.2: product-context lifts preserve the selected restriction role. -/
theorem productContextLift_isRestriction {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {X W V : ArchCtx A}
    {f : ContextMorphism X W} {g : ContextMorphism X V}
    (hf : f.IsRestriction) (hg : g.IsRestriction) :
    (productContextLiftMorphism f g).IsRestriction :=
  ⟨fun h => ⟨hf.1 h, hg.1 h⟩,
    fun h => ⟨hf.2.1 h, hg.2.1 h⟩,
    fun {observable} h =>
      match observable with
      | Sum.inl _observable => hf.2.2.1 h
      | Sum.inr _observable => hg.2.2.1 h,
    fun h => (productContext W V).supportReads_objectFamily h⟩

/--
II.命題4.2: canonical preorder whose arrows are selected restriction
context morphisms.
-/
noncomputable def contextMorphismPreorderCategory {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) : ContextPreorderCategory A where
  le source target := ∃ f : ContextMorphism source target, f.IsRestriction
  refl W := ⟨identityContextMorphism W,
    ⟨fun h => h, fun h => h, fun h => h,
      fun h => W.supportReads_objectFamily h⟩⟩
  trans := by
    intro W V X hWV hVX
    rcases hWV with ⟨f, hf⟩
    rcases hVX with ⟨g, hg⟩
    exact ⟨contextMorphismComp f g, contextMorphismComp_isRestriction hf hg⟩
  readableMorphism := fun h => Classical.choose h
  readableMorphism_isRestriction := fun h => Classical.choose_spec h

/--
II.命題4.2: componentwise product context gives a finite-meet structure for
the restriction-morphism preorder.
-/
noncomputable def productContextFiniteMeet {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} :
    ContextFiniteMeet (contextMorphismPreorderCategory A) where
  meet := productContext
  meet_le_left := fun W V =>
    ⟨productContextLeftMorphism W V, productContextLeft_isRestriction W V⟩
  meet_le_right := fun W V =>
    ⟨productContextRightMorphism W V, productContextRight_isRestriction W V⟩
  le_meet := by
    intro X W V hXW hXV
    rcases hXW with ⟨f, hf⟩
    rcases hXV with ⟨g, hg⟩
    exact ⟨productContextLiftMorphism f g, productContextLift_isRestriction hf hg⟩

/--
II.命題4.2: readable equivalence before quotienting.

The quotient that identifies readable identities is represented by the setoid
generated by mutual readable refinement.
-/
def ReadableEquivalent {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (W V : ArchCtx A) : Prop :=
  C.le W V ∧ C.le V W

namespace ReadableEquivalent

/-- II.命題4.2: readable equivalence is reflexive. -/
theorem refl {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (W : ArchCtx A) :
    ReadableEquivalent C W W :=
  ⟨C.refl W, C.refl W⟩

/-- II.命題4.2: readable equivalence is symmetric. -/
theorem symm {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {W V : ArchCtx A}
    (h : ReadableEquivalent C W V) :
    ReadableEquivalent C V W :=
  ⟨h.2, h.1⟩

/-- II.命題4.2: readable equivalence is transitive. -/
theorem trans {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} {W V X : ArchCtx A}
    (hWV : ReadableEquivalent C W V) (hVX : ReadableEquivalent C V X) :
    ReadableEquivalent C W X :=
  ⟨C.trans hWV.1 hVX.1, C.trans hVX.2 hWV.2⟩

end ReadableEquivalent

/-- II.命題4.2: the readable-equivalence setoid used for the quotient reading. -/
def readableSetoid {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) : Setoid (ArchCtx A) where
  r := ReadableEquivalent C
  iseqv := ⟨ReadableEquivalent.refl C, ReadableEquivalent.symm,
    ReadableEquivalent.trans⟩

/-- II.命題4.2: context objects after quotienting readable equivalence. -/
abbrev QuotientArchCtx {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) :=
  Quotient (readableSetoid C)

/--
II.命題4.2: finite-meet preorder category package.

This is the unquotiented reading: homs are thin, but antisymmetry is not yet
part of the data.
-/
structure ContextFiniteMeetPreorderCategory {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) where
  preorder : ContextPreorderCategory A
  finiteMeet : ContextFiniteMeet preorder

/--
II.命題4.2: finite-meet poset category package.

The extra `antisymm` field is the quotient-after-readable-equivalence reading:
once mutual readable refinement is identified, the preorder is read as a poset.
-/
structure ContextFiniteMeetPosetCategory {U : AtomCarrier.{u}}
    (A : ArchitectureObject U) extends ContextFiniteMeetPreorderCategory A where
  antisymm :
    ∀ {W V : ArchCtx A}, preorder.le W V -> preorder.le V W -> W = V

/--
II.命題4.2: finite-meet poset package on readable-equivalence quotient objects.

This is the quotient reading explicitly: objects are `QuotientArchCtx C`, not
raw contexts. The order and meet are part of the quotient package so later
proofs can use the quotient surface directly.
-/
structure QuotientFiniteMeetPosetCategory {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (C : ContextPreorderCategory A) where
  le : QuotientArchCtx C -> QuotientArchCtx C -> Prop
  refl : ∀ W : QuotientArchCtx C, le W W
  trans :
    ∀ {W V X : QuotientArchCtx C}, le W V -> le V X -> le W X
  antisymm :
    ∀ {W V : QuotientArchCtx C}, le W V -> le V W -> W = V
  meet : QuotientArchCtx C -> QuotientArchCtx C -> QuotientArchCtx C
  meet_le_left : ∀ W V : QuotientArchCtx C, le (meet W V) W
  meet_le_right : ∀ W V : QuotientArchCtx C, le (meet W V) V
  le_meet :
    ∀ {X W V : QuotientArchCtx C}, le X W -> le X V -> le X (meet W V)
  raw_le_to_quotient :
    ∀ {W V : ArchCtx A}, C.le W V -> le (Quotient.mk (readableSetoid C) W)
      (Quotient.mk (readableSetoid C) V)

/-- II.命題4.2: readable order descends to readable-equivalence quotients. -/
def quotientLe {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) :
    QuotientArchCtx C -> QuotientArchCtx C -> Prop :=
  Quotient.lift₂ (fun W V : ArchCtx A => C.le W V) (by
    intro W V W' V' hW hV
    apply propext
    constructor
    · intro h
      exact C.trans (C.trans hW.2 h) hV.1
    · intro h
      exact C.trans (C.trans hW.1 h) hV.2)

/--
II.命題4.2: quotient order is independent of readable-equivalent
representatives.
-/
theorem quotientLe_wellDefined {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) {W W' V V' : ArchCtx A}
    (hW : ReadableEquivalent C W W') (hV : ReadableEquivalent C V V') :
    quotientLe C (Quotient.mk (readableSetoid C) W)
      (Quotient.mk (readableSetoid C) V) ->
      quotientLe C (Quotient.mk (readableSetoid C) W')
        (Quotient.mk (readableSetoid C) V') := by
  intro h
  exact C.trans (C.trans hW.2 h) hV.1

/-- II.命題4.2: finite meet descends to readable-equivalence quotients. -/
def quotientMeet {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (M : ContextFiniteMeet C) :
    QuotientArchCtx C -> QuotientArchCtx C -> QuotientArchCtx C :=
  Quotient.lift₂
    (fun W V : ArchCtx A => Quotient.mk (readableSetoid C) (M.meet W V)) (by
    intro W V W' V' hW hV
    exact Quotient.sound ⟨
      M.le_meet
        (C.trans (M.meet_le_left W V) hW.1)
        (C.trans (M.meet_le_right W V) hV.1),
      M.le_meet
        (C.trans (M.meet_le_left W' V') hW.2)
        (C.trans (M.meet_le_right W' V') hV.2)⟩)

/--
II.命題4.2: quotient meet is independent of readable-equivalent
representatives.
-/
theorem quotientMeet_wellDefined {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (M : ContextFiniteMeet C)
    {W W' V V' : ArchCtx A}
    (hW : ReadableEquivalent C W W') (hV : ReadableEquivalent C V V') :
    ReadableEquivalent C (M.meet W V) (M.meet W' V') :=
  ⟨
    M.le_meet
      (C.trans (M.meet_le_left W V) hW.1)
      (C.trans (M.meet_le_right W V) hV.1),
    M.le_meet
      (C.trans (M.meet_le_left W' V') hW.2)
      (C.trans (M.meet_le_right W' V') hV.2)⟩

/--
II.命題4.2: build the readable-equivalence quotient finite-meet poset from the
preorder and finite-meet data.
-/
def quotientFiniteMeetPosetCategoryOf {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C) :
    QuotientFiniteMeetPosetCategory C where
  le := quotientLe C
  refl := by
    intro W
    refine Quotient.inductionOn W ?_
    intro W
    exact C.refl W
  trans := by
    intro W V X
    refine Quotient.inductionOn W ?_ V X
    intro W V X
    refine Quotient.inductionOn V ?_ X
    intro V X
    refine Quotient.inductionOn X ?_
    intro X hWV hVX
    exact C.trans hWV hVX
  antisymm := by
    intro W V
    refine Quotient.inductionOn W ?_ V
    intro W V
    refine Quotient.inductionOn V ?_
    intro V hWV hVW
    exact Quotient.sound ⟨hWV, hVW⟩
  meet := quotientMeet M
  meet_le_left := by
    intro W V
    refine Quotient.inductionOn W ?_ V
    intro W V
    refine Quotient.inductionOn V ?_
    intro V
    exact M.meet_le_left W V
  meet_le_right := by
    intro W V
    refine Quotient.inductionOn W ?_ V
    intro W V
    refine Quotient.inductionOn V ?_
    intro V
    exact M.meet_le_right W V
  le_meet := by
    intro X W V
    refine Quotient.inductionOn X ?_ W V
    intro X W V
    refine Quotient.inductionOn W ?_ V
    intro W V
    refine Quotient.inductionOn V ?_
    intro V hXW hXV
    exact M.le_meet hXW hXV
  raw_le_to_quotient := by
    intro W V h
    exact h

/-- II.命題4.2: build the finite-meet preorder category from explicit assumptions. -/
def finiteMeetPreorderCategoryOf {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C) :
    ContextFiniteMeetPreorderCategory A where
  preorder := C
  finiteMeet := M

/-- II.命題4.2: the explicit assumptions produce a finite-meet preorder category. -/
theorem minimalContextFiniteMeetPreorderCategory {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C) :
    ∃ site : ContextFiniteMeetPreorderCategory A,
      site.preorder = C ∧ HEq site.finiteMeet M :=
  ⟨finiteMeetPreorderCategoryOf C M, rfl, HEq.rfl⟩

/--
II.命題4.2: build the finite-meet poset category once antisymmetry after
readable-equivalence quotienting is fixed.
-/
def finiteMeetPosetCategoryOf {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C)
    (antisymm :
      ∀ {W V : ArchCtx A}, C.le W V -> C.le V W -> W = V) :
    ContextFiniteMeetPosetCategory A where
  preorder := C
  finiteMeet := M
  antisymm := antisymm

/--
II.命題4.2: the explicit assumptions plus antisymmetry produce a finite-meet
poset category.
-/
theorem minimalContextFiniteMeetPosetCategory {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C)
    (antisymm :
      ∀ {W V : ArchCtx A}, C.le W V -> C.le V W -> W = V) :
    ∃ site : ContextFiniteMeetPosetCategory A,
      site.preorder = C ∧ HEq site.finiteMeet M :=
  ⟨finiteMeetPosetCategoryOf C M antisymm, rfl, HEq.rfl⟩

/--
II.命題4.2: explicit quotient-order assumptions produce the finite-meet poset
category on readable-equivalence quotient objects.
-/
theorem minimalContextQuotientFiniteMeetPosetCategory {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (C : ContextPreorderCategory A)
    (Q : QuotientFiniteMeetPosetCategory C) :
    ∃ site : QuotientFiniteMeetPosetCategory C, site = Q :=
  ⟨Q, rfl⟩

/--
II.命題4.2: the readable-equivalence quotient of a finite-meet context
preorder carries the quotient finite-meet poset structure.
-/
theorem minimalContextQuotientFiniteMeetPosetCategory_fromFiniteMeet
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C) :
    ∃ site : QuotientFiniteMeetPosetCategory C,
      site = quotientFiniteMeetPosetCategoryOf C M :=
  ⟨quotientFiniteMeetPosetCategoryOf C M, rfl⟩

/--
II.仮定4.3: pullback / overlap package for context covers.

The package is explicit assumption data on `ArchCtx(A)`. It states that an
overlap over a base is available and projects to both local contexts and then
to the base.
-/
structure ContextOverlapPullback {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) where
  overlap : (base left right : ArchCtx A) -> ArchCtx A
  overlap_le_left :
    ∀ {base left right : ArchCtx A}, C.le left base -> C.le right base ->
      C.le (overlap base left right) left
  overlap_le_right :
    ∀ {base left right : ArchCtx A}, C.le left base -> C.le right base ->
      C.le (overlap base left right) right
  overlap_le_base :
    ∀ {base left right : ArchCtx A}, C.le left base -> C.le right base ->
      C.le (overlap base left right) base
  overlap_lift :
    ∀ {base left right X : ArchCtx A}, C.le left base -> C.le right base ->
      C.le X left -> C.le X right -> C.le X (overlap base left right)

namespace ContextOverlapPullback

/-- II.仮定4.3: the selected overlap maps to the left context. -/
theorem left {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (P : ContextOverlapPullback C)
    {base left right : ArchCtx A} (hl : C.le left base) (hr : C.le right base) :
    C.le (P.overlap base left right) left :=
  P.overlap_le_left hl hr

/-- II.仮定4.3: the selected overlap maps to the right context. -/
theorem right {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (P : ContextOverlapPullback C)
    {base left right : ArchCtx A} (hl : C.le left base) (hr : C.le right base) :
    C.le (P.overlap base left right) right :=
  P.overlap_le_right hl hr

/-- II.仮定4.3: the selected overlap maps to the common base. -/
theorem base {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (P : ContextOverlapPullback C)
    {base left right : ArchCtx A} (hl : C.le left base) (hr : C.le right base) :
    C.le (P.overlap base left right) base :=
  P.overlap_le_base hl hr

/-- II.仮定4.3: the selected overlap satisfies the pullback lifting property. -/
theorem lift {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : ContextPreorderCategory A} (P : ContextOverlapPullback C)
    {base left right X : ArchCtx A} (hl : C.le left base) (hr : C.le right base)
    (hXl : C.le X left) (hXr : C.le X right) :
    C.le X (P.overlap base left right) :=
  P.overlap_lift hl hr hXl hXr

end ContextOverlapPullback

/-- II.仮定4.3: in the finite-meet minimal model, overlap is realized by meet. -/
def meetOverlapPullback {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C) :
    ContextOverlapPullback C where
  overlap := fun _base left right => M.meet left right
  overlap_le_left := fun {_base} {left} {right} _hl _hr =>
    M.meet_le_left left right
  overlap_le_right := fun {_base} {left} {right} _hl _hr =>
    M.meet_le_right left right
  overlap_le_base := fun {_base} {_left} {_right} hl _hr =>
    C.trans (M.meet_le_left _ _) hl
  overlap_lift := fun {_base} {_left} {_right} {_X} _hl _hr hXl hXr =>
    M.le_meet hXl hXr

/--
II.仮定4.3 / 命題4.2: the finite-meet overlap agrees definitionally with
the meet of the two local contexts.
-/
theorem minimalMeetPullback {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (C : ContextPreorderCategory A) (M : ContextFiniteMeet C)
    (base left right : ArchCtx A) :
    (meetOverlapPullback C M).overlap base left right = M.meet left right :=
  rfl

end Site
end AAT.AG
