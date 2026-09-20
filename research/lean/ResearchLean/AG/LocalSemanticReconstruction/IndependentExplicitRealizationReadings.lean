import ResearchLean.AG.RealizationReconstruction.CSAATExplicitExactGeometryCategory
import Formal.Util.AssertStandardAxioms

/-!
# Primitive readings of explicit realization transport

Implementation notes: nine query roles retain both directions of each carrier
equivalence and each point of the actual context-morphism action. Naturality
is tested on every actual context morphism. The restriction-preservation proof
is derived from the pointwise inverse, reading, and naturality equations; it is
not stored as a completed transport or supplied as a separate global law.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentExplicitRealization

universe u

open CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {P Q : AATCorePackage U}

/-- The forward context image selected by the independently assembled package Hom. -/
abbrev forward (f : PackageTotalHom P Q) (W : Site.ContextCategoryObject P.contextPreorder) :=
  (coreContextFunctor f).obj W

/-- Primitive carrier-equivalence points and actual context-action points. -/
inductive Query (f : PackageTotalHom P Q) where
  /-- Forward support image at a context. -/
  | support (W : Site.ContextCategoryObject P.contextPreorder) (s : W.ctx.Support)
  /-- Reverse support image at a context. -/
  | supportBack (W : Site.ContextCategoryObject P.contextPreorder) (s : (forward f W).ctx.Support)
  /-- Forward axis image at a context. -/
  | axis (W : Site.ContextCategoryObject P.contextPreorder) (a : W.ctx.Axis)
  /-- Reverse axis image at a context. -/
  | axisBack (W : Site.ContextCategoryObject P.contextPreorder) (a : (forward f W).ctx.Axis)
  /-- Forward observable image at a context. -/
  | observable (W : Site.ContextCategoryObject P.contextPreorder) (x : W.ctx.Observable)
  /-- Reverse observable image at a context. -/
  | observableBack (W : Site.ContextCategoryObject P.contextPreorder) (x : (forward f W).ctx.Observable)
  /-- Support action of an actual context morphism at one transported support. -/
  | contextSupport {W V : Site.ContextCategoryObject P.contextPreorder}
      (g : Site.ContextMorphism W.ctx V.ctx) (s : (forward f W).ctx.Support)
  /-- Axis action of an actual context morphism at one transported axis. -/
  | contextAxis {W V : Site.ContextCategoryObject P.contextPreorder}
      (g : Site.ContextMorphism W.ctx V.ctx) (a : (forward f W).ctx.Axis)
  /-- Reverse observable action of an actual context morphism at one transported observable. -/
  | contextObservable {W V : Site.ContextCategoryObject P.contextPreorder}
      (g : Site.ContextMorphism W.ctx V.ctx) (x : (forward f V).ctx.Observable)

/-- Each response is a single value in the native directed carrier. -/
def Query.Value {f : PackageTotalHom P Q} : Query f → Type u
  | .support W _ => (forward f W).ctx.Support
  | .supportBack W _ => W.ctx.Support
  | .axis W _ => (forward f W).ctx.Axis
  | .axisBack W _ => W.ctx.Axis
  | .observable W _ => (forward f W).ctx.Observable
  | .observableBack W _ => W.ctx.Observable
  | @Query.contextSupport _ _ _ _ _ V _ _ => (forward f V).ctx.Support
  | @Query.contextAxis _ _ _ _ _ V _ _ => (forward f V).ctx.Axis
  | @Query.contextObservable _ _ _ _ W _ _ _ => (forward f W).ctx.Observable

/-- A dependent table of all explicit realization points. -/
abbrev Table (f : PackageTotalHom P Q) := (q : Query f) → q.Value

variable {f : PackageTotalHom P Q}

/-- Point inverse, reading, and actual-morphism naturality equations. -/
structure IsLawful (t : Table f) : Prop where
  /-- Reverse after forward support is identity. -/
  support_left : ∀ W s, t (.supportBack W (t (.support W s))) = s
  /-- Forward after reverse support is identity. -/
  support_right : ∀ W s, t (.support W (t (.supportBack W s))) = s
  /-- Reverse after forward axis is identity. -/
  axis_left : ∀ W a, t (.axisBack W (t (.axis W a))) = a
  /-- Forward after reverse axis is identity. -/
  axis_right : ∀ W a, t (.axis W (t (.axisBack W a))) = a
  /-- Reverse after forward observable is identity. -/
  observable_left : ∀ W x, t (.observableBack W (t (.observable W x))) = x
  /-- Forward after reverse observable is identity. -/
  observable_right : ∀ W x, t (.observable W (t (.observableBack W x))) = x
  /-- Support readings are preserved and reflected at each Atom. -/
  supportReads : ∀ W s a, W.ctx.minimal.supportReads s a ↔
    (forward f W).ctx.minimal.supportReads (t (.support W s)) (f.upper.atomEquiv a)
  /-- Axis readings are preserved and reflected. -/
  axisReads : ∀ W a, W.ctx.minimal.axisReads a ↔
    (forward f W).ctx.minimal.axisReads (t (.axis W a))
  /-- Observable readings are preserved and reflected. -/
  observableReads : ∀ W x, W.ctx.minimal.observableReads x ↔
    (forward f W).ctx.minimal.observableReads (t (.observable W x))
  /-- Support naturality uses the actual retained morphism. -/
  support_naturality : ∀ {W V} (g : Site.ContextMorphism W.ctx V.ctx) s,
    t (.contextSupport g (t (.support W s))) = t (.support V (g.supportMap s))
  /-- Axis naturality uses the same actual morphism. -/
  axis_naturality : ∀ {W V} (g : Site.ContextMorphism W.ctx V.ctx) a,
    t (.contextAxis g (t (.axis W a))) = t (.axis V (g.axisMap a))
  /-- Observable naturality retains the reverse direction of restriction. -/
  observable_naturality : ∀ {W V} (g : Site.ContextMorphism W.ctx V.ctx) x,
    t (.contextObservable g (t (.observable V x))) = t (.observable W (g.observableRestrict x))

/-- Collect the three point families of the image of one actual context morphism. -/
def contextMorphism (t : Table f) {W V : Site.ContextCategoryObject P.contextPreorder}
    (g : Site.ContextMorphism W.ctx V.ctx) :
    Site.ContextMorphism (forward f W).ctx (forward f V).ctx :=
  ⟨fun s => t (.contextSupport g s), fun a => t (.contextAxis g a),
    fun x => t (.contextObservable g x)⟩

/-- Pointwise naturality and inverse readings imply preservation of native restrictions. -/
theorem contextMorphism_isRestriction (t : Table f) (hl : IsLawful t)
    {W V : Site.ContextCategoryObject P.contextPreorder} (g : Site.ContextMorphism W.ctx V.ctx)
    (hg : g.IsRestriction) : (contextMorphism t g).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s a hs
    let s0 := t (.supportBack W s)
    let a0 := f.upper.atomEquiv.symm a
    have h0 : W.ctx.minimal.supportReads s0 a0 := (hl.supportReads W s0 a0).2 (by
      simpa [s0, a0, hl.support_right] using hs)
    have h1 := (hl.supportReads V (g.supportMap s0) a0).1 (hg.1 h0)
    have hn : t (.contextSupport g s) = t (.support V (g.supportMap s0)) :=
      (congrArg (fun z => t (.contextSupport g z)) (hl.support_right W s)).symm.trans
        (hl.support_naturality g s0)
    change (forward f V).ctx.minimal.supportReads (t (.contextSupport g s)) a
    rw [hn]
    simpa [a0] using h1
  · intro a ha
    let a0 := t (.axisBack W a)
    have h0 : W.ctx.minimal.axisReads a0 := (hl.axisReads W a0).2 (by
      simpa [a0, hl.axis_right] using ha)
    have h1 := (hl.axisReads V (g.axisMap a0)).1 (hg.2.1 h0)
    have hn : t (.contextAxis g a) = t (.axis V (g.axisMap a0)) :=
      (congrArg (fun z => t (.contextAxis g z)) (hl.axis_right W a)).symm.trans
        (hl.axis_naturality g a0)
    change (forward f V).ctx.minimal.axisReads (t (.contextAxis g a))
    rw [hn]
    exact h1
  · intro x hx
    let x0 := t (.observableBack V x)
    have h0 : V.ctx.minimal.observableReads x0 := (hl.observableReads V x0).2 (by
      simpa [x0, hl.observable_right] using hx)
    have h1 := (hl.observableReads W (g.observableRestrict x0)).1 (hg.2.2.1 h0)
    have hn : t (.contextObservable g x) = t (.observable W (g.observableRestrict x0)) :=
      (congrArg (fun z => t (.contextObservable g z)) (hl.observable_right V x)).symm.trans
        (hl.observable_naturality g x0)
    change (forward f W).ctx.minimal.observableReads (t (.contextObservable g x))
    rw [hn]
    exact h1
  · intro s a hs
    exact (forward f V).ctx.minimal.supportReads_objectFamily hs

/-- Assemble the full explicit realization supply from the nine primitive query roles. -/
def assemble (t : Table f) (hl : IsLawful t) : ExplicitRealizationTransportSupply P Q f where
  contextMorphism := contextMorphism t
  contextMorphism_isRestriction := contextMorphism_isRestriction t hl
  supportEquiv W :=
    ⟨fun s => t (.support W s), fun s => t (.supportBack W s), hl.support_left W, hl.support_right W⟩
  axisEquiv W :=
    ⟨fun a => t (.axis W a), fun a => t (.axisBack W a), hl.axis_left W, hl.axis_right W⟩
  observableEquiv W :=
    ⟨fun x => t (.observable W x), fun x => t (.observableBack W x), hl.observable_left W, hl.observable_right W⟩
  supportReads_iff := hl.supportReads
  axisReads_iff := hl.axisReads
  observableReads_iff := hl.observableReads
  support_naturality := hl.support_naturality
  axis_naturality := hl.axis_naturality
  observable_naturality := hl.observable_naturality

/-- Read each equivalence direction and each point of the actual context action. -/
def read (R : ExplicitRealizationTransportSupply P Q f) : Table f
  | .support W s => R.supportEquiv W s
  | .supportBack W s => (R.supportEquiv W).symm s
  | .axis W a => R.axisEquiv W a
  | .axisBack W a => (R.axisEquiv W).symm a
  | .observable W x => R.observableEquiv W x
  | .observableBack W x => (R.observableEquiv W).symm x
  | .contextSupport g s => (R.contextMorphism g).supportMap s
  | .contextAxis g a => (R.contextMorphism g).axisMap a
  | .contextObservable g x => (R.contextMorphism g).observableRestrict x

/-- Every native explicit realization supply gives all independent point equations. -/
theorem read_isLawful (R : ExplicitRealizationTransportSupply P Q f) : IsLawful (read R) where
  support_left W := (R.supportEquiv W).left_inv
  support_right W := (R.supportEquiv W).right_inv
  axis_left W := (R.axisEquiv W).left_inv
  axis_right W := (R.axisEquiv W).right_inv
  observable_left W := (R.observableEquiv W).left_inv
  observable_right W := (R.observableEquiv W).right_inv
  supportReads := R.supportReads_iff
  axisReads := R.axisReads_iff
  observableReads := R.observableReads_iff
  support_naturality := R.support_naturality
  axis_naturality := R.axis_naturality
  observable_naturality := R.observable_naturality

/-- Reassembly recovers the complete native action and every carrier equivalence. -/
theorem assemble_read (R : ExplicitRealizationTransportSupply P Q f) :
    assemble (read R) (read_isLawful R) = R := by
  apply ExplicitRealizationTransportSupply.ext
  · intro W V g
    rfl
  · intro W
    apply Equiv.ext
    intro s
    rfl
  · intro W
    apply Equiv.ext
    intro a
    rfl
  · intro W
    apply Equiv.ext
    intro x
    rfl

/-- Every raw query response survives the full native assembly. -/
theorem read_assemble (t : Table f) (hl : IsLawful t) : read (assemble t hl) = t := by
  funext q
  cases q <;> rfl

/-- All explicit realization supplies correspond to exactly the lawful primitive tables. -/
def readingEquiv (f : PackageTotalHom P Q) :
    ExplicitRealizationTransportSupply P Q f ≃ {t : Table f // IsLawful t} where
  toFun R := ⟨read R, read_isLawful R⟩
  invFun t := assemble t.val t.property
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble t.val t.property)

/-- The full primitive reading separates actual context actions as well as carrier maps. -/
theorem read_injective : Function.Injective (read (f := f)) := by
  intro R S h
  exact (readingEquiv f).injective (Subtype.ext h)

/-- Identity acts on each carrier and each retained context morphism point. -/
def identityTable (P : AATCorePackage U) : Table (PackageTotalHom.id P)
  | .support _ s => s
  | .supportBack _ s => s
  | .axis _ a => a
  | .axisBack _ a => a
  | .observable _ x => x
  | .observableBack _ x => x
  | .contextSupport g s => g.supportMap s
  | .contextAxis g a => g.axisMap a
  | .contextObservable g x => g.observableRestrict x

/-- Reading the native identity gives the directly defined point identity. -/
theorem read_id (P : AATCorePackage U) :
    read (ExplicitRealizationTransportSupply.id P) = identityTable P := by
  funext q
  cases q <;> rfl

/-- Compose primitive points in their original directions, including actual context actions. -/
def composeTable {R : AATCorePackage U} {g : PackageTotalHom Q R}
    (t : Table f) (s : Table g) : Table (PackageTotalHom.comp f g)
  | .support W x => s (.support (forward f W) (t (.support W x)))
  | .supportBack W x => t (.supportBack W (s (.supportBack (forward f W) x)))
  | .axis W x => s (.axis (forward f W) (t (.axis W x)))
  | .axisBack W x => t (.axisBack W (s (.axisBack (forward f W) x)))
  | .observable W x => s (.observable (forward f W) (t (.observable W x)))
  | .observableBack W x => t (.observableBack W (s (.observableBack (forward f W) x)))
  | @Query.contextSupport _ _ _ _ W V h x =>
    s (.support (forward f V) (t (.contextSupport h (s (.supportBack (forward f W) x)))))
  | @Query.contextAxis _ _ _ _ W V h x =>
    s (.axis (forward f V) (t (.contextAxis h (s (.axisBack (forward f W) x)))))
  | @Query.contextObservable _ _ _ _ W V h x =>
    s (.observable (forward f W)
      (t (.contextObservable h (s (.observableBack (forward f V) x)))))

/-- The direct composite table is the point reading of the full native composite. -/
theorem read_comp {R : AATCorePackage U} {g : PackageTotalHom Q R}
    (t : Table f) (s : Table g) (ht : IsLawful t) (hs : IsLawful s) :
    read (ExplicitRealizationTransportSupply.comp (assemble t ht) (assemble s hs)) =
      composeTable t s := by
  funext q
  cases q with
  | support | supportBack | axis | axisBack | observable | observableBack => rfl
  | contextSupport h x =>
    have hn := hs.support_naturality (contextMorphism t h)
      (s (.supportBack _ x))
    rw [hs.support_right] at hn
    exact hn
  | contextAxis h x =>
    have hn := hs.axis_naturality (contextMorphism t h)
      (s (.axisBack _ x))
    rw [hs.axis_right] at hn
    exact hn
  | contextObservable h x =>
    have hn := hs.observable_naturality (contextMorphism t h)
      (s (.observableBack _ x))
    rw [hs.observable_right] at hn
    exact hn

/-- The direct point identity satisfies every local inverse, reading, and naturality law. -/
theorem identityTable_isLawful (P : AATCorePackage U) : IsLawful (identityTable P) := by
  rw [← read_id]
  exact read_isLawful _

/-- Direct point composition preserves the local laws. -/
theorem composeTable_isLawful {R : AATCorePackage U} {g : PackageTotalHom Q R}
    (t : Table f) (s : Table g) (ht : IsLawful t) (hs : IsLawful s) :
    IsLawful (composeTable t s) := by
  rw [← read_comp t s ht hs]
  exact read_isLawful _

/-- Assembly sends the direct point identity to the native identity supply. -/
theorem assemble_id (P : AATCorePackage U) :
    assemble (identityTable P) (identityTable_isLawful P) =
      ExplicitRealizationTransportSupply.id P := by
  apply read_injective
  rw [read_assemble, read_id]

/-- Assembly preserves the direct point composite, on every retained context action. -/
theorem assemble_comp {R : AATCorePackage U} {g : PackageTotalHom Q R}
    (t : Table f) (s : Table g) (ht : IsLawful t) (hs : IsLawful s) :
    assemble (composeTable t s) (composeTable_isLawful t s ht hs) =
      ExplicitRealizationTransportSupply.comp (assemble t ht) (assemble s hs) := by
  apply read_injective
  rw [read_assemble, read_comp]

/-- Each composite response uses at most three primitive points, with no whole-function query argument. -/
theorem composeTable_finite_support {R : AATCorePackage U} {g : PackageTotalHom Q R}
    (t : Table f) (s : Table g) (q : Query (PackageTotalHom.comp f g)) :
    ∃ F : Finset (Query f), ∃ G : Finset (Query g), F.card + G.card ≤ 3 ∧
      ∀ (t' : Table f) (s' : Table g),
        (∀ p ∈ F, t p = t' p) → (∀ p ∈ G, s p = s' p) →
          composeTable t s q = composeTable t' s' q := by
  classical
  cases q with
  | support W x =>
    refine ⟨{.support W x}, {.support (forward f W) (t (.support W x))}, by simp, ?_⟩
    intro t' s' ht hs
    have h := ht (.support W x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact hs _ (by simp)
  | supportBack W x =>
    refine ⟨{.supportBack W (s (.supportBack (forward f W) x))},
      {.supportBack (forward f W) x}, by simp, ?_⟩
    intro t' s' ht hs
    have h := hs (.supportBack (forward f W) x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact ht _ (by simp)
  | axis W x =>
    refine ⟨{.axis W x}, {.axis (forward f W) (t (.axis W x))}, by simp, ?_⟩
    intro t' s' ht hs
    have h := ht (.axis W x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact hs _ (by simp)
  | axisBack W x =>
    refine ⟨{.axisBack W (s (.axisBack (forward f W) x))},
      {.axisBack (forward f W) x}, by simp, ?_⟩
    intro t' s' ht hs
    have h := hs (.axisBack (forward f W) x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact ht _ (by simp)
  | observable W x =>
    refine ⟨{.observable W x}, {.observable (forward f W) (t (.observable W x))}, by simp, ?_⟩
    intro t' s' ht hs
    have h := ht (.observable W x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact hs _ (by simp)
  | observableBack W x =>
    refine ⟨{.observableBack W (s (.observableBack (forward f W) x))},
      {.observableBack (forward f W) x}, by simp, ?_⟩
    intro t' s' ht hs
    have h := hs (.observableBack (forward f W) x) (by simp)
    dsimp only [composeTable]
    rw [← h]
    exact ht _ (by simp)
  | @contextSupport W V h x =>
    let y := s (.supportBack (forward f W) x)
    let z := t (.contextSupport h y)
    refine ⟨{.contextSupport h y}, {.supportBack (forward f W) x, .support (forward f V) z},
      by simp, ?_⟩
    intro t' s' ht hs
    have h1 := hs (.supportBack (forward f W) x) (by simp)
    have h2 := ht (.contextSupport h y) (by simp)
    have h3 := hs (.support (forward f V) z) (by simp)
    change s (.support (forward f V) z) =
      s' (.support (forward f V) (t' (.contextSupport h (s' (.supportBack (forward f W) x)))))
    rw [← h1, ← h2]
    exact h3
  | @contextAxis W V h x =>
    let y := s (.axisBack (forward f W) x)
    let z := t (.contextAxis h y)
    refine ⟨{.contextAxis h y}, {.axisBack (forward f W) x, .axis (forward f V) z},
      by simp, ?_⟩
    intro t' s' ht hs
    have h1 := hs (.axisBack (forward f W) x) (by simp)
    have h2 := ht (.contextAxis h y) (by simp)
    have h3 := hs (.axis (forward f V) z) (by simp)
    change s (.axis (forward f V) z) =
      s' (.axis (forward f V) (t' (.contextAxis h (s' (.axisBack (forward f W) x)))))
    rw [← h1, ← h2]
    exact h3
  | @contextObservable W V h x =>
    let y := s (.observableBack (forward f V) x)
    let z := t (.contextObservable h y)
    refine ⟨{.contextObservable h y}, {.observableBack (forward f V) x, .observable (forward f W) z},
      by simp, ?_⟩
    intro t' s' ht hs
    have h1 := hs (.observableBack (forward f V) x) (by simp)
    have h2 := ht (.contextObservable h y) (by simp)
    have h3 := hs (.observable (forward f W) z) (by simp)
    change s (.observable (forward f W) z) =
      s' (.observable (forward f W)
        (t' (.contextObservable h (s' (.observableBack (forward f V) x)))))
    rw [← h1, ← h2]
    exact h3

/-- Corrupt only the support action on endomorphisms, leaving all carrier equivalences unchanged. -/
noncomputable def freezeSupportEndomorphisms (P : AATCorePackage U) : Table (PackageTotalHom.id P) := by
  classical
  intro q
  match q with
  | @Query.contextSupport _ _ _ _ W V g s =>
    change V.ctx.Support
    exact if h : W = V then cast (congrArg (fun Z => Z.ctx.Support) h) s else g.supportMap s
  | q => exact read (ExplicitRealizationTransportSupply.id P) q

/-- A moved support detects corruption of actual-morphism naturality even with identity carrier maps. -/
theorem freezeSupportEndomorphisms_not_lawful (P : AATCorePackage U)
    (W : Site.ContextCategoryObject P.contextPreorder) (g : Site.ContextMorphism W.ctx W.ctx)
    (s : W.ctx.Support) (hm : g.supportMap s ≠ s) : ¬ IsLawful (freezeSupportEndomorphisms P) := by
  intro hl
  have h := hl.support_naturality g s
  apply hm
  symm
  simpa [freezeSupportEndomorphisms, read, ExplicitRealizationTransportSupply.id] using h

/-- A finite context with two supports and empty readings over any architecture object. -/
def twoSupportContext (A : ArchitectureObject U) : Site.ArchCtx A where
  minimal :=
    { Support := ULift.{u} Bool
      Axis := PUnit
      Observable := PUnit
      supportReads _ _ := False
      supportReads_objectFamily := False.elim
      axisReads _ := False
      observableReads _ := False }
  Extension := PUnit
  extension := PUnit.unit

/-- Swap the two supports while keeping the other primitive context maps fixed. -/
def swapSupport (A : ArchitectureObject U) :
    Site.ContextMorphism (twoSupportContext A) (twoSupportContext A) :=
  ⟨fun s => ⟨!s.down⟩, _root_.id, _root_.id⟩

/-- The changed actual context action fails on an explicit two-support finite witness. -/
theorem finite_support_action_rejected (P : AATCorePackage U) :
    ¬ IsLawful (freezeSupportEndomorphisms P) :=
  freezeSupportEndomorphisms_not_lawful P ⟨twoSupportContext P.object⟩
    (swapSupport P.object) ⟨false⟩ (by
      intro h
      exact Bool.noConfusion (congrArg ULift.down h))

/-- The native identity supplies a positive instance on the same arbitrary core. -/
theorem identity_lawful (P : AATCorePackage U) :
    IsLawful (read (ExplicitRealizationTransportSupply.id P)) := read_isLawful _

end AAT.AG.LocalSemanticReconstruction.IndependentExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentExplicitRealization
