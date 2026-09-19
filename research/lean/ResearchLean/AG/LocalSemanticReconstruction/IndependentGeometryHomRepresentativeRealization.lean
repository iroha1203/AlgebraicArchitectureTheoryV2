import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackagePoints
import Formal.Util.AssertStandardAxioms

/-!
# Representative realization transport from common primitive Hom points

Implementation notes: these three carrier maps remain directed. Local rules
compare readings at true context/value points and compare the primitive
source/target selected-restriction responses. Native naturality is derived
from those point squares after the core context functor is reconstructed.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- The common forward context graph activates the representative realization rows. -/
def contextPoints (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B) : Bool :=
  h (.atObjects A B (.context .forward W V))

/-- Directed support points retain both candidate context references. -/
def support (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Bool := h (.atObjects A B (.realization (.representativeSupport W V x y)))

/-- Directed axis points are independent of the support component. -/
def axis (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Bool := h (.atObjects A B (.realization (.representativeAxis W V x y)))

/-- Directed observable points retain the same source/target context ordering. -/
def observable (h : Table.{u, v} U .representative) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Bool := h (.atObjects A B (.realization (.representativeObservable W V x y)))

/-- Reading preservation and selected-restriction naturality use only primitive responses and true Hom cells. -/
structure PointLaws (s : IndependentContextPrimitive.Table A) (t : IndependentContextPrimitive.Table B)
    (h : Table.{u, v} U .representative) : Prop where
  /-- Support rows have one directed output at each active context pair. -/
  supportRows : IndependentFixedIndexedPointGraph.IsLawful (fun W : ArchCtx A => W.Support)
    (fun V : ArchCtx B => V.Support) (contextPoints h) (support h)
  /-- Axis rows have one directed output at each active context pair. -/
  axisRows : IndependentFixedIndexedPointGraph.IsLawful (fun W : ArchCtx A => W.Axis)
    (fun V : ArchCtx B => V.Axis) (contextPoints h) (axis h)
  /-- Observable rows have one directed output at each active context pair. -/
  observableRows : IndependentFixedIndexedPointGraph.IsLawful (fun W : ArchCtx A => W.Observable)
    (fun V : ArchCtx B => V.Observable) (contextPoints h) (observable h)
  /-- Support readings are preserved at the actual support and Atom point pairs. -/
  supportReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y a b, contextPoints h W V = true → support h W V x y = true →
    h (.atom .forward a b) = true → W.minimal.supportReads x a → V.minimal.supportReads y b
  /-- Axis reading preservation is a one-way implication. -/
  axisReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y, contextPoints h W V = true → axis h W V x y = true →
    W.minimal.axisReads x → V.minimal.axisReads y
  /-- Observable reading preservation is also one-way. -/
  observableReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y, contextPoints h W V = true → observable h W V x y = true →
    W.minimal.observableReads x → V.minimal.observableReads y
  /-- The support square compares the two selected readable support responses. -/
  supportNaturality : ∀ W X V Y x y xx yy,
    contextPoints h W V = true → contextPoints h X Y = true → support h W V x y = true →
    (s (.support W X x)).down = some xx → (t (.support V Y y)).down = some yy →
    support h X Y xx yy = true
  /-- The axis square compares two primitive axis responses. -/
  axisNaturality : ∀ W X V Y x y xx yy,
    contextPoints h W V = true → contextPoints h X Y = true → axis h W V x y = true →
    (s (.axis W X x)).down = some xx → (t (.axis V Y y)).down = some yy →
    axis h X Y xx yy = true
  /-- The observable square retains the native reverse restriction direction. -/
  observableNaturality : ∀ W X V Y x y xx yy,
    contextPoints h W V = true → contextPoints h X Y = true → observable h X Y x y = true →
    (s (.observable W X x)).down = some xx → (t (.observable V Y y)).down = some yy →
    observable h W V xx yy = true

/-- The selected support restriction is exactly its active primitive response. -/
theorem contextSupport_read (C : ContextPreorderCategory A) {W X : ArchCtx A}
    (hx : C.le W X) (x : W.Support) :
    (IndependentContextPrimitive.read C (.support W X x)).down = some ((C.morphism hx).supportMap x) := by
  classical
  simp only [IndependentContextPrimitive.read, dif_pos hx]
  rfl

/-- The selected axis restriction is exactly its active primitive response. -/
theorem contextAxis_read (C : ContextPreorderCategory A) {W X : ArchCtx A}
    (hx : C.le W X) (x : W.Axis) :
    (IndependentContextPrimitive.read C (.axis W X x)).down = some ((C.morphism hx).axisMap x) := by
  classical
  simp only [IndependentContextPrimitive.read, dif_pos hx]
  rfl

/-- The selected observable restriction is exactly its reverse-direction primitive response. -/
theorem contextObservable_read (C : ContextPreorderCategory A) {W X : ArchCtx A}
    (hx : C.le W X) (x : X.Observable) :
    (IndependentContextPrimitive.read C (.observable W X x)).down = some ((C.morphism hx).observableRestrict x) := by
  classical
  simp only [IndependentContextPrimitive.read, dif_pos hx]
  rfl

variable {P Q : AATCorePackage U}

/-- The comparison API requires only identification of reconstructed context and Atom points. -/
structure Maps (f : PackageTotalHom P Q) (h : Table.{u, v} U .representative) : Prop where
  /-- Forward native context images match the common context graph. -/
  context : ∀ (W : ArchCtx P.object) (V : ArchCtx Q.object), contextPoints h W V = true ↔ ((coreContextFunctor f).obj ⟨W⟩).ctx = V
  /-- Native Atom images match the common upper Atom graph. -/
  atom : ∀ a b, h (.atom .forward a b) = true ↔ f.upper.atomEquiv a = b

/-- The local conditions on native primitive context readings, used only for the comparison theorem. -/
abbrev NativePoints (P Q : AATCorePackage U) (h : Table.{u, v} U .representative) :=
  PointLaws (IndependentContextPrimitive.read P.contextPreorder) (IndependentContextPrimitive.read Q.contextPreorder) h

variable (f : PackageTotalHom P Q) (h : Table.{u, v} U .representative) (hm : Maps f h)

/-- The context image is supplied by the already constructed native core Hom. -/
def forward (W : ArchCtx P.object) : ArchCtx Q.object := ((coreContextFunctor f).obj ⟨W⟩).ctx

/-- Construct the full native representative realization supply from directed primitive point rules. -/
def assemble (hp : NativePoints P Q h) : RealizationTransportSupply P Q f := by
  classical
  let sf := IndependentFixedIndexedPointGraph.assemble (forward f) hm.context (support h) hp.supportRows
  let af := IndependentFixedIndexedPointGraph.assemble (forward f) hm.context (axis h) hp.axisRows
  let of := IndependentFixedIndexedPointGraph.assemble (forward f) hm.context (observable h) hp.observableRows
  have sp := IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (support h) hp.supportRows
  have ap := IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (axis h) hp.axisRows
  have op := IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context (observable h) hp.observableRows
  refine {
    supportComp := fun W => sf W.ctx
    axisComp := fun W => af W.ctx
    observableComp := fun W => of W.ctx
    supportReads := fun W x a hx => hp.supportReads W.ctx _ x _ a _
      ((hm.context _ _).2 rfl) ((sp _ _ _).2 rfl) ((hm.atom _ _).2 rfl) hx
    axisReads := fun W x hx => hp.axisReads W.ctx _ x _ ((hm.context _ _).2 rfl) ((ap _ _ _).2 rfl) hx
    observableReads := fun W x hx => hp.observableReads W.ctx _ x _ ((hm.context _ _).2 rfl) ((op _ _ _).2 rfl) hx
    support_naturality := ?_
    axis_naturality := ?_
    observable_naturality := ?_ }
  · intro W X g x
    have hWX : P.contextPreorder.le W.ctx X.ctx := leOfHom g
    have hVY : Q.contextPreorder.le (forward f W.ctx) (forward f X.ctx) := leOfHom ((coreContextFunctor f).map g)
    symm
    apply (sp X.ctx _ _).1
    exact hp.supportNaturality W.ctx X.ctx _ _ x _ _ _ ((hm.context _ _).2 rfl)
      ((hm.context _ _).2 rfl) ((sp _ _ _).2 rfl)
      (contextSupport_read P.contextPreorder hWX _) (contextSupport_read Q.contextPreorder hVY _)
  · intro W X g x
    have hWX : P.contextPreorder.le W.ctx X.ctx := leOfHom g
    have hVY : Q.contextPreorder.le (forward f W.ctx) (forward f X.ctx) := leOfHom ((coreContextFunctor f).map g)
    symm
    apply (ap X.ctx _ _).1
    exact hp.axisNaturality W.ctx X.ctx _ _ x _ _ _ ((hm.context _ _).2 rfl)
      ((hm.context _ _).2 rfl) ((ap _ _ _).2 rfl)
      (contextAxis_read P.contextPreorder hWX _) (contextAxis_read Q.contextPreorder hVY _)
  · intro W X g x
    have hWX : P.contextPreorder.le W.ctx X.ctx := leOfHom g
    have hVY : Q.contextPreorder.le (forward f W.ctx) (forward f X.ctx) := leOfHom ((coreContextFunctor f).map g)
    symm
    apply (op W.ctx _ _).1
    exact hp.observableNaturality W.ctx X.ctx _ _ x _ _ _ ((hm.context _ _).2 rfl)
      ((hm.context _ _).2 rfl) ((op _ _ _).2 rfl)
      (contextObservable_read P.contextPreorder hWX _) (contextObservable_read Q.contextPreorder hVY _)

/-- The native support comparison reads back to every candidate context/support point. -/
theorem read_support (hp : NativePoints P Q h) :
    IndependentFixedIndexedPointGraph.read (forward f) (fun W => (assemble f h hm hp).supportComp ⟨W⟩) = support h :=
  IndependentFixedIndexedPointGraph.read_assemble _ hm.context _ hp.supportRows

/-- The native axis comparison reads back to all active and inactive candidate pairs. -/
theorem read_axis (hp : NativePoints P Q h) :
    IndependentFixedIndexedPointGraph.read (forward f) (fun W => (assemble f h hm hp).axisComp ⟨W⟩) = axis h :=
  IndependentFixedIndexedPointGraph.read_assemble _ hm.context _ hp.axisRows

/-- The native observable comparison also retains every original candidate context point. -/
theorem read_observable (hp : NativePoints P Q h) :
    IndependentFixedIndexedPointGraph.read (forward f) (fun W => (assemble f h hm hp).observableComp ⟨W⟩) = observable h :=
  IndependentFixedIndexedPointGraph.read_assemble _ hm.context _ hp.observableRows

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRealization
