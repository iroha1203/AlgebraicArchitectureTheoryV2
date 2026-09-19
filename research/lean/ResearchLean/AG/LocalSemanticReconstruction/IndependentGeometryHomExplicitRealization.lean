import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointGraphs
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPackagePoints
import ResearchLean.AG.LocalSemanticReconstruction.IndependentExplicitRealizationReadings
import Formal.Util.AssertStandardAxioms

/-!
# Explicit realization from common primitive Hom points

Implementation notes: carrier inverse graphs and reading equivalences determine
transport of every actual context morphism by conjugation. This avoids a second
total-function construction whose outputs are already forced by naturality.
The original action queries remain in
the local table: their point equations compare that action with carrier edges,
and their inactive rows are false. No completed context action is supplied.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U}

/-- The primitive forward context graph activates the three inverse fiber graphs. -/
def contextPoints (h : Table.{u, v} U .explicit) (W : ArchCtx A) (V : ArchCtx B) : Bool :=
  h (.atObjects A B (.context .forward W V))

/-- Each support direction retains the same ordered source and target point pair. -/
def support (h : Table.{u, v} U .explicit) (d : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Support) (y : V.Support) : Bool := h (.atObjects A B (.realization (.explicitSupport d W V x y)))

/-- Each axis direction retains its actual context and value references. -/
def axis (h : Table.{u, v} U .explicit) (d : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Axis) (y : V.Axis) : Bool := h (.atObjects A B (.realization (.explicitAxis d W V x y)))

/-- Observable fiber equivalences are distinct from the observable-ring component. -/
def observable (h : Table.{u, v} U .explicit) (d : Direction) (W : ArchCtx A) (V : ArchCtx B)
    (x : W.Observable) (y : V.Observable) : Bool := h (.atObjects A B (.realization (.explicitObservable d W V x y)))

/-- A point of the retained actual support action. -/
def actualSupport (h : Table.{u, v} U .explicit) (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : V.Support) (z : Y.Support) : Bool :=
  h (.atObjects A B (.realization (.actualSupport W X V Y g y z)))

/-- A point of the retained actual axis action. -/
def actualAxis (h : Table.{u, v} U .explicit) (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : V.Axis) (z : Y.Axis) : Bool :=
  h (.atObjects A B (.realization (.actualAxis W X V Y g y z)))

/-- The observable action is contravariant in the actual context morphism. -/
def actualObservable (h : Table.{u, v} U .explicit) (W X : ArchCtx A) (V Y : ArchCtx B)
    (g : ContextMorphism W X) (y : Y.Observable) (z : V.Observable) : Bool :=
  h (.atObjects A B (.realization (.actualObservable W X V Y g y z)))

/-- Inverse, reading, and action laws compare primitive cells without a selected native Hom. -/
structure PointLaws (A B : ArchitectureObject U) (h : Table.{u, v} U .explicit) : Prop where
  /-- Forward and reverse support rows define inverse fiber maps. -/
  supportRows : IndependentFixedIndexedPointGraph.InverseLaws
    (contextPoints (A := A) (B := B) h) (support h .forward) (support h .backward)
  /-- Axis rows define inverse fiber maps independently. -/
  axisRows : IndependentFixedIndexedPointGraph.InverseLaws
    (contextPoints (A := A) (B := B) h) (axis h .forward) (axis h .backward)
  /-- Observable rows define inverse fiber maps in the same point ordering. -/
  observableRows : IndependentFixedIndexedPointGraph.InverseLaws
    (contextPoints (A := A) (B := B) h) (observable h .forward) (observable h .backward)
  /-- Support reading is preserved and reflected at true carrier and Atom points. -/
  supportReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y a b,
    contextPoints h W V = true → support h .forward W V x y = true →
    h (.atom .forward a b) = true → (W.minimal.supportReads x a ↔ V.minimal.supportReads y b)
  /-- Axis reading is preserved and reflected. -/
  axisReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y,
    contextPoints h W V = true → axis h .forward W V x y = true →
    (W.minimal.axisReads x ↔ V.minimal.axisReads y)
  /-- Observable reading is preserved and reflected. -/
  observableReads : ∀ (W : ArchCtx A) (V : ArchCtx B) x y,
    contextPoints h W V = true → observable h .forward W V x y = true →
    (W.minimal.observableReads x ↔ V.minimal.observableReads y)
  /-- Either inactive context pair makes an actual support cell false. -/
  supportInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g y z,
    contextPoints h W V = false ∨ contextPoints h X Y = false → actualSupport h W X V Y g y z = false
  /-- Either inactive context pair makes an actual axis cell false. -/
  axisInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g y z,
    contextPoints h W V = false ∨ contextPoints h X Y = false → actualAxis h W X V Y g y z = false
  /-- Either inactive context pair makes an actual observable cell false. -/
  observableInactive : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g y z,
    contextPoints h W V = false ∨ contextPoints h X Y = false → actualObservable h W X V Y g y z = false
  /-- Every actual support action cell agrees with its forward carrier edge. -/
  supportAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g x y z,
    contextPoints h W V = true → contextPoints h X Y = true → support h .forward W V x y = true →
    actualSupport h W X V Y g y z = support h .forward X Y (g.supportMap x) z
  /-- Every actual axis action cell agrees with its forward carrier edge. -/
  axisAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g x y z,
    contextPoints h W V = true → contextPoints h X Y = true → axis h .forward W V x y = true →
    actualAxis h W X V Y g y z = axis h .forward X Y (g.axisMap x) z
  /-- The observable action equation retains the reverse restriction direction. -/
  observableAction : ∀ (W X : ArchCtx A) (V Y : ArchCtx B) g x y z,
    contextPoints h W V = true → contextPoints h X Y = true → observable h .forward X Y x y = true →
    actualObservable h W X V Y g y z = observable h .forward W V (g.observableRestrict x) z

variable {P Q : AATCorePackage U}

/-- Comparison premises identify only the reconstructed context and Atom graphs. -/
structure Maps (f : PackageTotalHom P Q) (h : Table.{u, v} U .explicit) : Prop where
  /-- Context images agree with the common primitive context points. -/
  context : ∀ (W : ArchCtx P.object) (V : ArchCtx Q.object),
    contextPoints h W V = true ↔ ((coreContextFunctor f).obj ⟨W⟩).ctx = V
  /-- Atom images agree with the common primitive Atom points. -/
  atom : ∀ a b, h (.atom .forward a b) = true ↔ f.upper.atomEquiv a = b

variable (f : PackageTotalHom P Q) (h : Table.{u, v} U .explicit) (hm : Maps f h)

/-- The raw context reference of the independently reconstructed forward image. -/
def forward (W : ArchCtx P.object) : ArchCtx Q.object := ((coreContextFunctor f).obj ⟨W⟩).ctx

variable (hp : PointLaws P.object Q.object h)

/-- Assemble support equivalences using both independent graph directions. -/
def supportEquiv (W : ArchCtx P.object) : W.Support ≃ (forward f W).Support :=
  IndependentFixedIndexedPointGraph.assembleEquiv (forward f) hm.context
    (support h .forward) (support h .backward) hp.supportRows W

/-- Assemble axis equivalences using both independent graph directions. -/
def axisEquiv (W : ArchCtx P.object) : W.Axis ≃ (forward f W).Axis :=
  IndependentFixedIndexedPointGraph.assembleEquiv (forward f) hm.context
    (axis h .forward) (axis h .backward) hp.axisRows W

/-- Assemble observable equivalences using both independent graph directions. -/
def observableEquiv (W : ArchCtx P.object) : W.Observable ≃ (forward f W).Observable :=
  IndependentFixedIndexedPointGraph.assembleEquiv (forward f) hm.context
    (observable h .forward) (observable h .backward) hp.observableRows W

/-- Construct the native value table; conjugation supplies each actual context action. -/
def valueTable : IndependentExplicitRealization.Table f
  | .support W x => supportEquiv f h hm hp W.ctx x
  | .supportBack W y => (supportEquiv f h hm hp W.ctx).symm y
  | .axis W x => axisEquiv f h hm hp W.ctx x
  | .axisBack W y => (axisEquiv f h hm hp W.ctx).symm y
  | .observable W x => observableEquiv f h hm hp W.ctx x
  | .observableBack W y => (observableEquiv f h hm hp W.ctx).symm y
  | @IndependentExplicitRealization.Query.contextSupport _ _ _ _ W X g y =>
    supportEquiv f h hm hp X.ctx (g.supportMap ((supportEquiv f h hm hp W.ctx).symm y))
  | @IndependentExplicitRealization.Query.contextAxis _ _ _ _ W X g y =>
    axisEquiv f h hm hp X.ctx (g.axisMap ((axisEquiv f h hm hp W.ctx).symm y))
  | @IndependentExplicitRealization.Query.contextObservable _ _ _ _ W X g y =>
    observableEquiv f h hm hp W.ctx (g.observableRestrict ((observableEquiv f h hm hp X.ctx).symm y))

/-- Primitive inverse and reading clauses prove all native value-table laws. -/
theorem valueTable_isLawful : IndependentExplicitRealization.IsLawful (valueTable f h hm hp) where
  support_left W := (supportEquiv f h hm hp W.ctx).left_inv
  support_right W := (supportEquiv f h hm hp W.ctx).right_inv
  axis_left W := (axisEquiv f h hm hp W.ctx).left_inv
  axis_right W := (axisEquiv f h hm hp W.ctx).right_inv
  observable_left W := (observableEquiv f h hm hp W.ctx).left_inv
  observable_right W := (observableEquiv f h hm hp W.ctx).right_inv
  supportReads W x a := hp.supportReads W.ctx _ x _ a _ ((hm.context _ _).2 rfl)
    ((IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.supportRows.forward _ _ _).2 rfl)
    ((hm.atom _ _).2 rfl)
  axisReads W x := hp.axisReads W.ctx _ x _ ((hm.context _ _).2 rfl)
    ((IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.axisRows.forward _ _ _).2 rfl)
  observableReads W x := hp.observableReads W.ctx _ x _ ((hm.context _ _).2 rfl)
    ((IndependentFixedIndexedPointGraph.point_iff (forward f) hm.context _ hp.observableRows.forward _ _ _).2 rfl)
  support_naturality g x := by simp only [valueTable, Equiv.symm_apply_apply]
  axis_naturality g x := by simp only [valueTable, Equiv.symm_apply_apply]
  observable_naturality g x := by simp only [valueTable, Equiv.symm_apply_apply]

/-- Assemble the entire explicit realization, including preservation of actual restrictions. -/
def assemble : ExplicitRealizationTransportSupply P Q f :=
  IndependentExplicitRealization.assemble (valueTable f h hm hp) (valueTable_isLawful f h hm hp)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
