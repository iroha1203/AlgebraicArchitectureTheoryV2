import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointActionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFixedIndexedPointCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRealizationCompositionRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomAlgebraicCompositionFinite
import Formal.Util.AssertStandardAxioms

/-!
# Finite support for complete explicit realization composition

Fiber queries and actual Support, Axis, and Observable actions are reduced to
finite sets of the two original common Hom tables.

Implementation notes: action candidates bundle only the primitive point laws
needed to pull each intermediate cell back to an input fragment. A completed
realization supply is used only by existing comparison theorems and is not
stored in the finite-support data.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v uI uJ uK uS uM uT uX uY

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

namespace ExplicitRealization

/-- The three kinds of cells read by one actual action after a context-indexed
inverse graph has been composed. -/
inductive ActionCell (I : Type uI) (J : Type uJ)
    (S : I → Type uS) (T : J → Type uT) where
  | index (i : I) (j : J)
  | forward (i : I) (j : J) (x : S i) (y : T j)
  | backward (i : I) (j : J) (x : S i) (y : T j)

/-- If every composed index or fiber cell has a finite pullback to two original
declarations, then one actual action point has such a finite pullback as well. -/
theorem action_finite_support_of_cell_support
    {I : Type uI} {J : Type uJ} {S : I → Type uS} {T : J → Type uT}
    {X : Type uX} {Y : Type uY} {P : Type*}
    (left : P → X → Bool) (right : P → Y → Bool)
    (table : P → ActionCell I J S T → Bool)
    (laws : ∀ p, IndependentFixedIndexedPointGraph.InverseLaws
      (fun i j => table p (.index i j))
      (fun i j x y => table p (.forward i j x y))
      (fun i j x y => table p (.backward i j x y)))
    (p : P)
    (cellSupport : ∀ c, ∃ (D : Finset X) (E : Finset Y),
      ∀ p' : P, (∀ a ∈ D, left p a = left p' a) →
        (∀ a ∈ E, right p a = right p' a) → table p c = table p' c)
    (i i' : I) (j j' : J) (a : S i → S i') (y : T j) (z : T j') :
    ∃ (D : Finset X) (E : Finset Y),
      ∀ p' : P, (∀ q ∈ D, left p q = left p' q) →
        (∀ q ∈ E, right p q = right p' q) →
        IndependentFixedIndexedPointGraph.action
            (fun i j => table p (.index i j))
            (fun i j x y => table p (.forward i j x y))
            (fun i j x y => table p (.backward i j x y))
            (laws p) i i' j j' a y z =
          IndependentFixedIndexedPointGraph.action
            (fun i j => table p' (.index i j))
            (fun i j x y => table p' (.forward i j x y))
            (fun i j x y => table p' (.backward i j x y))
            (laws p') i i' j j' a y z := by
  classical
  obtain ⟨F, _, haction⟩ := IndependentFixedIndexedPointGraph.action_lifted_finite_support
    (fun i j => ActionCell.index i j)
    (fun i j x y => ActionCell.forward i j x y)
    (fun i j x y => ActionCell.backward i j x y)
    (table p) (laws p) i i' j j' a y z
  choose leftSupport rightSupport hsupport using cellSupport
  refine ⟨F.biUnion leftSupport, F.biUnion rightSupport, ?_⟩
  intro p' hleft hright
  apply haction (table p') (laws p')
  intro c hc
  apply hsupport c p'
  · intro q hq
    exact hleft q (Finset.mem_biUnion.mpr ⟨c, hc, hq⟩)
  · intro q hq
    exact hright q (Finset.mem_biUnion.mpr ⟨c, hc, hq⟩)

/-- Both directions of a composed dependent inverse graph have the same
three-cell support in the two original declarations. -/
theorem composeInverse_lifted_finite_support
    {I : Type uI} {J : Type uJ} {K : Type uK}
    {S : I → Type uS} {M : J → Type uM} {T : K → Type uT}
    {X : Type uX} {Y : Type uY}
    (leftIndex : I → J → X) (rightIndex : J → K → Y)
    (leftForward leftBackward : ∀ i j, S i → M j → X)
    (rightForward rightBackward : ∀ j l, M j → T l → Y)
    (h : X → Bool) (k : Y → Bool)
    (hp : ∀ i, ∃! j, h (leftIndex i j) = true)
    (hh : IndependentFixedIndexedPointGraph.InverseLaws
      (fun i j => h (leftIndex i j))
      (fun i j x y => h (leftForward i j x y))
      (fun i j x y => h (leftBackward i j x y)))
    (hk : IndependentFixedIndexedPointGraph.InverseLaws
      (fun j l => k (rightIndex j l))
      (fun j l x y => k (rightForward j l x y))
      (fun j l x y => k (rightBackward j l x y)))
    (d : Direction) (i : I) (l : K) (x : S i) (z : T l) :
    ∃ (D : Finset X) (E : Finset Y), D.card + E.card ≤ 3 ∧
      ∀ (h' : X → Bool) (k' : Y → Bool)
        (hp' : ∀ i, ∃! j, h' (leftIndex i j) = true)
        (hh' : IndependentFixedIndexedPointGraph.InverseLaws
          (fun i j => h' (leftIndex i j))
          (fun i j x y => h' (leftForward i j x y))
          (fun i j x y => h' (leftBackward i j x y)))
        (hk' : IndependentFixedIndexedPointGraph.InverseLaws
          (fun j l => k' (rightIndex j l))
          (fun j l x y => k' (rightForward j l x y))
          (fun j l x y => k' (rightBackward j l x y))),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        (match d with
          | .forward => IndependentFixedIndexedPointGraph.compose
              (fun i j => h (leftIndex i j)) hp
              (fun i j x y => h (leftForward i j x y)) hh.forward
              (fun j l x y => k (rightForward j l x y)) i l x z
          | .backward => IndependentFixedIndexedPointGraph.composeBackward
              (fun i j => h (leftIndex i j)) hp
              (fun i j x y => h (leftBackward i j x y))
              (fun j l => k (rightIndex j l))
              (fun j l x y => k (rightForward j l x y))
              (fun j l x y => k (rightBackward j l x y)) hk i l x z) =
        (match d with
          | .forward => IndependentFixedIndexedPointGraph.compose
              (fun i j => h' (leftIndex i j)) hp'
              (fun i j x y => h' (leftForward i j x y)) hh'.forward
              (fun j l x y => k' (rightForward j l x y)) i l x z
          | .backward => IndependentFixedIndexedPointGraph.composeBackward
              (fun i j => h' (leftIndex i j)) hp'
              (fun i j x y => h' (leftBackward i j x y))
              (fun j l => k' (rightIndex j l))
              (fun j l x y => k' (rightForward j l x y))
              (fun j l x y => k' (rightBackward j l x y)) hk' i l x z) := by
  obtain ⟨D, E, hcard, hs⟩ := IndependentFixedIndexedPointGraph.compose_lifted_finite_support
    leftIndex leftForward rightForward h k hp hh.forward i l x z
  refine ⟨D, E, hcard, ?_⟩
  intro h' k' hp' hh' hk' hD hE
  cases d with
  | forward => exact hs h' k' hp' hh'.forward hD hE
  | backward =>
    exact (congrFun (congrFun (congrFun (congrFun
      (IndependentFixedIndexedPointGraph.composeBackward_eq_forward
        (fun i j => h (leftIndex i j)) hp
        (fun i j x y => h (leftForward i j x y))
        (fun i j x y => h (leftBackward i j x y)) hh
        (fun j l => k (rightIndex j l))
        (fun j l x y => k (rightForward j l x y))
        (fun j l x y => k (rightBackward j l x y)) hk) i) l) x) z).trans
      ((hs h' k' hp' hh'.forward hD hE).trans
        (congrFun (congrFun (congrFun (congrFun
          (IndependentFixedIndexedPointGraph.composeBackward_eq_forward
            (fun i j => h' (leftIndex i j)) hp'
            (fun i j x y => h' (leftForward i j x y))
            (fun i j x y => h' (leftBackward i j x y)) hh'
            (fun j l => k' (rightIndex j l))
            (fun j l x y => k' (rightForward j l x y))
            (fun j l x y => k' (rightBackward j l x y)) hk') i) l) x) z).symm)

variable {U : AtomCarrier.{u}}
variable {A B C : ArchitectureObject U}

/-- The two primitive common tables and the laws needed to compose one
explicit realization declaration. -/
structure CompositionCandidate (A B C : ArchitectureObject U) where
  /-- First retained common table. -/
  left : Table.{u, v} U .explicit
  /-- Explicit realization point laws for the first table. -/
  leftLaws : PointLaws A B left
  /-- Unique intermediate context selected by the first table. -/
  leftContext : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints left W V = true
  /-- Second retained common table. -/
  right : Table.{u, v} U .explicit
  /-- Explicit realization point laws for the second table. -/
  rightLaws : PointLaws B C right

/-- View the composed context and support inverse rows as the three cells read
by the generic actual-action construction. -/
def supportActionTable (p : CompositionCandidate.{u, v} A B C) :
    ActionCell (ArchCtx A) (ArchCtx C) (fun W => W.Support) (fun Z => Z.Support) → Bool
  | .index W Z => IndependentIndexedCarrierGraph.composeIndex
      (contextPoints p.left) p.leftContext (contextPoints p.right) W Z
  | .forward W Z x z => composeSupport p.left p.leftLaws p.leftContext
      p.right p.rightLaws .forward W Z x z
  | .backward W Z x z => composeSupport p.left p.leftLaws p.leftContext
      p.right p.rightLaws .backward W Z x z

/-- The composed support action table retains the inverse-row laws proved for
the direct primitive composition. -/
theorem supportActionTable_laws (p : CompositionCandidate.{u, v} A B C) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (fun W Z => supportActionTable p (.index W Z))
      (fun W Z x z => supportActionTable p (.forward W Z x z))
      (fun W Z x z => supportActionTable p (.backward W Z x z)) :=
  composeSupport_inverseLaws p.left p.leftLaws p.leftContext p.right p.rightLaws

/-- Two original context cells determine one point of the composed context graph. -/
theorem composeContext_finite_support
    (h : Table.{u, v} U .explicit)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (W : ArchCtx A) (Z : ArchCtx C) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 2 ∧
      ∀ (h' : Table.{u, v} U .explicit)
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        IndependentIndexedCarrierGraph.composeIndex (contextPoints h) hctx (contextPoints k) W Z =
          IndependentIndexedCarrierGraph.composeIndex (contextPoints h') hctx' (contextPoints k') W Z := by
  classical
  let V := IndependentIndexedCarrierGraph.index (contextPoints h) hctx W
  refine ⟨{.atObjects A B (.context .forward W V)},
    {.atObjects B C (.context .forward V Z)}, by simp, ?_⟩
  intro h' hctx' k' hD hE
  have hleft : contextPoints h W
      (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) =
      contextPoints h' W
        (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) := by
    change h (.atObjects A B (.context .forward W
      (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W))) =
      h' (.atObjects A B (.context .forward W
        (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W)))
    exact hD _ (by simp [V])
  have hright : contextPoints k
      (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) Z =
      contextPoints k'
        (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) Z := by
    change k (.atObjects B C (.context .forward
      (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) Z)) =
      k' (.atObjects B C (.context .forward
        (IndependentIndexedCarrierGraph.index (contextPoints h) hctx W) Z))
    exact hE _ (by simp [V])
  exact IndependentIndexedCarrierGraph.composeIndex_point_support
    (contextPoints h) (contextPoints h') hctx hctx'
    (contextPoints k) (contextPoints k') W Z
    hleft hright

/-- Each direction of one composed support-fiber point uses at most three
original common query cells. -/
theorem composeSupport_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (d : Direction) (W : ArchCtx A) (Z : ArchCtx C) (x : W.Support) (z : Z.Support) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 3 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeSupport h hp hctx k kp d W Z x z =
          composeSupport h' hp' hctx' k' kp' d W Z x z := by
  obtain ⟨D, E, hcard, hs⟩ := composeInverse_lifted_finite_support
    (fun W V => Query.atObjects A B (.context .forward W V))
    (fun V Z => Query.atObjects B C (.context .forward V Z))
    (fun W V x y => Query.atObjects A B (.realization (.explicitSupport .forward W V x y)))
    (fun W V x y => Query.atObjects A B (.realization (.explicitSupport .backward W V x y)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitSupport .forward V Z y z)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitSupport .backward V Z y z)))
    h k hctx hp.supportRows kp.supportRows d W Z x z
  refine ⟨D, E, hcard, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  cases d with
  | forward => exact hs h' k' hctx' hp'.supportRows kp'.supportRows hD hE
  | backward => exact hs h' k' hctx' hp'.supportRows kp'.supportRows hD hE

/-- Every cell read by the composed actual support action is determined by
finite fragments of the two original common tables. -/
theorem supportActionTable_cell_finite_support
    (p : CompositionCandidate.{u, v} A B C)
    (c : ActionCell (ArchCtx A) (ArchCtx C)
      (fun W => W.Support) (fun Z => Z.Support)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ p' : CompositionCandidate.{u, v} A B C,
        (∀ a ∈ D, p.left a = p'.left a) →
        (∀ a ∈ E, p.right a = p'.right a) →
        supportActionTable p c = supportActionTable p' c := by
  cases c with
  | index W Z =>
    obtain ⟨D, E, _, hs⟩ := composeContext_finite_support
      p.left p.leftContext p.right W Z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftContext p'.right hD hE
  | forward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeSupport_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .forward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE
  | backward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeSupport_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .backward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE

/-- One actual support-action output is fixed by finite fragments of the two
original common declarations. -/
theorem composeActualSupport_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (W X : ArchCtx A) (V Y : ArchCtx C) (g : ContextMorphism W X)
    (y : V.Support) (z : Y.Support) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRealization h hp hctx k kp (.actualSupport W X V Y g y z) =
          composeRealization h' hp' hctx' k' kp' (.actualSupport W X V Y g y z) := by
  let p : CompositionCandidate.{u, v} A B C := ⟨h, hp, hctx, k, kp⟩
  obtain ⟨D, E, hs⟩ := action_finite_support_of_cell_support
    (fun p => p.left) (fun p => p.right) supportActionTable supportActionTable_laws p
    (supportActionTable_cell_finite_support p) W X V Y g.supportMap y z
  refine ⟨D, E, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  let p' : CompositionCandidate.{u, v} A B C := ⟨h', hp', hctx', k', kp'⟩
  exact hs p' hD hE

/-- Each direction of one composed axis-fiber point uses at most three
original common query cells. -/
theorem composeAxis_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (d : Direction) (W : ArchCtx A) (Z : ArchCtx C) (x : W.Axis) (z : Z.Axis) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 3 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeAxis h hp hctx k kp d W Z x z =
          composeAxis h' hp' hctx' k' kp' d W Z x z := by
  obtain ⟨D, E, hcard, hs⟩ := composeInverse_lifted_finite_support
    (fun W V => Query.atObjects A B (.context .forward W V))
    (fun V Z => Query.atObjects B C (.context .forward V Z))
    (fun W V x y => Query.atObjects A B (.realization (.explicitAxis .forward W V x y)))
    (fun W V x y => Query.atObjects A B (.realization (.explicitAxis .backward W V x y)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitAxis .forward V Z y z)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitAxis .backward V Z y z)))
    h k hctx hp.axisRows kp.axisRows d W Z x z
  refine ⟨D, E, hcard, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  cases d with
  | forward => exact hs h' k' hctx' hp'.axisRows kp'.axisRows hD hE
  | backward => exact hs h' k' hctx' hp'.axisRows kp'.axisRows hD hE

/-- Each direction of one composed observable-fiber point uses at most three
original common query cells. -/
theorem composeObservable_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (d : Direction) (W : ArchCtx A) (Z : ArchCtx C)
    (x : W.Observable) (z : Z.Observable) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)), D.card + E.card ≤ 3 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeObservable h hp hctx k kp d W Z x z =
          composeObservable h' hp' hctx' k' kp' d W Z x z := by
  obtain ⟨D, E, hcard, hs⟩ := composeInverse_lifted_finite_support
    (fun W V => Query.atObjects A B (.context .forward W V))
    (fun V Z => Query.atObjects B C (.context .forward V Z))
    (fun W V x y => Query.atObjects A B (.realization (.explicitObservable .forward W V x y)))
    (fun W V x y => Query.atObjects A B (.realization (.explicitObservable .backward W V x y)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitObservable .forward V Z y z)))
    (fun V Z y z => Query.atObjects B C (.realization (.explicitObservable .backward V Z y z)))
    h k hctx hp.observableRows kp.observableRows d W Z x z
  refine ⟨D, E, hcard, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  cases d with
  | forward => exact hs h' k' hctx' hp'.observableRows kp'.observableRows hD hE
  | backward => exact hs h' k' hctx' hp'.observableRows kp'.observableRows hD hE


/-- View the composed context and axis inverse rows as an actual-action table. -/
def axisActionTable (p : CompositionCandidate.{u, v} A B C) :
    ActionCell (ArchCtx A) (ArchCtx C) (fun W => W.Axis) (fun Z => Z.Axis) → Bool
  | .index W Z => IndependentIndexedCarrierGraph.composeIndex
      (contextPoints p.left) p.leftContext (contextPoints p.right) W Z
  | .forward W Z x z => composeAxis p.left p.leftLaws p.leftContext
      p.right p.rightLaws .forward W Z x z
  | .backward W Z x z => composeAxis p.left p.leftLaws p.leftContext
      p.right p.rightLaws .backward W Z x z

/-- The composed axis action table retains its inverse-row laws. -/
theorem axisActionTable_laws (p : CompositionCandidate.{u, v} A B C) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (fun W Z => axisActionTable p (.index W Z))
      (fun W Z x z => axisActionTable p (.forward W Z x z))
      (fun W Z x z => axisActionTable p (.backward W Z x z)) :=
  composeAxis_inverseLaws p.left p.leftLaws p.leftContext p.right p.rightLaws

/-- Every cell read by the composed actual axis action is determined by finite
fragments of the original tables. -/
theorem axisActionTable_cell_finite_support
    (p : CompositionCandidate.{u, v} A B C)
    (c : ActionCell (ArchCtx A) (ArchCtx C) (fun W => W.Axis) (fun Z => Z.Axis)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ p' : CompositionCandidate.{u, v} A B C,
        (∀ a ∈ D, p.left a = p'.left a) →
        (∀ a ∈ E, p.right a = p'.right a) →
        axisActionTable p c = axisActionTable p' c := by
  cases c with
  | index W Z =>
    obtain ⟨D, E, _, hs⟩ := composeContext_finite_support
      p.left p.leftContext p.right W Z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftContext p'.right hD hE
  | forward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeAxis_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .forward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE
  | backward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeAxis_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .backward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE

/-- One actual axis-action output is fixed by finite fragments of the two
original common declarations. -/
theorem composeActualAxis_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (W X : ArchCtx A) (V Y : ArchCtx C) (g : ContextMorphism W X)
    (y : V.Axis) (z : Y.Axis) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRealization h hp hctx k kp (.actualAxis W X V Y g y z) =
          composeRealization h' hp' hctx' k' kp' (.actualAxis W X V Y g y z) := by
  let p : CompositionCandidate.{u, v} A B C := ⟨h, hp, hctx, k, kp⟩
  obtain ⟨D, E, hs⟩ := action_finite_support_of_cell_support
    (fun p => p.left) (fun p => p.right) axisActionTable axisActionTable_laws p
    (axisActionTable_cell_finite_support p) W X V Y g.axisMap y z
  refine ⟨D, E, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  let p' : CompositionCandidate.{u, v} A B C := ⟨h', hp', hctx', k', kp'⟩
  exact hs p' hD hE

/-- View the composed context and observable inverse rows as the action table
used in the contravariant direction. -/
def observableActionTable (p : CompositionCandidate.{u, v} A B C) :
    ActionCell (ArchCtx A) (ArchCtx C)
      (fun W => W.Observable) (fun Z => Z.Observable) → Bool
  | .index W Z => IndependentIndexedCarrierGraph.composeIndex
      (contextPoints p.left) p.leftContext (contextPoints p.right) W Z
  | .forward W Z x z => composeObservable p.left p.leftLaws p.leftContext
      p.right p.rightLaws .forward W Z x z
  | .backward W Z x z => composeObservable p.left p.leftLaws p.leftContext
      p.right p.rightLaws .backward W Z x z

/-- The composed observable action table retains its inverse-row laws. -/
theorem observableActionTable_laws (p : CompositionCandidate.{u, v} A B C) :
    IndependentFixedIndexedPointGraph.InverseLaws
      (fun W Z => observableActionTable p (.index W Z))
      (fun W Z x z => observableActionTable p (.forward W Z x z))
      (fun W Z x z => observableActionTable p (.backward W Z x z)) :=
  composeObservable_inverseLaws p.left p.leftLaws p.leftContext p.right p.rightLaws

/-- Every cell read by the composed actual observable action is fixed by
finite fragments of the original declarations. -/
theorem observableActionTable_cell_finite_support
    (p : CompositionCandidate.{u, v} A B C)
    (c : ActionCell (ArchCtx A) (ArchCtx C)
      (fun W => W.Observable) (fun Z => Z.Observable)) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ p' : CompositionCandidate.{u, v} A B C,
        (∀ a ∈ D, p.left a = p'.left a) →
        (∀ a ∈ E, p.right a = p'.right a) →
        observableActionTable p c = observableActionTable p' c := by
  cases c with
  | index W Z =>
    obtain ⟨D, E, _, hs⟩ := composeContext_finite_support
      p.left p.leftContext p.right W Z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftContext p'.right hD hE
  | forward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeObservable_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .forward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE
  | backward W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeObservable_finite_support
      p.left p.leftLaws p.leftContext p.right p.rightLaws .backward W Z x z
    refine ⟨D, E, ?_⟩
    intro p' hD hE
    exact hs p'.left p'.leftLaws p'.leftContext p'.right p'.rightLaws hD hE

/-- One contravariant actual observable-action output is fixed by finite
fragments of the two original common declarations. -/
theorem composeActualObservable_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (W X : ArchCtx A) (V Y : ArchCtx C) (g : ContextMorphism W X)
    (y : Y.Observable) (z : V.Observable) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ a ∈ D, h a = h' a) → (∀ a ∈ E, k a = k' a) →
        composeRealization h hp hctx k kp (.actualObservable W X V Y g y z) =
          composeRealization h' hp' hctx' k' kp' (.actualObservable W X V Y g y z) := by
  let p : CompositionCandidate.{u, v} A B C := ⟨h, hp, hctx, k, kp⟩
  obtain ⟨D, E, hs⟩ := action_finite_support_of_cell_support
    (fun p => p.left) (fun p => p.right) observableActionTable observableActionTable_laws p
    (observableActionTable_cell_finite_support p) X W Y V g.observableRestrict y z
  refine ⟨D, E, ?_⟩
  intro h' hp' hctx' k' kp' hD hE
  let p' : CompositionCandidate.{u, v} A B C := ⟨h', hp', hctx', k', kp'⟩
  exact hs p' hD hE

/-- Every explicit realization-composition output is determined by finite
fragments of the two original common declarations, including actual actions. -/
theorem composeRealization_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws A B h)
    (hctx : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h W V = true)
    (k : Table.{u, v} U .explicit) (kp : PointLaws B C k)
    (a : RealizationQuery A C .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws A B h')
        (hctx' : ∀ W : ArchCtx A, ∃! V : ArchCtx B, contextPoints h' W V = true)
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws B C k'),
        (∀ q ∈ D, h q = h' q) → (∀ q ∈ E, k q = k' q) →
        composeRealization h hp hctx k kp a =
          composeRealization h' hp' hctx' k' kp' a := by
  cases a with
  | explicitSupport d W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeSupport_finite_support h hp hctx k kp d W Z x z
    exact ⟨D, E, hs⟩
  | explicitAxis d W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeAxis_finite_support h hp hctx k kp d W Z x z
    exact ⟨D, E, hs⟩
  | explicitObservable d W Z x z =>
    obtain ⟨D, E, _, hs⟩ := composeObservable_finite_support h hp hctx k kp d W Z x z
    exact ⟨D, E, hs⟩
  | actualSupport W X V Y g y z =>
    exact composeActualSupport_finite_support h hp hctx k kp W X V Y g y z
  | actualAxis W X V Y g y z =>
    exact composeActualAxis_finite_support h hp hctx k kp W X V Y g y z
  | actualObservable W X V Y g y z =>
    exact composeActualObservable_finite_support h hp hctx k kp W X V Y g y z

end ExplicitRealization

namespace Composition

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (ep : GeometryComponents.ExplicitPoints s t p)
variable (eq : GeometryComponents.ExplicitPoints t r q)

/-- Every explicit realization output, including an actual context action, is
fixed by two actual finite quotient fragments. -/
theorem explicitRealization_finite_fragment
    (a : RealizationQuery (assemble s).core.object (assemble r).core.object .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
        (ep' : GeometryComponents.ExplicitPoints s t p')
        (eq' : GeometryComponents.ExplicitPoints t r q'),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        explicitRealizationRows s t r p hp q ep eq a =
          explicitRealizationRows s t r p' hp' q' ep' eq' a := by
  obtain ⟨D, E, hs⟩ := ExplicitRealization.composeRealization_finite_support
    (PackageAssembly.retained s.1 t.1 p).table ep hp.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q).table eq a
  refine ⟨D, E, ?_⟩
  intro p' hp' q' ep' eq' hD hE
  exact hs (PackageAssembly.retained s.1 t.1 p').table ep' hp'.contextRows.forward
    (PackageAssembly.retained t.1 r.1 q').table eq'
    ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRealization
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
