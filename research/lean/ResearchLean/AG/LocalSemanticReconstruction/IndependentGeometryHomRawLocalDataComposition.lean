import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawCompositionRows
import Formal.Util.AssertStandardAxioms

/-!
# Primitive composition of raw dependent local-data points

Implementation notes: a backward context point selects the middle context and
a forward coordinate point selects the middle coordinate. Three original
local-data type responses then select the fiber carriers. Values compose by
the existing two-point inverse-graph construction. Missing type responses or
inactive context and coordinate candidates give the constant false row.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site
open IndependentRawCandidate (coord)

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
variable (s : IndependentRawCandidate.Table.{u, v} A) (t : IndependentRawCandidate.Table.{u, v} B)
variable (r : IndependentRawCandidate.Table.{u, v} C)
variable (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)
variable (k : Table.{u, v} U .explicit) (hk : PointLaws t r k)

/-- Compose one dependent fiber after its context and coordinate points have selected both input rows. -/
def composeLocalDataFiber (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (D E F : Type u) (d : D) (e : E) (f : F)
    (hW : contextPoints h W V = true) (hV : contextPoints k V Z = true)
    (hd : coordinatePoint h W V D E d e = true) (he : coordinatePoint k V Z E F e f = true) :
    IndependentInverseGraph.Table.{u, u} :=
  match hs : (s (.localData W D d)).down, ht : (t (.localData V E e)).down,
      hr : (r (.localData Z F f)).down with
  | some L, some M, some N =>
      IndependentInverseGraph.compose L M N (InverseRows.localData h A B W V D E d e)
        (hp.localDataRows W V D E d e L M hW hd hs ht)
        (InverseRows.localData k B C V Z E F e f) (hk.localDataRows V Z E F e f M N hV he ht hr)
  | _, _, _ => fun _ => false

/-- Three present type responses expose the original dependent inverse-graph composition. -/
theorem composeLocalDataFiber_some (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (D E F : Type u) (d : D) (e : E) (f : F)
    (hW : contextPoints h W V = true) (hV : contextPoints k V Z = true)
    (hd : coordinatePoint h W V D E d e = true) (he : coordinatePoint k V Z E F e f = true)
    (L M N : Type u) (hs : (s (.localData W D d)).down = some L)
    (ht : (t (.localData V E e)).down = some M) (hr : (r (.localData Z F f)).down = some N) :
    composeLocalDataFiber s t r h hp k hk W V Z D E F d e f hW hV hd he =
      IndependentInverseGraph.compose L M N (InverseRows.localData h A B W V D E d e)
        (hp.localDataRows W V D E d e L M hW hd hs ht)
        (InverseRows.localData k B C V Z E F e f) (hk.localDataRows V Z E F e f M N hV he ht hr) := by
  unfold composeLocalDataFiber
  split
  · rename_i L' M' N' hs' ht' hr'
    have hL : L' = L := Option.some.inj (hs'.symm.trans hs)
    have hM : M' = M := Option.some.inj (ht'.symm.trans ht)
    have hN : N' = N := Option.some.inj (hr'.symm.trans hr)
    subst L' M' N'
    rfl
  · rename_i hn
    exact False.elim (hn L M N hs ht hr)

variable (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true)

/-- Compose all raw local-data candidates by selecting only a middle context and a middle coordinate point. -/
def composeLocalData (W : ArchCtx A) (Z : ArchCtx C) (D F : Type u) (d : D) (f : F) :
    IndependentInverseGraph.Table.{u, u} := by
  classical
  let V := IndependentIndexedCarrierGraph.index (fun Z V => contextPoints k V Z) hq Z
  have hV : contextPoints k V Z = true := (IndependentIndexedCarrierGraph.active_iff _ hq Z V).2 rfl
  exact if hW : contextPoints h W V = true then
    if hD : D = coord s W then
      let e := IndependentInverseGraph.assemble (coord s W) (coord t V)
        (InverseRows.coordinate h A B W V) (hp.coordinateRows W V hW) (hD ▸ d)
      have hd : coordinatePoint h W V D (coord t V) d e = true := by
        cases hD
        exact (IndependentCarrierGraph.graph _ _ _ (hp.coordinateRows W V hW).forward.2).edge_target d
      if he : coordinatePoint k V Z (coord t V) F e f = true then
        composeLocalDataFiber s t r h hp k hk W V Z D (coord t V) F d e f hW hV hd he
      else fun _ => false
    else fun _ => false
  else fun _ => false

/-- A true pair of context points and two coordinate points selects the intended dependent composition. -/
theorem composeLocalData_active (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (d : coord s W) (e : coord t V) (F : Type u) (f : F)
    (hW : contextPoints h W V = true) (hV : contextPoints k V Z = true)
    (hd : coordinatePoint h W V (coord s W) (coord t V) d e = true)
    (he : coordinatePoint k V Z (coord t V) F e f = true) :
    composeLocalData s t r h hp k hk hq W Z (coord s W) F d f =
      composeLocalDataFiber s t r h hp k hk W V Z (coord s W) (coord t V) F d e f hW hV hd he := by
  have hVe := (IndependentIndexedCarrierGraph.active_iff (fun Z V => contextPoints k V Z) hq Z V).1 hV
  subst V
  have heq := (IndependentCarrierGraph.graph _ _ _ (hp.coordinateRows W _ hW).forward.2).edge_eq_true_iff_target_eq d e
  have heq' : IndependentInverseGraph.assemble _ _ _ (hp.coordinateRows W _ hW) d = e := heq.1 hd
  subst e
  simp only [composeLocalData, hW, dif_pos, eq_self, he]

/-- A false first backward context point makes every dependent local-data candidate false. -/
theorem composeLocalData_inactive_context (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (D F : Type u) (d : D) (f : F)
    (hV : contextPoints k V Z = true) (hW : contextPoints h W V = false) :
    composeLocalData s t r h hp k hk hq W Z D F d f = fun _ => false := by
  have hVe := (IndependentIndexedCarrierGraph.active_iff (fun Z V => contextPoints k V Z) hq Z V).1 hV
  subst V
  simp only [composeLocalData, hW, Bool.false_eq_true, ↓reduceDIte]

/-- A candidate source-coordinate carrier different from its primitive declaration has no local-data values. -/
theorem composeLocalData_inactive_carrier (W : ArchCtx A) (Z : ArchCtx C)
    (D F : Type u) (d : D) (f : F) (hD : D ≠ coord s W) :
    composeLocalData s t r h hp k hk hq W Z D F d f = fun _ => false := by
  classical
  simp only [composeLocalData, hD, ↓reduceDIte]
  split <;> rfl

/-- A false second coordinate point removes all dependent values after the middle coordinate is selected. -/
theorem composeLocalData_inactive_coordinate (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (d : coord s W) (e : coord t V) (F : Type u) (f : F)
    (hW : contextPoints h W V = true) (hV : contextPoints k V Z = true)
    (hd : coordinatePoint h W V (coord s W) (coord t V) d e = true)
    (he : coordinatePoint k V Z (coord t V) F e f = false) :
    composeLocalData s t r h hp k hk hq W Z (coord s W) F d f = fun _ => false := by
  have hVe := (IndependentIndexedCarrierGraph.active_iff (fun Z V => contextPoints k V Z) hq Z V).1 hV
  subst V
  have heq := (IndependentCarrierGraph.graph _ _ _ (hp.coordinateRows W _ hW).forward.2).edge_eq_true_iff_target_eq d e
  have heq' : IndependentInverseGraph.assemble _ _ _ (hp.coordinateRows W _ hW) d = e := heq.1 hd
  subst e
  simp only [composeLocalData, hW, eq_self, he, Bool.false_eq_true, ↓reduceDIte]

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
