import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawCompositionFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawLocalDataComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseCompositionFinite
import Formal.Util.AssertStandardAxioms

/-!
# Finite support for explicit raw local-data composition

Coordinate, relation, and dependent local-data rows are reduced to finite
fragments of the two original common Hom declarations.

Implementation notes: local-data support separately tracks the backward
context, intermediate coordinate, three type responses, and value graph. It
does not reuse coordinate support as a substitute for the dependent row.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site IndependentGeometryTableAssembly

namespace ExplicitRaw

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}
variable (s : IndependentRawCandidate.Table.{u, v} A)
variable (t : IndependentRawCandidate.Table.{u, v} B)
variable (r : IndependentRawCandidate.Table.{u, v} C)

/-- At active context and coordinate points, one local-data fiber output uses
at most two original local-data cells. Missing object responses use none. -/
theorem composeLocalDataFiber_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)
    (k : Table.{u, v} U .explicit) (kp : PointLaws t r k)
    (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (D E F : Type u) (d : D) (e : E) (f : F)
    (hW : contextPoints h W V = true) (hV : contextPoints k V Z = true)
    (hd : coordinatePoint h W V D E d e = true)
    (he : coordinatePoint k V Z E F e f = true)
    (a : IndependentInverseGraph.Query.{u, u}) :
    ∃ (L R : Finset (Query.{u, v} U .explicit)), L.card + R.card ≤ 2 ∧
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws s t h')
        (k' : Table.{u, v} U .explicit) (kp' : PointLaws t r k')
        (hW' : contextPoints h' W V = true) (hV' : contextPoints k' V Z = true)
        (hd' : coordinatePoint h' W V D E d e = true)
        (he' : coordinatePoint k' V Z E F e f = true),
        (∀ q ∈ L, h q = h' q) → (∀ q ∈ R, k q = k' q) →
        composeLocalDataFiber s t r h hp k kp W V Z D E F d e f hW hV hd he a =
          composeLocalDataFiber s t r h' hp' k' kp' W V Z D E F d e f hW' hV' hd' he' a := by
  classical
  cases hs : (s (.localData W D d)).down with
  | none =>
    refine ⟨∅, ∅, by simp, ?_⟩
    intro h' hp' k' kp' hW' hV' hd' he' _ _
    simp [composeLocalDataFiber, hs]
  | some SL =>
    cases ht : (t (.localData V E e)).down with
    | none =>
      refine ⟨∅, ∅, by simp, ?_⟩
      intro h' hp' k' kp' hW' hV' hd' he' _ _
      simp [composeLocalDataFiber, hs, ht]
    | some TM =>
      cases hr : (r (.localData Z F f)).down with
      | none =>
        refine ⟨∅, ∅, by simp, ?_⟩
        intro h' hp' k' kp' hW' hV' hd' he' _ _
        simp [composeLocalDataFiber, hs, ht, hr]
      | some RN =>
        obtain ⟨L, R, hcard, hsupport⟩ := IndependentInverseGraph.compose_finite_support
          SL TM RN (InverseRows.localData h A B W V D E d e)
          (hp.localDataRows W V D E d e SL TM hW hd hs ht)
          (InverseRows.localData k B C V Z E F e f)
          (kp.localDataRows V Z E F e f TM RN hV he ht hr) a
        let leftQuery : IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
          | .forward q => .atObjects A B (.raw (.localData .forward W V D E d e q))
          | .backward q => .atObjects A B (.raw (.localData .backward W V D E d e (InverseRows.reverse q)))
        let rightQuery : IndependentInverseGraph.Query.{u, u} → Query.{u, v} U .explicit
          | .forward q => .atObjects B C (.raw (.localData .forward V Z E F e f q))
          | .backward q => .atObjects B C (.raw (.localData .backward V Z E F e f (InverseRows.reverse q)))
        refine ⟨L.image leftQuery, R.image rightQuery,
          (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hcard, ?_⟩
        intro h' hp' k' kp' hW' hV' hd' he' hL hR
        have hv := hsupport (InverseRows.localData h' A B W V D E d e)
          (hp'.localDataRows W V D E d e SL TM hW' hd' hs ht)
          (InverseRows.localData k' B C V Z E F e f)
          (kp'.localDataRows V Z E F e f TM RN hV' he' ht hr)
          (by
            intro q hq
            cases q with
            | forward q => exact hL _ (Finset.mem_image_of_mem _ hq)
            | backward q => exact hL _ (Finset.mem_image_of_mem _ hq))
          (by
            intro q hq
            cases q with
            | forward q => exact hR _ (Finset.mem_image_of_mem _ hq)
            | backward q => exact hR _ (Finset.mem_image_of_mem _ hq))
        exact (congrFun (composeLocalDataFiber_some s t r h hp k kp W V Z D E F d e f
          hW hV hd he SL TM RN hs ht hr) a).trans
          (hv.trans (congrFun (composeLocalDataFiber_some s t r h' hp' k' kp' W V Z
            D E F d e f hW' hV' hd' he' SL TM RN hs ht hr) a).symm)

/-- Every dependent local-data composition point is determined by finite
fragments of the two original common declarations. -/
theorem composeLocalData_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)
    (k : Table.{u, v} U .explicit)
    (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true)
    (kp : PointLaws t r k)
    (W : ArchCtx A) (Z : ArchCtx C) (D F : Type u) (d : D) (f : F)
    (a : IndependentInverseGraph.Query.{u, u}) :
    ∃ (L R : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws s t h')
        (k' : Table.{u, v} U .explicit)
        (hq' : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k' V Z = true)
        (kp' : PointLaws t r k'),
        (∀ q ∈ L, h q = h' q) → (∀ q ∈ R, k q = k' q) →
        composeLocalData s t r h hp k kp hq W Z D F d f a =
          composeLocalData s t r h' hp' k' kp' hq' W Z D F d f a := by
  classical
  by_cases hD : D = IndependentRawCandidate.coord s W
  · subst D
    let V := IndependentIndexedCarrierGraph.index
      (fun Z V => contextPoints k V Z) hq Z
    have hV : contextPoints k V Z = true :=
      (IndependentIndexedCarrierGraph.active_iff _ hq Z V).2 rfl
    let leftContext : Query.{u, v} U .explicit :=
      .atObjects A B (.context .backward W V)
    let rightContext : Query.{u, v} U .explicit :=
      .atObjects B C (.context .backward V Z)
    by_cases hWt : contextPoints h W V = true
    · let e := IndependentInverseGraph.assemble
        (IndependentRawCandidate.coord s W) (IndependentRawCandidate.coord t V)
        (InverseRows.coordinate h A B W V) (hp.coordinateRows W V hWt) d
      have hd : coordinatePoint h W V (IndependentRawCandidate.coord s W)
          (IndependentRawCandidate.coord t V) d e = true :=
        (IndependentCarrierGraph.graph _ _ _
          (hp.coordinateRows W V hWt).forward.2).edge_target d
      let leftCoordinate : Query.{u, v} U .explicit :=
        .atObjects A B (.raw (.coordinate .forward W V
          (.edge (IndependentRawCandidate.coord s W)
            (IndependentRawCandidate.coord t V) d e)))
      let rightCoordinate : Query.{u, v} U .explicit :=
        .atObjects B C (.raw (.coordinate .forward V Z
          (.edge (IndependentRawCandidate.coord t V) F e f)))
      by_cases het : coordinatePoint k V Z (IndependentRawCandidate.coord t V) F e f = true
      · obtain ⟨L, R, _, hs⟩ := composeLocalDataFiber_finite_support s t r h hp k kp
          W V Z (IndependentRawCandidate.coord s W) (IndependentRawCandidate.coord t V)
          F d e f hWt hV hd het a
        refine ⟨{leftContext, leftCoordinate} ∪ L,
          {rightContext, rightCoordinate} ∪ R, ?_⟩
        intro h' hp' k' hq' kp' hL hR
        have hV' : contextPoints k' V Z = true :=
          (hR rightContext (Finset.mem_union_left _ (by simp))).symm.trans hV
        have hW' : contextPoints h' W V = true :=
          (hL leftContext (Finset.mem_union_left _ (by simp))).symm.trans hWt
        have hd' : coordinatePoint h' W V (IndependentRawCandidate.coord s W)
            (IndependentRawCandidate.coord t V) d e = true :=
          (hL leftCoordinate (Finset.mem_union_left _ (by simp))).symm.trans hd
        have he' : coordinatePoint k' V Z (IndependentRawCandidate.coord t V) F e f = true :=
          (hR rightCoordinate (Finset.mem_union_left _ (by simp))).symm.trans het
        have hfiber := hs h' hp' k' kp' hW' hV' hd' he'
          (fun q hq => hL q (Finset.mem_union_right _ hq))
          (fun q hq => hR q (Finset.mem_union_right _ hq))
        exact (congrFun (composeLocalData_active s t r h hp k kp hq W V Z d e F f
          hWt hV hd het) a).trans
          (hfiber.trans (congrFun (composeLocalData_active s t r h' hp' k' kp' hq'
            W V Z d e F f hW' hV' hd' he') a).symm)
      · have he0 : coordinatePoint k V Z (IndependentRawCandidate.coord t V) F e f = false :=
          Bool.eq_false_iff.mpr het
        refine ⟨{leftContext, leftCoordinate}, {rightContext, rightCoordinate}, ?_⟩
        intro h' hp' k' hq' kp' hL hR
        have hV' : contextPoints k' V Z = true :=
          (hR rightContext (by simp)).symm.trans hV
        have hW' : contextPoints h' W V = true :=
          (hL leftContext (by simp)).symm.trans hWt
        have hd' : coordinatePoint h' W V (IndependentRawCandidate.coord s W)
            (IndependentRawCandidate.coord t V) d e = true :=
          (hL leftCoordinate (by simp)).symm.trans hd
        have he0' : coordinatePoint k' V Z (IndependentRawCandidate.coord t V) F e f = false :=
          (hR rightCoordinate (by simp)).symm.trans he0
        exact (congrFun (composeLocalData_inactive_coordinate s t r h hp k kp hq
          W V Z d e F f hWt hV hd he0) a).trans
          (congrFun (composeLocalData_inactive_coordinate s t r h' hp' k' kp' hq'
            W V Z d e F f hW' hV' hd' he0') a).symm
    · have hW0 : contextPoints h W V = false := Bool.eq_false_iff.mpr hWt
      refine ⟨{leftContext}, {rightContext}, ?_⟩
      intro h' hp' k' hq' kp' hL hR
      have hV' : contextPoints k' V Z = true :=
        (hR rightContext (by simp)).symm.trans hV
      have hW0' : contextPoints h' W V = false :=
        (hL leftContext (by simp)).symm.trans hW0
      exact (congrFun (composeLocalData_inactive_context s t r h hp k kp hq
        W V Z (IndependentRawCandidate.coord s W) F d f hV hW0) a).trans
        (congrFun (composeLocalData_inactive_context s t r h' hp' k' kp' hq'
          W V Z (IndependentRawCandidate.coord s W) F d f hV' hW0') a).symm
  · refine ⟨∅, ∅, ?_⟩
    intro h' hp' k' hq' kp' _ _
    exact (congrFun (composeLocalData_inactive_carrier s t r h hp k kp hq
      W Z D F d f hD) a).trans
      (congrFun (composeLocalData_inactive_carrier s t r h' hp' k' kp' hq'
        W Z D F d f hD) a).symm

/-- Every raw-query composition output, including dependent local-data, is
determined by finite fragments of the two original common declarations. -/
theorem composeRaw_finite_support
    (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)
    (k : Table.{u, v} U .explicit)
    (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true)
    (kp : PointLaws t r k) (a : RawQuery A C .explicit) :
    ∃ (L R : Finset (Query.{u, v} U .explicit)),
      ∀ (h' : Table.{u, v} U .explicit) (hp' : PointLaws s t h')
        (k' : Table.{u, v} U .explicit)
        (hq' : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k' V Z = true)
        (kp' : PointLaws t r k'),
        (∀ q ∈ L, h q = h' q) → (∀ q ∈ R, k q = k' q) →
        composeRaw s t r h hp k hq kp a = composeRaw s t r h' hp' k' hq' kp' a := by
  cases a with
  | coordinate d W Z a =>
    cases d with
    | forward =>
      obtain ⟨L, R, _, hs⟩ := composeCoordinate_finite_support s t r h hp k hq kp
        (.edge W Z (.forward a))
      exact ⟨L, R, hs⟩
    | backward =>
      obtain ⟨L, R, _, hs⟩ := composeCoordinate_finite_support s t r h hp k hq kp
        (.edge W Z (.backward (InverseRows.reverse a)))
      exact ⟨L, R, hs⟩
  | relation d W Z a =>
    cases d with
    | forward =>
      obtain ⟨L, R, _, hs⟩ := composeRelation_finite_support s t r h hp k hq kp
        (.edge W Z (.forward a))
      exact ⟨L, R, hs⟩
    | backward =>
      obtain ⟨L, R, _, hs⟩ := composeRelation_finite_support s t r h hp k hq kp
        (.edge W Z (.backward (InverseRows.reverse a)))
      exact ⟨L, R, hs⟩
  | localData d W Z D F x z a =>
    cases d with
    | forward =>
      exact composeLocalData_finite_support s t r h hp k hq kp W Z D F x z (.forward a)
    | backward =>
      exact composeLocalData_finite_support s t r h hp k hq kp W Z D F x z
        (.backward (InverseRows.reverse a))

end ExplicitRaw

namespace Composition

variable {U : AtomCarrier.{u}} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)
variable (rp : GeometryComponents.ExplicitRawPoints s t p)
variable (rq : GeometryComponents.ExplicitRawPoints t r q)

/-- Every raw composition output is fixed by two actual finite quotient
fragments, including the dependent local-data role. -/
theorem explicitRaw_finite_fragment
    (a : RawQuery (assemble s).core.object (assemble r).core.object .explicit) :
    ∃ (D E : Finset (Query.{u, v} U .explicit)),
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading .explicit)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading .explicit)
        (hq' : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q').table)
        (rp' : GeometryComponents.ExplicitRawPoints s t p')
        (rq' : GeometryComponents.ExplicitRawPoints t r q'),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        explicitRawRows s t r p q hq rp rq a =
          explicitRawRows s t r p' q' hq' rp' rq' a := by
  obtain ⟨D, E, hs⟩ := ExplicitRaw.composeRaw_finite_support
    s.2.2.2.val t.2.2.2.val r.2.2.2.val
    (PackageAssembly.retained s.1 t.1 p).table rp
    (PackageAssembly.retained t.1 r.1 q).table hq.contextRows.backward rq a
  refine ⟨D, E, ?_⟩
  intro p' q' hq' rp' rq' hD hE
  exact hs (PackageAssembly.retained s.1 t.1 p').table rp'
    (PackageAssembly.retained t.1 r.1 q').table hq'.contextRows.backward rq'
    ((InvariantWitness.fragment_eq_iff_points _ _ p p' D).1 hD)
    ((InvariantWitness.fragment_eq_iff_points _ _ q q' E).1 hE)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
