import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawReadings
import Formal.Util.AssertStandardAxioms

/-!
# Exact recovery of all explicit raw Hom candidate points

Implementation notes: recovery splits on the original context and coordinate
point responses. True points recover the native inverse graphs; false points
use the independent inactivity laws. Candidate carrier normalization is used
to recover dependent local-data rows, so this proof includes the cells that a
reader restricted to native carriers would omit.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h) (hp : NativePoints G H h)

/-- The assembled raw map restores every coordinate query, in both directions and at inactive candidates. -/
theorem read_coordinate (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    readCoordinate (assemble f a h hm hp) W V = InverseRows.coordinate h _ _ W V := by
  cases hv : contextPoints h W V with
  | false =>
    have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
    rw [readCoordinate_inactive _ W V hn]
    funext q
    exact (hp.coordinateInactive W V hv q).symm
  | true =>
    obtain rfl := (hm.context W V).1 hv
    exact (readCoordinate_active (assemble f a h hm hp) V).trans
      (IndependentInverseGraph.read_assemble _ _ _ (hp.coordinateRows _ V ((hm.context _ V).2 rfl)))

/-- All relation-generator queries are recovered, including every inactive context and carrier candidate. -/
theorem read_relation (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    readRelation (assemble f a h hm hp) W V = InverseRows.relation h _ _ W V := by
  cases hv : contextPoints h W V with
  | false =>
    have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
    rw [readRelation_inactive _ W V hn]
    funext q
    exact (hp.relationInactive W V hv q).symm
  | true =>
    obtain rfl := (hm.context W V).1 hv
    exact (readRelation_active (assemble f a h hm hp) V).trans
      (IndependentInverseGraph.read_assemble _ _ _ (hp.relationRows _ V ((hm.context _ V).2 rfl)))

/-- Every dependent local-data query survives assembly, with inactive context, coordinate, and value carriers retained. -/
theorem read_localData (W : ArchCtx G.core.object) (V : ArchCtx H.core.object)
    (C D : Type u) (c : C) (d : D) :
    readLocalData (assemble f a h hm hp) W V C D c d = InverseRows.localData h _ _ W V C D c d := by
  classical
  cases hv : contextPoints h W V with
  | false =>
    have hn : inverse f V ≠ W := fun he => Bool.noConfusion (hv.symm.trans ((hm.context W V).2 he))
    rw [readLocalData_inactive_context _ W V C D c d hn]
    funext q
    exact (hp.localDataInactive W V C D c d (Or.inl hv) q).symm
  | true =>
    obtain rfl := (hm.context W V).1 hv
    change readLocalData (assemble f a h hm hp) (inverse f V) V C D c d = _
    cases hc : coordinatePoint h (inverse f V) V C D c d with
    | false =>
      have hr : readCoordinate (assemble f a h hm hp) (inverse f V) V (.forward (.edge C D c d)) = false := by
        rw [read_coordinate]
        exact hc
      rw [readLocalData_inactive_coordinate _ _ _ C D c d hr]
      funext q
      exact (hp.localDataInactive _ V C D c d (Or.inr hc) q).symm
    | true =>
      have hrows := hp.coordinateRows _ V ((hm.context _ V).2 rfl)
      have hC : C = (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord := by
        by_contra hn
        exact Bool.noConfusion ((hrows.forward.1 C D c d (Or.inl hn)).symm.trans hc)
      subst C
      have hD : D = (H.raw.coordFamily ⟨V⟩).Coord := by
        by_contra hn
        exact Bool.noConfusion ((hrows.forward.1 _ D c d (Or.inr hn)).symm.trans hc)
      subst D
      have he := (coordinate_forward_iff f a h hm hp V c d).1 hc
      subst d
      change readLocalData (assemble f a h hm hp) (inverse f V) V _ _ c
        (((assemble f a h hm hp).coordinate ⟨V⟩).coordinateEquiv c) = _
      rw [readLocalData_active]
      exact IndependentInverseGraph.read_assemble _ _ _
        (hp.localDataRows _ V _ _ c (coordinateEquiv f a h hm hp V c) _ _
          ((hm.context _ V).2 rfl) ((coordinate_forward_iff f a h hm hp V c _).2 rfl)
          (IndependentRawCandidate.read_localData G.site G.Coefficient G.raw _ c)
          (IndependentRawCandidate.read_localData H.site H.Coefficient H.raw V _))

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
