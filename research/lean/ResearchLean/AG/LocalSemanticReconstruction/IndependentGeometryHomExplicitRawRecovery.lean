import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawNative
import Formal.Util.AssertStandardAxioms

/-!
# Recovery of every native explicit raw-map component

Implementation notes: full candidate point recovery gives equality of the
coordinate and relation equivalences. Dependent local-data equivalences use
the resulting equality of target fibers and the same candidate readings.
Heterogeneous equality is used only to compare those dependent fields; no
choice of a coordinate or local-data representative is added to the Hom.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

/-- Equal candidate readings recover inverse maps even when their codomain carriers first require identification. -/
theorem inverse_read_heq {α β γ : Type u} (e : α ≃ β) (e' : α ≃ γ) (ht : β = γ)
    (hp : IndependentInverseGraph.read α β e = IndependentInverseGraph.read α γ e') : HEq e e' := by
  cases ht
  exact heq_of_eq (IndependentInverseGraph.read_injective α β hp)

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (R : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h)
variable (hc : ∀ W V, readCoordinate R W V = InverseRows.coordinate h _ _ W V)
variable (hr : ∀ W V, readRelation R W V = InverseRows.relation h _ _ W V)
variable (hl : ∀ W V C D c d, readLocalData R W V C D c d = InverseRows.localData h _ _ W V C D c d)

/-- Read every original raw Hom query, retaining the common source/target ordering in both directions. -/
def readRaw : RawQuery G.core.object H.core.object .explicit → Bool
  | .coordinate direction W V q => InverseRows.fromInverse (readCoordinate R W V) direction q
  | .relation direction W V q => InverseRows.fromInverse (readRelation R W V) direction q
  | .localData direction W V C D c d q =>
    InverseRows.fromInverse (readLocalData R W V C D c d) direction q

/-- All raw queries in the common Hom declaration are recovered after independent assembly. -/
theorem read_raw (hp : NativePoints G H h) (q : RawQuery G.core.object H.core.object .explicit) :
    readRaw f a (assemble f a h hm hp) q = h (.atObjects _ _ (.raw q)) := by
  cases q with
  | coordinate direction W V q =>
    change InverseRows.fromInverse (readCoordinate (assemble f a h hm hp) W V) direction q = _
    rw [read_coordinate]
    exact congrFun (congrFun (InverseRows.fromInverse_asInverse
      (fun direction q => h (.atObjects _ _ (.raw (.coordinate direction W V q))))) direction) q
  | relation direction W V q =>
    change InverseRows.fromInverse (readRelation (assemble f a h hm hp) W V) direction q = _
    rw [read_relation]
    exact congrFun (congrFun (InverseRows.fromInverse_asInverse
      (fun direction q => h (.atObjects _ _ (.raw (.relation direction W V q))))) direction) q
  | localData direction W V C D c d q =>
    change InverseRows.fromInverse (readLocalData (assemble f a h hm hp) W V C D c d) direction q = _
    rw [read_localData]
    exact congrFun (congrFun (InverseRows.fromInverse_asInverse
      (fun direction q => h (.atObjects _ _ (.raw (.localData direction W V C D c d q))))) direction) q

include hc in
/-- Constructing coordinates from a native map's candidate points recovers its original coordinate equivalence. -/
theorem coordinateEquiv_eq_native (hp : NativePoints G H h) (V : ArchCtx H.core.object) :
    coordinateEquiv f a h hm hp V = (R.coordinate ⟨V⟩).coordinateEquiv := by
  apply IndependentInverseGraph.read_injective _ _
  exact (readCoordinate_active (assemble f a h hm hp) V).symm.trans
    ((read_coordinate f a h hm hp (inverse f V) V).trans
      ((hc (inverse f V) V).symm.trans (readCoordinate_active R V)))

include hr in
/-- Relation-generator assembly recovers the original native equivalence on every context. -/
theorem relationEquiv_eq_native (hp : NativePoints G H h) (V : ArchCtx H.core.object) :
    relationEquiv f a h hm hp V = (R.relation ⟨V⟩).relationEquiv := by
  apply IndependentInverseGraph.read_injective _ _
  exact (readRelation_active (assemble f a h hm hp) V).symm.trans
    ((read_relation f a h hm hp (inverse f V) V).trans
      ((hr (inverse f V) V).symm.trans (readRelation_active R V)))

include hc hl in
/-- The complete coordinate transport is restored, including all dependent local-data equivalences. -/
theorem coordinateTransport_eq_native (hp : NativePoints G H h) (V : ArchCtx H.core.object) :
    coordinateTransport f a h hm hp V = R.coordinate ⟨V⟩ := by
  apply CoordinateFamilyExactEquiv.ext
  · exact coordinateEquiv_eq_native f a R h hm hc hp V
  · apply Function.hfunext rfl
    intro c d hcd
    cases hcd
    have he := congrArg (fun e : (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord ≃
      (H.raw.coordFamily ⟨V⟩).Coord => e c) (coordinateEquiv_eq_native f a R h hm hc hp V)
    apply inverse_read_heq _ _ (congrArg (H.raw.coordFamily ⟨V⟩).LocalData he)
    exact (readLocalData_active (assemble f a h hm hp) V c).symm.trans
      ((read_localData f a h hm hp (inverse f V) V _ _ c (coordinateEquiv f a h hm hp V c)).trans
        ((hl (inverse f V) V _ _ c (coordinateEquiv f a h hm hp V c)).symm.trans
          ((congrArg (fun d => readLocalData R (inverse f V) V _ _ c d) he).trans
            (readLocalData_active R V c))))

include hc hr hl in
/-- All computational fields of an arbitrary original explicit raw map are recovered from its primitive readings. -/
theorem assemble_eq_native (hp : NativePoints G H h) : assemble f a h hm hp = R := by
  apply RawAmbientRestrictionSystemExactMapAgainst.ext
  · funext V
    exact coordinateTransport_eq_native f a R h hm hc hl hp V.ctx
  · apply Function.hfunext rfl
    intro V Y hVY
    cases hVY
    exact IndependentExplicitRaw.relation_heq
      (coordinateTransport_eq_native f a R h hm hc hl hp V.ctx)
      (relationEquiv_eq_native f a R h hm hr hp V.ctx)

include hc hr hl in
/-- The native-to-primitive laws feed the assembler and recover the entire original raw map. -/
theorem assemble_points_of_native : assemble f a h hm (points_of_native f a R h hm hc hr hl) = R :=
  assemble_eq_native f a R h hm hc hr hl _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
