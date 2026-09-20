import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawCompositionNative
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawLocalDataComposition
import Formal.Util.AssertStandardAxioms

/-!
# Native comparison for primitive raw local-data composition

Implementation notes: inactive contexts and candidate coordinate carriers are
checked before selecting a local-data fiber. At actual carriers, the primitive
coordinate points select exactly the successive native coordinate images.
The three original type responses identify the dependent fiber carriers, so
the inverse-graph composition theorem applies to the entire value row.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}

/-- Mismatching coordinate carrier candidates force every native local-data cell to false. -/
theorem readLocalData_inactive_carriers {f : PackageTotalHom G.core H.core}
    {a : G.Coefficient →+* H.Coefficient}
    (R : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw)
    (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) (D F : Type u) (d : D) (z : F)
    (hn : D ≠ (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord ∨
      F ≠ (H.raw.coordFamily ⟨V⟩).Coord) :
    readLocalData R W V D F d z = fun _ => false := by
  by_cases hW : inverse f V = W
  · subst W
    apply readLocalData_inactive_coordinate
    rw [readCoordinate_active]
    exact (IndependentInverseGraph.read_isLawful _ _ (R.coordinate ⟨V⟩).coordinateEquiv).forward.1 _ _ _ _ hn
  · exact readLocalData_inactive_context R W V D F d z hW

variable (f : PackageTotalHom G.core H.core) (g : PackageTotalHom H.core K.core)
variable (a : G.Coefficient →+* H.Coefficient) (b : H.Coefficient →+* K.Coefficient)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h) (hp : NativePoints G H h)
variable (k : Table.{u, v} U .explicit) (km : Maps g b k) (kp : NativePoints H K k)
variable (hq : ∀ Z : ArchCtx K.core.object, ∃! V : ArchCtx H.core.object, contextPoints k V Z = true)

/-- Every primitive dependent local-data row equals the complete native raw composite reader. -/
theorem composeLocalData_eq_native (W : ArchCtx G.core.object) (Z : ArchCtx K.core.object)
    (D F : Type u) (d : D) (z : F) :
    composeLocalData (IndependentRawCandidate.read G.site G.Coefficient G.raw)
      (IndependentRawCandidate.read H.site H.Coefficient H.raw)
      (IndependentRawCandidate.read K.site K.Coefficient K.raw) h hp k kp hq W Z D F d z =
      readLocalData (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z D F d z := by
  classical
  have hV : contextPoints k (inverse g Z) Z = true := (km.context _ Z).2 rfl
  by_cases hW : inverse f (inverse g Z) = W
  · subst W
    have hW' : contextPoints h (inverse f (inverse g Z)) (inverse g Z) = true := (hm.context _ _).2 rfl
    by_cases hD : D = (G.raw.coordFamily ((coreContextInverse f).obj ((coreContextInverse g).obj ⟨Z⟩))).Coord
    · subst D
      let e := coordinateEquiv f a h hm hp (inverse g Z) d
      have hd : coordinatePoint h (inverse f (inverse g Z)) (inverse g Z) _ _ d e = true :=
        (coordinate_forward_iff f a h hm hp (inverse g Z) d e).2 rfl
      by_cases hF : F = (K.raw.coordFamily ⟨Z⟩).Coord
      · subst F
        by_cases he : coordinatePoint k (inverse g Z) Z _ _ e z = true
        · have hz := (coordinate_forward_iff g b k km kp Z e z).1 he
          subst z
          refine (composeLocalData_active _ _ _ h hp k kp hq (inverse f (inverse g Z)) (inverse g Z) Z
            d e (K.raw.coordFamily ⟨Z⟩).Coord (coordinateEquiv g b k km kp Z e) hW' hV hd he).trans ?_
          refine (composeLocalDataFiber_some _ _ _ h hp k kp (inverse f (inverse g Z)) (inverse g Z) Z
            _ _ _ d e (coordinateEquiv g b k km kp Z e) hW' hV hd he _ _ _
            (IndependentRawCandidate.read_localData G.site G.Coefficient G.raw (inverse f (inverse g Z)) d)
            (IndependentRawCandidate.read_localData H.site H.Coefficient H.raw (inverse g Z) e)
            (IndependentRawCandidate.read_localData K.site K.Coefficient K.raw Z _)).trans ?_
          exact (IndependentInverseGraph.compose_eq_read _ _ _ _ _ _ _).trans
            (readLocalData_active (f := PackageTotalHom.comp f g)
              ((assemble f a h hm hp).trans (assemble g b k km kp)) Z d).symm
        · have he' : coordinatePoint k (inverse g Z) Z _ _ e z = false := Bool.eq_false_iff.mpr he
          refine (composeLocalData_inactive_coordinate _ _ _ h hp k kp hq (inverse f (inverse g Z))
            (inverse g Z) Z d e (K.raw.coordFamily ⟨Z⟩).Coord z hW' hV hd he').trans ?_
          symm
          apply readLocalData_inactive_coordinate
          refine (congrFun (readCoordinate_active (f := PackageTotalHom.comp f g)
            ((assemble f a h hm hp).trans (assemble g b k km kp)) Z) (.forward (.edge _ _ d z))).trans ?_
          apply Bool.eq_false_iff.mpr
          intro ht
          have hz := (IndependentCarrierGraph.read_edge _ _
            (((assemble f a h hm hp).trans (assemble g b k km kp)).coordinate ⟨Z⟩).coordinateEquiv d z).1 ht
          exact he ((coordinate_forward_iff g b k km kp Z e z).2 hz)
      · have he : coordinatePoint k (inverse g Z) Z _ F e z = false :=
          (kp.coordinateRows _ Z hV).forward.1 _ _ _ _ (Or.inr hF)
        refine (composeLocalData_inactive_coordinate _ _ _ h hp k kp hq (inverse f (inverse g Z))
          (inverse g Z) Z d e F z hW' hV hd he).trans ?_
        exact (readLocalData_inactive_carriers (f := PackageTotalHom.comp f g)
          ((assemble f a h hm hp).trans (assemble g b k km kp)) _ Z _ F d z (Or.inr hF)).symm
    · refine (composeLocalData_inactive_carrier _ _ _ h hp k kp hq (inverse f (inverse g Z)) Z D F d z hD).trans ?_
      exact (readLocalData_inactive_carriers (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) _ Z D F d z (Or.inl hD)).symm
  · have hn : contextPoints h W (inverse g Z) = false := by
      cases he : contextPoints h W (inverse g Z) with
      | false => rfl
      | true => exact False.elim (hW ((hm.context W _).1 he))
    rw [composeLocalData_inactive_context _ _ _ h hp k kp hq W (inverse g Z) Z D F d z hV hn]
    exact (readLocalData_inactive_context (f := PackageTotalHom.comp f g)
      ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z D F d z hW).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
