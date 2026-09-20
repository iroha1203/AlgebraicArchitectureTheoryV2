import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawCompositionRows
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawPoints
import Formal.Util.AssertStandardAxioms

/-!
# Raw coordinate and relation composition compared with native transport

Implementation notes: native base and coefficient maps occur in the comparison
theorems. Their point identifications locate the middle and source contexts.
At those contexts the ordinary inverse-graph composition theorem gives the
whole native fiber reader, including inactive carrier candidates. A mismatching
source context uses the primitive inactivity equation on the entire row.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (g : PackageTotalHom H.core K.core)
variable (a : G.Coefficient →+* H.Coefficient) (b : H.Coefficient →+* K.Coefficient)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h) (hp : NativePoints G H h)
variable (k : Table.{u, v} U .explicit) (km : Maps g b k) (kp : NativePoints H K k)
variable (hq : ∀ Z : ArchCtx K.core.object, ∃! V : ArchCtx H.core.object, contextPoints k V Z = true)

/-- Every primitive coordinate composition row equals the complete native composite reader. -/
theorem composeCoordinate_eq_native (W : ArchCtx G.core.object) (Z : ArchCtx K.core.object) :
    IndependentIndexedInverseGraph.row
      (composeCoordinate (IndependentRawCandidate.read G.site G.Coefficient G.raw)
        (IndependentRawCandidate.read H.site H.Coefficient H.raw)
        (IndependentRawCandidate.read K.site K.Coefficient K.raw) h hp k hq kp) W Z =
      readCoordinate (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z := by
  have hV : contextPoints k (inverse g Z) Z = true := (km.context _ Z).2 rfl
  by_cases hW : inverse f (inverse g Z) = W
  · subst W
    refine (composeCoordinate_active _ _ _ h hp k hq kp
      (inverse f (inverse g Z)) (inverse g Z) Z hV ((hm.context _ _).2 rfl)).trans ?_
    exact (IndependentInverseGraph.compose_eq_read _ _ _ _ _ _ _).trans
      (readCoordinate_active (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) Z).symm
  · have hn : contextPoints h W (inverse g Z) = false := by
      cases he : contextPoints h W (inverse g Z) with
      | false => rfl
      | true => exact False.elim (hW ((hm.context W _).1 he))
    rw [composeCoordinate_inactive _ _ _ h hp k hq kp W (inverse g Z) Z hV hn]
    exact (readCoordinate_inactive (f := PackageTotalHom.comp f g)
      ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z hW).symm

/-- All primitive relation-generator rows equal native raw composition, including false context rows. -/
theorem composeRelation_eq_native (W : ArchCtx G.core.object) (Z : ArchCtx K.core.object) :
    IndependentIndexedInverseGraph.row
      (composeRelation (IndependentRawCandidate.read G.site G.Coefficient G.raw)
        (IndependentRawCandidate.read H.site H.Coefficient H.raw)
        (IndependentRawCandidate.read K.site K.Coefficient K.raw) h hp k hq kp) W Z =
      readRelation (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z := by
  have hV : contextPoints k (inverse g Z) Z = true := (km.context _ Z).2 rfl
  by_cases hW : inverse f (inverse g Z) = W
  · subst W
    refine (composeRelation_active _ _ _ h hp k hq kp
      (inverse f (inverse g Z)) (inverse g Z) Z hV ((hm.context _ _).2 rfl)).trans ?_
    exact (IndependentInverseGraph.compose_eq_read _ _ _ _ _ _ _).trans
      (readRelation_active (f := PackageTotalHom.comp f g)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) Z).symm
  · have hn : contextPoints h W (inverse g Z) = false := by
      cases he : contextPoints h W (inverse g Z) with
      | false => rfl
      | true => exact False.elim (hW ((hm.context W _).1 he))
    rw [composeRelation_inactive _ _ _ h hp k hq kp W (inverse g Z) Z hV hn]
    exact (readRelation_inactive (f := PackageTotalHom.comp f g)
      ((assemble f a h hm hp).trans (assemble g b k km kp)) W Z hW).symm

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
