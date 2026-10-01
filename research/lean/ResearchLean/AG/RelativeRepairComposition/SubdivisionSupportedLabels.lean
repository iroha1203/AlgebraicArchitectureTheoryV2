import ResearchLean.AG.RelativeRepairComposition.SubdivisionVertexLabels

/-!
# Entire allowed vertex labels with the new vertex free

The old fixed vertices are included by their original names. The fresh vertex
is absent from this image. Every old allowed label extends with any full fresh
value, and restriction retains all old fixed-arrow conditions.

## Implementation notes

Only old vertices are fixed and only retained edges carry the old zero-coboundary conditions. The fresh label is unrestricted before a morphism equation is imposed. Fixing it at this stage would delete actual reidentifications.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
variable (hchosen : chosen ∉ fixed)

/-- All new allowed original vertex labels restrict to old allowed labels. -/
noncomputable def collapseAllowedLabel :
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) →+
      supportedC0 T vertices fixed where
  toFun b := ⟨collapseVertex T chosen F b.1, by
    constructor
    · intro v hv
      exact supportedC0_vertex_zero (originalTower T chosen F) _ _ b (.inl v) ⟨v,hv,rfl⟩
    · intro e he
      have hen : e ≠ chosen := fun h => hchosen (h ▸ he)
      rw [← collapse_d0,collapseCorrection_old T chosen F _ e hen]
      exact supportedC0_d0_mem (originalTower T chosen F) _ _ b
        (oldEdgeName K chosen e hen) ⟨⟨e,hen⟩,he,rfl⟩⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

omit hchosen in
/-- Every full old allowed label extends by an arbitrary full fresh-vertex value. -/
noncomputable def expandAllowedLabel (b : supportedC0 T vertices fixed)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed) :=
  ⟨expandVertex T chosen F b.1 t, by
    constructor
    · rintro v ⟨v,hv,rfl⟩
      exact supportedC0_vertex_zero T vertices fixed b v hv
    · rintro n ⟨⟨e,he⟩,hfixed,rfl⟩
      change expandVertex T chosen F b.1 t (.inl e.2.1) -
        (originalTower T chosen F).toTower.localCoefficients.edge (oldEdge K chosen e he)
          (expandVertex T chosen F b.1 t (.inl e.1)) = 0
      rw [coefficient_edge_old,expandVertex_old,expandVertex_old]
      exact supportedC0_d0_mem T vertices fixed b e hfixed⟩

/-- Every extended allowed label retains the complete old allowed label. -/
theorem collapse_expand_allowed (b : supportedC0 T vertices fixed)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    collapseAllowedLabel T chosen F vertices fixed hchosen
      (expandAllowedLabel T chosen F vertices fixed b t) = b := Subtype.ext rfl

/-- The complete old allowed label and actual fresh value restore every new allowed label. -/
theorem expand_collapse_allowed
    (b : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)) :
    expandAllowedLabel T chosen F vertices fixed
      (collapseAllowedLabel T chosen F vertices fixed hchosen b) (b.1 (.inr ())) = b :=
  Subtype.ext (expand_collapse_vertex T chosen F b.1)

omit hchosen in
/-- Every old vertex value of an extended full allowed label is its original old value. -/
theorem expandAllowedLabel_old (b : supportedC0 T vertices fixed)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) (v : K.Vertex) :
    (expandAllowedLabel T chosen F vertices fixed b t).1 (.inl v) = b.1 v := rfl

omit hchosen in
/-- The fresh value of an extended full allowed label is exactly the supplied full value. -/
theorem expandAllowedLabel_fresh (b : supportedC0 T vertices fixed)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (expandAllowedLabel T chosen F vertices fixed b t).1 (.inr ()) = t := rfl

/-- Label collapse preserves each original vertex label value. -/
theorem collapseAllowedLabel_old
    (b : supportedC0 (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (v : K.Vertex) :
    (collapseAllowedLabel T chosen F vertices fixed hchosen b).1 v = b.1 (.inl v) := rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
