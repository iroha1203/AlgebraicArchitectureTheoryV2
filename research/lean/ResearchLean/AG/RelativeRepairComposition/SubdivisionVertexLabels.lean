import ResearchLean.AG.RelativeRepairComposition.SubdivisionCoefficientMaps

/-!
# Every original vertex label and the free fresh-vertex label

Collapse restricts a full vertex reidentification to original vertices. The
fresh value is independent. Its two coboundaries cancel under the same actual
full kernel transport composition, so label collapse commutes with d0.
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

/-- Restrict the entire original vertex-cochain label without dropping any original vertex value. -/
noncomputable def collapseVertex : C0 (originalTower T chosen F).toTower.localCoefficients →+
    C0 T.toTower.localCoefficients where
  toFun b v := b (.inl v)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Restore the full vertex label with one specified full fresh-vertex value. -/
noncomputable def expandVertex (b : C0 T.toTower.localCoefficients)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    C0 (originalTower T chosen F).toTower.localCoefficients :=
  fun v => match v with
    | .inl v => b v
    | .inr _ => t

/-- Every original label value is retained by restoration. -/
theorem expandVertex_old (b : C0 T.toTower.localCoefficients)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) (v : K.Vertex) :
    expandVertex T chosen F b t (.inl v) = b v := rfl

/-- The restored fresh-vertex label has exactly its supplied full value. -/
theorem expandVertex_fresh (b : C0 T.toTower.localCoefficients)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    expandVertex T chosen F b t (.inr ()) = t := rfl

/-- Restriction recovers all old vertex label values. -/
theorem collapse_expand_vertex (b : C0 T.toTower.localCoefficients)
    (t : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    collapseVertex T chosen F (expandVertex T chosen F b t) = b := rfl

/-- Restriction and the actual full fresh value restore every full new vertex label. -/
theorem expand_collapse_vertex (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    expandVertex T chosen F (collapseVertex T chosen F b) (b (.inr ())) = b := by
  funext v
  cases v with
  | inl _ => rfl
  | inr u => cases u; rfl

/-- Collapse of every full actual vertex coboundary is the original vertex coboundary of the same restricted label. -/
theorem collapse_d0 (b : C0 (originalTower T chosen F).toTower.localCoefficients) :
    collapseCorrection T chosen F (d0 (originalTower T chosen F).toTower.localCoefficients b) =
      d0 T.toTower.localCoefficients (collapseVertex T chosen F b) := by
  classical
  funext e
  by_cases he : e = chosen
  · subst e
    rw [collapseCorrection_chosen]
    simp only [d0,firstEdgeName,secondEdgeName,coefficient_edge_second,coefficient_edge_first]
    let bt : T.toTower.localCoefficients.A chosen.2.1 := b (.inl chosen.2.1)
    let bm : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) := b (.inr ())
    let bs : T.toTower.localCoefficients.A chosen.1 := b (.inl chosen.1)
    change (bt - rho2AddEquiv T chosen F bm) +
      rho2AddEquiv T chosen F (bm - rho1AddEquiv T chosen F bs) =
        bt - T.toTower.localCoefficients.edge chosen.2.2 bs
    rw [map_sub,coefficient_transport_comp]
    abel
  · rw [collapseCorrection_old T chosen F _ e he]
    change b (.inl e.2.1) -
      (originalTower T chosen F).toTower.localCoefficients.edge (oldEdge K chosen e he) (b (.inl e.1)) = _
    rw [coefficient_edge_old]
    rfl

/-- Full correction collapse is additive before any support or permission is imposed. -/
theorem collapseCorrection_add
    (h k : C1 (originalTower T chosen F).toTower.localCoefficients) :
    collapseCorrection T chosen F (h + k) =
      collapseCorrection T chosen F h + collapseCorrection T chosen F k := by
  classical
  funext e
  by_cases he : e = chosen
  · subst e
    rw [collapseCorrection_chosen]
    change _ = collapseCorrection T chosen F h chosen + collapseCorrection T chosen F k chosen
    rw [collapseCorrection_chosen,collapseCorrection_chosen]
    let ht : T.toTower.localCoefficients.A chosen.2.1 := h (secondEdgeName K chosen)
    let kt : T.toTower.localCoefficients.A chosen.2.1 := k (secondEdgeName K chosen)
    let hm : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) := h (firstEdgeName K chosen)
    let km : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) := k (firstEdgeName K chosen)
    change (ht + kt) + rho2AddEquiv T chosen F (hm + km) =
      (ht + rho2AddEquiv T chosen F hm) + (kt + rho2AddEquiv T chosen F km)
    rw [map_add]
    abel
  · rw [collapseCorrection_old T chosen F _ e he]
    change _ = collapseCorrection T chosen F h e + collapseCorrection T chosen F k e
    rw [collapseCorrection_old T chosen F _ e he,collapseCorrection_old T chosen F _ e he]
    rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
