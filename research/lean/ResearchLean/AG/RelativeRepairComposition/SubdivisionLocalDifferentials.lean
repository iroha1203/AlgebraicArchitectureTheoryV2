import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalLabels
import ResearchLean.AG.RelativeRepairComposition.SubdivisionActualDefect

/-!
# The independent local differentials under actual subdivision

## Implementation notes

Face and triple names, targets and fixed sets remain literal. The local edge
comparison is actual collapse of degreewise extension. Its old extension is
exactly the global collapsed family, so the accepted full face comparison
applies. Degree zero instead uses region closure at both actual factor ends.
-/
namespace AAT.AG.RelativeRepairComposition.RelativeCover
open TransportCoherence AbelianLiftingObstruction
universe uG uA

/-- The local relative coboundary reads both original endpoint labels by closure. -/
theorem d0_value {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
    (U P : ClosedRegion K) (b : C0 M U P) (e : U.edges) :
    (d0 M U P b).1 e = b.1 ⟨e.1.2.1,(U.edge_closed _ e.2).2⟩ -
      M.edge e.1.2.2 (b.1 ⟨e.1.1,(U.edge_closed _ e.2).1⟩) := by
  change Family.extend M.A U.vertices b.1 e.1.2.1 -
    M.edge e.1.2.2 (Family.extend M.A U.vertices b.1 e.1.1) = _
  rw [Family.extend_on M.A U.vertices b.1 e.1.2.1 (U.edge_closed _ e.2).2,
    Family.extend_on M.A U.vertices b.1 e.1.1 (U.edge_closed _ e.2).1]

end AAT.AG.RelativeRepairComposition.RelativeCover

namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (U P : ClosedRegion K) (hp : chosen ∉ P.edges)

/-- The independent local vertex differential is old d0 paired with the full supplement identity. -/
theorem local_d0
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local1Equiv T chosen F U P hp
      (RelativeCover.d0 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) b) =
    (RelativeCover.d0 T.toTower.localCoefficients U P (local0Equiv T chosen F U P hp b).1,
      (local0Equiv T chosen F U P hp b).2) := by
  apply Prod.ext
  · apply Subtype.ext
    funext e
    rcases e with ⟨e,hu⟩
    by_cases he : e = chosen
    · subst e
      rw [local1Equiv_chosen T chosen F U P hp _ hu]
      rw [RelativeCover.d0_value,RelativeCover.d0_value,RelativeCover.d0_value]
      simp only [firstEdgeName,secondEdgeName]
      rw [coefficient_edge_second,coefficient_edge_first]
      let bt : T.toTower.localCoefficients.A chosen.2.1 := b.1 ⟨.inl chosen.2.1,(U.edge_closed _ hu).2⟩
      let bw : (originalTower T chosen F).toTower.localCoefficients.A (.inr ()) := b.1 ⟨.inr (),hu⟩
      let bs : T.toTower.localCoefficients.A chosen.1 := b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩
      change (bt - rho2AddEquiv T chosen F bw) +
        rho2AddEquiv T chosen F (bw - rho1AddEquiv T chosen F bs) =
        bt - T.toTower.localCoefficients.edge chosen.2.2 bs
      rw [coefficient_transport_comp,map_sub]
      abel
    · rw [local1Equiv_retained T chosen F U P hp _ ⟨e,hu⟩ he,
        RelativeCover.d0_value,RelativeCover.d0_value]
      change b.1 ⟨.inl e.2.1,(U.edge_closed _ hu).2⟩ -
        (originalTower T chosen F).toTower.localCoefficients.edge (oldEdge K chosen e he)
          (b.1 ⟨.inl e.1,(U.edge_closed _ hu).1⟩) = _
      rw [coefficient_edge_old]
      rfl
  · apply Subtype.ext
    by_cases hu : chosen ∈ U.edges
    · change (local1Equiv T chosen F U P hp (RelativeCover.d0 _ _ _ b)).2.1 =
        (displacementLocal0 T chosen F U P b).1
      rw [local1Equiv_first,Family.extend_on
          (fun e : EdgeName (K := presentation K chosen) =>
            (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
          (expandedRegion K chosen U).edges _ (firstEdgeName K chosen) hu,
        RelativeCover.d0_value,displacementLocal0_in T chosen F U P b hu]
      change b.1 ⟨.inr (),hu⟩ -
        (originalTower T chosen F).toTower.localCoefficients.edge (firstEdge K chosen)
          (b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩) = _
      rw [coefficient_edge_first]
      rfl
    · exact (localSupplement_zero T chosen F U hu _).trans
        (localSupplement_zero T chosen F U hu _).symm

/-- All local face names and their complete actual target kernels are retained. -/
noncomputable def local2Equiv :
    RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃+
    RelativeCover.C2 T.toTower.localCoefficients U P := AddEquiv.refl _

/-- All local triple names and their complete actual target kernels are retained. -/
noncomputable def local3Equiv :
    RelativeCover.C3 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃+
    RelativeCover.C3 T.toTower.localCoefficients U P := AddEquiv.refl _

/-- The face comparison reads every same original value. -/
theorem local2Equiv_value
    (c : RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (f : U.faces) :
    (local2Equiv T chosen F U P c).1 f = c.1 f := rfl

/-- The triple comparison reads every same original value. -/
theorem local3Equiv_value
    (c : RelativeCover.C3 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) (t : U.triples) :
    (local3Equiv T chosen F U P c).1 t = c.1 t := rfl

/-- The independent local face differential reads exactly the same collapsed old family. -/
theorem local_d1
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local2Equiv T chosen F U P
      (RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) h) =
    RelativeCover.d1 T.toTower.localCoefficients U P (local1Equiv T chosen F U P hp h).1 := by
  apply Subtype.ext
  funext f
  change d1 (originalTower T chosen F).toTower.localCoefficients
    (Family.extend _ (expandedRegion K chosen U).edges h.1) f.1 =
    d1 T.toTower.localCoefficients (Family.extend _ U.edges
      (local1Equiv T chosen F U P hp h).1.1) f.1
  rw [local1Equiv_extend,d1_collapse]

/-- Both full local three-cell routes keep their same original differential. -/
theorem local_d2
    (c : RelativeCover.C2 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local3Equiv T chosen F U P
      (RelativeCover.d2 (originalTower T chosen F).toTower.localCoefficients
        (expandedRegion K chosen U) (expandedRegion K chosen P) c) =
    RelativeCover.d2 T.toTower.localCoefficients U P (local2Equiv T chosen F U P c) := by
  apply Subtype.ext
  funext t
  change d2 (originalTower T chosen F).toTower.localCoefficients
    (Family.extend _ U.faces c.1) t.1 =
    d2 T.toTower.localCoefficients (Family.extend _ U.faces c.1) t.1
  rw [d2_substitute]
  rfl

/-- The full actual original defect is retained on every included face. -/
theorem local_defect (f : U.faces) :
    (originalTower T chosen F).toTower.defect f.1 = T.toTower.defect f.1 :=
  congrFun (defect_substitute T chosen F) f.1

/-- The signed actual right-hand side is retained on every included face. -/
theorem local_rhs (f : U.faces) :
    -((originalTower T chosen F).toTower.defect f.1) = -(T.toTower.defect f.1) :=
  congrArg (fun x : T.toTower.localCoefficients.A (K.twoTarget f.1) => -x)
    (local_defect T chosen F U f)

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.RelativeCover
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
