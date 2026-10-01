import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.StrictSupportedCover
import ResearchLean.AG.RelativeRepairComposition.FiniteCoverGluing
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Finite restoration of strict supported original equations

## Implementation notes

The finite cover selector assembles the full original cochains. Candidate
conditions are imposed after assembly and checked at a covering region.
Shared original vertex labels, including stabilizers, are assembled separately
from their effects on edges.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA uI
namespace StrictCoverRestoration
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K) (U : I → ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))

/-- Restrict every original global label without forgetting its forbidden-edge condition. -/
def restrictLabels : SupportedEquation.Labels M P ClosedRegion.all candidates allowed →+
    StrictSupportedCover.Labels M P U candidates allowed where
  toFun b := ⟨fun i => ⟨RelativeCover.r0 M P (ClosedRegion.to_all (U i)) b.1,by
    intro e he
    have hd := RelativeCover.r_d0 M P (ClosedRegion.to_all (U i)) b.1
    have hv := congrArg (fun c => c.1 e) hd
    exact hv.symm.trans (b.2 ⟨e.1,Set.mem_univ e.1⟩ he)⟩,by intro i j v hi hj; rfl⟩
  map_zero' := by apply Subtype.ext; funext i; apply Subtype.ext; exact map_zero _
  map_add' b c := by apply Subtype.ext; funext i; apply Subtype.ext; exact map_add _ b.1 c.1

variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- Restrict whole affine solutions to every region, with literal shared-edge agreement. -/
def restrictObjects (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ) :
    StrictSupportedCover.Objects M P U candidates allowed δ :=
  ⟨fun i => ⟨CoverEquation.restrictSolution M P δ (ClosedRegion.to_all (U i)) h.1,by
    intro e he
    exact h.2 ⟨e.1,Set.mem_univ e.1⟩ he⟩,by intros; rfl⟩

variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)]
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)

/-- Restore the full global label by a bounded search through the finite cover list. -/
def glueLabels : StrictSupportedCover.Labels M P U candidates allowed →+
    SupportedEquation.Labels M P ClosedRegion.all candidates allowed where
  toFun b := ⟨FiniteCoverGlue.glue0 M P U enumI hc
    (StrictSupportedCover.localLabels M P U candidates allowed b),by
    intro e he
    obtain ⟨i,hi⟩ := hc.edges e.1
    have hb := FiniteCoverGlue.restrict_glue0 M P U enumI hc
      (StrictSupportedCover.localLabels M P U candidates allowed b)
    have hbi := congrArg (fun c : IndexedCover.Compatible0 M P U => c.1 i) hb
    change RelativeCover.r0 M P (ClosedRegion.to_all (U i)) _ = (b.1 i).1 at hbi
    have hd := RelativeCover.r_d0 M P (ClosedRegion.to_all (U i))
      (FiniteCoverGlue.glue0 M P U enumI hc
        (StrictSupportedCover.localLabels M P U candidates allowed b))
    have hv := congrArg (fun c => c.1 ⟨e.1,hi⟩) hd
    change (RelativeCover.d0 M ClosedRegion.all P _).1 e =
      (RelativeCover.d0 M (U i) P (RelativeCover.r0 M P (ClosedRegion.to_all (U i)) _)).1 ⟨e.1,hi⟩ at hv
    rw [hbi] at hv
    exact hv.trans ((b.1 i).2 ⟨e.1,hi⟩ he)⟩
  map_zero' := by apply Subtype.ext; exact map_zero (FiniteCoverGlue.glue0 M P U enumI hc)
  map_add' b c := by
    apply Subtype.ext
    have he : StrictSupportedCover.localLabels M P U candidates allowed (b+c) =
        StrictSupportedCover.localLabels M P U candidates allowed b +
          StrictSupportedCover.localLabels M P U candidates allowed c := Subtype.ext rfl
    change FiniteCoverGlue.glue0 M P U enumI hc _ = _
    rw [he,map_add]
    rfl

omit [∀ i, DecidablePred (· ∈ (U i).edges)] in
/-- Restoring and restricting labels returns every full local label. -/
theorem restrict_glue_labels (b : StrictSupportedCover.Labels M P U candidates allowed) :
    restrictLabels M P U candidates allowed (glueLabels M P U candidates allowed enumI hc b) = b := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  exact congrArg (fun c : IndexedCover.Compatible0 M P U => c.1 i)
    (FiniteCoverGlue.restrict_glue0 M P U enumI hc
      (StrictSupportedCover.localLabels M P U candidates allowed b))

omit [∀ i, DecidablePred (· ∈ (U i).edges)] in
/-- Restricting and restoring a label returns every original global value. -/
theorem glue_restrict_labels (b : SupportedEquation.Labels M P ClosedRegion.all candidates allowed) :
    glueLabels M P U candidates allowed enumI hc (restrictLabels M P U candidates allowed b) = b := by
  apply Subtype.ext
  exact FiniteCoverGlue.glue_restriction0 M P U enumI hc b.1

/-- Exact label equivalence keeps the complete original gauge group. -/
def labelEquiv : SupportedEquation.Labels M P ClosedRegion.all candidates allowed ≃+
    StrictSupportedCover.Labels M P U candidates allowed where
  toFun := restrictLabels M P U candidates allowed
  invFun := glueLabels M P U candidates allowed enumI hc
  left_inv := glue_restrict_labels M P U candidates allowed enumI hc
  right_inv := restrict_glue_labels M P U candidates allowed enumI hc
  map_add' := map_add (restrictLabels M P U candidates allowed)

/-- Finite full-cochain assembly satisfies every original face equation and support constraint. -/
def glueObjects (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ :=
  ⟨⟨FiniteCoverGlue.glue1 M P U enumI hc
      (StrictSupportedCover.localEdges M P U candidates allowed δ h),by
    rw [CoverEquation.defect_all]
    apply IndexedCover.restriction2_injective M P U hc
    apply Subtype.ext
    funext i
    change RelativeCover.r2 M P (ClosedRegion.to_all (U i))
      (RelativeCover.d1 M ClosedRegion.all P _) =
      RelativeCover.r2 M P (ClosedRegion.to_all (U i)) (-δ)
    rw [RelativeCover.r_d1,map_neg]
    have hh := FiniteCoverGlue.restrict_glue1 M P U enumI hc
      (StrictSupportedCover.localEdges M P U candidates allowed δ h)
    have hhi := congrArg (fun c : IndexedCover.Compatible1 M P U => c.1 i) hh
    change RelativeCover.r1 M P (ClosedRegion.to_all (U i)) _ = (h.1 i).1.1 at hhi
    rw [hhi]
    exact (h.1 i).1.2⟩,by
    intro e he
    obtain ⟨i,hi⟩ := hc.edges e.1
    have hv := FiniteCoverGlue.glue1_value M P U enumI hc
      (StrictSupportedCover.localEdges M P U candidates allowed δ h) i ⟨e.1,hi⟩
    exact hv.trans ((h.1 i).2 ⟨e.1,hi⟩ he)⟩

omit [∀ i, DecidablePred (· ∈ (U i).vertices)] in
/-- Every strict local object is recovered on all original edges. -/
theorem restrict_glue_objects (h : StrictSupportedCover.Objects M P U candidates allowed δ) :
    restrictObjects M P U candidates allowed δ
      (glueObjects M P U candidates allowed δ enumI hc h) = h := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun c : IndexedCover.Compatible1 M P U => c.1 i)
    (FiniteCoverGlue.restrict_glue1 M P U enumI hc
      (StrictSupportedCover.localEdges M P U candidates allowed δ h))

omit [∀ i, DecidablePred (· ∈ (U i).vertices)] in
/-- The entire original global affine solution is recovered after restriction. -/
theorem glue_restrict_objects (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ) :
    glueObjects M P U candidates allowed δ enumI hc
      (restrictObjects M P U candidates allowed δ h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  exact FiniteCoverGlue.glue_restriction1 M P U enumI hc h.1.1

/-- Full objects, including all private freedoms, have exact finite-cover coordinates. -/
def objectEquiv : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ ≃
    StrictSupportedCover.Objects M P U candidates allowed δ where
  toFun := restrictObjects M P U candidates allowed δ
  invFun := glueObjects M P U candidates allowed δ enumI hc
  left_inv := glue_restrict_objects M P U candidates allowed δ enumI hc
  right_inv := restrict_glue_objects M P U candidates allowed δ enumI hc

omit [∀ i, DecidablePred (· ∈ (U i).vertices)] [∀ i, DecidablePred (· ∈ (U i).edges)] in
/-- Restriction transports the action of every permitted original label. -/
theorem restrict_equivariant
    (b : SupportedEquation.Labels M P ClosedRegion.all candidates allowed)
    (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ) :
    restrictObjects M P U candidates allowed δ
      (SupportedEquation.gauge M P ClosedRegion.all candidates allowed δ b h) =
    StrictSupportedCover.gauge M P U candidates allowed δ
      (restrictLabels M P U candidates allowed b)
      (restrictObjects M P U candidates allowed δ h) := by
  apply Subtype.ext
  funext i
  apply Subtype.ext
  apply Subtype.ext
  change RelativeCover.r1 M P (ClosedRegion.to_all (U i))
    (h.1.1 + RelativeCover.d0 M ClosedRegion.all P b.1) =
    RelativeCover.r1 M P (ClosedRegion.to_all (U i)) h.1.1 +
      RelativeCover.d0 M (U i) P (RelativeCover.r0 M P (ClosedRegion.to_all (U i)) b.1)
  rw [map_add,RelativeCover.r_d0]

/-- The full original supported groupoid is the strict finite-cover groupoid. -/
noncomputable def equivalence : SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed δ ≌
    StrictSupportedCover.Groupoid M P U candidates allowed δ :=
  changedLabelEquivalence (labelEquiv M P U candidates allowed enumI hc).toMultiplicative
    (objectEquiv M P U candidates allowed δ enumI hc)
    (restrict_equivariant M P U candidates allowed δ)

/-- Both inverse functors agree exactly on all full objects and all labels. -/
theorem functor_inverse :
    (equivalence M P U candidates allowed δ enumI hc).functor ⋙
      (equivalence M P U candidates allowed δ enumI hc).inverse =
      𝟭 (SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed δ) :=
  changed_label_functor_inverse (labelEquiv M P U candidates allowed enumI hc).toMultiplicative
    (objectEquiv M P U candidates allowed δ enumI hc)
    (restrict_equivariant M P U candidates allowed δ)

/-- The inverse composite restores every strict local object and compatible label exactly. -/
theorem inverse_functor :
    (equivalence M P U candidates allowed δ enumI hc).inverse ⋙
      (equivalence M P U candidates allowed δ enumI hc).functor =
      𝟭 (StrictSupportedCover.Groupoid M P U candidates allowed δ) :=
  changed_label_inverse_functor (labelEquiv M P U candidates allowed enumI hc).toMultiplicative
    (objectEquiv M P U candidates allowed δ enumI hc)
    (restrict_equivariant M P U candidates allowed δ)

end StrictCoverRestoration
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
