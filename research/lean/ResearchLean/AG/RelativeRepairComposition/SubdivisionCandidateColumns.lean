import ResearchLean.AG.RelativeRepairComposition.SubdivisionRangeQuotient
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeEquations

/-!
# Retained complete candidate names and their full original kernel columns

The actual factor edge is always allowed. Every original candidate keeps its
complete name and entire original target kernel, with its independent masked
correction, full original differential and always quotient.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.CandidateColumns
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
set_option maxHeartbeats 2000000
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))

variable (chosen : EdgeName (K := K)) (F : Factorization T chosen)
variable (hp : chosen ∉ P.edges) (hc : chosen ∉ candidates)
attribute [local instance] LinearCoefficients.coefficientModules
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)
local notation "M" => T.toTower.localCoefficients
local notation "newP" => oldRegion K chosen P hp
local notation "newCandidates" => oldEdgeSet K chosen candidates
local notation "newLinear" => LinearCoefficients.edge_linear T chosen F hlinear

attribute [local instance] Classical.propDecidable

/-- Retain each original candidate as its unchanged complete named edge. -/
def retainedCandidate (e : candidates) : newCandidates :=
  ⟨oldEdgeName K chosen e.1 (fun he => hc (he ▸ e.2)),
    ⟨⟨e.1,fun he => hc (he ▸ e.2)⟩,e.2,rfl⟩⟩

/-- All and only original candidate names occur among independently retained new candidates. -/
theorem retainedCandidate_bijective :
    Function.Bijective (retainedCandidate candidates chosen hc) := by
  constructor
  · intro e f h
    have hv := congrArg (fun a : newCandidates => edgeNameEquiv K chosen a.1) h
    change (Sum.inl (⟨e.1,fun he => hc (he ▸ e.2)⟩ : {a : EdgeName (K := K) // a ≠ chosen}) : Name K chosen) =
      Sum.inl (⟨f.1,fun he => hc (he ▸ f.2)⟩ : {a : EdgeName (K := K) // a ≠ chosen}) at hv
    exact Subtype.ext (congrArg (fun a : {a : EdgeName (K := K) // a ≠ chosen} => a.1) (Sum.inl.inj hv))
  · rintro ⟨_,⟨e,he,rfl⟩⟩
    exact ⟨⟨e.1,he⟩,rfl⟩

/-- The candidate comparison is a bijection on all original complete names. -/
noncomputable def nameEquiv : candidates ≃ newCandidates :=
  Equiv.ofBijective (retainedCandidate candidates chosen hc)
    (retainedCandidate_bijective candidates chosen hc)

/-- Every forward name is the same untouched original candidate edge. -/
theorem nameEquiv_value (e : candidates) :
    (nameEquiv candidates chosen hc e).1 =
      oldEdgeName K chosen e.1 (fun he => hc (he ▸ e.2)) := rfl

/-- The entire actual original target kernel is retained by each complete candidate name. -/
noncomputable def kernelEquiv (e : candidates) :
    T.toTower.localCoefficients.A e.1.2.1 ≃ₗ[k]
      (originalTower T chosen F).toTower.localCoefficients.A
        (nameEquiv candidates chosen hc e).1.2.1 := LinearEquiv.refl k _

/-- Whole candidate kernel values stay literally unchanged. -/
theorem kernelEquiv_value (e : candidates) (x : T.toTower.localCoefficients.A e.1.2.1) :
    kernelEquiv (k := k) T candidates chosen F hc e x = x := rfl

variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)

include houtside in
/-- Every independently retained candidate lies outside the generated fixed region. -/
theorem retained_outside : ∀ e ∈ newCandidates, e ∉ (oldRegion K chosen P hp).edges := by
  rintro _ ⟨e,he,rfl⟩ ⟨f,hf,h⟩
  have hi := retained_injective K chosen h
  exact houtside e.1 he (hi ▸ hf)

/-- All original and new zero masks read the same original candidate values after actual collapse. -/
theorem candidate_collapse (e : candidates) (x : T.toTower.localCoefficients.A e.1.2.1) :
    collapseCorrection T chosen F
      (fun f => (OriginalColumns.candidateCochain (k := k)
        (originalTower T chosen F).toTower.localCoefficients newP newCandidates
        (retained_outside P candidates chosen hp houtside)
        (LinearMap.single k
          (fun a : newCandidates => (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1)
          (nameEquiv candidates chosen hc e) (kernelEquiv (k := k) T candidates chosen F hc e x))).1
        ⟨f,Set.mem_univ f⟩) =
      (fun f => (OriginalColumns.candidateCochain (k := k) M P candidates houtside
        (LinearMap.single k (fun a : candidates => T.toTower.localCoefficients.A a.1.2.1) e x)).1 ⟨f,Set.mem_univ f⟩) := by
  classical
  funext f
  by_cases hf : f = chosen
  · subst f
    rw [collapseCorrection_chosen]
    have hn1 : firstEdgeName K chosen ∉ newCandidates := by
      rintro ⟨a,ha,h⟩
      have hh := congrArg (edgeNameEquiv K chosen) h
      change Sum.inl a = Sum.inr false at hh
      cases hh
    have hn2 : secondEdgeName K chosen ∉ newCandidates := by
      rintro ⟨a,ha,h⟩
      have hh := congrArg (edgeNameEquiv K chosen) h
      change Sum.inl a = Sum.inr true at hh
      cases hh
    rw [OriginalColumns.noncandidate_value _ _ _ _ _ _ hn1,
      OriginalColumns.noncandidate_value _ _ _ _ _ _ hn2,
      map_zero,add_zero,OriginalColumns.noncandidate_value _ _ _ _ _ _ hc]
  · rw [collapseCorrection_old T chosen F _ f hf]
    by_cases hfc : f ∈ candidates
    · let a : candidates := ⟨f,hfc⟩
      have hnc : oldEdgeName K chosen f hf ∈ newCandidates := ⟨⟨f,hf⟩,hfc,rfl⟩
      rw [OriginalColumns.candidate_value _ _ _ _ _ ⟨_,hnc⟩,
        OriginalColumns.candidate_value _ _ _ _ _ a]
      change (LinearMap.single k
        (fun a : newCandidates => (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1)
        (nameEquiv candidates chosen hc e) x) (nameEquiv candidates chosen hc a) =
          (LinearMap.single k (fun a : candidates => T.toTower.localCoefficients.A a.1.2.1) e x) a
      by_cases hae : a = e
      · have hfe : f = e.1 := congrArg Subtype.val hae
        subst f
        change (LinearMap.single k
          (fun a : newCandidates => (originalTower T chosen F).toTower.localCoefficients.A a.1.2.1)
          (nameEquiv candidates chosen hc e) x) (nameEquiv candidates chosen hc e) =
          (LinearMap.single k (fun a : candidates => T.toTower.localCoefficients.A a.1.2.1) e x) e
        simp only [LinearMap.single_apply,Pi.single_eq_same]
      · have hne : nameEquiv candidates chosen hc a ≠ nameEquiv candidates chosen hc e :=
          fun h => hae ((nameEquiv candidates chosen hc).injective h)
        simp only [LinearMap.single_apply,Pi.single_eq_of_ne hae,Pi.single_eq_of_ne hne]
    · have hnc : oldEdgeName K chosen f hf ∉ newCandidates := by
        rintro ⟨a,ha,h⟩
        have hi : a = ⟨f,hf⟩ := retained_injective K chosen h
        have ha' : a.1 ∈ candidates := ha
        apply hfc
        have hname : a.1 = f := congrArg Subtype.val hi
        rw [← hname]
        exact ha'
      rw [OriginalColumns.noncandidate_value _ _ _ _ _ _ hnc,
        OriginalColumns.noncandidate_value _ _ _ _ _ _ hfc]

/-- The complete relative differential follows the same actual full correction comparison. -/
theorem differential_collapse
    (hnew : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all newP)
    (hold : RelativeCover.C1 M ClosedRegion.all P)
    (hvalues : collapseCorrection T chosen F (fun e => hnew.1 ⟨e,Set.mem_univ e⟩) =
      (fun e => hold.1 ⟨e,Set.mem_univ e⟩)) :
    AlwaysDifferential.faceLinearEquiv (k := k) T P chosen F hp
      (FiniteCoefficients.differential1 (originalTower T chosen F).toTower.localCoefficients
        newLinear ClosedRegion.all newP hnew) =
      FiniteCoefficients.differential1 M hlinear ClosedRegion.all P hold := by
  rw [FiniteCoefficients.differential1_eq,FiniteCoefficients.differential1_eq]
  apply Subtype.ext
  funext f
  have hn := congrFun (RelativeCover.original2_restrict
    (originalTower T chosen F).toTower.localCoefficients newP
    (RelativeCover.d1 (originalTower T chosen F).toTower.localCoefficients ClosedRegion.all newP hnew)) f
  have hnd := congrArg (fun c : RelativeComplex.relativeC2
    (originalTower T chosen F).toTower.localCoefficients newP => c.1 f.1)
    (RelativeCover.original_d1 (originalTower T chosen F).toTower.localCoefficients newP hnew)
  have ho := congrFun (RelativeCover.original2_restrict M P (RelativeCover.d1 M ClosedRegion.all P hold)) f
  have hod := congrArg (fun c : RelativeComplex.relativeC2 M P => c.1 f.1)
    (RelativeCover.original_d1 M P hold)
  exact hn.symm.trans (hnd.trans ((congrFun (d1_collapse T chosen F
    (fun e => hnew.1 ⟨e,Set.mem_univ e⟩)) f.1).trans
      ((congrArg (fun h : C1 M => d1 M h f.1) hvalues).trans (hod.symm.trans ho))))

/-- Each full actual candidate differential column is preserved with its original whole kernel. -/
theorem column_collapse (e : candidates) (x : T.toTower.localCoefficients.A e.1.2.1) :
    AlwaysDifferential.faceLinearEquiv (k := k) T P chosen F hp
      (OriginalColumns.column (k := k) (originalTower T chosen F).toTower.localCoefficients
        newP newCandidates (retained_outside P candidates chosen hp houtside) newLinear
        (nameEquiv candidates chosen hc e) (kernelEquiv (k := k) T candidates chosen F hc e x)) =
      OriginalColumns.column (k := k) M P candidates houtside hlinear e x := by
  classical
  simp only [OriginalColumns.column,OriginalColumns.candidateMap,LinearMap.comp_apply]
  simpa only [FiniteCoefficients.differential1_eq] using
    (differential_collapse T P chosen F hp hlinear _ _
    (candidate_collapse (k := k) T P candidates chosen F hp hc houtside e x))

/-- The full named quotient column uses precisely the same actual always quotient comparison. -/
theorem quotient_column (e : candidates) (x : T.toTower.localCoefficients.A e.1.2.1) :
    RangeQuotient.equivalence T P candidates chosen F hp hc hlinear
      (OriginalRanges.column (k := k) (originalTower T chosen F).toTower.localCoefficients
        newP newCandidates (retained_outside P candidates chosen hp houtside) newLinear
        (nameEquiv candidates chosen hc e) (kernelEquiv (k := k) T candidates chosen F hc e x)) =
      OriginalRanges.column (k := k) M P candidates houtside hlinear e x := by
  classical
  change RangeQuotient.equivalence T P candidates chosen F hp hc hlinear
    (LinearInterface.q (OriginalColumns.D (k := k)
      (originalTower T chosen F).toTower.localCoefficients newP newCandidates newLinear)
      (OriginalColumns.column (k := k) (originalTower T chosen F).toTower.localCoefficients
        newP newCandidates (retained_outside P candidates chosen hp houtside) newLinear
        (nameEquiv candidates chosen hc e) (kernelEquiv (k := k) T candidates chosen F hc e x))) = _
  rw [RangeQuotient.equivalence_q]
  exact congrArg (LinearInterface.q (OriginalColumns.D (k := k) M P candidates hlinear))
    (column_collapse T P candidates chosen F hp hc hlinear houtside e x)

end AAT.AG.RelativeRepairComposition.Subdivision.CandidateColumns
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.CandidateColumns
