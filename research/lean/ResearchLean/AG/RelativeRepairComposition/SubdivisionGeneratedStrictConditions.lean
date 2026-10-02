import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalCorrections
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPrivatePartition
import ResearchLean.AG.RelativeRepairComposition.SubdivisionPermissions

/-!
# Independent original strict predicates under the actual local comparison

## Implementation notes

Both predicates read their own complete original edge families. Retained
forbidden names and every strict shared value agree under actual collapse.
Private incidence excludes both factors from overlaps; it imposes no condition
on their arbitrary local values. These predicates will be applied to each
side's independent generated restoration, preserving every private freedom.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uA uI uE uB uD vE vB vD

/-- Independently impose zero forbidden values and literal equality of every shared value. -/
def Compatible {K : FiniteTransportPresentation.{uG}} {I : Type uI}
    (M : LocalCoefficients.{uG,uA} K) (U : I → ClosedRegion K) (P : ClosedRegion K)
    (forbidden : Set (EdgeName (K := K))) (h : ∀ j, RelativeCover.C1 M (U j) P) : Prop :=
  (∀ j (e : (U j).edges), e.1 ∈ forbidden → (h j).1 e = 0) ∧
  (∀ j l e (hj : e ∈ (U j).edges) (hl : e ∈ (U l).edges), l ≠ j →
    (h j).1 ⟨e,hj⟩ = (h l).1 ⟨e,hl⟩)

variable {K : FiniteTransportPresentation.{uG}} {I : Type uI}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen) (U : I → ClosedRegion K)
variable (P : ClosedRegion K) (candidates : Set (EdgeName (K := K)))
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P

include hi in
/-- Every shared original edge avoids the private chosen name. -/
theorem shared_ne_chosen (j l : I) (hlj : l ≠ j) (e : EdgeName (K := K))
    (hj : e ∈ (U j).edges) (hl : e ∈ (U l).edges) : e ≠ chosen := by
  intro he
  subst e
  exact chosen_not_overlap K chosen U
    (private_chosen_unique K chosen U P candidates owner hi) j l (Ne.symm hlj) ⟨hj,hl⟩

variable (forbidden : Set (EdgeName (K := K))) (hf : chosen ∉ forbidden)

include hf in
/-- Every independently defined strict condition survives and is reflected by full actual collapse. -/
theorem compatibility_iff
    (h : ∀ j, RelativeCover.C1 Mn (Un j) Pn) :
    Compatible Mn Un Pn (oldEdgeSet K chosen forbidden) h ↔
      Compatible Mo U P forbidden
        (fun j => (local1Equiv T chosen factor (U j) P hi.2.1 (h j)).1) := by
  constructor
  · rintro ⟨hs,hg⟩
    constructor
    · intro j e he
      have hn : e.1 ≠ chosen := fun hx => hf (hx ▸ he)
      rw [local1Equiv_retained T chosen factor (U j) P hi.2.1 (h j) e hn]
      exact hs j ⟨oldEdgeName K chosen e.1 hn,e.2⟩ ⟨⟨e.1,hn⟩,he,rfl⟩
    · intro j l e hj hl hlj
      have hn := shared_ne_chosen chosen U P candidates owner hi j l hlj e hj hl
      rw [local1Equiv_retained T chosen factor (U j) P hi.2.1 (h j) ⟨e,hj⟩ hn,
        local1Equiv_retained T chosen factor (U l) P hi.2.1 (h l) ⟨e,hl⟩ hn]
      exact hg j l (oldEdgeName K chosen e hn) hj hl hlj
  · rintro ⟨hs,hg⟩
    constructor
    · intro j a ha
      rcases a with ⟨a,haU⟩
      rcases ha with ⟨e,he,hea⟩
      change retainedEdgeName K chosen e = a at hea
      subst a
      have ho := hs j ⟨e.1,haU⟩ he
      rw [local1Equiv_retained T chosen factor (U j) P hi.2.1 (h j) ⟨e.1,haU⟩ e.2] at ho
      exact ho
    · intro j l a hj hl hlj
      obtain ⟨a,rfl⟩ := (edgeNameEquiv K chosen).symm.surjective a
      cases a with
      | inl e =>
        have ho := hg j l e.1 hj hl hlj
        rw [local1Equiv_retained T chosen factor (U j) P hi.2.1 (h j) ⟨e.1,hj⟩ e.2,
          local1Equiv_retained T chosen factor (U l) P hi.2.1 (h l) ⟨e.1,hl⟩ e.2] at ho
        exact ho
      | inr b =>
        cases b
        · exact False.elim ((shared_ne_chosen chosen U P candidates owner hi j l hlj
            chosen hj hl) rfl)
        · exact False.elim ((shared_ne_chosen chosen U P candidates owner hi j l hlj
            chosen hj hl) rfl)

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedStrictConditions
