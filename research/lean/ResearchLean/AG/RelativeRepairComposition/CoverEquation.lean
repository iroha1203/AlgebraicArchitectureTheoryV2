import ResearchLean.AG.RelativeRepairComposition.RelativeCoverComplex
import ResearchLean.AG.RelativeRepairComposition.AffineEquation

/-!
# Original-index affine repair descent on a closed cover.

All restriction maps retain their original edge and vertex values. Cover exactness
generates seam strictification, full and faithful reconstruction, and native descent.
## Implementation notes

G-130 B uses the original-cell relative families with the actual affine right-hand
side. The comma category retains overlap arrows. Degree-zero surjectivity absorbs
a seam; degree-one exactness glues the corrected pair; degree-two injectivity
checks the global equation. No extension is assumed to be a chain map. Replacing
the comma category with orbit classes would lose the original stabilizer labels.
-/

namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction
universe uG uA
namespace CoverEquation
variable {K : FiniteTransportPresentation.{uG}}
variable (M : LocalCoefficients.{uG,uA} K) (P : ClosedRegion K)
variable (δ : RelativeCover.C2 M ClosedRegion.all P)

/-- The same global face values restricted to a native closed region. -/
def defect (U : ClosedRegion K) : RelativeCover.C2 M U P :=
  RelativeCover.r2 M P (ClosedRegion.to_all U) δ

/-- Restriction to the complete original region keeps the entire face cochain. -/
theorem defect_all : defect M P δ ClosedRegion.all = δ := by
  apply Subtype.ext
  funext f
  rfl

/-- Restriction keeps the identical original face values. -/
theorem restrict_defect {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U) :
    RelativeCover.r2 M P i (defect M P δ U) = defect M P δ V := rfl

/-- Solutions on the original names of a closed region. -/
abbrev Solution (U : ClosedRegion K) :=
  Equation.Solution (RelativeCover.d0 M U P) (RelativeCover.d1 M U P)
    (RelativeCover.d1_d0 M U P) (-defect M P δ U)

/-- The action groupoid retains every relative original vertex label. -/
abbrev Groupoid (U : ClosedRegion K) :=
  Equation.Groupoid (RelativeCover.d0 M U P) (RelativeCover.d1 M U P)
    (RelativeCover.d1_d0 M U P) (-defect M P δ U)

/-- Restriction preserves the same affine face equation. -/
def restrictSolution {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U)
    (h : Solution M P δ U) : Solution M P δ V :=
  ⟨RelativeCover.r1 M P i h.1, by
    rw [← RelativeCover.r_d1, h.2, map_neg, restrict_defect]⟩

/-- Restricted gauge action uses precisely the same included vertex values. -/
theorem restrict_gauge {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U)
    (b : Multiplicative (RelativeCover.C0 M U P)) (h : Solution M P δ U) :
    restrictSolution M P δ i (b • h) =
      (Multiplicative.ofAdd (RelativeCover.r0 M P i b.toAdd)) •
        restrictSolution M P δ i h := by
  apply Subtype.ext
  change RelativeCover.r1 M P i (h.1 + RelativeCover.d0 M U P b.toAdd) =
    RelativeCover.r1 M P i h.1 +
      RelativeCover.d0 M V P (RelativeCover.r0 M P i b.toAdd)
  rw [map_add, RelativeCover.r_d0]

/-- The same included cochains define the full restriction functor. -/
noncomputable def restrictionFunctor {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U) :
    Groupoid M P δ U ⥤ Groupoid M P δ V :=
  actionLabelFunctor (RelativeCover.r0 M P i).toMultiplicative
    (restrictSolution M P δ i) (restrict_gauge M P δ i)

/-- Objects are restricted on every original named edge. -/
theorem restriction_obj_value {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U)
    (h : Groupoid M P δ U) (e : V.edges) :
    ((restrictionFunctor M P δ i).obj h).back.1.1 e =
      h.back.1.1 ⟨e.1,i.edges e.2⟩ := rfl

/-- Morphisms retain every original vertex value on the included region. -/
theorem restriction_map_value {U V : ClosedRegion K} (i : ClosedRegion.Inclusion V U)
    {h k : Groupoid M P δ U} (b : h ⟶ k) (v : V.vertices) :
    ((restrictionFunctor M P δ i).map b).1.toAdd.1 v =
      b.1.toAdd.1 ⟨v.1,i.vertices v.2⟩ := rfl


variable (U V : ClosedRegion K)

/-- Native homotopy pullback: local affine repairs with a full overlap gauge arrow. -/
abbrev Descent := Comma
  (restrictionFunctor M P δ (ClosedRegion.inter_left U V))
  (restrictionFunctor M P δ (ClosedRegion.inter_right U V))

/-- The overlap arrow of a global repair has zero label on every vertex. -/
noncomputable def diagonalObj (h : Groupoid M P δ ClosedRegion.all) :
    Descent M P δ U V where
  left := (restrictionFunctor M P δ (ClosedRegion.to_all U)).obj h
  right := (restrictionFunctor M P δ (ClosedRegion.to_all V)).obj h
  hom := Equation.homOfLabel _ _ _ _ 0 (by
    rw [map_zero, add_zero]
    rfl)

/-- Global repairs restrict with all labels, including their seam compatibility. -/
noncomputable def diagonalFunctor :
    Groupoid M P δ ClosedRegion.all ⥤ Descent M P δ U V where
  obj := diagonalObj M P δ U V
  map f :=
    { left := (restrictionFunctor M P δ (ClosedRegion.to_all U)).map f
      right := (restrictionFunctor M P δ (ClosedRegion.to_all V)).map f
      w := by
        apply Subtype.ext
        change (1 : Multiplicative (RelativeCover.C0 M (ClosedRegion.inter U V) P)) *
          Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * 1
        rw [one_mul, mul_one]
        rfl }
  map_id _ := Comma.hom_ext _ _ (Subtype.ext rfl) (Subtype.ext rfl)
  map_comp _ _ := Comma.hom_ext _ _ (Subtype.ext rfl) (Subtype.ext rfl)

/-- A diagonal object's seam has the original zero-cochain label. -/
theorem diagonal_seam_label (h : Groupoid M P δ ClosedRegion.all) :
    (diagonalObj M P δ U V h).hom.1.toAdd = 0 := rfl

/-- A cover detects equality of every global gauge label. -/
theorem diagonal_faithful (hc : ClosedRegion.Cover U V) :
    (diagonalFunctor M P δ U V).Faithful where
  map_injective := by
    intro h k f g he
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    apply RelativeCover.diagonal0_injective M P U V hc
    apply Prod.ext
    · exact congrArg (fun b => b.left.1.toAdd) he
    · exact congrArg (fun b => b.right.1.toAdd) he

/-- Every compatible pair of local gauge arrows is the restriction of a global arrow. -/
theorem diagonal_full (hc : ClosedRegion.Cover U V) :
    (diagonalFunctor M P δ U V).Full where
  map_surjective := by
    intro h k f
    let pair := (f.left.1.toAdd, f.right.1.toAdd)
    have hz : RelativeCover.difference0 M P U V pair = 0 := by
      have hw := congrArg (fun b => b.1.toAdd) f.w
      change (0 : RelativeCover.C0 M (ClosedRegion.inter U V) P) +
        RelativeCover.r0 M P (ClosedRegion.inter_left U V) f.left.1.toAdd =
        RelativeCover.r0 M P (ClosedRegion.inter_right U V) f.right.1.toAdd + 0 at hw
      simp only [zero_add, add_zero] at hw
      exact sub_eq_zero.mpr hw
    obtain ⟨b,hb⟩ := (RelativeCover.degree0_exact M P U V hc pair).mp hz
    have hbU := congrArg Prod.fst hb
    have hbV := congrArg Prod.snd hb
    change RelativeCover.r0 M P (ClosedRegion.to_all U) b = f.left.1.toAdd at hbU
    change RelativeCover.r0 M P (ClosedRegion.to_all V) b = f.right.1.toAdd at hbV
    have hg : k.back.1 = h.back.1 + RelativeCover.d0 M ClosedRegion.all P b := by
      apply RelativeCover.diagonal1_injective M P U V hc
      apply Prod.ext
      · change RelativeCover.r1 M P (ClosedRegion.to_all U) k.back.1 =
          RelativeCover.r1 M P (ClosedRegion.to_all U)
            (h.back.1 + RelativeCover.d0 M ClosedRegion.all P b)
        rw [map_add, RelativeCover.r_d0, hbU]
        exact Equation.hom_condition _ _ _ _ f.left
      · change RelativeCover.r1 M P (ClosedRegion.to_all V) k.back.1 =
          RelativeCover.r1 M P (ClosedRegion.to_all V)
            (h.back.1 + RelativeCover.d0 M ClosedRegion.all P b)
        rw [map_add, RelativeCover.r_d0, hbV]
        exact Equation.hom_condition _ _ _ _ f.right
    refine ⟨Equation.homOfLabel _ _ _ _ b hg, ?_⟩
    apply Comma.hom_ext
    · apply Subtype.ext; apply Multiplicative.toAdd.injective
      exact hbU
    · apply Subtype.ext; apply Multiplicative.toAdd.injective
      exact hbV

/-- An overlap gauge can be strictified and all corrected local edge values glued. -/
theorem glue_solution (hc : ClosedRegion.Cover U V) (X : Descent M P δ U V) :
    ∃ (a : RelativeCover.C0 M U P × RelativeCover.C0 M V P)
      (h : RelativeCover.C1 M ClosedRegion.all P),
      RelativeCover.difference0 M P U V a = X.hom.1.toAdd ∧
      RelativeCover.diagonal1 M P U V h =
        (X.left.back.1, X.right.back.1) + RelativeCover.pairD0 M P U V a ∧
      RelativeCover.d1 M ClosedRegion.all P h = -δ := by
  obtain ⟨a,ha⟩ := RelativeCover.difference0_surjective M P U V X.hom.1.toAdd
  let localPair := (X.left.back.1, X.right.back.1)
  have hseam := Equation.hom_condition _ _ _ _ X.hom
  have hdiff : RelativeCover.difference1 M P U V localPair =
      -RelativeCover.d0 M (ClosedRegion.inter U V) P X.hom.1.toAdd := by
    change RelativeCover.r1 M P (ClosedRegion.inter_left U V) X.left.back.1 -
      RelativeCover.r1 M P (ClosedRegion.inter_right U V) X.right.back.1 = _
    change RelativeCover.r1 M P (ClosedRegion.inter_right U V) X.right.back.1 =
      RelativeCover.r1 M P (ClosedRegion.inter_left U V) X.left.back.1 + _ at hseam
    rw [hseam]
    abel
  have hz : RelativeCover.difference1 M P U V
      (localPair + RelativeCover.pairD0 M P U V a) = 0 := by
    rw [map_add, hdiff, RelativeCover.difference_d0, ha, neg_add_cancel]
  obtain ⟨h,hh⟩ := (RelativeCover.degree1_exact M P U V hc _).mp hz
  refine ⟨a,h,ha,hh,?_⟩
  apply RelativeCover.diagonal2_injective M P U V hc
  rw [RelativeCover.diagonal_d1, hh, map_neg]
  have hu := X.left.back.2
  have hv := X.right.back.2
  change (RelativeCover.d1 M U P
      (X.left.back.1 + RelativeCover.d0 M U P a.1),
    RelativeCover.d1 M V P
      (X.right.back.1 + RelativeCover.d0 M V P a.2)) =
    -(defect M P δ U, defect M P δ V)
  rw [map_add, map_add, RelativeCover.d1_d0, RelativeCover.d1_d0,
    hu, hv, add_zero, add_zero]
  rfl

/-- Each local descent datum is isomorphic to a restricted global solution. -/
theorem diagonal_ess_surj (hc : ClosedRegion.Cover U V) :
    (diagonalFunctor M P δ U V).EssSurj where
  mem_essImage X := by
    obtain ⟨a,h,ha,hh,heq⟩ := glue_solution M P δ U V hc X
    let global : Groupoid M P δ ClosedRegion.all :=
      ⟨(), ⟨h,by rw [defect_all]; exact heq⟩⟩
    have hu := congrArg Prod.fst hh
    have hv := congrArg Prod.snd hh
    change RelativeCover.r1 M P (ClosedRegion.to_all U) h =
      X.left.back.1 + RelativeCover.d0 M U P a.1 at hu
    change RelativeCover.r1 M P (ClosedRegion.to_all V) h =
      X.right.back.1 + RelativeCover.d0 M V P a.2 at hv
    have hu' : X.left.back.1 =
        ((diagonalObj M P δ U V global).left).back.1 + RelativeCover.d0 M U P (-a.1) := by
      change X.left.back.1 = RelativeCover.r1 M P (ClosedRegion.to_all U) h + _
      rw [hu, map_neg]; abel
    have hv' : X.right.back.1 =
        ((diagonalObj M P δ U V global).right).back.1 + RelativeCover.d0 M V P (-a.2) := by
      change X.right.back.1 = RelativeCover.r1 M P (ClosedRegion.to_all V) h + _
      rw [hv, map_neg]; abel
    let l := Equation.homOfLabel _ _ _ _ (-a.1) hu'
    let r := Equation.homOfLabel _ _ _ _ (-a.2) hv'
    refine ⟨global, ⟨Comma.isoMk (asIso l) (asIso r) ?_⟩⟩
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    change X.hom.1.toAdd +
      RelativeCover.r0 M P (ClosedRegion.inter_left U V) (-a.1) =
      RelativeCover.r0 M P (ClosedRegion.inter_right U V) (-a.2) + 0
    change RelativeCover.r0 M P (ClosedRegion.inter_left U V) a.1 -
      RelativeCover.r0 M P (ClosedRegion.inter_right U V) a.2 = X.hom.1.toAdd at ha
    rw [map_neg, map_neg, add_zero, ← ha]
    abel

/-- A closed cover generates full, faithful, essentially surjective descent. -/
theorem diagonal_is_equivalence (hc : ClosedRegion.Cover U V) :
    (diagonalFunctor M P δ U V).IsEquivalence where
  faithful := diagonal_faithful M P δ U V hc
  full := diagonal_full M P δ U V hc
  essSurj := diagonal_ess_surj M P δ U V hc

/-- Native binary descent follows from the generated relative cover exactness. -/
noncomputable def descentEquivalence (hc : ClosedRegion.Cover U V) :
    Groupoid M P δ ClosedRegion.all ≌ Descent M P δ U V := by
  letI := diagonal_is_equivalence M P δ U V hc
  exact (diagonalFunctor M P δ U V).asEquivalence

end CoverEquation
end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
