import ResearchLean.AG.RelativeRepairComposition.SupplementalAction

/-!
# Native contraction of the whole supplemental translation groupoid

## Implementation notes

Projection keeps every old object and old label. The zero section is an inverse
functor, and the counit restores each arbitrary full supplemental value by its
entire translation label. No supplemental objects or original stabilizers are
removed from the source groupoid.
-/
namespace AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction
open CategoryTheory
universe ug uy ur
variable (G : Type ug) (Y : Type uy) (R : Type ur)
variable [AddCommGroup G] [AddCommGroup R] [AddAction G Y]

/-- Every old native label is retained by projection. -/
def labelProjection : Multiplicative (G × R) →* Multiplicative G where
  toFun b := Multiplicative.ofAdd b.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inverse section retains the whole old label with zero supplemental displacement. -/
def labelSection : Multiplicative G →* Multiplicative (G × R) where
  toFun b := Multiplicative.ofAdd (b.toAdd,0)
  map_one' := rfl
  map_mul' b c := by
    apply Multiplicative.ofAdd.injective
    exact Prod.ext rfl (zero_add (0 : R)).symm

/-- Projection preserves every old native object and every old native arrow. -/
def projection : ActionCategory (Multiplicative (G × R)) (Y × R) ⥤ ActionCategory (Multiplicative G) Y :=
  actionLabelFunctor (labelProjection G R) Prod.fst (by intro b y; rfl)

/-- A zero supplemental section preserves every old object and every original arrow. -/
def sectionFunctor : ActionCategory (Multiplicative G) Y ⥤ ActionCategory (Multiplicative (G × R)) (Y × R) :=
  actionLabelFunctor (labelSection G R) (fun y => (y,0)) (by
    intro b y
    apply Prod.ext
    · rfl
    · exact (zero_add (0 : R)).symm)

/-- Every arbitrary supplemental object is restored by the whole original translation label. -/
def counitComponent (x : ActionCategory (Multiplicative (G × R)) (Y × R)) :
    (projection G Y R ⋙ sectionFunctor G Y R).obj x ≅ x where
  hom := ⟨Multiplicative.ofAdd (0,x.back.2),by
    apply Prod.ext
    · exact zero_vadd G x.back.1
    · exact zero_add x.back.2⟩
  inv := ⟨Multiplicative.ofAdd (0,-x.back.2),by
    apply Prod.ext
    · exact zero_vadd G x.back.1
    · exact add_neg_cancel x.back.2⟩
  hom_inv_id := by
    apply Subtype.ext
    apply Multiplicative.ofAdd.injective
    exact Prod.ext (zero_add (0 : G)) (neg_add_cancel x.back.2)
  inv_hom_id := by
    apply Subtype.ext
    apply Multiplicative.ofAdd.injective
    exact Prod.ext (zero_add (0 : G)) (add_neg_cancel x.back.2)

/-- The entire supplemental restoration is natural on all old and supplemental native labels. -/
def counitIso : projection G Y R ⋙ sectionFunctor G Y R ≅ 𝟭 _ :=
  NatIso.ofComponents (counitComponent G Y R) (by
    intro x y f
    apply Subtype.ext
    apply Multiplicative.ofAdd.injective
    have hv := congrArg Prod.snd f.2
    change x.back.2 + f.1.toAdd.2 = y.back.2 at hv
    change (0 + f.1.toAdd.1,y.back.2 + 0) = (f.1.toAdd.1 + 0,f.1.toAdd.2 + x.back.2)
    simp only [zero_add,add_zero]
    exact Prod.ext rfl (hv.symm.trans (add_comm _ _)))

/-- Every old object and label is fixed exactly by section followed by projection. -/
def unitIso : 𝟭 (ActionCategory (Multiplicative G) Y) ≅ sectionFunctor G Y R ⋙ projection G Y R :=
  NatIso.ofComponents (F := 𝟭 (ActionCategory (Multiplicative G) Y))
    (G := sectionFunctor G Y R ⋙ projection G Y R)
    (fun x => eqToIso (ActionCategory.back_coe x).symm) (by
    intro x y f
    apply Subtype.ext
    change (show Multiplicative G from (eqToHom (ActionCategory.back_coe y).symm).1) *
        (show Multiplicative G from f.1) =
      (show Multiplicative G from f.1) *
        (show Multiplicative G from (eqToHom (ActionCategory.back_coe x).symm).1)
    rw [action_eqToHom_label,action_eqToHom_label,one_mul,mul_one])

/-- The full supplemental translation groupoid is contractible while all original stabilizer labels survive. -/
def equivalence : ActionCategory (Multiplicative G) Y ≌ ActionCategory (Multiplicative (G × R)) (Y × R) where
  functor := sectionFunctor G Y R
  inverse := projection G Y R
  unitIso := unitIso G Y R
  counitIso := counitIso G Y R
  functor_unitIso_comp x := by
    apply Subtype.ext
    change Multiplicative.ofAdd (0,(0 : R)) *
      labelSection G R (eqToHom (ActionCategory.back_coe x).symm).1 = (1 : Multiplicative (G × R))
    rw [action_eqToHom_label,map_one]
    exact one_mul _

/-- The full counit label reads exactly zero old label and the actual arbitrary supplemental value. -/
theorem counit_label (x : ActionCategory (Multiplicative (G × R)) (Y × R)) :
    ((counitIso G Y R).hom.app x).1.toAdd = (0,x.back.2) := rfl

end AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.SupplementalGroupoidContraction
