import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Composition laws for full strict coordinate functors

## Implementation notes

These generic identities use both full functor inverse laws, rather than
object-map identities. The finite display application discharges these laws
with the accepted original repair-coordinate constructions.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory
universe uC uD uE uF vC vD vE vF
variable {C : Type uC} {D : Type uD} {E : Type uE} {F : Type uF}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vE} E] [Category.{vF} F]

/-- Changing a full coordinate display restores first and then reads the new display. -/
def strictComparison (e : C ≌ D) (f : C ≌ E) : D ≌ E := e.symm.trans f

/-- The comparison restores the same full original objects and arrows. -/
theorem strict_comparison_rec (e : C ≌ D) (f : C ≌ E)
    (hf : f.functor ⋙ f.inverse = 𝟭 C) :
    (strictComparison e f).functor ⋙ f.inverse = e.inverse := by
  change e.inverse ⋙ (f.functor ⋙ f.inverse) = e.inverse
  rw [hf,Functor.comp_id]

/-- Original full coordinates commute with changing their display. -/
theorem strict_comparison_coord (e : C ≌ D) (f : C ≌ E)
    (he : e.functor ⋙ e.inverse = 𝟭 C) :
    e.functor ⋙ (strictComparison e f).functor = f.functor := by
  change (e.functor ⋙ e.inverse) ⋙ f.functor = f.functor
  rw [he,Functor.id_comp]

/-- Three display changes compose as whole functors, including transported arrows. -/
theorem strict_comparison_comp (e : C ≌ D) (f : C ≌ E) (g : C ≌ F)
    (hf : f.functor ⋙ f.inverse = 𝟭 C) :
    (strictComparison e f).functor ⋙ (strictComparison f g).functor =
      (strictComparison e g).functor := by
  change e.inverse ⋙ ((f.functor ⋙ f.inverse) ⋙ g.functor) = e.inverse ⋙ g.functor
  rw [hf,Functor.id_comp]

/-- The complete comparison has a strict inverse on the old display. -/
theorem strict_comparison_inverse (e : C ≌ D) (f : C ≌ E)
    (hf : f.functor ⋙ f.inverse = 𝟭 C) (he : e.inverse ⋙ e.functor = 𝟭 D) :
    (strictComparison e f).functor ⋙ (strictComparison e f).inverse = 𝟭 D := by
  change e.inverse ⋙ ((f.functor ⋙ f.inverse) ⋙ e.functor) = 𝟭 D
  rw [hf,Functor.id_comp]
  exact he

/-- The complete inverse comparison is strict on the new display as well. -/
theorem strict_inverse_comparison (e : C ≌ D) (f : C ≌ E)
    (he : e.functor ⋙ e.inverse = 𝟭 C) (hf : f.inverse ⋙ f.functor = 𝟭 E) :
    (strictComparison e f).inverse ⋙ (strictComparison e f).functor = 𝟭 E := by
  change f.inverse ⋙ ((e.functor ⋙ e.inverse) ⋙ f.functor) = 𝟭 E
  rw [he,Functor.id_comp]
  exact hf

/-- Composing constructed strict coordinate equivalences preserves the full forward-inverse law. -/
theorem strict_trans_functor_inverse (e : C ≌ D) (f : D ≌ E)
    (he : e.functor ⋙ e.inverse = 𝟭 C) (hf : f.functor ⋙ f.inverse = 𝟭 D) :
    (e.trans f).functor ⋙ (e.trans f).inverse = 𝟭 C :=
  strict_comparison_inverse e.symm f hf he

/-- Composing constructed strict coordinate equivalences preserves the full inverse-forward law. -/
theorem strict_trans_inverse_functor (e : C ≌ D) (f : D ≌ E)
    (he : e.inverse ⋙ e.functor = 𝟭 D) (hf : f.inverse ⋙ f.functor = 𝟭 E) :
    (e.trans f).inverse ⋙ (e.trans f).functor = 𝟭 E :=
  strict_inverse_comparison e.symm f he hf

end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
