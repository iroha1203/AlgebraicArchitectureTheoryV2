import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerShortExact
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Unconditional sheafification of the law-generated ideal-power sequence

The raw law-generated short exact sequence takes values in
`AddCommGrpCat.{u}` while the category of contexts and its covers live one
universe higher.  We first apply Mathlib's fully faithful additive universe-lift
functor objectwise.  The resulting `AddCommGrpCat.{u + 1}`-valued presheaves
support Mathlib's concrete canonical sheafification on every selected AAT site.

Both steps preserve finite limits and finite colimits, so the generated short
exact sequence remains short exact.  No `HasSheafify` premise, selected sheaf,
or exactness certificate is accepted.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedIdealPowerLiftedSheafification

universe u

open CategoryTheory Limits Opposite
open AAT.AG AAT.AG.LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

/-- The original coefficient-presheaf category of the generated raw sequence. -/
abbrev SmallPresheafCategory :=
  S.categoryᵒᵖ ⥤ AddCommGrpCat.{u}

/-- The one-universe-larger coefficient-presheaf category used for sheafification. -/
abbrev LargePresheafCategory :=
  S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1}

/-- Apply the additive-group universe lift objectwise to a raw coefficient presheaf. -/
noncomputable abbrev liftPresheafFunctor :
    SmallPresheafCategory (S := S) ⥤ LargePresheafCategory (S := S) :=
  (Functor.whiskeringRight S.categoryᵒᵖ
    AddCommGrpCat.{u} AddCommGrpCat.{u + 1}).obj
      AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Objectwise universe lift is additive on the coefficient-presheaf category. -/
instance liftPresheafFunctor_additive :
    (liftPresheafFunctor (S := S)).Additive where
  map_add := by
    intro X Y f g
    ext W x
    rfl

/-- The generated raw short complex after objectwise coefficient universe lift. -/
noncomputable def liftedShortComplex :
    ShortComplex (LargePresheafCategory (S := S)) :=
  (LawGeneratedIdealPowerSequence.Raw.shortComplex G).map
    (liftPresheafFunctor (S := S))

/-- Objectwise universe lift preserves the generated raw short exact sequence. -/
theorem liftedShortComplex_shortExact :
    (liftedShortComplex G).ShortExact :=
  (LawGeneratedIdealPowerSequence.Raw.shortComplex_shortExact G).map_of_exact
    (liftPresheafFunctor (S := S))

/--
The universe-lifted sequence sent through Mathlib's canonical additive
sheafification.  At coefficient universe `u + 1`, the concrete
`HasSheafify` instance is inferred for every AAT site.
-/
noncomputable def sheafifiedShortComplex :
    ShortComplex (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
  (liftedShortComplex G).map
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1})

/-- Canonical large-universe sheafification preserves the generated short exact sequence. -/
theorem sheafifiedShortComplex_shortExact :
    (sheafifiedShortComplex G).ShortExact :=
  (liftedShortComplex_shortExact G).map_of_exact
    (presheafToSheaf S.topology AddCommGrpCat.{u + 1})

end LawGeneratedIdealPowerLiftedSheafification
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerLiftedSheafification
