import ResearchLean.AG.QualitySurface.LawGeneratedIdealPowerSequence
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Subobject.Basic

/-!
# Law-generated ideal subpresheaf

This file constructs the additive presheaf carried by the law-generated
obstruction ideals.  It is a subpresheaf of the ambient observable presheaf by
construction: restriction stability follows from `map_obstructionIdeal_le`,
and the inclusion is an objectwise injective natural transformation.

Under a selected `HasSheafify` instance, the inclusion induces a morphism
between the additive sheafifications.  The canonical-unit square records the
provenance of that morphism.  This additive construction does not by itself
prove stability under a sheafified ring action and is therefore not asserted to
be an ideal subsheaf of a ring sheaf.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedIdealSubpresheaf

universe u

open CategoryTheory Limits Opposite
open AAT.AG AAT.AG.LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

/-- The ambient observable rings, read through their additive groups. -/
def observableCoefficient : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (G.Observable W.unop)
  map {X Y} φ := AddCommGrpCat.ofHom (G.restrict φ.unop).toAddMonoidHom
  map_id X := by
    ext x
    exact G.restrict_id X.unop x
  map_comp {X Y Z} φ ψ := by
    ext x
    exact G.restrict_comp ψ.unop φ.unop x

/-- Restriction on the subtype carried by the generated obstruction ideal. -/
def obstructionIdealRestrict {source target : S.category} (f : source ⟶ target) :
    G.obstructionIdeal target →+ G.obstructionIdeal source where
  toFun x :=
    ⟨G.restrict f x.1,
      (Ideal.map_le_iff_le_comap.mp (G.map_obstructionIdeal_le f)) x.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (G.restrict f)
  map_add' x y := by
    apply Subtype.ext
    exact map_add (G.restrict f) x.1 y.1

@[simp]
theorem obstructionIdealRestrict_val {source target : S.category}
    (f : source ⟶ target) (x : G.obstructionIdeal target) :
    (obstructionIdealRestrict G f x : G.Observable source) = G.restrict f x.1 :=
  rfl

/-- The additive presheaf whose sections are the generated obstruction ideals. -/
def obstructionIdealCoefficient : S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj W := AddCommGrpCat.of (G.obstructionIdeal W.unop)
  map {X Y} φ := AddCommGrpCat.ofHom (obstructionIdealRestrict G φ.unop)
  map_id X := by
    ext x
    exact G.restrict_id X.unop x.1
  map_comp {X Y Z} φ ψ := by
    ext x
    exact G.restrict_comp ψ.unop φ.unop x.1

/-- The generated obstruction ideals include naturally in the ambient observables. -/
def obstructionIdealInclusion :
    obstructionIdealCoefficient G ⟶ observableCoefficient G where
  app W := AddCommGrpCat.ofHom (G.obstructionIdeal W.unop).subtype.toAddMonoidHom
  naturality {X Y} φ := by
    ext x
    rfl

/-- The generated ideal inclusion is objectwise injective. -/
instance obstructionIdealInclusion_mono : Mono (obstructionIdealInclusion G) := by
  rw [NatTrans.mono_iff_mono_app]
  intro W
  rw [AddCommGrpCat.mono_iff_injective]
  exact Subtype.val_injective

/-- The generated additive ideal presheaf as a categorical subobject. -/
def obstructionIdealSubobject : Subobject (observableCoefficient G) :=
  Subobject.mk (obstructionIdealInclusion G)

/-! ## Canonical additive sheafification provenance -/

variable [HasSheafify S.topology AddCommGrpCat.{u}]

/-- The morphism induced between the canonical additive sheafifications. -/
noncomputable def sheafifiedObstructionIdealInclusion :
    (presheafToSheaf S.topology AddCommGrpCat.{u}).obj
        (obstructionIdealCoefficient G) ⟶
      (presheafToSheaf S.topology AddCommGrpCat.{u}).obj
        (observableCoefficient G) :=
  (presheafToSheaf S.topology AddCommGrpCat.{u}).map
    (obstructionIdealInclusion G)

/--
The canonical units commute with the generated inclusion and its sheafified
image.  This fixes the latter morphism's provenance in the raw law-generated
ideal inclusion.
-/
theorem sheafifiedObstructionIdealInclusion_provenance :
    obstructionIdealInclusion G ≫
        toSheafify S.topology (observableCoefficient G) =
      toSheafify S.topology (obstructionIdealCoefficient G) ≫
        (sheafifiedObstructionIdealInclusion G).val := by
  exact toSheafify_naturality S.topology (obstructionIdealInclusion G)

end LawGeneratedIdealSubpresheaf
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedIdealSubpresheaf
