import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseAgainstComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawPointLaws
import Formal.Util.AssertStandardAxioms

/-!
# Direct raw coordinate and relation composition on common Hom points

Implementation notes: the carriers come from the original primitive raw object
tables. The second backward context graph selects the middle context. The
coordinate and relation graphs then compose in their original fiber direction.
Every candidate carrier and every inactive context row remains part of the
table. No complete native raw map is used to define these compositions.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site
open IndependentRawCandidate (coord rel)

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}

/-- All common coordinate inverse rows, indexed by their original source and target contexts. -/
def coordinateTable (h : Table.{u, v} U .explicit) :
    IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx B)
  | .edge W V a => InverseRows.coordinate h A B W V a

/-- All common relation-generator inverse rows with the same original context indices. -/
def relationTable (h : Table.{u, v} U .explicit) :
    IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx B)
  | .edge W V a => InverseRows.relation h A B W V a

variable (s : IndependentRawCandidate.Table.{u, v} A) (t : IndependentRawCandidate.Table.{u, v} B)
variable (r : IndependentRawCandidate.Table.{u, v} C)
variable (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)

include hp in
/-- Coordinate row laws follow directly from the original raw primitive conditions. -/
theorem coordinateTable_isLawful : IndependentIndexedInverseGraph.IsLawful (contextPoints h)
    (coord s) (coord t) (coordinateTable h) :=
  ⟨hp.coordinateInactive, hp.coordinateRows⟩

include hp in
/-- Relation row laws use their own original inverse and inactivity conditions. -/
theorem relationTable_isLawful : IndependentIndexedInverseGraph.IsLawful (contextPoints h)
    (rel s) (rel t) (relationTable h) :=
  ⟨hp.relationInactive, hp.relationRows⟩

variable (k : Table.{u, v} U .explicit)
variable (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true)
variable (hk : PointLaws t r k)

/-- Compose raw coordinate points against the independently specified backward context graph. -/
def composeCoordinate : IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx C) :=
  IndependentIndexedInverseGraph.composeAgainst (contextPoints h) (coord s) (coord t) (coord r)
    (coordinateTable h) (coordinateTable_isLawful s t h hp) (contextPoints k) hq
    (coordinateTable k) (coordinateTable_isLawful t r k hk)

/-- Compose relation-generator points with the same primitive middle context. -/
def composeRelation : IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u} (ArchCtx A) (ArchCtx C) :=
  IndependentIndexedInverseGraph.composeAgainst (contextPoints h) (rel s) (rel t) (rel r)
    (relationTable h) (relationTable_isLawful s t h hp) (contextPoints k) hq
    (relationTable k) (relationTable_isLawful t r k hk)

/-- Two true context points expose the direct coordinate-fiber composition at their middle context. -/
theorem composeCoordinate_active (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (hV : contextPoints k V Z = true) (hW : contextPoints h W V = true) :
    IndependentIndexedInverseGraph.row (composeCoordinate s t r h hp k hq hk) W Z =
      IndependentInverseGraph.compose (coord s W) (coord t V) (coord r Z)
        (InverseRows.coordinate h A B W V) (hp.coordinateRows W V hW)
        (InverseRows.coordinate k B C V Z) (hk.coordinateRows V Z hV) :=
  IndependentIndexedInverseGraph.composeAgainst_at_pair _ _ _ _ _ _ _ _ _ _ W V Z hV hW

/-- Two true context points expose the direct relation-generator composition. -/
theorem composeRelation_active (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (hV : contextPoints k V Z = true) (hW : contextPoints h W V = true) :
    IndependentIndexedInverseGraph.row (composeRelation s t r h hp k hq hk) W Z =
      IndependentInverseGraph.compose (rel s W) (rel t V) (rel r Z)
        (InverseRows.relation h A B W V) (hp.relationRows W V hW)
        (InverseRows.relation k B C V Z) (hk.relationRows V Z hV) :=
  IndependentIndexedInverseGraph.composeAgainst_at_pair _ _ _ _ _ _ _ _ _ _ W V Z hV hW

/-- A false first context point removes all composite coordinate candidate cells. -/
theorem composeCoordinate_inactive (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (hV : contextPoints k V Z = true) (hW : contextPoints h W V = false) :
    IndependentIndexedInverseGraph.row (composeCoordinate s t r h hp k hq hk) W Z = fun _ => false :=
  IndependentIndexedInverseGraph.composeAgainst_false_at_pair _ _ _ _ _ _ _ _ _ _ W V Z hV hW

/-- A false first context point removes all composite relation-generator candidate cells. -/
theorem composeRelation_inactive (W : ArchCtx A) (V : ArchCtx B) (Z : ArchCtx C)
    (hV : contextPoints k V Z = true) (hW : contextPoints h W V = false) :
    IndependentIndexedInverseGraph.row (composeRelation s t r h hp k hq hk) W Z = fun _ => false :=
  IndependentIndexedInverseGraph.composeAgainst_false_at_pair _ _ _ _ _ _ _ _ _ _ W V Z hV hW

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
