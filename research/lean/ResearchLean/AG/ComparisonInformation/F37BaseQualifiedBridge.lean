import ResearchLean.AG.ComparisonInformation.F37GeneralComparison
import ResearchLean.AG.RealizationComparisonIdempotents.QualifiedComparisonGroup
import Formal.Util.AssertStandardAxioms

/-!
# Base-qualified specialization of the general comparison group

This module specializes Definition 7.2 to the composite-fiber automorphism
subgroups of complete geometries.  The specialization has exactly the
comparison equation used by the existing `qualifiedComparisonSubgroup`, and
the isomorphism retains both endpoint changes.  Composing with the existing
reversible-comparison equivalence identifies the same group with the
base-qualified automorphisms of the identity-idempotent comparison in `M(E)`.

Implementation notes: this is a comparison of independently existing
subgroups, not a second definition of the base-fixed group.  The source and
target projection equations below witness that the identification preserves
the actual automorphism data.
-/

open CategoryTheory

namespace AAT.AG.ComparisonInformation

open AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct RealizationComparisonIdempotents

universe u v

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}

/-- Proposition 7.3: the general comparison group, restricted to the two
composite-fiber automorphism subgroups, is the previously constructed
base-qualified comparison group of a complete geometry comparison. -/
noncomputable def baseQualifiedGeneralComparisonMulEquiv
    (c : GeometryTotalHom G H) :
    generalComparisonSubgroup c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) ≃*
      qualifiedComparisonSubgroup c where
  toFun pair := ⟨pair.1, by
    change pair.1.1.1.hom ≫ c = c ≫ pair.1.2.1.hom
    exact pair.2⟩
  invFun pair := ⟨pair.1, by
    change pair.1.1.1.hom ≫ c = c ≫ pair.1.2.1.hom
    exact pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The specialization retains the source endpoint projection. -/
@[simp] theorem baseQualifiedGeneralComparison_source_projection
    (c : GeometryTotalHom G H)
    (pair : generalComparisonSubgroup c
      (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H)) :
    qualifiedComparisonSourceProjection c
        (baseQualifiedGeneralComparisonMulEquiv c pair) =
      generalComparisonSourceProjection c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) pair :=
  rfl

/-- The specialization retains the target endpoint projection. -/
@[simp] theorem baseQualifiedGeneralComparison_target_projection
    (c : GeometryTotalHom G H)
    (pair : generalComparisonSubgroup c
      (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H)) :
    qualifiedComparisonTargetProjection c
        (baseQualifiedGeneralComparisonMulEquiv c pair) =
      generalComparisonTargetProjection c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) pair :=
  rfl

/-- Proposition 7.3's base-fixed comparison group in `M(E_geom)` follows
from the general subgroup specialization and the existing reversible-square
construction; no extra condition is imposed on the comparison itself. -/
noncomputable def baseQualifiedGeneralReversibleMulEquiv
    (c : GeometryTotalHom G H) :
    generalComparisonSubgroup c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) ≃*
      baseQualifiedReversibleComparisonSubgroup c :=
  (baseQualifiedGeneralComparisonMulEquiv c).trans
    (qualifiedComparisonReversibleMulEquiv c)

/-- The composed identification commutes with the source projection. -/
@[simp] theorem baseQualifiedGeneralReversible_source_projection
    (c : GeometryTotalHom G H)
    (pair : generalComparisonSubgroup c
      (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H)) :
    baseQualifiedReversibleComparisonSourceProjection c
        (baseQualifiedGeneralReversibleMulEquiv c pair) =
      generalComparisonSourceProjection c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) pair :=
  rfl

/-- The composed identification commutes with the target projection. -/
@[simp] theorem baseQualifiedGeneralReversible_target_projection
    (c : GeometryTotalHom G H)
    (pair : generalComparisonSubgroup c
      (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H)) :
    baseQualifiedReversibleComparisonTargetProjection c
        (baseQualifiedGeneralReversibleMulEquiv c pair) =
      generalComparisonTargetProjection c
        (compositeFiberAutSubgroup G) (compositeFiberAutSubgroup H) pair :=
  rfl

end AAT.AG.ComparisonInformation

#assert_standard_axioms_only AAT.AG.ComparisonInformation
