import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalLinearCoordinates

/-!
# Complete finite bases of the same actual subdivided coefficient kernels

## Implementation notes

Every old vertex keeps its input basis literally. The fresh basis uses the
inverse of the actual first transport followed by the original source basis.
This constructs finite coordinates on the whole fresh kernel without changing
its carrier or defining new matrix outputs from an old elimination result.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)

/-- All old full bases and the generated fresh full basis use the actual original kernel. -/
noncomputable def expandedBases :
    FiniteFamily.Bases (k := k) (originalTower T chosen F).toTower.localCoefficients.A where
  dimension
    | .inl v => bases.dimension v
    | .inr _ => bases.dimension chosen.1
  coordinate
    | .inl v => bases.coordinate v
    | .inr _ => (LinearCoefficients.rho1LinearEquiv (k := k) T chosen F).symm.trans
        (bases.coordinate chosen.1)

/-- The original complete dimension is unchanged at every retained vertex. -/
theorem expanded_dimension_old (v : K.Vertex) :
    (expandedBases T chosen F bases).dimension (.inl v) = bases.dimension v := rfl

/-- The fresh complete dimension is generated from the original chosen source. -/
theorem expanded_dimension_fresh :
    (expandedBases T chosen F bases).dimension (.inr ()) = bases.dimension chosen.1 := rfl

/-- Every retained actual coefficient has exactly the original full basis coordinates. -/
theorem expanded_coordinate_old (v : K.Vertex) (x : T.toTower.localCoefficients.A v) :
    (expandedBases T chosen F bases).coordinate (.inl v) x = bases.coordinate v x := rfl

/-- The fresh coordinates read the inverse actual transport before the old source basis. -/
theorem expanded_coordinate_fresh
    (x : (originalTower T chosen F).toTower.localCoefficients.A (.inr ())) :
    (expandedBases T chosen F bases).coordinate (.inr ()) x =
      bases.coordinate chosen.1 ((rho1AddEquiv T chosen F).symm x) := rfl

/-- Restoration uses the actual first transport of the complete original source value. -/
theorem expanded_coordinate_fresh_inverse (x : Fin (bases.dimension chosen.1) → k) :
    ((expandedBases T chosen F bases).coordinate (.inr ())).symm x =
      rho1AddEquiv T chosen F ((bases.coordinate chosen.1).symm x) := rfl

/-- Full fresh reconstruction followed by extraction retains every basis component. -/
theorem expanded_fresh_roundtrip (x : Fin (bases.dimension chosen.1) → k) :
    (expandedBases T chosen F bases).coordinate (.inr ())
      (rho1AddEquiv T chosen F ((bases.coordinate chosen.1).symm x)) = x :=
  ((expandedBases T chosen F bases).coordinate (.inr ())).apply_symm_apply x

end AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.FiniteBases
