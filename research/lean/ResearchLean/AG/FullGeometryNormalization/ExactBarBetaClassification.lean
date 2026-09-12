import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaProjection
import ResearchLean.AG.FullGeometryNormalization.ExactBarAlphaNormalizationNaturality
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeTransportIdentityClassification

/-!
# Classification of the exact selected complete-geometry comparison

This module completes the general classification part of G-122(C).  On the
selected branch, the actual bottom-push/right-pull projector is the canonical
normalization of the via-base endpoint, and its conjugate is the canonical
normalization of the direct endpoint.  Off that branch both projectors are
identities.  Consequently the selected comparison is invertible exactly off
the selector.

## Implementation notes

The selected endpoint identifications use the actual exact transport
naturality theorems.  The identity classification is reflected through the
proved core projection comparison and then discharged by G-116's selector
classification together with the established noninjectivity of canonical
object normalization.  Thus no endpoint admissibility, identity-reflection,
or noninjectivity certificate is accepted from the caller.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 3000000

/-- A local universe-polymorphic form of the standard fact that an invertible
idempotent endomorphism is the identity. -/
private theorem isIso_iff_eq_id_of_idempotent
    {C : Type u} [Category.{v} C] {X : C} (e : X ⟶ X)
    (idem : e ≫ e = e) :
    IsIso e ↔ e = 𝟙 X := by
  constructor
  · intro isIso
    letI : IsIso e := isIso
    exact (cancel_epi_id e).1 idem
  · rintro rfl
    infer_instance

/-- Conjugating the target endomorphism in a commuting square by its
comparison isomorphism recovers the source endomorphism. -/
private theorem iso_conjugate_eq_of_comm
    {C : Type u} [Category.{v} C] {X Y : C} (alpha : X ≅ Y)
    (source : X ⟶ X) (target : Y ⟶ Y)
    (comm : source ≫ alpha.hom = alpha.hom ≫ target) :
    alpha.hom ≫ target ≫ alpha.inv = source := by
  calc
    alpha.hom ≫ target ≫ alpha.inv =
        (source ≫ alpha.hom) ≫ alpha.inv :=
      by
        simpa only [Category.assoc] using
          congrArg (fun h => h ≫ alpha.inv) comm.symm
    _ = source := by simp

/-- On the selected branch, the transported target projector `barD` is the
canonical normalization of the actual via-base complete-geometry endpoint. -/
theorem authoredExactBarDAt_eq_endpoint_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactBarDAt A z omega k g =
      canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt A z k g)
        (authoredExactViaBaseGeometryAt_admissible A z k g selected.2) := by
  rw [authoredExactBarDAt_eq_normalization_route A z omega k g selected]
  change
    (exactGeometryPullFunctor (authoredExactRightInput A)).map
        ((geomFiberTransportFunctor
          (authoredExactBottomInput A).semantic.hom).map
            (canonicalGeometryFiberNormalization
              (authoredSouthwestGeometryFiberAt A z k g) selected.2)) = _
  rw [geomFiberTransportFunctor_map_normalization]
  simpa only [authoredExactViaBaseGeometryAt,
    authoredExactViaBaseGeometryAt_admissible,
    authoredExactTargetGeometryAt] using
      (exactGeometryPullFunctor_map_normalization
        (authoredExactRightInput A)
        (authoredExactTargetGeometryAt A z k g)
        (canonicalGeometryNormalizationAdmissible_exactTransport
          (authoredExactBottomInput A)
          (authoredSouthwestGeometryFiberAt A z k g) selected.2))

/-- On the selected branch, the conjugate source projector `barE` is the
canonical normalization of the actual direct complete-geometry endpoint. -/
theorem authoredExactBarEAt_eq_endpoint_normalization
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactBarEAt A z omega k g =
      canonicalGeometryFiberNormalization
        (authoredExactDirectGeometryAt A z k g)
        (authoredExactDirectGeometryAt_admissible A z k g selected.2) := by
  let alpha := authoredExactBarAlphaIsoAt A z k g
  let barD := authoredExactBarDAt A z omega k g
  let nDirect := canonicalGeometryFiberNormalization
    (authoredExactDirectGeometryAt A z k g)
    (authoredExactDirectGeometryAt_admissible A z k g selected.2)
  let nVia := canonicalGeometryFiberNormalization
    (authoredExactViaBaseGeometryAt A z k g)
    (authoredExactViaBaseGeometryAt_admissible A z k g selected.2)
  have naturality : nDirect ≫ alpha.hom = alpha.hom ≫ nVia := by
    simpa only [alpha, nDirect, nVia] using
      authoredExactBarAlphaIsoAt_normalization_natural
        A z k g selected.2
  have barDEq : barD = nVia := by
    simpa only [barD, nVia] using
      authoredExactBarDAt_eq_endpoint_normalization
        A z omega k g selected
  change alpha.hom ≫ barD ≫ alpha.inv = nDirect
  calc
    alpha.hom ≫ barD ≫ alpha.inv =
        alpha.hom ≫ nVia ≫ alpha.inv :=
      congrArg (fun h => alpha.hom ≫ h ≫ alpha.inv) barDEq
    _ = nDirect := iso_conjugate_eq_of_comm alpha nDirect nVia naturality

/-- The two selected complete-geometry projectors are exactly the canonical
normalizations of their respective generated endpoints. -/
theorem authoredExactBarProjectorsAt_eq_endpoint_normalizations
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (selected : omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
      (A.context.supportPackage z.as)) :
    authoredExactBarEAt A z omega k g =
        canonicalGeometryFiberNormalization
          (authoredExactDirectGeometryAt A z k g)
          (authoredExactDirectGeometryAt_admissible A z k g selected.2) ∧
      authoredExactBarDAt A z omega k g =
        canonicalGeometryFiberNormalization
          (authoredExactViaBaseGeometryAt A z k g)
          (authoredExactViaBaseGeometryAt_admissible A z k g selected.2) :=
  ⟨authoredExactBarEAt_eq_endpoint_normalization A z omega k g selected,
    authoredExactBarDAt_eq_endpoint_normalization A z omega k g selected⟩

/-- Off the selected branch, the conjugate source projector `barE` is the
identity. -/
theorem authoredExactBarEAt_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as))) :
    authoredExactBarEAt A z omega k g = 𝟙 _ := by
  rw [authoredExactBarEAt,
    authoredExactBarDAt_eq_id A z omega k g notSelected]
  simp

/-- Off the selected branch, both generated complete-geometry projectors are
identities. -/
theorem authoredExactBarProjectorsAt_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (notSelected : ¬ (omega z.as ≠ 1 ∧
      CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as))) :
    authoredExactBarEAt A z omega k g = 𝟙 _ ∧
      authoredExactBarDAt A z omega k g = 𝟙 _ :=
  ⟨authoredExactBarEAt_eq_id A z omega k g notSelected,
    authoredExactBarDAt_eq_id A z omega k g notSelected⟩

/-- The transported target projector is the identity exactly off the same
G-116 selector used to construct it. -/
theorem authoredExactBarDAt_eq_id_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    authoredExactBarDAt A z omega k g = 𝟙 _ ↔
      ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)) := by
  constructor
  · intro barDEqId selected
    let projection := geometryFiberProjection
      A.context.square.semantic.square.northeast
    let endpointIso := authoredExactViaBaseSupportCoreIsoAt A z k g
    have mappedEqId :
        projection.map (authoredExactBarDAt A z omega k g) = 𝟙 _ := by
      rw [barDEqId]
      exact projection.map_id _
    have projected := authoredExactBarDAt_projection A z omega k g
    rw [mappedEqId, Category.id_comp] at projected
    have collapseEqId :
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
            A omega z =
          𝟙 ((authoredSupportViaBaseRoute A.context).obj z) := by
      apply (cancel_epi endpointIso.hom).1
      simpa only [Category.comp_id] using projected.symm
    have outsideSelected :=
      (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_eq_id_iff
        A omega z).1 collapseEqId
    exact outsideSelected
      ⟨selected.1, selected.2,
        canonicalObjectNormalization_not_injective
          (A.context.supportPackage z.as)⟩
  · exact authoredExactBarDAt_eq_id A z omega k g

/-- Since `barAlpha` is invertible, the exact selected comparison is
invertible exactly when its target projector is invertible. -/
theorem authoredExactBarBetaAt_isIso_iff_barDAt_isIso
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    IsIso (authoredExactBarBetaAt A z omega k g) ↔
      IsIso (authoredExactBarDAt A z omega k g) := by
  change IsIso ((authoredExactBarAlphaIsoAt A z k g).hom ≫
      authoredExactBarDAt A z omega k g) ↔
    IsIso (authoredExactBarDAt A z omega k g)
  exact isIso_comp_left_iff _ _

/-- The exact selected comparison is invertible exactly when its idempotent
target projector is the identity. -/
theorem authoredExactBarBetaAt_isIso_iff_barDAt_eq_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    IsIso (authoredExactBarBetaAt A z omega k g) ↔
      authoredExactBarDAt A z omega k g = 𝟙 _ :=
  (authoredExactBarBetaAt_isIso_iff_barDAt_isIso A z omega k g).trans
    (isIso_iff_eq_id_of_idempotent
      (authoredExactBarDAt A z omega k g)
      (authoredExactBarDAt_idem A z omega k g))

/-- G-122(C), general raw-failure chain: invertibility of `barBeta` is
equivalent to identity of `barD`, and that identity occurs exactly off the
selected branch. -/
theorem authoredExactBarBetaAt_rawFailureLocus
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (IsIso (authoredExactBarBetaAt A z omega k g) ↔
      authoredExactBarDAt A z omega k g = 𝟙 _) ∧
    (authoredExactBarDAt A z omega k g = 𝟙 _ ↔
      ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as))) :=
  ⟨authoredExactBarBetaAt_isIso_iff_barDAt_eq_id A z omega k g,
    authoredExactBarDAt_eq_id_iff A z omega k g⟩

/-- The outer links of the exact selected comparison classification:
`barBeta` is invertible exactly off the G-116 selector. -/
theorem authoredExactBarBetaAt_isIso_iff_not_selected
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    IsIso (authoredExactBarBetaAt A z omega k g) ↔
      ¬ (omega z.as ≠ 1 ∧ CanonicalObjectNormalizationAdmissible
        (A.context.supportPackage z.as)) :=
  (authoredExactBarBetaAt_isIso_iff_barDAt_eq_id A z omega k g).trans
    (authoredExactBarDAt_eq_id_iff A z omega k g)

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
