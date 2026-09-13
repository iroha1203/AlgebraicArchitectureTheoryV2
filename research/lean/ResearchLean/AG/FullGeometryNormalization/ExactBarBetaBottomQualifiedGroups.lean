import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaComparisonGroup

/-!
# Bottom-qualified groups for the actual selector comparison

The endpoints of the actual `barAlpha`/`barBeta` comparison live in one
geometry fiber.  Consequently every endpoint automorphism has identity
package-base map.  This module records that fact as an actual `packagePoint`
predicate, then builds the bottom-qualified endpoint, centralizing,
raw-compatible, and Karoubi-image subgroup hierarchy used by G-122(D).

The qualified groups are not defined as aliases for `top`: their defining
carrier is the literal endpoint bottom identity.  Their `eq_top` theorems are
derived from the fiber lift law.  This keeps the predicate visible to the
later section, reflection, and exactness arguments while recording that it is
automatic for the actual selector endpoints.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.FullGeometryNormalization

universe u v

open AtomFoundation GeometryTransport CrossStageCoherence DoctrineFiberProduct
open TransportCoherence ComparisonInformationLoss

set_option synthInstance.maxHeartbeats 100000

/-! ## The actual bottom identity in a geometry fiber -/

/-- Every morphism internal to one geometry fiber has identity package-base
map.  This is the actual `πρ` equation supplied by the fiber lift law. -/
theorem geometryFiberMorphism_packageBase_identity
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P : GeomFiber.{u, v} X} (f : P ⟶ P) :
    f.1.base.base = 𝟙 (packagePoint P.1.core) := by
  letI := f.2
  have h := CategoryTheory.IsHomLift.fac'
    (crossStageProjection.{u, v} U) (𝟙 X) f.1
  rw [crossStageProjection_map] at h
  simpa using h

/-- Raw endpoint automorphisms whose actual package-base map is identity. -/
noncomputable def geometryFiberBottomEndpointSubgroup
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : GeomFiber.{u, v} X) : Subgroup (Aut P) where
  carrier a := a.hom.1.base.base = 𝟙 (packagePoint P.1.core)
  one_mem' := geometryFiberMorphism_packageBase_identity (𝟙 P)
  mul_mem' := by
    intro a b _ _
    exact geometryFiberMorphism_packageBase_identity (a * b).hom
  inv_mem' := by
    intro a _
    exact geometryFiberMorphism_packageBase_identity a.inv

/-- Membership in the raw fiber endpoint bottom subgroup is the literal
package-base identity predicate. -/
theorem mem_geometryFiberBottomEndpointSubgroup
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P : GeomFiber.{u, v} X} {a : Aut P} :
    a ∈ geometryFiberBottomEndpointSubgroup P ↔
      a.hom.1.base.base = 𝟙 (packagePoint P.1.core) := by
  change (a.hom.1.base.base = 𝟙 (packagePoint P.1.core)) ↔ _
  rfl

/-- The raw endpoint bottom subgroup is all automorphisms, as a theorem
derived from the fiber lift law. -/
theorem geometryFiberBottomEndpointSubgroup_eq_top
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : GeomFiber.{u, v} X) :
    geometryFiberBottomEndpointSubgroup P = ⊤ := by
  apply top_unique
  intro a _
  change a.hom.1.base.base = 𝟙 (packagePoint P.1.core)
  exact geometryFiberMorphism_packageBase_identity a.hom

/-- Karoubi endpoint automorphisms whose underlying fiber morphism has
identity package-base map. -/
noncomputable def geometryFiberKaroubiBottomEndpointSubgroup
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : Karoubi (GeomFiber.{u, v} X)) : Subgroup (Aut P) where
  carrier a := a.hom.f.1.base.base = 𝟙 (packagePoint P.X.1.core)
  one_mem' := geometryFiberMorphism_packageBase_identity
    ((𝟙 P : P ⟶ P).f)
  mul_mem' := by
    intro a b _ _
    exact geometryFiberMorphism_packageBase_identity (a * b).hom.f
  inv_mem' := by
    intro a _
    exact geometryFiberMorphism_packageBase_identity a.inv.f

/-- Membership in the Karoubi endpoint bottom subgroup is the literal
underlying package-base identity predicate. -/
theorem mem_geometryFiberKaroubiBottomEndpointSubgroup
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {P : Karoubi (GeomFiber.{u, v} X)} {a : Aut P} :
    a ∈ geometryFiberKaroubiBottomEndpointSubgroup P ↔
      a.hom.f.1.base.base = 𝟙 (packagePoint P.X.1.core) := by
  change (a.hom.f.1.base.base = 𝟙 (packagePoint P.X.1.core)) ↔ _
  rfl

/-- The Karoubi endpoint bottom subgroup is all automorphisms, again derived
from the underlying fiber lift law. -/
theorem geometryFiberKaroubiBottomEndpointSubgroup_eq_top
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : Karoubi (GeomFiber.{u, v} X)) :
    geometryFiberKaroubiBottomEndpointSubgroup P = ⊤ := by
  apply top_unique
  intro a _
  change a.hom.f.1.base.base = 𝟙 (packagePoint P.X.1.core)
  exact geometryFiberMorphism_packageBase_identity a.hom.f

/-! ## Named actual endpoint groups -/

noncomputable abbrev AuthoredExactRawSourceBottomEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  geometryFiberBottomEndpointSubgroup
    (authoredExactDirectGeometryAt A z k g)

noncomputable abbrev AuthoredExactRawTargetBottomEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  geometryFiberBottomEndpointSubgroup
    (authoredExactViaBaseGeometryAt A z k g)

noncomputable abbrev AuthoredExactKaroubiSourceBottomEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  geometryFiberKaroubiBottomEndpointSubgroup
    (authoredExactBarESourceKaroubiAt A z omega k g)

noncomputable abbrev AuthoredExactKaroubiTargetBottomEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :=
  geometryFiberKaroubiBottomEndpointSubgroup
    (authoredExactBarDTargetKaroubiAt A z omega k g)

/-! ## Bottom-qualified centralizing and comparison hierarchy -/

private noncomputable def authoredExactCentralizingSourceHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactCentralizingEndpointSubgroup A z omega k g →*
      Aut (authoredExactDirectGeometryAt A z k g) where
  toFun pair := pair.1.1
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def authoredExactCentralizingTargetHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactCentralizingEndpointSubgroup A z omega k g →*
      Aut (authoredExactViaBaseGeometryAt A z k g) where
  toFun pair := pair.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Bottom-qualified endpoint-centralizing pairs. -/
noncomputable def AuthoredExactBottomCentralizingEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup (AuthoredExactCentralizingEndpointSubgroup A z omega k g) :=
  Subgroup.comap (authoredExactCentralizingSourceHom A z omega k g)
      (AuthoredExactRawSourceBottomEndpointSubgroup A z k g) ⊓
    Subgroup.comap (authoredExactCentralizingTargetHom A z omega k g)
      (AuthoredExactRawTargetBottomEndpointSubgroup A z k g)

/-- Bottom-qualified centralizing membership is the two actual package-base
identity equations. -/
theorem mem_AuthoredExactBottomCentralizingEndpointSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {A : AuthoredBCDatumSquare U} {z : A.context.Category}
    {omega : DefectCochain A.toTransportData}
    {k : Type v} [CommRing k]
    {g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k}
    {pair : AuthoredExactCentralizingEndpointSubgroup A z omega k g} :
    pair ∈ AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g ↔
      pair.1.1.hom.1.base.base =
          𝟙 (packagePoint (authoredExactDirectGeometryAt A z k g).1.core) ∧
        pair.1.2.hom.1.base.base =
          𝟙 (packagePoint (authoredExactViaBaseGeometryAt A z k g).1.core) := by
  change
    (pair.1.1 ∈ AuthoredExactRawSourceBottomEndpointSubgroup A z k g ∧
      pair.1.2 ∈ AuthoredExactRawTargetBottomEndpointSubgroup A z k g) ↔ _
  rw [mem_geometryFiberBottomEndpointSubgroup,
    mem_geometryFiberBottomEndpointSubgroup]

/-- Actual fiber centralizing pairs are automatically bottom-qualified. -/
theorem AuthoredExactBottomCentralizingEndpointSubgroup_eq_top
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g = ⊤ := by
  apply top_unique
  intro pair _
  rw [mem_AuthoredExactBottomCentralizingEndpointSubgroup]
  exact ⟨geometryFiberMorphism_packageBase_identity pair.1.1.hom,
    geometryFiberMorphism_packageBase_identity pair.1.2.hom⟩

/-- Bottom-qualified centralizing pairs preserving the reversible raw
comparison `barAlpha`. -/
noncomputable def AuthoredExactBottomCentralizingRawComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup (AuthoredExactBottomCentralizingEndpointSubgroup
      A z omega k g) :=
  Subgroup.comap
    (AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g).subtype
    (AuthoredExactCentralizingRawComparisonSubgroup A z omega k g)

/-- Inside the bottom-qualified centralizing group, membership is exactly
compatibility with the reversible raw comparison `barAlpha`. -/
theorem mem_AuthoredExactBottomCentralizingRawComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {A : AuthoredBCDatumSquare U} {z : A.context.Category}
    {omega : DefectCochain A.toTransportData}
    {k : Type v} [CommRing k]
    {g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k}
    {pair : AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g} :
    pair ∈ AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g ↔
      pair.1.1.1.hom ≫ (authoredExactBarAlphaIsoAt A z k g).hom =
        (authoredExactBarAlphaIsoAt A z k g).hom ≫ pair.1.1.2.hom := by
  rfl

private noncomputable def authoredExactKaroubiEndpointSourceHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
      Aut (authoredExactBarDTargetKaroubiAt A z omega k g)) →*
      Aut (authoredExactBarESourceKaroubiAt A z omega k g) where
  toFun pair := pair.1
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def authoredExactKaroubiEndpointTargetHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
      Aut (authoredExactBarDTargetKaroubiAt A z omega k g)) →*
      Aut (authoredExactBarDTargetKaroubiAt A z omega k g) where
  toFun pair := pair.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Pairs of actual Karoubi endpoint automorphisms which are both trivial at
the package bottom. -/
noncomputable def AuthoredExactBottomKaroubiEndpointPairSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup (Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
      Aut (authoredExactBarDTargetKaroubiAt A z omega k g)) :=
  Subgroup.comap (authoredExactKaroubiEndpointSourceHom A z omega k g)
      (AuthoredExactKaroubiSourceBottomEndpointSubgroup A z omega k g) ⊓
    Subgroup.comap (authoredExactKaroubiEndpointTargetHom A z omega k g)
      (AuthoredExactKaroubiTargetBottomEndpointSubgroup A z omega k g)

/-- Membership in the bottom Karoubi endpoint product is the two literal
package-base identity equations. -/
theorem mem_AuthoredExactBottomKaroubiEndpointPairSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {A : AuthoredBCDatumSquare U} {z : A.context.Category}
    {omega : DefectCochain A.toTransportData}
    {k : Type v} [CommRing k]
    {g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k}
    {pair : Aut (authoredExactBarESourceKaroubiAt A z omega k g) ×
      Aut (authoredExactBarDTargetKaroubiAt A z omega k g)} :
    pair ∈ AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g ↔
      pair.1.hom.f.1.base.base =
          𝟙 (packagePoint (authoredExactDirectGeometryAt A z k g).1.core) ∧
        pair.2.hom.f.1.base.base =
          𝟙 (packagePoint (authoredExactViaBaseGeometryAt A z k g).1.core) := by
  change
    (pair.1 ∈ AuthoredExactKaroubiSourceBottomEndpointSubgroup A z omega k g ∧
      pair.2 ∈ AuthoredExactKaroubiTargetBottomEndpointSubgroup A z omega k g) ↔ _
  rw [mem_geometryFiberKaroubiBottomEndpointSubgroup,
    mem_geometryFiberKaroubiBottomEndpointSubgroup]
  rfl

/-- Every actual Karoubi endpoint pair is bottom-qualified, by the fiber lift
law rather than by definition. -/
theorem AuthoredExactBottomKaroubiEndpointPairSubgroup_eq_top
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g = ⊤ := by
  apply top_unique
  intro pair _
  rw [mem_AuthoredExactBottomKaroubiEndpointPairSubgroup]
  exact ⟨geometryFiberMorphism_packageBase_identity pair.1.hom.f,
    geometryFiberMorphism_packageBase_identity pair.2.hom.f⟩

/-- Bottom-qualified Karoubi endpoint pairs which preserve the actual image
comparison `barBeta`. -/
noncomputable def AuthoredExactBottomKaroubiComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup (AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g) :=
  Subgroup.comap
    (AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g).subtype
    (AuthoredExactKaroubiComparisonSubgroup A z omega k g)

/-- Bottom image membership is exactly preservation of the actual Karoubi
comparison inside the typed bottom endpoint product. -/
theorem mem_AuthoredExactBottomKaroubiComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {A : AuthoredBCDatumSquare U} {z : A.context.Category}
    {omega : DefectCochain A.toTransportData}
    {k : Type v} [CommRing k]
    {g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k}
    {pair : AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g} :
    pair ∈ AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g ↔
      pair.1.1.hom ≫ (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom =
        (authoredExactBarBetaKaroubiIsoAt A z omega k g).hom ≫
          pair.1.2.hom := by
  rfl

/-- Bottom-qualified centralizing pairs preserving the same ambient
`barBeta`; this is the typed preimage group used by reflection. -/
noncomputable def AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    Subgroup (AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g) :=
  Subgroup.comap
    (AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g).subtype
    (centralizingCompatibleSubgroup
      (authoredExactBarBetaAt A z omega k g)
      (authoredExactBarEAt A z omega k g)
      (authoredExactBarDAt A z omega k g))

/-- Membership in the typed `barBeta` group is literal ambient `barBeta`
compatibility. -/
theorem mem_AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {A : AuthoredBCDatumSquare U} {z : A.context.Category}
    {omega : DefectCochain A.toTransportData}
    {k : Type v} [CommRing k]
    {g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k}
    {pair : AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g} :
    pair ∈ AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
        A z omega k g ↔
      pair.1.1.1.hom ≫ authoredExactBarBetaAt A z omega k g =
        authoredExactBarBetaAt A z omega k g ≫ pair.1.1.2.hom := by
  rfl

/-! ## Typed subgroup reassociation -/

/-- A bottom-qualified raw-compatible pair remains a bottom-qualified
centralizing endpoint pair after forgetting raw compatibility. -/
noncomputable def authoredExactBottomRawToCentralizingHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g →*
      AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g where
  toFun pair := pair.1
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem authoredExactBottomRawToCentralizingHom_val
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingRawComparisonSubgroup
      A z omega k g) :
    authoredExactBottomRawToCentralizingHom A z omega k g pair = pair.1 :=
  rfl

/-- Reassociation of the actual bottom-qualified centralizing group with the
already accepted ambient centralizing group. -/
noncomputable def authoredExactBottomCentralizingEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g ≃*
      AuthoredExactCentralizingEndpointSubgroup A z omega k g where
  toFun pair := pair.1
  invFun pair := ⟨pair, by
    rw [AuthoredExactBottomCentralizingEndpointSubgroup_eq_top]
    trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Reassociation of the bottom-qualified raw-compatible group with the
accepted raw-compatible group. -/
noncomputable def authoredExactBottomRawComparisonEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g ≃*
      AuthoredExactCentralizingRawComparisonSubgroup A z omega k g where
  toFun pair := ⟨pair.1.1, pair.2⟩
  invFun pair :=
    ⟨⟨pair.1, by
      rw [mem_AuthoredExactBottomCentralizingEndpointSubgroup]
      exact ⟨geometryFiberMorphism_packageBase_identity pair.1.1.1.hom,
        geometryFiberMorphism_packageBase_identity pair.1.1.2.hom⟩⟩,
      pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Reassociation of the bottom-qualified Karoubi image group with the
accepted actual image comparison group. -/
noncomputable def authoredExactBottomKaroubiComparisonEquiv
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g ≃*
      AuthoredExactKaroubiComparisonSubgroup A z omega k g where
  toFun pair := ⟨pair.1.1, pair.2⟩
  invFun pair :=
    ⟨⟨pair.1, by
      rw [mem_AuthoredExactBottomKaroubiEndpointPairSubgroup]
      exact ⟨geometryFiberMorphism_packageBase_identity pair.1.1.hom.f,
        geometryFiberMorphism_packageBase_identity pair.1.2.hom.f⟩⟩,
      pair.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-! ## Bottom preservation and restricted selector homomorphism -/

/-- The ambient sandwich restriction preserves the actual endpoint bottom
identity. -/
theorem authoredExactEndpointRestriction_preserves_bottom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g) :
    (authoredExactEndpointRestrictionHom A z omega k g pair.1).1 ∈
        AuthoredExactKaroubiSourceBottomEndpointSubgroup A z omega k g ∧
    (authoredExactEndpointRestrictionHom A z omega k g pair.1).2 ∈
        AuthoredExactKaroubiTargetBottomEndpointSubgroup A z omega k g := by
  constructor
  · rw [mem_geometryFiberKaroubiBottomEndpointSubgroup]
    exact geometryFiberMorphism_packageBase_identity _
  · rw [mem_geometryFiberKaroubiBottomEndpointSubgroup]
    exact geometryFiberMorphism_packageBase_identity _

/-- The ambient selector restriction, typed between the two actual bottom
endpoint groups. -/
noncomputable def authoredExactBottomEndpointRestrictionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g →*
      AuthoredExactBottomKaroubiEndpointPairSubgroup A z omega k g where
  toFun pair := ⟨authoredExactEndpointRestrictionHom A z omega k g pair.1,
    authoredExactEndpointRestriction_preserves_bottom A z omega k g pair⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (authoredExactEndpointRestrictionHom A z omega k g)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (authoredExactEndpointRestrictionHom A z omega k g)
      first.1 second.1

/-- Evaluation of the typed bottom ambient restriction is the accepted
ambient sandwich pair. -/
@[simp]
theorem authoredExactBottomEndpointRestrictionHom_val
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingEndpointSubgroup A z omega k g) :
    (authoredExactBottomEndpointRestrictionHom A z omega k g pair).1 =
      authoredExactEndpointRestrictionHom A z omega k g pair.1 :=
  rfl

/-- The typed bottom ambient preimage is precisely the group of bottom
centralizing pairs preserving the same ambient `barBeta`. -/
theorem authoredExactBottomEndpointRestriction_preimage_eq_barBeta
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    (AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g).comap
        (authoredExactBottomEndpointRestrictionHom A z omega k g) =
      AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
        A z omega k g := by
  ext pair
  change
    authoredExactBottomEndpointRestrictionHom A z omega k g pair ∈
        AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g ↔
      pair ∈ AuthoredExactBottomCentralizingBarBetaComparisonSubgroup
        A z omega k g
  rw [mem_AuthoredExactBottomKaroubiComparisonSubgroup,
    mem_AuthoredExactBottomCentralizingBarBetaComparisonSubgroup]
  exact authoredExactEndpointRestriction_mem_image_iff_mem_barBeta
    A z omega k g pair.1

/-- The actual restricted comparison homomorphism maps bottom-qualified raw
pairs to bottom-qualified Karoubi image pairs. -/
theorem authoredExactCompatibleRestriction_preserves_bottom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingRawComparisonSubgroup
      A z omega k g) :
    authoredExactBottomEndpointRestrictionHom A z omega k g pair.1 ∈
      AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g := by
  change authoredExactEndpointRestrictionHom A z omega k g pair.1.1 ∈
    AuthoredExactKaroubiComparisonSubgroup A z omega k g
  exact authoredExactEndpointRestriction_preserves_comparison
    A z omega k g ⟨pair.1.1, pair.2⟩

/-- G-122(D)'s selector restriction inside the actual bottom-qualified
hierarchy. -/
noncomputable def authoredExactBottomCompatibleRestrictionHom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k) :
    AuthoredExactBottomCentralizingRawComparisonSubgroup A z omega k g →*
      AuthoredExactBottomKaroubiComparisonSubgroup A z omega k g where
  toFun pair := ⟨authoredExactBottomEndpointRestrictionHom
      A z omega k g pair.1,
    authoredExactCompatibleRestriction_preserves_bottom A z omega k g pair⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (authoredExactBottomEndpointRestrictionHom A z omega k g)
  map_mul' first second := by
    apply Subtype.ext
    exact map_mul (authoredExactBottomEndpointRestrictionHom A z omega k g)
      first.1 second.1

/-- Evaluation of the bottom-qualified selector restriction retains the
accepted actual restricted comparison value. -/
@[simp]
theorem authoredExactBottomCompatibleRestrictionHom_val
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingRawComparisonSubgroup
      A z omega k g) :
    (authoredExactBottomCompatibleRestrictionHom A z omega k g pair).1 =
      authoredExactBottomEndpointRestrictionHom A z omega k g pair.1 :=
  rfl

/-- The bottom-qualified restriction is the accepted selector restriction
after the three explicit reassociations. -/
theorem authoredExactBottomCompatibleRestriction_reassociates
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (A : AuthoredBCDatumSquare U) (z : A.context.Category)
    (omega : DefectCochain A.toTransportData)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt (A.context.supportPackage z.as) k)
    (pair : AuthoredExactBottomCentralizingRawComparisonSubgroup
      A z omega k g) :
    authoredExactBottomKaroubiComparisonEquiv A z omega k g
        (authoredExactBottomCompatibleRestrictionHom A z omega k g pair) =
      authoredExactCompatibleRestrictionHom A z omega k g
        (authoredExactBottomRawComparisonEquiv A z omega k g pair) :=
  rfl

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
