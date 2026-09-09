import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationNaturalityFailure

/-!
# Automorphism groups carried by canonical normalization

This file completes G-119(D).  The full normalization functor sends every pair
of endpoint automorphisms to a pair in the normalized category.  Functoriality
carries the raw comparison-preservation equation to the normalized one, giving
a homomorphism between the two comparison-preserving subgroups.

The final restriction imposes the target's bottom qualification separately on
the raw and normalized sides: `πV` sends both raw endpoint automorphisms to
identities, while `π_N` does so after normalization.  The D3 equality
`π_N N = πV` proves that the subgroup homomorphism preserves this qualification.

## Implementation notes

Comparison preservation and bottom triviality are represented by standard
`Subgroup`, `Subgroup.comap`, and kernel constructions.  They are not stored in
new automorphism structures.  No reflection or surjectivity of the resulting
homomorphisms is asserted; those questions remain assigned to S2 and S4.
-/

open CategoryTheory

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation

universe v₁ v₂ u₁ u₂ u

/-- Any functor induces a group homomorphism on the automorphism group of an
object.  The construction uses the functor's standard action on isomorphisms. -/
noncomputable def functorAutomorphismHom
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (X : C) :
    Aut X →* Aut (F.obj X) where
  toFun a := F.mapIso a
  map_one' := by
    apply Iso.ext
    exact F.map_id X
  map_mul' _ _ := by
    apply Iso.ext
    exact F.map_comp _ _

/-- G-119(D)'s homomorphism `r_N` on the full product of endpoint
automorphism groups. -/
noncomputable def normalizationEndpointAutomorphismHom
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) :
    (Aut P × Aut Q) →*
      (Aut ((packageNormalizationFunctor U).obj P) ×
        Aut ((packageNormalizationFunctor U).obj Q)) :=
  MonoidHom.prodMap
    (functorAutomorphismHom (packageNormalizationFunctor U) P)
    (functorAutomorphismHom (packageNormalizationFunctor U) Q)

/-- Normalization rule: the source endpoint of `r_N(p,b)` has hom
`N(p.hom)`. -/
@[simp]
theorem normalizationEndpointAutomorphismHom_fst_hom
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) (pair : Aut P × Aut Q) :
    (normalizationEndpointAutomorphismHom P Q pair).1.hom =
      (packageNormalizationFunctor U).map pair.1.hom :=
  rfl

/-- Normalization rule: the target endpoint of `r_N(p,b)` has hom
`N(b.hom)`. -/
@[simp]
theorem normalizationEndpointAutomorphismHom_snd_hom
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) (pair : Aut P × Aut Q) :
    (normalizationEndpointAutomorphismHom P Q pair).2.hom =
      (packageNormalizationFunctor U).map pair.2.hom :=
  rfl

/-- Raw endpoint automorphism pairs preserving `c`, expressed by the fixed
equation `p ≫ c = c ≫ b`. -/
def rawNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup (Aut P × Aut Q) where
  carrier pair := pair.1.hom ≫ c = c ≫ pair.2.hom
  one_mem' := by rfl
  mul_mem' := by
    rintro ⟨p₁, b₁⟩ ⟨p₂, b₂⟩ first second
    change (p₂.hom ≫ p₁.hom) ≫ c = c ≫ (b₂.hom ≫ b₁.hom)
    rw [Category.assoc, first, ← Category.assoc, second, Category.assoc]
  inv_mem' := by
    rintro ⟨p, b⟩ relation
    change p.inv ≫ c = c ≫ b.inv
    calc
      p.inv ≫ c = p.inv ≫ ((c ≫ b.hom) ≫ b.inv) := by simp
      _ = p.inv ≫ ((p.hom ≫ c) ≫ b.inv) := by rw [relation]
      _ = c ≫ b.inv := by simp

/-- Membership in the raw comparison subgroup is exactly the original
comparison-preservation equation. -/
theorem mem_rawNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} {c : P ⟶ Q}
    {pair : Aut P × Aut Q} :
    pair ∈ rawNormalizationComparisonSubgroup c ↔
      pair.1.hom ≫ c = c ≫ pair.2.hom :=
  Iff.rfl

/-- Normalized endpoint automorphism pairs preserving `N(c)`. -/
def normalizedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup
      (Aut ((packageNormalizationFunctor U).obj P) ×
        Aut ((packageNormalizationFunctor U).obj Q)) where
  carrier pair :=
    pair.1.hom ≫ (packageNormalizationFunctor U).map c =
      (packageNormalizationFunctor U).map c ≫ pair.2.hom
  one_mem' := by
    change (𝟙 _ : _ ⟶ _) ≫ (packageNormalizationFunctor U).map c =
      (packageNormalizationFunctor U).map c ≫ (𝟙 _ : _ ⟶ _)
    rw [Category.id_comp, Category.comp_id]
  mul_mem' := by
    rintro ⟨p₁, b₁⟩ ⟨p₂, b₂⟩ first second
    change (p₂.hom ≫ p₁.hom) ≫ _ = _ ≫ (b₂.hom ≫ b₁.hom)
    rw [Category.assoc, first, ← Category.assoc, second, Category.assoc]
  inv_mem' := by
    rintro ⟨p, b⟩ relation
    have relation' :
        p.hom ≫ (packageNormalizationFunctor U).map c =
          (packageNormalizationFunctor U).map c ≫ b.hom := relation
    change p.inv ≫ (packageNormalizationFunctor U).map c =
      (packageNormalizationFunctor U).map c ≫ b.inv
    calc
      p.inv ≫ (packageNormalizationFunctor U).map c =
          p.inv ≫ (((packageNormalizationFunctor U).map c ≫ b.hom) ≫ b.inv) := by
            simp
      _ = p.inv ≫ ((p.hom ≫ (packageNormalizationFunctor U).map c) ≫ b.inv) := by
        rw [relation']
      _ = (packageNormalizationFunctor U).map c ≫ b.inv := by simp

/-- Membership in the normalized comparison subgroup is exactly preservation
of `N(c)` by the two normalized endpoint automorphisms. -/
theorem mem_normalizedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} {c : P ⟶ Q}
    {pair : Aut ((packageNormalizationFunctor U).obj P) ×
      Aut ((packageNormalizationFunctor U).obj Q)} :
    pair ∈ normalizedComparisonSubgroup c ↔
      pair.1.hom ≫ (packageNormalizationFunctor U).map c =
        (packageNormalizationFunctor U).map c ≫ pair.2.hom :=
  Iff.rfl

/-- Functoriality of `N` sends every raw comparison-preserving pair to a pair
preserving `N(c)`. -/
theorem normalizationEndpointAutomorphism_preserves_comparison
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : Aut P × Aut Q)
    (h : pair ∈ rawNormalizationComparisonSubgroup c) :
    normalizationEndpointAutomorphismHom P Q pair ∈
      normalizedComparisonSubgroup c := by
  have mapped := congrArg
    (fun k => (packageNormalizationFunctor U).map k) h
  simpa only [normalizationEndpointAutomorphismHom,
    functorAutomorphismHom, Functor.map_comp] using mapped

/-- The restriction of `r_N` from the raw comparison-preserving subgroup to
the normalized comparison-preserving subgroup. -/
noncomputable def normalizationComparisonSubgroupHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawNormalizationComparisonSubgroup c →*
      normalizedComparisonSubgroup c where
  toFun pair :=
    ⟨normalizationEndpointAutomorphismHom P Q pair.1,
      normalizationEndpointAutomorphism_preserves_comparison
        c pair.1 pair.2⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (normalizationEndpointAutomorphismHom P Q)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (normalizationEndpointAutomorphismHom P Q) a.1 b.1

/-- Evaluation rule: the comparison-subgroup restriction has the same
underlying endpoint pair as the full normalization homomorphism. -/
@[simp]
theorem normalizationComparisonSubgroupHom_val
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : rawNormalizationComparisonSubgroup c) :
    (normalizationComparisonSubgroupHom c pair).1 =
      normalizationEndpointAutomorphismHom P Q pair.1 :=
  rfl

/-- The source projection from the raw comparison-preserving subgroup. -/
noncomputable def rawNormalizationComparisonSourceHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawNormalizationComparisonSubgroup c →* Aut P :=
  (MonoidHom.fst (Aut P) (Aut Q)).comp
    (rawNormalizationComparisonSubgroup c).subtype

/-- The target projection from the raw comparison-preserving subgroup. -/
noncomputable def rawNormalizationComparisonTargetHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawNormalizationComparisonSubgroup c →* Aut Q :=
  (MonoidHom.snd (Aut P) (Aut Q)).comp
    (rawNormalizationComparisonSubgroup c).subtype

/-- The source projection from the normalized comparison-preserving subgroup. -/
noncomputable def normalizedComparisonSourceHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    normalizedComparisonSubgroup c →*
      Aut ((packageNormalizationFunctor U).obj P) :=
  (MonoidHom.fst _ _).comp (normalizedComparisonSubgroup c).subtype

/-- The target projection from the normalized comparison-preserving subgroup. -/
noncomputable def normalizedComparisonTargetHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    normalizedComparisonSubgroup c →*
      Aut ((packageNormalizationFunctor U).obj Q) :=
  (MonoidHom.snd _ _).comp (normalizedComparisonSubgroup c).subtype

/-- Raw endpoint automorphisms are observed at the bottom through `πV`. -/
noncomputable def rawNormalizationBottomAutomorphismHom
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    Aut P →*
      Aut ((canonicalNormalizationCoreInclusion U ⋙
        packageProjection U).obj P) :=
  functorAutomorphismHom
    (canonicalNormalizationCoreInclusion U ⋙ packageProjection U) P

/-- Evaluation rule: raw bottom observation maps the underlying automorphism
through `πV`. -/
@[simp]
theorem rawNormalizationBottomAutomorphismHom_hom
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U)
    (a : Aut P) :
    (rawNormalizationBottomAutomorphismHom P a).hom =
      (canonicalNormalizationCoreInclusion U ⋙ packageProjection U).map a.hom :=
  rfl

/-- Normalized endpoint automorphisms are observed at the bottom through
`π_N`. -/
noncomputable def normalizedBottomAutomorphismHom
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U) :
    Aut ((packageNormalizationFunctor U).obj P) →*
      Aut ((normalizedPackageProjection U).obj
        ((packageNormalizationFunctor U).obj P)) :=
  functorAutomorphismHom
    (normalizedPackageProjection U) ((packageNormalizationFunctor U).obj P)

/-- Evaluation rule: normalized bottom observation maps the underlying
automorphism through `π_N`. -/
@[simp]
theorem normalizedBottomAutomorphismHom_hom
    {U : AtomCarrier.{u}} (P : CanonicalNormalizationAdmissiblePackage U)
    (a : Aut ((packageNormalizationFunctor U).obj P)) :
    (normalizedBottomAutomorphismHom P a).hom =
      (normalizedPackageProjection U).map a.hom :=
  rfl

/-- Raw comparison-preserving pairs whose two endpoint automorphisms become
identities under `πV`. -/
noncomputable def rawBaseQualifiedNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup (rawNormalizationComparisonSubgroup c) :=
  Subgroup.comap (rawNormalizationComparisonSourceHom c)
      (rawNormalizationBottomAutomorphismHom P).ker ⊓
    Subgroup.comap (rawNormalizationComparisonTargetHom c)
      (rawNormalizationBottomAutomorphismHom Q).ker

/-- Membership in the raw qualified subgroup is exactly the two endpoint
identity conditions under `πV`; comparison preservation is carried by the
ambient subgroup. -/
theorem mem_rawBaseQualifiedNormalizationComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} {c : P ⟶ Q}
    {pair : rawNormalizationComparisonSubgroup c} :
    pair ∈ rawBaseQualifiedNormalizationComparisonSubgroup c ↔
      rawNormalizationBottomAutomorphismHom P pair.1.1 = 1 ∧
        rawNormalizationBottomAutomorphismHom Q pair.1.2 = 1 :=
  Iff.rfl

/-- Normalized comparison-preserving pairs whose endpoint automorphisms become
identities under `π_N`. -/
noncomputable def normalizedBaseQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup (normalizedComparisonSubgroup c) :=
  Subgroup.comap (normalizedComparisonSourceHom c)
      (normalizedBottomAutomorphismHom P).ker ⊓
    Subgroup.comap (normalizedComparisonTargetHom c)
      (normalizedBottomAutomorphismHom Q).ker

/-- Membership in the normalized qualified subgroup is exactly the two
endpoint identity conditions under `π_N`; preservation of `N(c)` is carried
by the ambient subgroup. -/
theorem mem_normalizedBaseQualifiedComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} {c : P ⟶ Q}
    {pair : normalizedComparisonSubgroup c} :
    pair ∈ normalizedBaseQualifiedComparisonSubgroup c ↔
      normalizedBottomAutomorphismHom P pair.1.1 = 1 ∧
        normalizedBottomAutomorphismHom Q pair.1.2 = 1 :=
  Iff.rfl

/-- The identity `π_N N=πV` carries bottom-trivial raw endpoint
automorphisms to bottom-trivial normalized endpoint automorphisms. -/
theorem normalizationEndpointAutomorphism_preserves_bottom
    {U : AtomCarrier.{u}}
    (P : CanonicalNormalizationAdmissiblePackage U) (a : Aut P)
    (h : rawNormalizationBottomAutomorphismHom P a = 1) :
    normalizedBottomAutomorphismHom P
        (functorAutomorphismHom (packageNormalizationFunctor U) P a) = 1 := by
  apply Iso.ext
  change (normalizedPackageProjection U).map
      ((packageNormalizationFunctor U).map a.hom) = 𝟙 _
  have comparison :
      (normalizedPackageProjection U).map
          ((packageNormalizationFunctor U).map a.hom) =
        (canonicalNormalizationCoreInclusion U ⋙
          packageProjection U).map a.hom := by
    simpa using normalizedPackageProjection_normalization_map a.hom
  have bottomIdentity := congrArg Iso.hom h
  change (canonicalNormalizationCoreInclusion U ⋙
    packageProjection U).map a.hom = 𝟙 _ at bottomIdentity
  exact comparison.trans bottomIdentity

/-- G-119(D)'s final restriction: normalization sends every raw
base-qualified comparison-preserving pair to a normalized base-qualified pair.
No reflection or lift-surjectivity statement is included. -/
noncomputable def normalizationBaseQualifiedComparisonSubgroupHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawBaseQualifiedNormalizationComparisonSubgroup c →*
      normalizedBaseQualifiedComparisonSubgroup c where
  toFun pair := by
    refine ⟨normalizationComparisonSubgroupHom c pair.1, ?_⟩
    constructor
    · exact normalizationEndpointAutomorphism_preserves_bottom
        P pair.1.1.1 pair.2.1
    · exact normalizationEndpointAutomorphism_preserves_bottom
        Q pair.1.1.2 pair.2.2
  map_one' := by
    apply Subtype.ext
    exact map_one (normalizationComparisonSubgroupHom c)
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (normalizationComparisonSubgroupHom c) a.1 b.1

/-- Evaluation rule: the base-qualified restriction retains the underlying
comparison-subgroup value of the first restriction of `r_N`. -/
@[simp]
theorem normalizationBaseQualifiedComparisonSubgroupHom_val
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : rawBaseQualifiedNormalizationComparisonSubgroup c) :
    (normalizationBaseQualifiedComparisonSubgroupHom c pair).1 =
      normalizationComparisonSubgroupHom c pair.1 :=
  rfl

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
