import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationComparisonGroup

/-!
# Comparison information under canonical normalization

This file specializes the general restriction, reflection, lift-fiber, and
short-exact API of G-120(A,C) to G-119's canonical normalization functor.  It
first treats all endpoint automorphisms.  It then constructs the two endpoint
base-fixing groups required by G-120(D), restricts normalization between them,
and repeats the comparison analysis inside those groups.

Implementation notes: base qualification is represented by subgroups of the
full raw and normalized endpoint products before comparison compatibility is
imposed.  Thus `Gamma_base` and `Delta_base` are literally nested subgroups of
`Q_base` and `R_base`.  Explicit group equivalences identify these subgroups
with G-119's accepted comparison-first nesting, and a commuting theorem—not a
new certificate field—identifies the two restricted homomorphisms.
-/

open CategoryTheory

namespace AAT.AG.ComparisonInformationLoss

open AtomFoundation
open AAT.AG.RealizationComparisonIdempotents

universe u

/-! ## Full endpoint automorphism groups -/

/-- Functorial normalization maps the raw comparison subgroup into the
normalized comparison subgroup. -/
theorem normalizationEndpointAutomorphism_map_le
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.map (normalizationEndpointAutomorphismHom P Q)
        (rawNormalizationComparisonSubgroup c) ≤
      normalizedComparisonSubgroup c := by
  rintro pair ⟨rawPair, hraw, rfl⟩
  exact normalizationEndpointAutomorphism_preserves_comparison c rawPair hraw

/-- The generic restriction of `r_N` to comparison-preserving pairs. -/
noncomputable def normalizationCompatibleRestrictionHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawNormalizationComparisonSubgroup c →*
      normalizedComparisonSubgroup c :=
  restrictedSubgroupHom (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)
    (normalizationEndpointAutomorphism_map_le c)

/-- The G-120 restriction is the accepted G-119 comparison-subgroup
homomorphism. -/
theorem normalizationCompatibleRestrictionHom_eq_existing
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    normalizationCompatibleRestrictionHom c = normalizationComparisonSubgroupHom c := by
  apply MonoidHom.ext
  intro pair
  apply Subtype.ext
  rfl

/-- G-120(D)'s exact reflection criterion for canonical normalization on all
endpoint automorphisms. -/
theorem normalizationComparison_reflection_iff
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.comap (normalizationEndpointAutomorphismHom P Q)
        (normalizedComparisonSubgroup c) = rawNormalizationComparisonSubgroup c ↔
      (normalizationEndpointAutomorphismHom P Q).ker ≤
          rawNormalizationComparisonSubgroup c ∧
        Subgroup.map (normalizationEndpointAutomorphismHom P Q)
            (rawNormalizationComparisonSubgroup c) =
          normalizedComparisonSubgroup c ⊓
            (normalizationEndpointAutomorphismHom P Q).range :=
  comap_eq_iff_ker_le_and_map_eq_inf_range
    (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)

/-- The fiber of compatible raw endpoint changes over a fixed normalized
compatible change. -/
abbrev NormalizationCompatibleLiftFiber
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c) :=
  RestrictedFiber (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)
    (normalizationEndpointAutomorphism_map_le c) t

/-- The full normalization lift fiber inherits the generic opposite-kernel
right action. -/
noncomputable instance normalizationCompatibleLiftFiberSMul
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c) :
    SMul (normalizationCompatibleRestrictionHom c).kerᵐᵒᵖ
      (NormalizationCompatibleLiftFiber c t) := by
  exact restrictedFiberSMul (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)
    (normalizationEndpointAutomorphism_map_le c) t

/-- The full normalization right action satisfies the group action laws. -/
noncomputable instance normalizationCompatibleLiftFiberMulAction
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c) :
    MulAction (normalizationCompatibleRestrictionHom c).kerᵐᵒᵖ
      (NormalizationCompatibleLiftFiber c t) := by
  exact restrictedFiberMulAction (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)
    (normalizationEndpointAutomorphism_map_le c) t

/-- A compatible normalized change has a compatible raw lift exactly when it
lies in the image of the raw comparison subgroup. -/
theorem nonempty_normalizationCompatibleLiftFiber_iff_mem_map
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c) :
    Nonempty (NormalizationCompatibleLiftFiber c t) ↔
      (t : Aut ((packageNormalizationFunctor U).obj P) ×
        Aut ((packageNormalizationFunctor U).obj Q)) ∈
        Subgroup.map (normalizationEndpointAutomorphismHom P Q)
          (rawNormalizationComparisonSubgroup c) :=
  nonempty_restrictedFiber_iff_mem_map _ _ _ _ t

/-- The restricted kernel acts freely by right multiplication on each
canonical-normalization lift fiber. -/
theorem normalizationCompatibleLiftFiber_action_free
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c)
    (x : NormalizationCompatibleLiftFiber c t) :
    Function.Injective (fun k : (normalizationCompatibleRestrictionHom c).kerᵐᵒᵖ =>
      k • x) :=
  restrictedFiber_action_free _ _ _ _ t x

/-- The restricted kernel action is transitive on every nonempty
canonical-normalization lift fiber. -/
theorem normalizationCompatibleLiftFiber_action_transitive
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c)
    (x y : NormalizationCompatibleLiftFiber c t) :
    ∃ k : (normalizationCompatibleRestrictionHom c).kerᵐᵒᵖ, k • x = y :=
  restrictedFiber_action_transitive _ _ _ _ t x y

/-- Every two compatible raw lifts have a unique right-kernel displacement. -/
theorem normalizationCompatibleLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedComparisonSubgroup c)
    (x y : NormalizationCompatibleLiftFiber c t) :
    ∃! k : (normalizationCompatibleRestrictionHom c).kerᵐᵒᵖ, k • x = y :=
  restrictedFiber_existsUnique_smul_eq _ _ _ _ t x y

/-- Surjectivity onto all normalized compatible changes gives the canonical
normalization short exact sequence. -/
theorem normalizationCompatibleRestriction_shortExact
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (hsurj : Subgroup.map (normalizationEndpointAutomorphismHom P Q)
        (rawNormalizationComparisonSubgroup c) = normalizedComparisonSubgroup c) :
    IsGroupShortExact
      (restrictedKernelInclusion (normalizationEndpointAutomorphismHom P Q)
        (rawNormalizationComparisonSubgroup c) (normalizedComparisonSubgroup c)
        (normalizationEndpointAutomorphism_map_le c))
      (normalizationCompatibleRestrictionHom c) :=
  (restrictedSubgroupHom_shortExact_iff_map_eq _ _ _ _).mpr hsurj

/-! ## Endpoint base-fixing groups and their comparison subgroups -/

/-- `Q_base`: raw endpoint automorphism pairs whose two components become the
identity under the raw bottom projection. -/
noncomputable def rawNormalizationBaseEndpointSubgroup
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) :
    Subgroup (Aut P × Aut Q) :=
  Subgroup.comap (MonoidHom.fst (Aut P) (Aut Q))
      (rawNormalizationBottomAutomorphismHom P).ker ⊓
    Subgroup.comap (MonoidHom.snd (Aut P) (Aut Q))
      (rawNormalizationBottomAutomorphismHom Q).ker

/-- Membership in `Q_base` is exactly the two raw bottom-identity equations. -/
theorem mem_rawNormalizationBaseEndpointSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} {pair : Aut P × Aut Q} :
    pair ∈ rawNormalizationBaseEndpointSubgroup P Q ↔
      rawNormalizationBottomAutomorphismHom P pair.1 = 1 ∧
        rawNormalizationBottomAutomorphismHom Q pair.2 = 1 :=
  Iff.rfl

/-- `R_base`: normalized endpoint automorphism pairs whose two components
become the identity under the normalized bottom projection. -/
noncomputable def normalizedBaseEndpointSubgroup
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) :
    Subgroup (Aut ((packageNormalizationFunctor U).obj P) ×
      Aut ((packageNormalizationFunctor U).obj Q)) :=
  Subgroup.comap (MonoidHom.fst _ _)
      (normalizedBottomAutomorphismHom P).ker ⊓
    Subgroup.comap (MonoidHom.snd _ _)
      (normalizedBottomAutomorphismHom Q).ker

/-- Membership in `R_base` is exactly the two normalized bottom-identity
equations. -/
theorem mem_normalizedBaseEndpointSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U}
    {pair : Aut ((packageNormalizationFunctor U).obj P) ×
      Aut ((packageNormalizationFunctor U).obj Q)} :
    pair ∈ normalizedBaseEndpointSubgroup P Q ↔
      normalizedBottomAutomorphismHom P pair.1 = 1 ∧
        normalizedBottomAutomorphismHom Q pair.2 = 1 :=
  Iff.rfl

/-- Canonical normalization sends all of `Q_base` into `R_base`. -/
theorem normalizationEndpointAutomorphism_base_map_le
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) :
    Subgroup.map (normalizationEndpointAutomorphismHom P Q)
        (rawNormalizationBaseEndpointSubgroup P Q) ≤
      normalizedBaseEndpointSubgroup P Q := by
  rintro pair ⟨rawPair, hbase, rfl⟩
  exact ⟨normalizationEndpointAutomorphism_preserves_bottom P rawPair.1 hbase.1,
    normalizationEndpointAutomorphism_preserves_bottom Q rawPair.2 hbase.2⟩

/-- `r_base : Q_base → R_base`, obtained by restricting the full endpoint
normalization homomorphism. -/
noncomputable def normalizationBaseEndpointHom
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U) :
    rawNormalizationBaseEndpointSubgroup P Q →*
      normalizedBaseEndpointSubgroup P Q :=
  restrictedSubgroupHom (normalizationEndpointAutomorphismHom P Q)
    (rawNormalizationBaseEndpointSubgroup P Q)
    (normalizedBaseEndpointSubgroup P Q)
    (normalizationEndpointAutomorphism_base_map_le P Q)

/-- Evaluation of `r_base` retains the full normalized endpoint pair. -/
@[simp]
theorem normalizationBaseEndpointHom_coe
    {U : AtomCarrier.{u}}
    (P Q : CanonicalNormalizationAdmissiblePackage U)
    (pair : rawNormalizationBaseEndpointSubgroup P Q) :
    ((normalizationBaseEndpointHom P Q pair : normalizedBaseEndpointSubgroup P Q) :
        Aut ((packageNormalizationFunctor U).obj P) ×
          Aut ((packageNormalizationFunctor U).obj Q)) =
      normalizationEndpointAutomorphismHom P Q pair.1 :=
  rfl

/-- `Gamma_base`, comparison-compatible raw pairs inside `Q_base`. -/
noncomputable def rawBaseComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup (rawNormalizationBaseEndpointSubgroup P Q) :=
  Subgroup.comap (rawNormalizationBaseEndpointSubgroup P Q).subtype
    (rawNormalizationComparisonSubgroup c)

/-- The ambient image of `Gamma_base` is `Q_base ∩ Gamma_c`. -/
theorem rawBaseComparisonSubgroup_map_eq_inf
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.map (rawNormalizationBaseEndpointSubgroup P Q).subtype
        (rawBaseComparisonSubgroup c) =
      rawNormalizationBaseEndpointSubgroup P Q ⊓
        rawNormalizationComparisonSubgroup c := by
  rw [rawBaseComparisonSubgroup, Subgroup.map_comap_eq,
    Subgroup.range_subtype, inf_comm]

/-- `Delta_base`, comparison-compatible normalized pairs inside `R_base`. -/
noncomputable def normalizedBaseComparisonSubgroup
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup (normalizedBaseEndpointSubgroup P Q) :=
  Subgroup.comap (normalizedBaseEndpointSubgroup P Q).subtype
    (normalizedComparisonSubgroup c)

/-- The ambient image of `Delta_base` is `R_base ∩ Gamma_(N(c))`. -/
theorem normalizedBaseComparisonSubgroup_map_eq_inf
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.map (normalizedBaseEndpointSubgroup P Q).subtype
        (normalizedBaseComparisonSubgroup c) =
      normalizedBaseEndpointSubgroup P Q ⊓ normalizedComparisonSubgroup c := by
  rw [normalizedBaseComparisonSubgroup, Subgroup.map_comap_eq,
    Subgroup.range_subtype, inf_comm]

/-- The base restriction preserves comparison compatibility. -/
theorem normalizationBaseEndpointHom_map_le
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.map (normalizationBaseEndpointHom P Q)
        (rawBaseComparisonSubgroup c) ≤ normalizedBaseComparisonSubgroup c := by
  rintro pair ⟨rawPair, hcomparison, rfl⟩
  exact normalizationEndpointAutomorphism_preserves_comparison
    c rawPair.1 hcomparison

/-- `rBar_base : Gamma_base → Delta_base`. -/
noncomputable abbrev normalizationBaseCompatibleRestrictionHom
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawBaseComparisonSubgroup c →* normalizedBaseComparisonSubgroup c :=
  restrictedSubgroupHom (normalizationBaseEndpointHom P Q)
    (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)
    (normalizationBaseEndpointHom_map_le c)

/-! ## Agreement with G-119's comparison-first nesting -/

/-- Reassociation of the two raw subgroup restrictions, preserving the
underlying endpoint pair. -/
noncomputable def rawBaseComparisonEquivExisting
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    rawBaseComparisonSubgroup c ≃*
      rawBaseQualifiedNormalizationComparisonSubgroup c where
  toFun pair := ⟨⟨pair.1.1, pair.property⟩, pair.1.property⟩
  invFun pair := ⟨⟨pair.1.1, pair.property⟩, pair.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The raw reassociation preserves the complete underlying endpoint pair. -/
@[simp]
theorem rawBaseComparisonEquivExisting_coe
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : rawBaseComparisonSubgroup c) :
    ((rawBaseComparisonEquivExisting c pair :
      rawBaseQualifiedNormalizationComparisonSubgroup c) :
        rawNormalizationComparisonSubgroup c).1 = pair.1.1 :=
  rfl

/-- Reassociation of the two normalized subgroup restrictions, preserving the
underlying endpoint pair. -/
noncomputable def normalizedBaseComparisonEquivExisting
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    normalizedBaseComparisonSubgroup c ≃*
      normalizedBaseQualifiedComparisonSubgroup c where
  toFun pair := ⟨⟨pair.1.1, pair.property⟩, pair.1.property⟩
  invFun pair := ⟨⟨pair.1.1, pair.property⟩, pair.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The normalized reassociation preserves the complete underlying endpoint
pair. -/
@[simp]
theorem normalizedBaseComparisonEquivExisting_coe
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : normalizedBaseComparisonSubgroup c) :
    ((normalizedBaseComparisonEquivExisting c pair :
      normalizedBaseQualifiedComparisonSubgroup c) :
        normalizedComparisonSubgroup c).1 = pair.1.1 :=
  rfl

/-- Under the underlying-pair-preserving reassociations, `rBar_base` is the
accepted G-119 base-qualified comparison homomorphism. -/
theorem normalizationBaseCompatibleRestriction_agrees_existing
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (pair : rawBaseComparisonSubgroup c) :
    normalizedBaseComparisonEquivExisting c
        (normalizationBaseCompatibleRestrictionHom c pair) =
      normalizationBaseQualifiedComparisonSubgroupHom c
        (rawBaseComparisonEquivExisting c pair) := by
  rfl

/-- Homomorphism-level form of the agreement with G-119 under the two
underlying-pair-preserving reassociations. -/
theorem normalizationBaseCompatibleRestriction_hom_agrees_existing
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    (normalizedBaseComparisonEquivExisting c).toMonoidHom.comp
        (normalizationBaseCompatibleRestrictionHom c) =
      (normalizationBaseQualifiedComparisonSubgroupHom c).comp
        (rawBaseComparisonEquivExisting c).toMonoidHom := by
  apply MonoidHom.ext
  intro pair
  exact normalizationBaseCompatibleRestriction_agrees_existing c pair

/-! ## Base-qualified reflection, lift fibers, and exactness -/

/-- G-120(D)'s base-qualified reflection criterion. -/
theorem normalizationBaseComparison_reflection_iff
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q) :
    Subgroup.comap (normalizationBaseEndpointHom P Q)
        (normalizedBaseComparisonSubgroup c) = rawBaseComparisonSubgroup c ↔
      (normalizationBaseEndpointHom P Q).ker ≤ rawBaseComparisonSubgroup c ∧
        Subgroup.map (normalizationBaseEndpointHom P Q)
            (rawBaseComparisonSubgroup c) =
          normalizedBaseComparisonSubgroup c ⊓
            (normalizationBaseEndpointHom P Q).range :=
  comap_eq_iff_ker_le_and_map_eq_inf_range
    (normalizationBaseEndpointHom P Q)
    (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)

/-- The fiber of base-qualified raw compatible changes over a fixed
base-qualified normalized compatible change. -/
abbrev NormalizationBaseCompatibleLiftFiber
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c) :=
  RestrictedFiber (normalizationBaseEndpointHom P Q)
    (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)
    (normalizationBaseEndpointHom_map_le c) t

/-- The base-qualified lift fiber inherits the opposite-kernel right action. -/
noncomputable instance normalizationBaseCompatibleLiftFiberSMul
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c) :
    SMul (normalizationBaseCompatibleRestrictionHom c).kerᵐᵒᵖ
      (NormalizationBaseCompatibleLiftFiber c t) := by
  exact restrictedFiberSMul (normalizationBaseEndpointHom P Q)
    (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)
    (normalizationBaseEndpointHom_map_le c) t

set_option synthInstance.maxHeartbeats 100000 in
/-- The base-qualified right action satisfies the group action laws. -/
noncomputable instance normalizationBaseCompatibleLiftFiberMulAction
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c) :
    MulAction (normalizationBaseCompatibleRestrictionHom c).kerᵐᵒᵖ
      (NormalizationBaseCompatibleLiftFiber c t) := by
  exact restrictedFiberMulAction (normalizationBaseEndpointHom P Q)
    (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)
    (normalizationBaseEndpointHom_map_le c) t

/-- A base-qualified normalized compatible change has a base-qualified raw
compatible lift exactly when it lies in `r_base(Gamma_base)`. -/
theorem nonempty_normalizationBaseCompatibleLiftFiber_iff_mem_map
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c) :
    Nonempty (NormalizationBaseCompatibleLiftFiber c t) ↔
      (t : normalizedBaseEndpointSubgroup P Q) ∈
        Subgroup.map (normalizationBaseEndpointHom P Q)
          (rawBaseComparisonSubgroup c) :=
  nonempty_restrictedFiber_iff_mem_map _ _ _ _ t

/-- The base-qualified restricted kernel acts freely by right multiplication
on every nonempty lift fiber. -/
theorem normalizationBaseCompatibleLiftFiber_action_free
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c)
    (x : NormalizationBaseCompatibleLiftFiber c t) :
    Function.Injective (fun k :
      (normalizationBaseCompatibleRestrictionHom c).kerᵐᵒᵖ => k • x) :=
  restrictedFiber_action_free _ _ _ _ t x

/-- The base-qualified restricted kernel action is transitive. -/
theorem normalizationBaseCompatibleLiftFiber_action_transitive
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c)
    (x y : NormalizationBaseCompatibleLiftFiber c t) :
    ∃ k : (normalizationBaseCompatibleRestrictionHom c).kerᵐᵒᵖ, k • x = y :=
  restrictedFiber_action_transitive _ _ _ _ t x y

/-- Every two base-qualified lifts have a unique right-kernel displacement. -/
theorem normalizationBaseCompatibleLiftFiber_existsUnique_smul_eq
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (t : normalizedBaseComparisonSubgroup c)
    (x y : NormalizationBaseCompatibleLiftFiber c t) :
    ∃! k : (normalizationBaseCompatibleRestrictionHom c).kerᵐᵒᵖ, k • x = y :=
  restrictedFiber_existsUnique_smul_eq _ _ _ _ t x y

/-- Surjectivity onto `Delta_base` gives the base-qualified short exact
sequence. -/
theorem normalizationBaseCompatibleRestriction_shortExact
    {U : AtomCarrier.{u}}
    {P Q : CanonicalNormalizationAdmissiblePackage U} (c : P ⟶ Q)
    (hsurj : Subgroup.map (normalizationBaseEndpointHom P Q)
        (rawBaseComparisonSubgroup c) = normalizedBaseComparisonSubgroup c) :
    IsGroupShortExact
      (restrictedKernelInclusion (normalizationBaseEndpointHom P Q)
        (rawBaseComparisonSubgroup c) (normalizedBaseComparisonSubgroup c)
        (normalizationBaseEndpointHom_map_le c))
      (normalizationBaseCompatibleRestrictionHom c) :=
  (restrictedSubgroupHom_shortExact_iff_map_eq _ _ _ _).mpr hsurj

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss

end AAT.AG.ComparisonInformationLoss
