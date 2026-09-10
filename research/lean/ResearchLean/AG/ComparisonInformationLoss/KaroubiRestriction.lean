import ResearchLean.AG.ComparisonInformationLoss.GroupHomRestriction
import ResearchLean.AG.RealizationComparisonIdempotents.KaroubiArrowEquivalence

/-!
# Comparison automorphisms restricted to idempotent images

This file constructs the categorical map required by G-120(C).  Endpoint
automorphisms centralizing fixed idempotents are sandwiched by those
idempotents, producing genuine automorphisms of the corresponding Karoubi
objects.  Their product preserves the normalized comparison, and the general
restriction, reflection, lift-fiber, and short-exact API is then applied.

Implementation notes: the source subgroup is a `Subgroup.comap` inside the
product of the two centralizers.  This keeps `Gamma_0` literally a subgroup of
`H`, while a separate theorem identifies its ambient image with
`H ⊓ Gamma_c`.  The Karoubi automorphisms use the requested sandwich maps;
replacing their inverse maps by an existence proof would lose the explicit
`e b⁻¹ e` and `d p⁻¹ d` formulas.
-/

open CategoryTheory
open CategoryTheory.Idempotents

namespace AAT.AG.ComparisonInformationLoss

universe v u

variable {E : Type u} [Category.{v} E]

/-- The Karoubi object determined by an idempotent endomorphism. -/
def idempotentKaroubiObject (X : E) (e : X ⟶ X) (he : e ≫ e = e) : Karoubi E where
  X := X
  p := e
  idem := he

/-- Endpoint automorphisms that centralize a specified endomorphism. -/
def idempotentCentralizerAutSubgroup (X : E) (e : X ⟶ X) : Subgroup (Aut X) where
  carrier b := b.hom ≫ e = e ≫ b.hom
  one_mem' := by
    change (𝟙 X) ≫ e = e ≫ 𝟙 X
    simp
  mul_mem' := by
    intro b p hb hp
    change (p.hom ≫ b.hom) ≫ e = e ≫ (p.hom ≫ b.hom)
    rw [Category.assoc, hb, ← Category.assoc, hp, Category.assoc]
  inv_mem' := by
    intro b hb
    change b.inv ≫ e = e ≫ b.inv
    calc
      b.inv ≫ e = b.inv ≫ ((e ≫ b.hom) ≫ b.inv) := by simp
      _ = b.inv ≫ ((b.hom ≫ e) ≫ b.inv) := by rw [hb]
      _ = e ≫ b.inv := by simp

/-- Membership API for the endpoint centralizer. -/
theorem mem_idempotentCentralizerAutSubgroup
    (X : E) (e : X ⟶ X) (b : Aut X) :
    b ∈ idempotentCentralizerAutSubgroup X e ↔ b.hom ≫ e = e ≫ b.hom :=
  Iff.rfl

/-- The inverse of a centralizing automorphism also centralizes the chosen
endomorphism. -/
theorem idempotentCentralizerAutSubgroup_inv_comm
    (X : E) (e : X ⟶ X) (b : idempotentCentralizerAutSubgroup X e) :
    b.1.inv ≫ e = e ≫ b.1.inv :=
  (idempotentCentralizerAutSubgroup X e).inv_mem b.property

/-- A centralizing automorphism's requested hom sandwich reduces to its
restriction followed by the idempotent. -/
theorem idempotentCentralizerAutSubgroup_hom_sandwich
    (X : E) (e : X ⟶ X) (he : e ≫ e = e)
    (b : idempotentCentralizerAutSubgroup X e) :
    e ≫ b.1.hom ≫ e = b.1.hom ≫ e := by
  calc
    e ≫ b.1.hom ≫ e = e ≫ (e ≫ b.1.hom) := by rw [b.property]
    _ = (e ≫ e) ≫ b.1.hom := (Category.assoc _ _ _).symm
    _ = e ≫ b.1.hom := by rw [he]
    _ = b.1.hom ≫ e := b.property.symm

/-- A centralizing automorphism's requested inverse sandwich reduces to its
inverse followed by the idempotent. -/
theorem idempotentCentralizerAutSubgroup_inv_sandwich
    (X : E) (e : X ⟶ X) (he : e ≫ e = e)
    (b : idempotentCentralizerAutSubgroup X e) :
    e ≫ b.1.inv ≫ e = b.1.inv ≫ e := by
  calc
    e ≫ b.1.inv ≫ e = e ≫ (e ≫ b.1.inv) := by
      rw [idempotentCentralizerAutSubgroup_inv_comm X e b]
    _ = (e ≫ e) ≫ b.1.inv := (Category.assoc _ _ _).symm
    _ = e ≫ b.1.inv := by rw [he]
    _ = b.1.inv ≫ e := (idempotentCentralizerAutSubgroup_inv_comm X e b).symm

/-- Sandwiched endpoint automorphism on the Karoubi image.  The inverse is the
requested sandwich by the raw inverse automorphism. -/
def idempotentRestrictionAut (X : E) (e : X ⟶ X) (he : e ≫ e = e)
    (b : idempotentCentralizerAutSubgroup X e) :
    Aut (idempotentKaroubiObject X e he) where
  hom :=
    { f := b.1.hom ≫ e
      comm := by
        dsimp [idempotentKaroubiObject]
        simpa only [Category.assoc, he] using
          idempotentCentralizerAutSubgroup_hom_sandwich X e he b }
  inv :=
    { f := b.1.inv ≫ e
      comm := by
        dsimp [idempotentKaroubiObject]
        simpa only [Category.assoc, he] using
          idempotentCentralizerAutSubgroup_inv_sandwich X e he b }
  hom_inv_id := by
    apply Karoubi.Hom.ext
    dsimp [idempotentKaroubiObject]
    calc
      (b.1.hom ≫ e) ≫ (b.1.inv ≫ e) =
          b.1.hom ≫ (e ≫ b.1.inv) ≫ e := by simp only [Category.assoc]
      _ = b.1.hom ≫ (b.1.inv ≫ e) ≫ e := by
        rw [(idempotentCentralizerAutSubgroup_inv_comm X e b).symm]
      _ = e := by simp [he]
  inv_hom_id := by
    apply Karoubi.Hom.ext
    dsimp [idempotentKaroubiObject]
    calc
      (b.1.inv ≫ e) ≫ (b.1.hom ≫ e) =
          b.1.inv ≫ (e ≫ b.1.hom) ≫ e := by simp only [Category.assoc]
      _ = b.1.inv ≫ (b.1.hom ≫ e) ≫ e := by rw [b.property.symm]
      _ = e := by simp [he]

/-- The sandwich construction is a group homomorphism from the centralizer to
the automorphism group of the Karoubi image. -/
def idempotentRestrictionHom (X : E) (e : X ⟶ X) (he : e ≫ e = e) :
    idempotentCentralizerAutSubgroup X e →*
      Aut (idempotentKaroubiObject X e he) where
  toFun := idempotentRestrictionAut X e he
  map_one' := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    change (𝟙 X) ≫ e = e
    simp
  map_mul' b p := by
    apply Iso.ext
    apply Karoubi.Hom.ext
    change (p.1.hom ≫ b.1.hom) ≫ e =
      (p.1.hom ≫ e) ≫ (b.1.hom ≫ e)
    calc
      (p.1.hom ≫ b.1.hom) ≫ e = p.1.hom ≫ (b.1.hom ≫ e) :=
        Category.assoc _ _ _
      _ = p.1.hom ≫ (e ≫ b.1.hom) := by rw [b.property]
      _ = (p.1.hom ≫ e) ≫ b.1.hom := (Category.assoc _ _ _).symm
      _ = (p.1.hom ≫ e) ≫ (b.1.hom ≫ e) := by
        symm
        calc
          (p.1.hom ≫ e) ≫ (b.1.hom ≫ e) =
              p.1.hom ≫ (e ≫ b.1.hom) ≫ e := by
            simp only [Category.assoc]
          _ = p.1.hom ≫ (b.1.hom ≫ e) ≫ e := by rw [b.property.symm]
          _ = p.1.hom ≫ b.1.hom ≫ e := by simp only [Category.assoc, he]
          _ = p.1.hom ≫ (e ≫ b.1.hom) := by rw [b.property]
          _ = (p.1.hom ≫ e) ≫ b.1.hom := (Category.assoc _ _ _).symm

/-- Evaluation of the sandwiched automorphism hom component. -/
@[simp]
theorem idempotentRestrictionHom_hom_f
    (X : E) (e : X ⟶ X) (he : e ≫ e = e)
    (b : idempotentCentralizerAutSubgroup X e) :
    (idempotentRestrictionHom X e he b).hom.f = e ≫ b.1.hom ≫ e :=
  (idempotentCentralizerAutSubgroup_hom_sandwich X e he b).symm

/-- Evaluation of the sandwiched automorphism inverse component. -/
@[simp]
theorem idempotentRestrictionHom_inv_f
    (X : E) (e : X ⟶ X) (he : e ≫ e = e)
    (b : idempotentCentralizerAutSubgroup X e) :
    (idempotentRestrictionHom X e he b).inv.f = e ≫ b.1.inv ≫ e :=
  (idempotentCentralizerAutSubgroup_inv_sandwich X e he b).symm

/-! ## Endpoint products and comparison preservation -/

/-- Comparison-preserving endpoint automorphism pairs for an arbitrary
categorical comparison. -/
def comparisonAutomorphismSubgroup {X Y : E} (c : X ⟶ Y) :
    Subgroup (Aut X × Aut Y) where
  carrier pair := pair.1.hom ≫ c = c ≫ pair.2.hom
  one_mem' := by
    change (𝟙 X) ≫ c = c ≫ 𝟙 Y
    simp
  mul_mem' := by
    rintro ⟨b₁, p₁⟩ ⟨b₂, p₂⟩ h₁ h₂
    change (b₂.hom ≫ b₁.hom) ≫ c = c ≫ (p₂.hom ≫ p₁.hom)
    rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]
  inv_mem' := by
    rintro ⟨b, p⟩ h
    change b.inv ≫ c = c ≫ p.inv
    calc
      b.inv ≫ c = b.inv ≫ ((c ≫ p.hom) ≫ p.inv) := by simp
      _ = b.inv ≫ ((b.hom ≫ c) ≫ p.inv) := by rw [h]
      _ = c ≫ p.inv := by simp

/-- Membership is the endpoint comparison square itself. -/
theorem mem_comparisonAutomorphismSubgroup {X Y : E} (c : X ⟶ Y)
    (pair : Aut X × Aut Y) :
    pair ∈ comparisonAutomorphismSubgroup c ↔
      pair.1.hom ≫ c = c ≫ pair.2.hom :=
  Iff.rfl

/-- The fixed raw comparison and compatible endpoint idempotents as the
idempotent arrow-square input of G-119's Karoubi-arrow equivalence. -/
def idempotentComparisonKaroubiArrow {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    Karoubi (Arrow E) where
  X := { left := X, right := Y, hom := c }
  p := Arrow.homMk e d hedc
  idem := by
    apply Arrow.hom_ext
    · exact he
    · exact hd

/-- The Karoubi comparison `a = e c d`.  Its morphism proof deliberately uses
the fixed compatibility equation `e c = c d`, preserving the target's route
from the raw idempotent square. -/
def idempotentImageComparison {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    idempotentKaroubiObject X e he ⟶ idempotentKaroubiObject Y d hd where
  f := e ≫ c ≫ d
  comm := by
    dsimp [idempotentKaroubiObject]
    have hleft : e ≫ c ≫ d = c ≫ d := by
      calc
        e ≫ c ≫ d = (e ≫ c) ≫ d := (Category.assoc _ _ _).symm
        _ = (c ≫ d) ≫ d := by rw [hedc]
        _ = c ≫ (d ≫ d) := Category.assoc _ _ _
        _ = c ≫ d := by rw [hd]
    calc
      e ≫ (e ≫ c ≫ d) ≫ d = e ≫ c ≫ d := by
        simp only [← Category.assoc, he]
        rw [Category.assoc, hd]
      _ = c ≫ d := hleft
      _ = e ≫ c ≫ d := hleft.symm

/-- Evaluation of the normalized comparison is the requested sandwich. -/
@[simp]
theorem idempotentImageComparison_f {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    (idempotentImageComparison c e d he hd hedc).f = e ≫ c ≫ d :=
  rfl

/-- The comparison constructed here agrees on its full underlying morphism
with the comparison produced by G-119's Karoubi-arrow equivalence from the
actual idempotent square. -/
theorem idempotentImageComparison_agrees_karoubiArrowEquivalence
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    (AAT.AG.RealizationComparisonIdempotents.karoubiArrowToArrowKaroubiObj
      (idempotentComparisonKaroubiArrow c e d he hd hedc)).hom.f =
        (idempotentImageComparison c e d he hd hedc).f :=
  rfl

/-- G-120(C)'s centralizing endpoint product `H`. -/
def centralizingEndpointSubgroup (X Y : E) (e : X ⟶ X) (d : Y ⟶ Y) :
    Subgroup (Aut X × Aut Y) :=
  (idempotentCentralizerAutSubgroup X e).prod
    (idempotentCentralizerAutSubgroup Y d)

/-- `Gamma_0` as a subgroup of `H`, obtained by restricting raw comparison
compatibility to the two endpoint centralizers. -/
def centralizingCompatibleSubgroup {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y) :
    Subgroup (centralizingEndpointSubgroup X Y e d) :=
  Subgroup.comap (centralizingEndpointSubgroup X Y e d).subtype
    (comparisonAutomorphismSubgroup c)

/-- The ambient image of `Gamma_0` is exactly `H ⊓ Gamma_c`. -/
theorem centralizingCompatibleSubgroup_map_eq_inf {X Y : E} (c : X ⟶ Y)
    (e : X ⟶ X) (d : Y ⟶ Y) :
    Subgroup.map (centralizingEndpointSubgroup X Y e d).subtype
        (centralizingCompatibleSubgroup c e d) =
      centralizingEndpointSubgroup X Y e d ⊓ comparisonAutomorphismSubgroup c := by
  rw [centralizingCompatibleSubgroup, Subgroup.map_comap_eq,
    Subgroup.range_subtype, inf_comm]

/-- Projection of `H` to the source endpoint centralizer. -/
def centralizingEndpointSourceHom (X Y : E) (e : X ⟶ X) (d : Y ⟶ Y) :
    centralizingEndpointSubgroup X Y e d →*
      idempotentCentralizerAutSubgroup X e where
  toFun pair := ⟨pair.1.1, pair.property.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of `H` to the target endpoint centralizer. -/
def centralizingEndpointTargetHom (X Y : E) (e : X ⟶ X) (d : Y ⟶ Y) :
    centralizingEndpointSubgroup X Y e d →*
      idempotentCentralizerAutSubgroup Y d where
  toFun pair := ⟨pair.1.2, pair.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The endpoint sandwich homomorphism `r : H → Aut(X,e) × Aut(Y,d)`. -/
def idempotentEndpointRestrictionHom (X Y : E)
    (e : X ⟶ X) (d : Y ⟶ Y) (he : e ≫ e = e) (hd : d ≫ d = d) :
    centralizingEndpointSubgroup X Y e d →*
      (Aut (idempotentKaroubiObject X e he) ×
        Aut (idempotentKaroubiObject Y d hd)) :=
  MonoidHom.prod
    ((idempotentRestrictionHom X e he).comp
      (centralizingEndpointSourceHom X Y e d))
    ((idempotentRestrictionHom Y d hd).comp
      (centralizingEndpointTargetHom X Y e d))

/-- The source component of `r` is the requested `e b e`. -/
@[simp]
theorem idempotentEndpointRestrictionHom_fst_hom_f (X Y : E)
    (e : X ⟶ X) (d : Y ⟶ Y) (he : e ≫ e = e) (hd : d ≫ d = d)
    (pair : centralizingEndpointSubgroup X Y e d) :
    (idempotentEndpointRestrictionHom X Y e d he hd pair).1.hom.f =
      e ≫ pair.1.1.hom ≫ e :=
  idempotentRestrictionHom_hom_f X e he ⟨pair.1.1, pair.property.1⟩

/-- The target component of `r` is the requested `d p d`. -/
@[simp]
theorem idempotentEndpointRestrictionHom_snd_hom_f (X Y : E)
    (e : X ⟶ X) (d : Y ⟶ Y) (he : e ≫ e = e) (hd : d ≫ d = d)
    (pair : centralizingEndpointSubgroup X Y e d) :
    (idempotentEndpointRestrictionHom X Y e d he hd pair).2.hom.f =
      d ≫ pair.1.2.hom ≫ d :=
  idempotentRestrictionHom_hom_f Y d hd ⟨pair.1.2, pair.property.2⟩

/-! ## Preservation and the specialized C API -/

/-- The endpoint sandwich homomorphism preserves comparison compatibility. -/
theorem idempotentEndpointRestriction_preserves_comparison
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (pair : centralizingCompatibleSubgroup c e d) :
    idempotentEndpointRestrictionHom X Y e d he hd pair.1 ∈
      comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc) := by
  change
    (idempotentEndpointRestrictionHom X Y e d he hd pair.1).1.hom ≫
        idempotentImageComparison c e d he hd hedc =
      idempotentImageComparison c e d he hd hedc ≫
        (idempotentEndpointRestrictionHom X Y e d he hd pair.1).2.hom
  apply Karoubi.Hom.ext
  change
    (idempotentEndpointRestrictionHom X Y e d he hd pair.1).1.hom.f ≫
        (idempotentImageComparison c e d he hd hedc).f =
      (idempotentImageComparison c e d he hd hedc).f ≫
        (idempotentEndpointRestrictionHom X Y e d he hd pair.1).2.hom.f
  rw [idempotentEndpointRestrictionHom_fst_hom_f,
    idempotentEndpointRestrictionHom_snd_hom_f, idempotentImageComparison_f]
  have hraw : pair.1.1.1.hom ≫ c = c ≫ pair.1.1.2.hom := pair.property
  have hb : pair.1.1.1.hom ≫ e = e ≫ pair.1.1.1.hom := pair.1.property.1
  have hp : pair.1.1.2.hom ≫ d = d ≫ pair.1.1.2.hom := pair.1.property.2
  rw [idempotentCentralizerAutSubgroup_hom_sandwich X e he
      ⟨pair.1.1.1, pair.1.property.1⟩,
    idempotentCentralizerAutSubgroup_hom_sandwich Y d hd
      ⟨pair.1.1.2, pair.1.property.2⟩]
  slice_lhs 2 3 => rw [he]
  slice_lhs 1 2 => rw [hb]
  slice_lhs 2 3 => rw [hraw]
  slice_rhs 3 4 => rw [← hp]
  slice_rhs 4 5 => rw [hd]
  simp only [Category.assoc]

/-- Preservation as the subgroup-image inclusion required to form the
restricted homomorphism `rBar : Gamma_0 → Gamma_a`. -/
theorem idempotentEndpointRestriction_map_le
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    Subgroup.map (idempotentEndpointRestrictionHom X Y e d he hd)
        (centralizingCompatibleSubgroup c e d) ≤
      comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc) := by
  rintro image ⟨pair, hpair, rfl⟩
  exact idempotentEndpointRestriction_preserves_comparison c e d he hd hedc
    ⟨pair, hpair⟩

/-- G-120(C.1)'s restricted homomorphism `rBar : Gamma_0 → Gamma_a`. -/
def idempotentCompatibleRestrictionHom
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    centralizingCompatibleSubgroup c e d →*
      comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc) :=
  restrictedSubgroupHom (idempotentEndpointRestrictionHom X Y e d he hd)
    (centralizingCompatibleSubgroup c e d)
    (comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
    (idempotentEndpointRestriction_map_le c e d he hd hedc)

/-- Evaluation of `rBar` retains the actual endpoint sandwich pair. -/
@[simp]
theorem idempotentCompatibleRestrictionHom_coe
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (pair : centralizingCompatibleSubgroup c e d) :
    ((idempotentCompatibleRestrictionHom c e d he hd hedc pair :
        comparisonAutomorphismSubgroup
          (idempotentImageComparison c e d he hd hedc)) :
      Aut (idempotentKaroubiObject X e he) ×
        Aut (idempotentKaroubiObject Y d hd)) =
      idempotentEndpointRestrictionHom X Y e d he hd pair.1 :=
  rfl

/-- G-120(C.2): reflection is equivalent to kernel containment together with
the exact intersection of `Gamma_a` with the ambient image of `r`. -/
theorem idempotentEndpointRestriction_reflection_iff
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d) :
    (comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)).comap
        (idempotentEndpointRestrictionHom X Y e d he hd) =
          centralizingCompatibleSubgroup c e d ↔
      (idempotentEndpointRestrictionHom X Y e d he hd).ker ≤
          centralizingCompatibleSubgroup c e d ∧
        Subgroup.map (idempotentEndpointRestrictionHom X Y e d he hd)
            (centralizingCompatibleSubgroup c e d) =
          comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc) ⊓
            (idempotentEndpointRestrictionHom X Y e d he hd).range :=
  comap_eq_iff_ker_le_and_map_eq_inf_range
    (idempotentEndpointRestrictionHom X Y e d he hd)
    (centralizingCompatibleSubgroup c e d)
    (comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))

/-- The C.3 lift fiber of a compatible idempotent-image change. -/
abbrev IdempotentCompatibleLiftFiber
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)) :=
  RestrictedFiber (idempotentEndpointRestrictionHom X Y e d he hd)
    (centralizingCompatibleSubgroup c e d)
    (comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
    (idempotentEndpointRestriction_map_le c e d he hd hedc) t

/-- The specialized fiber inherits the generic opposite-kernel right action. -/
instance idempotentCompatibleLiftFiberSMul
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)) :
    SMul (idempotentCompatibleRestrictionHom c e d he hd hedc).kerᵐᵒᵖ
      (IdempotentCompatibleLiftFiber c e d he hd hedc t) := by
  unfold idempotentCompatibleRestrictionHom IdempotentCompatibleLiftFiber
  infer_instance

/-- The specialized right action satisfies the group action laws. -/
instance idempotentCompatibleLiftFiberMulAction
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)) :
    MulAction (idempotentCompatibleRestrictionHom c e d he hd hedc).kerᵐᵒᵖ
      (IdempotentCompatibleLiftFiber c e d he hd hedc t) := by
  unfold idempotentCompatibleRestrictionHom IdempotentCompatibleLiftFiber
  infer_instance

/-- G-120(C.3)'s lift criterion: a compatible image change has a compatible
raw lift exactly when it lies in `r(Gamma_0)`. -/
theorem nonempty_idempotentCompatibleLiftFiber_iff_mem_map
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)) :
    Nonempty (IdempotentCompatibleLiftFiber c e d he hd hedc t) ↔
      (t : Aut (idempotentKaroubiObject X e he) ×
        Aut (idempotentKaroubiObject Y d hd)) ∈
        Subgroup.map (idempotentEndpointRestrictionHom X Y e d he hd)
          (centralizingCompatibleSubgroup c e d) :=
  nonempty_restrictedFiber_iff_mem_map _ _ _ _ t

/-- The restricted kernel acts freely by right multiplication on every
nonempty C.3 lift fiber. -/
theorem idempotentCompatibleLiftFiber_action_free
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
    (x : IdempotentCompatibleLiftFiber c e d he hd hedc t) :
    Function.Injective (fun k : (idempotentCompatibleRestrictionHom
      c e d he hd hedc).kerᵐᵒᵖ => k • x) :=
  restrictedFiber_action_free _ _ _ _ t x

/-- The restricted kernel action is transitive on a nonempty C.3 lift fiber. -/
theorem idempotentCompatibleLiftFiber_action_transitive
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
    (x y : IdempotentCompatibleLiftFiber c e d he hd hedc t) :
    ∃ k : (idempotentCompatibleRestrictionHom c e d he hd hedc).kerᵐᵒᵖ,
      k • x = y :=
  restrictedFiber_action_transitive _ _ _ _ t x y

/-- Every two points of a C.3 lift fiber have a unique right-kernel
displacement. -/
theorem idempotentCompatibleLiftFiber_existsUnique_smul_eq
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (t : comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
    (x y : IdempotentCompatibleLiftFiber c e d he hd hedc t) :
    ∃! k : (idempotentCompatibleRestrictionHom c e d he hd hedc).kerᵐᵒᵖ,
      k • x = y :=
  restrictedFiber_existsUnique_smul_eq _ _ _ _ t x y

/-- G-120(C.3)'s short-exact conclusion under the stated surjectivity
condition `r(Gamma_0) = Gamma_a`. -/
theorem idempotentCompatibleRestriction_shortExact
    {X Y : E} (c : X ⟶ Y) (e : X ⟶ X) (d : Y ⟶ Y)
    (he : e ≫ e = e) (hd : d ≫ d = d) (hedc : e ≫ c = c ≫ d)
    (hsurj : Subgroup.map (idempotentEndpointRestrictionHom X Y e d he hd)
        (centralizingCompatibleSubgroup c e d) =
      comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc)) :
    IsGroupShortExact
      (restrictedKernelInclusion (idempotentEndpointRestrictionHom X Y e d he hd)
        (centralizingCompatibleSubgroup c e d)
        (comparisonAutomorphismSubgroup (idempotentImageComparison c e d he hd hedc))
        (idempotentEndpointRestriction_map_le c e d he hd hedc))
      (idempotentCompatibleRestrictionHom c e d he hd hedc) :=
  (restrictedSubgroupHom_shortExact_iff_map_eq _ _ _ _).mpr hsurj

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss

end AAT.AG.ComparisonInformationLoss
