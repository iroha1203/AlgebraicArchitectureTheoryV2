import ResearchLean.AG.RealizationComparisonIdempotents.MaximalSubgroupoid
import Mathlib.Algebra.Group.Graph
import Formal.Util.AssertStandardAxioms

/-!
# Comparison groups for arbitrary categories and endpoint subgroups

The endpoint groups are the actual subgroups of categorical automorphisms.
The comparison equation is imposed on their product, and the arrow-category
isomorphisms are constructed from the same endpoint maps.  In particular,
no geometry-specific base condition enters the general results.

Implementation notes: `Subgroup` records the chosen endpoint changes and
their comparison equation.  The arrow and Karoubi statements use mathlib's
`Arrow` and `Karoubi` rather than a parallel square structure.  Fibers are
represented by the actual sets of endpoint lifts.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.ComparisonInformation

universe u v

variable {E : Type u} [Category.{v} E] {X Y : E}

/-- Definition 7.2 for any category and any chosen endpoint subgroups. -/
def generalComparisonSubgroup (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) :
    Subgroup (GX × GY) where
  carrier pair := pair.1.1.hom ≫ c = c ≫ pair.2.1.hom
  one_mem' := by
    change (𝟙 X) ≫ c = c ≫ (𝟙 Y)
    simp
  mul_mem' := by
    rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h₁ h₂
    change (a₂.1.hom ≫ a₁.1.hom) ≫ c = c ≫ (b₂.1.hom ≫ b₁.1.hom)
    rw [Category.assoc, h₁, ← Category.assoc, h₂, Category.assoc]
  inv_mem' := by
    rintro ⟨a, b⟩ h
    change a.1.inv ≫ c = c ≫ b.1.inv
    calc
      a.1.inv ≫ c = a.1.inv ≫ ((c ≫ b.1.hom) ≫ b.1.inv) := by simp
      _ = a.1.inv ≫ ((a.1.hom ≫ c) ≫ b.1.inv) := by rw [h]
      _ = c ≫ b.1.inv := by simp

@[simp] theorem mem_generalComparisonSubgroup (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (pair : GX × GY) :
    pair ∈ generalComparisonSubgroup c GX GY ↔
      pair.1.1.hom ≫ c = c ≫ pair.2.1.hom := Iff.rfl

/-- The two actual endpoint projections of Definition 7.2. -/
def generalComparisonSourceProjection (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) :
    generalComparisonSubgroup c GX GY →* GX :=
  (MonoidHom.fst GX GY).comp (generalComparisonSubgroup c GX GY).subtype

/-- The target endpoint projection of Definition 7.2; its inputs are the chosen endpoint subgroups. -/
def generalComparisonTargetProjection (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) :
    generalComparisonSubgroup c GX GY →* GY :=
  (MonoidHom.snd GX GY).comp (generalComparisonSubgroup c GX GY).subtype

/-- Proposition 7.3's unrestricted arrow-square identification. -/
noncomputable def generalComparisonArrowMulEquiv (c : X ⟶ Y) :
    generalComparisonSubgroup c ⊤ ⊤ ≃* Aut (Arrow.mk c) where
  toFun pair := Arrow.isoMk pair.1.1.1 pair.1.2.1 pair.2
  invFun square :=
    ⟨(⟨Comma.leftIso square, Subgroup.mem_top _⟩,
      ⟨Comma.rightIso square, Subgroup.mem_top _⟩),
      square.hom.w⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> apply Iso.ext <;> rfl
  right_inv square := by
    apply Iso.ext
    apply Arrow.hom_ext <;> rfl
  map_mul' a b := by
    apply Iso.ext
    apply Arrow.hom_ext <;> rfl

@[simp] theorem generalComparisonArrowMulEquiv_source (c : X ⟶ Y)
    (pair : generalComparisonSubgroup c ⊤ ⊤) :
    Comma.leftIso (generalComparisonArrowMulEquiv c pair) = pair.1.1.1 := rfl

@[simp] theorem generalComparisonArrowMulEquiv_target (c : X ⟶ Y)
    (pair : generalComparisonSubgroup c ⊤ ⊤) :
    Comma.rightIso (generalComparisonArrowMulEquiv c pair) = pair.1.2.1 := rfl

/-- Proposition 7.3 for the identity-idempotent inclusion into
`M(E) = Arrow (Karoubi E)`, for every category `E`. -/
noncomputable def generalComparisonKaroubiArrowMulEquiv (c : X ⟶ Y) :
    generalComparisonSubgroup c ⊤ ⊤ ≃*
      Aut (Arrow.mk ((toKaroubi E).map c)) where
  toFun pair := Arrow.isoMk
    ((toKaroubi E).mapIso pair.1.1.1)
    ((toKaroubi E).mapIso pair.1.2.1)
    (by apply Karoubi.hom_ext; exact pair.2)
  invFun square :=
    ⟨(⟨{
        hom := square.hom.left.f
        inv := square.inv.left.f
        hom_inv_id := by
          have h := congrArg Karoubi.Hom.f (Comma.leftIso square).hom_inv_id
          simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h
        inv_hom_id := by
          have h := congrArg Karoubi.Hom.f (Comma.leftIso square).inv_hom_id
          simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h },
        Subgroup.mem_top _⟩,
      ⟨{
        hom := square.hom.right.f
        inv := square.inv.right.f
        hom_inv_id := by
          have h := congrArg Karoubi.Hom.f (Comma.rightIso square).hom_inv_id
          simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h
        inv_hom_id := by
          have h := congrArg Karoubi.Hom.f (Comma.rightIso square).inv_hom_id
          simpa only [Karoubi.comp_f, Karoubi.id_f, Karoubi.coe_p] using h },
        Subgroup.mem_top _⟩),
      congrArg Karoubi.Hom.f square.hom.w⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;> apply Iso.ext <;> rfl
  right_inv square := by
    apply Iso.ext
    apply Arrow.hom_ext
    · apply Karoubi.hom_ext; rfl
    · apply Karoubi.hom_ext; rfl
  map_mul' a b := by
    apply Iso.ext
    apply Arrow.hom_ext
    · apply Karoubi.hom_ext; rfl
    · apply Karoubi.hom_ext; rfl

@[simp] theorem generalComparisonKaroubiArrowMulEquiv_source (c : X ⟶ Y)
    (pair : generalComparisonSubgroup c ⊤ ⊤) :
    (generalComparisonKaroubiArrowMulEquiv c pair).hom.left.f =
      pair.1.1.1.hom := rfl

@[simp] theorem generalComparisonKaroubiArrowMulEquiv_target (c : X ⟶ Y)
    (pair : generalComparisonSubgroup c ⊤ ⊤) :
    (generalComparisonKaroubiArrowMulEquiv c pair).hom.right.f =
      pair.1.2.1.hom := rfl

/-- Identity-idempotent inclusion preserves the entire automorphism group of
an arrow.  This explicitly connects the ordinary arrow category to `M(E)`. -/
noncomputable def arrowToKaroubiArrowAutMulEquiv (c : X ⟶ Y) :
    Aut (Arrow.mk c) ≃* Aut (Arrow.mk ((toKaroubi E).map c)) :=
  (generalComparisonArrowMulEquiv c).symm.trans
    (generalComparisonKaroubiArrowMulEquiv c)

@[simp] theorem arrowToKaroubiArrowAutMulEquiv_source (c : X ⟶ Y)
    (square : Aut (Arrow.mk c)) :
    (arrowToKaroubiArrowAutMulEquiv c square).hom.left.f =
      square.hom.left := by
  change (generalComparisonArrowMulEquiv c).symm square |>.1.1.1.hom = _
  rfl

@[simp] theorem arrowToKaroubiArrowAutMulEquiv_target (c : X ⟶ Y)
    (square : Aut (Arrow.mk c)) :
    (arrowToKaroubiArrowAutMulEquiv c square).hom.right.f =
      square.hom.right := by
  change (generalComparisonArrowMulEquiv c).symm square |>.1.2.1.hom = _
  rfl

/-- Postcomparison stabilizer inside the chosen target subgroup. -/
def generalTargetStabilizer (c : X ⟶ Y) (GY : Subgroup (Aut Y)) :
    Subgroup GY where
  carrier b := c ≫ b.1.hom = c
  one_mem' := by
    change c ≫ (𝟙 Y) = c
    simp
  mul_mem' := by
    intro a b ha hb
    change c ≫ (b.1.hom ≫ a.1.hom) = c
    rw [← Category.assoc, hb, ha]
  inv_mem' := by
    intro b hb
    change c ≫ b.1.inv = c
    calc
      c ≫ b.1.inv = (c ≫ b.1.hom) ≫ b.1.inv := by rw [hb]
      _ = c := by simp

/-- Precomparison stabilizer inside the chosen source subgroup. -/
def generalSourceStabilizer (c : X ⟶ Y) (GX : Subgroup (Aut X)) :
    Subgroup GX where
  carrier a := a.1.hom ≫ c = c
  one_mem' := by
    change (𝟙 X) ≫ c = c
    simp
  mul_mem' := by
    intro a b ha hb
    change (b.1.hom ≫ a.1.hom) ≫ c = c
    rw [Category.assoc, ha, hb]
  inv_mem' := by
    intro a ha
    change a.1.inv ≫ c = c
    calc
      a.1.inv ≫ c = a.1.inv ≫ (a.1.hom ≫ c) := by rw [ha]
      _ = c := by simp

/-- Theorem 7.4, first kernel identification, for arbitrary endpoint groups. -/
noncomputable def generalSourceKernelMulEquiv (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) :
    (generalComparisonSourceProjection c GX GY).ker ≃*
      generalTargetStabilizer c GY where
  toFun k := ⟨k.1.1.2, by
    have h : k.1.1.1 = 1 := k.2
    have relation : k.1.1.1.1.hom ≫ c = c ≫ k.1.1.2.1.hom := k.1.2
    rw [h] at relation
    change (𝟙 X) ≫ c = c ≫ k.1.1.2.1.hom at relation
    change c ≫ k.1.1.2.1.hom = c
    simpa only [Category.id_comp] using relation.symm⟩
  invFun b := ⟨⟨(1, b.1), by
    have relation : c ≫ b.1.1.hom = c := b.2
    change (𝟙 X) ≫ c = c ≫ b.1.1.hom
    simpa only [Category.id_comp] using relation.symm⟩, rfl⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact k.2.symm
    · rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Theorem 7.4, second kernel identification. -/
noncomputable def generalTargetKernelMulEquiv (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) :
    (generalComparisonTargetProjection c GX GY).ker ≃*
      generalSourceStabilizer c GX where
  toFun k := ⟨k.1.1.1, by
    have h : k.1.1.2 = 1 := k.2
    have relation : k.1.1.1.1.hom ≫ c = c ≫ k.1.1.2.1.hom := k.1.2
    rw [h] at relation
    change k.1.1.1.1.hom ≫ c = c ≫ (𝟙 Y) at relation
    change k.1.1.1.1.hom ≫ c = c
    simpa only [Category.comp_id] using relation⟩
  invFun a := ⟨⟨(a.1, 1), by
    have relation : a.1.1.hom ≫ c = c := a.2
    change a.1.1.hom ≫ c = c ≫ (𝟙 Y)
    simpa only [Category.comp_id] using relation⟩, rfl⟩
  left_inv k := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact k.2.symm
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- A target endpoint change follows a specified source change. -/
def TargetLift (c : X ⟶ Y) (GX : Subgroup (Aut X))
    (GY : Subgroup (Aut Y)) (a : GX) :=
  {b : GY // a.1.hom ≫ c = c ≫ b.1.hom}

/-- A source endpoint change follows a specified target change. -/
def SourceLift (c : X ⟶ Y) (GX : Subgroup (Aut X))
    (GY : Subgroup (Aut Y)) (b : GY) :=
  {a : GX // a.1.hom ≫ c = c ≫ b.1.hom}

/-- Theorem 7.4: a follower exists exactly on the source projection image. -/
theorem general_source_range_iff_lift (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX) :
    a ∈ (generalComparisonSourceProjection c GX GY).range ↔
      Nonempty (TargetLift c GX GY a) := by
  constructor
  · rintro ⟨pair, h⟩
    exact ⟨⟨pair.1.2, h ▸ pair.2⟩⟩
  · rintro ⟨lift⟩
    exact ⟨⟨(a, lift.1), lift.2⟩, rfl⟩

/-- The symmetric existence criterion for the target projection. -/
theorem general_target_range_iff_lift (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY) :
    b ∈ (generalComparisonTargetProjection c GX GY).range ↔
      Nonempty (SourceLift c GX GY b) := by
  constructor
  · rintro ⟨pair, h⟩
    exact ⟨⟨pair.1.1, h ▸ pair.2⟩⟩
  · rintro ⟨lift⟩
    exact ⟨⟨(lift.1, b), lift.2⟩, rfl⟩

/-- The target stabilizer acts on actual followers of a fixed source change. -/
noncomputable def targetLiftAction (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX)
    (t : generalTargetStabilizer c GY) (lift : TargetLift c GX GY a) :
    TargetLift c GX GY a :=
  ⟨t.1 * lift.1, by
    change a.1.hom ≫ c = c ≫ (lift.1.1.hom ≫ t.1.1.hom)
    symm
    calc
      c ≫ (lift.1.1.hom ≫ t.1.1.hom) =
          (c ≫ lift.1.1.hom) ≫ t.1.1.hom := by simp [Category.assoc]
      _ = (a.1.hom ≫ c) ≫ t.1.1.hom := by
        exact congrArg (fun f : X ⟶ Y => f ≫ t.1.1.hom) lift.2.symm
      _ = a.1.hom ≫ (c ≫ t.1.1.hom) := Category.assoc _ _ _
      _ = a.1.hom ≫ c := by rw [t.2]⟩

/-- The target stabilizer acts on the actual target followers in Theorem 7.4. -/
noncomputable instance targetLiftSMul (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX) :
    SMul (generalTargetStabilizer c GY) (TargetLift c GX GY a) where
  smul := targetLiftAction c GX GY a

/-- The group action laws for Theorem 7.4 follow from composition of target changes. -/
noncomputable instance targetLiftMulAction (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX) :
    MulAction (generalTargetStabilizer c GY) (TargetLift c GX GY a) where
  one_smul lift := by apply Subtype.ext; exact one_mul lift.1
  mul_smul t s lift := by apply Subtype.ext; exact mul_assoc t.1 s.1 lift.1

/-- Theorem 7.4: the target follower fiber is a torsor when inhabited. -/
theorem targetLift_existsUnique (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX)
    (source target : TargetLift c GX GY a) :
    ∃! t : generalTargetStabilizer c GY, t • source = target := by
  let difference : GY := target.1 * source.1⁻¹
  have hsource : (a, source.1) ∈ generalComparisonSubgroup c GX GY := source.2
  have hinv := (generalComparisonSubgroup c GX GY).inv_mem hsource
  have hsourceInv : a.1.inv ≫ c = c ≫ source.1.1.inv := hinv
  have hmem : difference ∈ generalTargetStabilizer c GY := by
    change c ≫ (source.1.1.inv ≫ target.1.1.hom) = c
    calc
      c ≫ (source.1.1.inv ≫ target.1.1.hom) =
          (c ≫ source.1.1.inv) ≫ target.1.1.hom := by simp
      _ = (a.1.inv ≫ c) ≫ target.1.1.hom := by rw [hsourceInv]
      _ = a.1.inv ≫ (a.1.hom ≫ c) := by
        calc
          (a.1.inv ≫ c) ≫ target.1.1.hom =
              a.1.inv ≫ (c ≫ target.1.1.hom) := Category.assoc _ _ _
          _ = a.1.inv ≫ (a.1.hom ≫ c) :=
            congrArg (fun f : X ⟶ Y => a.1.inv ≫ f) target.2.symm
      _ = c := by simp
  refine ⟨⟨difference, hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (target.1 * source.1⁻¹) * source.1 = target.1
    simp
  · intro other hother
    apply Subtype.ext
    have hval : other.1 * source.1 = target.1 := congrArg Subtype.val hother
    change other.1 = target.1 * source.1⁻¹
    calc
      other.1 = (other.1 * source.1) * source.1⁻¹ := by simp
      _ = target.1 * source.1⁻¹ := by rw [hval]

/-- Choosing one follower identifies the target fiber with its stabilizer. -/
noncomputable def targetLiftEquiv (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (a : GX)
    (origin : TargetLift c GX GY a) :
    generalTargetStabilizer c GY ≃ TargetLift c GX GY a :=
  Equiv.ofBijective (fun t => t • origin) ⟨
    by
      intro t s h
      have ht : t.1 * origin.1 = s.1 * origin.1 := congrArg Subtype.val h
      apply Subtype.ext
      exact mul_right_cancel ht,
    by
      intro target
      obtain ⟨t, ht, _⟩ := targetLift_existsUnique c GX GY a origin target
      exact ⟨t, ht⟩⟩

/-- The source stabilizer acts on actual source followers. -/
noncomputable def sourceLiftAction (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY)
    (s : generalSourceStabilizer c GX) (lift : SourceLift c GX GY b) :
    SourceLift c GX GY b :=
  ⟨s.1 * lift.1, by
    change (lift.1.1.hom ≫ s.1.1.hom) ≫ c = c ≫ b.1.hom
    calc
      (lift.1.1.hom ≫ s.1.1.hom) ≫ c =
          lift.1.1.hom ≫ (s.1.1.hom ≫ c) := Category.assoc _ _ _
      _ = lift.1.1.hom ≫ c := by rw [s.2]
      _ = c ≫ b.1.hom := lift.2⟩

/-- The source stabilizer acts on the actual source followers in Theorem 7.4. -/
noncomputable instance sourceLiftSMul (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY) :
    SMul (generalSourceStabilizer c GX) (SourceLift c GX GY b) where
  smul := sourceLiftAction c GX GY b

/-- The group action laws for Theorem 7.4 follow from composition of source changes. -/
noncomputable instance sourceLiftMulAction (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY) :
    MulAction (generalSourceStabilizer c GX) (SourceLift c GX GY b) where
  one_smul lift := by apply Subtype.ext; exact one_mul lift.1
  mul_smul s t lift := by apply Subtype.ext; exact mul_assoc s.1 t.1 lift.1

/-- Theorem 7.4: the source follower fiber is a torsor when inhabited. -/
theorem sourceLift_existsUnique (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY)
    (source target : SourceLift c GX GY b) :
    ∃! s : generalSourceStabilizer c GX, s • source = target := by
  let difference : GX := target.1 * source.1⁻¹
  have hsource : (source.1, b) ∈ generalComparisonSubgroup c GX GY := source.2
  have hinv := (generalComparisonSubgroup c GX GY).inv_mem hsource
  have hsourceInv : source.1.1.inv ≫ c = c ≫ b.1.inv := hinv
  have hmem : difference ∈ generalSourceStabilizer c GX := by
    change (source.1.1.inv ≫ target.1.1.hom) ≫ c = c
    calc
      (source.1.1.inv ≫ target.1.1.hom) ≫ c =
          source.1.1.inv ≫ (target.1.1.hom ≫ c) := Category.assoc _ _ _
      _ = source.1.1.inv ≫ (c ≫ b.1.hom) := by rw [target.2]
      _ = (source.1.1.inv ≫ c) ≫ b.1.hom := by simp [Category.assoc]
      _ = (c ≫ b.1.inv) ≫ b.1.hom := by rw [hsourceInv]
      _ = c := by simp
  refine ⟨⟨difference, hmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (target.1 * source.1⁻¹) * source.1 = target.1
    simp
  · intro other hother
    apply Subtype.ext
    have hval : other.1 * source.1 = target.1 := congrArg Subtype.val hother
    change other.1 = target.1 * source.1⁻¹
    calc
      other.1 = (other.1 * source.1) * source.1⁻¹ := by simp
      _ = target.1 * source.1⁻¹ := by rw [hval]

/-- Choosing one follower identifies the source fiber with its stabilizer. -/
noncomputable def sourceLiftEquiv (c : X ⟶ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y)) (b : GY)
    (origin : SourceLift c GX GY b) :
    generalSourceStabilizer c GX ≃ SourceLift c GX GY b :=
  Equiv.ofBijective (fun s => s • origin) ⟨
    by
      intro s t h
      have hs : s.1 * origin.1 = t.1 * origin.1 := congrArg Subtype.val h
      apply Subtype.ext
      exact mul_right_cancel hs,
    by
      intro target
      obtain ⟨s, hs, _⟩ := sourceLift_existsUnique c GX GY b origin target
      exact ⟨s, hs⟩⟩

/-- Conjugation by an isomorphic comparison on the full automorphism groups. -/
noncomputable def generalConjugation (c : X ≅ Y) : Aut X ≃* Aut Y where
  toFun a :=
    { hom := c.inv ≫ a.hom ≫ c.hom
      inv := c.inv ≫ a.inv ≫ c.hom
      hom_inv_id := by simp
      inv_hom_id := by simp }
  invFun b :=
    { hom := c.hom ≫ b.hom ≫ c.inv
      inv := c.hom ≫ b.inv ≫ c.inv
      hom_inv_id := by simp
      inv_hom_id := by simp }
  left_inv a := by apply Iso.ext; simp [Category.assoc]
  right_inv b := by apply Iso.ext; simp [Category.assoc]
  map_mul' a b := by
    apply Iso.ext
    change c.inv ≫ (b.hom ≫ a.hom) ≫ c.hom =
      (c.inv ≫ b.hom ≫ c.hom) ≫ (c.inv ≫ a.hom ≫ c.hom)
    simp [Category.assoc]

/-- Corollary 7.5 for arbitrary compatible endpoint subgroups.
The hypothesis is the precise statement that allowed source changes remain
allowed after conjugation, as required for a graph over all of `GX`. -/
noncomputable def generalIsoGraphMulEquiv (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hconj : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY) :
    GX ≃* generalComparisonSubgroup c.hom GX GY where
  toFun a := ⟨(a, ⟨generalConjugation c a.1, hconj a.1 a.2⟩), by
    change a.1.hom ≫ c.hom =
      c.hom ≫ (c.inv ≫ a.1.hom ≫ c.hom)
    simp⟩
  invFun pair := pair.1.1
  left_inv _ := rfl
  right_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      apply Iso.ext
      change c.inv ≫ pair.1.1.1.hom ≫ c.hom = pair.1.2.1.hom
      calc
        c.inv ≫ pair.1.1.1.hom ≫ c.hom =
            c.inv ≫ (pair.1.1.1.hom ≫ c.hom) := by simp
        _ = c.inv ≫ (c.hom ≫ pair.1.2.1.hom) := by rw [pair.2]
        _ = pair.1.2.1.hom := by simp
  map_mul' a b := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact map_mul (generalConjugation c) a.1 b.1

@[simp] theorem generalIsoGraphMulEquiv_source (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hconj : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY)
    (a : GX) :
    generalComparisonSourceProjection c.hom GX GY
      (generalIsoGraphMulEquiv c GX GY hconj a) = a := rfl

@[simp] theorem generalIsoGraphMulEquiv_target (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hconj : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY)
    (a : GX) :
    (generalComparisonTargetProjection c.hom GX GY
      (generalIsoGraphMulEquiv c GX GY hconj a)).1 =
      generalConjugation c a.1 := rfl

/-- Conjugation restricts to a group equivalence when the two chosen endpoint
subgroups correspond exactly under the comparison isomorphism. -/
noncomputable def generalRestrictedConjugation (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hforward : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY)
    (hbackward : ∀ b : Aut Y, b ∈ GY →
      (generalConjugation c).symm b ∈ GX) : GX ≃* GY where
  toFun a := ⟨generalConjugation c a.1, hforward a.1 a.2⟩
  invFun b := ⟨(generalConjugation c).symm b.1, hbackward b.1 b.2⟩
  left_inv a := by apply Subtype.ext; exact (generalConjugation c).symm_apply_apply a.1
  right_inv b := by apply Subtype.ext; exact (generalConjugation c).apply_symm_apply b.1
  map_mul' a b := by
    apply Subtype.ext
    exact map_mul (generalConjugation c) a.1 b.1

/-- Corollary 7.5's second endpoint equivalence: under exact subgroup
correspondence, the target projection is also a group isomorphism. -/
noncomputable def generalIsoTargetProjectionMulEquiv (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hforward : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY)
    (hbackward : ∀ b : Aut Y, b ∈ GY →
      (generalConjugation c).symm b ∈ GX) :
    generalComparisonSubgroup c.hom GX GY ≃* GY :=
  (generalIsoGraphMulEquiv c GX GY hforward).symm.trans
    (generalRestrictedConjugation c GX GY hforward hbackward)

@[simp] theorem generalIsoTargetProjectionMulEquiv_apply (c : X ≅ Y)
    (GX : Subgroup (Aut X)) (GY : Subgroup (Aut Y))
    (hforward : ∀ a : Aut X, a ∈ GX → generalConjugation c a ∈ GY)
    (hbackward : ∀ b : Aut Y, b ∈ GY →
      (generalConjugation c).symm b ∈ GX)
    (pair : generalComparisonSubgroup c.hom GX GY) :
    generalIsoTargetProjectionMulEquiv c GX GY hforward hbackward pair =
      generalComparisonTargetProjection c.hom GX GY pair := by
  have h := (generalIsoGraphMulEquiv c GX GY hforward).apply_symm_apply pair
  exact congrArg (fun q => q.1.2) h

end AAT.AG.ComparisonInformation

#assert_standard_axioms_only AAT.AG.ComparisonInformation
