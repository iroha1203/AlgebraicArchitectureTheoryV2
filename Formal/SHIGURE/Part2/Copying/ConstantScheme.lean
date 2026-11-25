import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Constant schemes of states

Construction 4.2 and the scheme side of Theorem 4.3.

## Implementation notes

A constant scheme is the scheme coproduct of copies of the base. The structural
map is the fold map. A test scheme over the base maps into the coproduct by
choosing a copy locally, as recorded by a locally constant function on its space.
The fibres of these functions give the clopen decomposition when needed. Keeping
the label function as the common datum makes precomposition and base change
pointwise and avoids explicit transport of a family of open subschemes.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace SHIGURE.Copying

universe u

variable (S : Scheme.{u})

/-- The constant scheme of Construction 4.2, expressed over an arbitrary base scheme. -/
def constantScheme (X : Type u) : Scheme.{u} :=
  ∐ (fun _ : X => S)

/-- The inclusion of a state of the constant scheme in Construction 4.2. -/
def stateInclusion (X : Type u) (x : X) : S ⟶ constantScheme S X :=
  Sigma.ι (fun _ : X => S) x

/-- The coproduct copies of Construction 4.2 are open subschemes. -/
instance stateInclusion_isOpenImmersion (X : Type u) (x : X) :
    IsOpenImmersion (stateInclusion S X x) := by
  change IsOpenImmersion (Sigma.ι (fun _ : X => S) x)
  infer_instance

/-- The structural map of the constant scheme is given by folding all copies onto the base. -/
def constantSchemeOver (X : Type u) : Over S :=
  Over.mk (Sigma.desc fun _ : X => 𝟙 S)

/-- A state inclusion is over the base. Simplify the composite to the identity of the base. -/
@[reassoc (attr := simp)]
theorem stateInclusion_over (X : Type u) (x : X) :
    stateInclusion S X x ≫ (constantSchemeOver S X).hom = 𝟙 S :=
  Sigma.ι_desc _ _

/-- Construction 4.2 sends a function of states to the corresponding arrow of constant schemes. -/
def mapStateSchemes {X Y : Type u} (f : X → Y) :
    constantSchemeOver S X ⟶ constantSchemeOver S Y :=
  Over.homMk (Sigma.desc (fun x => stateInclusion S Y (f x))) <| by
    apply Sigma.hom_ext
    intro x
    simp only [Sigma.ι_desc_assoc]
    exact (stateInclusion_over S Y (f x)).trans (stateInclusion_over S X x).symm

/-- The arrow of Construction 4.2 on a state inclusion. Simplify to the inclusion of its image. -/
@[reassoc (attr := simp)]
theorem stateInclusion_mapStateSchemes {X Y : Type u} (f : X → Y) (x : X) :
    stateInclusion S X x ≫ (mapStateSchemes S f).left = stateInclusion S Y (f x) :=
  Sigma.ι_desc _ _

variable {S}

/-- The state of a point of the constant scheme, from the underlying space of the coproduct. -/
def stateLabel {X : Type u} (x : constantScheme S X) : X :=
  (AlgebraicGeometry.sigmaMk (fun _ : X => S)).symm x |>.1

/-- A point of a state summand has that state's label. Simplify on the summand inclusion. -/
@[simp]
theorem stateLabel_inclusion {X : Type u} (i : X) (x : S) :
    stateLabel (stateInclusion S X i x) = i := by
  change ((AlgebraicGeometry.sigmaMk (fun _ : X => S)).symm (Sigma.ι (fun _ : X => S) i x)).1 = i
  simpa only [AlgebraicGeometry.sigmaMk_mk] using
    congrArg Sigma.fst ((AlgebraicGeometry.sigmaMk (fun _ : X => S)).symm_apply_apply ⟨i, x⟩)

/-- The label fibres of the constant scheme are the open summands of its coproduct. -/
theorem stateLabel_eq_iff_mem_range {X : Type u} (i : X) (x : constantScheme S X) :
    stateLabel x = i ↔ x ∈ Set.range (stateInclusion S X i) := by
  constructor
  · intro hx
    obtain ⟨⟨j, y⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun _ : X => S)).surjective x
    rw [AlgebraicGeometry.sigmaMk_mk] at hx ⊢
    change stateLabel (stateInclusion S X j y) = i at hx
    rw [stateLabel_inclusion] at hx
    subst j
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact stateLabel_inclusion i y

/-- The label of an arrow into a constant scheme is locally constant on the test scheme. -/
def labelOfPoint {T : Over S} {X : Type u} (f : T ⟶ constantSchemeOver S X) :
    LocallyConstant T.left X where
  toFun p := stateLabel (f.left p)
  isLocallyConstant := IsLocallyConstant.iff_isOpen_fiber.mpr fun i => by
    have h : (fun p => stateLabel (f.left p)) ⁻¹' {i} =
        f.left ⁻¹' Set.range (stateInclusion S X i) := by
      ext p
      exact stateLabel_eq_iff_mem_range i (f.left p)
    rw [h]
    exact (stateInclusion S X i).isOpenEmbedding.isOpen_range.preimage f.left.continuous

/-- The open part of a locally constant label at a chosen state, used to recover a scheme map. -/
def labelPart {T : Scheme.{u}} {X : Type u} (l : LocallyConstant T X) (i : X) : T.Opens :=
  ⟨{x | l x = i}, l.isLocallyConstant.isOpen_fiber i⟩

/-- Membership in the open part is evaluation of its label. Simplify membership to equality. -/
@[simp]
theorem mem_labelPart {T : Scheme.{u}} {X : Type u} (l : LocallyConstant T X) (i : X) (x : T) :
    x ∈ labelPart l i ↔ l x = i :=
  Iff.rfl

/-- The open parts of a locally constant label express the scheme as their disjoint coproduct. -/
def labelCofanIsColimit {T : Scheme.{u}} {X : Type u} (l : LocallyConstant T X) :
    IsColimit (Cofan.mk T fun i : X => (labelPart l i).ι) :=
  Nonempty.some <| AlgebraicGeometry.nonempty_isColimit_cofanMk_of _
    (by
      simp only [Scheme.Opens.opensRange_ι]
      apply top_unique
      intro x _
      rw [Opens.mem_iSup]
      exact ⟨l x, rfl⟩)
    (by
      intro i j hij
      simp only [Scheme.Opens.opensRange_ι]
      change Disjoint (labelPart l i) (labelPart l j)
      rw [disjoint_iff]
      apply le_bot_iff.mp
      rintro x ⟨hi, hj⟩
      exact hij (hi.symm.trans hj))

/-- The scheme arrow belonging to a locally constant label, formed by gluing the structural
maps from open parts into their selected copies of the base. -/
def pointOfLabel {T : Over S} {X : Type u} (l : LocallyConstant T.left X) :
    T ⟶ constantSchemeOver S X :=
  let c := labelCofanIsColimit l
  Over.homMk (c.desc (Cofan.mk _ fun i => (labelPart l i).ι ≫ T.hom ≫ stateInclusion S X i)) <| by
    apply c.hom_ext
    rintro ⟨i⟩
    rw [c.fac_assoc]
    change ((labelPart l i).ι ≫ T.hom ≫ stateInclusion S X i) ≫
      (constantSchemeOver S X).hom = (labelPart l i).ι ≫ T.hom
    simp

/-- The point built from a label sends each part into its selected copy of the base. -/
@[reassoc]
theorem labelPart_pointOfLabel {T : Over S} {X : Type u} (l : LocallyConstant T.left X) (i : X) :
    (labelPart l i).ι ≫ (pointOfLabel l).left =
      (labelPart l i).ι ≫ T.hom ≫ stateInclusion S X i :=
  (labelCofanIsColimit l).fac _ ⟨i⟩

/-- The selected label is recovered pointwise from the glued arrow into the coproduct. -/
theorem labelOfPoint_pointOfLabel {T : Over S} {X : Type u} (l : LocallyConstant T.left X) :
    labelOfPoint (pointOfLabel l) = l := by
  ext x
  let i := l x
  have hx : x ∈ Set.range (labelPart l i).ι := by
    rw [Scheme.Opens.range_ι]
    rfl
  obtain ⟨q, hq⟩ := hx
  change stateLabel ((pointOfLabel l).left x) = i
  rw [← hq, ← Scheme.Hom.comp_apply, labelPart_pointOfLabel]
  exact stateLabel_inclusion i (T.hom ((labelPart l i).ι q))

/-- A map into the constant scheme over the base is determined by its locally constant label. -/
theorem pointOfLabel_labelOfPoint {T : Over S} {X : Type u}
    (f : T ⟶ constantSchemeOver S X) : pointOfLabel (labelOfPoint f) = f := by
  apply Over.OverMorphism.ext
  let l := labelOfPoint f
  apply (labelCofanIsColimit l).hom_ext
  rintro ⟨i⟩
  change (labelPart l i).ι ≫ (pointOfLabel l).left = (labelPart l i).ι ≫ f.left
  rw [labelPart_pointOfLabel]
  let ιi := stateInclusion S X i
  let g := (labelPart l i).ι ≫ f.left
  have hg : Set.range g ⊆ Set.range ιi := by
    rintro _ ⟨x, rfl⟩
    apply (stateLabel_eq_iff_mem_range i _).mp
    have hx : (labelPart l i).ι x ∈ labelPart l i := x.property
    exact (mem_labelPart l i _).mp hx
  let g' := IsOpenImmersion.lift ιi g hg
  have hfac : g' ≫ ιi = g := IsOpenImmersion.lift_fac _ _ _
  have hbase : g' = (labelPart l i).ι ≫ T.hom := by
    calc
      g' = g' ≫ ιi ≫ (constantSchemeOver S X).hom := by
        change g' = g' ≫ stateInclusion S X i ≫ (constantSchemeOver S X).hom
        simp
      _ = g ≫ (constantSchemeOver S X).hom := by rw [← Category.assoc, hfac]
      _ = (labelPart l i).ι ≫ T.hom := by
        change ((labelPart l i).ι ≫ f.left) ≫ (constantSchemeOver S X).hom = _
        rw [Category.assoc, Over.w]
  rw [← Category.assoc, ← hbase]
  exact hfac

/-- The scheme-side point calculation of Theorem 4.3, for any test scheme over the base. -/
def constantPointLabelsEquiv (T : Over S) (X : Type u) :
    (T ⟶ constantSchemeOver S X) ≃ LocallyConstant T.left X where
  toFun := labelOfPoint
  invFun := pointOfLabel
  left_inv := pointOfLabel_labelOfPoint
  right_inv := labelOfPoint_pointOfLabel

/-- The point formula for the forward direction of `constantPointLabelsEquiv` in Theorem 4.3. -/
theorem constantPointLabelsEquiv_apply {T : Over S} {X : Type u}
    (f : T ⟶ constantSchemeOver S X) (p : T.left) :
    constantPointLabelsEquiv T X f p = stateLabel (f.left p) :=
  rfl

/-- Naturality in the test scheme for the point computation of Theorem 4.3. -/
theorem constantPointLabelsEquiv_precomp {T U : Over S} {X : Type u}
    (g : U ⟶ T) (f : T ⟶ constantSchemeOver S X) (p : U.left) :
    constantPointLabelsEquiv U X (g ≫ f) p =
      constantPointLabelsEquiv T X f (g.left p) :=
  rfl

/-- The label of the image under a state function is the image of the label in Construction 4.2. -/
@[simp]
theorem stateLabel_mapStateSchemes {X Y : Type u} (f : X → Y) (p : constantScheme S X) :
    stateLabel ((mapStateSchemes S f).left p) = f (stateLabel p) := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun _ : X => S)).surjective p
  rw [AlgebraicGeometry.sigmaMk_mk]
  change stateLabel ((mapStateSchemes S f).left (stateInclusion S X i x)) =
    f (stateLabel (stateInclusion S X i x))
  have h := congrArg (fun g : S ⟶ constantScheme S Y => g x) (stateInclusion_mapStateSchemes S f i)
  change (mapStateSchemes S f).left (stateInclusion S X i x) = stateInclusion S Y (f i) x at h
  rw [h, stateLabel_inclusion, stateLabel_inclusion]

/-- Construction 4.2 preserves the identity state function on the scheme side. -/
theorem mapStateSchemes_id (X : Type u) :
    mapStateSchemes S (id : X → X) = 𝟙 (constantSchemeOver S X) := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  change stateInclusion S X i ≫ (mapStateSchemes S id).left =
    stateInclusion S X i ≫ 𝟙 (constantScheme S X)
  simp

/-- Construction 4.2 preserves composition of state functions on the scheme side. -/
theorem mapStateSchemes_comp {X Y Z : Type u} (f : X → Y) (g : Y → Z) :
    mapStateSchemes S (g ∘ f) = mapStateSchemes S f ≫ mapStateSchemes S g := by
  apply Over.OverMorphism.ext
  apply Sigma.hom_ext
  intro i
  change stateInclusion S X i ≫ (mapStateSchemes S (g ∘ f)).left =
    stateInclusion S X i ≫ (mapStateSchemes S f).left ≫ (mapStateSchemes S g).left
  simp

/-- Two arrows into a constant scheme over the base agree if they select the same state
at every point. This is the uniqueness part of the scheme comparison of Theorem 4.3. -/
theorem constantPoint_ext {T : Over S} {X : Type u}
    {f g : T ⟶ constantSchemeOver S X}
    (h : ∀ p : T.left, stateLabel (f.left p) = stateLabel (g.left p)) : f = g := by
  apply (constantPointLabelsEquiv T X).injective
  ext p
  exact h p

variable {S' : Scheme.{u}}

/-- On each summand the comparison to the original constant scheme uses the base morphism. -/
def mapConstantBase (g : S' ⟶ S) (X : Type u) : constantScheme S' X ⟶ constantScheme S X :=
  Sigma.desc fun x => g ≫ stateInclusion S X x

/-- Simplify the base comparison of a summand to the base morphism followed by the inclusion. -/
@[reassoc (attr := simp)]
theorem stateInclusion_mapConstantBase (g : S' ⟶ S) (X : Type u) (x : X) :
    stateInclusion S' X x ≫ mapConstantBase g X = g ≫ stateInclusion S X x :=
  Sigma.ι_desc _ _

/-- The structural maps for the constant-scheme comparison give a commuting square. -/
@[reassoc]
theorem mapConstantBase_over (g : S' ⟶ S) (X : Type u) :
    mapConstantBase g X ≫ (constantSchemeOver S X).hom =
      (constantSchemeOver S' X).hom ≫ g := by
  apply Sigma.hom_ext
  intro x
  change stateInclusion S' X x ≫ mapConstantBase g X ≫ (constantSchemeOver S X).hom =
    stateInclusion S' X x ≫ (constantSchemeOver S' X).hom ≫ g
  simp

/-- The base comparison takes a point to a point with the same label. Simplify to its
label in the constant scheme over the new base. -/
@[simp]
theorem stateLabel_mapConstantBase (g : S' ⟶ S) {X : Type u} (p : constantScheme S' X) :
    stateLabel (mapConstantBase g X p) = stateLabel p := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun _ : X => S')).surjective p
  rw [AlgebraicGeometry.sigmaMk_mk]
  change stateLabel (mapConstantBase g X (stateInclusion S' X i x)) =
    stateLabel (stateInclusion S' X i x)
  have h := congrArg (fun k : S' ⟶ constantScheme S X => k x) (stateInclusion_mapConstantBase g X i)
  change mapConstantBase g X (stateInclusion S' X i x) = stateInclusion S X i (g x) at h
  rw [h, stateLabel_inclusion, stateLabel_inclusion]

/-- Changing the base of a constant scheme is a pullback, as used in Theorem 4.3.
The universal arrow uses the old label and the new structural map. -/
theorem constantScheme_isPullback (g : S' ⟶ S) (X : Type u) :
    IsPullback (mapConstantBase g X) (constantSchemeOver S' X).hom
      (constantSchemeOver S X).hom g := by
  let liftPoint (c : PullbackCone (constantSchemeOver S X).hom g) :
      Over.mk c.snd ⟶ constantSchemeOver S' X :=
    let l : LocallyConstant c.pt X := labelOfPoint ((Over.homMk c.fst c.condition) :
      Over.mk (c.snd ≫ g) ⟶ constantSchemeOver S X)
    pointOfLabel (T := Over.mk c.snd) l
  refine IsPullback.of_isLimit' ⟨mapConstantBase_over g X⟩
    (PullbackCone.IsLimit.mk _ (fun c => (liftPoint c).left) ?_ ?_ ?_)
  · intro c
    let m := liftPoint c
    have hw : (m.left ≫ mapConstantBase g X) ≫ (constantSchemeOver S X).hom = c.snd ≫ g := by
      rw [Category.assoc, mapConstantBase_over, ← Category.assoc, Over.w m]
      rfl
    let f₁ : Over.mk (c.snd ≫ g) ⟶ constantSchemeOver S X :=
      Over.homMk (m.left ≫ mapConstantBase g X) hw
    let f₂ : Over.mk (c.snd ≫ g) ⟶ constantSchemeOver S X := Over.homMk c.fst c.condition
    have he : f₁ = f₂ := by
      apply constantPoint_ext
      intro p
      change stateLabel (mapConstantBase g X (m.left p)) = stateLabel (f₂.left p)
      rw [stateLabel_mapConstantBase]
      let l : LocallyConstant c.pt X := labelOfPoint (S := S) (T := Over.mk (c.snd ≫ g)) f₂
      exact congrArg (fun t : LocallyConstant c.pt X => t p)
        (labelOfPoint_pointOfLabel (T := Over.mk c.snd) l)
    exact congrArg (fun f => f.left) he
  · intro c
    exact Over.w (liftPoint c)
  · intro c m hm₁ hm₂
    let k : Over.mk c.snd ⟶ constantSchemeOver S' X := Over.homMk m hm₂
    let f : Over.mk (c.snd ≫ g) ⟶ constantSchemeOver S X := Over.homMk c.fst c.condition
    have he : k = liftPoint c := by
      apply constantPoint_ext
      intro p
      have h := congrArg (fun h : c.pt ⟶ constantScheme S X => h p) hm₁
      change mapConstantBase g X (m p) = c.fst p at h
      calc
        stateLabel (k.left p) = stateLabel (mapConstantBase g X (m p)) := by
          rw [stateLabel_mapConstantBase]
          rfl
        _ = stateLabel (c.fst p) := congrArg stateLabel h
        _ = stateLabel ((liftPoint c).left p) := by
          let l : LocallyConstant c.pt X := labelOfPoint (S := S) (T := Over.mk (c.snd ≫ g)) f
          exact (congrArg (fun t : LocallyConstant c.pt X => t p)
            (labelOfPoint_pointOfLabel (T := Over.mk c.snd) l)).symm
    exact congrArg (fun f => f.left) he

/-- Pullback of an arrow of constant schemes along a base arrow in Theorem 4.3. -/
def changeConstantMapBase (g : S' ⟶ S) {X Y : Type u}
    (f : constantSchemeOver S X ⟶ constantSchemeOver S Y) :
    constantSchemeOver S' X ⟶ constantSchemeOver S' Y :=
  let h := constantScheme_isPullback g Y
  let k : mapConstantBase g X ≫ f.left ≫ (constantSchemeOver S Y).hom =
      (constantSchemeOver S' X).hom ≫ g := by
    rw [Over.w f]
    exact mapConstantBase_over g X
  Over.homMk (h.lift (mapConstantBase g X ≫ f.left) (constantSchemeOver S' X).hom
    (by simpa only [Category.assoc] using k)) (h.lift_snd _ _ _)

/-- The pulled-back arrow in Theorem 4.3 satisfies the pullback compatibility
equation on the original constant schemes. -/
@[reassoc]
theorem changeConstantMapBase_fst (g : S' ⟶ S) {X Y : Type u}
    (f : constantSchemeOver S X ⟶ constantSchemeOver S Y) :
    (changeConstantMapBase g f).left ≫ mapConstantBase g Y =
      mapConstantBase g X ≫ f.left :=
  (constantScheme_isPullback g Y).lift_fst _ _ _

/-- The label of a pulled-back arrow is the pullback of its label along the base comparison
in Theorem 4.3. -/
theorem stateLabel_changeConstantMapBase (g : S' ⟶ S) {X Y : Type u}
    (f : constantSchemeOver S X ⟶ constantSchemeOver S Y) (p : constantScheme S' X) :
    stateLabel ((changeConstantMapBase g f).left p) =
      stateLabel (f.left (mapConstantBase g X p)) := by
  have h := changeConstantMapBase_fst g f
  have hp := congrArg (fun k : constantScheme S' X ⟶ constantScheme S Y => k p) h
  change mapConstantBase g Y ((changeConstantMapBase g f).left p) =
    f.left (mapConstantBase g X p) at hp
  rw [← hp, stateLabel_mapConstantBase]

/-- The state inclusion, as an arrow over the base. -/
def overStateInclusion (S : Scheme.{u}) (X : Type u) (x : X) :
    Over.mk (𝟙 S) ⟶ constantSchemeOver S X :=
  Over.homMk (stateInclusion S X x) (stateInclusion_over S X x)

/-- An arrow out of a constant scheme over the base is determined by the maps from its copies
of the base, as in Theorem 4.3. -/
def constantMapsPointsEquiv (S : Scheme.{u}) (X Y : Type u) :
    (constantSchemeOver S X ⟶ constantSchemeOver S Y) ≃
      (X → (Over.mk (𝟙 S) ⟶ constantSchemeOver S Y)) where
  toFun f x := overStateInclusion S X x ≫ f
  invFun F := Over.homMk (Sigma.desc fun i => (F i).left) <| by
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_desc_assoc, Over.w]
    exact (stateInclusion_over S X i).symm
  left_inv f := by
    apply Over.OverMorphism.ext
    apply Sigma.hom_ext
    intro i
    exact Sigma.ι_desc _ _
  right_inv F := by
    funext i
    apply Over.OverMorphism.ext
    exact Sigma.ι_desc _ _

/-- An arrow into the constant scheme sends each point to the summand predicted by its label
and to the point in that summand predicted by its structural map. -/
theorem stateInclusion_label_over {X : Type u} (p : constantScheme S X) :
    stateInclusion S X (stateLabel p) ((constantSchemeOver S X).hom p) = p := by
  obtain ⟨⟨i, x⟩, rfl⟩ := (AlgebraicGeometry.sigmaMk (fun _ : X => S)).surjective p
  rw [AlgebraicGeometry.sigmaMk_mk]
  change stateInclusion S X (stateLabel (stateInclusion S X i x))
    ((constantSchemeOver S X).hom (stateInclusion S X i x)) = stateInclusion S X i x
  have h := congrArg (fun k : S ⟶ S => k x) (stateInclusion_over S X i)
  change (constantSchemeOver S X).hom (stateInclusion S X i x) = x at h
  rw [h, stateLabel_inclusion]

/-- At a point of the affine base, the state label and the point of the base determine
the image of a point under a constant-scheme arrow. -/
theorem image_stateInclusion_eq {X Y : Type u} (f : constantSchemeOver S X ⟶ constantSchemeOver S Y)
    (x : X) (p : S) :
    f.left (stateInclusion S X x p) =
      stateInclusion S Y (stateLabel (f.left (stateInclusion S X x p))) p := by
  have h := stateInclusion_label_over (f.left (stateInclusion S X x p))
  have hw := congrArg (fun k : S ⟶ S => k p)
    (show stateInclusion S X x ≫ f.left ≫ (constantSchemeOver S Y).hom = 𝟙 S from
      by rw [Over.w f, stateInclusion_over])
  change (constantSchemeOver S Y).hom (f.left (stateInclusion S X x p)) = p at hw
  rw [hw] at h
  exact h.symm

end SHIGURE.Copying
