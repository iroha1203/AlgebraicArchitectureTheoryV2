import Formal.SHIGURE.Part2.Schemes.FppfAffineTargetMaps

/-! # Fppf descent of sections of an affine morphism

The section condition and the identities on the original covering family
are detected on fppf covers. Over an affine open of the base, the section
descends as a map between affine schemes. The resulting maps glue on the
open cover of the base.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

section LocalSchemeMaps

variable {X Y : Scheme.{u}} {cover : FppfCover.{u,v} X} (m : ∀ i, cover.X i ⟶ Y)

/-- Recovery on the pullback cover of a chart also gives recovery on every
test object mapping to the chart and an original cover component. -/
private theorem recoveredMap_on_test {U : Scheme.{u}} (a : U ⟶ X) (g : U ⟶ Y)
    (h : ∀ i, (cover.pullback₁ a).f i ≫ g = cover.pullbackHom a i ≫ m i)
    {T : Scheme.{u}} {i : cover.I₀} (p : T ⟶ U) (q : T ⟶ cover.X i)
    (w : p ≫ a = q ≫ cover.f i) : p ≫ g = q ≫ m i := by
  let k := pullback.lift p q w
  have left : k ≫ (cover.pullback₁ a).f i = p := pullback.lift_fst p q w
  have right : k ≫ cover.pullbackHom a i = q := pullback.lift_snd p q w
  calc
    p ≫ g = k ≫ (cover.pullback₁ a).f i ≫ g := by rw [← Category.assoc, left]
    _ = k ≫ cover.pullbackHom a i ≫ m i := congrArg (k ≫ ·) (h i)
    _ = q ≫ m i := by rw [← Category.assoc, right]

/-- Two recovered maps agree on their overlap by fppf separation. -/
private theorem recoveredMaps_agree {U V T : Scheme.{u}} {a : U ⟶ X} {b : V ⟶ X}
    {g : U ⟶ Y} {h : V ⟶ Y}
    (hg : ∀ i, (cover.pullback₁ a).f i ≫ g = cover.pullbackHom a i ≫ m i)
    (hh : ∀ i, (cover.pullback₁ b).f i ≫ h = cover.pullbackHom b i ≫ m i)
    (p : T ⟶ U) (q : T ⟶ V) (w : p ≫ a = q ≫ b) : p ≫ g = q ≫ h := by
  let W := cover.pullback₁ (p ≫ a)
  apply fppfCover_hom_ext W
  intro i
  let r := W.f i
  let s := cover.pullbackHom (p ≫ a) i
  have eq : s ≫ cover.f i = r ≫ p ≫ a := cover.pullbackHom_map (p ≫ a) i
  have ep : (r ≫ p) ≫ a = s ≫ cover.f i := by rw [Category.assoc, ← eq]
  have eq' : (r ≫ q) ≫ b = s ≫ cover.f i := by rw [Category.assoc, ← w, ← eq]
  change r ≫ p ≫ g = r ≫ q ≫ h
  rw [← Category.assoc, ← Category.assoc]
  exact (recoveredMap_on_test m a g hg (r ≫ p) s ep).trans
    (recoveredMap_on_test m b h hh (r ≫ q) s eq').symm

/-- Recovered morphisms on the open charts of the base glue uniquely to
a morphism agreeing on the original fppf cover. -/
private theorem glue_recovered (opens : Scheme.OpenCover.{w} X)
    (g : ∀ a, opens.X a ⟶ Y)
    (hg : ∀ a i, (cover.pullback₁ (opens.f a)).f i ≫ g a =
      cover.pullbackHom (opens.f a) i ≫ m i) :
    ∃! f : X ⟶ Y, ∀ i, cover.f i ≫ f = m i := by
  have equal (a b : opens.I₀) : pullback.fst (opens.f a) (opens.f b) ≫ g a =
      pullback.snd (opens.f a) (opens.f b) ≫ g b :=
    recoveredMaps_agree m (hg a) (hg b) _ _ pullback.condition
  let f := opens.glueMorphisms g equal
  have h (i : cover.I₀) : cover.f i ≫ f = m i := by
    let W : (cover.X i).OpenCover := opens.pullback₁ (cover.f i)
    apply W.hom_ext
    intro a
    let p := W.f a
    let q := opens.pullbackHom (cover.f i) a
    have comm : q ≫ opens.f a = p ≫ cover.f i := opens.pullbackHom_map (cover.f i) a
    change p ≫ cover.f i ≫ f = p ≫ m i
    rw [← Category.assoc, ← comm, Category.assoc, opens.ι_glueMorphisms]
    exact recoveredMap_on_test m (opens.f a) (g a) (hg a) q p comm
  exact ⟨f, h, fun f' h' => fppfCover_hom_ext cover (fun i => (h' i).trans (h i).symm)⟩

end LocalSchemeMaps

section RelativeAffine

variable {X Y : Scheme.{u}} {cover : FppfCover.{u,v} X} (h : Y ⟶ X)
  (m : ∀ i, cover.X i ⟶ Y) (commutes : ∀ i, m i ≫ h = cover.f i)

/-- The restriction of a local section takes values in the scheme pullback. -/
private def restrictedMap {U : Scheme.{u}} (a : U ⟶ X) (i : cover.I₀) :
    (cover.pullback₁ a).X i ⟶ pullback h a :=
  pullback.lift (cover.pullbackHom a i ≫ m i) ((cover.pullback₁ a).f i)
    (by rw [Category.assoc, commutes, cover.pullbackHom_map])

variable (compatible : Presieve.Arrows.Compatible (yoneda.obj Y) cover.f m)

include compatible in
/-- The original test agreement implies agreement for the restricted sections. -/
private theorem restrictedMap_compatible {U : Scheme.{u}} (a : U ⟶ X) :
    Presieve.Arrows.Compatible (yoneda.obj (pullback h a)) (cover.pullback₁ a).f
      (restrictedMap h m commutes a) := by
  intro i j T p q w
  change p ≫ restrictedMap h m commutes a i = q ≫ restrictedMap h m commutes a j
  apply pullback.hom_ext
  · simp only [Category.assoc, restrictedMap, pullback.lift_fst]
    rw [← Category.assoc p, ← Category.assoc q]
    apply compatible i j T
    rw [Category.assoc, Category.assoc, cover.pullbackHom_map, cover.pullbackHom_map,
      ← Category.assoc, ← Category.assoc, w]
  · simpa only [Category.assoc, restrictedMap, pullback.lift_snd] using w

include commutes compatible in
/-- On an affine chart the section descends as a map to the affine pullback scheme. -/
private theorem recoversAffineChart [IsAffineHom h] {U : Scheme.{u}} [IsAffine U] (a : U ⟶ X) :
    ∃ g : U ⟶ Y, ∀ i, (cover.pullback₁ a).f i ≫ g = cover.pullbackHom a i ≫ m i := by
  let W := cover.pullback₁ a
  let m' := restrictedMap h m commutes a
  obtain ⟨g, hg, _⟩ := fppfAffineTargetMaps_existUnique W m' (restrictedMap_compatible h m commutes compatible a)
  refine ⟨g ≫ pullback.fst h a, ?_⟩
  intro i
  change W.f i ≫ g ≫ pullback.fst h a = cover.pullbackHom a i ≫ m i
  rw [← Category.assoc, hg]
  exact pullback.lift_fst _ _ _

include commutes compatible in
/-- An affine scheme over the base represents an actual fppf sheaf of
sections, with recovery of every section on the original cover.
This gives the section descent used for the relative spectrum in B.3.
Affineness is the property of the B.7 projection. The fppf family,
its overlap agreement and its local section equations are the input datum. -/
theorem relativeAffineSection_descent [IsAffineHom h] :
    ∃! g : X ⟶ Y, (g ≫ h = 𝟙 X) ∧ ∀ i, cover.f i ≫ g = m i := by
  let A := X.affineOpenCover
  let W := A.openCover
  have each (a : W.I₀) : ∃ g : W.X a ⟶ Y, ∀ i,
      (cover.pullback₁ (W.f a)).f i ≫ g = cover.pullbackHom (W.f a) i ≫ m i :=
    recoversAffineChart h m commutes compatible (W.f a)
  choose g hg using each
  obtain ⟨s, hs, unique⟩ := glue_recovered m W g hg
  have sOver : s ≫ h = 𝟙 X := by
    apply fppfCover_hom_ext cover
    intro i
    rw [← Category.assoc, hs, commutes, Category.comp_id]
  exact ⟨s, ⟨sOver, hs⟩, fun s' hs' => unique s' hs'.2⟩

end RelativeAffine

end

end SHIGURE.SchemeDescent
