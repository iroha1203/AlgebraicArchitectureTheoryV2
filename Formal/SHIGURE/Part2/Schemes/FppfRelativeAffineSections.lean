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

variable {X Y : Scheme.{u}} {cover : FppfCover.{u,v} X} (m : CompatibleSchemeMapFamily cover Y)

/-- Compatibility of a recovered map on a base chart with every original
map on the base changes of the chart. -/
def CompatibleSchemeMapFamily.RecoveredOn {U : Scheme.{u}} (a : U ⟶ X) (g : U ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ ⦃i : cover.I₀⦄ (p : T ⟶ U) (q : T ⟶ cover.X i)
    (_ : p ≫ a = q ≫ cover.f i), p ≫ g = q ≫ m.map i

/-- The test property follows from checking the canonical overlaps of the
chart with the original family. -/
theorem CompatibleSchemeMapFamily.recoveredOn_of_pullback {U : Scheme.{u}} (a : U ⟶ X) (g : U ⟶ Y)
    (h : ∀ i, (cover.pullback₁ a).f i ≫ g = cover.pullbackHom a i ≫ m.map i) :
    m.RecoveredOn a g := by
  intro T i p q w
  let k := pullback.lift p q w
  have left : k ≫ (cover.pullback₁ a).f i = p := pullback.lift_fst p q w
  have right : k ≫ cover.pullbackHom a i = q := pullback.lift_snd p q w
  calc
    p ≫ g = k ≫ (cover.pullback₁ a).f i ≫ g := by rw [← Category.assoc, left]
    _ = k ≫ cover.pullbackHom a i ≫ m.map i := congrArg (k ≫ ·) (h i)
    _ = q ≫ m.map i := by rw [← Category.assoc, right]

private theorem recoveredMaps_agree {U V T : Scheme.{u}} {a : U ⟶ X} {b : V ⟶ X}
    {g : U ⟶ Y} {h : V ⟶ Y} (hg : m.RecoveredOn a g) (hh : m.RecoveredOn b h)
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
  exact (hg (r ≫ p) s ep).trans (hh (r ≫ q) s eq').symm

/-- Recovered morphisms on the open charts of the base glue uniquely to
a morphism agreeing on the original fppf cover. -/
theorem CompatibleSchemeMapFamily.glue_recovered (opens : Scheme.OpenCover.{w} X)
    (g : ∀ a, opens.X a ⟶ Y) (hg : ∀ a, m.RecoveredOn (opens.f a) (g a)) :
    ∃! f : X ⟶ Y, ∀ i, cover.f i ≫ f = m.map i := by
  have equal (a b : opens.I₀) : pullback.fst (opens.f a) (opens.f b) ≫ g a =
      pullback.snd (opens.f a) (opens.f b) ≫ g b :=
    recoveredMaps_agree m (hg a) (hg b) _ _ pullback.condition
  let f := opens.glueMorphisms g equal
  have h (i : cover.I₀) : cover.f i ≫ f = m.map i := by
    let W : (cover.X i).OpenCover := opens.pullback₁ (cover.f i)
    apply W.hom_ext
    intro a
    let p := W.f a
    let q := opens.pullbackHom (cover.f i) a
    have comm : q ≫ opens.f a = p ≫ cover.f i := opens.pullbackHom_map (cover.f i) a
    change p ≫ cover.f i ≫ f = p ≫ m.map i
    rw [← Category.assoc, ← comm, Category.assoc, opens.ι_glueMorphisms]
    exact hg a q p comm
  exact ⟨f, h, fun f' h' => fppfCover_hom_ext cover (fun i => (h' i).trans (h i).symm)⟩

end LocalSchemeMaps

section RelativeAffine

variable {X Y : Scheme.{u}} {cover : FppfCover.{u,v} X} (h : Y ⟶ X)
  (m : CompatibleSchemeMapFamily cover Y) (commutes : ∀ i, m.map i ≫ h = cover.f i)

private def restrictedMap {U : Scheme.{u}} (a : U ⟶ X) (i : cover.I₀) :
    (cover.pullback₁ a).X i ⟶ pullback h a :=
  pullback.lift (cover.pullbackHom a i ≫ m.map i) ((cover.pullback₁ a).f i)
    (by rw [Category.assoc, commutes, cover.pullbackHom_map])

private def restrictedFamily {U : Scheme.{u}} (a : U ⟶ X) :
    CompatibleSchemeMapFamily (cover.pullback₁ a) (pullback h a) where
  map := restrictedMap h m commutes a
  agree := by
    intro T i j p q w
    apply pullback.hom_ext
    · simp only [Category.assoc, restrictedMap, pullback.lift_fst]
      rw [← Category.assoc p, ← Category.assoc q]
      apply m.agree
      rw [Category.assoc, Category.assoc, cover.pullbackHom_map, cover.pullbackHom_map,
        ← Category.assoc, ← Category.assoc, w]
    · simpa only [Category.assoc, restrictedMap, pullback.lift_snd] using w

include commutes in
private theorem recoversAffineChart [IsAffineHom h] {U : Scheme.{u}} [IsAffine U] (a : U ⟶ X) :
    ∃ g : U ⟶ Y, m.RecoveredOn a g := by
  let W := cover.pullback₁ a
  let m' := restrictedFamily h m commutes a
  obtain ⟨g, hg, _⟩ := fppfAffineTargetMaps_existUnique W m'
  refine ⟨g ≫ pullback.fst h a, m.recoveredOn_of_pullback _ _ ?_⟩
  intro i
  change W.f i ≫ g ≫ pullback.fst h a = cover.pullbackHom a i ≫ m.map i
  rw [← Category.assoc, hg]
  exact pullback.lift_fst _ _ _

include commutes in
/-- An affine scheme over the base represents an actual fppf sheaf of
sections, with recovery of every section on the original cover. -/
theorem relativeAffineSection_descent [IsAffineHom h] :
    ∃! g : X ⟶ Y, (g ≫ h = 𝟙 X) ∧ ∀ i, cover.f i ≫ g = m.map i := by
  let A := X.affineOpenCover
  let W := A.openCover
  have each (i : W.I₀) : ∃ g : W.X i ⟶ Y, m.RecoveredOn (W.f i) g :=
    recoversAffineChart h m commutes (W.f i)
  choose g hg using each
  obtain ⟨s, hs, unique⟩ := m.glue_recovered W g hg
  have sOver : s ≫ h = 𝟙 X := by
    apply fppfCover_hom_ext cover
    intro i
    rw [← Category.assoc, hs, commutes, Category.comp_id]
  exact ⟨s, ⟨sOver, hs⟩, fun s' hs' => unique s' hs'.2⟩

end RelativeAffine

end

end SHIGURE.SchemeDescent
