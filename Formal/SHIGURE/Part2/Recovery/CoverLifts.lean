import Formal.SHIGURE.Part2.Recovery.LocalLawDescent
import Formal.SHIGURE.Part2.Recovery.RelativePullbackSite

/-!
# Relative tests factoring through open charts

A lift to a chart retains the underlying test scheme. Two lifts to
distinct charts give a test on their fiber product. Restriction along
maps of relative tests and the maps to inverse-image chart tests are
induced by the underlying scheme morphisms.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S}

/-- A relative test factors through the indicated open chart. -/
def CoverLift (C : Scheme.OpenCover.{u} S) (i : C.I₀) (T : Over S) :=
  {p : T.left ⟶ C.X i // p ≫ C.f i = T.hom}

namespace CoverLift

variable {i j : C.I₀} {T U V : Over S}

/-- A chart lift is unique because the chart inclusion is a monomorphism. -/
instance : Subsingleton (CoverLift C i T) :=
  ⟨fun a b => Subtype.ext ((cancel_mono (C.f i)).mp (a.property.trans b.property.symm))⟩

/-- The original test as a relative test over the chart. -/
abbrev test (a : CoverLift C i T) : Over (C.X i) := Over.mk a.val

/-- A test over an open chart is already a lift of its composite to the base. -/
def ofTest (W : Over (C.X i)) : CoverLift C i ((Over.map (C.f i)).obj W) :=
  ⟨W.hom, rfl⟩

/-- The lift of the source obtained by composing into a lifted target test. -/
def pullback (a : CoverLift C i T) (g : U ⟶ T) : CoverLift C i U :=
  ⟨g.left ≫ a.val, by rw [Category.assoc, a.property, Over.w]⟩

/-- Every map of tests with lifts commutes with their maps into the chart. -/
def map (a : CoverLift C i T) (b : CoverLift C i U) (g : U ⟶ T) : b.test ⟶ a.test :=
  Over.homMk g.left (congrArg Subtype.val (Subsingleton.elim (a.pullback g) b))

/-- A lifted identity reduces to the identity in the chart slice. -/
@[simp]
theorem map_id (a : CoverLift C i T) : a.map a (𝟙 T) = 𝟙 a.test :=
  Over.OverMorphism.ext rfl

/-- A lifted composite reduces to the composite of the lifted maps. -/
@[simp]
theorem map_comp (a : CoverLift C i T) (b : CoverLift C i U) (c : CoverLift C i V)
    (g : V ⟶ U) (h : U ⟶ T) : a.map c (g ≫ h) = b.map c g ≫ a.map b h :=
  Over.OverMorphism.ext rfl

/-- View a lifted test as a test over the base via the identity of its scheme. -/
def toBase (a : CoverLift C i T) : (Over.map (C.f i)).obj a.test ≅ T :=
  Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact a.property.symm)

/-- The canonical map from a test factoring through the chart to the inverse-image test. -/
def toChartTest (a : CoverLift C i U) (g : U ⟶ T) : a.test ⟶ coefficientCoverTest C T i :=
  coefficientCoverTestLift C T i (a.toBase.hom ≫ g)

/-- The pulled-back chart test is itself a lift. -/
abbrev chartLift (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀) :
    CoverLift C i ((Over.map (C.f i)).obj (coefficientCoverTest C T i)) :=
  ofTest (coefficientCoverTest C T i)

/-- Transport the canonical map to the chart test back to the base. -/
def toChartBase (a : CoverLift C i U) (g : U ⟶ T) :
    U ⟶ (Over.map (C.f i)).obj (coefficientCoverTest C T i) :=
  a.toBase.inv ≫ (Over.map (C.f i)).map (a.toChartTest g)

/-- The lift followed by the chart inclusion reduces to the original map of tests. -/
@[simp]
theorem toChartBase_inclusion (a : CoverLift C i U) (g : U ⟶ T) :
    a.toChartBase g ≫ coefficientCoverTestInclusion C T i = g := by
  simp only [toChartBase, Category.assoc, toChartTest, coefficientCoverTestLift_inclusion,
    Iso.inv_hom_id_assoc]

/-- The chart map read from the comparison over the base is the canonical lift. -/
theorem map_toChartBase (a : CoverLift C i U) (g : U ⟶ T) :
    (chartLift C T i).map a (a.toChartBase g) = a.toChartTest g := by
  apply Over.OverMorphism.ext
  change a.toBase.inv.left ≫ (a.toChartTest g).left = (a.toChartTest g).left
  simp [toBase]

/-- A map of tests induces the fiber-product map on their inverse-image opens. -/
def chartTestMap (g : U ⟶ T) (i : C.I₀) : coefficientCoverTest C U i ⟶ coefficientCoverTest C T i :=
  (relativeSchemePullback (C.f i)).map g

/-- The fiber-product map commutes with the chart inclusions. -/
@[reassoc]
theorem chartTestMap_inclusion (g : U ⟶ T) (i : C.I₀) :
    (Over.map (C.f i)).map (chartTestMap g i) ≫ coefficientCoverTestInclusion C T i =
      coefficientCoverTestInclusion C U i ≫ g := by
  apply Over.OverMorphism.ext
  exact Limits.pullback.lift_fst _ _ _

private theorem chartTest_ext (x y : U ⟶ (Over.map (C.f i)).obj (coefficientCoverTest C T i))
    (h : x ≫ coefficientCoverTestInclusion C T i = y ≫ coefficientCoverTestInclusion C T i) : x = y := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · exact congrArg (fun a : U ⟶ T => a.left) h
  · apply (cancel_mono (C.f i)).mp
    rw [Category.assoc, Category.assoc]
    exact (Over.w x).trans (Over.w y).symm

/-- The canonical lift is compatible with a map of target tests. -/
theorem toChartTest_comp_target (b : CoverLift C i V) (f : V ⟶ U) (g : U ⟶ T) :
    b.toChartTest (f ≫ g) = b.toChartTest f ≫ chartTestMap g i := by
  have h : b.toChartBase (f ≫ g) = b.toChartBase f ≫ (Over.map (C.f i)).map (chartTestMap g i) := by
    apply chartTest_ext
    rw [toChartBase_inclusion, Category.assoc, chartTestMap_inclusion, ← Category.assoc, toChartBase_inclusion]
  apply Over.OverMorphism.ext
  have e := congrArg (fun a : V ⟶ (Over.map (C.f i)).obj (coefficientCoverTest C T i) => a.left) h
  simpa only [toChartBase, Over.comp_left, Over.map_map_left, toBase, Over.isoMk_inv_left, Iso.refl_inv,
    Category.id_comp] using e

/-- The canonical lift is compatible with a map of lifted source tests. -/
theorem toChartTest_comp_source (a : CoverLift C i U) (b : CoverLift C i V) (f : V ⟶ U) (g : U ⟶ T) :
    b.toChartTest (f ≫ g) = a.map b f ≫ a.toChartTest g := by
  have h : b.toChartBase (f ≫ g) = f ≫ a.toChartBase g := by
    apply chartTest_ext
    rw [toChartBase_inclusion, Category.assoc, toChartBase_inclusion]
  apply Over.OverMorphism.ext
  have e := congrArg (fun a : V ⟶ (Over.map (C.f i)).obj (coefficientCoverTest C T i) => a.left) h
  simpa only [toChartBase, map, Over.homMk_left, Over.comp_left, Over.map_map_left, toBase,
    Over.isoMk_inv_left, Iso.refl_inv, Category.id_comp] using e

/-- Lifting the chart inclusion back into the same chart reduces to the identity. -/
@[simp]
theorem toChartTest_inclusion (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀) :
    (chartLift C T i).toChartTest (coefficientCoverTestInclusion C T i) = 𝟙 _ := by
  have h : (chartLift C T i).toChartBase (coefficientCoverTestInclusion C T i) = 𝟙 _ := by
    apply chartTest_ext
    rw [toChartBase_inclusion, Category.id_comp]
  rw [← map_toChartBase, h, map_id]

/-- Two lifts give a relative test over the actual intersection of the open charts. -/
def overlapTest (a : CoverLift C i T) (b : CoverLift C j T) :
    Over (Limits.pullback (C.f i) (C.f j)) :=
  Over.mk (Limits.pullback.lift a.val b.val (a.property.trans b.property.symm))

/-- The first projection of the overlap test has the same scheme and arrow as the first lift. -/
def overlapLeft (a : CoverLift C i T) (b : CoverLift C j T) :
    (Over.map (Limits.pullback.fst (C.f i) (C.f j))).obj (a.overlapTest b) ≅ a.test :=
  Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact (Limits.pullback.lift_fst _ _ _).symm)

/-- The second projection has the same scheme and arrow as the second lift. -/
def overlapRight (a : CoverLift C i T) (b : CoverLift C j T) :
    (Over.map (Limits.pullback.snd (C.f i) (C.f j))).obj (a.overlapTest b) ≅ b.test :=
  Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact (Limits.pullback.lift_snd _ _ _).symm)

/-- Maps of tests respect the common intersection of any two open lifts. -/
def overlapMap (a : CoverLift C i T) (b : CoverLift C j T) (a' : CoverLift C i U) (b' : CoverLift C j U)
    (g : U ⟶ T) : a'.overlapTest b' ⟶ a.overlapTest b :=
  Over.homMk g.left (by
    apply Limits.pullback.hom_ext
    · simp only [Category.assoc, overlapTest, Over.mk_hom, Limits.pullback.lift_fst]
      exact Over.w (a.map a' g)
    · simp only [Category.assoc, overlapTest, Over.mk_hom, Limits.pullback.lift_snd]
      exact Over.w (b.map b' g))

end CoverLift
end SHIGURE.Copying
