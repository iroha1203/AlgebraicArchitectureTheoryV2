import Formal.SHIGURE.Part2.Recovery.LocalLawDescent

/-!
# Gluing carrier maps across coefficient opens

The overlap condition compares the local maps after restricting sections
to a common relative test. The sheaf axiom on the inverse-image cover of
each test then constructs the unique global map.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} (C : Scheme.OpenCover.{u} S) {F G : ZariskiSheaf S}

/-- Compatibility of local sheaf maps on every test of an overlap. -/
structure LocalSheafMaps (F G : ZariskiSheaf S) where
  /-- The actual sheaf map over a member of the open cover. -/
  onOpen (i : C.I₀) : (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj F ⟶
    (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).obj G
  /-- Sections that restrict to the same section on an overlap have the same restricted images. -/
  agree (i j : C.I₀) {T : Over S} {U : Over (C.X i)} {V : Over (C.X j)}
    (a : T ⟶ (Over.map (C.f i)).obj U) (b : T ⟶ (Over.map (C.f j)).obj V)
    (x : F.val.obj (op ((Over.map (C.f i)).obj U))) (y : F.val.obj (op ((Over.map (C.f j)).obj V))) :
    F.val.map a.op x = F.val.map b.op y →
      G.val.map a.op ((onOpen i).val.app (op U) x) = G.val.map b.op ((onOpen j).val.app (op V) y)

namespace LocalSheafMaps

variable {C} (D : LocalSheafMaps C F G)

/-- Restrict a single global map to the cover; naturality supplies the overlap condition. -/
def ofGlobal (f : F ⟶ G) : LocalSheafMaps C F G where
  onOpen i := (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map f
  agree i j T U V a b x y e := by
    change G.val.map a.op (f.val.app (op ((Over.map (C.f i)).obj U)) x) =
      G.val.map b.op (f.val.app (op ((Over.map (C.f j)).obj V)) y)
    rw [← FunctorToTypes.naturality _ _ f.val a.op, ← FunctorToTypes.naturality _ _ f.val b.op, e]

private def openImage (T : Over S) (x : F.val.obj (op T)) (i : C.I₀) :=
  (D.onOpen i).val.app (op (coefficientCoverTest C T i))
    (F.val.map (coefficientCoverTestInclusion C T i).op x)

private theorem openImage_compatible (T : Over S) (x : F.val.obj (op T)) :
    Presieve.Arrows.Compatible G.val (coefficientCoverTestInclusion C T) (D.openImage T x) := by
  intro i j W a b e
  apply D.agree i j a b
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, e]

private theorem exists_gluedSection (T : Over S) (x : F.val.obj (op T)) :
    ∃! y : G.val.obj (op T), ∀ i, G.val.map (coefficientCoverTestInclusion C T i).op y = D.openImage T x i := by
  let U := fun i => (Over.map (C.f i)).obj (coefficientCoverTest C T i)
  let ι := coefficientCoverTestInclusion C T
  have hC : Sieve.ofArrows U ι ∈ (Scheme.zariskiTopology.over S) T :=
    coefficientCoverTest_covering C T _ (Sieve.ofArrows_mk _ _)
  have hG := (isSheaf_iff_isSheaf_of_type _ _).mp G.cond
  exact (Presieve.isSheafFor_arrows_iff G.val ι).mp
    ((Presieve.isSheafFor_iff_generate _).mpr (hG _ hC)) _ (D.openImage_compatible T x)

private def gluedSection (T : Over S) (x : F.val.obj (op T)) : G.val.obj (op T) :=
  (D.exists_gluedSection T x).choose

private theorem gluedSection_onCover (T : Over S) (x : F.val.obj (op T)) (i : C.I₀) :
    G.val.map (coefficientCoverTestInclusion C T i).op (D.gluedSection T x) = D.openImage T x i :=
  (D.exists_gluedSection T x).choose_spec.1 i

private theorem gluedSection_onOpen (i : C.I₀) {U : Over (C.X i)} {T : Over S}
    (a : (Over.map (C.f i)).obj U ⟶ T) (x : F.val.obj (op T)) :
    G.val.map a.op (D.gluedSection T x) = (D.onOpen i).val.app (op U) (F.val.map a.op x) := by
  let V := (Over.map (C.f i)).obj U
  apply coefficientCoverTest_sections_ext C V G
  intro j
  let b := coefficientCoverTestInclusion C V j
  let v := coefficientCoverTestInclusion C T j
  let p := (Over.map (C.f j)).map (coefficientCoverTestLift C T j (b ≫ a))
  have hp : p ≫ v = b ≫ a := coefficientCoverTestLift_inclusion C T j (b ≫ a)
  have commute (P : (Over S)ᵒᵖ ⥤ Type u) (z : P.obj (op T)) :
      P.map b.op (P.map a.op z) = P.map p.op (P.map v.op z) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, hp]
  rw [commute, D.gluedSection_onCover]
  exact D.agree j i p b _ _ (commute F.val x).symm

/-- Glue all local maps by the actual compatible sections on each relative test. -/
def glue : F ⟶ G :=
  ⟨{ app := fun T => ↾D.gluedSection T.unop
     naturality := by
       intro U V a
       ext x
       apply coefficientCoverTest_sections_ext C V.unop G
       intro i
       let b := coefficientCoverTestInclusion C V.unop i
       have h := D.gluedSection_onOpen i (b ≫ a.unop) x
       rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply] at h
       exact (D.gluedSection_onOpen i b (F.val.map a x)).trans h.symm }⟩

/-- The glued arrow restricts to the specified arrow on every coefficient open. -/
theorem glue_onOpen (i : C.I₀) :
    (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map D.glue = D.onOpen i := by
  ext U x
  have h := D.gluedSection_onOpen i (𝟙 ((Over.map (C.f i)).obj U.unop)) x
  rw [op_id, FunctorToTypes.map_id_apply, FunctorToTypes.map_id_apply] at h
  exact h

/-- The gluing of the restrictions of a global arrow recovers it. -/
theorem glue_ofGlobal (f : F ⟶ G) : (ofGlobal (C := C) f).glue = f := by
  ext T x
  apply coefficientCoverTest_sections_ext C T.unop G
  intro i
  exact ((ofGlobal (C := C) f).gluedSection_onCover T.unop x i).trans
    (FunctorToTypes.naturality _ _ f.val (coefficientCoverTestInclusion C T.unop i).op x)

end LocalSheafMaps
end SHIGURE.Copying
