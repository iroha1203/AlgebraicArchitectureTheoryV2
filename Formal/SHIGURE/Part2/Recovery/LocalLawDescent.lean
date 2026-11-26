import Formal.SHIGURE.Part2.Recovery.PresentationRestriction
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# Locality of Laws under a Zariski covering of coefficients

On an arbitrary relative test, the pullback open cover detects membership
in the conclusion subsheaf. This transports local model conditions to the
global sheaf structure, including Laws with positive local witnesses.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {sig : Signature.{u}}

/-- The piece of a relative test over one member of the coefficient cover. -/
def coefficientCoverTest (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀) : Over (C.X i) :=
  Over.mk (C.pullbackHom T.hom i)

/-- The inverse-image open considered as a morphism of tests over the original base. -/
def coefficientCoverTestInclusion (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀) :
    (Over.map (C.f i)).obj (coefficientCoverTest C T i) ⟶ T :=
  Over.homMk ((C.pullback₁ T.hom).f i) (C.pullbackHom_map T.hom i).symm

/-- A test factoring through a cover member maps to the inverse-image open by the fiber product. -/
def coefficientCoverTestLift (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀)
    {W : Over (C.X i)} (a : (Over.map (C.f i)).obj W ⟶ T) : W ⟶ coefficientCoverTest C T i :=
  Over.homMk (pullback.lift a.left W.hom (Over.w a)) (pullback.lift_snd a.left W.hom (Over.w a))

/-- The lift followed by the inverse-image inclusion is the original map of relative tests. -/
theorem coefficientCoverTestLift_inclusion (C : Scheme.OpenCover.{u} S) (T : Over S) (i : C.I₀)
    {W : Over (C.X i)} (a : (Over.map (C.f i)).obj W ⟶ T) :
    (Over.map (C.f i)).map (coefficientCoverTestLift C T i a) ≫ coefficientCoverTestInclusion C T i = a := by
  apply Over.OverMorphism.ext
  exact pullback.lift_fst a.left W.hom (Over.w a)

/-- The inverse images of the coefficient cover cover every relative test. -/
theorem coefficientCoverTest_covering (C : Scheme.OpenCover.{u} S) (T : Over S) (Q : Sieve T)
    (h : ∀ i, Q (coefficientCoverTestInclusion C T i)) : Q ∈ (Scheme.zariskiTopology.over S) T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.mem_grothendieckTopology_iff.mpr ⟨C.pullback₁ T.hom, ?_⟩
  rintro _ _ ⟨i⟩
  let g := coefficientCoverTestInclusion C T i
  apply (Sieve.overEquiv_symm_iff (Sieve.overEquiv T Q) g).mp
  rw [Equiv.symm_apply_apply]
  exact h i

/-- Membership in any relative subsheaf is local on the inverse-image cover of a test. -/
theorem coefficientCoverTest_predicate (C : Scheme.OpenCover.{u} S) (T : Over S)
    {F : ZariskiSheaf S} (P : SheafPredicate F) {x : F.val.obj (op T)}
    (h : ∀ i, F.val.map (coefficientCoverTestInclusion C T i).op x ∈
      P.carrier.obj (op ((Over.map (C.f i)).obj (coefficientCoverTest C T i)))) :
    x ∈ P.carrier.obj (op T) :=
  (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).mp F.cond)).mp P.isSheaf _ _
    (coefficientCoverTest_covering C T _ h)

/-- Each written Law descends from its restrictions to the actual open cover. -/
theorem holdsLaw_of_openCover (C : Scheme.OpenCover.{u} S)
    (A : SheafStructure sig (Scheme.zariskiTopology.over S)) (law : Law sig)
    (localLaw : ∀ i, (restrictStructure (C.f i) A).holdsLaw law) : A.holdsLaw law := by
  intro U a ha
  let T := U.unop
  apply coefficientCoverTest_predicate C T (A.interpretFormula law.conclusion)
  intro i
  let Ti := coefficientCoverTest C T i
  let g := coefficientCoverTestInclusion C T i
  have hi := (A.interpretFormula law.input).carrier.map g.op ha
  exact (mem_restrictFormula_iff (C.f i) A law.conclusion Ti _).mp
    (localLaw i (op Ti) ((mem_restrictFormula_iff (C.f i) A law.input Ti _).mpr hi))

/-- Two sections of a sheaf coincide if they coincide on the inverse images of an open cover. -/
theorem coefficientCoverTest_sections_ext (C : Scheme.OpenCover.{u} S) (T : Over S)
    (F : ZariskiSheaf S) {x y : F.val.obj (op T)}
    (h : ∀ i, F.val.map (coefficientCoverTestInclusion C T i).op x =
      F.val.map (coefficientCoverTestInclusion C T i).op y) : x = y := by
  let Q := Sieve.ofArrows (fun i => (Over.map (C.f i)).obj (coefficientCoverTest C T i))
    (coefficientCoverTestInclusion C T)
  have covering : Q ∈ (Scheme.zariskiTopology.over S) T :=
    coefficientCoverTest_covering C T Q (Sieve.ofArrows_mk _ _)
  have sheaf := (isSheaf_iff_isSheaf_of_type _ _).mp F.cond
  apply (sheaf Q covering).isSeparatedFor.ext
  intro W f hf
  obtain ⟨V, g, j, hj, rfl⟩ := hf
  obtain ⟨i⟩ := hj
  rw [op_comp, FunctorToTypes.map_comp_apply, FunctorToTypes.map_comp_apply, h i]

/-- Relative sheaf maps are determined by their restrictions to the open cover. -/
theorem coefficientCover_sheafMap_ext (C : Scheme.OpenCover.{u} S) {F G : ZariskiSheaf S}
    {f g : F ⟶ G}
    (h : ∀ i, (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map f =
      (Scheme.zariskiTopology.overMapPullback (Type u) (C.f i)).map g) : f = g := by
  ext T x
  apply coefficientCoverTest_sections_ext C T.unop G
  intro i
  let j := coefficientCoverTestInclusion C T.unop i
  rw [← FunctorToTypes.naturality _ _ f.val j.op, ← FunctorToTypes.naturality _ _ g.val j.op]
  exact congrArg (fun k => k.val.app (op (coefficientCoverTest C T.unop i)) (F.val.map j.op x)) (h i)

/-- A relative sheaf map is an isomorphism if it is bijective on all tests over the open charts. -/
theorem coefficientCover_isIso (C : Scheme.OpenCover.{u} S) {F G : ZariskiSheaf S} (f : F ⟶ G)
    (h : ∀ (i : C.I₀) (V : Over (C.X i)),
      Function.Bijective (f.val.app (op ((Over.map (C.f i)).obj V)))) : IsIso f := by
  apply (Sheaf.isLocallyBijective_iff_isIso f).mp
  refine ⟨(Sheaf.isLocallyInjective_iff_injective f).mpr ?_, ?_⟩
  · intro U x y e
    apply coefficientCoverTest_sections_ext C U.unop F
    intro i
    let g := coefficientCoverTestInclusion C U.unop i
    apply (h i (coefficientCoverTest C U.unop i)).1
    rw [FunctorToTypes.naturality _ _ f.val, FunctorToTypes.naturality _ _ f.val]
    exact congrArg (G.val.map g.op) e
  · constructor
    intro U s
    apply coefficientCoverTest_covering C U
    intro i
    exact (h i (coefficientCoverTest C U i)).2 _

/-- Structure-preserving arrows are determined by their Zariski restrictions. -/
theorem restrictStructureMap_openCover_ext (C : Scheme.OpenCover.{u} S)
    {A B : SheafStructure sig (Scheme.zariskiTopology.over S)} (f g : A ⟶ B)
    (h : ∀ i, restrictStructureMap (C.f i) f = restrictStructureMap (C.f i) g) : f = g := by
  apply SheafStructure.Hom.ext
  funext s
  apply coefficientCover_sheafMap_ext C
  intro i
  exact congrArg (fun k => k.onSort s) (h i)

end SHIGURE.Copying
