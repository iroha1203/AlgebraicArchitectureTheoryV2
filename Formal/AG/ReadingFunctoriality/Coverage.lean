import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.Site.FinitePosetGeometry
import Formal.AG.Cohomology.CechComplex
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# Coverage and cohomology functoriality

This module owns topology refinement, selected-cover refinement, canonical
Čech functoriality, and actual sheaf-cohomology comparison fixed by Part 4
SD3–SD5.
-/

noncomputable section

namespace AAT.AG

universe u v w w'

open CategoryTheory CategoryTheory.Limits

/-! ## Coverage refinement -/

/--
A refinement witness from `J` to `J'`: every `J`-cover contains a selected
`J'`-cover.

Implementation notes: the contained sieve is retained as data so refinement
witnesses compose without making a global choice.
-/
structure CoverageTopologyRefinement
    {C : Type u} [Category.{v} C]
    (J J' : GrothendieckTopology C) where
  /-- Select a `J'`-cover contained in the supplied `J`-cover. -/
  refineCover :
    ∀ (X : C) (R : Sieve X), R ∈ J X →
      {R' : Sieve X // R' ∈ J' X ∧ R' ≤ R}

namespace CoverageTopologyRefinement

variable {C : Type u} [Category.{v} C]

/-- A coverage-refinement witness induces the corresponding topology order. -/
theorem le {J J' : GrothendieckTopology C}
    (r : CoverageTopologyRefinement J J') :
    J ≤ J' := by
  intro X R hR
  exact J'.superset_covering (r.refineCover X R hR).property.2
    (r.refineCover X R hR).property.1

/-- Identity coverage refinement. -/
def refl (J : GrothendieckTopology C) :
    CoverageTopologyRefinement J J where
  refineCover _ R hR := ⟨R, hR, le_rfl⟩

/-- Composite coverage refinement. -/
def comp {J₁ J₂ J₃ : GrothendieckTopology C}
    (f : CoverageTopologyRefinement J₁ J₂)
    (g : CoverageTopologyRefinement J₂ J₃) :
    CoverageTopologyRefinement J₁ J₃ where
  refineCover X R hR := by
    let R₂ := f.refineCover X R hR
    let R₃ := g.refineCover X R₂.1 R₂.property.1
    exact ⟨R₃.1, R₃.property.1, le_trans R₃.property.2 R₂.property.2⟩

end CoverageTopologyRefinement

namespace Site.AATCoverageFamily

/--
A selected-cover refinement: every fine chart factors through a coarse chart
over the common base.

Implementation notes: the triangle records the factorization in the AAT
context preorder rather than only after conversion to the thin category.
-/
structure Refinement
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    (coarse fine : Site.AATCoverageFamily S.requirements S.overlap base) where
  /-- Coarse chart selected by each fine chart. -/
  indexMap : fine.Index → coarse.Index
  /-- Fine-to-coarse chart factor. -/
  factor :
    ∀ i, S.contextPreorder.le (fine.patch i) (coarse.patch (indexMap i))
  /-- The chart factor followed by the coarse inclusion is the fine inclusion. -/
  factor_triangle :
    ∀ i,
      S.contextPreorder.trans (factor i) (coarse.inclusion (indexMap i)) =
        fine.inclusion i

namespace Refinement

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Identity selected-cover refinement. -/
def refl (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Refinement 𝒰 𝒰 where
  indexMap := id
  factor i := S.contextPreorder.refl (𝒰.patch i)
  factor_triangle _ := Subsingleton.elim _ _

/-- Composite selected-cover refinement. -/
def comp
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲) :
    Refinement 𝒰 𝒲 where
  indexMap i := r.indexMap (s.indexMap i)
  factor i := S.contextPreorder.trans (s.factor i) (r.factor (s.indexMap i))
  factor_triangle _ := Subsingleton.elim _ _

/-- A selected-cover refinement reverses inclusion of the generated sieves. -/
theorem presieve_le
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) :
    Sieve.generate 𝒱.presieve ≤ Sieve.generate 𝒰.presieve := by
  rw [Sieve.generate_le_iff]
  change Presieve.ofArrows _ _ ≤ _
  rw [Presieve.ofArrows_le_iff]
  intro i
  refine ⟨_, homOfLE (r.factor i), homOfLE (𝒰.inclusion (r.indexMap i)), ?_, ?_⟩
  · exact Presieve.ofArrows.mk (r.indexMap i)
  · exact Subsingleton.elim _ _

end Refinement

/-- Every selected AAT cover generates a covering sieve in the site topology. -/
theorem mem_topology
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {base : S.category}
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    Sieve.generate 𝒰.presieve ∈ S.topology base :=
  Site.AATGrothendieckTopology.generate_mem 𝒰

end Site.AATCoverageFamily

/-! ## Canonical cover-relative Čech geometry -/

namespace Cohomology

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Canonical iterated overlap of an ordered tuple of selected cover charts. -/
noncomputable def canonicalTupleOverlap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ n, Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n → S.category
  | 0, σ => Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ 0))
  | n + 1, σ =>
      Site.ContextCategoryObject.of S.contextPreorder
        (S.overlap.overlap base.ctx
          (canonicalTupleOverlap 𝒰 n (fun i => σ i.castSucc)).ctx
          (𝒰.patch (σ (Fin.last (n + 1)))))

/-- Degree-zero canonical overlap is the selected singleton chart. -/
@[simp] theorem canonicalTupleOverlap_zero
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (σ : Fin 1 → 𝒰.Index) :
    canonicalTupleOverlap 𝒰 0 σ =
      Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch (σ 0)) :=
  rfl

/-- Successor canonical overlaps are formed by one further selected overlap. -/
@[simp] theorem canonicalTupleOverlap_succ
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 2) → 𝒰.Index) :
    (canonicalTupleOverlap 𝒰 (n + 1) σ).ctx =
      S.overlap.overlap base.ctx
        (canonicalTupleOverlap 𝒰 n (fun i => σ i.castSucc)).ctx
        (𝒰.patch (σ (Fin.last (n + 1)))) :=
  rfl

private theorem canonicalTupleOverlap_le_base
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ (n : Nat) (σ : Fin (n + 1) → 𝒰.Index),
      S.contextPreorder.le (canonicalTupleOverlap 𝒰 n σ).ctx base.ctx
  | 0, σ => 𝒰.inclusion (σ 0)
  | n + 1, σ =>
      S.overlap.overlap_le_base
        (canonicalTupleOverlap_le_base 𝒰 n (fun i => σ i.castSucc))
        (𝒰.inclusion (σ (Fin.last (n + 1))))

private theorem canonicalTupleOverlap_le_patch
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ (n : Nat) (σ : Fin (n + 1) → 𝒰.Index) (k : Fin (n + 1)),
      S.contextPreorder.le (canonicalTupleOverlap 𝒰 n σ).ctx (𝒰.patch (σ k))
  | 0, σ, k => by
      have hk : k = 0 := by
        apply Fin.ext
        exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ k.isLt)
      subst k
      exact S.contextPreorder.refl (𝒰.patch (σ 0))
  | n + 1, σ, k => by
      refine Fin.lastCases ?_ (fun k' => ?_) k
      · exact S.overlap.overlap_le_right
          (canonicalTupleOverlap_le_base 𝒰 n (fun i => σ i.castSucc))
          (𝒰.inclusion (σ (Fin.last (n + 1))))
      · exact S.contextPreorder.trans
          (S.overlap.overlap_le_left
            (canonicalTupleOverlap_le_base 𝒰 n (fun i => σ i.castSucc))
            (𝒰.inclusion (σ (Fin.last (n + 1)))))
          (canonicalTupleOverlap_le_patch 𝒰 n (fun i => σ i.castSucc) k')

private theorem canonicalTupleOverlap_lift
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    ∀ {n : Nat} {X : Site.ArchCtx A} (σ : Fin (n + 1) → 𝒰.Index),
      (∀ k, S.contextPreorder.le X (𝒰.patch (σ k))) →
        S.contextPreorder.le X (canonicalTupleOverlap 𝒰 n σ).ctx
  | 0, _, _, h => h 0
  | n + 1, _, σ, h =>
      S.overlap.overlap_lift
        (canonicalTupleOverlap_le_base 𝒰 n (fun i => σ i.castSucc))
        (𝒰.inclusion (σ (Fin.last (n + 1))))
        (canonicalTupleOverlap_lift 𝒰 (fun i => σ i.castSucc) (fun i => h i.castSucc))
        (h (Fin.last (n + 1)))

/-- Deleting a tuple entry gives the canonical face morphism of overlaps. -/
theorem canonicalTupleOverlap_face_le
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2)) (σ : Fin (n + 2) → 𝒰.Index) :
    S.contextPreorder.le
      (canonicalTupleOverlap 𝒰 (n + 1) σ).ctx
      (canonicalTupleOverlap 𝒰 n
        (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
          (SimplexCategory.δ i) σ)).ctx := by
  apply canonicalTupleOverlap_lift
  intro k
  exact canonicalTupleOverlap_le_patch 𝒰 (n + 1) σ
    ((SimplexCategory.δ i).toOrderHom k)

/--
Canonical overlap morphism induced by an arbitrary simplex-category map.

Implementation notes: the source tuple overlap maps to every chart selected by
the pulled-back tuple, so the iterated-overlap lifting property constructs the
map without accepting additional comparison data.
-/
private noncomputable def canonicalTupleOverlapMap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    {x y : SimplexCategory} (f : x ⟶ y)
    (σ : Fin (y.len + 1) → 𝒰.Index) :
    canonicalTupleOverlap 𝒰 y.len σ ⟶
      canonicalTupleOverlap 𝒰 x.len (fun i ↦ σ (f.toOrderHom i)) := by
  apply homOfLE
  apply canonicalTupleOverlap_lift
  intro k
  exact canonicalTupleOverlap_le_patch 𝒰 y.len σ (f.toOrderHom k)

/-- Canonical cover-relative Čech cover generated by a selected AAT cover. -/
noncomputable def canonicalCoverRelative
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    CoverRelativeCechCover S where
  base := base
  Index := 𝒰.Index
  chart i := Site.ContextCategoryObject.of S.contextPreorder (𝒰.patch i)
  inclusion i := homOfLE (𝒰.inclusion i)
  simplex n := Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n
  overlap n σ := canonicalTupleOverlap 𝒰 n σ
  face _ i σ :=
    Site.FinitePosetCechCanonicalTupleSimplex.simplexMap (SimplexCategory.δ i) σ
  faceRestriction n i σ := homOfLE (canonicalTupleOverlap_face_le 𝒰 n i σ)

/-- The canonical cover-relative cover retains its selected base. -/
@[simp] theorem canonicalCoverRelative_base
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) :
    (canonicalCoverRelative 𝒰).base = base :=
  rfl

/-- Canonical simplices are ordered tuples of selected chart indices. -/
@[simp] theorem canonicalCoverRelative_simplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base) (n : Nat) :
    (canonicalCoverRelative 𝒰).simplex n =
      Site.FinitePosetCechCanonicalTupleSimplex 𝒰.Index n :=
  rfl

/-- Canonical cover-relative overlaps are the generated tuple overlaps. -/
@[simp] theorem canonicalCoverRelative_overlap
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : Fin (n + 1) → 𝒰.Index) :
    (canonicalCoverRelative 𝒰).overlap n σ = canonicalTupleOverlap 𝒰 n σ :=
  rfl

/-- Canonical cover-relative faces are standard simplex-category cofaces. -/
@[simp] theorem canonicalCoverRelative_face
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (i : Fin (n + 2)) (σ : Fin (n + 2) → 𝒰.Index) :
    (canonicalCoverRelative 𝒰).face n i σ =
      Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
        (SimplexCategory.δ i) σ :=
  rfl

/-- Canonical faces satisfy the standard triangular two-face identity. -/
theorem canonicalCoverRelative_twoFace
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : (canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (canonicalCoverRelative 𝒰).face n i
        ((canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (canonicalCoverRelative 𝒰).face n j
        ((canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ) :=
  Site.FinitePosetCechCanonicalTupleSimplex.twoFace_simplex_eq n σ i j hij

/-- Canonical face restrictions satisfy the corresponding two-face identity. -/
theorem canonicalCoverRelative_faceRestriction_twoFace
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (n : Nat) (σ : (canonicalCoverRelative 𝒰).simplex (n + 2))
    (i j : Fin (n + 2)) (hij : i ≤ j) :
    (canonicalCoverRelative 𝒰).faceRestriction (n + 1) j.succ σ ≫
        (canonicalCoverRelative 𝒰).faceRestriction n i
          ((canonicalCoverRelative 𝒰).face (n + 1) j.succ σ) =
      (canonicalCoverRelative 𝒰).faceRestriction (n + 1) i.castSucc σ ≫
        (canonicalCoverRelative 𝒰).faceRestriction n j
          ((canonicalCoverRelative 𝒰).face (n + 1) i.castSucc σ) ≫
        eqToHom (congrArg ((canonicalCoverRelative 𝒰).overlap n)
          (canonicalCoverRelative_twoFace 𝒰 n σ i j hij).symm) := by
  exact Subsingleton.elim _ _

end Cohomology

namespace Site.AATCoverageFamily.Refinement

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Apply a selected-cover refinement pointwise to canonical simplices. -/
def simplexMap
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (n : Nat) :
    (Cohomology.canonicalCoverRelative 𝒱).simplex n →
      (Cohomology.canonicalCoverRelative 𝒰).simplex n :=
  fun σ i => r.indexMap (σ i)

/-- Refinement-induced morphism from a fine tuple overlap to its coarse image. -/
noncomputable def overlapMap
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (n : Nat)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex n) :
    (Cohomology.canonicalCoverRelative 𝒱).overlap n σ ⟶
      (Cohomology.canonicalCoverRelative 𝒰).overlap n (r.simplexMap n σ) := by
  apply homOfLE
  apply Cohomology.canonicalTupleOverlap_lift
  intro k
  exact S.contextPreorder.trans
    (Cohomology.canonicalTupleOverlap_le_patch 𝒱 n σ k)
    (r.factor (σ k))

/-- Refinement-induced overlap maps commute with canonical face restrictions. -/
theorem overlapMap_face_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱)
    (n : Nat) (i : Fin (n + 2))
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex (n + 1)) :
    (Cohomology.canonicalCoverRelative 𝒱).faceRestriction n i σ ≫
        r.overlapMap n ((Cohomology.canonicalCoverRelative 𝒱).face n i σ) =
      r.overlapMap (n + 1) σ ≫
        (Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i
          (r.simplexMap (n + 1) σ) := by
  exact Subsingleton.elim _ _

end Site.AATCoverageFamily.Refinement

/-! ## Canonical additive Čech functoriality -/

namespace Cohomology

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- A restriction map of the obstruction sheaf as an additive homomorphism. -/
def ObstructionSheaf.mapAddMonoidHom
    (Ob : ObstructionSheaf S) {X Y : S.category} (f : X ⟶ Y) :
    Ob.carrier.toPresheaf.obj (Opposite.op Y) →+
      Ob.carrier.toPresheaf.obj (Opposite.op X) where
  toFun := Ob.carrier.toPresheaf.map f.op
  map_zero' := Ob.map_zero f
  map_add' := Ob.map_add f

/-- The obstruction coefficient bundled as a small additive presheaf. -/
private def obstructionSmallAddCommGrpPresheaf
    (Ob : ObstructionSheaf S) :
    S.categoryᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj X := by
    letI := Ob.addCommGroup X.unop
    exact AddCommGrpCat.of
      (Ob.carrier.toPresheaf.obj X)
  map {X Y} f := by
    letI := Ob.addCommGroup X.unop
    letI := Ob.addCommGroup Y.unop
    exact AddCommGrpCat.ofHom
      (Ob.mapAddMonoidHom f.unop)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro x
    exact FunctorToTypes.map_id_apply
      (F := Ob.carrier.toPresheaf) x
  map_comp {X Y Z} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact FunctorToTypes.map_comp_apply
      (F := Ob.carrier.toPresheaf) f g x

/--
The obstruction coefficient presheaf in the universe required by Mathlib's
local sheaf-cohomology API.
-/
private noncomputable def obstructionAddCommGrpPresheaf
    (Ob : ObstructionSheaf S) :
    S.categoryᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  obstructionSmallAddCommGrpPresheaf Ob ⋙
    AddCommGrpCat.uliftFunctor.{u + 1, u}

/-- Bundle an obstruction coefficient as an actual additive-group-valued sheaf. -/
noncomputable def ObstructionSheaf.toAddCommGrpSheaf
    (Ob : ObstructionSheaf S) :
    Sheaf S.topology AddCommGrpCat.{u + 1} where
  val := obstructionAddCommGrpPresheaf Ob
  cond := by
    refine (Presheaf.isSheaf_iff_isSheaf_forget
      (J := S.topology)
      (P' := obstructionAddCommGrpPresheaf Ob)
      (forget AddCommGrpCat.{u + 1})).2 ?_
    refine (isSheaf_iff_isSheaf_of_type S.topology
      (obstructionAddCommGrpPresheaf Ob ⋙
        forget AddCommGrpCat.{u + 1})).2 ?_
    exact Presieve.isSheaf_comp_uliftFunctor S.topology
      Ob.carrier.presieve_isSheaf

/-- The standard Ext universe for additive-group-valued sheaves. -/
theorem standardAddCommGrpSheafHasExt
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{w}] :
    HasExt.{max (max u v) (w + 1)}
      (Sheaf J AddCommGrpCat.{w}) :=
  HasExt.standard _

/-- The standard Ext instance for additive coefficients on an AAT site. -/
noncomputable instance aatSheafHasExt
    [HasSheafify S.topology AddCommGrpCat.{u + 1}] :
    HasExt.{u + 2} (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
  standardAddCommGrpSheafHasExt

/-- Sum the coefficients of a free abelian group indexed by maps to a terminal object. -/
private def terminalFreeForward
    {C : Type u} [Category.{v} C]
    {X : C} (Y : C) :
    FreeAbelianGroup (Y ⟶ X) →+ ULift.{v} ℤ :=
  FreeAbelianGroup.lift (fun _ => ULift.up 1)

/-- Send an integer to the corresponding multiple of the unique terminal map. -/
private def terminalFreeInverse
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) (Y : C) :
    ULift.{v} ℤ →+ FreeAbelianGroup (Y ⟶ X) where
  toFun z := z.down • FreeAbelianGroup.of (hX.from Y)
  map_zero' := by simp
  map_add' x y := by
    change (x.down + y.down) • FreeAbelianGroup.of (hX.from Y) = _
    rw [add_smul]

/-- A free abelian group on maps to a terminal object is canonically `ULift ℤ`. -/
private noncomputable def terminalFreeAddEquiv
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) (Y : C) :
    FreeAbelianGroup (Y ⟶ X) ≃+ ULift.{v} ℤ where
  toFun := terminalFreeForward Y
  invFun := terminalFreeInverse hX Y
  map_add' := (terminalFreeForward Y).map_add
  right_inv z := by
    rcases z with ⟨z⟩
    apply ULift.ext
    simp [terminalFreeForward, terminalFreeInverse]
  left_inv z := by
    let lhs : FreeAbelianGroup (Y ⟶ X) →+ FreeAbelianGroup (Y ⟶ X) :=
      (terminalFreeInverse hX Y).comp (terminalFreeForward Y)
    have hlhs : lhs = AddMonoidHom.id _ := by
      apply FreeAbelianGroup.lift_ext
      intro f
      change FreeAbelianGroup.of (hX.from Y) = FreeAbelianGroup.of f
      congr
      exact hX.hom_ext _ _
    exact DFunLike.congr_fun hlhs z

/-- The terminal free-representable presheaf is the constant integer presheaf. -/
private noncomputable def terminalFreePresheafIso
    {C : Type u} [Category.{v} C]
    {X : C} (hX : IsTerminal X) :
    yoneda.obj X ⋙ AddCommGrpCat.free ≅
      (Functor.const Cᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  NatIso.ofComponents
    (fun Y => (terminalFreeAddEquiv hX Y.unop).toAddCommGrpIso)
    (fun {Y Z} f => by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro g
      change terminalFreeForward Z.unop
          (FreeAbelianGroup.map (fun k => f.unop ≫ k)
            (FreeAbelianGroup.of g)) =
        terminalFreeForward Y.unop (FreeAbelianGroup.of g)
      rw [FreeAbelianGroup.map_of_apply]
      simp [terminalFreeForward])

/--
The source object defining local cohomology at a terminal object is the
constant integer sheaf defining global cohomology.
-/
private noncomputable def terminalCohomologySourceIso
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{v}]
    (X : C) (hX : IsTerminal X) :
    (presheafToSheaf J AddCommGrpCat.{v}).obj
        (yoneda.obj X ⋙ AddCommGrpCat.free) ≅
      (constantSheaf J AddCommGrpCat.{v}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (presheafToSheaf J AddCommGrpCat.{v}).mapIso
    (terminalFreePresheafIso hX)

/-- Local cohomology at a terminal object is canonically global cohomology. -/
noncomputable def terminalHComparison
    {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C}
    (F : Sheaf J AddCommGrpCat.{v})
    [HasSheafify J AddCommGrpCat.{v}]
    [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]
    (X : C) (hX : IsTerminal X) (n : Nat) :
    F.H' n X ≃+ F.H n := by
  let e := terminalCohomologySourceIso (J := J) X hX
  exact AddEquiv.ofBijective
    ((Abelian.Ext.mk₀ e.inv).precomp F (zero_add n))
    ⟨by
      intro a b hab
      have h := congrArg
        ((Abelian.Ext.mk₀ e.hom).precomp F (zero_add n)) hab
      change
        (Abelian.Ext.mk₀ e.hom).comp
            ((Abelian.Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n) =
          (Abelian.Ext.mk₀ e.hom).comp
            ((Abelian.Ext.mk₀ e.inv).comp b (zero_add n)) (zero_add n)
        at h
      simpa only [Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id,
        Abelian.Ext.mk₀_id_comp] using h,
     by
      intro y
      refine ⟨(Abelian.Ext.mk₀ e.hom).precomp F (zero_add n) y, ?_⟩
      change
        (Abelian.Ext.mk₀ e.inv).comp
            ((Abelian.Ext.mk₀ e.hom).comp y (zero_add n)) (zero_add n) = y
      rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id,
        Abelian.Ext.mk₀_id_comp]⟩

/-- The cosimplicial additive group of canonical cover-relative Čech cochains. -/
private noncomputable def canonicalCechCosimplicialObject
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) : CosimplicialObject AddCommGrpCat.{u} where
  obj x := by
    letI : ∀ σ : (canonicalCoverRelative 𝒰).simplex x.len,
        AddCommGroup
          (Ob.carrier.toPresheaf.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap x.len σ))) :=
      fun σ ↦ Ob.addCommGroup ((canonicalCoverRelative 𝒰).overlap x.len σ)
    letI : AddCommGroup
        (CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob x.len) :=
      Pi.addCommGroup
    exact AddCommGrpCat.of
      (CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob x.len)
  map {x y} f := by
    letI : ∀ σ : (canonicalCoverRelative 𝒰).simplex x.len,
        AddCommGroup
          (Ob.carrier.toPresheaf.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap x.len σ))) :=
      fun σ ↦ Ob.addCommGroup ((canonicalCoverRelative 𝒰).overlap x.len σ)
    letI : AddCommGroup
        (CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob x.len) :=
      Pi.addCommGroup
    letI : ∀ σ : (canonicalCoverRelative 𝒰).simplex y.len,
        AddCommGroup
          (Ob.carrier.toPresheaf.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap y.len σ))) :=
      fun σ ↦ Ob.addCommGroup ((canonicalCoverRelative 𝒰).overlap y.len σ)
    letI : AddCommGroup
        (CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob y.len) :=
      Pi.addCommGroup
    exact AddCommGrpCat.ofHom
      { toFun := fun c σ ↦
          Ob.mapAddMonoidHom (canonicalTupleOverlapMap 𝒰 f σ)
            (c (fun i ↦ σ (f.toOrderHom i)))
        map_zero' := by
          funext σ
          exact map_zero (Ob.mapAddMonoidHom (canonicalTupleOverlapMap 𝒰 f σ))
        map_add' := by
          intro c d
          funext σ
          exact map_add (Ob.mapAddMonoidHom (canonicalTupleOverlapMap 𝒰 f σ)) _ _ }
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro c
    funext σ
    change Ob.carrier.toPresheaf.map
      (canonicalTupleOverlapMap 𝒰 (CategoryStruct.id x) σ).op (c σ) = c σ
    have hf : canonicalTupleOverlapMap 𝒰 (CategoryStruct.id x) σ = 𝟙 _ :=
      Subsingleton.elim _ _
    rw [hf]
    exact FunctorToTypes.map_id_apply (F := Ob.carrier.toPresheaf) (c σ)
  map_comp {x y z} f g := by
    apply ConcreteCategory.hom_ext
    intro c
    funext σ
    change
      Ob.carrier.toPresheaf.map (canonicalTupleOverlapMap 𝒰 (f ≫ g) σ).op
          (c (fun i ↦ σ ((f ≫ g).toOrderHom i))) =
        Ob.carrier.toPresheaf.map (canonicalTupleOverlapMap 𝒰 g σ).op
          (Ob.carrier.toPresheaf.map
            (canonicalTupleOverlapMap 𝒰 f (fun i ↦ σ (g.toOrderHom i))).op
            (c (fun i ↦ σ (g.toOrderHom (f.toOrderHom i)))))
    rw [← FunctorToTypes.map_comp_apply]
    congr

private theorem canonicalCechCosimplicialObject_delta_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : Nat) (i : Fin (n + 2))
    (c : CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob n)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1)) :
    ((canonicalCechCosimplicialObject 𝒰 Ob).δ i).hom c σ =
      Ob.mapAddMonoidHom
        ((canonicalCoverRelative 𝒰).faceRestriction n i σ)
        (c ((canonicalCoverRelative 𝒰).face n i σ)) := by
  change Ob.carrier.toPresheaf.map
      (canonicalTupleOverlapMap 𝒰 (SimplexCategory.δ i) σ).op
      (c (fun k ↦ σ ((SimplexCategory.δ i).toOrderHom k))) =
    Ob.carrier.toPresheaf.map
      ((canonicalCoverRelative 𝒰).faceRestriction n i σ).op
      (c ((canonicalCoverRelative 𝒰).face n i σ))
  congr 2

/-- Canonical Čech complex generated by the selected cover's restriction maps. -/
noncomputable def canonicalCechComplex
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) :
    CoverRelativeCechComplex (canonicalCoverRelative 𝒰) Ob where
  cochainAddCommGroup n := by
    letI : ∀ σ : (canonicalCoverRelative 𝒰).simplex n,
        AddCommGroup
          (Ob.carrier.toPresheaf.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap n σ))) :=
      fun σ ↦ Ob.addCommGroup ((canonicalCoverRelative 𝒰).overlap n σ)
    exact Pi.addCommGroup
  alternatingFaceCombination n terms := fun σ ↦
    ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) • terms σ i
  differential n :=
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD
      (canonicalCechCosimplicialObject 𝒰 Ob) n).hom
  differential_eq_alternatingFaceCombination n c := by
    letI : ∀ τ : (canonicalCoverRelative 𝒰).simplex n,
        AddCommGroup
          (Ob.carrier.toPresheaf.obj
            (Opposite.op ((canonicalCoverRelative 𝒰).overlap n τ))) :=
      fun τ ↦ Ob.addCommGroup ((canonicalCoverRelative 𝒰).overlap n τ)
    letI : AddCommGroup
        (CoverRelativeCechCochain (canonicalCoverRelative 𝒰) Ob n) :=
      Pi.addCommGroup
    funext σ
    simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD]
    change (AddCommGrpCat.homAddEquiv
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        (canonicalCechCosimplicialObject 𝒰 Ob).δ i)) c σ = _
    rw [map_sum]
    change ((AddMonoidHom.eval c)
      (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        AddCommGrpCat.homAddEquiv
          ((canonicalCechCosimplicialObject 𝒰 Ob).δ i))) σ = _
    rw [map_sum, Finset.sum_apply]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro i _hi
    change ((-1 : ℤ) ^ i.1) •
      ((canonicalCechCosimplicialObject 𝒰 Ob).δ i).hom c σ = _
    rw [canonicalCechCosimplicialObject_delta_apply]
    rfl
  differential_comp n c := by
    have h := ConcreteCategory.congr_hom
      (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared
        (canonicalCechCosimplicialObject 𝒰 Ob) n) c
    exact h

/-- The canonical differential is the explicit alternating restriction sum. -/
theorem canonicalCechComplex_d_apply
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (canonicalCoverRelative 𝒰).simplex (n + 1)) :
    (canonicalCechComplex 𝒰 Ob).d n c σ =
      ∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
        Ob.mapAddMonoidHom
          ((canonicalCoverRelative 𝒰).faceRestriction n i σ)
          (c ((canonicalCoverRelative 𝒰).face n i σ)) := by
  simp only [CoverRelativeCechComplex.d, canonicalCechComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.objD]
  change (AddCommGrpCat.homAddEquiv
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
      (canonicalCechCosimplicialObject 𝒰 Ob).δ i)) c σ = _
  rw [map_sum]
  change ((AddMonoidHom.eval c)
    (∑ i : Fin (n + 2), ((-1 : ℤ) ^ i.1) •
      AddCommGrpCat.homAddEquiv
        ((canonicalCechCosimplicialObject 𝒰 Ob).δ i))) σ = _
  rw [map_sum, Finset.sum_apply]
  simp only [map_zsmul]
  apply Finset.sum_congr rfl
  intro i _hi
  change ((-1 : ℤ) ^ i.1) •
    ((canonicalCechCosimplicialObject 𝒰 Ob).δ i).hom c σ = _
  rw [canonicalCechCosimplicialObject_delta_apply]

/-- The canonical alternating differential squares to zero. -/
theorem canonicalCechComplex_d_comp_d
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : ObstructionSheaf S) (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).AdditiveCochain n) :
    (canonicalCechComplex 𝒰 Ob).d (n + 1)
        ((canonicalCechComplex 𝒰 Ob).d n c) =
      (0 : (canonicalCechComplex 𝒰 Ob).AdditiveCochain (n + 2)) :=
  (canonicalCechComplex 𝒰 Ob).differential_comp n c

namespace CoverRelativeCechComplex

variable {𝒰 𝒱 𝒲 : CoverRelativeCechCover S}
variable {Ob : ObstructionSheaf S}

/-- Additive Čech cohomology: the zero kernel and positive-degree quotients. -/
def AdditiveCechHn (K : CoverRelativeCechComplex 𝒰 Ob) : Nat → Type u
  | 0 => K.CechCocycleSubgroup 0
  | n + 1 =>
      K.CechCocycleSubgroup (n + 1) ⧸ K.CechCoboundarySubgroupSucc n

/-- Every additive Čech cohomology degree carries its quotient group structure. -/
instance additiveCechHnAddCommGroup
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    AddCommGroup (K.AdditiveCechHn n) := by
  cases n with
  | zero =>
      change AddCommGroup (K.CechCocycleSubgroup 0)
      infer_instance
  | succ n =>
      change AddCommGroup
        (K.CechCocycleSubgroup (n + 1) ⧸ K.CechCoboundarySubgroupSucc n)
      infer_instance

/-- Send a cocycle to its additive Čech cohomology class. -/
def additiveCohomologyClass
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    K.CechCocycle n → K.AdditiveCechHn n := by
  cases n with
  | zero =>
      intro c
      exact ⟨c.1, c.2⟩
  | succ n =>
      intro c
      exact QuotientAddGroup.mk ⟨c.1, c.2⟩

/-- A cochain map between cover-relative Čech complexes. -/
structure Hom
    (K : CoverRelativeCechComplex 𝒰 Ob)
    (L : CoverRelativeCechComplex 𝒱 Ob) where
  /-- The additive map in every cochain degree. -/
  app : ∀ n, K.AdditiveCochain n →+ L.AdditiveCochain n
  /-- The degreewise maps commute with the selected differentials. -/
  commutes : ∀ n c, app (n + 1) (K.d n c) = L.d n (app n c)

namespace Hom

/-- Cochain maps are equal when all of their degreewise additive maps agree. -/
@[ext] theorem ext
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    {f g : Hom K L} (h : f.app = g.app) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- A cochain map sends cocycles to cocycles. -/
def mapCocycle
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : Nat) :
    K.CechCocycle n → L.CechCocycle n := fun c ↦
  ⟨f.app n c.1, by
    rw [← f.commutes, c.2]
    exact map_zero (f.app (n + 1))⟩

/-- Additive version of `mapCocycle` on the cocycle subgroups. -/
private def mapCocycleAddMonoidHom
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : Nat) :
    K.CechCocycleSubgroup n →+ L.CechCocycleSubgroup n where
  toFun c := ⟨f.app n c.1, by
    letI := L.cochainAddCommGroup (n + 1)
    change L.d n (f.app n c.1) = 0
    rw [← f.commutes, c.2]
    exact map_zero (f.app (n + 1))⟩
  map_zero' := by ext; exact map_zero (f.app n)
  map_add' x y := by ext; exact map_add (f.app n) x.1 y.1

/-- Identity cochain map. -/
def id (K : CoverRelativeCechComplex 𝒰 Ob) : Hom K K where
  app _ := AddMonoidHom.id _
  commutes _ _ := rfl

/-- Composite of cochain maps, written in forward application order. -/
def comp
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    {M : CoverRelativeCechComplex 𝒲 Ob}
    (f : Hom K L) (g : Hom L M) : Hom K M where
  app n := (g.app n).comp (f.app n)
  commutes n c := by
    rw [AddMonoidHom.comp_apply, f.commutes, g.commutes]
    rfl

/-- The arbitrary-degree additive cohomology map induced by a cochain map. -/
def mapAdditiveCechHn
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    (f : Hom K L) (n : Nat) :
    K.AdditiveCechHn n →+ L.AdditiveCechHn n := by
  cases n with
  | zero => exact mapCocycleAddMonoidHom f 0
  | succ n =>
      apply QuotientAddGroup.map
        (K.CechCoboundarySubgroupSucc n)
        (L.CechCoboundarySubgroupSucc n)
        (mapCocycleAddMonoidHom f (n + 1))
      intro z hz
      change ∃ b : K.Cn n, z = K.coboundaryCocycle n b at hz
      rcases hz with ⟨b, rfl⟩
      change ∃ b' : L.Cn n,
        mapCocycleAddMonoidHom f (n + 1) (K.coboundaryCocycle n b) =
          L.coboundaryCocycle n b'
      refine ⟨f.app n b, ?_⟩
      ext
      exact f.commutes n b

/-- The identity cochain map induces the identity in every degree. -/
@[simp] theorem mapAdditiveCechHn_id
    (K : CoverRelativeCechComplex 𝒰 Ob) (n : Nat) :
    (id K).mapAdditiveCechHn n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  cases n with
  | zero => rfl
  | succ n =>
      change K.CechCocycleSubgroup (n + 1) ⧸
        K.CechCoboundarySubgroupSucc n at x
      induction x using QuotientAddGroup.induction_on with
      | _ z => rfl

/-- Cohomology maps preserve composition in every degree. -/
@[simp] theorem mapAdditiveCechHn_comp
    {K : CoverRelativeCechComplex 𝒰 Ob}
    {L : CoverRelativeCechComplex 𝒱 Ob}
    {M : CoverRelativeCechComplex 𝒲 Ob}
    (f : Hom K L) (g : Hom L M) (n : Nat) :
    (f.comp g).mapAdditiveCechHn n =
      (g.mapAdditiveCechHn n).comp (f.mapAdditiveCechHn n) := by
  apply AddMonoidHom.ext
  intro x
  cases n with
  | zero => rfl
  | succ n =>
      change K.CechCocycleSubgroup (n + 1) ⧸
        K.CechCoboundarySubgroupSucc n at x
      induction x using QuotientAddGroup.induction_on with
      | _ z => rfl

end Hom
end CoverRelativeCechComplex

end Cohomology

namespace Site.AATCoverageFamily.Refinement

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- The one-way canonical Čech cochain map induced by a cover refinement. -/
noncomputable def canonicalCechHom
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (Ob : Cohomology.ObstructionSheaf S) :
    Cohomology.CoverRelativeCechComplex.Hom
      (Cohomology.canonicalCechComplex 𝒰 Ob)
      (Cohomology.canonicalCechComplex 𝒱 Ob) where
  app n :=
    { toFun := fun c σ ↦
        Ob.mapAddMonoidHom (r.overlapMap n σ) (c (r.simplexMap n σ))
      map_zero' := by
        funext σ
        exact map_zero (Ob.mapAddMonoidHom (r.overlapMap n σ))
      map_add' := by
        intro c d
        funext σ
        exact map_add (Ob.mapAddMonoidHom (r.overlapMap n σ)) _ _ }
  commutes n c := by
    funext σ
    change Ob.mapAddMonoidHom (r.overlapMap (n + 1) σ)
        ((Cohomology.canonicalCechComplex 𝒰 Ob).d n c
          (r.simplexMap (n + 1) σ)) =
      (Cohomology.canonicalCechComplex 𝒱 Ob).d n
        (fun τ ↦ Ob.mapAddMonoidHom (r.overlapMap n τ)
          (c (r.simplexMap n τ))) σ
    rw [Cohomology.canonicalCechComplex_d_apply,
      Cohomology.canonicalCechComplex_d_apply, map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_zsmul]
    congr 1
    change Ob.carrier.toPresheaf.map (r.overlapMap (n + 1) σ).op
        (Ob.carrier.toPresheaf.map
          ((Cohomology.canonicalCoverRelative 𝒰).faceRestriction n i
            (r.simplexMap (n + 1) σ)).op
          (c ((Cohomology.canonicalCoverRelative 𝒰).face n i
            (r.simplexMap (n + 1) σ)))) =
      Ob.carrier.toPresheaf.map
          ((Cohomology.canonicalCoverRelative 𝒱).faceRestriction n i σ).op
        (Ob.carrier.toPresheaf.map
          (r.overlapMap n
            ((Cohomology.canonicalCoverRelative 𝒱).face n i σ)).op
          (c (r.simplexMap n
            ((Cohomology.canonicalCoverRelative 𝒱).face n i σ))))
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply]
    congr

/-- Pointwise formula for the refinement-induced cochain map. -/
theorem canonicalCechHom_app_apply
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (Ob : Cohomology.ObstructionSheaf S)
    (n : Nat)
    (c : (Cohomology.canonicalCechComplex 𝒰 Ob).AdditiveCochain n)
    (σ : (Cohomology.canonicalCoverRelative 𝒱).simplex n) :
    (r.canonicalCechHom Ob).app n c σ =
      Ob.mapAddMonoidHom (r.overlapMap n σ)
        (c (r.simplexMap n σ)) :=
  rfl

/-- Identity refinements induce the identity cochain map. -/
@[simp] theorem canonicalCechHom_refl
    (𝒰 : Site.AATCoverageFamily S.requirements S.overlap base)
    (Ob : Cohomology.ObstructionSheaf S) :
    (refl 𝒰).canonicalCechHom Ob =
      Cohomology.CoverRelativeCechComplex.Hom.id
        (Cohomology.canonicalCechComplex 𝒰 Ob) := by
  apply Cohomology.CoverRelativeCechComplex.Hom.ext
  funext n
  apply AddMonoidHom.ext
  intro c
  funext σ
  change Ob.carrier.toPresheaf.map ((refl 𝒰).overlapMap n σ).op (c σ) = c σ
  have hf : (refl 𝒰).overlapMap n σ = 𝟙 _ := Subsingleton.elim _ _
  rw [hf]
  exact FunctorToTypes.map_id_apply (F := Ob.carrier.toPresheaf) (c σ)

/-- Composite refinements induce the composite canonical cochain map. -/
@[simp] theorem canonicalCechHom_comp
    {𝒰 𝒱 𝒲 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Refinement 𝒰 𝒱) (s : Refinement 𝒱 𝒲)
    (Ob : Cohomology.ObstructionSheaf S) :
    (r.comp s).canonicalCechHom Ob =
      (r.canonicalCechHom Ob).comp (s.canonicalCechHom Ob) := by
  apply Cohomology.CoverRelativeCechComplex.Hom.ext
  funext n
  apply AddMonoidHom.ext
  intro c
  funext σ
  change Ob.carrier.toPresheaf.map ((r.comp s).overlapMap n σ).op
      (c (r.simplexMap n (s.simplexMap n σ))) =
    Ob.carrier.toPresheaf.map (s.overlapMap n σ).op
      (Ob.carrier.toPresheaf.map (r.overlapMap n (s.simplexMap n σ)).op
        (c (r.simplexMap n (s.simplexMap n σ))))
  rw [← FunctorToTypes.map_comp_apply]
  congr

end Site.AATCoverageFamily.Refinement

namespace Cohomology

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {base : S.category}

/-- Refinement maps carry each cocycle class to the class of its image. -/
theorem obstructionClass_naturality
    {𝒰 𝒱 : Site.AATCoverageFamily S.requirements S.overlap base}
    (r : Site.AATCoverageFamily.Refinement 𝒰 𝒱)
    (Ob : ObstructionSheaf S) (n : Nat)
    (c : (canonicalCechComplex 𝒰 Ob).CechCocycle n) :
    (r.canonicalCechHom Ob).mapAdditiveCechHn n
        ((canonicalCechComplex 𝒰 Ob).additiveCohomologyClass n c) =
      (canonicalCechComplex 𝒱 Ob).additiveCohomologyClass n
        ((r.canonicalCechHom Ob).mapCocycle n c) := by
  cases n with
  | zero => rfl
  | succ n => rfl

end Cohomology

/-! ## Sheaves for a change of coverage topology -/

/--
An additive coefficient presheaf which is a sheaf for both selected
topologies.

Implementation notes: this structure bundles the coefficient presheaf itself,
not a certificate about separately supplied data. A presheaf which fails either
sheaf condition is represented by the absence of a constructor rather than by
a negative inhabitant. The two proof fields are exactly the data needed to form
the coarse and fine Mathlib `Sheaf` objects; no comparison map is stored.
-/
structure CommonCoefficientSheaf
    {C : Type u} [Category.{v} C]
    (J J' : GrothendieckTopology C) where
  /-- The common underlying additive presheaf. -/
  presheaf : Cᵒᵖ ⥤ AddCommGrpCat.{w}
  /-- The sheaf condition for the coarse topology. -/
  isSheaf_coarse : Presheaf.IsSheaf J presheaf
  /-- The sheaf condition for the fine topology. -/
  isSheaf_fine : Presheaf.IsSheaf J' presheaf

namespace CommonCoefficientSheaf

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

/-- The common coefficient regarded as a sheaf for the coarse topology. -/
def coarse (F : CommonCoefficientSheaf J J') :
    Sheaf J AddCommGrpCat.{w} :=
  ⟨F.presheaf, F.isSheaf_coarse⟩

/-- The common coefficient regarded as a sheaf for the fine topology. -/
def fine (F : CommonCoefficientSheaf J J') :
    Sheaf J' AddCommGrpCat.{w} :=
  ⟨F.presheaf, F.isSheaf_fine⟩

/-- With the same topology, the two bundled sheaves are canonically isomorphic. -/
noncomputable def sameTopologyIso (F : CommonCoefficientSheaf J J) :
    F.coarse ≅ F.fine :=
  Iso.refl _

/-- The cohomology map induced by the canonical same-topology coefficient iso. -/
noncomputable def sameTopologyHMap
    (F : CommonCoefficientSheaf J J)
    [HasSheafify J AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  (Abelian.Ext.mk₀ F.sameTopologyIso.hom).postcomp
    ((constantSheaf J AddCommGrpCat.{w}).obj
      (AddCommGrpCat.of (ULift ℤ))) (add_zero n)

end CommonCoefficientSheaf

namespace CoverageTopologyRefinement

variable {C : Type u} [Category.{v} C]
variable {J J' : GrothendieckTopology C}

set_option linter.unusedVariables false in
/--
Sheafify a coarse sheaf for the finer topology.

Implementation notes: the left-adjoint functor depends only on `J` and `J'`.
The receiver `r` intentionally records the selected topology refinement for the
paired right adjoint and the adjunction below, where `r.le` is proof-used. Keeping
the receiver here gives those constructions one coherent API; it is not used to
manufacture a preservation premise or a comparison map.
-/
noncomputable def fineSheafification
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    Sheaf J AddCommGrpCat.{w} ⥤ Sheaf J' AddCommGrpCat.{w} :=
  sheafToPresheaf J AddCommGrpCat.{w} ⋙
    presheafToSheaf J' AddCommGrpCat.{w}

/-- A fine sheaf is also a sheaf for the coarser topology. -/
theorem isSheaf_coarse
    (r : CoverageTopologyRefinement J J')
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w})
    (hP : Presheaf.IsSheaf J' P) :
    Presheaf.IsSheaf J P :=
  fun E =>
    Presieve.isSheaf_of_le
      (P ⋙ coyoneda.obj (Opposite.op E)) r.le (hP E)

/-- Restrict a fine sheaf to the coarser topology. -/
def coarseRestriction
    (r : CoverageTopologyRefinement J J') :
    Sheaf J' AddCommGrpCat.{w} ⥤ Sheaf J AddCommGrpCat.{w} where
  obj F := ⟨F.val, r.isSheaf_coarse F.val F.cond⟩
  map η := ⟨η.val⟩

/-- Fine sheafification is left adjoint to coarse restriction. -/
noncomputable def fineSheafificationAdjunction
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification ⊣ r.coarseRestriction :=
  (sheafificationAdjunction J' AddCommGrpCat.{w}).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{w})
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Fine sheafification is additive. -/
noncomputable instance fineSheafification_additive
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.Additive := by
  change (sheafToPresheaf J AddCommGrpCat.{w} ⋙
    presheafToSheaf J' AddCommGrpCat.{w}).Additive
  letI : (sheafToPresheaf J AddCommGrpCat.{w}).Additive :=
    { map_add := by intros; rfl }
  infer_instance

/-- Fine sheafification preserves finite limits. -/
noncomputable instance fineSheafification_preservesFiniteLimits
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    Limits.PreservesFiniteLimits r.fineSheafification := by
  exact Limits.comp_preservesFiniteLimits _ _

/-- Fine sheafification preserves finite colimits. -/
noncomputable instance fineSheafification_preservesFiniteColimits
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    Limits.PreservesFiniteColimits r.fineSheafification := by
  constructor
  intro K _ _
  exact (Adjunction.leftAdjoint_preservesColimits.{0, 0}
    r.fineSheafificationAdjunction).preservesColimitsOfShape

/-- Fine sheafification recovers a coefficient already sheafy for both topologies. -/
noncomputable def commonCoefficientIso
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.obj F.coarse ≅ F.fine :=
  asIso ((sheafificationAdjunction J' AddCommGrpCat.{w}).counit.app F.fine)

/-- Fine sheafification carries the coarse constant integer sheaf to the fine one. -/
noncomputable def constantSheafIso
    (r : CoverageTopologyRefinement J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}] :
    r.fineSheafification.obj
        ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift ℤ))) ≅
      (constantSheaf J' AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ)) := by
  let adj₁ := (sheafificationAdjunction J AddCommGrpCat.{w}).comp
    r.fineSheafificationAdjunction
  let adj₂ := sheafificationAdjunction J' AddCommGrpCat.{w}
  exact (adj₁.leftAdjointUniq adj₂).app
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift ℤ)))

/--
The topology-change map on sheaf cohomology obtained from exact-functor Ext
naturality and the two canonical sheafification isomorphisms.
-/
noncomputable def sheafHExtMap
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  ((Abelian.Ext.mk₀ (r.commonCoefficientIso F).hom).postcomp
      ((constantSheaf J' AddCommGrpCat.{w}).obj
        (AddCommGrpCat.of (ULift ℤ))) (add_zero n)).comp
    (((Abelian.Ext.mk₀ r.constantSheafIso.inv).precomp
        (r.fineSheafification.obj F.coarse) (zero_add n)).comp
      (r.fineSheafification.mapExtAddHom
        ((constantSheaf J AddCommGrpCat.{w}).obj
          (AddCommGrpCat.of (ULift ℤ))) F.coarse n))

/-- The public topology-change map on sheaf cohomology. -/
noncomputable def sheafHMap
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    F.coarse.H n →+ F.fine.H n :=
  r.sheafHExtMap F n

/-- The public topology-change map is definitionally the concrete Ext composite. -/
@[simp] theorem sheafHMap_eq_ext
    (r : CoverageTopologyRefinement J J')
    (F : CommonCoefficientSheaf J J')
    [HasSheafify J AddCommGrpCat.{w}]
    [HasSheafify J' AddCommGrpCat.{w}]
    [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
    [HasExt.{w'} (Sheaf J' AddCommGrpCat.{w})]
    (n : Nat) :
    r.sheafHMap F n = r.sheafHExtMap F n :=
  rfl

end CoverageTopologyRefinement
end AAT.AG
