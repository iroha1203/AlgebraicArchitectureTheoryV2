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

/-!
# Coverage and cohomology functoriality

This module owns topology refinement, selected-cover refinement, canonical
Čech functoriality, and actual sheaf-cohomology comparison fixed by Part 4
SD3–SD5.
-/

noncomputable section

namespace AAT.AG

universe u v

open CategoryTheory

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
end AAT.AG
