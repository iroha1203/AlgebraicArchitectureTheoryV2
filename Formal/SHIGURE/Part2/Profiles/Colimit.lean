import Formal.SHIGURE.Part2.Profiles.Charts
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# Filtered recovery of all copying maps

Theorem 4.6 takes the colimit of the relative affine test points in `Type`.
Every copying map appears at its row supports, and two charts that present
the same map agree after enlargement to the pointwise union.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SHIGURE.Copying.SupportProfile

universe u

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable [Algebra k R] [Algebra k S]
variable {X Y : Type u}

/-- Support profiles form a nonempty filtered index category by pointwise union. -/
theorem isFiltered (X Y : Type u) : IsFiltered (SupportProfile X Y) :=
  inferInstance

private theorem profileLeOfHom {F G : SupportProfile X Y} (h : F ⟶ G) : F ≤ G :=
  fun x => leOfHom (h x)

/-- The diagram of chart points at a fixed affine test algebra in Theorem 4.6. -/
def affinePointDiagram (k R X Y : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    SupportProfile X Y ⥤ Type u where
  obj F := specOver R ⟶ F.chart k
  map h := ↾fun p => p ≫ transition (profileLeOfHom h)
  map_id F := by
    ext1 p
    apply F.affinePointRowsEquiv.injective
    exact affinePointRowsEquiv_transition _ p
  map_comp {F G H} f g := by
    ext1 p
    apply H.affinePointRowsEquiv.injective
    change H.affinePointRowsEquiv (p ≫ transition (profileLeOfHom (f ≫ g))) =
      H.affinePointRowsEquiv ((p ≫ transition (profileLeOfHom f)) ≫ transition (profileLeOfHom g))
    rw [affinePointRowsEquiv_transition, affinePointRowsEquiv_transition,
      affinePointRowsEquiv_transition]
    rfl

/-- Drop the profile and use the coefficient row correspondence of Theorem 4.3. -/
def affinePointCocone (k R X Y : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    Cocone (affinePointDiagram k R X Y) where
  pt := CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y
  ι :=
    { app := fun F => ↾fun p => (coalgebraRowsEquiv X Y).symm (F.affinePointRowsEquiv p).val
      naturality := by
        intro F G h
        ext1 p
        change (coalgebraRowsEquiv X Y).symm (G.affinePointRowsEquiv
          (p ≫ transition (profileLeOfHom h))).val =
          (coalgebraRowsEquiv X Y).symm (F.affinePointRowsEquiv p).val
        rw [affinePointRowsEquiv_transition]
        rfl }

/-- The cocone of all copying maps is a colimit of the chart points at the test algebra. -/
def affinePointCoconeIsColimit (k R X Y : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    IsColimit (affinePointCocone k R X Y) := by
  apply Types.FilteredColimit.isColimitOf (affinePointDiagram k R X Y)
  · intro f
    let a := coalgebraRowsEquiv X Y f
    let F : SupportProfile X Y := fun x => (a.val x).support
    let b : F.RowsAt R := ⟨a, fun _ => Finset.Subset.rfl⟩
    refine ⟨F, F.affinePointRowsEquiv.symm b, ?_⟩
    change f = (coalgebraRowsEquiv X Y).symm
      (F.affinePointRowsEquiv (F.affinePointRowsEquiv.symm b)).val
    rw [Equiv.apply_symm_apply]
    exact ((coalgebraRowsEquiv X Y).symm_apply_apply f).symm
  · intro F G p q h
    classical
    let H : SupportProfile X Y := fun x => F x ∪ G x
    have hF : F ≤ H := fun _ => Finset.subset_union_left
    have hG : G ≤ H := fun _ => Finset.subset_union_right
    refine ⟨H, fun x => homOfLE (hF x), fun x => homOfLE (hG x), ?_⟩
    apply H.affinePointRowsEquiv.injective
    change H.affinePointRowsEquiv (p ≫ transition hF) =
      H.affinePointRowsEquiv (q ≫ transition hG)
    rw [affinePointRowsEquiv_transition, affinePointRowsEquiv_transition]
    exact Subtype.ext ((coalgebraRowsEquiv X Y).symm.injective h)

/-- Theorem 4.6. The colimit of the affine chart points is the set of all copying maps. -/
def colimitEquiv (k R X Y : Type u) [CommRing k] [CommRing R] [Algebra k R] :
    colimit (affinePointDiagram k R X Y) ≃ (CopyCoalgebra R X →ₗc[R] CopyCoalgebra R Y) :=
  (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) (affinePointCoconeIsColimit k R X Y)).toEquiv

/-- The colimit correspondence on the leg from a chart sends a point to its copying map. -/
theorem colimitEquiv_ι (F : SupportProfile X Y) (p : specOver R ⟶ F.chart k) :
    colimitEquiv k R X Y (colimit.ι (affinePointDiagram k R X Y) F p) =
      (coalgebraRowsEquiv X Y).symm (F.affinePointRowsEquiv p).val :=
  congrFun (colimit.comp_coconePointUniqueUpToIso_hom (affinePointCoconeIsColimit k R X Y) F) p

/-- A map of test algebras induces a map of all chart point sets. -/
def affinePointDiagramMap (g : R →ₐ[k] S) (X Y : Type u) :
    affinePointDiagram k R X Y ⟶ affinePointDiagram k S X Y where
  app _ := ↾fun p => specOverMap g ≫ p
  naturality := by
    intro F G h
    ext1 p
    exact (Category.assoc (specOverMap g) p (transition (profileLeOfHom h))).symm

/-- The colimit correspondence commutes with a change of affine test algebra. -/
theorem colimitEquiv_natural (g : R →ₐ[k] S) (a : colimit (affinePointDiagram k R X Y)) :
    coalgebraRowsEquiv X Y (colimitEquiv k S X Y (colim.map (affinePointDiagramMap g X Y) a)) =
      mapRows g.toRingHom (coalgebraRowsEquiv X Y (colimitEquiv k R X Y a)) := by
  obtain ⟨F, p, rfl⟩ := Types.jointly_surjective' a
  have h := congrFun (colimit.ι_map (affinePointDiagramMap g X Y) F) p
  change colim.map (affinePointDiagramMap g X Y) (colimit.ι (affinePointDiagram k R X Y) F p) =
    colimit.ι (affinePointDiagram k S X Y) F (specOverMap g ≫ p) at h
  rw [h, colimitEquiv_ι, colimitEquiv_ι, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    affinePointRowsEquiv_natural]
  rfl

end SHIGURE.Copying.SupportProfile
