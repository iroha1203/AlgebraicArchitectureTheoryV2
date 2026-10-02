import ResearchLean.AG.RelativeRepairComposition.RelativeComplex
import Mathlib.Algebra.Homology.HomologicalComplexBiprod
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Native product coordinates for two cochain complexes

The product has the actual two differentials on its two coordinates. Its
comparison is the native binary biproduct, through the coordinate projections
and inclusions in every degree.

## Implementation notes

Cartesian product coordinates make original values directly inspectable. The
native comparison is constructed from chain maps with both differentials,
rather than only from degreewise group isomorphisms.
-/
namespace AAT.AG.RelativeRepairComposition.NativeProductComplex
open CategoryTheory Limits
universe u
variable (K L : CochainComplex AddCommGrpCat.{u} ℕ)

/-- Cartesian product groups with the actual differentials on both factors. -/
noncomputable def complex : CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of (fun n => AddCommGrpCat.of (K.X n × L.X n))
    (fun n => AddCommGrpCat.ofHom ((K.d n (n+1)).hom.prodMap (L.d n (n+1)).hom)) (by
      intro n
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      apply Prod.ext
      · exact CategoryTheory.congr_fun (K.d_comp_d n (n+1) (n+2)) x.1
      · exact CategoryTheory.congr_fun (L.d_comp_d n (n+1) (n+2)) x.2)

/-- The adjacent differential applies precisely the original differential on each coordinate. -/
theorem complex_d (n : ℕ) :
    (complex K L).d n (n+1) =
      AddCommGrpCat.ofHom ((K.d n (n+1)).hom.prodMap (L.d n (n+1)).hom) :=
  CochainComplex.of_d _ _ _ n

/-- The original first coordinate projection is a chain map in every degree. -/
noncomputable def fst : complex K L ⟶ K where
  f n := AddCommGrpCat.ofHom (AddMonoidHom.fst (K.X n) (L.X n))
  comm' i j hij := by
    change i+1=j at hij
    subst j
    simp only [complex,CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rfl

/-- The original second coordinate projection is a chain map in every degree. -/
noncomputable def snd : complex K L ⟶ L where
  f n := AddCommGrpCat.ofHom (AddMonoidHom.snd (K.X n) (L.X n))
  comm' i j hij := by
    change i+1=j at hij
    subst j
    simp only [complex,CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    rfl

/-- The first factor enters with zero second value, compatibly with its actual differential. -/
noncomputable def inl : K ⟶ complex K L where
  f n := AddCommGrpCat.ofHom ((AddMonoidHom.id (K.X n)).prod (0 : K.X n →+ L.X n))
  comm' i j hij := by
    change i+1=j at hij
    subst j
    simp only [complex,CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Prod.ext
    · rfl
    · exact map_zero (L.d i (i+1)).hom

/-- The second factor enters with zero first value, compatibly with its actual differential. -/
noncomputable def inr : L ⟶ complex K L where
  f n := AddCommGrpCat.ofHom ((0 : L.X n →+ K.X n).prod (AddMonoidHom.id (L.X n)))
  comm' i j hij := by
    change i+1=j at hij
    subst j
    simp only [complex,CochainComplex.of_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply Prod.ext
    · exact map_zero (K.d i (i+1)).hom
    · rfl

/-- The actual Cartesian product complex is the native binary biproduct. -/
noncomputable def iso : complex K L ≅ K ⊞ L where
  hom := biprod.lift (fst K L) (snd K L)
  inv := biprod.desc (inl K L) (inr K L)
  hom_inv_id := by
    rw [biprod.lift_desc]
    apply HomologicalComplex.Hom.ext
    funext n
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact Prod.ext (add_zero _) (zero_add _)
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext'
    all_goals simp only [Category.assoc,biprod.lift_fst,biprod.lift_snd,
      biprod.inl_desc_assoc,biprod.inr_desc_assoc,biprod.inl_fst,biprod.inl_snd,
      biprod.inr_fst,biprod.inr_snd,Category.id_comp]
    all_goals apply HomologicalComplex.Hom.ext; funext n
    all_goals apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; rfl

/-- The native comparison has exactly the old first coordinate. -/
theorem iso_fst : (iso K L).hom ≫ biprod.fst = fst K L := biprod.lift_fst _ _

/-- The native comparison has exactly the full supplemental coordinate. -/
theorem iso_snd : (iso K L).hom ≫ biprod.snd = snd K L := biprod.lift_snd _ _

end AAT.AG.RelativeRepairComposition.NativeProductComplex
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeProductComplex
