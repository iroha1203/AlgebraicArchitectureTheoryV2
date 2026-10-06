import ResearchLean.AG.AtlasDefectComposition.FiniteComplexFamily
import Formal.Util.AssertStandardAxioms
/-! # 加法的構成と全有限直和の指定射

Implementation notes: 任意universeの有限添字で既存加法性から直和保存を導く。
構成間の自然変換も同じ成分射の biproduct map に移す。
-/
noncomputable section
open CategoryTheory Limits
namespace AAT.AG.AtlasDefectComposition
universe j
variable {J : Type j} [Fintype J]
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
variable (T : C ⥤ D) [T.Additive] (X : J → C) [HasBiproduct X]
variable [HasBiproduct (T.obj ∘ X)]
/-- F の加法的構成は全有限ラベル直和を同じ添字の直和へ同定する。 -/
def additiveSumIso : T.obj (⨁ X) ≅ ⨁ (T.obj ∘ X) :=
  letI := FiniteComplexFamily.additivePreservesFamily T X
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves T (biproduct.isBilimit X))
/-- 保存同型の各成分射影は元のラベル射影への構成の作用である。 -/
@[simp] theorem additiveSumIso_projection (j : J) :
    (additiveSumIso T X).hom ≫ biproduct.π (T.obj ∘ X) j =
      T.map (biproduct.π X j) := by
  dsimp only [additiveSumIso,biproduct.uniqueUpToIso_hom]
  exact biproduct.lift_π _ j
variable (U : C ⥤ D) [U.Additive] [HasBiproduct (U.obj ∘ X)]
/-- F の指定自然変換は全有限直和の同型を通して同じ成分射の直和となる。 -/
theorem additiveSumIso_natural (η : T ⟶ U) :
    (additiveSumIso T X).hom ≫ biproduct.map (f := T.obj ∘ X) (g := U.obj ∘ X) (fun j => η.app (X j)) =
      η.app (⨁ X) ≫ (additiveSumIso U X).hom := by
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc,biproduct.map_π]
  rw [← Category.assoc,additiveSumIso_projection,additiveSumIso_projection]
  exact η.naturality (biproduct.π X j)
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
