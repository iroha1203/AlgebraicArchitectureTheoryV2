import Formal.SHIGURE.Part2.Schemes.AffineCanonicalCoefficientFunctor
import Formal.SHIGURE.Part2.Schemes.AffineCanonicalOverlapComparison
import Formal.SHIGURE.Part2.Schemes.AffineGeometryToCoefficients

/-! # Comparing geometric and coefficient descent on an affine singleton -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

/-- Naturality of a chart comparison after factoring the original chart. -/
private theorem comparison_chart_naturality
    {C D E : Type*} [Category C] [Category D] [Category E]
    (P : C ⥤ D) (T : D ⥤ E) (Q : C ⥤ E) (η : P ⋙ T ≅ Q)
    {X Y : C} (e : X ≅ Y) {Z : D} (a : P.obj X ≅ Z) (b : Z ≅ P.obj Y)
    (h : P.mapIso e = a ≪≫ b) :
    η.app X ≪≫ Q.mapIso e = T.mapIso a ≪≫ T.mapIso b ≪≫ η.app Y := by
  apply Iso.ext
  have m : P.map e.hom = a.hom ≫ b.hom := congrArg Iso.hom h
  have n := η.hom.naturality e.hom
  change η.hom.app X ≫ Q.map e.hom = T.map a.hom ≫ T.map b.hom ≫ η.hom.app Y
  rw [← Category.assoc, ← Functor.map_comp, ← m]
  exact n.symm

/-- Transport the overlap comparison across two pairs of charts. Keeping
the diagram abstract avoids unfolding the concrete categories of sheaves. -/
private theorem comparison_chart_square {C : Type*} [Category C]
    {P₀ P₁ Q₀ Q₁ R₀ R₁ S₀ S₁ : C}
    (k₀ : P₀ ≅ Q₀) (k₁ : P₁ ≅ Q₁) (c₀ : Q₀ ≅ S₀) (c₁ : Q₁ ≅ S₁)
    (a₀ : P₀ ≅ R₀) (a₁ : P₁ ≅ R₁) (b₀ : R₀ ≅ S₀) (b₁ : R₁ ≅ S₁)
    (d : Q₀ ≅ Q₁) (g : R₀ ≅ R₁) (z : S₀ ≅ S₁)
    (h₀ : k₀ ≪≫ c₀ = a₀ ≪≫ b₀) (h₁ : k₁ ≪≫ c₁ = a₁ ≪≫ b₁)
    (hd : k₀ ≪≫ d ≪≫ k₁.symm = a₀ ≪≫ g ≪≫ a₁.symm)
    (hg : g = b₀ ≪≫ z ≪≫ b₁.symm) : c₀ ≪≫ z = d ≪≫ c₁ := by
  have h := congrArg (fun x => k₀.symm ≪≫ x ≪≫ k₁ ≪≫ c₁) hd
  rw [hg] at h
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc] at h
  have hc₀ : k₀.symm ≪≫ a₀ ≪≫ b₀ = c₀ := by
    simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using
      (congrArg (fun x => k₀.symm ≪≫ x) h₀).symm
  have hc₁ : b₁.symm ≪≫ a₁.symm ≪≫ k₁ ≪≫ c₁ = Iso.refl S₁ := by
    have eq : a₁.symm ≪≫ k₁ ≪≫ c₁ = b₁ := by
      simpa only [Iso.trans_assoc, Iso.symm_self_id_assoc] using
        congrArg (fun x => a₁.symm ≪≫ x) h₁
    simp only [eq, Iso.symm_self_id]
  calc
    c₀ ≪≫ z = c₀ ≪≫ z ≪≫ (b₁.symm ≪≫ a₁.symm ≪≫ k₁ ≪≫ c₁) := by
      rw [hc₁, Iso.trans_refl]
    _ = (k₀.symm ≪≫ a₀ ≪≫ b₀) ≪≫ z ≪≫
        (b₁.symm ≪≫ a₁.symm ≪≫ k₁ ≪≫ c₁) := by rw [hc₀]
    _ = d ≪≫ c₁ := by simpa only [Iso.trans_assoc] using h.symm

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B]

private abbrev forgetQuasiCoherent (X : Scheme.{u}) :=
  (quasiCoherentModulesProperty.prop (.mk (op X))).ι

private abbrev affineBaseRingMap : CommRingCat.of A ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (algebraMap A B)

private abbrev affineOverlapRingMap (i : Fin 2) :
    CommRingCat.of B ⟶ CommRingCat.of (B ⊗[A] B) :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

private theorem affineOverlapRingSquare :
    affineBaseRingMap (A := A) (B := B) ≫ affineOverlapRingMap (A := A) (B := B) 0 =
      affineBaseRingMap (A := A) (B := B) ≫ affineOverlapRingMap (A := A) (B := B) 1 := by
  ext x
  exact ((affineDoubleEmbedding A B 0).commutes x).trans
    ((affineDoubleEmbedding A B 1).commutes x).symm

/-- The coefficient chart, viewed as an isomorphism of the actual sheaves. -/
private def affineCanonicalSheafChart (M : ModuleCat.{u} A) :
    (tilde.functor (CommRingCat.of B)).obj
        (affineDescentCoefficientModule (affineCanonicalDatum (B := B) M)) ≅
      (pullback (affineScalarMap A B)).obj
        ((tilde.functor (CommRingCat.of A)).obj M) :=
  (forgetQuasiCoherent (Spec (CommRingCat.of B))).mapIso
    (affineDescentCoefficientChart (affineCanonicalDatum (B := B) M))

/-- The actual coefficient isomorphism factors through its sheaf chart and
the affine pullback comparison. -/
private theorem affineCanonicalSheafChart_factor (M : ModuleCat.{u} A) :
    (tilde.functor (CommRingCat.of B)).mapIso (affineCanonicalCoefficientIso (B := B) M) =
      affineCanonicalSheafChart (B := B) M ≪≫
        (tildePullbackIso (CommRingCat.ofHom (algebraMap A B))).app M := by
  apply Iso.ext
  have h := congrArg (fun f => (forgetQuasiCoherent (Spec (CommRingCat.of B))).map f)
    (affineCanonicalCoefficientIso_tilde_hom (B := B) M)
  simpa only [Functor.map_comp, affineTildePullbackIso_forget_hom] using h

/-- The coefficient chart and the affine pullback chart give the same
comparison after either restriction to an affine test scheme. -/
private theorem affineCanonicalPullbackChart_factor (M : ModuleCat.{u} A)
    {T : CommRingCat.{u}} (p : CommRingCat.of B ⟶ T) :
    (tildePullbackIso p).app
        (affineDescentCoefficientModule (affineCanonicalDatum (B := B) M)) ≪≫
      (ModuleCat.extendScalars p.hom ⋙ tilde.functor T).mapIso
        (affineCanonicalCoefficientIso (B := B) M) =
    (pullback (Spec.map p)).mapIso (affineCanonicalSheafChart (B := B) M) ≪≫
      affineIteratedTildeChart (CommRingCat.ofHom (algebraMap A B)) M p := by
  have h := comparison_chart_naturality (tilde.functor (CommRingCat.of B))
    (pullback (Spec.map p)) (ModuleCat.extendScalars p.hom ⋙ tilde.functor T)
    (tildePullbackIso p) (affineCanonicalCoefficientIso (B := B) M)
    (affineCanonicalSheafChart (B := B) M)
    ((tildePullbackIso (CommRingCat.ofHom (algebraMap A B))).app M)
    (affineCanonicalSheafChart_factor (B := B) M)
  simpa only [affineIteratedTildeChart, Iso.trans_assoc] using h

/-- On the actual affine double overlap, the geometric comparison is the
associated sheaf of the canonical scalar comparison. -/
private theorem affineCanonicalOverlap_sheaf (M : ModuleCat.{u} A) :
    (forgetQuasiCoherent (Spec (CommRingCat.of (B ⊗[A] B)))).mapIso
        (affineDoubleTransition A B (affineCanonicalDatum (B := B) M)) =
      affineIteratedTildeChart (affineBaseRingMap (A := A) (B := B)) M
          (affineOverlapRingMap (A := A) (B := B) 0) ≪≫
        (tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
          (canonicalScalarComparison (algebraMap A B)
            (affineOverlapRingMap (A := A) (B := B) 0).hom
            (affineOverlapRingMap (A := A) (B := B) 1).hom
            (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (B ⊗[A] B) => f.hom)
              (affineOverlapRingSquare (A := A) (B := B))) M) ≪≫
        (affineIteratedTildeChart (affineBaseRingMap (A := A) (B := B)) M
          (affineOverlapRingMap (A := A) (B := B) 1)).symm := by
  apply Iso.ext
  exact singletonCanonicalAffineComparison
    (affineBaseRingMap (A := A) (B := B))
    (affineOverlapRingMap (A := A) (B := B) 0)
    (affineOverlapRingMap (A := A) (B := B) 1)
    (affineOverlapRingSquare (A := A) (B := B)) M
    (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))))
    (affineDoubleProjection_base A B 0) (affineDoubleProjection_base A B 1)

/-- The scalar overlap is recovered from the geometric transition in the
    associated-module charts. -/
private theorem affineCanonicalScalarExtension_sheaf (M : ModuleCat.{u} A) :
    (tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
        (affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M)) =
      ((tildePullbackIso (affineOverlapRingMap (A := A) (B := B) 0)).app
          (affineDescentCoefficientModule (affineCanonicalDatum (B := B) M))).symm ≪≫
        (pullback (Spec.map (affineOverlapRingMap (A := A) (B := B) 0))).mapIso
          (affineCanonicalSheafChart (B := B) M) ≪≫
        (forgetQuasiCoherent (Spec (CommRingCat.of (B ⊗[A] B)))).mapIso
          (affineDoubleTransition A B (affineCanonicalDatum (B := B) M)) ≪≫
        ((pullback (Spec.map (affineOverlapRingMap (A := A) (B := B) 1))).mapIso
          (affineCanonicalSheafChart (B := B) M)).symm ≪≫
        (tildePullbackIso (affineOverlapRingMap (A := A) (B := B) 1)).app
          (affineDescentCoefficientModule (affineCanonicalDatum (B := B) M)) := by
  let D := affineCanonicalDatum (B := B) M
  let C := affineDescentCoefficientModule D
  let E := affineTildeEquivalence (CommRingCat.of (B ⊗[A] B))
  let p := affineOverlapRingMap (A := A) (B := B) 0
  let q := affineOverlapRingMap (A := A) (B := B) 1
  let a := (affineTildePullbackIso p).app C
  let b := (affineTildePullbackIso q).app C
  let c := affineDescentCoefficientChart D
  let t := a.symm ≪≫ (affinePullbackFunctor p).mapIso c ≪≫
    affineDoubleTransition A B D ≪≫ ((affinePullbackFunctor q).mapIso c).symm ≪≫ b
  have h : E.functor.map (affineDescentScalarExtensionIso D).hom = t.hom :=
    E.fullyFaithfulFunctor.map_preimage t.hom
  have hf := congrArg (fun f => (forgetQuasiCoherent (Spec (CommRingCat.of (B ⊗[A] B)))).map f) h
  apply Iso.ext
  simpa only [t, Iso.trans_hom, Iso.symm_hom, Functor.map_comp,
    Functor.mapIso_hom, Functor.mapIso_inv, affineTildePullbackIso_forget_hom,
    affineTildePullbackIso_forget_inv] using hf

/-- Once the actual geometric comparison has been identified with B.4 on
objects and maps, the full-faithful coefficient functor reflects effective
descent. The identification is a separate construction. -/
private theorem singletonEquivalence_of_coefficientComparison
    (comparison : affineCanonicalDatumFunctor A B ⋙
        (affineGeometryToCoefficients (A := A) (B := B)) ≅
      DescentModule.extend (A := A) (B := B)) :
    (quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => affineScalarMap A B)).IsEquivalence := by
  let T := affineTildeFunctor (CommRingCat.of A)
  letI : T.IsEquivalence := (affineTildeEquivalence (CommRingCat.of A)).isEquivalence_functor
  let C := quasiCoherentModulesPseudofunctor.toDescentData
    (fun _ : Unit => affineScalarMap A B)
  let H := affineGeometryToCoefficients (A := A) (B := B)
  letI : H.Faithful := (affineGeometryToCoefficientsFullyFaithful (A := A) (B := B)).faithful
  letI : H.Full := (affineGeometryToCoefficientsFullyFaithful (A := A) (B := B)).full
  letI : (DescentModule.extend (A := A) (B := B)).IsEquivalence :=
    (DescentModule.equivalence (A := A) (B := B)).isEquivalence_functor
  letI : ((T ⋙ C) ⋙ H).IsEquivalence := Functor.isEquivalence_of_iso comparison.symm
  letI : (T ⋙ C).Faithful := Functor.Faithful.of_comp (T ⋙ C) H
  letI : (T ⋙ C).Full := Functor.Full.of_comp_faithful (T ⋙ C) H
  letI : (T ⋙ C).EssSurj := Functor.essSurj_of_comp_fully_faithful (T ⋙ C) H
  letI : (T ⋙ C).IsEquivalence := {}
  exact Functor.isEquivalence_of_comp_left T C

end

end SHIGURE.SchemeDescent
