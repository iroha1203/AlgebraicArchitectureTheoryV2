import Formal.SHIGURE.Part2.Schemes.AffineCanonicalCoefficientFunctor
import Formal.SHIGURE.Part2.Schemes.AffineCanonicalOverlapComparison
import Formal.SHIGURE.Part2.Schemes.AffineGeometryToCoefficients
import Formal.SHIGURE.Part2.Descent.CanonicalOverlapTensor

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

/-- Lift a named equality of morphisms to their isomorphisms. -/
private theorem iso_of_named_homs {C : Type*} [Category C] {P Q : C}
    {m n : P ⟶ Q} (h : m = n)
    (y : P ≅ Q) (hy : y.hom = n)
    (x : P ≅ Q) (hx : x.hom = m) : x = y :=
  Iso.ext (hx.trans (h.trans hy.symm))

/-- Conjugating a comparison by an isomorphism gives a commuting square. -/
private theorem conjugate_comparison_square {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) {X Y : C} (e : X ≅ Y) (d : F.obj X ≅ G.obj X) :
    F.map e.hom ≫ ((F.mapIso e).symm ≪≫ d ≪≫ G.mapIso e).hom =
      d.hom ≫ G.map e.hom := by
  let a := F.mapIso e
  change a.hom ≫ (a.inv ≫ d.hom ≫ G.map e.hom) = d.hom ≫ G.map e.hom
  rw [a.hom_inv_id_assoc]

/-- Compatible squares compose along the intermediate chart. -/
private theorem compose_comparison_squares {C D : Type*} [Category C] [Category D]
    (F G : C ⥤ D) {X Y Z : C}
    (d : F.obj X ⟶ G.obj X) (c : F.obj Y ⟶ G.obj Y) (z : F.obj Z ⟶ G.obj Z)
    (e : X ⟶ Y) (t : Y ⟶ Z)
    (h₁ : F.map e ≫ c = d ≫ G.map e) (h₂ : F.map t ≫ z = c ≫ G.map t) :
    F.map (e ≫ t) ≫ z = d ≫ G.map (e ≫ t) := by
  calc
    F.map (e ≫ t) ≫ z = F.map e ≫ (F.map t ≫ z) := by rw [F.map_comp, Category.assoc]
    _ = F.map e ≫ (c ≫ G.map t) := by rw [h₂]
    _ = (F.map e ≫ c) ≫ G.map t := (Category.assoc _ _ _).symm
    _ = (d ≫ G.map e) ≫ G.map t := by rw [h₁]
    _ = d ≫ G.map (e ≫ t) := by rw [G.map_comp, Category.assoc]

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

section AbstractAffineComparison

variable {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (p q : S ⟶ T) (h : f ≫ p = f ≫ q)
    (M : ModuleCat.{u} R) (b : Spec T ⟶ Spec R)
    (hp : Spec.map p ≫ Spec.map f = b) (hq : Spec.map q ≫ Spec.map f = b)

private def affineNamedHoms :=
  iso_of_named_homs (C := (Spec T).Modules)
    (singletonCanonicalAffineComparison f p q h M b hp hq)

private def affineRightHoms :=
  affineNamedHoms f p q h M b hp hq
    (affineIteratedTildeChart f M p ≪≫
      (tilde.functor T).mapIso
        (canonicalScalarComparison f.hom p.hom q.hom
          (congrArg (fun k : R ⟶ T => k.hom) h) M) ≪≫
      (affineIteratedTildeChart f M q).symm)
    rfl

private def affineBothIsos :=
  affineRightHoms f p q h M b hp hq
    ((quasiCoherentModulesProperty.prop (.mk (op (Spec T)))).ι.mapIso
      (((quasiCoherentModulesPseudofunctor.toDescentData
          (fun _ : Unit => Spec.map f)).obj ((affineTildeFunctor R).obj M)).iso
        b (i₁ := ()) (i₂ := ()) (Spec.map p) (Spec.map q) hp hq))

private def affineIsoProof :=
  affineBothIsos f p q h M b hp hq
    (singletonMappedIso_hom_betweenPullbacks
      (Spec.map f) (Spec.map p) (Spec.map q) b hp hq
      ((affineTildeFunctor R).obj M))

end AbstractAffineComparison

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B]

private abbrev forgetQuasiCoherent (X : Scheme.{u}) :=
  (quasiCoherentModulesProperty.prop (.mk (op X))).ι

private abbrev affineBaseRingMap : CommRingCat.of A ⟶ CommRingCat.of B :=
  CommRingCat.ofHom (algebraMap A B)

private abbrev affineOverlapRingMap (i : Fin 2) :
    CommRingCat.of B ⟶ CommRingCat.of (B ⊗[A] B) :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

omit [Module.FaithfullyFlat A B] in
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

omit [Module.FaithfullyFlat A B] in
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

omit [Module.FaithfullyFlat A B] in
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

omit [Module.FaithfullyFlat A B] in
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
  exact affineIsoProof
    (affineBaseRingMap (A := A) (B := B))
    (affineOverlapRingMap (A := A) (B := B) 0)
    (affineOverlapRingMap (A := A) (B := B) 1)
    (affineOverlapRingSquare (A := A) (B := B)) M
    (Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))))
    (affineDoubleProjection_base A B 0) (affineDoubleProjection_base A B 1)

omit [Module.FaithfullyFlat A B] in
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

omit [Module.FaithfullyFlat A B] in
/-- The coefficient comparison carries the geometric scalar transition to
the canonical scalar comparison on the two affine overlap charts. -/
private theorem affineCanonicalScalarSquare_sheaf (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (affineOverlapRingMap (A := A) (B := B) 0).hom ⋙
        tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
        (affineCanonicalCoefficientIso (B := B) M) ≪≫
      (tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
        (canonicalScalarComparison (algebraMap A B)
          (affineOverlapRingMap (A := A) (B := B) 0).hom
          (affineOverlapRingMap (A := A) (B := B) 1).hom
          (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (B ⊗[A] B) => f.hom)
            (affineOverlapRingSquare (A := A) (B := B))) M) =
    (tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
        (affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M)) ≪≫
      (ModuleCat.extendScalars (affineOverlapRingMap (A := A) (B := B) 1).hom ⋙
        tilde.functor (CommRingCat.of (B ⊗[A] B))).mapIso
        (affineCanonicalCoefficientIso (B := B) M) := by
  let T := CommRingCat.of (B ⊗[A] B)
  let p := affineOverlapRingMap (A := A) (B := B) 0
  let q := affineOverlapRingMap (A := A) (B := B) 1
  let C := affineDescentCoefficientModule (affineCanonicalDatum (B := B) M)
  let e := affineCanonicalCoefficientIso (B := B) M
  let c := affineCanonicalSheafChart (B := B) M
  let k₀ := (tildePullbackIso p).app C
  let k₁ := (tildePullbackIso q).app C
  let c₀ := (ModuleCat.extendScalars p.hom ⋙ tilde.functor T).mapIso e
  let c₁ := (ModuleCat.extendScalars q.hom ⋙ tilde.functor T).mapIso e
  let a₀ := (pullback (Spec.map p)).mapIso c
  let a₁ := (pullback (Spec.map q)).mapIso c
  let b₀ := affineIteratedTildeChart (affineBaseRingMap (A := A) (B := B)) M p
  let b₁ := affineIteratedTildeChart (affineBaseRingMap (A := A) (B := B)) M q
  let d := (tilde.functor T).mapIso
    (affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M))
  let g := (forgetQuasiCoherent (Spec T)).mapIso
    (affineDoubleTransition A B (affineCanonicalDatum (B := B) M))
  let z := (tilde.functor T).mapIso
    (canonicalScalarComparison (algebraMap A B) p.hom q.hom
      (congrArg (fun f : CommRingCat.of A ⟶ T => f.hom)
        (affineOverlapRingSquare (A := A) (B := B))) M)
  have h₀ : k₀ ≪≫ c₀ = a₀ ≪≫ b₀ := affineCanonicalPullbackChart_factor (B := B) M p
  have h₁ : k₁ ≪≫ c₁ = a₁ ≪≫ b₁ := affineCanonicalPullbackChart_factor (B := B) M q
  have hd : k₀ ≪≫ d ≪≫ k₁.symm = a₀ ≪≫ g ≪≫ a₁.symm := by
    have factor : d = k₀.symm ≪≫ a₀ ≪≫ g ≪≫ a₁.symm ≪≫ k₁ :=
      affineCanonicalScalarExtension_sheaf (B := B) M
    have h := congrArg (fun x => k₀ ≪≫ x ≪≫ k₁.symm) factor
    simpa only [Iso.trans_assoc, Iso.self_symm_id_assoc, Iso.self_symm_id,
      Iso.trans_refl] using h
  have hg : g = b₀ ≪≫ z ≪≫ b₁.symm := affineCanonicalOverlap_sheaf (B := B) M
  exact comparison_chart_square k₀ k₁ c₀ c₁ a₀ a₁ b₀ b₁ d g z h₀ h₁ hd hg

omit [Module.FaithfullyFlat A B] in
/-- The coefficient chart intertwines the actual scalar transition with the
canonical comparison on the two overlap algebras. -/
private theorem affineCanonicalScalarSquare (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (affineOverlapRingMap (A := A) (B := B) 0).hom).map
        (affineCanonicalCoefficientIso (B := B) M).hom ≫
      (canonicalScalarComparison (algebraMap A B)
        (affineOverlapRingMap (A := A) (B := B) 0).hom
        (affineOverlapRingMap (A := A) (B := B) 1).hom
        (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (B ⊗[A] B) => f.hom)
          (affineOverlapRingSquare (A := A) (B := B))) M).hom =
    (affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M)).hom ≫
      (ModuleCat.extendScalars (affineOverlapRingMap (A := A) (B := B) 1).hom).map
        (affineCanonicalCoefficientIso (B := B) M).hom := by
  apply (tilde.fullyFaithfulFunctor (R := CommRingCat.of (B ⊗[A] B))).map_injective
  have h := congrArg Iso.hom (affineCanonicalScalarSquare_sheaf (B := B) M)
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Functor.comp_map, Functor.map_comp] using h

omit [Module.FaithfullyFlat A B] in
/-- The tensor presentation preserves the actual scalar comparison. -/
private theorem affineCanonicalTensorSquare (M : ModuleCat.{u} A) :
    (ModuleCat.extendScalars (firstScalarEmbedding A B)).map
        (affineCanonicalTensorIso (B := B) M).hom ≫
      (canonicalScalarComparisonOnTensor M (extendScalarsTensorIso (B := B) M)).hom =
    (affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M)).hom ≫
      (ModuleCat.extendScalars (secondScalarEmbedding A B)).map
        (affineCanonicalTensorIso (B := B) M).hom := by
  let F := ModuleCat.extendScalars (firstScalarEmbedding A B)
  let G := ModuleCat.extendScalars (secondScalarEmbedding A B)
  let e := affineCanonicalCoefficientIso (B := B) M
  let t := extendScalarsTensorIso (B := B) M
  let d := affineDescentScalarExtensionIso (affineCanonicalDatum (B := B) M)
  let c := canonicalScalarComparison (algebraMap A B)
    (affineOverlapRingMap (A := A) (B := B) 0).hom
    (affineOverlapRingMap (A := A) (B := B) 1).hom
    (congrArg (fun f : CommRingCat.of A ⟶ CommRingCat.of (B ⊗[A] B) => f.hom)
      (affineOverlapRingSquare (A := A) (B := B))) M
  let z := canonicalScalarComparisonOnTensor M t
  have h₁ : F.map e.hom ≫ c.hom = d.hom ≫ G.map e.hom :=
    affineCanonicalScalarSquare (B := B) M
  have h₂ : F.map t.hom ≫ z.hom = c.hom ≫ G.map t.hom :=
    conjugate_comparison_square F G t c
  exact compose_comparison_squares F G d.hom c.hom z.hom e.hom t.hom h₁ h₂

omit [Module.FaithfullyFlat A B] in
set_option maxRecDepth 2048 in
/-- The tensor chart is a morphism of the actual coefficient descent data. -/
private theorem affineCanonicalTensorCompatible (M : ModuleCat.{u} A) :
    ((affineGeometryToCoefficients (A := A) (B := B)).obj
        (affineCanonicalDatum (B := B) M)).datum.Compatible
      ((DescentModule.extend (A := A) (B := B)).obj M).datum
      (affineCanonicalTensorIso (B := B) M).hom.hom := by
  let D := affineCanonicalDatum (B := B) M
  let N := affineDescentCoefficientModule D
  letI : Module A N := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  intro x
  have h := scalarOverlapIso_comm (A := A) (B := B)
    (affineDescentScalarExtensionIso D)
    (canonicalScalarComparisonOnTensor M (extendScalarsTensorIso (B := B) M))
    (affineCanonicalTensorIso (B := B) M).hom (affineCanonicalTensorSquare (B := B) M) x
  have standardAt := congrArg
    (fun θ : OverlapIso A B (B ⊗[A] M) =>
      θ (((affineCanonicalTensorIso (B := B) M).hom.hom.restrictScalars A).rTensor B x))
    (canonicalScalarComparisonOnTensor_standard (A := A) (B := B) M)
  exact h.trans standardAt

omit [Module.FaithfullyFlat A B] in
set_option maxRecDepth 2048 in
/-- The canonical geometric datum and standard coefficient extension are
isomorphic as descent data, with inverse induced by the same tensor chart. -/
private def affineCanonicalDescentIso (M : ModuleCat.{u} A) :
    (affineGeometryToCoefficients (A := A) (B := B)).obj
        (affineCanonicalDatum (B := B) M) ≅
      (DescentModule.extend (A := A) (B := B)).obj M := by
  let X := (affineGeometryToCoefficients (A := A) (B := B)).obj
    (affineCanonicalDatum (B := B) M)
  let Y := (DescentModule.extend (A := A) (B := B)).obj M
  let e := affineCanonicalTensorIso (B := B) M
  have compatible : X.datum.Compatible Y.datum e.toLinearEquiv.toLinearMap :=
    affineCanonicalTensorCompatible (B := B) M
  refine ⟨⟨e.hom.hom, compatible⟩,
    ⟨e.inv.hom, X.datum.compatible_symm Y.datum e.toLinearEquiv compatible⟩, ?_, ?_⟩
  · apply DescentModule.Hom.ext
    ext x
    exact e.toLinearEquiv.left_inv x
  · apply DescentModule.Hom.ext
    ext x
    exact e.toLinearEquiv.right_inv x

omit [Module.FaithfullyFlat A B] in
private def affineCanonicalDatumMap {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    affineCanonicalDatum (B := B) M ⟶ affineCanonicalDatum (B := B) N :=
  (quasiCoherentModulesPseudofunctor.toDescentData (fun _ : Unit => affineScalarMap A B)).map
    ((affineTildeFunctor (CommRingCat.of A)).map f)

omit [Module.FaithfullyFlat A B] in
set_option maxRecDepth 2048 in
/-- The tensor charts commute with every map of modules over the base. -/
private theorem affineCanonicalTensorNaturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    affineDescentCoefficientMap (affineCanonicalDatumMap (B := B) f) ≫
        (affineCanonicalTensorIso (B := B) N).hom =
      (affineCanonicalTensorIso (B := B) M).hom ≫
        ModuleCat.ofHom (f.hom.baseChange B) := by
  let G := ModuleCat.extendScalars (algebraMap A B)
  let g := affineDescentCoefficientMap (affineCanonicalDatumMap (B := B) f)
  let eM := (affineCanonicalCoefficientIso (B := B) M).hom
  let eN := (affineCanonicalCoefficientIso (B := B) N).hom
  let tM := (extendScalarsTensorIso (B := B) M).hom
  let tN := (extendScalarsTensorIso (B := B) N).hom
  let v := ModuleCat.ofHom (f.hom.baseChange B)
  have first : g ≫ eN = eM ≫ G.map f := by
    have h := (affineCanonicalCoefficientNatIso A B).hom.naturality f
    rw [affineCanonicalCoefficientNatIso_app_hom, affineCanonicalCoefficientNatIso_app_hom] at h
    exact h
  have second : G.map f ≫ tN = tM ≫ v := extendScalarsTensorIso_natural (B := B) f
  change g ≫ (eN ≫ tN) = (eM ≫ tM) ≫ v
  calc
    g ≫ (eN ≫ tN) = (g ≫ eN) ≫ tN := (Category.assoc _ _ _).symm
    _ = (eM ≫ G.map f) ≫ tN := by rw [first]
    _ = eM ≫ (G.map f ≫ tN) := Category.assoc _ _ _
    _ = eM ≫ (tM ≫ v) := by rw [second]
    _ = (eM ≫ tM) ≫ v := (Category.assoc _ _ _).symm

omit [Module.FaithfullyFlat A B] in
private def affineCanonicalDatumFunctorNormalized : ModuleCat.{u} A ⥤ AffineSingletonDescentData A B where
  obj M := affineCanonicalDatum (B := B) M
  map f := affineCanonicalDatumMap (B := B) f
  map_id M := by
    let T := affineTildeFunctor (CommRingCat.of A)
    let C := quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => affineScalarMap A B)
    change C.map (T.map (𝟙 M)) = 𝟙 (C.obj (T.obj M))
    rw [T.map_id, C.map_id]
  map_comp f g := by simp only [affineCanonicalDatumMap, Functor.map_comp]

omit [Module.FaithfullyFlat A B] in
private def affineCanonicalDatumPresentation :
    affineCanonicalDatumFunctor A B ≅ affineCanonicalDatumFunctorNormalized (A := A) (B := B) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    rfl)

omit [Module.FaithfullyFlat A B] in
private def affineCanonicalDescentNatIsoNormalized :
    affineCanonicalDatumFunctorNormalized (A := A) (B := B) ⋙
        (affineGeometryToCoefficients (A := A) (B := B)) ≅
      DescentModule.extend (A := A) (B := B) :=
  NatIso.ofComponents (fun M => affineCanonicalDescentIso (B := B) M) (by
    intro M N f
    apply DescentModule.Hom.ext
    exact congrArg ModuleCat.Hom.hom (affineCanonicalTensorNaturality (B := B) f))

omit [Module.FaithfullyFlat A B] in
/-- The coefficient descent isomorphisms are natural in all module maps. -/
private def affineCanonicalDescentNatIso :
    affineCanonicalDatumFunctor A B ⋙ (affineGeometryToCoefficients (A := A) (B := B)) ≅
      DescentModule.extend (A := A) (B := B) :=
  Functor.isoWhiskerRight (affineCanonicalDatumPresentation (A := A) (B := B))
      (affineGeometryToCoefficients (A := A) (B := B)) ≪≫
    affineCanonicalDescentNatIsoNormalized (A := A) (B := B)

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

/-- A faithfully flat affine morphism has effective descent for all
quasi-coherent modules and all their compatible morphisms. -/
theorem affineSingletonFaithfullyFlatDescent :
    (quasiCoherentModulesPseudofunctor.toDescentData
      (fun _ : Unit => affineScalarMap A B)).IsEquivalence :=
  singletonEquivalence_of_coefficientComparison (affineCanonicalDescentNatIso (A := A) (B := B))

end

end SHIGURE.SchemeDescent
