import Formal.SHIGURE.Part2.Schemes.AffineCoefficientComparison
import Formal.SHIGURE.Part2.Schemes.DescentRechart

/-! # The geometric affine datum in its associated-module charts -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Opposite Scheme.Modules TensorProduct

noncomputable section

universe u

private abbrev forget (X : Scheme.{u}) := (quasiCoherentModulesProperty.prop (.mk (op X))).ι

section PullbackComponents

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} R)

/-- The affine pullback comparison has its original module-sheaf component. -/
theorem affineTildePullbackIso_forget_hom :
    (forget (Spec S)).map ((affineTildePullbackIso f).hom.app M) = (tildePullbackIso f).hom.app M := rfl

/-- Forget the inverse comparison to the original module-sheaf component. -/
theorem affineTildePullbackIso_forget_inv :
    (forget (Spec S)).map ((affineTildePullbackIso f).inv.app M) = (tildePullbackIso f).inv.app M := rfl

end PullbackComponents

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B

private abbrev bund (i : Fin 2) : CommRingCat.of B ⟶ CommRingCat.of B₂ :=
  CommRingCat.ofHom (affineDoubleEmbedding A B i).toRingHom

private def affineTildeDescentChartIso (data : AffineSingletonDescentData A B) (i : Unit) :
    (affineTildeFunctor (CommRingCat.of B)).obj (affineDescentCoefficientModule data) ≅ data.obj i := by
  cases i
  exact affineDescentCoefficientChart data

/-- Express the whole geometric descent object in its actual associated module charts. -/
def affineTildeDescentData (data : AffineSingletonDescentData A B) : AffineSingletonDescentData A B :=
  descentRechart (X := fun _ : Unit =>
    (affineTildeFunctor (CommRingCat.of B)).obj (affineDescentCoefficientModule data))
    data (affineTildeDescentChartIso data)

/-- The associated module presentation respects all comparisons on all test schemes. -/
def affineTildeDescentDataIso (data : AffineSingletonDescentData A B) : affineTildeDescentData data ≅ data :=
  descentRechartIso (X := fun _ : Unit =>
    (affineTildeFunctor (CommRingCat.of B)).obj (affineDescentCoefficientModule data))
    data (affineTildeDescentChartIso data)

set_option maxHeartbeats 825000 in
/-- The double-overlap comparison in the new chart is the associated sheaf of
the original comparison expressed as a scalar extension. -/
theorem affineTildeDescentData_double (data : AffineSingletonDescentData A B) :
    (affineDoubleTransition A B (affineTildeDescentData data)).hom =
      (affineTildePullbackIso (bund (A := A) (B := B) 0)).hom.app (affineDescentCoefficientModule data) ≫
      (affineTildeFunctor (CommRingCat.of B₂)).map (affineDescentScalarExtensionIso data).hom ≫
      (affineTildePullbackIso (bund (A := A) (B := B) 1)).inv.app (affineDescentCoefficientModule data) := by
  let M := affineDescentCoefficientModule data
  let e := affineDescentCoefficientChart data
  let p := affinePullbackFunctor (bund (A := A) (B := B) 0)
  let q := affinePullbackFunctor (bund (A := A) (B := B) 1)
  let c := (affineTildePullbackIso (bund (A := A) (B := B) 0)).app M
  let d := (affineTildePullbackIso (bund (A := A) (B := B) 1)).app M
  let h := (affineDoubleTransition A B data).hom
  let E := affineTildeFunctor (CommRingCat.of B₂)
  let δ := affineDescentScalarExtensionIso data
  let t := c.symm ≪≫ p.mapIso e ≪≫ affineDoubleTransition A B data ≪≫ (q.mapIso e).symm ≪≫ d
  let k := p.map e.hom ≫ h ≫ q.map e.inv
  have equal : E.map δ.hom = t.hom :=
    (affineTildeEquivalence (CommRingCat.of B₂)).fullyFaithfulFunctor.map_preimage t.hom
  have component : t.hom = c.inv ≫ k ≫ d.hom := by
    dsimp only [t, k, h, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.mapIso_inv]
    simp only [Category.assoc]
  change k = c.hom ≫ E.map δ.hom ≫ d.inv
  rw [equal, component]
  simp only [Category.assoc, c.hom_inv_id_assoc, d.hom_inv_id]
  exact (Category.comp_id k).symm

set_option maxHeartbeats 550000 in
/-- Forgetting the normalized double overlap gives the corresponding tilde map. -/
theorem affineTildeDescentData_double_forget (data : AffineSingletonDescentData A B) :
    (forget (Spec (CommRingCat.of B₂))).map (affineDoubleTransition A B (affineTildeDescentData data)).hom =
      (tildePullbackIso (bund (A := A) (B := B) 0)).hom.app (affineDescentCoefficientModule data) ≫
        (tilde.functor (CommRingCat.of B₂)).map (affineDescentScalarExtensionIso data).hom ≫
        (tildePullbackIso (bund (A := A) (B := B) 1)).inv.app (affineDescentCoefficientModule data) := by
  let E := affineTildeFunctor (CommRingCat.of B₂)
  let I := forget (Spec (CommRingCat.of B₂))
  let M := affineDescentCoefficientModule data
  let c := (affineTildePullbackIso (bund (A := A) (B := B) 0)).app M
  let d := (affineTildePullbackIso (bund (A := A) (B := B) 1)).app M
  let δ := (affineDescentScalarExtensionIso data).hom
  have h : (affineDoubleTransition A B (affineTildeDescentData data)).hom = c.hom ≫ E.map δ ≫ d.inv :=
    affineTildeDescentData_double data
  have h' := congrArg I.map h
  change I.map (affineDoubleTransition A B (affineTildeDescentData data)).hom = _
  rw [h', I.map_comp, I.map_comp]
  rfl


end

end SHIGURE.SchemeDescent
