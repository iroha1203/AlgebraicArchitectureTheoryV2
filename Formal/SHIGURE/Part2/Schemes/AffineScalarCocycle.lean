import Formal.SHIGURE.Part2.Schemes.AffinePullHomComparison
import Formal.SHIGURE.Part2.Schemes.AffineOverlapRingDiagram
import Formal.SHIGURE.Part2.Schemes.AffineDescentAssociated

/-! # The geometric triple cocycle in affine scalar extensions -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules TensorProduct
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B
local notation "B₃" => B ⊗[A] (B ⊗[A] B)

private abbrev F := quasiCoherentModulesPseudofunctor
private abbrev forget (X : Scheme.{u}) := (quasiCoherentModulesProperty.prop (.mk (op X))).ι

private abbrev doubleRing (i : Fin 2) := affineDoubleRingHom A B i
private abbrev tripleRing (i : Fin 3) := affineTripleRingHom A B i
private abbrev pairRing (i j : Fin 3) := affinePairRingHom A B i j

/-- Extend the actual double-overlap scalar map to the specified pair of
positions in the triple tensor algebra. -/
def affineDescentPairScalarHom (D : AffineSingletonDescentData A B) (i j : Fin 3) :
    (ModuleCat.extendScalars (tripleRing (A := A) (B := B) i).hom).obj (affineDescentCoefficientModule D) ⟶
      (ModuleCat.extendScalars (tripleRing (A := A) (B := B) j).hom).obj (affineDescentCoefficientModule D) :=
  scalarExtensionPullHomAt (doubleRing (A := A) (B := B) 0).hom
    (doubleRing (A := A) (B := B) 1).hom (pairRing (A := A) (B := B) i j).hom
    (congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of B₃ => k.hom) (affinePairRingHom_comp_left A B i j))
    (congrArg (fun k : CommRingCat.of B ⟶ CommRingCat.of B₃ => k.hom) (affinePairRingHom_comp_right A B i j))
    (affineDescentScalarExtensionIso D).hom

private abbrev geometricPair (D : AffineSingletonDescentData A B) (i j : Fin 3) :=
  pullHom (affineDoubleTransition A B (affineTildeDescentData D)).hom (affinePairProjection A B i j)
    (affineTripleProjection A B i) (affineTripleProjection A B j)
    (affinePairProjection_left A B i j) (affinePairProjection_right A B i j)

set_option maxHeartbeats 750000 in
/-- The original geometric pair transition is the associated module of its
scalar extension, with the original triple projection comparisons. -/
theorem affineDescentPairScalarHom_tilde (D : AffineSingletonDescentData A B) (i j : Fin 3) :
    (forget (Spec (CommRingCat.of B₃))).map (geometricPair D i j) =
      (tildePullbackIso (tripleRing (A := A) (B := B) i)).hom.app (affineDescentCoefficientModule D) ≫
      (tilde.functor (CommRingCat.of B₃)).map (affineDescentPairScalarHom D i j) ≫
      (tildePullbackIso (tripleRing (A := A) (B := B) j)).inv.app (affineDescentCoefficientModule D) :=
  affinePullHom_scalar_at (doubleRing (A := A) (B := B) 0) (doubleRing (A := A) (B := B) 1)
    (pairRing (A := A) (B := B) i j) (affinePairRingHom_comp_left A B i j) (affinePairRingHom_comp_right A B i j)
    (affineDoubleTransition A B (affineTildeDescentData D)).hom (affineDescentScalarExtensionIso D).hom
    (affineTildeDescentData_double_forget D)

private theorem reflect_conjugated_composition {C D : Type*} [Category C] [Category D]
    (G : C ⥤ D) [G.Faithful] {X₀ X₁ X₂ : C} {Y₀ Y₁ Y₂ : D}
    (a : Y₀ ≅ G.obj X₀) (b : Y₁ ≅ G.obj X₁) (c : Y₂ ≅ G.obj X₂)
    (m : X₀ ⟶ X₁) (n : X₁ ⟶ X₂) (p : X₀ ⟶ X₂)
    (h : (a.hom ≫ G.map m ≫ b.inv) ≫ (b.hom ≫ G.map n ≫ c.inv) = a.hom ≫ G.map p ≫ c.inv) :
    m ≫ n = p := by
  apply G.map_injective
  rw [G.map_comp]
  apply (cancel_epi a.hom).1
  apply (cancel_mono c.inv).1
  simpa only [Category.assoc, b.inv_hom_id_assoc] using h

set_option maxHeartbeats 850000 in
/-- The scalar extensions of the original affine descent datum satisfy the
triple cocycle before choosing tensor coordinates for their modules. -/
theorem affineDescentPairScalarHom_cocycle (D : AffineSingletonDescentData A B) (i j k : Fin 3) :
    affineDescentPairScalarHom D i j ≫ affineDescentPairScalarHom D j k = affineDescentPairScalarHom D i k := by
  let T := CommRingCat.of B₃
  let I := forget (Spec T)
  let G := tilde.functor T
  let M := affineDescentCoefficientModule D
  let a := (tildePullbackIso (tripleRing (A := A) (B := B) i)).app M
  let b := (tildePullbackIso (tripleRing (A := A) (B := B) j)).app M
  let c := (tildePullbackIso (tripleRing (A := A) (B := B) k)).app M
  let x := geometricPair D i j
  let y := geometricPair D j k
  let z := geometricPair D i k
  have geometry : x ≫ y = z := affineTensorCocycle A B (affineTildeDescentData D) i j k
  have original : I.map x ≫ I.map y = I.map z :=
    (I.map_comp x y).symm.trans (congrArg I.map geometry)
  let d := affineDescentPairScalarHom D i j
  let e := affineDescentPairScalarHom D j k
  let f := affineDescentPairScalarHom D i k
  have first : I.map x = a.hom ≫ G.map d ≫ b.inv := affineDescentPairScalarHom_tilde D i j
  have second : I.map y = b.hom ≫ G.map e ≫ c.inv := affineDescentPairScalarHom_tilde D j k
  have last : I.map z = a.hom ≫ G.map f ≫ c.inv := affineDescentPairScalarHom_tilde D i k
  rw [first, second, last] at original
  letI : G.Faithful := (tilde.fullyFaithfulFunctor (R := T)).faithful
  exact reflect_conjugated_composition G a b c d e f original

end

end SHIGURE.SchemeDescent
