import Formal.SHIGURE.Part2.Schemes.QuasiCoherentAlgebraOnStack
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentSheafAlgebras

/-! # Relative spectrum data from quasi-coherent algebra sheaves on the stack

The equivalence with affine-site sheaves from B.7 supplies the chart data.
Every original transition is transported along the corresponding
reconstruction isomorphisms, including its pullback mate.
-/

namespace SHIGURE.SchemeDescent.QuasiCoherentAlgebraOnStack

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u a b

variable {F : Pseudofunctor (LocallyDiscrete (Scheme.{u})ᵒᵖ) Cat.{a,b}}

/-- Use the localization of the original quasi-coherent algebra sheaves on
affine opens, with their coherently specified transitions. The Cartesian
condition concerns the adjoint pullback of the original sheaf transition. -/
def ofSheaves (D : ∀ T : CoGrothendieck F, Under T.base.sheaf)
    (qc : ∀ T, IsQuasiCoherentSheafAlgebra (D T))
    (m : ∀ {S T : CoGrothendieck F} (f : S ⟶ T),
      D T ⟶ (pushforwardAlgebra f.base).obj (D S))
    (identity : ∀ T, m (𝟙 T) = (pushforwardAlgebraId T.base).inv.app (D T))
    (comp : ∀ {R S T : CoGrothendieck F} (f : R ⟶ S) (g : S ⟶ T),
      m (f ≫ g) = m g ≫ (pushforwardAlgebra g.base).map (m f) ≫
        (pushforwardAlgebraComp g.base f.base).hom.app (D R))
    (cartesian : ∀ {S T : Scheme.{u}} (f : S ⟶ T) (N : F.obj (.mk (op T))),
      IsIso (((pullbackAlgebraAdjunction f).homEquiv (D ⟨T, N⟩)
        (D (CoGrothendieck.domainCartesianLift N f))).symm
          (m (CoGrothendieck.cartesianLift N f)))) : QuasiCoherentAlgebraOnStack F := by
  let A (T : CoGrothendieck F) := QuasiCoherentAlgebra.ofSheaf (D T) (qc T)
  let e (T : CoGrothendieck F) := QuasiCoherentAlgebra.ofSheaf_algebraSheafIso (D T) (qc T)
  let transition {S T : CoGrothendieck F} (f : S ⟶ T) :
      (A T).algebraSheaf ⟶ (pushforwardAlgebra f.base).obj (A S).algebraSheaf :=
    (e T).hom ≫ m f ≫ (pushforwardAlgebra f.base).map (e S).inv
  refine ⟨A, @transition, ?_, ?_, ?_⟩
  · intro T
    let P := pushforwardAlgebra (𝟙 T.base)
    let E := pushforwardAlgebraId T.base
    change (e T).hom ≫ m (𝟙 T) ≫ P.map (e T).inv = E.inv.app (A T).algebraSheaf
    have natural : (e T).hom ≫ E.inv.app (D T) =
        E.inv.app (A T).algebraSheaf ≫ P.map (e T).hom :=
      E.inv.naturality (e T).hom
    rw [identity, ← Category.assoc, natural]
    simp only [Category.assoc, ← P.map_comp, Iso.hom_inv_id, P.map_id]
    exact Category.comp_id _
  · intro R S T f g
    let P := pushforwardAlgebra f.base
    let Q := pushforwardAlgebra g.base
    let E := pushforwardAlgebraComp g.base f.base
    change (e T).hom ≫ m (f ≫ g) ≫ (pushforwardAlgebra (f.base ≫ g.base)).map (e R).inv =
      ((e T).hom ≫ m g ≫ Q.map (e S).inv) ≫
        Q.map ((e S).hom ≫ m f ≫ P.map (e R).inv) ≫ E.hom.app (A R).algebraSheaf
    rw [comp]
    simp only [Functor.map_comp, Category.assoc]
    rw [← Q.map_comp_assoc, Iso.inv_hom_id, Q.map_id, Category.id_comp]
    have natural : E.hom.app (D R) ≫ (pushforwardAlgebra (f.base ≫ g.base)).map (e R).inv =
        Q.map (P.map (e R).inv) ≫ E.hom.app (A R).algebraSheaf :=
      (E.hom.naturality (e R).inv).symm
    rw [natural]
  · intro S T f N
    let K : CoGrothendieck F := ⟨T, N⟩
    let J := CoGrothendieck.domainCartesianLift N f
    let adj := pullbackAlgebraAdjunction f
    let g := CoGrothendieck.cartesianLift N f
    let h := (adj.homEquiv (D K) (D J)).symm (m g)
    haveI : IsIso h := cartesian f N
    change IsIso ((adj.homEquiv (A K).algebraSheaf (A J).algebraSheaf).symm
      ((e K).hom ≫ m g ≫ (pushforwardAlgebra f).map (e J).inv))
    rw [adj.homEquiv_naturality_left_symm, adj.homEquiv_naturality_right_symm]
    change IsIso ((pullbackAlgebra f).map (e K).hom ≫ h ≫ (e J).inv)
    infer_instance


end

end SHIGURE.SchemeDescent.QuasiCoherentAlgebraOnStack
