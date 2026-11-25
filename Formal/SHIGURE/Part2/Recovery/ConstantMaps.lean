import Formal.SHIGURE.Part2.Realizations.ConstantStructures
import Formal.SHIGURE.Part1.StructureMaps
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Recovering all maps of constant carriers

A map of the carrier sheaves is read on the identity test over the base.
Connectedness makes the image of a native state constant on that test.
Naturality then determines its value on the open fibers of every section.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {X Y : Type u}

/-- The test object whose structural morphism is the identity. -/
private def baseTest (S : Scheme.{u}) : Over S := Over.mk (𝟙 S)

/-- Every relative test has its structural map to the identity test. -/
private def toBaseTest (T : Over S) : T ⟶ baseTest S :=
  Over.homMk T.hom (by change T.hom ≫ 𝟙 S = T.hom; simp)

/-- Read a map of constant carriers on the native sections of the base. -/
def readConstantCarrierMap [Nonempty S] (f : constantCarrier S X ⟶ constantCarrier S Y) (x : X) : Y :=
  let g : LocallyConstant S Y := f.val.app (op (baseTest S)) (nativeState S (baseTest S) x)
  g (Classical.choice inferInstance)

/-- The constant carrier map returns its original function when evaluated at native sections. -/
@[simp]
theorem readConstantCarrierMap_constantCarrierMap [Nonempty S] (f : X → Y) :
    readConstantCarrierMap (constantCarrierMap S f) = f := rfl

/-- A sheaf map sends a native section on any test to the reconstructed native state. -/
theorem constantCarrierMap_app_nativeState [PreconnectedSpace S] [Nonempty S]
    (f : constantCarrier S X ⟶ constantCarrier S Y) (T : Over S) (x : X) :
    f.val.app (op T) (nativeState S T x) = nativeState S T (readConstantCarrierMap f x) := by
  let h := toBaseTest T
  let b : LocallyConstant S Y := f.val.app (op (baseTest S)) (nativeState S (baseTest S) x)
  have hn := FunctorToTypes.naturality _ _ f.val h.op (nativeState S (baseTest S) x)
  rw [nativeState_restrict] at hn
  have he : b = LocallyConstant.const S (readConstantCarrierMap f x) :=
    b.eq_const (Classical.choice inferInstance)
  rw [hn]
  change (constantCarrier S Y).val.map h.op b = _
  rw [he]
  rfl

/-- Over a connected nonempty base all maps of the carrier sheaves are actual native maps. -/
theorem constantCarrierMap_readConstantCarrierMap [PreconnectedSpace S] [Nonempty S]
    (f : constantCarrier S X ⟶ constantCarrier S Y) :
    constantCarrierMap S (readConstantCarrierMap f) = f := by
  ext T a
  let c : LocallyConstant T.unop.left X := a
  let d : LocallyConstant T.unop.left Y := f.val.app T a
  change LocallyConstant.map (readConstantCarrierMap f) c = d
  apply LocallyConstant.ext
  intro t
  let O : T.unop.left.Opens := ⟨c ⁻¹' {c t}, c.isLocallyConstant {c t}⟩
  let U := Over.mk (O.ι ≫ T.unop.hom)
  let g : U ⟶ T.unop := Over.homMk O.ι
  let u : U.left := ⟨t, rfl⟩
  have hc : (constantCarrier S X).val.map g.op a = nativeState S U (c t) := by
    let h : LocallyConstant U.left X := (constantCarrier S X).val.map g.op a
    change h = LocallyConstant.const U.left (c t)
    exact LocallyConstant.ext (fun z => z.property)
  have hn := FunctorToTypes.naturality _ _ f.val g.op a
  rw [hc, constantCarrierMap_app_nativeState] at hn
  exact congrArg (fun b : LocallyConstant U.left Y => b u) hn

/-- All arrows of the constant carrier sheaves correspond to native functions. -/
def constantCarrierMapsEquiv [PreconnectedSpace S] [Nonempty S] :
    (X → Y) ≃ (constantCarrier S X ⟶ constantCarrier S Y) where
  toFun := constantCarrierMap S
  invFun := readConstantCarrierMap
  left_inv := readConstantCarrierMap_constantCarrierMap
  right_inv := constantCarrierMap_readConstantCarrierMap

end SHIGURE.Copying
