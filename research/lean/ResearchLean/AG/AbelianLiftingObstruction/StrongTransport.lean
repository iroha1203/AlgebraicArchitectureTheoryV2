import ResearchLean.AG.TransportCoherence.ArbitraryObstruction

/-!
# Transport along one actual strongly opcartesian arrow

G-129 A uses the canonical comparison to transport fiber automorphisms.
This arrow-level API is compared below with the existing path-level whisker.

## Implementation notes

The construction accepts only the original arrow and its strong lifting
property. The transported automorphism and its group laws are derived from
canonical comparison and uniqueness, without a supplied transport map.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uE uB vE vB uG
variable {E : Type uE} {B : Type uB} [Category.{vE} E] [Category.{vB} B]

/-- API: precomposing a strong arrow with a fiber automorphism remains strong. -/
theorem fiberAut_comp_strong (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a : FiberAut r X) : r.IsStronglyCocartesian σ (FiberAut.hom a ≫ f) := by
  letI : r.IsStronglyCocartesian σ f := hf
  letI : r.IsHomLift (𝟙 (r.obj X)) a.1.hom := by
    rw [← a.2]
    infer_instance
  letI : r.IsStronglyCocartesian (𝟙 (r.obj X)) a.1.hom :=
    Functor.IsStronglyCocartesian.of_iso r (𝟙 (r.obj X)) a.1
  simpa only [Category.id_comp, FiberAut.hom] using
    (Functor.IsStronglyCocartesian.comp r :
      r.IsStronglyCocartesian (𝟙 (r.obj X) ≫ σ) (a.1.hom ≫ f))

/-- G-129 A: construct transport from the canonical comparison of actual arrows. -/
noncomputable def fiberTransport (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a : FiberAut r X) : FiberAut r Y :=
  canonicalFiberComparator r σ f (FiberAut.hom a ≫ f) hf
    (fiberAut_comp_strong r f hf a)

/-- API: the defining factorization is the original arrow equation. -/
theorem fiberTransport_fac (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a : FiberAut r X) : f ≫ FiberAut.hom (fiberTransport r f hf a) = FiberAut.hom a ≫ f :=
  canonicalFiberComparator_fac r σ f (FiberAut.hom a ≫ f) hf
    (fiberAut_comp_strong r f hf a)

/-- API: strong uniqueness determines transport from its factorization. -/
theorem fiberTransport_unique (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a : FiberAut r X) (b : FiberAut r Y)
    (h : f ≫ FiberAut.hom b = FiberAut.hom a ≫ f) : b = fiberTransport r f hf a :=
  FiberAut.ext_of_strong_fac f hf b _ (h.trans (fiberTransport_fac r f hf a).symm)

/-- API: transport preserves the identity automorphism. -/
theorem fiberTransport_one (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f) :
    fiberTransport r f hf 1 = 1 := by
  symm
  apply fiberTransport_unique
  change f ≫ 𝟙 Y = 𝟙 X ≫ f
  simp

/-- API: uniqueness derives the group law, including the categorical product order. -/
theorem fiberTransport_mul (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a b : FiberAut r X) :
    fiberTransport r f hf (a * b) = fiberTransport r f hf a * fiberTransport r f hf b := by
  symm
  apply fiberTransport_unique
  change f ≫ (FiberAut.hom (fiberTransport r f hf b) ≫
      FiberAut.hom (fiberTransport r f hf a)) =
    (FiberAut.hom b ≫ FiberAut.hom a) ≫ f
  rw [← Category.assoc, fiberTransport_fac, Category.assoc,
    fiberTransport_fac, ← Category.assoc]

/-- G-129 A: fiber transport as a derived group homomorphism. -/
noncomputable def fiberTransportHom (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f) :
    FiberAut r X →* FiberAut r Y where
  toFun := fiberTransport r f hf
  map_one' := fiberTransport_one r f hf
  map_mul' := fiberTransport_mul r f hf

/-- API: evaluating the homomorphism preserves the defining arrow equation. -/
theorem fiberTransportHom_fac (r : E ⥤ B) {X Y : E}
    {σ : r.obj X ⟶ r.obj Y} (f : X ⟶ Y) (hf : r.IsStronglyCocartesian σ f)
    (a : FiberAut r X) :
    f ≫ FiberAut.hom (fiberTransportHom r f hf a) = FiberAut.hom a ≫ f :=
  fiberTransport_fac r f hf a

/-- API connection: transport of any reselected path is the existing whisker map. -/
theorem fiberTransportHom_eq_whisker {K : FiniteTransportTwoPresentation.{uG}}
    (r : E ⥤ B) (data : LiftData K r) (current : EdgeReselection data)
    {i j : K.Vertex} (path : K.Path i j) :
    fiberTransportHom r (reselectedPathLift data current path)
      (reselectedPathLift_isStronglyCocartesian data current path) =
      whiskerFiberAutHom data current path := by
  apply MonoidHom.ext
  intro a
  exact (fiberTransport_unique r (reselectedPathLift data current path)
    (reselectedPathLift_isStronglyCocartesian data current path) a
    (whiskerFiberAutHom data current path a)
    (Arbitrary.whiskerFiberAut_fac data current a path)).symm

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
