import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationUniversalFactor

/-!
# Strong cartesianness of realization-exact upper normalizations

The complete factor contract is lifted to total refinement-geometry
morphisms.  Its two carrier cancellation directions prove factorization and
recovery; the standard contract extensionality argument then gives uniqueness
and the strongly Cartesian universal property.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence

set_option maxHeartbeats 3000000

private def refinementGeomReadHomCastBase
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {f g : RefinementGeometryBaseHom G H} (hfg : f = g)
    (F : RefinementGeomReadHom G H f) : RefinementGeomReadHom G H g := by
  cases hfg
  exact F

private theorem refinementGeomReadHomCastBase_heq
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {f g : RefinementGeometryBaseHom G H} (hfg : f = g)
    (F : RefinementGeomReadHom G H f) :
    HEq (refinementGeomReadHomCastBase hfg F) F := by
  cases hfg
  rfl

private theorem refinementGeomReadHomComp_castBase_heq
    {U : AtomCarrier.{u}} {G H K : GeometryPackage.{u, v} U}
    {f f' : RefinementGeometryBaseHom G H}
    {g : RefinementGeometryBaseHom H K} (hff' : f = f')
    (F : RefinementGeomReadHom G H f)
    (T : RefinementGeomReadHom H K g) :
    HEq (RefinementGeomReadHom.comp
      (refinementGeomReadHomCastBase hff' F) T)
      (RefinementGeomReadHom.comp F T) := by
  cases hff'
  rfl

/-- Total canonical factor through a realization-exact upper normalization. -/
noncomputable def upperPairPullCartesianFactor
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx)
    {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩ ⟨P⟩)
    (h : RefinementGeometryHom K G)
    (hbase : h.base = g.comp f) :
    RefinementGeometryHom K
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward) where
  base := g
  geometry := upperPairPullCartesianFactorGeomCore G f backward
    forward_backward backward_forward R hctx g (hbase ▸ h.geometry)

/-- The canonical total factor composes with the direct normalization leg to
the supplied compatible morphism. -/
theorem upperPairPullCartesianFactor_fac
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx)
    {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩ ⟨P⟩)
    (h : RefinementGeometryHom K G)
    (hbase : h.base = g.comp f) :
    RefinementGeometryHom.comp
        (upperPairPullCartesianFactor G f backward forward_backward
          backward_forward R hctx g h hbase)
        (upperPairPullRefinementGeometryHom G f backward backward_forward
          R.homSupply hctx) = h := by
  apply RefinementGeometryHom.ext
  · exact hbase.symm
  · let T : RefinementGeomReadHom K G (g.comp f) := hbase ▸ h.geometry
    have hgeometry :
        (RefinementGeometryHom.comp
          (upperPairPullCartesianFactor G f backward forward_backward
            backward_forward R hctx g h hbase)
          (upperPairPullRefinementGeometryHom G f backward backward_forward
            R.homSupply hctx)).geometry = T := by
      apply RefinementGeomReadHom.ext
      · rfl
      · apply heq_of_eq
        funext W support
        exact R.support_forward_inverse
          (refinementGeometryContextForward (G := K)
            (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward) g W) _
      · apply heq_of_eq
        funext W axis
        exact R.axis_forward_inverse
          (refinementGeometryContextForward (G := K)
            (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward) g W) _
      · apply heq_of_eq
        funext W observable
        exact R.observable_forward_inverse
          (refinementGeometryContextForward (G := K)
            (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
              G f.upper backward) g W) _
    exact (heq_of_eq hgeometry).trans (by
      dsimp [T]
      exact eqRec_heq hbase h.geometry)

/-- Factoring a composite through the direct normalization leg recovers its
first complete geometry contract. -/
theorem upperPairPullCartesianFactorGeomCore_of_composite
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx)
    {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩ ⟨P⟩)
    (T : RefinementGeomReadHom K
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward) g) :
    upperPairPullCartesianFactorGeomCore G f backward forward_backward
        backward_forward R hctx g
        (RefinementGeomReadHom.comp T
          (upperPairPullRefinementGeomReadHom G f backward backward_forward
            R.homSupply hctx)) = T := by
  apply RefinementGeomReadHom.ext
  · rfl
  · apply heq_of_eq
    funext W support
    exact R.support_inverse_forward
      (refinementGeometryContextForward (G := K)
        (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) g W) _
  · apply heq_of_eq
    funext W axis
    exact R.axis_inverse_forward
      (refinementGeometryContextForward (G := K)
        (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) g W) _
  · apply heq_of_eq
    funext W observable
    exact R.observable_inverse_forward
      (refinementGeometryContextForward (G := K)
        (H := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) g W) _

/-- The canonical total factor is unique over its specified lower package
map. -/
theorem upperPairPullCartesianFactor_unique
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx)
    {K : GeometryPackage.{u, v} U}
    (g : RefinementPackageHom ⟨K.core⟩ ⟨P⟩)
    (h : RefinementGeometryHom K G)
    (hbase : h.base = g.comp f)
    (k : RefinementGeometryHom K
      (UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
        G f.upper backward))
    (hkbase : k.base = g)
    (hkfac : RefinementGeometryHom.comp k
      (upperPairPullRefinementGeometryHom G f backward backward_forward
        R.homSupply hctx) = h) :
    k = upperPairPullCartesianFactor G f backward forward_backward
      backward_forward R hctx g h hbase := by
  let kGeometry := refinementGeomReadHomCastBase hkbase k.geometry
  let T : RefinementGeomReadHom K G (g.comp f) := hbase ▸ h.geometry
  have hnormalized : RefinementGeomReadHom.comp kGeometry
      (upperPairPullRefinementGeomReadHom G f backward backward_forward
        R.homSupply hctx) = T := by
    apply eq_of_heq
    have hT : HEq h.geometry T := by
      dsimp [T]
      exact (eqRec_heq hbase h.geometry).symm
    exact ((refinementGeomReadHomComp_castBase_heq hkbase k.geometry
      (upperPairPullRefinementGeomReadHom G f backward backward_forward
        R.homSupply hctx)).trans
      (RefinementGeometryHom.geometry_heq hkfac)).trans hT
  have hkGeometry : kGeometry =
      upperPairPullCartesianFactorGeomCore G f backward forward_backward
        backward_forward R hctx g T := by
    calc
      kGeometry = upperPairPullCartesianFactorGeomCore G f backward
          forward_backward backward_forward R hctx g
          (RefinementGeomReadHom.comp kGeometry
            (upperPairPullRefinementGeomReadHom G f backward backward_forward
              R.homSupply hctx)) :=
        (upperPairPullCartesianFactorGeomCore_of_composite G f backward
          forward_backward backward_forward R hctx g kGeometry).symm
      _ = upperPairPullCartesianFactorGeomCore G f backward forward_backward
          backward_forward R hctx g T :=
        congrArg (upperPairPullCartesianFactorGeomCore G f backward
          forward_backward backward_forward R hctx g) hnormalized
  apply RefinementGeometryHom.ext
  · exact hkbase
  · exact (refinementGeomReadHomCastBase_heq hkbase k.geometry).symm.trans
      (heq_of_eq hkGeometry)

/-- A direct realization-exact normalization hom is strongly Cartesian over
the refinement-geometry projection. -/
theorem upperPairPullRefinementGeometryHom_isStronglyCartesian
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (G : GeometryPackage.{u, v} U)
    (f : RefinementPackageHom ⟨P⟩ ⟨G.core⟩)
    (backward : SignedExactCoreReadingHom G.core P)
    (forward_backward : f.upper.comp backward =
      SignedExactCoreReadingHom.refl P)
    (backward_forward : backward.comp f.upper =
      SignedExactCoreReadingHom.refl G.core)
    (R : RealizationExactUpperEquivalence
      (refinementExactUpperEquivalence f backward
        forward_backward backward_forward))
    (hctx : ∀ V : G.site.category,
      (refinementGeometryContextForward
        (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
          G f.upper backward) (H := G) f
        (refinementGeometryContextBackward
          (G := UpperGeometryCleavage.pullGeometryPackageAlongUpperPair
            G f.upper backward) (H := G) f V)).ctx = V.ctx) :
    (refinementGeometryProjection U).IsStronglyCartesian f
      (upperPairPullRefinementGeometryHom G f backward backward_forward
        R.homSupply hctx) := by
  let lift := upperPairPullRefinementGeometryHom G f backward backward_forward
    R.homSupply hctx
  letI : (refinementGeometryProjection U).IsHomLift f lift := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementGeometryProjection U) _ lift rfl rfl
    rfl
  apply CategoryTheory.Functor.IsStronglyCartesian.mk
  intro K g h hLift
  have hbase : h.base = g.comp f := by
    exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (refinementGeometryProjection U) (g.comp f) h).symm
  let factor := upperPairPullCartesianFactor G f backward forward_backward
    backward_forward R hctx g h hbase
  refine ⟨factor, ?_, ?_⟩
  · constructor
    · rw [← show factor.base = g from rfl]
      change (refinementGeometryProjection U).IsHomLift
        ((refinementGeometryProjection U).map factor) factor
      infer_instance
    · exact upperPairPullCartesianFactor_fac G f backward forward_backward
        backward_forward R hctx g h hbase
  · intro factor' hfactor'
    apply upperPairPullCartesianFactor_unique G f backward forward_backward
      backward_forward R hctx g h hbase factor'
    · letI : (refinementGeometryProjection U).IsHomLift g factor' := hfactor'.1
      exact (CategoryTheory.IsHomLift.eq_of_isHomLift
        (p := refinementGeometryProjection U) g factor').symm
    · exact hfactor'.2

namespace UpperGeometryCompatibleProblemInputData

/-- The premise-free finite base direct normalization leg is strongly
Cartesian. -/
theorem canonicalAuthoredBaseRouteGeometryHomAt_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.canonicalAuthoredBaseRouteGeometryHomAt i) :=
  upperPairPullRefinementGeometryHom_isStronglyCartesian
    (input.sourceGeometry i).package
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteUpperEquivalenceAt i).backward
    (input.generatedBaseRouteUpperEquivalenceAt i).forward_backward
    (input.generatedBaseRouteUpperEquivalenceAt i).backward_forward
    (input.generatedBaseRouteRealizationExactAt i)
    (input.canonicalAuthoredBaseRouteContextForward_backwardAt i)

/-- The premise-free finite pulled direct normalization leg is strongly
Cartesian. -/
theorem canonicalAuthoredPulledRouteGeometryHomAt_isStronglyCartesian
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}}
    {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.canonicalAuthoredPulledRouteGeometryHomAt i) :=
  upperPairPullRefinementGeometryHom_isStronglyCartesian
    (input.sourceGeometry i).package
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteUpperEquivalenceAt i).backward
    (input.generatedPulledRouteUpperEquivalenceAt i).forward_backward
    (input.generatedPulledRouteUpperEquivalenceAt i).backward_forward
    (input.generatedPulledRouteRealizationExactAt i)
    (input.canonicalAuthoredPulledRouteContextForward_backwardAt i)

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
