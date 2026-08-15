import ResearchLean.AG.GeometryTransport.Factorization

/-!
# Uniqueness of geometry-stage opcartesian lifts

This module instantiates categorical uniqueness for the canonical G-108 lift.
The resulting isomorphism is retained together with its two fiber equations;
the remainder of the file exposes the reversible geometry components carried
by those two legs.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-- An equality-induced core-package morphism uses the identity Atom map. -/
@[simp] theorem PackageTotalHom.eqToHom_atomEquiv {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (h : P = Q) :
    (eqToHom h : PackageTotalHom P Q).upper.atomEquiv = Equiv.refl U.Atom := by
  subst h
  rfl

/-- A geometry-category isomorphism whose two legs remain in one core fiber. -/
structure GeometryFiberInnerIso {U : AtomCarrier.{u}}
    (C Q : GeometryPackage.{u, v} U) (hcore : C.core = Q.core) where
  iso : C ≅ Q
  hom_base_eq : iso.hom.base =
    (eqToHom hcore : PackageTotalHom C.core Q.core)
  inv_base_eq : iso.inv.base =
    (eqToHom hcore.symm : PackageTotalHom Q.core C.core)

namespace GeometryFiberInnerIso

/-- Forward geometry data normalized to the equality-induced fiber map. -/
noncomputable def homGeometry {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) :
    GeomReadHom C Q (eqToHom hcore) :=
  GeomReadHom.castBase e.hom_base_eq e.iso.hom.geometry

/-- Reverse geometry data normalized to the reverse equality-induced map. -/
noncomputable def invGeometry {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) :
    GeomReadHom Q C (eqToHom hcore.symm) :=
  GeomReadHom.castBase e.inv_base_eq e.iso.inv.geometry

/-- The coefficient component of a fiber isomorphism is a ring equivalence. -/
noncomputable def coefficientEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) : C.Coefficient ≃+* Q.Coefficient where
  toFun := e.iso.hom.geometry.coefficientHom
  invFun := e.iso.inv.geometry.coefficientHom
  left_inv x := by
    have h := congrArg
      (fun k : C ⟶ C => (show GeometryTotalHom C C from k).geometry.coefficientHom x)
      e.iso.hom_inv_id
    exact h
  right_inv x := by
    have h := congrArg
      (fun k : Q ⟶ Q => (show GeometryTotalHom Q Q from k).geometry.coefficientHom x)
      e.iso.inv_hom_id
    exact h
  map_mul' x y := e.iso.hom.geometry.coefficientHom.map_mul x y
  map_add' x y := e.iso.hom.geometry.coefficientHom.map_add x y

/-! The nine selected coverage predicates are reflected as well as preserved. -/

theorem requiredSupport_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (atom : U.Atom) :
    C.geometry.requirements.requiredSupport atom ↔
      Q.geometry.requirements.requiredSupport
        ((eqToHom hcore : PackageTotalHom C.core Q.core).upper.atomEquiv atom) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.requiredSupport atom
  · intro h
    simpa using e.invGeometry.coverage.requiredSupport atom h

theorem requiredEquationCoordinate_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (coordinate : C.site.equationSystem.RequiredCoordinate) :
    C.geometry.requirements.requiredEquationCoordinate coordinate ↔
      Q.geometry.requirements.requiredEquationCoordinate
        (requiredCoordinateMap (eqToHom hcore) coordinate) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.requiredEquationCoordinate coordinate
  · intro h
    simpa [requiredCoordinateMap] using
      e.invGeometry.coverage.requiredEquationCoordinate coordinate h

theorem selectedViolationWitness_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (coordinate : C.site.equationSystem.Coordinate) :
    C.geometry.requirements.selectedViolationWitness coordinate ↔
      Q.geometry.requirements.selectedViolationWitness
        (equationCoordinateMap (eqToHom hcore) coordinate) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.selectedViolationWitness coordinate
  · intro h
    simpa [equationCoordinateMap] using
      e.invGeometry.coverage.selectedViolationWitness coordinate h

theorem requiredAxis_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (axis : C.site.signature.Axis) :
    C.geometry.requirements.requiredAxis axis ↔
      Q.geometry.requirements.requiredAxis
        ((eqToHom hcore : PackageTotalHom C.core Q.core).upper.axisMap axis) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.requiredAxis axis
  · intro h
    simpa using e.invGeometry.coverage.requiredAxis axis h

theorem supportVisibleOn_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (W : Site.ArchCtx C.core.object) (atom : U.Atom) :
    C.geometry.requirements.supportVisibleOn W atom ↔
      Q.geometry.requirements.supportVisibleOn
        (contextMap (eqToHom hcore) W)
        ((eqToHom hcore : PackageTotalHom C.core Q.core).upper.atomEquiv atom) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.supportVisibleOn W atom
  · intro h
    simpa [contextMap] using e.invGeometry.coverage.supportVisibleOn W atom h

theorem equationCoordinateVisibleOn_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (W : Site.ArchCtx C.core.object)
    (coordinate : C.site.equationSystem.RequiredCoordinate) :
    C.geometry.requirements.equationCoordinateVisibleOn W coordinate ↔
      Q.geometry.requirements.equationCoordinateVisibleOn
        (contextMap (eqToHom hcore) W)
        (requiredCoordinateMap (eqToHom hcore) coordinate) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.equationCoordinateVisibleOn W coordinate
  · intro h
    simpa [contextMap, requiredCoordinateMap] using
      e.invGeometry.coverage.equationCoordinateVisibleOn W coordinate h

theorem violationWitnessVisibleOn_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (W : Site.ArchCtx C.core.object)
    (coordinate : C.site.equationSystem.Coordinate) :
    C.geometry.requirements.violationWitnessVisibleOn W coordinate ↔
      Q.geometry.requirements.violationWitnessVisibleOn
        (contextMap (eqToHom hcore) W)
        (equationCoordinateMap (eqToHom hcore) coordinate) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.violationWitnessVisibleOn W coordinate
  · intro h
    simpa [contextMap, equationCoordinateMap] using
      e.invGeometry.coverage.violationWitnessVisibleOn W coordinate h

theorem axisReadableOn_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (W : Site.ArchCtx C.core.object) (axis : C.site.signature.Axis) :
    C.geometry.requirements.axisReadableOn W axis ↔
      Q.geometry.requirements.axisReadableOn
        (contextMap (eqToHom hcore) W)
        ((eqToHom hcore : PackageTotalHom C.core Q.core).upper.axisMap axis) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.axisReadableOn W axis
  · intro h
    simpa [contextMap] using e.invGeometry.coverage.axisReadableOn W axis h

theorem boundaryVisibleOn_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (W V : Site.ArchCtx C.core.object) :
    C.geometry.requirements.boundaryVisibleOn W V ↔
      Q.geometry.requirements.boundaryVisibleOn
        (contextMap (eqToHom hcore) W) (contextMap (eqToHom hcore) V) := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  constructor
  · exact e.homGeometry.coverage.boundaryVisibleOn W V
  · intro h
    simpa [contextMap] using e.invGeometry.coverage.boundaryVisibleOn W V h

/-- The selected overlap objects are isomorphic, not artificially identified. -/
noncomputable def selectedOverlapIso {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore)
    (base left right : Site.ArchCtx Q.core.object) :
    contextForward (eqToHom hcore)
        ⟨C.geometry.overlap.overlap
          (contextBackwardMap (eqToHom hcore) base)
          (contextBackwardMap (eqToHom hcore) left)
          (contextBackwardMap (eqToHom hcore) right)⟩ ≅
      (⟨Q.geometry.overlap.overlap base left right⟩ : Q.site.category) :=
  e.homGeometry.overlap.overlapIso base left right

/-- The complete forward raw restriction system is the required reindexing
and coefficient base change; restriction naturality is part of this equality. -/
theorem raw_forward_eq {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) :
    Q.raw = rawTransport (eqToHom hcore) e.homGeometry.coefficientHom :=
  e.homGeometry.raw_eq

/-- The reverse raw comparison is supplied by the inverse leg. -/
theorem raw_inverse_eq {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) :
    C.raw = rawTransport (eqToHom hcore.symm) e.invGeometry.coefficientHom :=
  e.invGeometry.raw_eq

/-- Coordinate presentations are changed only by a reversible display map. -/
noncomputable def coordinatePresentationEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    (C.raw.coordFamily W).Coord ≃
      (Q.raw.coordFamily
        ⟨contextMap (eqToHom hcore) W.ctx⟩).Coord := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  exact Equiv.cast (congrArg
    (fun raw => (raw.coordFamily W).Coord) e.raw_forward_eq).symm

/-- Structural-relation presentations are likewise reversibly displayed. -/
noncomputable def relationPresentationEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    (C.raw.relationFamily W).Relation ≃
      (Q.raw.relationFamily
        ⟨contextMap (eqToHom hcore) W.ctx⟩).Relation := by
  rcases C with ⟨Ccore, Cgeometry, CCoefficient, CcommRing, Craw⟩
  rcases Q with ⟨Qcore, Qgeometry, QCoefficient, QcommRing, Qraw⟩
  dsimp at hcore
  cases hcore
  exact Equiv.cast (congrArg
    (fun raw => (raw.relationFamily W).Relation) e.raw_forward_eq).symm

/-! Reversible context-local realization carriers. -/

/-- The context endpoint of the forward comparison followed by the reverse
comparison is the original context. -/
theorem homInvContext_eq {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    contextForward e.iso.inv.base (contextForward e.iso.hom.base W) = W := by
  have h := congrArg
    (fun k : C ⟶ C => contextForward
      (show GeometryTotalHom C C from k).base W) e.iso.hom_inv_id
  exact h

/-- The reverse comparison followed by the forward comparison fixes target
contexts. -/
theorem invHomContext_eq {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : Q.site.category) :
    contextForward e.iso.hom.base (contextForward e.iso.inv.base W) = W := by
  have h := congrArg
    (fun k : Q ⟶ Q => contextForward
      (show GeometryTotalHom Q Q from k).base W) e.iso.inv_hom_id
  exact h

private theorem support_eq_of_sigma_eq {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder}
    {support : W.ctx.Support} {support' : V.ctx.Support}
    (h : (⟨W, support⟩ : Σ X, X.ctx.Support) = ⟨V, support'⟩) :
    supportEquivOfContextEq (congrArg Sigma.fst h) support = support' := by
  cases h
  rfl

private theorem axis_eq_of_sigma_eq {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder}
    {axis : W.ctx.Axis} {axis' : V.ctx.Axis}
    (h : (⟨W, axis⟩ : Σ X, X.ctx.Axis) = ⟨V, axis'⟩) :
    axisEquivOfContextEq (congrArg Sigma.fst h) axis = axis' := by
  cases h
  rfl

private theorem observable_eq_of_sigma_eq {U : AtomCarrier.{u}}
    {P : AATCorePackage U}
    {W V : Site.ContextCategoryObject P.contextPreorder}
    {observable : W.ctx.Observable} {observable' : V.ctx.Observable}
    (h : (⟨W, observable⟩ : Σ X, X.ctx.Observable) = ⟨V, observable'⟩) :
    observableEquivOfContextEq (congrArg Sigma.fst h) observable = observable' := by
  cases h
  rfl

/-- The support comparison family of a fiber isomorphism is pointwise an
equivalence. -/
noncomputable def supportComparisonEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    W.ctx.Support ≃ (contextForward e.iso.hom.base W).ctx.Support where
  toFun := e.iso.hom.geometry.supportComp W
  invFun support := supportEquivOfContextEq (e.homInvContext_eq W)
    (e.iso.inv.geometry.supportComp (contextForward e.iso.hom.base W) support)
  left_inv support := by
    have hpair := congrArg
      (fun k : C ⟶ C =>
        (⟨contextForward (show GeometryTotalHom C C from k).base W,
          (show GeometryTotalHom C C from k).geometry.supportComp W support⟩ :
          Σ X, X.ctx.Support)) e.iso.hom_inv_id
    exact support_eq_of_sigma_eq hpair
  right_inv support := by
    let backSupport := e.iso.inv.geometry.supportComp
      (contextForward e.iso.hom.base W) support
    have hpair := congrArg
      (fun k : Q ⟶ Q =>
        (⟨contextForward (show GeometryTotalHom Q Q from k).base
            (contextForward e.iso.hom.base W),
          (show GeometryTotalHom Q Q from k).geometry.supportComp
            (contextForward e.iso.hom.base W) support⟩ :
          Σ X, X.ctx.Support)) e.iso.inv_hom_id
    have hcomposite := support_eq_of_sigma_eq hpair
    calc
      e.iso.hom.geometry.supportComp W
          (supportEquivOfContextEq (e.homInvContext_eq W) backSupport) =
          supportEquivOfContextEq
            (congrArg (fun X => contextForward e.iso.hom.base X)
              (e.homInvContext_eq W))
            (e.iso.hom.geometry.supportComp
              (contextForward e.iso.inv.base
                (contextForward e.iso.hom.base W)) backSupport) := by
            exact (supportEquivOfContextEq_family
              (fun X => contextForward e.iso.hom.base X)
              e.iso.hom.geometry.supportComp (e.homInvContext_eq W)
              backSupport).symm
      _ = support := by
        exact hcomposite

/-- The axis comparison family is pointwise an equivalence. -/
noncomputable def axisComparisonEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    W.ctx.Axis ≃ (contextForward e.iso.hom.base W).ctx.Axis where
  toFun := e.iso.hom.geometry.axisComp W
  invFun axis := axisEquivOfContextEq (e.homInvContext_eq W)
    (e.iso.inv.geometry.axisComp (contextForward e.iso.hom.base W) axis)
  left_inv axis := by
    have hpair := congrArg
      (fun k : C ⟶ C =>
        (⟨contextForward (show GeometryTotalHom C C from k).base W,
          (show GeometryTotalHom C C from k).geometry.axisComp W axis⟩ :
          Σ X, X.ctx.Axis)) e.iso.hom_inv_id
    exact axis_eq_of_sigma_eq hpair
  right_inv axis := by
    let backAxis := e.iso.inv.geometry.axisComp
      (contextForward e.iso.hom.base W) axis
    have hpair := congrArg
      (fun k : Q ⟶ Q =>
        (⟨contextForward (show GeometryTotalHom Q Q from k).base
            (contextForward e.iso.hom.base W),
          (show GeometryTotalHom Q Q from k).geometry.axisComp
            (contextForward e.iso.hom.base W) axis⟩ :
          Σ X, X.ctx.Axis)) e.iso.inv_hom_id
    have hcomposite := axis_eq_of_sigma_eq hpair
    calc
      e.iso.hom.geometry.axisComp W
          (axisEquivOfContextEq (e.homInvContext_eq W) backAxis) =
          axisEquivOfContextEq
            (congrArg (fun X => contextForward e.iso.hom.base X)
              (e.homInvContext_eq W))
            (e.iso.hom.geometry.axisComp
              (contextForward e.iso.inv.base
                (contextForward e.iso.hom.base W)) backAxis) := by
            exact (axisEquivOfContextEq_family
              (fun X => contextForward e.iso.hom.base X)
              e.iso.hom.geometry.axisComp (e.homInvContext_eq W) backAxis).symm
      _ = axis := hcomposite

/-- The observable comparison family is pointwise an equivalence. -/
noncomputable def observableComparisonEquiv {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category) :
    W.ctx.Observable ≃ (contextForward e.iso.hom.base W).ctx.Observable where
  toFun := e.iso.hom.geometry.observableComp W
  invFun observable := observableEquivOfContextEq (e.homInvContext_eq W)
    (e.iso.inv.geometry.observableComp
      (contextForward e.iso.hom.base W) observable)
  left_inv observable := by
    have hpair := congrArg
      (fun k : C ⟶ C =>
        (⟨contextForward (show GeometryTotalHom C C from k).base W,
          (show GeometryTotalHom C C from k).geometry.observableComp W observable⟩ :
          Σ X, X.ctx.Observable)) e.iso.hom_inv_id
    exact observable_eq_of_sigma_eq hpair
  right_inv observable := by
    let backObservable := e.iso.inv.geometry.observableComp
      (contextForward e.iso.hom.base W) observable
    have hpair := congrArg
      (fun k : Q ⟶ Q =>
        (⟨contextForward (show GeometryTotalHom Q Q from k).base
            (contextForward e.iso.hom.base W),
          (show GeometryTotalHom Q Q from k).geometry.observableComp
            (contextForward e.iso.hom.base W) observable⟩ :
          Σ X, X.ctx.Observable)) e.iso.inv_hom_id
    have hcomposite := observable_eq_of_sigma_eq hpair
    calc
      e.iso.hom.geometry.observableComp W
          (observableEquivOfContextEq (e.homInvContext_eq W) backObservable) =
          observableEquivOfContextEq
            (congrArg (fun X => contextForward e.iso.hom.base X)
              (e.homInvContext_eq W))
            (e.iso.hom.geometry.observableComp
              (contextForward e.iso.inv.base
                (contextForward e.iso.hom.base W)) backObservable) := by
            exact (observableEquivOfContextEq_family
              (fun X => contextForward e.iso.hom.base X)
              e.iso.hom.geometry.observableComp (e.homInvContext_eq W)
              backObservable).symm
      _ = observable := hcomposite

/-- Fiber support equivalences preserve and reflect cross-context reading. -/
theorem supportComparison_reads_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category)
    (support : W.ctx.Support) (atom : U.Atom) :
    (contextForward e.iso.hom.base W).ctx.minimal.supportReads
        (e.supportComparisonEquiv W support)
        (e.iso.hom.base.upper.atomEquiv atom) ↔
      W.ctx.minimal.supportReads support atom := by
  constructor
  · intro hread
    have hback := e.iso.inv.geometry.supportReads
      (contextForward e.iso.hom.base W)
      (e.iso.hom.geometry.supportComp W support)
      (e.iso.hom.base.upper.atomEquiv atom) hread
    have hatomHom : e.iso.hom.base.upper.atomEquiv = Equiv.refl U.Atom := by
      rw [e.hom_base_eq]
      exact PackageTotalHom.eqToHom_atomEquiv hcore
    have hatomInv : e.iso.inv.base.upper.atomEquiv = Equiv.refl U.Atom := by
      rw [e.inv_base_eq]
      exact PackageTotalHom.eqToHom_atomEquiv hcore.symm
    rw [hatomHom, hatomInv] at hback
    have hcast := (supportEquivOfContextEq_reads_iff
      (e.homInvContext_eq W)
      (e.iso.inv.geometry.supportComp
        (contextForward e.iso.hom.base W)
        (e.iso.hom.geometry.supportComp W support)) atom).2 hback
    have hcancel := (e.supportComparisonEquiv W).left_inv support
    change supportEquivOfContextEq (e.homInvContext_eq W)
        (e.iso.inv.geometry.supportComp
          (contextForward e.iso.hom.base W)
          (e.iso.hom.geometry.supportComp W support)) = support at hcancel
    rw [hcancel] at hcast
    exact hcast
  · exact e.iso.hom.geometry.supportReads W support atom

/-- Fiber axis equivalences preserve and reflect axis readability. -/
theorem axisComparison_reads_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category)
    (axis : W.ctx.Axis) :
    (contextForward e.iso.hom.base W).ctx.minimal.axisReads
        (e.axisComparisonEquiv W axis) ↔ W.ctx.minimal.axisReads axis := by
  constructor
  · intro hread
    have hback := e.iso.inv.geometry.axisReads
      (contextForward e.iso.hom.base W)
      (e.iso.hom.geometry.axisComp W axis) hread
    have hcast := (axisEquivOfContextEq_reads_iff (e.homInvContext_eq W)
      (e.iso.inv.geometry.axisComp
        (contextForward e.iso.hom.base W)
        (e.iso.hom.geometry.axisComp W axis))).2 hback
    have hcancel := (e.axisComparisonEquiv W).left_inv axis
    change axisEquivOfContextEq (e.homInvContext_eq W)
        (e.iso.inv.geometry.axisComp
          (contextForward e.iso.hom.base W)
          (e.iso.hom.geometry.axisComp W axis)) = axis at hcancel
    rw [hcancel] at hcast
    exact hcast
  · exact e.iso.hom.geometry.axisReads W axis

/-- Fiber observable equivalences preserve and reflect observable readability. -/
theorem observableComparison_reads_iff {U : AtomCarrier.{u}}
    {C Q : GeometryPackage.{u, v} U} {hcore : C.core = Q.core}
    (e : GeometryFiberInnerIso C Q hcore) (W : C.site.category)
    (observable : W.ctx.Observable) :
    (contextForward e.iso.hom.base W).ctx.minimal.observableReads
        (e.observableComparisonEquiv W observable) ↔
      W.ctx.minimal.observableReads observable := by
  constructor
  · intro hread
    have hback := e.iso.inv.geometry.observableReads
      (contextForward e.iso.hom.base W)
      (e.iso.hom.geometry.observableComp W observable) hread
    have hcast := (observableEquivOfContextEq_reads_iff
      (e.homInvContext_eq W)
      (e.iso.inv.geometry.observableComp
        (contextForward e.iso.hom.base W)
        (e.iso.hom.geometry.observableComp W observable))).2 hback
    have hcancel := (e.observableComparisonEquiv W).left_inv observable
    change observableEquivOfContextEq (e.homInvContext_eq W)
        (e.iso.inv.geometry.observableComp
          (contextForward e.iso.hom.base W)
          (e.iso.hom.geometry.observableComp W observable)) = observable at hcancel
    rw [hcancel] at hcast
    exact hcast
  · exact e.iso.hom.geometry.observableReads W observable

end GeometryFiberInnerIso

/-- The canonical G-108 lift and any strongly cocartesian lift over the same
core target are uniquely isomorphic inside that core fiber. -/
noncomputable def geomTransportAlong_liftUniqueUpToFiberIso
    {U : AtomCarrier.{u}} (G Q : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (hcore : (geomTransportAlong G sigma).core = Q.core)
    (phi : GeometryTotalHom G Q)
    [(geometryProjection U).IsStronglyCocartesian
      (PackageTotalHom.comp (transportAlongHom G.core sigma)
        (eqToHom hcore : PackageTotalHom
          (geomTransportAlong G sigma).core Q.core)) phi] :
    GeometryFiberInnerIso (geomTransportAlong G sigma) Q hcore := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (transportAlongHom G.core sigma) (geomTransportAlongHom G sigma) :=
    geomTransportAlongHom_isStronglyCocartesian G sigma
  have baseFac :
      PackageTotalHom.comp (transportAlongHom G.core sigma)
          (eqToHom hcore : PackageTotalHom
            (geomTransportAlong G sigma).core Q.core) =
        (transportAlongHom G.core sigma) ≫ (eqToIso hcore).hom := by
    rfl
  let geometryIso : geomTransportAlong G sigma ≅ Q :=
    CategoryTheory.Functor.IsStronglyCocartesian.codomainIsoOfBaseIso
      (p := geometryProjection U)
      (f := transportAlongHom G.core sigma)
      (f' := PackageTotalHom.comp (transportAlongHom G.core sigma)
        (eqToHom hcore : PackageTotalHom
          (geomTransportAlong G sigma).core Q.core))
      (g := eqToIso hcore) baseFac (geomTransportAlongHom G sigma) phi
  have homLift : (geometryProjection U).IsHomLift
      (eqToHom hcore : PackageTotalHom
        (geomTransportAlong G sigma).core Q.core) geometryIso.hom := by
    change (geometryProjection U).IsHomLift
      (eqToHom hcore : PackageTotalHom
        (geomTransportAlong G sigma).core Q.core)
      (CategoryTheory.Functor.IsStronglyCocartesian.map
        (geometryProjection U) (transportAlongHom G.core sigma)
        (geomTransportAlongHom G sigma) baseFac phi)
    infer_instance
  have invLift : (geometryProjection U).IsHomLift
      (eqToHom hcore.symm : PackageTotalHom
        Q.core (geomTransportAlong G sigma).core) geometryIso.inv := by
    letI : (geometryProjection U).IsHomLift
        (eqToIso hcore).hom geometryIso.hom := by
      simpa using homLift
    simpa using CategoryTheory.IsHomLift.inv_lift_inv
      (geometryProjection U) (eqToIso hcore) geometryIso
  refine ⟨geometryIso, ?_, ?_⟩
  · exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (geometryProjection U) _ geometryIso.hom).symm
  · exact (CategoryTheory.IsHomLift.eq_of_isHomLift
      (geometryProjection U) _ geometryIso.inv).symm

/-- The forward fiber isomorphism identifies the canonical lift with the
arbitrary strongly cocartesian lift. -/
@[simp] theorem geomTransportAlong_liftUniqueUpToFiberIso_hom_fac
    {U : AtomCarrier.{u}} (G Q : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (hcore : (geomTransportAlong G sigma).core = Q.core)
    (phi : GeometryTotalHom G Q)
    [(geometryProjection U).IsStronglyCocartesian
      (PackageTotalHom.comp (transportAlongHom G.core sigma)
        (eqToHom hcore : PackageTotalHom
          (geomTransportAlong G sigma).core Q.core)) phi] :
    GeometryTotalHom.comp (geomTransportAlongHom G sigma)
      (geomTransportAlong_liftUniqueUpToFiberIso
        G Q sigma hcore phi).iso.hom = phi := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (transportAlongHom G.core sigma) (geomTransportAlongHom G sigma) :=
    geomTransportAlongHom_isStronglyCocartesian G sigma
  unfold geomTransportAlong_liftUniqueUpToFiberIso
  dsimp only
  simpa only using (CategoryTheory.Functor.IsStronglyCocartesian.fac
    (p := geometryProjection U)
    (f := transportAlongHom G.core sigma)
    (φ := geomTransportAlongHom G sigma)
    (g := eqToHom hcore)
    (f' := PackageTotalHom.comp (transportAlongHom G.core sigma)
      (eqToHom hcore : PackageTotalHom
        (geomTransportAlong G sigma).core Q.core))
    (hf' := by rfl) (φ' := phi))

/-- Composing the arbitrary lift with the inverse fiber isomorphism recovers
the canonical lift. -/
@[simp] theorem geomTransportAlong_liftUniqueUpToFiberIso_inv_fac
    {U : AtomCarrier.{u}} (G Q : GeometryPackage.{u, v} U)
    {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (hcore : (geomTransportAlong G sigma).core = Q.core)
    (phi : GeometryTotalHom G Q)
    [(geometryProjection U).IsStronglyCocartesian
      (PackageTotalHom.comp (transportAlongHom G.core sigma)
        (eqToHom hcore : PackageTotalHom
          (geomTransportAlong G sigma).core Q.core)) phi] :
    GeometryTotalHom.comp phi
      (geomTransportAlong_liftUniqueUpToFiberIso
        G Q sigma hcore phi).iso.inv = geomTransportAlongHom G sigma := by
  let geometryIso :=
    (geomTransportAlong_liftUniqueUpToFiberIso G Q sigma hcore phi).iso
  have hfac : GeometryTotalHom.comp (geomTransportAlongHom G sigma)
      geometryIso.hom = phi :=
    geomTransportAlong_liftUniqueUpToFiberIso_hom_fac G Q sigma hcore phi
  calc
    GeometryTotalHom.comp phi geometryIso.inv =
        GeometryTotalHom.comp
          (GeometryTotalHom.comp (geomTransportAlongHom G sigma)
            geometryIso.hom) geometryIso.inv :=
      congrArg (fun k => GeometryTotalHom.comp k geometryIso.inv) hfac.symm
    _ = geomTransportAlongHom G sigma := by
      change ((geomTransportAlongHom G sigma) ≫ geometryIso.hom) ≫
        geometryIso.inv = geomTransportAlongHom G sigma
      simp

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
