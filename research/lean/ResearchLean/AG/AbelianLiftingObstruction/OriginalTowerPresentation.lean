import ResearchLean.AG.AbelianLiftingObstruction.TowerPresentation

/-!
# Local coefficients from the original arrows and a lifted core selection

The original arrows remain explicit. A selected edge is their composite with
the supplied lift of the fixed core value. The strong properties of this
selected edge follow from those of the original arrows and the fiber
automorphism; they are not new hypotheses.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

/-- The selected upper arrows are the original arrows followed by the chosen lifts. -/
def selectedUpper (K : FiniteTransportPresentation.{uG})
    {E : Type uE} {B : Type uB} {D : Type uD}
    [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
    (p : E ⥤ B) (q : B ⥤ D)
    (L : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q))
    (lift : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (L.object j)) :
    LiftData K.toFiniteTransportTwoPresentation (p ⋙ q) where
  object := L.object
  edgeBase := L.edgeBase
  edgeLift e := reselectedEdgeLift L (fun _ _ e => lift e) e
  edgeStrong e := reselectedEdgeLift_isStronglyCocartesian L
    (fun _ _ e => lift e) e

/-- Reselection leaves every original base path unchanged. -/
theorem selectedUpper_pathBase (K : FiniteTransportPresentation.{uG})
    {E : Type uE} {B : Type uB} {D : Type uD}
    [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
    (p : E ⥤ B) (q : B ⥤ D)
    (L : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q))
    (lift : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (L.object j))
    {i j : K.Vertex} (w : K.Path i j) :
    (selectedUpper K p q L lift).pathBase w = L.pathBase w := by
  induction w with
  | nil v => rfl
  | cons e tail ih =>
      simp only [LiftData.pathBase]
      exact congrArg (fun x => L.edgeBase e ≫ x) ih

/-- The selected image arrows remain strong for the lower projection. -/
theorem selectedLowerStrong (K : FiniteTransportPresentation.{uG})
    {E : Type uE} {B : Type uB} {D : Type uD}
    [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
    (p : E ⥤ B) (q : B ⥤ D)
    (L : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q))
    (hLower : ∀ {i j : K.Vertex} (e : K.Edge i j),
      q.IsStronglyCocartesian (L.edgeBase e) (p.map (L.edgeLift e)))
    (lift : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (L.object j))
    {i j : K.Vertex} (e : K.Edge i j) :
    q.IsStronglyCocartesian (L.edgeBase e)
      (p.map ((selectedUpper K p q L lift).edgeLift e)) := by
  let lower : LiftData K.toFiniteTransportTwoPresentation q :=
    { object := fun v => p.obj (L.object v)
      edgeBase := L.edgeBase
      edgeLift := fun e => p.map (L.edgeLift e)
      edgeStrong := hLower }
  have h := reselectedEdgeLift_isStronglyCocartesian lower
    (fun _ _ e => fiberPushforward p q _ (lift e)) e
  change q.IsStronglyCocartesian (L.edgeBase e)
    (p.map (L.edgeLift e) ≫
      FiberAut.hom (fiberPushforward p q _ (lift e))) at h
  change q.IsStronglyCocartesian (L.edgeBase e)
    (p.map (L.edgeLift e ≫ FiberAut.hom (lift e)))
  simpa only [Functor.map_comp, fiberPushforward_hom] using h

/-- G-129 A: the original arrows, fixed core selection, and one lift of that selection. -/
structure OriginalTowerPresentation (K : FiniteTransportPresentation.{uG})
    {E : Type uE} {B : Type uB} {D : Type uD}
    [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
    (p : E ⥤ B) (q : B ⥤ D) where
  original : LiftData K.toFiniteTransportTwoPresentation (p ⋙ q)
  originalLowerStrong : ∀ {i j : K.Vertex} (e : K.Edge i j),
    q.IsStronglyCocartesian (original.edgeBase e) (p.map (original.edgeLift e))
  core : ∀ {i j : K.Vertex} (_ : K.Edge i j),
    FiberAut q (p.obj (original.object j))
  lift : ∀ {i j : K.Vertex} (_ : K.Edge i j),
    FiberAut (p ⋙ q) (original.object j)
  lift_core : ∀ {i j : K.Vertex} (e : K.Edge i j),
    fiberPushforward p q (original.object j) (lift e) = core e
  faceBase : ∀ f : K.TwoCell,
    original.pathBase (K.twoLeft f) = original.pathBase (K.twoRight f)
  comparator : ∀ f : K.TwoCell,
    FiberAut (p ⋙ q) (original.object (K.twoTarget f))
  /-- A2 for the selected arrows constructed from `original` and `lift`. -/
  coreAlignment : ∀ f : K.TwoCell,
    p.map ((selectedUpper K p q original lift).pathLift (K.twoLeft f)) ≫
      p.map (FiberAut.hom (comparator f)) =
    p.map ((selectedUpper K p q original lift).pathLift (K.twoRight f))
  kernelComm : ∀ v : K.Vertex, ∀ a b : Kernel p q (original.object v),
    a * b = b * a
  edgeBijective : ∀ {i j : K.Vertex} (e : K.Edge i j),
    Function.Bijective (kernelTransportHom p q
      ((selectedUpper K p q original lift).edgeLift e)
      ((selectedUpper K p q original lift).edgeStrong e)
      (selectedLowerStrong K p q original originalLowerStrong lift e))
  comparatorCentralizes : ∀ f : K.TwoCell,
    ∀ a : Kernel p q (original.object (K.twoTarget f)),
      comparator f * kernelInclusion p q _ a =
        kernelInclusion p q _ a * comparator f

namespace OriginalTowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The selected tower is derived from the original edges and their specified lifts. -/
def toTower : TowerPresentation K p q where
  upper := selectedUpper K p q T.original T.lift
  lowerStrong := selectedLowerStrong K p q T.original T.originalLowerStrong T.lift
  faceBase := by
    intro f
    rw [selectedUpper_pathBase, selectedUpper_pathBase]
    exact T.faceBase f
  comparator := T.comparator
  coreAlignment := T.coreAlignment
  kernelComm := T.kernelComm
  edgeBijective := T.edgeBijective
  comparatorCentralizes := T.comparatorCentralizes

/-- The core value of the chosen upper lift is exactly the fixed edge selection. -/
theorem selectedEdge_core {i j : K.Vertex} (e : K.Edge i j) :
    fiberPushforward p q (T.original.object j) (T.lift e) = T.core e :=
  T.lift_core e

/-- An alternative lift of the same fixed core selection gives the same kernel edge map. -/
theorem edgeTransport_independent_lift
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (e : K.Edge i j) :
    kernelTransportHom p q ((T.toTower).upper.edgeLift e)
      ((T.toTower).upper.edgeStrong e) ((T.toTower).lowerStrong e) =
    kernelTransportHom p q ((selectedUpper K p q T.original other).edgeLift e)
      ((selectedUpper K p q T.original other).edgeStrong e)
      (selectedLowerStrong K p q T.original T.originalLowerStrong other e) := by
  exact kernelTransport_independent_lift p q (T.original.edgeLift e)
    (T.lift e) (other e) ((T.lift_core e).trans (hother e).symm)
    ((T.toTower).upper.edgeStrong e)
    ((selectedUpper K p q T.original other).edgeStrong e)
    ((T.toTower).lowerStrong e)
    (selectedLowerStrong K p q T.original T.originalLowerStrong other e)
    (T.kernelComm j)

/-- Lower strong transport propagates along every path for an arbitrary lift choice. -/
theorem selectedLowerPathStrong
    (choice : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    {i j : K.Vertex} (w : K.Path i j) :
    q.IsStronglyCocartesian
      ((selectedUpper K p q T.original choice).pathBase w)
      (p.map ((selectedUpper K p q T.original choice).pathLift w)) := by
  induction w with
  | nil v =>
      simpa only [LiftData.pathBase, LiftData.pathLift, p.map_id] using
        identityStrong q (p.obj (T.original.object v))
  | cons e tail ih =>
      letI : q.IsStronglyCocartesian
          ((selectedUpper K p q T.original choice).edgeBase e)
          (p.map ((selectedUpper K p q T.original choice).edgeLift e)) :=
        selectedLowerStrong K p q T.original T.originalLowerStrong choice e
      letI : q.IsStronglyCocartesian
          ((selectedUpper K p q T.original choice).pathBase tail)
          (p.map ((selectedUpper K p q T.original choice).pathLift tail)) := ih
      simpa only [LiftData.pathBase, LiftData.pathLift, p.map_comp] using
        (Functor.IsStronglyCocartesian.comp q :
          q.IsStronglyCocartesian
            ((selectedUpper K p q T.original choice).edgeBase e ≫
              (selectedUpper K p q T.original choice).pathBase tail)
            (p.map ((selectedUpper K p q T.original choice).edgeLift e) ≫
              p.map ((selectedUpper K p q T.original choice).pathLift tail)))

/-- Generated actual-kernel transport along a path for any choice of lifted core. -/
noncomputable def selectedPathKernelTransportHom
    (choice : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    {i j : K.Vertex} (w : K.Path i j) :
    Kernel p q (T.original.object i) →* Kernel p q (T.original.object j) :=
  kernelTransportHom p q ((selectedUpper K p q T.original choice).pathLift w)
    ((selectedUpper K p q T.original choice).pathLift_isStronglyCocartesian w)
    (T.selectedLowerPathStrong choice w)

/-- The generated path map factors through the first edge and the remaining path. -/
theorem selectedPathKernelTransportHom_cons
    (choice : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    {i j k : K.Vertex} (e : K.Edge i j) (w : K.Path j k) :
    T.selectedPathKernelTransportHom choice (PresentedPath.cons e w) =
      (T.selectedPathKernelTransportHom choice w).comp
        (kernelTransportHom p q ((selectedUpper K p q T.original choice).edgeLift e)
          ((selectedUpper K p q T.original choice).edgeStrong e)
          (selectedLowerStrong K p q T.original T.originalLowerStrong choice e)) := by
  simpa only [selectedPathKernelTransportHom, LiftData.pathLift] using
    kernelTransportHom_comp p q
      ((selectedUpper K p q T.original choice).edgeLift e)
      ((selectedUpper K p q T.original choice).pathLift w)
      ((selectedUpper K p q T.original choice).edgeStrong e)
      ((selectedUpper K p q T.original choice).pathLift_isStronglyCocartesian w)
      (selectedLowerStrong K p q T.original T.originalLowerStrong choice e)
      (T.selectedLowerPathStrong choice w)

/-- Kernel transport along every typed path is independent of lifts of one fixed core choice. -/
theorem pathTransport_independent_lift
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (w : K.Path i j) :
    T.selectedPathKernelTransportHom T.lift w =
      T.selectedPathKernelTransportHom other w := by
  induction w with
  | nil v =>
      rfl
  | cons e tail ih =>
      rw [T.selectedPathKernelTransportHom_cons,
        T.selectedPathKernelTransportHom_cons, ih]
      exact congrArg (fun h => (T.selectedPathKernelTransportHom other tail).comp h)
        (T.edgeTransport_independent_lift other hother e)

/-- The descended local coefficient transport is the same for every lift of this core. -/
theorem localCoefficients_path_independent_lift
    (other : ∀ {i j : K.Vertex} (_ : K.Edge i j),
      FiberAut (p ⋙ q) (T.original.object j))
    (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
      fiberPushforward p q (T.original.object j) (other e) = T.core e)
    {i j : K.Vertex} (w : K.Path i j)
    (a : Kernel p q (T.original.object i)) :
    ((T.toTower).localCoefficients.toEdgeCoefficients.pathTransport w)
      (Additive.ofMul a) =
      Additive.ofMul (T.selectedPathKernelTransportHom other w a) := by
  calc
    ((T.toTower).localCoefficients.toEdgeCoefficients.pathTransport w)
        (Additive.ofMul a) =
        Additive.ofMul ((T.toTower).pathKernelTransportHom w a) :=
          (T.toTower).edgeCoefficients_pathTransport w a
    _ = Additive.ofMul (T.selectedPathKernelTransportHom T.lift w a) := rfl
    _ = Additive.ofMul (T.selectedPathKernelTransportHom other w a) := by
          rw [T.pathTransport_independent_lift other hother w]

end OriginalTowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
