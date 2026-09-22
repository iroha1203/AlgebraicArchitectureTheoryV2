import ResearchLean.AG.TransportCoherence.FinitePresentation

/-!
# Finite transport presentations over an arbitrary functor

This module formalizes Definitions 4.17--4.19 and Construction 4.18 of the
fixed Rising Sea manuscript for an arbitrary functor `r : E ⥤ B`.

The finite graph, path, and face syntax is reused from `FinitePresentation`.
The realization is new: vertices are arbitrary objects of `E`, every edge
carries a selected base arrow and a strongly cocartesian lift, parallel faces
carry only equality of their composite base arrows and an authored endpoint
fiber automorphism.  Standard comparisons, raw defects, and the effect of
reselecting edge lifts are then constructed from those data.

No comparison equation, vanishing condition, or reselection law is stored in
the input structures.  In particular, the noncommutative path-transition laws
of Lemma 4.20 are deliberately left to the next proof obligation.
-/

namespace AAT.AG.TransportCoherence.Arbitrary

universe uG uE uB vE vB u

open CategoryTheory

/-! ## Fiber automorphisms for an arbitrary functor -/

/-- Automorphisms of `X` whose image under `r` is the identity of `r.obj X`. -/
def fiberAutSubgroup
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) (X : E) : Subgroup (Aut X) where
  carrier automorphism := r.map automorphism.hom = 𝟙 (r.obj X)
  one_mem' := by
    simpa only [Iso.refl_hom] using r.map_id X
  mul_mem' := by
    intro left right hleft hright
    change r.map (right.hom ≫ left.hom) = 𝟙 (r.obj X)
    rw [r.map_comp, hright, hleft]
    simp
  inv_mem' := by
    intro automorphism homMap
    have mappedIso : r.mapIso automorphism = Iso.refl (r.obj X) := by
      apply Iso.ext
      exact homMap
    have invMap := congrArg (fun iso : Aut (r.obj X) => iso.inv) mappedIso
    simpa using invMap

/-- The possibly noncommutative group `Aut_r(X)` from equation (4.19). -/
abbrev FiberAut
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) (X : E) :=
  fiberAutSubgroup r X

namespace FiberAut

variable {E : Type uE} {B : Type uB}
variable [Category.{vE} E] [Category.{vB} B]
variable {r : E ⥤ B} {X : E}

/-- Underlying forward arrow of a fiber automorphism. -/
def hom (automorphism : FiberAut r X) : X ⟶ X :=
  automorphism.1.hom

/-- Underlying inverse arrow of a fiber automorphism. -/
def inv (automorphism : FiberAut r X) : X ⟶ X :=
  automorphism.1.inv

/-- The forward arrow of a fiber automorphism lies over the identity. -/
theorem hom_map_eq (automorphism : FiberAut r X) :
    r.map (hom automorphism) = 𝟙 (r.obj X) :=
  automorphism.2

/-- The inverse arrow of a fiber automorphism lies over the identity. -/
theorem inv_map_eq (automorphism : FiberAut r X) :
    r.map (inv automorphism) = 𝟙 (r.obj X) := by
  exact (fiberAutSubgroup r X).inv_mem automorphism.2

/--
Two endpoint fiber automorphisms are equal when they have the same composite
after one strongly cocartesian lift.
-/
theorem ext_of_strong_fac {Y : E} {σ : r.obj X ⟶ r.obj Y}
    (lift : X ⟶ Y) (hlift : r.IsStronglyCocartesian σ lift)
    (left right : FiberAut r Y)
    (fac : lift ≫ hom left = lift ≫ hom right) :
    left = right := by
  letI : r.IsStronglyCocartesian σ lift := hlift
  letI : r.IsHomLift (𝟙 (r.obj Y)) left.1.hom := by
    rw [← left.2]
    infer_instance
  letI : r.IsHomLift (𝟙 (r.obj Y)) right.1.hom := by
    rw [← right.2]
    infer_instance
  apply Subtype.ext
  apply Iso.ext
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    r σ lift (𝟙 (r.obj Y))
  exact fac

end FiberAut

/-! ## Arbitrary realization of finite path and face data -/

/--
Realization of the vertices and edges of a finite transport presentation over
an arbitrary functor.  `edgeStrong` is precisely the local hypothesis in
Definition 4.17; it also certifies that each `edgeLift` lies over `edgeBase`.
-/
structure LiftData
    (G : FiniteTransportTwoPresentation.{uG})
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) where
  /-- Object of the total category assigned to every vertex. -/
  object : G.Vertex → E
  /-- Base arrow assigned to every directed edge. -/
  edgeBase : {i j : G.Vertex} → G.Edge i j →
    (r.obj (object i) ⟶ r.obj (object j))
  /-- Selected lift assigned to every directed edge. -/
  edgeLift : {i j : G.Vertex} → G.Edge i j → (object i ⟶ object j)
  /-- Every selected edge arrow is a strong lift of its assigned base arrow. -/
  edgeStrong : ∀ {i j : G.Vertex} (edge : G.Edge i j),
    r.IsStronglyCocartesian (edgeBase edge) (edgeLift edge)

namespace LiftData

variable {G : FiniteTransportTwoPresentation.{uG}}
variable {E : Type uE} {B : Type uB}
variable [Category.{vE} E] [Category.{vB} B]
variable {r : E ⥤ B} (data : LiftData G r)

/-- Evaluate a finite path in the base category. -/
def pathBase : {i j : G.Vertex} → G.Path i j →
    (r.obj (data.object i) ⟶ r.obj (data.object j))
  | _, _, .nil vertex => 𝟙 (r.obj (data.object vertex))
  | _, _, .cons edge tail => data.edgeBase edge ≫ pathBase tail

/-- Evaluate a finite path by composing its selected total lifts. -/
def pathLift : {i j : G.Vertex} → G.Path i j →
    (data.object i ⟶ data.object j)
  | _, _, .nil vertex => 𝟙 (data.object vertex)
  | _, _, .cons edge tail => data.edgeLift edge ≫ pathLift tail

/-- Base evaluation sends path concatenation to categorical composition. -/
theorem pathBase_append {i j k : G.Vertex}
    (first : G.Path i j) (second : G.Path j k) :
    data.pathBase (first.append second) =
      data.pathBase first ≫ data.pathBase second := by
  induction first with
  | nil vertex =>
      simp only [PresentedPath.append, pathBase, Category.id_comp]
  | cons edge tail inductionHypothesis =>
      simp only [PresentedPath.append, pathBase]
      rw [inductionHypothesis]
      exact (Category.assoc _ _ _).symm

/-- Total evaluation sends path concatenation to categorical composition. -/
theorem pathLift_append {i j k : G.Vertex}
    (first : G.Path i j) (second : G.Path j k) :
    data.pathLift (first.append second) =
      data.pathLift first ≫ data.pathLift second := by
  induction first with
  | nil vertex =>
      simp only [PresentedPath.append, pathLift, Category.id_comp]
  | cons edge tail inductionHypothesis =>
      simp only [PresentedPath.append, pathLift]
      rw [inductionHypothesis]
      exact (Category.assoc _ _ _).symm

/-- Every finite path evaluates to a strongly cocartesian lift of its base path. -/
theorem pathLift_isStronglyCocartesian {i j : G.Vertex}
    (path : G.Path i j) :
    r.IsStronglyCocartesian (data.pathBase path) (data.pathLift path) := by
  induction path with
  | nil vertex =>
      letI : r.IsHomLift
          (𝟙 (r.obj (data.object vertex)))
          (Iso.refl (data.object vertex)).hom := by
        change r.IsHomLift
          (𝟙 (r.obj (data.object vertex)))
          (𝟙 (data.object vertex))
        exact CategoryTheory.IsHomLift.id rfl
      simpa only [pathBase, pathLift] using
        (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
          r (𝟙 (r.obj (data.object vertex)))
          (Iso.refl (data.object vertex)))
  | cons edge tail inductionHypothesis =>
      letI : r.IsStronglyCocartesian
          (data.edgeBase edge) (data.edgeLift edge) :=
        data.edgeStrong edge
      letI : r.IsStronglyCocartesian
          (data.pathBase tail) (data.pathLift tail) :=
        inductionHypothesis
      simpa only [pathBase, pathLift] using
        (CategoryTheory.Functor.IsStronglyCocartesian.comp r :
          r.IsStronglyCocartesian
            (data.edgeBase edge ≫ data.pathBase tail)
            (data.edgeLift edge ≫ data.pathLift tail))

/-- The image of every evaluated path is exactly its recursively evaluated base path. -/
theorem map_pathLift {i j : G.Vertex} (path : G.Path i j) :
    r.map (data.pathLift path) = data.pathBase path := by
  letI : r.IsStronglyCocartesian
      (data.pathBase path) (data.pathLift path) :=
    data.pathLift_isStronglyCocartesian path
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    r (data.pathBase path) (data.pathLift path)).symm

end LiftData

/--
Finite comparison data from Definition 4.17 over an arbitrary functor.

The comparator is authored input.  It is not required to agree with the
canonical comparison, and no defect equation or coherence conclusion is
stored in this structure.
-/
structure TransportData
    (G : FiniteTransportTwoPresentation.{uG})
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) where
  /-- Realized vertices and selected strong edge lifts. -/
  lift : LiftData G r
  /-- The two boundary paths of each face have the same composite base arrow. -/
  faceBase : ∀ cell : G.TwoCell,
    lift.pathBase (G.twoLeft cell) = lift.pathBase (G.twoRight cell)
  /-- Authored endpoint-fiber automorphism `u_f`. -/
  comparator : (cell : G.TwoCell) →
    FiberAut r (lift.object (G.twoTarget cell))

/-! ## Edge and path reselection (Definition 4.19) -/

/-- One endpoint fiber automorphism for every edge, equation (4.22). -/
abbrev EdgeReselection
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r) :=
  (i j : G.Vertex) → (edge : G.Edge i j) →
    FiberAut r (data.object j)

/-- Reselect one edge lift by postcomposing its target-fiber automorphism. -/
def reselectedEdgeLift
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (edge : G.Edge i j) : data.object i ⟶ data.object j :=
  data.edgeLift edge ≫ FiberAut.hom (reselection i j edge)

/-- Reselecting an edge preserves its exact assigned base arrow. -/
theorem reselectedEdgeLift_map_eq
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (edge : G.Edge i j) :
    r.map (reselectedEdgeLift data reselection edge) = data.edgeBase edge := by
  rw [reselectedEdgeLift, r.map_comp,
    FiberAut.hom_map_eq, Category.comp_id]
  letI : r.IsStronglyCocartesian
      (data.edgeBase edge) (data.edgeLift edge) := data.edgeStrong edge
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    r (data.edgeBase edge) (data.edgeLift edge)).symm

/-- Reselecting an edge by a vertical isomorphism preserves strong cocartesianness. -/
theorem reselectedEdgeLift_isStronglyCocartesian
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (edge : G.Edge i j) :
    r.IsStronglyCocartesian (data.edgeBase edge)
      (reselectedEdgeLift data reselection edge) := by
  letI : r.IsStronglyCocartesian
      (data.edgeBase edge) (data.edgeLift edge) :=
    data.edgeStrong edge
  letI : r.IsHomLift
      (𝟙 (r.obj (data.object j)))
      (reselection i j edge).1.hom := by
    rw [← (reselection i j edge).2]
    infer_instance
  letI : r.IsStronglyCocartesian
      (𝟙 (r.obj (data.object j)))
      (reselection i j edge).1.hom :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_iso
      r (𝟙 (r.obj (data.object j))) (reselection i j edge).1
  simpa only [reselectedEdgeLift, FiberAut.hom, Category.comp_id] using
    (CategoryTheory.Functor.IsStronglyCocartesian.comp r :
      r.IsStronglyCocartesian
        (data.edgeBase edge ≫ 𝟙 (r.obj (data.object j)))
        (data.edgeLift edge ≫ (reselection i j edge).1.hom))

/-- The identity edge reselection leaves the selected edge lift unchanged. -/
theorem reselectedEdgeLift_one
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    {i j : G.Vertex} (edge : G.Edge i j) :
    reselectedEdgeLift data (1 : EdgeReselection data) edge =
      data.edgeLift edge := by
  change data.edgeLift edge ≫ 𝟙 (data.object j) = data.edgeLift edge
  exact Category.comp_id _

/-- The edge-lift realization after one edge reselection. -/
def reselectLiftData
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) : LiftData G r where
  object := data.object
  edgeBase := data.edgeBase
  edgeLift := reselectedEdgeLift data reselection
  edgeStrong := reselectedEdgeLift_isStronglyCocartesian data reselection

/-- Reselection changes only total lifts, not the recursively evaluated base path. -/
theorem reselectLiftData_pathBase
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (path : G.Path i j) :
    (reselectLiftData data reselection).pathBase path = data.pathBase path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change data.edgeBase edge ≫
          (reselectLiftData data reselection).pathBase tail =
        data.edgeBase edge ≫ data.pathBase tail
      rw [inductionHypothesis]

/-- Evaluate a path after reselecting all of its edge lifts. -/
def reselectedPathLift
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (path : G.Path i j) : data.object i ⟶ data.object j :=
  (reselectLiftData data reselection).pathLift path

/-- The identity edge reselection leaves every finite path lift unchanged. -/
theorem reselectedPathLift_one
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    {i j : G.Vertex} (path : G.Path i j) :
    reselectedPathLift data (1 : EdgeReselection data) path =
      data.pathLift path := by
  induction path with
  | nil vertex => rfl
  | cons edge tail inductionHypothesis =>
      change reselectedEdgeLift data (1 : EdgeReselection data) edge ≫
          reselectedPathLift data (1 : EdgeReselection data) tail =
        data.edgeLift edge ≫ data.pathLift tail
      rw [reselectedEdgeLift_one, inductionHypothesis]

/-- Reselected path evaluation has the original composite base arrow. -/
theorem reselectedPathLift_map_eq
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (path : G.Path i j) :
    r.map (reselectedPathLift data reselection path) = data.pathBase path := by
  have mapped := (reselectLiftData data reselection).map_pathLift path
  rw [reselectLiftData_pathBase data reselection path] at mapped
  exact mapped

/-- Every reselected finite path remains a strong lift of the same base path. -/
theorem reselectedPathLift_isStronglyCocartesian
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : LiftData G r)
    (reselection : EdgeReselection data) {i j : G.Vertex}
    (path : G.Path i j) :
    r.IsStronglyCocartesian (data.pathBase path)
      (reselectedPathLift data reselection path) :=
  by
    have strong :=
      (reselectLiftData data reselection).pathLift_isStronglyCocartesian path
    rw [reselectLiftData_pathBase data reselection path] at strong
    exact strong

/-! ## Standard face comparison and raw defect (Construction 4.18) -/

/-- Canonical endpoint comparison between two strong lifts of one base arrow. -/
noncomputable def canonicalFiberComparator
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) {X Y : E} (σ : r.obj X ⟶ r.obj Y)
    (left right : X ⟶ Y)
    (hleft : r.IsStronglyCocartesian σ left)
    (hright : r.IsStronglyCocartesian σ right) : FiberAut r Y := by
  letI : r.IsStronglyCocartesian σ left := hleft
  letI : r.IsStronglyCocartesian σ right := hright
  let comparison : Aut Y :=
    CategoryTheory.Functor.IsCocartesian.codomainUniqueUpToIso
      r σ left right
  have homLift : r.IsHomLift (𝟙 (r.obj Y)) comparison.hom := by
    change r.IsHomLift (𝟙 (r.obj Y))
      (CategoryTheory.Functor.IsCocartesian.map r σ left right)
    infer_instance
  have homMap : r.map comparison.hom = 𝟙 (r.obj Y) :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      r (𝟙 (r.obj Y)) comparison.hom).symm
  exact ⟨comparison, homMap⟩

/-- The canonical comparator is characterized by factorization of the first lift. -/
@[simp]
theorem canonicalFiberComparator_fac
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    (r : E ⥤ B) {X Y : E} (σ : r.obj X ⟶ r.obj Y)
    (left right : X ⟶ Y)
    (hleft : r.IsStronglyCocartesian σ left)
    (hright : r.IsStronglyCocartesian σ right) :
    left ≫ FiberAut.hom
        (canonicalFiberComparator r σ left right hleft hright) = right := by
  letI : r.IsStronglyCocartesian σ left := hleft
  letI : r.IsStronglyCocartesian σ right := hright
  unfold canonicalFiberComparator FiberAut.hom
  dsimp only
  exact CategoryTheory.Functor.IsCocartesian.fac r σ left right

/-- The canonical comparison `φ_f(a)` between reselected face paths. -/
noncomputable def canonicalFaceComparator
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    FiberAut r (data.lift.object (G.twoTarget cell)) := by
  have leftStrong := reselectedPathLift_isStronglyCocartesian
    data.lift reselection (G.twoLeft cell)
  have rightStrong : r.IsStronglyCocartesian
      (data.lift.pathBase (G.twoLeft cell))
      (reselectedPathLift data.lift reselection (G.twoRight cell)) := by
    rw [data.faceBase cell]
    exact reselectedPathLift_isStronglyCocartesian
      data.lift reselection (G.twoRight cell)
  exact canonicalFiberComparator r
    (data.lift.pathBase (G.twoLeft cell))
    (reselectedPathLift data.lift reselection (G.twoLeft cell))
    (reselectedPathLift data.lift reselection (G.twoRight cell))
    leftStrong rightStrong

/-- Equation (4.20): the canonical comparator identifies the two path lifts. -/
@[simp]
theorem canonicalFaceComparator_fac
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    reselectedPathLift data.lift reselection (G.twoLeft cell) ≫
        FiberAut.hom (canonicalFaceComparator data reselection cell) =
      reselectedPathLift data.lift reselection (G.twoRight cell) := by
  unfold canonicalFaceComparator
  apply canonicalFiberComparator_fac

/-- Equation (4.21): authored comparison times inverse standard comparison. -/
noncomputable def rawFaceDefect
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    FiberAut r (data.lift.object (G.twoTarget cell)) :=
  data.comparator cell * (canonicalFaceComparator data reselection cell)⁻¹

/-- The raw defect has the fixed noncommutative order `φ⁻¹ ≫ u` on arrows. -/
theorem rawFaceDefect_hom
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    FiberAut.hom (rawFaceDefect data reselection cell) =
      FiberAut.inv (canonicalFaceComparator data reselection cell) ≫
        FiberAut.hom (data.comparator cell) := by
  rfl

/-- The raw defect is identity exactly when authored and canonical comparisons agree. -/
theorem rawFaceDefect_eq_one_iff
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r)
    (reselection : EdgeReselection data.lift) (cell : G.TwoCell) :
    rawFaceDefect data reselection cell = 1 ↔
      data.comparator cell = canonicalFaceComparator data reselection cell := by
  unfold rawFaceDefect
  constructor
  · intro equality
    calc
      data.comparator cell =
          (data.comparator cell *
            (canonicalFaceComparator data reselection cell)⁻¹) *
              canonicalFaceComparator data reselection cell := by
        simp [mul_assoc]
      _ = 1 * canonicalFaceComparator data reselection cell :=
        congrArg
          (fun automorphism =>
            automorphism * canonicalFaceComparator data reselection cell)
          equality
      _ = canonicalFaceComparator data reselection cell := one_mul _
  · intro equality
    rw [equality]
    exact mul_inv_cancel _

/-- The standard comparison of Construction 4.18 before edge reselection. -/
noncomputable def initialCanonicalFaceComparator
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r) (cell : G.TwoCell) :
    FiberAut r (data.lift.object (G.twoTarget cell)) := by
  have leftStrong := data.lift.pathLift_isStronglyCocartesian
    (G.twoLeft cell)
  have rightStrong : r.IsStronglyCocartesian
      (data.lift.pathBase (G.twoLeft cell))
      (data.lift.pathLift (G.twoRight cell)) := by
    rw [data.faceBase cell]
    exact data.lift.pathLift_isStronglyCocartesian (G.twoRight cell)
  exact canonicalFiberComparator r
    (data.lift.pathBase (G.twoLeft cell))
    (data.lift.pathLift (G.twoLeft cell))
    (data.lift.pathLift (G.twoRight cell))
    leftStrong rightStrong

/-- Equation (4.20) for the unreselected path lifts. -/
@[simp]
theorem initialCanonicalFaceComparator_fac
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r) (cell : G.TwoCell) :
    data.lift.pathLift (G.twoLeft cell) ≫
        FiberAut.hom (initialCanonicalFaceComparator data cell) =
      data.lift.pathLift (G.twoRight cell) := by
  unfold initialCanonicalFaceComparator
  apply canonicalFiberComparator_fac

/-- The comparison computed at the identity edge gauge is the initial comparison. -/
theorem canonicalFaceComparator_one
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r) (cell : G.TwoCell) :
    canonicalFaceComparator data 1 cell =
      initialCanonicalFaceComparator data cell := by
  apply FiberAut.ext_of_strong_fac
    (data.lift.pathLift (G.twoLeft cell))
    (data.lift.pathLift_isStronglyCocartesian (G.twoLeft cell))
  calc
    data.lift.pathLift (G.twoLeft cell) ≫
        FiberAut.hom (canonicalFaceComparator data 1 cell) =
      reselectedPathLift data.lift 1 (G.twoLeft cell) ≫
        FiberAut.hom (canonicalFaceComparator data 1 cell) := by
          rw [reselectedPathLift_one]
    _ = reselectedPathLift data.lift 1 (G.twoRight cell) :=
      canonicalFaceComparator_fac data 1 cell
    _ = data.lift.pathLift (G.twoRight cell) :=
      reselectedPathLift_one data.lift (G.twoRight cell)
    _ = data.lift.pathLift (G.twoLeft cell) ≫
        FiberAut.hom (initialCanonicalFaceComparator data cell) :=
      (initialCanonicalFaceComparator_fac data cell).symm

/-- The raw defect of Construction 4.18 before any edge reselection. -/
noncomputable def initialRawFaceDefect
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r) (cell : G.TwoCell) :
    FiberAut r (data.lift.object (G.twoTarget cell)) :=
  data.comparator cell * (initialCanonicalFaceComparator data cell)⁻¹

/-- The identity-gauge raw defect is the original raw defect of Construction 4.18. -/
theorem rawFaceDefect_one
    {G : FiniteTransportTwoPresentation.{uG}}
    {E : Type uE} {B : Type uB}
    [Category.{vE} E] [Category.{vB} B]
    {r : E ⥤ B} (data : TransportData G r) (cell : G.TwoCell) :
    rawFaceDefect data 1 cell = initialRawFaceDefect data cell := by
  rw [rawFaceDefect, initialRawFaceDefect, canonicalFaceComparator_one]

/-! ## Connection to the existing package-projection implementation -/

open AtomFoundation

/-- Existing package-fiber automorphisms are the arbitrary fiber group at `packageProjection`. -/
def packageFiberAutMulEquiv {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    PackageFiberAut P ≃* FiberAut (packageProjection U) P where
  toFun automorphism := ⟨automorphism.1, automorphism.2⟩
  invFun automorphism := ⟨automorphism.1, automorphism.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The fiber-group equivalence preserves the underlying total-category arrow. -/
@[simp]
theorem packageFiberAutMulEquiv_hom
    {U : AtomCarrier.{u}} {P : AATCorePackage U}
    (automorphism : PackageFiberAut P) :
    FiberAut.hom (packageFiberAutMulEquiv P automorphism) =
      PackageFiberAut.hom automorphism := by
  rfl

/-- Existing package edge-lift data as an arbitrary-functor realization. -/
def packageLiftData
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U) :
    LiftData G.toFiniteTransportTwoPresentation (packageProjection U) where
  object := data.package
  edgeBase := fun edge => (data.edgeLift edge).base
  edgeLift := data.edgeLift
  edgeStrong := data.edgeStrong

/-- The generic path lift is the existing package path lift. -/
theorem packageLiftData_pathLift
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U)
    {i j : G.Vertex} (path : G.Path i j) :
    (packageLiftData data).pathLift path = data.pathLift path := by
  induction path with
  | nil vertex =>
      change PackageTotalHom.id (data.package vertex) =
        PackageTotalHom.id (data.package vertex)
      rfl
  | cons edge tail inductionHypothesis =>
      simp only [LiftData.pathLift, AdmissibleLiftData.pathLift]
      rw [inductionHypothesis]
      rfl

/-- The generic base path is the exact base of the existing package path lift. -/
theorem packageLiftData_pathBase
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U)
    {i j : G.Vertex} (path : G.Path i j) :
    (packageLiftData data).pathBase path = (data.pathLift path).base := by
  induction path with
  | nil vertex =>
      change ExtInstHom.id (packagePoint (data.package vertex)) =
        ExtInstHom.id (packagePoint (data.package vertex))
      rfl
  | cons edge tail inductionHypothesis =>
      simp only [LiftData.pathBase, AdmissibleLiftData.pathLift]
      rw [inductionHypothesis]
      rfl

/-- Existing finite comparison data as arbitrary-functor comparison data. -/
def packageTransportData
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleTransportData G U) :
    TransportData G.toFiniteTransportTwoPresentation (packageProjection U) where
  lift := packageLiftData data.lift
  faceBase := by
    intro cell
    rw [packageLiftData_pathBase, packageLiftData_pathBase]
    exact data.twoCellBase cell
  comparator := fun cell => packageFiberAutMulEquiv _ (data.comparator cell)

/-- Convert an existing package edge reselection to the arbitrary-functor one. -/
def packageEdgeReselection
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U)
    (reselection : AAT.AG.TransportCoherence.EdgeReselection data) :
    EdgeReselection (packageLiftData data) :=
  fun i j edge => packageFiberAutMulEquiv _ (reselection i j edge)

/-- Generic and existing package edge reselection choose the same total arrow. -/
theorem package_reselectedEdgeLift
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U)
    (reselection : AAT.AG.TransportCoherence.EdgeReselection data)
    {i j : G.Vertex} (edge : G.Edge i j) :
    reselectedEdgeLift (packageLiftData data)
        (packageEdgeReselection data reselection) edge =
      AAT.AG.TransportCoherence.reselectedEdgeLift data reselection edge := by
  rfl

/-- Generic and existing package path reselection evaluate to the same total arrow. -/
theorem package_reselectedPathLift
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleLiftData G U)
    (reselection : AAT.AG.TransportCoherence.EdgeReselection data)
    {i j : G.Vertex} (path : G.Path i j) :
    reselectedPathLift (packageLiftData data)
        (packageEdgeReselection data reselection) path =
      AAT.AG.TransportCoherence.reselectedPathLift data reselection path := by
  induction path with
  | nil vertex =>
      change PackageTotalHom.id (data.package vertex) =
        PackageTotalHom.id (data.package vertex)
      rfl
  | cons edge tail inductionHypothesis =>
      change reselectedEdgeLift (packageLiftData data)
          (packageEdgeReselection data reselection) edge ≫
            reselectedPathLift (packageLiftData data)
              (packageEdgeReselection data reselection) tail =
        (AAT.AG.TransportCoherence.reselectedEdgeLift
          data reselection edge).comp
          (AAT.AG.TransportCoherence.reselectedPathLift
            data reselection tail)
      rw [package_reselectedEdgeLift, inductionHypothesis]
      rfl

/--
The arbitrary canonical face comparison specializes to the existing package
comparison for every edge reselection.
-/
theorem package_canonicalFaceComparator
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleTransportData G U)
    (reselection : AAT.AG.TransportCoherence.EdgeReselection data.lift)
    (cell : G.TwoCell) :
    canonicalFaceComparator (packageTransportData data)
        (packageEdgeReselection data.lift reselection) cell =
      packageFiberAutMulEquiv _
        (AAT.AG.TransportCoherence.canonicalTwoCellComparator
          data reselection cell) := by
  apply FiberAut.ext_of_strong_fac
    (reselectedPathLift (packageLiftData data.lift)
      (packageEdgeReselection data.lift reselection) (G.twoLeft cell))
    (reselectedPathLift_isStronglyCocartesian
      (packageLiftData data.lift)
      (packageEdgeReselection data.lift reselection) (G.twoLeft cell))
  calc
    reselectedPathLift (packageLiftData data.lift)
        (packageEdgeReselection data.lift reselection) (G.twoLeft cell) ≫
          FiberAut.hom
            (canonicalFaceComparator (packageTransportData data)
              (packageEdgeReselection data.lift reselection) cell) =
      reselectedPathLift (packageLiftData data.lift)
        (packageEdgeReselection data.lift reselection) (G.twoRight cell) :=
      canonicalFaceComparator_fac (packageTransportData data)
        (packageEdgeReselection data.lift reselection) cell
    _ = AAT.AG.TransportCoherence.reselectedPathLift
          data.lift reselection (G.twoRight cell) :=
      package_reselectedPathLift data.lift reselection (G.twoRight cell)
    _ = (AAT.AG.TransportCoherence.reselectedPathLift
          data.lift reselection (G.twoLeft cell)).comp
        (PackageFiberAut.hom
          (AAT.AG.TransportCoherence.canonicalTwoCellComparator
            data reselection cell)) :=
      (AAT.AG.TransportCoherence.canonicalTwoCellComparator_fac
        data reselection cell).symm
    _ = reselectedPathLift (packageLiftData data.lift)
          (packageEdgeReselection data.lift reselection) (G.twoLeft cell) ≫
        FiberAut.hom
          (packageFiberAutMulEquiv _
            (AAT.AG.TransportCoherence.canonicalTwoCellComparator
              data reselection cell)) := by
      rw [package_reselectedPathLift, packageFiberAutMulEquiv_hom]
      rfl

/-- The arbitrary raw defect specializes to the existing package raw defect. -/
theorem package_rawFaceDefect
    {G : FiniteTransportPresentation.{u}}
    {U : AtomCarrier.{u}} (data : AdmissibleTransportData G U)
    (reselection : AAT.AG.TransportCoherence.EdgeReselection data.lift)
    (cell : G.TwoCell) :
    rawFaceDefect (packageTransportData data)
        (packageEdgeReselection data.lift reselection) cell =
      packageFiberAutMulEquiv _
        (AAT.AG.TransportCoherence.rawTwoCellDefect
          data reselection cell) := by
  unfold rawFaceDefect AAT.AG.TransportCoherence.rawTwoCellDefect
  rw [package_canonicalFaceComparator]
  exact (map_mul (packageFiberAutMulEquiv _)
    (data.comparator cell)
    (AAT.AG.TransportCoherence.canonicalTwoCellComparator
      data reselection cell)⁻¹).symm

end AAT.AG.TransportCoherence.Arbitrary

#assert_standard_axioms_only AAT.AG.TransportCoherence.Arbitrary
