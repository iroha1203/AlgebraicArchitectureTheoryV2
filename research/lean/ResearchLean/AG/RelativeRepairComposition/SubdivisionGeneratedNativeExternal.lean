import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedExternalArrows

/-!
# All native actual environments compose strictly with independent generated repair arrows

## Implementation notes

Environment labels are read from the entire original actual native repair
arrows through their full additive shared-kernel maps. Both identities and
compositions preserve strict shared-label agreement; no environment object or
arrow is restricted to a chosen representative.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))



universe uX vX
variable (W : ClosedRegion K) (hw : chosen ∉ W.edges)
local notation "N" => GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ allowed)
local notation "O" => GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ allowed)
local notation "C" => GeneratedStrictObjects.rangeObjectsEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef allowed values
local notation "EN" => GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed
local notation "EO" => GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc allowed

universe uJ
variable {J : FiniteTransportPresentation.{uJ}}
variable (Tenv : OriginalTowerPresentation J p q) (envVertices : Set J.Vertex)
variable (envFixed : Set (EdgeName (K := J)))
variable (readVertex : W.vertices → J.Vertex)
variable (readKernel : ∀ v : W.vertices,
  Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1)
local notation "Xenv" => RepairGroupoid Tenv envVertices envFixed
local notation "G" => ActionCategory
  (Multiplicative (StrictSupportedCover.Labels Mn Pn Un Cn (oldEdgeSet K chosen allowed))) N
local notation "Enative" => GeneratedActualNative.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed

/-- Every original full native environment arrow is read through its original vertex label and a complete shared-kernel homomorphism. -/
noncomputable def environmentLabel (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1) {x y : Xenv} (f : x ⟶ y) (v : W.vertices) : (Mo).A v.1 :=
  readKernel v (f.1.toAdd.1 (readVertex v))

omit [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every actual external identity has literal zero full shared label. -/
theorem environment_identity (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1) (x : Xenv) (v : W.vertices) :
    environmentLabel T W Tenv envVertices envFixed readVertex readKernel (𝟙 x) v = 0 :=
  map_zero (readKernel v)

omit [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- All original actual environment arrow compositions read the full sum of their original labels. -/
theorem environment_composition (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1) {x y z : Xenv} (f : x ⟶ y) (g : y ⟶ z) (v : W.vertices) :
    environmentLabel T W Tenv envVertices envFixed readVertex readKernel (f ≫ g) v =
      environmentLabel T W Tenv envVertices envFixed readVertex readKernel g v +
      environmentLabel T W Tenv envVertices envFixed readVertex readKernel f v :=
  map_add (readKernel v) _ _

/-- Full compatible arrows to every original native environment have both inverse constructions. -/
noncomputable def nativeHomEquiv (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1) (x y : G) (a b : Xenv) :=
  GeneratedExternalArrows.externalHomEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W
    (fun {x y} f v => environmentLabel T W Tenv envVertices envFixed readVertex readKernel (x := x) (y := y) f v) x y a b

/-- Full generated shared labels compose by the same sum of independently restored original actual labels. -/
theorem generated_composition {x y z : G} (f : x ⟶ y) (g : y ⟶ z) (v : W.vertices) :
    GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W (f ≫ g) v =
    GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W g v +
    GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W f v := by
  change (((Enative).inverse.map (f ≫ g)).1.toAdd).1 (.inl v.1) = _
  rw [(Enative).inverse.map_comp]
  rfl

/-- Every native generated identity reads zero in the complete shared actual kernel. -/
theorem generated_identity (x : G) (v : W.vertices) :
    GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W (𝟙 x) v = 0 := by
  change (((Enative).inverse.map (𝟙 x)).1.toAdd).1 (.inl v.1) = 0
  rw [(Enative).inverse.map_id]
  rfl

/-- All full native external compatible pairs remain strictly compatible under actual arrow composition. -/
theorem compatible_composition (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1)
    {x y z : G} {a b c : Xenv} (f : x ⟶ y) (g : y ⟶ z) (r : a ⟶ b) (s : b ⟶ c)
    (hf : ∀ v : W.vertices,
      GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W f v =
        environmentLabel T W Tenv envVertices envFixed readVertex readKernel r v)
    (hg : ∀ v : W.vertices,
      GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W g v =
        environmentLabel T W Tenv envVertices envFixed readVertex readKernel s v) :
    ∀ v : W.vertices,
      GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W (f ≫ g) v =
        environmentLabel T W Tenv envVertices envFixed readVertex readKernel (r ≫ s) v := by
  intro v
  rw [generated_composition,environment_composition,hf v,hg v]

/-- Every full native external identity forms a strictly compatible pair with the generated identity. -/
theorem compatible_identity (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ (Mo).A v.1) (x : G) (a : Xenv) :
    ∀ v : W.vertices,
      GeneratedExternalArrows.newSharedLabel T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc allowed W (𝟙 x) v =
        environmentLabel T W Tenv envVertices envFixed readVertex readKernel (𝟙 a) v := by
  intro v
  rw [generated_identity,environment_identity]

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedNativeExternal
