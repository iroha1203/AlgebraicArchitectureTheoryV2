import ResearchLean.AG.RelativeRepairComposition.W5OriginalDifferentials
import ResearchLean.AG.RelativeRepairComposition.W5Regions
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge
import ResearchLean.AG.RelativeRepairComposition.CoverCohomology

/-! # W5's whole relative cochains on the unchanged original regions

Every family retains the full native coefficient on each selected original
cell. The inverse constructions and differential evaluations precede taking
any cohomology quotient or assuming that the two input values agree.
-/
namespace AAT.AG.RelativeRepairComposition.W5RelativeCoefficients
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations W5OriginalDifferentials
variable (b₁ b₂ : ZMod 2)
local notation "T" => originalTower b₁ b₂
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower b₁ b₂))
attribute [local instance] Classical.propDecidable

/-- The physical fixed part has no original face to impose coherence upon. -/
theorem fixed_faces (f : geometry.TwoCell) (hf : f ∈ fixedRegion.faces) :
    (T).toTower.upper.pathLift (geometry.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      (T).toTower.upper.pathLift (geometry.twoRight f) := hf.elim
/-- Every original relative vertex family is zero because P retains every endpoint. -/
theorem vertex_zero (U : ClosedRegion geometry) (a : RelativeCover.C0 M U fixedRegion) : a = 0 := by
  apply Subtype.ext
  funext v
  exact a.2 v (Set.mem_univ _)
/-- Read the full original target kernel on each selected edge. -/
noncomputable def edgeCoordinate (U : ClosedRegion geometry)
    (a : RelativeCover.C1 M U fixedRegion) (e : U.edges) : ZMod 2 :=
  kernelCoordinate b₁ b₂ e.1.2.1 (a.1 e)
/-- Every selected physically fixed edge has zero correction in the whole family. -/
theorem fixed_coordinate (U : ClosedRegion geometry) (a : RelativeCover.C1 M U fixedRegion)
    (e : U.edges) (he : e.1 ∈ fixedRegion.edges) : edgeCoordinate b₁ b₂ U a e = 0 := by
  rw [edgeCoordinate,a.2 e he,map_zero]
/-- A degree-one family on all original edges keeps u only on the shared e. -/
noncomputable def fullCochain (u : ZMod 2) : C1 M :=
  fun e => (kernelCoordinate b₁ b₂ e.2.1).symm (correctionValue u e.2.2.1)
/-- Restrict the full original family to any closed patch, retaining the physical a,b zeros. -/
noncomputable def cochain (U : ClosedRegion geometry) (u : ZMod 2) :
    RelativeCover.C1 M U fixedRegion :=
  ⟨fun e => fullCochain b₁ b₂ u e.1, by
    intro e he
    rcases he with he | he
    · have he' : e.1 = name edgeA := he
      rcases e with ⟨e,hu⟩
      change e = name edgeA at he'
      subst e
      simp [fullCochain,correctionValue,name,edgeA,edgeE]
    · have he' : e.1 = name edgeB := he
      rcases e with ⟨e,hu⟩
      change e = name edgeB at he'
      subst e
      simp [fullCochain,correctionValue,name,edgeB,edgeE]⟩
/-- Every selected original coefficient inverse restores the complete edge coordinate. -/
theorem cochain_value (U : ClosedRegion geometry) (u : ZMod 2) (e : U.edges) :
    edgeCoordinate b₁ b₂ U (cochain b₁ b₂ U u) e = correctionValue u e.1.2.2.1 :=
  (kernelCoordinate b₁ b₂ e.1.2.1).apply_symm_apply _
/-- The original shared edge determines every whole relative cochain on any patch containing it. -/
theorem cochain_reconstruct (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges)
    (a : RelativeCover.C1 M U fixedRegion) :
    cochain b₁ b₂ U (edgeCoordinate b₁ b₂ U a ⟨name edgeE,he⟩) = a := by
  apply Subtype.ext
  funext e
  apply (kernelCoordinate b₁ b₂ e.1.2.1).injective
  change edgeCoordinate b₁ b₂ U (cochain b₁ b₂ U _) e = edgeCoordinate b₁ b₂ U a e
  rw [cochain_value]
  rcases e with ⟨⟨i,j,e,hs,ht⟩,hu⟩
  cases hs
  cases ht
  fin_cases e
  · rfl
  · change 0 = edgeCoordinate b₁ b₂ U a ⟨name edgeA,hu⟩
    exact (fixed_coordinate b₁ b₂ U a ⟨name edgeA,hu⟩ (Or.inl rfl)).symm
  · change 0 = edgeCoordinate b₁ b₂ U a ⟨name edgeB,hu⟩
    exact (fixed_coordinate b₁ b₂ U a ⟨name edgeB,hu⟩ (Or.inr rfl)).symm
/-- Whole relative degree-one cochains and F2 have both inverse additive coordinates. -/
noncomputable def edgeCoordinates (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges) :
    RelativeCover.C1 M U fixedRegion ≃+ ZMod 2 where
  toFun a := edgeCoordinate b₁ b₂ U a ⟨name edgeE,he⟩
  invFun := cochain b₁ b₂ U
  left_inv := cochain_reconstruct b₁ b₂ U he
  right_inv u := by
    change edgeCoordinate b₁ b₂ U (cochain b₁ b₂ U u) ⟨name edgeE,he⟩ = u
    rw [cochain_value]
    rfl
  map_add' a c := (kernelCoordinate b₁ b₂ vertexT).map_add _ _
/-- All selected original faces retain their whole kernel coordinates with both inverses. -/
noncomputable def faceCoordinates (U : ClosedRegion geometry) :
    RelativeCover.C2 M U fixedRegion ≃+ (U.faces → ZMod 2) where
  toFun a f := kernelCoordinate b₁ b₂ vertexT (a.1 f)
  invFun a := ⟨fun f => (kernelCoordinate b₁ b₂ vertexT).symm (a f), by
    intro f hf; exact hf.elim⟩
  left_inv a := by
    apply Subtype.ext
    funext f
    exact (kernelCoordinate b₁ b₂ vertexT).symm_apply_apply _
  right_inv a := by
    funext f
    exact (kernelCoordinate b₁ b₂ vertexT).apply_symm_apply _
  map_add' a c := by
    funext f
    exact (kernelCoordinate b₁ b₂ vertexT).map_add _ _
/-- The same original full path differential sends the restored shared value to each selected face. -/
theorem cochain_d1_value (U : ClosedRegion geometry) (u : ZMod 2) (f : U.faces) :
    faceCoordinates b₁ b₂ U (RelativeCover.d1 M U fixedRegion (cochain b₁ b₂ U u)) f = u := by
  have hd := congrFun (ClosedRegion.r_d1 M U (fullCochain b₁ b₂ u)) f
  change kernelCoordinate b₁ b₂ vertexT
    (ClosedRegion.d1Hom M U (cochain b₁ b₂ U u).1 f) = _
  change d1 M (fullCochain b₁ b₂ u) f.1 =
    ClosedRegion.d1Hom M U (cochain b₁ b₂ U u).1 f at hd
  rw [← hd,d1_value]
  change kernelCoordinate b₁ b₂ vertexT ((kernelCoordinate b₁ b₂ vertexT).symm _) -
    kernelCoordinate b₁ b₂ vertexT ((kernelCoordinate b₁ b₂ vertexT).symm _) = _
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rcases f with ⟨f,hf⟩
  cases f <;> simp [correctionValue,name,edgeE,edgeA,edgeB]
/-- Every whole relative differential is diagonal in its original shared value. -/
theorem d1_value (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges)
    (a : RelativeCover.C1 M U fixedRegion) (f : U.faces) :
    faceCoordinates b₁ b₂ U (RelativeCover.d1 M U fixedRegion a) f =
      edgeCoordinates b₁ b₂ U he a := by
  have hd := cochain_d1_value b₁ b₂ U (edgeCoordinates b₁ b₂ U he a) f
  have hrec : cochain b₁ b₂ U (edgeCoordinates b₁ b₂ U he a) = a := cochain_reconstruct b₁ b₂ U he a
  rw [hrec] at hd
  exact hd
/-- Every selected original degree-two differential is zero on its original empty 3-cell family. -/
theorem d2_zero (U : ClosedRegion geometry) (a : RelativeCover.C2 M U fixedRegion) :
    RelativeCover.d2 M U fixedRegion a = 0 := by
  apply Subtype.ext
  funext t
  exact t.1.elim
/-- The whole relative actual defect is generated from the original affine words. -/
noncomputable def actualDefect := ActualEquation.defectFamily T fixedRegion (fixed_faces b₁ b₂)
/-- Both full original relative defect values are the same signed physical inputs. -/
theorem actualDefect_value (f : Bool) :
    faceCoordinates b₁ b₂ ClosedRegion.all (actualDefect b₁ b₂) ⟨f,Set.mem_univ _⟩ =
      -inputValue b₁ b₂ f := defect_coordinate b₁ b₂ f

end AAT.AG.RelativeRepairComposition.W5RelativeCoefficients
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5RelativeCoefficients
