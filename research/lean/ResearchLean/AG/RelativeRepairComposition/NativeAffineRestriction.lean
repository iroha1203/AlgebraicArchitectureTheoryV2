import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid
import ResearchLean.AG.RelativeRepairComposition.TowerRestriction

/-! # Restricting the same original affine operations and full vertex labels -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {K : FiniteTransportPresentation.{uG}} (U : ClosedRegion K)

/-- Restrict a real operation family to the same selected original edge values. -/
def restrictOperations (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A) :
    ∀ {i j : (ClosedRegion.presentation U).Vertex},
      (ClosedRegion.presentation U).Edge i j → Operations k A := fun e => R e.1

/-- Every restricted affine word is the ordered value of the same complete original word. -/
theorem restricted_path_value (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    {i j : (ClosedRegion.presentation U).Vertex} (w : (ClosedRegion.presentation U).Path i j) :
    GroupExtension.pathValue (ClosedRegion.presentation U) (restrictOperations U R) w =
      GroupExtension.pathValue K R (ClosedRegion.forgetPath U w) := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change GroupExtension.pathValue (ClosedRegion.presentation U) (restrictOperations U R) w * R e.1 = _
    rw [ih]
    rfl

variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)

include hfaces in
/-- The restricted original core alignment follows from the same primitive original face alignment. -/
theorem restricted_faces (f : (ClosedRegion.presentation U).TwoCell) :
    (GroupExtension.pathValue (ClosedRegion.presentation U) (restrictOperations U R)
      ((ClosedRegion.presentation U).twoLeft f)).linear =
    (GroupExtension.pathValue (ClosedRegion.presentation U) (restrictOperations U R)
      ((ClosedRegion.presentation U).twoRight f)).linear := by
  rw [restricted_path_value, restricted_path_value]
  change (GroupExtension.pathValue K R (ClosedRegion.forgetPath U
    ((ClosedRegion.twoPresentation U).twoLeft f))).linear =
      (GroupExtension.pathValue K R (ClosedRegion.forgetPath U
        ((ClosedRegion.twoPresentation U).twoRight f))).linear
  rw [ClosedRegion.forget_two_left U f, ClosedRegion.forget_two_right U f]
  exact hfaces f.1

/-- Constructing the full affine tower commutes with restricting the same original typed presentation. -/
theorem restricted_tower_eq :
    ClosedRegion.restrictTower U (tower K L R c hfaces) =
      tower (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces) := rfl

variable (fixed : Set (EdgeName (K := K))) (vertices : Set K.Vertex)

/-- Independently specified affine repairs restrict their actual values and physical fixed names. -/
noncomputable def restrictAffineRepair (s : Repair K R c fixed) :
    Repair (ClosedRegion.presentation U) (restrictOperations U R) (fun f => c f.1)
      (ClosedRegion.restrictedEdges U fixed) where
  operation := restrictOperations U s.operation
  linear e := s.linear e.1
  face f := by
    rw [restricted_path_value, restricted_path_value]
    change translation (k := k) (c f.1) * GroupExtension.pathValue K s.operation
      (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoLeft f)) =
        GroupExtension.pathValue K s.operation
          (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoRight f))
    rw [ClosedRegion.forget_two_left U f, ClosedRegion.forget_two_right U f]
    exact s.face f.1
  fixed_value e he := s.fixed_value (ClosedRegion.edgeNameEquiv U e).1 he

/-- Restricting the real repair keeps each selected original edge operation exactly. -/
theorem affine_restriction_value (s : Repair K R c fixed)
    {i j : (ClosedRegion.presentation U).Vertex} (e : (ClosedRegion.presentation U).Edge i j) :
    (restrictAffineRepair U R c fixed s).operation e = s.operation e.1 := rfl

/-- The independently defined real repair restriction agrees with native actual repair restriction. -/
theorem affine_restriction_native (s : SupportedRepair (tower K L R c hfaces) fixed) :
    restrictAffineRepair U R c fixed (repairEquivalence K L R c hfaces fixed s) =
      repairEquivalence (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces) (ClosedRegion.restrictedEdges U fixed)
          (ClosedRegion.restrictRepair U (tower K L R c hfaces) fixed s) := rfl

/-- Full real translation labels restrict by their original vertex values and fixed original edge equations. -/
def restrictAffineLabels : gaugeLabels K R vertices fixed →+
    gaugeLabels (ClosedRegion.presentation U) (restrictOperations U R)
      (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed) where
  toFun b := ⟨fun v => b.1 v.1, by
    constructor
    · intro v hv; exact b.2.1 v.1 hv
    · intro e he; exact b.2.2 (ClosedRegion.edgeNameEquiv U e).1 he⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Restricting full real gauge labels agrees with the same native gauge-label restriction at every vertex. -/
theorem affine_label_restriction_native
    (b : supportedC0 (tower K L R c hfaces) vertices fixed) :
    restrictAffineLabels U R fixed vertices (gaugeLabelEquivalence K L R c hfaces vertices fixed b) =
      gaugeLabelEquivalence (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces)
        (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed)
          (ClosedRegion.restrictGaugeLabel U (tower K L R c hfaces) vertices fixed b) := rfl

/-- Restriction commutes with each independently specified original real affine reidentification. -/
theorem affine_restriction_gauge (b : gaugeLabels K R vertices fixed) (s : Repair K R c fixed) :
    restrictAffineRepair U R c fixed (gauge K L R c hfaces vertices fixed b s) =
      gauge (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces)
        (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed)
        (restrictAffineLabels U R fixed vertices b) (restrictAffineRepair U R c fixed s) := by
  apply Repair.ext
  intro i j e
  rw [affine_restriction_value, gauge_value, gauge_value, affine_restriction_value]
  rfl

/-- The independent real-affine restriction functor keeps every selected original operation and full vertex label. -/
noncomputable def affineRestrictionFunctor : Groupoid K L R c hfaces vertices fixed ⥤
    Groupoid (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
      (fun f => c f.1) (restricted_faces U R hfaces)
      (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed) := by
  letI := gaugeAddAction K L R c hfaces vertices fixed
  letI := gaugeAddAction (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
    (fun f => c f.1) (restricted_faces U R hfaces)
    (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed)
  exact {
    obj := fun s => (restrictAffineRepair U R c fixed s.back :
      Groupoid (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces)
        (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed))
    map := fun {s _} b => ⟨Multiplicative.ofAdd (restrictAffineLabels U R fixed vertices b.1.toAdd),
      (affine_restriction_gauge U L R c hfaces fixed vertices b.1.toAdd s.back).symm.trans
        (congrArg (restrictAffineRepair U R c fixed) b.2)⟩
    map_id := fun _ => Subtype.ext rfl
    map_comp := fun _ _ => Subtype.ext rfl }

/-- The two independent restriction routes agree as functors on actual original edge objects and all gauge arrows. -/
theorem affine_restriction_functors :
    (groupoidEquivalence K L R c hfaces vertices fixed).functor ⋙
      affineRestrictionFunctor U L R c hfaces fixed vertices =
    ClosedRegion.repairRestrictionFunctor U (tower K L R c hfaces) vertices fixed ⋙
      (groupoidEquivalence (ClosedRegion.presentation U) (restrictOperations U L) (restrictOperations U R)
        (fun f => c f.1) (restricted_faces U R hfaces)
        (ClosedRegion.restrictedVertices U vertices) (ClosedRegion.restrictedEdges U fixed)).functor := rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
