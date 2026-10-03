import ResearchLean.AG.RelativeRepairComposition.W5ActualRepairs

/-! # Independent W5 local repairs and the physically fixed overlap

Local objects are actual whole affine operations on the original selected
cells. The shared edge is free on the overlap, while every original vertex
label vanishes because both endpoints belong to the same physical P.
-/
namespace AAT.AG.RelativeRepairComposition.W5LocalRepairs
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine W5AffineInput W5Regions W5AuthoredOperations W5ActualRepairs
attribute [local instance] Classical.propDecidable

/-- All independent actual repairs on any original closed patch. -/
abbrev LocalRepairs (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry) :=
  NativeAffine.Repair (ClosedRegion.presentation U) (restrictOperations U (reference b₁ b₂))
    (fun f => comparison f.1) (ClosedRegion.restrictedEdges U fixedRegion.edges)
/-- The original full actual local groupoid retains its complete label family. -/
abbrev LocalCategory (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry) :=
  NativeAffine.Groupoid (ClosedRegion.presentation U) (restrictOperations U (reference b₁ b₂))
    (restrictOperations U (reference b₁ b₂)) (fun f => comparison f.1)
    (restricted_faces U (reference b₁ b₂) (linear_faces b₁ b₂))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U fixedRegion.edges)
/-- Every original translation label on the patch with the actual physical conditions. -/
noncomputable abbrev LocalLabels (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry) :=
  gaugeLabels (ClosedRegion.presentation U) (restrictOperations U (reference b₁ b₂))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U fixedRegion.edges)
/-- Full actual global labels act by the original affine gauge formula. -/
noncomputable local instance globalAction (b₁ b₂ : ZMod 2) :
    AddAction (gaugeLabels geometry (reference b₁ b₂) fixedRegion.vertices fixedRegion.edges) (RealRepairs b₁ b₂) :=
  gaugeAddAction geometry (reference b₁ b₂) (reference b₁ b₂) comparison (linear_faces b₁ b₂)
    fixedRegion.vertices fixedRegion.edges
/-- Full local labels act by the same original restricted gauge formula. -/
noncomputable local instance localAction (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry) :
    AddAction (LocalLabels b₁ b₂ U) (LocalRepairs b₁ b₂ U) :=
  gaugeAddAction (ClosedRegion.presentation U) (restrictOperations U (reference b₁ b₂))
    (restrictOperations U (reference b₁ b₂)) (fun f => comparison f.1)
    (restricted_faces U (reference b₁ b₂) (linear_faces b₁ b₂))
    (ClosedRegion.restrictedVertices U fixedRegion.vertices)
    (ClosedRegion.restrictedEdges U fixedRegion.edges)

/-- The full label family is zero by the original physical fixed vertices. -/
theorem labels_zero (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry)
    (a : LocalLabels b₁ b₂ U) : a = 0 := by
  apply Subtype.ext
  funext v
  exact a.2.1 v (Set.mem_univ _)
/-- Each selected original typed name is restored without changing its endpoints. -/
def localName (U : ClosedRegion geometry) (n : Fin 3) (hn : name n ∈ U.edges) :=
  (ClosedRegion.edgeNameEquiv U).symm ⟨name n,hn⟩
/-- Read the independent original shared operation at zero. -/
def localValue (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges)
    {b₁ b₂ : ZMod 2} (R : LocalRepairs b₁ b₂ U) : ZMod 2 :=
  R.operation (localName U edgeE he).2.2 0
/-- The original linear part determines every local map from its whole zero value. -/
theorem local_operation_apply (U : ClosedRegion geometry) {b₁ b₂ : ZMod 2}
    (R : LocalRepairs b₁ b₂ U) {i j : (ClosedRegion.presentation U).Vertex}
    (e : (ClosedRegion.presentation U).Edge i j) (x : ZMod 2) :
    R.operation e x = x + R.operation e 0 := by
  rw [NativeAffine.operation_apply,R.linear]
  change (reference b₁ b₂ e.1).linear x + _ = _
  rw [reference_linear]
  rfl
/-- Every selected physical input is the same unchanged original actual map. -/
theorem local_fixed_map (U : ClosedRegion geometry) {b₁ b₂ : ZMod 2}
    (R : LocalRepairs b₁ b₂ U) {i j : (ClosedRegion.presentation U).Vertex}
    (e : (ClosedRegion.presentation U).Edge i j)
    (h : (ClosedRegion.edgeNameEquiv U ⟨i,j,e⟩).1 ∈ fixedRegion.edges) :
    R.operation e = reference b₁ b₂ e.1 := R.fixed_value ⟨i,j,e⟩ h
/-- Every full local map is reconstructed from the original shared value and original fixed inputs. -/
theorem localValue_operations (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges)
    {b₁ b₂ : ZMod 2} (R : LocalRepairs b₁ b₂ U) :
    @restrictOperations _ _ _ _ _ _ U (operation b₁ b₂ (localValue U he R)) = @R.operation := by
  funext i j e
  rcases i with ⟨i,hi⟩
  rcases j with ⟨j,hj⟩
  rcases e with ⟨⟨e,hs,ht⟩,hu⟩
  cases hs
  cases ht
  fin_cases e
  · apply AffineEquiv.ext
    intro x
    change operation b₁ b₂ (localValue U he R) (name edgeE).2.2 x = _
    rw [operation_e_apply,local_operation_apply]
    rfl
  · change operation b₁ b₂ (localValue U he R) (name edgeA).2.2 = R.operation (localName U edgeA hu).2.2
    rw [local_fixed_map U R (localName U edgeA hu).2.2 (Or.inl rfl)]
    apply AffineEquiv.ext
    intro x
    change operation b₁ b₂ (localValue U he R) (name edgeA).2.2 x = reference b₁ b₂ (name edgeA).2.2 x
    rw [operation_a_apply, reference_a_apply]
  · change operation b₁ b₂ (localValue U he R) (name edgeB).2.2 = R.operation (localName U edgeB hu).2.2
    rw [local_fixed_map U R (localName U edgeB hu).2.2 (Or.inr rfl)]
    apply AffineEquiv.ext
    intro x
    change operation b₁ b₂ (localValue U he R) (name edgeB).2.2 x = reference b₁ b₂ (name edgeB).2.2 x
    rw [operation_b_apply, reference_b_apply]
/-- Every independent selected actual face imposes its original scalar equation. -/
theorem localValue_face (U : ClosedRegion geometry) (he : name edgeE ∈ U.edges)
    {b₁ b₂ : ZMod 2} (R : LocalRepairs b₁ b₂ U) (f : U.faces) :
    localValue U he R = inputValue b₁ b₂ f.1 := by
  have hf := R.face f
  rw [← localValue_operations U he R,restricted_path_value,restricted_path_value] at hf
  change translation (k := ZMod 2) (comparison f.1) *
    GroupExtension.pathValue geometry (operation b₁ b₂ (localValue U he R))
      (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoLeft f)) =
    GroupExtension.pathValue geometry (operation b₁ b₂ (localValue U he R))
      (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoRight f)) at hf
  rw [ClosedRegion.forget_two_left,ClosedRegion.forget_two_right] at hf
  exact (face_iff b₁ b₂ _ f.1).mp hf
/-- The scalar conditions for the selected original faces construct all full local affine maps. -/
noncomputable def localFromValue (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry)
    (u : ZMod 2) (hf : ∀ f ∈ U.faces, u = inputValue b₁ b₂ f) : LocalRepairs b₁ b₂ U where
  operation := restrictOperations U (operation b₁ b₂ u)
  linear e := operation_linear b₁ b₂ u e.1
  face f := by
    rw [restricted_path_value,restricted_path_value]
    change translation (k := ZMod 2) (comparison f.1) *
      GroupExtension.pathValue geometry (operation b₁ b₂ u)
        (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoLeft f)) =
      GroupExtension.pathValue geometry (operation b₁ b₂ u)
        (ClosedRegion.forgetPath U ((ClosedRegion.twoPresentation U).twoRight f))
    rw [ClosedRegion.forget_two_left,ClosedRegion.forget_two_right]
    exact (face_iff b₁ b₂ u f.1).mpr (hf f.1 f.2)
  fixed_value e he := operation_fixed b₁ b₂ u (ClosedRegion.edgeNameEquiv U e).1 he
/-- Reading a constructed local shared operation restores the same full value. -/
theorem localValue_from (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry)
    (he : name edgeE ∈ U.edges) (u : ZMod 2)
    (hf : ∀ f ∈ U.faces, u = inputValue b₁ b₂ f) :
    localValue U he (localFromValue b₁ b₂ U u hf) = u := by
  change operation b₁ b₂ u (name edgeE).2.2 0 = u
  rw [operation_e_apply,zero_add]
/-- The indexed patch always has an actual local plan on its same original face. -/
noncomputable def localPlan (b₁ b₂ : ZMod 2) (side : Bool) : LocalRepairs b₁ b₂ (region side) :=
  localFromValue b₁ b₂ (region side) (inputValue b₁ b₂ side) (by
    intro f hf
    cases side
    · have hf' : f = false := hf
      rw [hf']
    · have hf' : f = true := hf
      rw [hf'])
/-- Each original indexed patch contains the original shared e. -/
theorem patch_shared (side : Bool) : name edgeE ∈ (region side).edges := by
  rw [region_edges]
  exact Or.inl rfl
/-- Every independent actual local plan derives its same physical input value. -/
theorem localValue_input (b₁ b₂ : ZMod 2) (side : Bool) (R : LocalRepairs b₁ b₂ (region side)) :
    localValue (region side) (patch_shared side) R = inputValue b₁ b₂ side :=
  localValue_face (region side) (patch_shared side) R ⟨side,face_in_region side⟩
/-- Every whole independent actual local object is the restored original plan on that same patch. -/
theorem local_unique (b₁ b₂ : ZMod 2) (side : Bool) (R : LocalRepairs b₁ b₂ (region side)) :
    localPlan b₁ b₂ side = R := by
  have hm := localValue_operations (region side) (patch_shared side) R
  rw [localValue_input b₁ b₂ side R] at hm
  apply NativeAffine.Repair.ext
  intro i j e
  exact congrFun (congrFun (congrFun hm i) j) e

/-- The same overlap has the original shared edge. -/
theorem overlap_has_shared : name edgeE ∈ overlap.edges := by rw [overlap_edges]; rfl
/-- Neither selected original face restricts to the overlap. -/
theorem overlap_no_face (f : Bool) (hf : f ∈ overlap.faces) : False := by
  rw [overlap_faces] at hf
  exact hf.elim
/-- The whole original overlap repair family and F2 have both inverse object coordinates. -/
noncomputable def overlapValueEquiv (b₁ b₂ : ZMod 2) : LocalRepairs b₁ b₂ overlap ≃ ZMod 2 where
  toFun := localValue overlap overlap_has_shared
  invFun u := localFromValue b₁ b₂ overlap u (by intro f hf; exact (overlap_no_face f hf).elim)
  left_inv R := by
    apply NativeAffine.Repair.ext
    intro i j e
    exact congrFun (congrFun (congrFun (localValue_operations overlap overlap_has_shared R) i) j) e
  right_inv u := localValue_from b₁ b₂ overlap overlap_has_shared u _
/-- Actual global restriction keeps each original operation and all original vertex labels. -/
noncomputable def actualRestriction (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry) :
    ActualCategory b₁ b₂ ⥤ LocalCategory b₁ b₂ U :=
  affineRestrictionFunctor U (reference b₁ b₂) (reference b₁ b₂) comparison (linear_faces b₁ b₂)
    fixedRegion.edges fixedRegion.vertices
/-- The actual restriction functor retains the exact original selected operation. -/
theorem restriction_operation (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry)
    (R : ActualCategory b₁ b₂) {i j : (ClosedRegion.presentation U).Vertex}
    (e : (ClosedRegion.presentation U).Edge i j) :
    ((actualRestriction b₁ b₂ U).obj R).back.operation e = R.back.operation e.1 := rfl
/-- All restricted actual arrow labels remain the exact same original vertex values. -/
theorem restriction_label (b₁ b₂ : ZMod 2) (U : ClosedRegion geometry)
    {R Q : ActualCategory b₁ b₂} (f : R ⟶ Q) (v : (ClosedRegion.presentation U).Vertex) :
    ((actualRestriction b₁ b₂ U).map f).1.toAdd.1 v = f.1.toAdd.1 v.1 := rfl

end AAT.AG.RelativeRepairComposition.W5LocalRepairs
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.W5LocalRepairs
