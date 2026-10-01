import ResearchLean.AG.RelativeRepairComposition.NativeAffineDifferentials

/-!
# Linear translation contributions of the full original words and pastings

## Implementation notes

Each map evaluates the full original recursive expression with fixed real linear
transport. Its linearity follows by induction on that expression. Incidence-only
columns would omit repeated occurrences and whiskered suffix transports.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)

/-- The complete original path translation sum is linear in all named edge vectors. -/
def vectorPathLinear {i j : K.Vertex} (w : K.Path i j) :
    (EdgeName (K := K) → A) →ₗ[k] A where
  toFun h := vectorPath K R h w
  map_add' h g := by
    induction w with
    | nil _ => exact (zero_add 0).symm
    | cons e w ih =>
      change (GroupExtension.pathValue K R w).linear (h ⟨_,_,e⟩ + g ⟨_,_,e⟩) +
        vectorPath K R (h + g) w = _
      rw [map_add, ih]
      simp only [vectorPath]
      abel
  map_smul' t h := by
    induction w with
    | nil _ => exact (smul_zero t).symm
    | cons e w ih =>
      change (GroupExtension.pathValue K R w).linear (t • h ⟨_,_,e⟩) +
        vectorPath K R (t • h) w = t • _
      rw [map_smul, ih]
      simp only [vectorPath, RingHom.id_apply, smul_add]

/-- The full original face differential is the difference of its two word-linear maps. -/
def vectorFaceDifferential : (EdgeName (K := K) → A) →ₗ[k] (K.TwoCell → A) :=
  LinearMap.pi fun f => vectorPathLinear K R (K.twoLeft f) - vectorPathLinear K R (K.twoRight f)

/-- Each original oriented whiskered face contributes a linear transported comparison vector. -/
def vectorFaceLinear {s t : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) : (K.TwoCell → A) →ₗ[k] A :=
  match f.orientation with
  | .forward => (GroupExtension.pathValue K R f.outgoing).linear.toLinearMap.comp (LinearMap.proj f.cell)
  | .backward => -((GroupExtension.pathValue K R f.outgoing).linear.toLinearMap.comp (LinearMap.proj f.cell))

/-- The original real oriented-face evaluation is exactly its generated linear map. -/
theorem vector_face_linear_value {s t : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation s t) (a : K.TwoCell → A) :
    vectorFaceLinear K R f a = vectorFace K R a f := by
  cases ho : f.orientation <;> simp [vectorFaceLinear, vectorFace, ho]

/-- Every occurrence in the complete original typed pasting contributes to the linear comparison sum. -/
def vectorPastingLinear {s t : K.Vertex} {w z : K.Path s t}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) : (K.TwoCell → A) →ₗ[k] A where
  toFun a := vectorPasting K R a p
  map_add' a b := by
    induction p with
    | nil _ => exact (zero_add 0).symm
    | cons step tail ih =>
      simp only [vectorPasting, ← vector_face_linear_value]
      rw [map_add, ih]
      abel
  map_smul' r a := by
    induction p with
    | nil _ => exact (smul_zero r).symm
    | cons step tail ih =>
      simp only [vectorPasting, ← vector_face_linear_value, RingHom.id_apply]
      rw [map_smul, ih]
      simp only [smul_add, RingHom.id_apply]

/-- The original real pasting evaluation is exactly its full generated linear map. -/
theorem vector_pasting_linear_value {s t : K.Vertex} {w z : K.Path s t}
    (p : RewritePasting K.toFiniteTransportTwoPresentation w z) (a : K.TwoCell → A) :
    vectorPastingLinear K R p a = vectorPasting K R a p := rfl

/-- The original degree-two comparison differential retains both full typed pasting routes. -/
def vectorPastingDifferential : (K.TwoCell → A) →ₗ[k] (K.ThreeCell → A) :=
  LinearMap.pi fun s => vectorPastingLinear K R (K.threeLeft s) - vectorPastingLinear K R (K.threeRight s)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
