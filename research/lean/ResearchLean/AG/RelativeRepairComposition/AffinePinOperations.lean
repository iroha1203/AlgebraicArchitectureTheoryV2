import ResearchLean.AG.RelativeRepairComposition.ParallelPinIncidence
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection

/-!
# Real affine operations on parallel-pin geometry

The original pin operation is the same arbitrary original L. Its reference is
translation by the specified correction followed by the old R. All original
comparison words and full three-cell laws are preserved by their typed copies.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
local notation "J" => ParallelPinGeometry.presentation K

/-- Assign real operations separately to the old and newly named parallel edges. -/
def extendOperation
    (old pin : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A) :
    ∀ {i j : (J).Vertex}, (J).Edge i j → Operations k A :=
  fun e => match e with | .inl e => old e | .inr e => pin e

/-- Restriction reads exactly the old real operations in the extended geometry. -/
def oldOperation (O : ∀ {i j : (J).Vertex}, (J).Edge i j → Operations k A) :
    ∀ {i j : K.Vertex}, K.Edge i j → Operations k A := fun e => O (.inl e)

/-- The complete copied old word evaluates the same actual operations in order. -/
theorem included_word_value (O : ∀ {i j : (J).Vertex}, (J).Edge i j → Operations k A)
    {i j : K.Vertex} (w : K.Path i j) :
    GroupExtension.pathValue J O (ParallelPinGeometry.includePath K w) =
      GroupExtension.pathValue K (oldOperation K O) w := by
  induction w with
  | nil _ => rfl
  | cons e w ih =>
    change GroupExtension.pathValue J O (ParallelPinGeometry.includePath K w) * O (.inl e) = _
    rw [ih]
    rfl

/-- Old comparisons are retained, while each new parallel face has identity comparison. -/
def comparison (c : K.TwoCell → A) : (J).TwoCell → A :=
  fun f => match f with | .inl f => c f | .inr _ => 0

/-- The new reference is the actual full translation followed by the old reference operation. -/
def reference (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) :
    ∀ {i j : (J).Vertex}, (J).Edge i j → Operations k A :=
  extendOperation K R (fun {i j} e => translation (k := k) (t ⟨i,j,e⟩) * R e)

/-- The arbitrary original pin remains the same original edge L. -/
def original (L : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A) :
    ∀ {i j : (J).Vertex}, (J).Edge i j → Operations k A := extendOperation K L L

/-- Pin reference and old reference have precisely the same original linear transport. -/
theorem pin_linear (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) {i j : K.Vertex} (e : K.Edge i j) :
    (reference K R t (.inr e)).linear = (R e).linear := by
  change projection (translation (k := k) (t ⟨i,j,e⟩) * R e) = projection (R e)
  rw [map_mul, projection_translation, one_mul]

/-- The original affine core reselection agrees for old and pin edges. -/
theorem pin_core_projection
    (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) {i j : K.Vertex} (e : K.Edge i j) :
    projection (reference K R t (.inr e) * (original K L (.inr e))⁻¹) =
      projection (R e * (L e)⁻¹) := by
  rw [map_mul, map_mul]
  change (reference K R t (.inr e)).linear * projection (L e)⁻¹ = _
  rw [pin_linear]
  rfl

/-- The copied old face conditions and new pin linear equality generate all face alignment. -/
theorem reference_faces (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A)
    (hf : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) :
    ∀ f : (J).TwoCell,
      (GroupExtension.pathValue J (reference K R t) ((J).twoLeft f)).linear =
        (GroupExtension.pathValue J (reference K R t) ((J).twoRight f)).linear := by
  intro f
  cases f with
  | inl f =>
    change (GroupExtension.pathValue J (reference K R t)
        (ParallelPinGeometry.includePath K (K.twoLeft f))).linear =
      (GroupExtension.pathValue J (reference K R t)
        (ParallelPinGeometry.includePath K (K.twoRight f))).linear
    rw [included_word_value, included_word_value]
    exact hf f
  | inr e =>
    change (1 * R e.2.2).linear = (1 * reference K R t (.inr e.2.2)).linear
    rw [one_mul, one_mul, pin_linear]

/-- Every copied oriented comparison retains its full outgoing context operation. -/
theorem included_face_value
    (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) (c : K.TwoCell → A) {i j : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation i j) :
    faceOperation J (reference K R t) (comparison K c)
      (ParallelPinGeometry.includeFace K f) = faceOperation K R c f := by
  simp only [faceOperation, ParallelPinGeometry.includeFace, included_word_value]
  rfl

/-- Every full original three-cell route retains the same ordered real comparison product. -/
theorem included_pasting_value
    (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) (c : K.TwoCell → A) {i j : K.Vertex}
    {w z : K.Path i j} (p : RewritePasting K.toFiniteTransportTwoPresentation w z) :
    pastingOperation J (reference K R t) (comparison K c)
      (ParallelPinGeometry.includePasting K p) = pastingOperation K R c p := by
  induction p with
  | nil _ => rfl
  | cons s tail ih =>
    change pastingOperation J _ _ (ParallelPinGeometry.includePasting K tail) *
      faceOperation J _ _ (ParallelPinGeometry.includeFace K s.face) = _
    rw [ih, included_face_value]
    rfl

/-- Original authored three-cell laws hold on the new actual input with no new three-cells. -/
theorem reference_three_law
    (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
    (t : EdgeName (K := K) → A) (c : K.TwoCell → A)
    (hthree : ∀ f : K.ThreeCell,
      pastingOperation K R c (K.threeLeft f) = pastingOperation K R c (K.threeRight f)) :
    ∀ f : (J).ThreeCell,
      pastingOperation J (reference K R t) (comparison K c) ((J).threeLeft f) =
        pastingOperation J (reference K R t) (comparison K c) ((J).threeRight f) := by
  intro f
  change pastingOperation J (reference K R t) (comparison K c)
      (ParallelPinGeometry.includePasting K (K.threeLeft f)) =
    pastingOperation J (reference K R t) (comparison K c)
      (ParallelPinGeometry.includePasting K (K.threeRight f))
  rw [included_pasting_value, included_pasting_value]
  exact hthree f

end AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
