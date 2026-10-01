import ResearchLean.AG.RelativeRepairComposition.AffinePrimitiveDefect
import ResearchLean.AG.RelativeRepairComposition.AffineVectorLinear

/-!
# Every parameter is realized by primitive full affine operations

## Implementation notes

The parameter maps describe actual original-edge, reference-edge and comparison
translations. The same linear parts and original typed geometry stay fixed. The
right-hand-side linear map is computed from those translations and full word
maps. It is not a supplied assertion about the resulting native defect. Conditions
on the input family are proved separately from this construction of every value.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG uV
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → A)) (η : V →ₗ[k] (K.TwoCell → A))

/-- Each parameter realizes the arbitrary original edges as full actual affine operations. -/
def familyOriginal (v : V) : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A :=
  translatedOperations K L (θL v)

/-- Each parameter realizes the reference edges with their same full original linear components. -/
def familyReference (v : V) : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A :=
  translatedOperations K R (θR v)

/-- Each parameter realizes every specified original comparison translation. -/
def familyComparisons (v : V) : K.TwoCell → A := c + η v

/-- Zero parameter restores every original operation. -/
theorem family_original_zero {i j : K.Vertex} (e : K.Edge i j) :
    familyOriginal K L θL 0 e = L e := by
  change translation (k := k) ((θL 0) ⟨_,_,e⟩) * L e = L e
  rw [map_zero]
  change translation (k := k) (0 : A) * L e = L e
  rw [translation_zero, one_mul]

/-- Zero parameter restores every original reference operation. -/
theorem family_reference_zero {i j : K.Vertex} (e : K.Edge i j) :
    familyReference K R θR 0 e = R e := family_original_zero K R θR e

/-- Zero parameter restores every specified original comparison vector. -/
theorem family_comparisons_zero : familyComparisons K c η 0 = c := by
  unfold familyComparisons
  rw [map_zero, add_zero]

/-- All parameters preserve both original reference-word linear components and their alignment. -/
theorem family_aligned
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V) (f : K.TwoCell) :
    (GroupExtension.pathValue K (familyReference K R θR v) (K.twoLeft f)).linear =
      (GroupExtension.pathValue K (familyReference K R θR v) (K.twoRight f)).linear := by
  unfold familyReference
  rw [translated_word_linear, translated_word_linear]
  exact hfaces f

/-- The whole original native tower is generated for every parameter, retaining its actual original edges. -/
noncomputable def familyTower
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V) :=
  tower K (familyOriginal K L θL v) (familyReference K R θR v)
    (familyComparisons K c η v) (family_aligned K R θR hfaces v)

/-- Every parameterized original input edge survives the same native tower construction. -/
theorem family_tower_original
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V)
    {i j : K.Vertex} (e : K.Edge i j) :
    (familyTower K L R c θL θR η hfaces v).original.edgeLift e = familyOriginal K L θL v e := rfl

/-- Every parameterized reference edge survives selection with its real translation value. -/
theorem family_tower_reference
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V)
    {i j : K.Vertex} (e : K.Edge i j) :
    (familyTower K L R c θL θR η hfaces v).toTower.upper.edgeLift e =
      familyReference K R θR v e := tower_reference_edge _ _ _ _ _ _

/-- The original core is fixed even when both original and reference translations vary. -/
theorem family_core (v : V) {i j : K.Vertex} (e : K.Edge i j) :
    core K (familyOriginal K L θL v) (familyReference K R θR v) e = core K L R e := by
  unfold core
  congr 1

/-- The full defect's linear parameter term is generated from comparisons and both original word contributions. -/
def familyDefectLinear : V →ₗ[k] (K.TwoCell → A) :=
  η + (vectorFaceDifferential K R).comp θR

/-- Primitive affine evaluation produces the affine defect family for every parameter and every original face. -/
theorem family_defect_affine
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V) (f : K.TwoCell) :
    realDefectVector K (familyReference K R θR v) (familyComparisons K c η v) f =
      realDefectVector K R c f + familyDefectLinear K R θR η v f := by
  unfold familyReference familyComparisons
  rw [translated_defect K R c (θR v) (η v) f (hfaces f)]
  change realDefectVector K R c f + η v f + vectorPath K R (θR v) (K.twoLeft f) -
    vectorPath K R (θR v) (K.twoRight f) =
      realDefectVector K R c f + (η v f +
        (vectorPath K R (θR v) (K.twoLeft f) - vectorPath K R (θR v) (K.twoRight f)))
  abel

/-- The same generated native full-kernel defect has exactly the primitive affine value, not an assumed RHS. -/
theorem family_defect_native
    (hfaces : ∀ f : K.TwoCell,
      (GroupExtension.pathValue K R (K.twoLeft f)).linear =
        (GroupExtension.pathValue K R (K.twoRight f)).linear) (v : V) (f : K.TwoCell) :
    coefficient K (familyOriginal K L θL v) (familyReference K R θR v)
        (familyComparisons K c η v) (family_aligned K R θR hfaces v) (K.twoTarget f)
        ((familyTower K L R c θL θR η hfaces v).toTower.defect f) =
      realDefectVector K R c f + familyDefectLinear K R θR η v f := by
  unfold familyTower
  rw [real_defect_native]
  exact family_defect_affine K R c θR η hfaces v f

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
