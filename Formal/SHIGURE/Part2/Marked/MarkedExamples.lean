import Formal.SHIGURE.Part2.Marked.MarkedRealizations
import Formal.SHIGURE.Part2.Families.SchemeLawExamples

/-! # Nondegenerate marked realization examples

The fixed nonempty nullary-Law presentation acts on the rank-one
structure sheaf of `Spec ℤ`. Two named generators mark it by `(1,0)`.
The first selected column is a basis and the second is not, although
the full marking is surjective. The zero marking supplies the negative
surjectivity example on the same nonzero carrier.

## Implementation notes

The sheaf marking is the coproduct descent map of the identity and zero.
Its splitting and selected-column computations use the actual free-sheaf
coproduct universal property. The affine witnesses read the same carrier
on the whole affine open, keeping the written Law and rank evidence.
-/

namespace SHIGURE.RealizationFamilies.Marked.Examples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite SchemeDescent
open SchemeLawExamples

noncomputable section

/-- The nonempty affine base of all marked fixtures. -/
abbrev integerScheme := Spec (CommRingCat.of ℤ)

/-- The same rank-one realization underlies all positive and negative
markings; its actual nullary primitive satisfies the fixed written Law. -/
def integerRealization : SchemeRealization vanishingSectionLaws (fun _ => 1)
    (𝟙 integerScheme) :=
  ⟨sectionStructure 0, zeroSection_schemeRealizationProperty⟩

/-- The concrete rank-one free sheaf is canonically the structure sheaf,
using its singleton set of named generators. -/
def rankOneFreeIso : freeModuleSheaf integerScheme 1 ≅ unitModule integerScheme :=
  coproductUniqueIso (fun _ : ULift (Fin 1) => unitModule integerScheme)

/-- The two-generator marking sends the first generator to `1` and the
second to `0`, as actual morphisms of module sheaves. -/
def firstGeneratorMarking : freeModuleSheaf integerScheme 2 ⟶ unitModule integerScheme :=
  Sigma.desc (fun i : ULift (Fin 2) => if i.down = 0 then 𝟙 _ else 0)

/-- The coproduct marking reads exactly the declared generator vector. -/
theorem firstGeneratorMarking_ι (i : ULift (Fin 2)) :
    SheafOfModules.ιFree i ≫ firstGeneratorMarking =
      if i.down = 0 then 𝟙 (unitModule integerScheme) else 0 := by
  exact Sigma.ι_desc _ i

/-- Marked data with the surjective marking `(1,0)` on a nonzero rank-one carrier. -/
def firstMarkedData : SchemeMarkedData vanishingSectionLaws (fun _ => 2) (fun _ => 1)
    (𝟙 integerScheme) where
  realization := integerRealization
  marking _ := firstGeneratorMarking

/-- Zero marking on the very same realization, used to test surjectivity. -/
def zeroMarkedData : SchemeMarkedData vanishingSectionLaws (fun _ => 2) (fun _ => 1)
    (𝟙 integerScheme) where
  realization := integerRealization
  marking _ := 0

/-- The first generator splits `(1,0)`, proving genuine sheaf epimorphy. -/
theorem firstMarkedData_isSurjective : firstMarkedData.IsSurjective := by
  intro s
  change Epi firstGeneratorMarking
  have split : SheafOfModules.ιFree (⟨0⟩ : ULift (Fin 2)) ≫ firstGeneratorMarking = 𝟙 _ := by
    simpa only [ite_true] using firstGeneratorMarking_ι (⟨0⟩ : ULift (Fin 2))
  exact epi_of_epi_fac split

/-- The structure sheaf on `Spec ℤ` is nonzero, as detected on its global
unit section by the canonical global-section isomorphism. -/
theorem integerUnit_id_ne_zero : (𝟙 (unitModule integerScheme)) ≠ 0 := by
  intro h
  have value := congrArg (fun f : unitModule integerScheme ⟶ unitModule integerScheme =>
    f.val.app (op (⊤ : integerScheme.Opens)) (1 : Γ(integerScheme, ⊤))) h
  change (1 : Γ(integerScheme, ⊤)) = 0 at value
  have integerValue := congrArg (fun r => (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom r) value
  exact (by decide : (1 : ℤ) ≠ 0) (by simpa only [map_one, map_zero] using integerValue)

/-- The zero marking is not an epimorphism on this same nonzero carrier. -/
theorem zeroMarkedData_not_isSurjective : ¬ zeroMarkedData.IsSurjective := by
  intro h
  letI : Epi (0 : freeModuleSheaf integerScheme 2 ⟶ unitModule integerScheme) := h ()
  exact integerUnit_id_ne_zero ((cancel_epi (0 : freeModuleSheaf integerScheme 2 ⟶
    unitModule integerScheme)).mp (by simp))

/-- The object-property spelling of marked surjectivity accepts `(1,0)`. -/
theorem firstMarkedData_schemeMarkedProperty :
    schemeMarkedProperty vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      (𝟙 integerScheme) firstMarkedData :=
  firstMarkedData_isSurjective

/-- The same object property rejects the zero marking. -/
theorem zeroMarkedData_not_schemeMarkedProperty :
    ¬ schemeMarkedProperty vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      (𝟙 integerScheme) zeroMarkedData :=
  zeroMarkedData_not_isSurjective

/-- A fixed surjectively marked rank-one realization with two generators. -/
def firstMarkedRealization : SchemeMarkedRealization vanishingSectionLaws
    (fun _ => 2) (fun _ => 1) (𝟙 integerScheme) :=
  ⟨firstMarkedData, firstMarkedData_isSurjective⟩

/-- Select one of the two named columns, preserving the required increasing order. -/
def columnChoice (j : Fin 2) : ChartIndex (sig := sectionSignature) (fun _ => 2) (fun _ => 1) :=
  fun _ => ⟨⟨fun _ => j, fun a b _ => Subsingleton.elim a b⟩,
    by
      intro a b
      have equal : a = b := Subsingleton.elim _ _
      subst b
      exact iff_of_true le_rfl le_rfl⟩

/-- The selected column morphism is identity for column zero and zero
for column one, interpreted through the canonical rank-one free comparison. -/
theorem selected_column_marking (j : Fin 2) :
    selectedGeneratorMap (fun _ => 2) (fun _ => 1) (columnChoice j) () ≫
      firstGeneratorMarking = if j = 0 then rankOneFreeIso.hom else 0 := by
  apply (SheafOfModules.isColimitFreeCofan (R := integerScheme.ringCatSheaf) (ULift (Fin 1))).hom_ext
  rintro ⟨i⟩
  change SheafOfModules.ιFree i ≫ _ = SheafOfModules.ιFree i ≫ _
  rw [← Category.assoc]
  change (SheafOfModules.ιFree i ≫ SheafOfModules.freeMap
    (fun _ : ULift (Fin 1) => (⟨j⟩ : ULift (Fin 2)))) ≫ firstGeneratorMarking = _
  rw [SheafOfModules.ιFree_freeMap, firstGeneratorMarking_ι]
  by_cases h : j = 0
  · subst j
    change 𝟙 (unitModule integerScheme) = SheafOfModules.ιFree i ≫ rankOneFreeIso.hom
    have comp := (colimit.isColimit (Discrete.functor (fun _ : ULift (Fin 1) =>
      unitModule integerScheme))).comp_coconePointUniqueUpToIso_hom
        (colimitCoconeOfUnique (fun _ : ULift (Fin 1) => unitModule integerScheme)).isColimit
        (Discrete.mk i)
    change SheafOfModules.ιFree i ≫ rankOneFreeIso.hom = 𝟙 _ at comp
    exact comp.symm
  · simp [h]

/-- The first column is a basis of the actual nonzero rank-one carrier. -/
theorem firstColumn_hasBasisColumns :
    hasBasisColumns vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      (columnChoice 0) firstMarkedRealization := by
  intro s
  change IsIso (selectedGeneratorMap (fun _ => 2) (fun _ => 1) (columnChoice 0) s ≫
    firstGeneratorMarking)
  cases s
  rw [selected_column_marking]
  simp only [ite_true]
  infer_instance

/-- The second column is not a basis of the same surjectively marked
realization: its selected morphism is zero into a nonzero carrier. -/
theorem secondColumn_not_hasBasisColumns :
    ¬ hasBasisColumns vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      (columnChoice 1) firstMarkedRealization := by
  intro h
  have iso := h ()
  change IsIso (selectedGeneratorMap (fun _ => 2) (fun _ => 1) (columnChoice 1) () ≫
    firstGeneratorMarking) at iso
  rw [selected_column_marking, if_neg (by decide : (1 : Fin 2) ≠ 0)] at iso
  letI := iso
  exact integerUnit_id_ne_zero ((cancel_epi (0 : freeModuleSheaf integerScheme 1 ⟶
    unitModule integerScheme)).mp (by simp))


/-- The whole affine open reads the same rank-one Lawful sheaf realization
as an actual affine realization over its canonical section coefficient ring. -/
def affineIntegerRealization : AffineRealization vanishingSectionLaws (fun _ => 1)
    (sectionBaseMap (𝟙 integerScheme) ⊤) :=
  ⟨sectionsStructure (sectionStructure 0) ⊤,
    schemeRealizationProperty_affine zeroSection_schemeRealizationProperty
      ⟨⊤, isAffineOpen_top _⟩⟩

/-- The affine marking `(1,0)` is projection onto the first coordinate
of the same nonzero section module. -/
def affineFirstMarkedData : AffineMarkedData vanishingSectionLaws (fun _ => 2) (fun _ => 1)
    (sectionBaseMap (𝟙 integerScheme) ⊤) where
  realization := affineIntegerRealization
  marking _ := (LinearMap.proj 0 : (Fin 2 → Γ(integerScheme, ⊤)) →ₗ[Γ(integerScheme, ⊤)]
    Γ(integerScheme, ⊤))

/-- The zero affine marking keeps exactly the same realization and carrier. -/
def affineZeroMarkedData : AffineMarkedData vanishingSectionLaws (fun _ => 2) (fun _ => 1)
    (sectionBaseMap (𝟙 integerScheme) ⊤) where
  realization := affineIntegerRealization
  marking _ := 0

/-- The affine projection marking is surjective, with an explicit preimage
for every section. -/
theorem affineFirstMarkedData_surjective :
    affineMarkingsSurjective vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      affineFirstMarkedData := by
  intro s x
  exact ⟨fun _ => x, rfl⟩

/-- The zero affine marking misses the unit section on `Spec ℤ`, proving
the negative affine surjectivity instance on a nonzero rank-one carrier. -/
theorem affineZeroMarkedData_not_surjective :
    ¬ affineMarkingsSurjective vanishingSectionLaws (fun _ => 2) (fun _ => 1)
      affineZeroMarkedData := by
  intro h
  obtain ⟨x, hx⟩ := h () (1 : Γ(integerScheme, ⊤))
  have equal : (0 : Γ(integerScheme, ⊤)) = 1 := hx
  have integerValue := congrArg (fun r => (Scheme.ΓSpecIso (CommRingCat.of ℤ)).hom r) equal
  exact (by decide : (0 : ℤ) ≠ 1) (by simpa only [map_zero, map_one] using integerValue)

end

end SHIGURE.RealizationFamilies.Marked.Examples
