import ResearchLean.AG.AtlasCoefficientFiber.LawSupportFamilies
import ResearchLean.AG.AtlasCoefficientFiber.SupportEmpty

/-!
# G-135 D：原Law図式の空台・空Law

## Implementation notes

空台の元P制限とliteral R制限、空Lawの発生ラベルの不在をそのまま使う。
非空性仮定を足さず、同じcanonical全族座標の次数別単射で零性を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision AtlasDefectComposition
universe u

/-- Law添字が空なら同じ元発生ラベルも空である。 -/
theorem lawSupportLabels_empty {Source : Type u} (laws : FiniteLawFamily Source) [IsEmpty laws.Law] :
    IsEmpty (LawValueLabel laws) := ⟨fun l => isEmptyElim l.law⟩

/-- 空添字の元複体族へ同型なら、元複体の全整数次数が零加群。 -/
theorem coefficientFamily_emptyDegree {J : Type u} [IsEmpty J]
    {X : CochainComplex (ModuleCat.{u} ℚ) ℤ}
    {F : J → CochainComplex (ModuleCat.{u} ℚ) ℤ}
    (e : X ≅ FiniteComplexFamily.complex F) (n : ℤ) : Subsingleton (X.X n) := by
  letI : ∀ j, Subsingleton ((F j).X n) := fun j => isEmptyElim j
  letI := FiniteComplexFamily.degreeSubsingleton F n
  constructor
  intro x y
  apply ((HomologicalComplex.eval _ _ n).mapIso e).toLinearEquiv.injective
  change (e.hom.f n) x = (e.hom.f n) y
  exact Subsingleton.elim _ _

variable {Source : Type u} [finiteSource : Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 同じ原Law Pの空台への射は全整数次数で零写像。 -/
theorem lawSupportP_empty (l : LawValueLabel laws) :
    lawSupportP M laws ha l (Set.empty_subset _) = 0 := by
  rw [lawSupportP_projection]
  have hz : zeroExtensionMap (supportPushforwardHom M (Set.empty_subset (labelValueFiber laws qc ha l))) = 0 := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    by_cases h0 : n = 0
    · subst n
      rw [zeroExtensionMap_f0_apply, supportPushforwardHom_f0, supportPushforward0_empty]
      rfl
    by_cases h1 : n = 1
    · subst n
      rw [zeroExtensionMap_f1_apply, supportPushforwardHom_f1, supportPushforward1_empty]
      rfl
    by_cases h2 : n = 2
    · subst n
      rw [zeroExtensionMap_f2_apply, supportPushforwardHom_f2, supportPushforward2_empty]
      rfl
    rw [zeroExtensionMap_f, degreeMap_out _ n h0 h1 h2]
    rfl
  rw [hz, comp_zero]

omit finiteSource in
/-- 空台への同じ原Law literal R射は直接Phi制限による零写像。 -/
theorem lawSupportR_empty (l : LawValueLabel laws) :
    lawSupportR M laws ha l (Set.empty_subset _) = 0 := by
  apply LinearMap.ext
  intro z
  rw [lawSupportR_apply, supportFiberR_empty]
  rfl

variable [IsEmpty laws.Law]

/-- 空Lawの元Pはcanonical座標の全整数次数で零となる。 -/
theorem lawSupportEmptyP (n : ℤ) :
    Subsingleton ((zeroExtension (lawPushforwardComplex M laws ha)).X n) := by
  letI := lawSupportLabels_empty laws
  exact coefficientFamily_emptyDegree (lawPushforwardStandardIso M laws ha) n
/-- 空Lawの元細cochainはcanonical座標の全整数次数で零となる。 -/
theorem lawSupportEmptyFine (n : ℤ) :
    Subsingleton ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).X n) := by
  letI := lawSupportLabels_empty laws
  exact coefficientFamily_emptyDegree (lawFineStandardIso (Nf := Nf) (h := h) laws ha) n
/-- 空Lawの元Qはcanonical座標の全整数次数で零となる。 -/
theorem lawSupportEmptyQ (n : ℤ) :
    Subsingleton ((zeroExtension (lawRestrictionComplex M laws ha)).X n) := by
  letI := lawSupportLabels_empty laws
  exact coefficientFamily_emptyDegree (lawRestrictionStandardIso M laws ha) n
/-- 空Lawの元粗cochainはcanonical座標の全整数次数で零となる。 -/
theorem lawSupportEmptyCoarse (n : ℤ) :
    Subsingleton ((zeroExtension (Nc.lawGeneratedComplex laws ha)).X n) := by
  letI := lawSupportLabels_empty laws
  exact coefficientFamily_emptyDegree (lawCoarseStandardIso (Nc := Nc) laws ha) n

omit finiteSource in
/-- 空Lawのliteral原κ*核も元ラベル族同型により零となる。 -/
theorem lawSupportEmptyR : Subsingleton (lawR M laws ha) := by
  letI := lawSupportLabels_empty laws
  exact (lawRFamilyEquiv M laws ha).injective.subsingleton

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportLabels_empty
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFamily_emptyDegree
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportP_empty
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportR_empty
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyP
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyFine
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyQ
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyCoarse
#print axioms AAT.AG.AtlasCoefficientFiber.lawSupportEmptyR
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
