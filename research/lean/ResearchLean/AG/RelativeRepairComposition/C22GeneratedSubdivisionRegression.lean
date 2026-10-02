import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedInterfaces
import ResearchLean.AG.RelativeRepairComposition.C21LocalSubdivisionRegression
import ResearchLean.AG.RelativeRepairComposition.C19SubdivisionRangeRegression

/-!
# Independent generated interfaces on the same whole affine W4

## Implementation notes

The complete authored baa face, actual original flip, full native translation
kernels and specified factors are retained. Complete finite lists and bases are
constructed from these original inputs. Both actual local generators use the
general comparison, and every old and fresh value is retained on restoration.
-/
namespace AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
open NativeAffine Subdivision C17SubdivisionInput
open C20SubdivisionCoverRegression C21LocalSubdivisionRegression
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
attribute [local instance] Subdivision.LinearCoefficients.coefficientModules

/-- Equality of original complete W4 names is decided from their original Unit/Bool incidence. -/
local instance edgeDecidableEq : DecidableEq (EdgeName (K := geometry)) :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Σ _ : Unit, Bool))

/-- The original authored face equality is precisely Unit equality. -/
local instance faceDecidableEq : DecidableEq geometry.TwoCell := inferInstanceAs (DecidableEq Unit)

/-- The complete original vertex set decides every original vertex as included. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := geometry)).vertices) :=
  fun _ => isTrue trivial

/-- The complete original edge set decides every original complete edge name as included. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := geometry)).edges) :=
  fun _ => isTrue trivial

/-- The complete original face set decides the authored face as included. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := geometry)).faces) :=
  fun _ => isTrue trivial

/-- All original vertex memberships of both W4 members use their authored closed sets. -/
local instance regionsVerticesDecidable : ∀ j, DecidablePred (· ∈ (regions j).vertices) := by
  intro j v
  cases j <;> exact isTrue trivial

/-- Each original edge membership uses the complete member or the empty fixed edge set. -/
local instance regionsEdgesDecidable : ∀ j, DecidablePred (· ∈ (regions j).edges) := by
  intro j e
  cases j
  · exact isTrue trivial
  · exact isFalse (fun h => h)

/-- Each original face membership uses the complete member or the empty fixed face set. -/
local instance regionsFacesDecidable : ∀ j, DecidablePred (· ∈ (regions j).faces) := by
  intro j f
  cases j
  · exact isTrue trivial
  · exact isFalse (fun h => h)

/-- Original fixed edge membership is the specified empty authored set. -/
local instance fixedEdgesDecidable : DecidablePred (· ∈ fixedRegion.edges) := fun _ => isFalse (fun h => h)

/-- Original fixed face membership is the specified empty authored set. -/
local instance fixedFacesDecidable : DecidablePred (· ∈ fixedRegion.faces) := fun _ => isFalse (fun h => h)

/-- The original complete kernel basis has dimension one at every original vertex. -/
noncomputable def bases : FiniteFamily.Bases (k := ZMod 3) originalTower.toTower.localCoefficients.A where
  dimension _ := 1
  coordinate v := (linearCoefficient geometry reference reference comparison linear_faces v).trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 3) (ZMod 3)).symm

/-- All prime-field values are listed explicitly before independent generation. -/
def enumK : FiniteElimination.Enumeration (ZMod 3) :=
  ⟨[0,1,2],by intro a; fin_cases a <;> simp⟩

/-- Every complete original edge name is listed independently of repairs and right-hand sides. -/
def enumEdges : FiniteElimination.Enumeration (EdgeName (K := geometry)) :=
  ⟨[chosen,candidate],by
    rintro ⟨s,t,e⟩
    cases s
    cases t
    cases e <;> simp [chosen,candidate]⟩

/-- The complete authored original face is the same baa comparison. -/
def enumFaces : FiniteElimination.Enumeration geometry.TwoCell :=
  ⟨[()],by intro f; cases f; simp⟩

/-- The sole full basis component is constructed from the generated dimension one. -/
def basisIndex (v : geometry.Vertex) : Fin (bases.dimension v) := ⟨0,by change 0 < 1; decide⟩

/-- Every full original kernel basis value reads the same native translation coordinate. -/
theorem basis_value (v : geometry.Vertex) (x : originalTower.toTower.localCoefficients.A v) :
    bases.coordinate v x (basisIndex v) = coefficient geometry reference reference comparison linear_faces v x := rfl

/-- The whole original public index retains the authored b and its entire one-dimensional kernel. -/
abbrev OldPublicIndex := FiniteNative.ZIndex originalTower.toTower.localCoefficients bases
  ClosedRegion.all fixedRegion (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)

/-- The complete public b coordinate is constructed from the original candidate and full basis. -/
def publicIndex : OldPublicIndex :=
  ⟨⟨⟨candidate,trivial,not_false⟩,basisIndex ()⟩,
    ClosedRegion.candidate_not_private regions fixedRegion {candidate} false candidate rfl⟩

/-- Every original full public index is this same authored b basis component. -/
theorem publicIndex_unique (x : OldPublicIndex) : x = publicIndex := by
  rcases x with ⟨⟨⟨⟨s,t,e⟩,hu,hp⟩,j⟩,hn⟩
  cases s
  cases t
  cases e
  · exact False.elim (hn chosen_private)
  · change Fin 1 at j
    fin_cases j
    rfl

/-- The actual signed defect reads one in the full original face basis. -/
theorem actual_rhs_coordinate :
    FiniteNative.coordinate2 originalTower.toTower.localCoefficients bases ClosedRegion.all fixedRegion
      actualRHS ⟨⟨(),trivial,not_false⟩,basisIndex ()⟩ = (1 : ZMod 3) := by
  change middleCoefficient (-(originalTower.toTower.defect ())) = 1
  rw [map_neg,C18SubdivisionRegression.old_defect_coordinate,neg_neg]

/-- The actual original equation forces the full native b correction to one for every solution. -/
theorem old_solution_candidate
    (h : FiniteNative.RelativeEquation originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion actualRHS) :
    middleCoefficient (h.1.1 ⟨candidate,trivial⟩) = (1 : ZMod 3) := by
  have hv := congrArg C19SubdivisionRangeRegression.faceCoordinate h.2
  have hd := C19SubdivisionRangeRegression.relative_differential_coordinate h.1
  rw [FiniteCoefficients.differential1_eq] at hd
  rw [hd] at hv
  rw [C19SubdivisionRangeRegression.faceCoordinate_value] at hv
  change middleCoefficient (h.1.1 ⟨candidate,trivial⟩) = middleCoefficient (-(originalTower.toTower.defect ())) at hv
  rw [map_neg,C18SubdivisionRegression.old_defect_coordinate,neg_neg] at hv
  exact hv

/-- Every solution reads the same full original public b basis value. -/
theorem old_solution_public
    (h : FiniteNative.RelativeEquation originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion actualRHS) :
    (FiniteNative.edgeSplit originalTower.toTower.localCoefficients bases ClosedRegion.all fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) h.1).2 publicIndex = (1 : ZMod 3) :=
  old_solution_candidate h

/-- The independently generated original relation accepts exactly public b=1, for every full public vector. -/
theorem old_relation_iff (z : OldPublicIndex → ZMod 3) :
    z ∈ FiniteNative.generatedRelation originalTower.toTower.localCoefficients bases ClosedRegion.all fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
      C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces ↔ z publicIndex = 1 := by
  rw [FiniteNative.generated_relation_iff_relative]
  constructor
  · rintro ⟨h,hz⟩
    rw [← hz]
    exact old_solution_public h
  · intro hz
    refine ⟨oldLocalSolution 0,?_⟩
    funext j
    rw [publicIndex_unique j,old_solution_public]
    exact hz.symm

/-- Every full public basis component in the expanded actual W4 remains independently indexed. -/
abbrev NewPublicIndex := FiniteNative.ZIndex splitTower.toTower.localCoefficients
  (FiniteBases.expandedBases originalTower chosen factors bases)
  (expandedRegion geometry chosen ClosedRegion.all) (expandedRegion geometry chosen fixedRegion)
  (ClosedRegion.privateAlwaysEdges (fun j => expandedRegion geometry chosen (regions j))
    (expandedRegion geometry chosen fixedRegion) (oldEdgeSet geometry chosen {candidate}) false)

/-- The full retained b index is obtained by the actual two-sided public index comparison. -/
noncomputable def newPublicIndex : NewPublicIndex :=
  (GeneratedPublic.publicIndexEquiv originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private false).symm publicIndex

/-- The independent new generator accepts exactly the same complete public b value one. -/
theorem new_relation_iff (z : NewPublicIndex → ZMod 3) :
    z ∈ GeneratedRelations.newRelation originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := actualRHS) ↔ z newPublicIndex = 1 := by
  rw [GeneratedRelations.relation_iff]
  change GeneratedPublic.publicCoordinateEquiv originalTower chosen factors bases regions fixedRegion
    {candidate} false chosen_private false z ∈
      FiniteNative.generatedRelation originalTower.toTower.localCoefficients bases ClosedRegion.all fixedRegion
        (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
        C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces ↔ _
  rw [old_relation_iff]
  rfl

/-- The original independent relation rejects the entire zero public vector. -/
theorem old_zero_public_rejected :
    (0 : OldPublicIndex → ZMod 3) ∉
      FiniteNative.generatedRelation originalTower.toTower.localCoefficients bases ClosedRegion.all fixedRegion
        (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
        C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces := by
  rw [old_relation_iff]
  exact zero_ne_one

/-- The independent subdivided relation rejects the same entire zero public vector. -/
theorem new_zero_public_rejected :
    (0 : NewPublicIndex → ZMod 3) ∉
      GeneratedRelations.newRelation originalTower chosen factors bases regions fixedRegion {candidate}
        false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
        (value := actualRHS) := by
  rw [new_relation_iff]
  exact zero_ne_one

/-- The old generator is instantiated once from the whole actual W4 input, before any repair parameter. -/
noncomputable def oldExtraction :=
  FiniteNative.generatedRelativeEquiv originalTower.toTower.localCoefficients bases
    ClosedRegion.all fixedRegion (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
    C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces

/-- The independent new generator is instantiated once from its own actual full input. -/
noncomputable def newExtraction :=
  GeneratedRelations.newGeneratedEquiv originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
    (value := actualRHS)

/-- Compare both independently instantiated complete generators, retaining every supplemental value. -/
noncomputable def interfaceComparison :=
  GeneratedInterfaces.objectsEquiv originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
    (value := actualRHS)

/-- The fixture comparison uses the same actual local collapse and both complete generator restorations. -/
theorem interfaceComparison_value
    (y : GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := actualRHS)) :
    interfaceComparison y =
      (oldExtraction (localEquationEquiv originalTower chosen factors ClosedRegion.all fixedRegion
        (by exact not_false) actualRHS (newExtraction.symm y)).1,
        (localEquationEquiv originalTower chosen factors ClosedRegion.all fixedRegion
          (by exact not_false) actualRHS (newExtraction.symm y)).2) := rfl

/-- The old independent generator is applied to every actual original W4 repair parameter. -/
noncomputable def oldGenerated (h : ZMod 3) := oldExtraction (oldLocalSolution h)

/-- The new independent generator is applied to every full old and fresh actual W4 parameter. -/
noncomputable def newGenerated (h r : ZMod 3) := newExtraction (newLocalSolution h r)

/-- All independent old generated repair parameters retain the forced full public b value. -/
theorem old_generated_public (h : ZMod 3) : (oldGenerated h).1.1 publicIndex = 1 := by
  rw [oldGenerated,oldExtraction,FiniteNative.generatedRelativeEquiv_public]
  exact old_solution_public (oldLocalSolution h)

/-- Every full independently generated new object retains the same original public b value. -/
theorem new_generated_public
    (y : GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := actualRHS)) : y.1.1 newPublicIndex = 1 :=
  (new_relation_iff y.1.1).mp y.1.2

/-- Every new independently generated parameter restores its complete original actual local solution. -/
theorem newGenerated_restore (h r : ZMod 3) :
    newExtraction.symm (newGenerated h r) = newLocalSolution h r := by
  unfold newGenerated
  exact newExtraction.symm_apply_apply _

/-- The generated comparison recovers every independent old parameter and every entire supplement. -/
theorem generated_coordinates (h r : ZMod 3) :
    interfaceComparison (newGenerated h r) = (oldGenerated h,supplement r) := by
  rw [interfaceComparison_value,newGenerated_restore]
  have hc : localEquationEquiv originalTower chosen factors ClosedRegion.all fixedRegion
      (by exact not_false) actualRHS (newLocalSolution h r) = (oldLocalSolution h,supplement r) :=
    (localEquationEquiv originalTower chosen factors ClosedRegion.all fixedRegion
      (by exact not_false) actualRHS).apply_symm_apply _
  rw [hc]
  rfl

/-- Independently generated sections restore the actual first factor for every full parameter. -/
theorem generated_first_coordinate (h r : ZMod 3) :
    middleCoefficient (((newExtraction).symm (newGenerated h r)).1.1
        ⟨firstEdgeName geometry chosen,trivial⟩) = r := by
  rw [newGenerated_restore]
  exact newLocal_first_coordinate h r

/-- Independent new sections restore the complete second factor h+r without suppressing fresh freedom. -/
theorem generated_second_coordinate (h r : ZMod 3) :
    middleCoefficient (((newExtraction).symm (newGenerated h r)).1.1
        ⟨secondEdgeName geometry chosen,trivial⟩) = h+r := by
  rw [newGenerated_restore]
  exact newLocal_second_coordinate h r

/-- Every retained actual full kernel value survives independent generated restoration. -/
theorem generated_retained (h r : ZMod 3) (e : ClosedRegion.all.edges) (he : e.1 ≠ chosen) :
    ((newExtraction).symm (newGenerated h r)).1.1
        ⟨oldEdgeName geometry chosen e.1 he,e.2⟩ = (oldLocal h).1 e := by
  rw [newGenerated_restore]
  exact newLocal_retained h r e he

/-- The same full original relative labels are compared once by the actual local degree-zero map. -/
noncomputable def labelsComparison :=
  GeneratedInterfaces.labelsEquiv originalTower chosen factors regions fixedRegion {candidate}
    false chosen_private false

/-- Every full fresh label has actual old label zero and the whole prescribed displacement. -/
theorem generated_label_coordinates (t : ZMod 3) :
    (labelsComparison (Multiplicative.ofAdd (localFreshLabel t))).toAdd =
      (0,supplement t) := by
  rw [labelsComparison,GeneratedInterfaces.labelsEquiv_value]
  exact localFreshLabel_coordinates t

/-- The whole multiplicative label retains the same complete old label and prescribed fresh displacement. -/
theorem labelsComparison_fresh (t : ZMod 3) :
    labelsComparison (Multiplicative.ofAdd (localFreshLabel t)) =
      Multiplicative.ofAdd ((0 : RelativeCover.C0 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion),supplement t) := by
  have hb := congrArg Multiplicative.ofAdd (generated_label_coordinates t)
  rw [ofAdd_toAdd] at hb
  exact hb

/-- The concrete full new action is the independently generated native action. -/
noncomputable local instance newInterfaceAction :
    AddAction (RelativeCover.C0 splitTower.toTower.localCoefficients
      (expandedRegion geometry chosen ClosedRegion.all) (expandedRegion geometry chosen fixedRegion))
      (GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
        false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
        (value := actualRHS)) :=
  GeneratedInterfaces.newGeneratedAddAction originalTower chosen factors bases regions fixedRegion {candidate}
    false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces (value := actualRHS)

/-- The concrete old action uses the original independently generated section and original full labels. -/
noncomputable local instance oldInterfaceAction :
    AddAction (RelativeCover.C0 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion)
      (FiniteNative.GeneratedRelativeObjects originalTower.toTower.localCoefficients bases (regions false)
        fixedRegion (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
        C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces) :=
  LinearInterface.interfaceAddAction
    (FiniteNative.D originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear)
    (FiniteNative.F originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear)
    (FiniteNative.generatedSection originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces)
    (FiniteNative.generatedSection_regular originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces)
    (FiniteNative.a originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear)
    (FiniteNative.c originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear)
    (FiniteNative.D_a_add_F_c originalTower.toTower.localCoefficients bases (regions false) fixedRegion
      (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false) C19SubdivisionRangeRegression.original_linear)
    (FiniteNative.coordinate2 originalTower.toTower.localCoefficients bases (regions false) fixedRegion actualRHS)

/-- The concrete paired action is the full native old action and full supplemental translation. -/
noncomputable local instance productInterfaceAction :
    AddAction
      (RelativeCover.C0 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion ×
        localSupplement originalTower chosen factors ClosedRegion.all)
      (FiniteNative.GeneratedRelativeObjects originalTower.toTower.localCoefficients bases (regions false)
        fixedRegion (ClosedRegion.privateAlwaysEdges regions fixedRegion {candidate} false)
        C19SubdivisionRangeRegression.original_linear actualRHS enumK enumEdges enumFaces ×
        localSupplement originalTower chosen factors (regions false)) := SupplementalAction.productAddAction

set_option maxRecDepth 32768 in
/-- The native action on independently generated objects retains every fresh original label. -/
theorem generated_label_action (t : ZMod 3)
    (y : GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces (value := actualRHS)) :
    interfaceComparison (Multiplicative.ofAdd (localFreshLabel t) • y) =
    Multiplicative.ofAdd ((0 : RelativeCover.C0 originalTower.toTower.localCoefficients ClosedRegion.all fixedRegion),supplement t) •
      interfaceComparison y := by
  have h := GeneratedInterfaces.objects_equivariant originalTower chosen factors bases regions fixedRegion
    {candidate} false chosen_private false C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
    (value := actualRHS) (Multiplicative.ofAdd (localFreshLabel t)) y
  change interfaceComparison (Multiplicative.ofAdd (localFreshLabel t) • y) =
    labelsComparison (Multiplicative.ofAdd (localFreshLabel t)) • interfaceComparison y at h
  exact h.trans (congrArg (fun b => b • interfaceComparison y) (labelsComparison_fresh t))

/-- The independently generated excluded member retains only the zero supplement. -/
theorem excluded_generated_supplement
    (y : GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private true C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := (0 : RelativeCover.C2 originalTower.toTower.localCoefficients fixedRegion fixedRegion))) :
    (GeneratedInterfaces.objectsEquiv originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private true C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := (0 : RelativeCover.C2 originalTower.toTower.localCoefficients fixedRegion fixedRegion)) y).2.1 = 0 :=
  localSupplement_zero originalTower chosen factors fixedRegion (by exact not_false) _

/-- The same actual nonzero fresh kernel value cannot occur in any excluded generated object. -/
theorem excluded_generated_nonzero_rejected :
    ¬ ∃ y : GeneratedRelations.newGeneratedObjects originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private true C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := (0 : RelativeCover.C2 originalTower.toTower.localCoefficients fixedRegion fixedRegion)),
    (GeneratedInterfaces.objectsEquiv originalTower chosen factors bases regions fixedRegion {candidate}
      false chosen_private true C19SubdivisionRangeRegression.original_linear enumK enumEdges enumFaces
      (value := (0 : RelativeCover.C2 originalTower.toTower.localCoefficients fixedRegion fixedRegion)) y).2.1 =
      C18SubdivisionRegression.freshOne := by
  rintro ⟨y,hy⟩
  rw [excluded_generated_supplement] at hy
  exact C18SubdivisionRegression.freshOne_ne_zero hy.symm

end AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.C22GeneratedSubdivisionRegression
