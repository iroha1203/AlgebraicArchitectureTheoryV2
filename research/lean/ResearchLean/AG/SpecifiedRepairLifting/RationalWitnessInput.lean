import ResearchLean.AG.SpecifiedRepairLifting.RationalWitnessContext

/-! # W1の一生成元・一Lawと実Čech入力

Implementation notes: 原始関係は空であり、sourceとLawの発生は各一個。
実context上の局所定数係数層から元のČech複体を生成する。
反映・共通label・支持はこの有限表から証明し、障害消滅をfieldへ入れない。
-/
noncomputable section
open CategoryTheory Set TopologicalSpace
namespace AAT.AG.SpecifiedRepairLifting.RationalWitnessInput
open RationalWitnessGeometry RationalWitnessContext
open ObstructionDiagnosticBridge CanonicalResolution ResolutionInvariance Cohomology TwoPhase
/-- 固定された一sourceの恒等reading。 -/
abbrev reading : Reading Unit where
  Target := Unit
  read := id
  surjective := Function.surjective_id
/-- 固定された一Lawの一つの発生値。 -/
def laws : FiniteLawFamily Unit where
  Law := Unit
  lawFintype := inferInstance
  Value := fun _ => Unit
  valueDecidableEq := fun _ => inferInstance
  eval := fun _ _ => ()
/-- 一つのLawは実readingに沿って降下する。 -/
theorem adequate : laws.Adequate reading := by
  intro law
  exact ⟨fun _ => (),fun _ => rfl⟩
/-- 二つの実chartと一つの重なりからなる固定nerve。 -/
abbrev nerve : CoverNerve where
  Chart := Bool
  EdgeComponent := Unit
  FaceComponent := Empty
  edgeLeft := fun _ => false
  edgeRight := fun _ => true
  faceEdge0 := fun f => nomatch f
  faceEdge1 := fun f => nomatch f
  faceEdge2 := fun f => nomatch f
  edgeOverlapComponent _ := Nonempty ↥(patch false ⊓ patch true)
  faceTripleOverlapComponent := fun f => nomatch f
  edgeOverlapComponent_holds _ := by
    rw [patch_intersection]
    exact neighborhoodNonempty .edge
  faceTripleOverlapComponent_holds := fun f => nomatch f
/-- 全chartが同じ唯一targetを実際に支持する。 -/
def supportedNerve : TargetSupportedNerve reading where
  nerve := nerve
  chartFintype := inferInstance
  edgeFintype := inferInstance
  faceFintype := inferInstance
  chartSupport _ := univ
  chartSupport_nonempty _ := ⟨(),mem_univ _⟩
  faceEdge0_left := fun f => nomatch f
  faceEdge0_right := fun f => nomatch f
  faceEdge1_right := fun f => nomatch f
/-- 原始生成元は一つで、関係は空。 -/
def presentation : GeneratorPresentation laws where
  relation := fun _ _ => False
  relation_preserves_label := by intros; contradiction
instance primitiveSubsingleton : Subsingleton (PrimitiveGenerator laws) := by
  change Subsingleton (Unit × Unit)
  infer_instance
instance blockSubsingleton : Subsingleton presentation.Block := by
  infer_instance
/-- 一つの原始生成元からできる同じblock。 -/
def block : presentation.Block := presentation.blockOf ((),())
instance blockUnique : Unique presentation.Block where
  default := block
  uniq _ := Subsingleton.elim _ _
/-- 生成labelは一つだけ。 -/
instance labelSubsingleton : Subsingleton (LawValueLabel laws) where
  allEq a b := by
    obtain ⟨x,rfl⟩ := presentation.blockLabel_surjective a
    obtain ⟨y,rfl⟩ := presentation.blockLabel_surjective b
    rw [Subsingleton.elim x y]
/-- 原始Law発生から生成するlabel。 -/
def label : LawValueLabel laws := LawValueLabel.ofSource laws () ()
instance labelUnique : Unique (LawValueLabel laws) where
  default := label
  uniq _ := Subsingleton.elim _ _
/-- 原始生成元の一元性から反映条件を放電する。 -/
theorem reflection : presentation.ReflectionCondition := by
  intro left right _
  have h : left = right := Subsingleton.elim _ _
  subst right
  exact Relation.EqvGen.refl _
/-- 共通label条件は同じ唯一targetから生成する。 -/
theorem common_support : GeneratorPresentation.CommonLabelChartSupport supportedNerve laws adequate := by
  intro l
  refine ⟨(),fun _ => (show () ∈ (univ : Set Unit) from mem_univ _),?_⟩
  exact @Subsingleton.elim Unit inferInstance _ _
instance supportedFaceEmpty : IsEmpty supportedNerve.nerve.FaceComponent := by
  change IsEmpty Empty
  infer_instance
/-- 実二chartと実交差contextによる元G-125 cover。 -/
def cechCover : GeneratorPresentation.FaceEmptyAATCechCover supportedNerve contextOpenSupport where
  base := Site.ContextCategoryObject.of contextPreorder baseContext
  chartContext i := Site.ContextCategoryObject.of contextPreorder (openContext (patch i))
  edgeContext _ := Site.ContextCategoryObject.of contextPreorder (openContext (patch false ⊓ patch true))
  inclusion _ := homOfLE (openContext_le le_top)
  edgeLeftRestriction _ := homOfLE (openContext_le inf_le_left)
  edgeRightRestriction _ := homOfLE (openContext_le inf_le_right)
  chartSupportNonempty i := by
    change Nonempty (contextSupport (openContext (patch i)))
    rw [contextSupport_openContext]
    exact patchNonempty i
  chartSupportPreconnected i := by
    change PreconnectedSpace (contextSupport (openContext (patch i)))
    rw [contextSupport_openContext]
    exact patchPreconnected i
  edgeSupportNonempty _ := by
    change Nonempty (contextSupport (openContext (patch false ⊓ patch true)))
    rw [contextSupport_openContext,patch_intersection]
    exact neighborhoodNonempty .edge
  edgeSupportPreconnected _ := by
    change PreconnectedSpace (contextSupport (openContext (patch false ⊓ patch true)))
    rw [contextSupport_openContext,patch_intersection]
    exact neighborhoodPreconnected .edge
end AAT.AG.SpecifiedRepairLifting.RationalWitnessInput

#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.reading
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.laws
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.adequate
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.nerve
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.supportedNerve
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.presentation
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.primitiveSubsingleton
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.blockSubsingleton
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.block
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.blockUnique
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.labelSubsingleton
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.label
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.labelUnique
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.reflection
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.common_support
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.supportedFaceEmpty
#print axioms AAT.AG.SpecifiedRepairLifting.RationalWitnessInput.cechCover
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.RationalWitnessInput
