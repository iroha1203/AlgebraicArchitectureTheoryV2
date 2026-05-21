import Formal.Arch.Evolution.SFTFieldCover

/-!
Binary SFT descent over exact clocked cones.

This module contains the first substantive descent surface: global clocked cone
points project to compatible local cone families, and selected gluing
assumptions build a global cone point back from a compatible local family.  The
inverse laws are stated as selected equivalence relations instead of definitional
equality, avoiding overclaiming dependent path equality.
-/

namespace Formal.Arch

universe u v w x y z a b

/--
A selected equivalence witness with explicit relatedness relations.

The inverse laws are stated up to the selected relations, and those relations
must themselves be equivalence relations.  This keeps the API from accepting an
arbitrary preorder or unconstrained predicate as an "equivalence" surface.
-/
structure ConeEquivalence (A : Type u) (B : Type v) where
  toFun : A -> B
  invFun : B -> A
  leftRelated : A -> A -> Prop
  rightRelated : B -> B -> Prop
  left_refl : ∀ a, leftRelated a a
  left_symm : ∀ {a b}, leftRelated a b -> leftRelated b a
  left_trans : ∀ {a b c}, leftRelated a b -> leftRelated b c ->
    leftRelated a c
  right_refl : ∀ b, rightRelated b b
  right_symm : ∀ {a b}, rightRelated a b -> rightRelated b a
  right_trans : ∀ {a b c}, rightRelated a b -> rightRelated b c ->
    rightRelated a c
  left_related : ∀ a, leftRelated (invFun (toFun a)) a
  right_related : ∀ b, rightRelated (toFun (invFun b)) b
  equivalenceBoundary : Prop
  nonConclusions : Prop

namespace ConeEquivalence

/-- The selected equivalence exposes its left inverse law up to relatedness. -/
theorem left_inverse_related
    {A : Type u} {B : Type v}
    (equiv : ConeEquivalence A B) (a : A) :
    equiv.leftRelated (equiv.invFun (equiv.toFun a)) a :=
  equiv.left_related a

/-- The selected equivalence exposes its right inverse law up to relatedness. -/
theorem right_inverse_related
    {A : Type u} {B : Type v}
    (equiv : ConeEquivalence A B) (b : B) :
    equiv.rightRelated (equiv.toFun (equiv.invFun b)) b :=
  equiv.right_related b

theorem left_related_refl
    {A : Type u} {B : Type v}
    (equiv : ConeEquivalence A B) (a : A) :
    equiv.leftRelated a a :=
  equiv.left_refl a

theorem right_related_refl
    {A : Type u} {B : Type v}
    (equiv : ConeEquivalence A B) (b : B) :
    equiv.rightRelated b b :=
  equiv.right_refl b

end ConeEquivalence

/--
Binary SFT model over a binary field cover.

The theorem-bearing fields are the support and step projection predicates from
global to local regions.  Local-to-global path gluing is intentionally supplied
later by `BinaryDescentAssumptions`.
-/
structure BinarySFTModel
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    (cover : BinaryFieldCover Global Left Right Interface)
    (OperationG : Type y) (OperationL : Type z)
    (OperationR : Type a) (OperationI : Type b) where
  globalSupport : OperationSupport Global OperationG
  globalRelation : StepRelation Global OperationG
  leftSupport : OperationSupport Left OperationL
  leftRelation : StepRelation Left OperationL
  rightSupport : OperationSupport Right OperationR
  rightRelation : StepRelation Right OperationR
  interfaceSupport : OperationSupport Interface OperationI
  interfaceRelation : StepRelation Interface OperationI
  projectLeftOp : OperationG -> OperationL
  projectRightOp : OperationG -> OperationR
  projectInterfaceLeftOp : OperationL -> OperationI
  projectInterfaceRightOp : OperationR -> OperationI
  projected_ops_compatible : Prop
  global_support_projects_left :
    ∀ g op,
      globalSupport.Supports g op ->
        leftSupport.Supports (cover.restrictLeft g) (projectLeftOp op)
  global_support_projects_right :
    ∀ g op,
      globalSupport.Supports g op ->
        rightSupport.Supports (cover.restrictRight g) (projectRightOp op)
  global_step_projects_left :
    ∀ {g₀ g₁ : Global} {op : OperationG},
      globalSupport.Supports g₀ op ->
        globalRelation.Realizes g₀ op g₁ ->
          leftRelation.Realizes
            (cover.restrictLeft g₀)
            (projectLeftOp op)
            (cover.restrictLeft g₁)
  global_step_projects_right :
    ∀ {g₀ g₁ : Global} {op : OperationG},
      globalSupport.Supports g₀ op ->
        globalRelation.Realizes g₀ op g₁ ->
          rightRelation.Realizes
            (cover.restrictRight g₀)
            (projectRightOp op)
            (cover.restrictRight g₁)
  compatible_local_steps_glue : Prop
  idle_projects : Prop
  idle_glues : Prop
  supportBoundary : Prop
  stepBoundary : Prop
  policyBoundary : Prop
  observationBoundary : Prop
  nonConclusions : Prop

namespace BinarySFTModel

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable (model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI)

/-- Support projection from global support to left local support. -/
def GlobalSupportProjectsLeft : Prop :=
  ∀ g op,
    model.globalSupport.Supports g op ->
      model.leftSupport.Supports
        (cover.restrictLeft g) (model.projectLeftOp op)

/-- Support projection from global support to right local support. -/
def GlobalSupportProjectsRight : Prop :=
  ∀ g op,
    model.globalSupport.Supports g op ->
      model.rightSupport.Supports
        (cover.restrictRight g) (model.projectRightOp op)

/-- Step projection from global step relation to left local step relation. -/
def GlobalStepProjectsLeft : Prop :=
  ∀ {g₀ g₁ : Global} {op : OperationG},
    model.globalSupport.Supports g₀ op ->
      model.globalRelation.Realizes g₀ op g₁ ->
        model.leftRelation.Realizes
          (cover.restrictLeft g₀)
          (model.projectLeftOp op)
          (cover.restrictLeft g₁)

/-- Step projection from global step relation to right local step relation. -/
def GlobalStepProjectsRight : Prop :=
  ∀ {g₀ g₁ : Global} {op : OperationG},
    model.globalSupport.Supports g₀ op ->
      model.globalRelation.Realizes g₀ op g₁ ->
        model.rightRelation.Realizes
          (cover.restrictRight g₀)
          (model.projectRightOp op)
          (cover.restrictRight g₁)

/-- Local-step gluing remains an explicit selected predicate. -/
def CompatibleLocalStepsGlue : Prop :=
  model.compatible_local_steps_glue

/-- Idle-step projection remains an explicit selected predicate. -/
def IdleStepProjects : Prop :=
  model.idle_projects

/-- Idle-step gluing remains an explicit selected predicate. -/
def IdleStepGlues : Prop :=
  model.idle_glues

/-- Project one global clocked step to the left region. -/
def projectClockedStepLeft
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      ClockedFieldStep model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldStep model.leftSupport model.leftRelation
          (cover.restrictLeft g₀) (cover.restrictLeft g₁)
  | _, _, ClockedFieldStep.active step =>
      ClockedFieldStep.active
        { operation := model.projectLeftOp step.operation
          supported :=
            model.global_support_projects_left
              _ step.operation step.supported
          realizes :=
            model.global_step_projects_left
              step.supported step.realizes }
  | g, _, ClockedFieldStep.idle _ =>
      ClockedFieldStep.idle (cover.restrictLeft g)

/-- Project one global clocked step to the right region. -/
def projectClockedStepRight
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      ClockedFieldStep model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldStep model.rightSupport model.rightRelation
          (cover.restrictRight g₀) (cover.restrictRight g₁)
  | _, _, ClockedFieldStep.active step =>
      ClockedFieldStep.active
        { operation := model.projectRightOp step.operation
          supported :=
            model.global_support_projects_right
              _ step.operation step.supported
          realizes :=
            model.global_step_projects_right
              step.supported step.realizes }
  | g, _, ClockedFieldStep.idle _ =>
      ClockedFieldStep.idle (cover.restrictRight g)

/-- Project a global clocked path to the left local region. -/
def projectClockedPathLeft
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldPath model.leftSupport model.leftRelation
          (cover.restrictLeft g₀) (cover.restrictLeft g₁)
  | _, _, ArchitecturePath.nil g => ArchitecturePath.nil (cover.restrictLeft g)
  | _, _, ArchitecturePath.cons step rest =>
      ArchitecturePath.cons
        (projectClockedStepLeft model step)
        (projectClockedPathLeft (model := model) rest)

/-- Project a global clocked path to the right local region. -/
def projectClockedPathRight
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁ ->
        ClockedFieldPath model.rightSupport model.rightRelation
          (cover.restrictRight g₀) (cover.restrictRight g₁)
  | _, _, ArchitecturePath.nil g => ArchitecturePath.nil (cover.restrictRight g)
  | _, _, ArchitecturePath.cons step rest =>
      ArchitecturePath.cons
        (projectClockedStepRight model step)
        (projectClockedPathRight (model := model) rest)

/-- Left projection preserves the exact number of clock ticks. -/
@[simp] theorem projectClockedPathLeft_length
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      (path :
        ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁) ->
        ArchitecturePath.length (projectClockedPathLeft (model := model) path) =
          ArchitecturePath.length path
  | _, _, ArchitecturePath.nil _ => rfl
  | _, _, ArchitecturePath.cons _ rest => by
      simp [projectClockedPathLeft, ArchitecturePath.length,
        projectClockedPathLeft_length (model := model) rest]

/-- Right projection preserves the exact number of clock ticks. -/
@[simp] theorem projectClockedPathRight_length
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {g₀ g₁ : Global} ->
      (path :
        ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁) ->
        ArchitecturePath.length (projectClockedPathRight (model := model) path) =
          ArchitecturePath.length path
  | _, _, ArchitecturePath.nil _ => rfl
  | _, _, ArchitecturePath.cons _ rest => by
      simp [projectClockedPathRight, ArchitecturePath.length,
        projectClockedPathRight_length (model := model) rest]

/-- Exact global clocked cone membership projects to exact left local membership. -/
theorem projectClockedForecastCone_left
    {source target : Global} {horizon : Nat}
    {path :
      ClockedFieldPath model.globalSupport model.globalRelation source target}
    (hCone :
      ClockedForecastCone model.globalSupport model.globalRelation
        source horizon target path) :
    ClockedForecastCone model.leftSupport model.leftRelation
      (cover.restrictLeft source) horizon (cover.restrictLeft target)
      (projectClockedPathLeft (model := model) path) := by
  simpa [ClockedForecastCone, ExactClockedFieldPath] using hCone

/-- Exact global clocked cone membership projects to exact right local membership. -/
theorem projectClockedForecastCone_right
    {source target : Global} {horizon : Nat}
    {path :
      ClockedFieldPath model.globalSupport model.globalRelation source target}
    (hCone :
      ClockedForecastCone model.globalSupport model.globalRelation
        source horizon target path) :
    ClockedForecastCone model.rightSupport model.rightRelation
      (cover.restrictRight source) horizon (cover.restrictRight target)
      (projectClockedPathRight (model := model) path) := by
  simpa [ClockedForecastCone, ExactClockedFieldPath] using hCone

end BinarySFTModel

/--
A compatible pair of local clock ticks.

The step-level interface agreement is intentionally still a boundary predicate:
it records that the left and right ticks are being read as projections of the
same global tick without forcing a particular interface-step representation yet.
-/
structure CompatibleLocalClockedStep
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    {left₀ left₁ : Left}
    {right₀ right₁ : Right} where
  leftStep :
    ClockedFieldStep model.leftSupport model.leftRelation left₀ left₁
  rightStep :
    ClockedFieldStep model.rightSupport model.rightRelation right₀ right₁
  sourceCompatible :
    cover.compatible left₀ right₀
  targetCompatible :
    cover.compatible left₁ right₁
  interfaceStepAgreement : Prop
  nonConclusions : Prop

/--
Tickwise compatibility between two local clocked paths.

The inductive shape aligns left and right ticks one-for-one, which is the data
needed to glue an exact shared-clock local cone family back to a global path.
-/
inductive CompatibleLocalClockedPath
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    {left₀ left₁ : Left} ->
    {right₀ right₁ : Right} ->
    ClockedFieldPath model.leftSupport model.leftRelation left₀ left₁ ->
    ClockedFieldPath model.rightSupport model.rightRelation right₀ right₁ ->
      Type (max u v w x y z a b) where
  | nil {left₀ : Left} {right₀ : Right}
      (hCompatible : cover.compatible left₀ right₀) :
      CompatibleLocalClockedPath model
        (ArchitecturePath.nil left₀)
        (ArchitecturePath.nil right₀)
  | cons
      {left₀ left₁ left₂ : Left}
      {right₀ right₁ right₂ : Right}
      {leftRest :
        ClockedFieldPath model.leftSupport model.leftRelation left₁ left₂}
      {rightRest :
        ClockedFieldPath model.rightSupport model.rightRelation right₁ right₂}
      (stepPair :
        CompatibleLocalClockedStep model
          (left₀ := left₀) (left₁ := left₁)
          (right₀ := right₀) (right₁ := right₁))
      (rest :
        CompatibleLocalClockedPath model leftRest rightRest) :
      CompatibleLocalClockedPath model
        (ArchitecturePath.cons stepPair.leftStep leftRest)
        (ArchitecturePath.cons stepPair.rightStep rightRest)

namespace CompatibleLocalClockedPath

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}

/-- Tickwise-compatible local paths have the same clock length. -/
theorem left_length_eq_right_length :
    {left₀ left₁ : Left} ->
    {right₀ right₁ : Right} ->
    {leftPath :
      ClockedFieldPath model.leftSupport model.leftRelation left₀ left₁} ->
    {rightPath :
      ClockedFieldPath model.rightSupport model.rightRelation right₀ right₁} ->
    CompatibleLocalClockedPath model leftPath rightPath ->
      ArchitecturePath.length leftPath =
        ArchitecturePath.length rightPath
  | _, _, _, _, _, _, CompatibleLocalClockedPath.nil _ => rfl
  | _, _, _, _, _, _, CompatibleLocalClockedPath.cons _ rest => by
      simpa [ArchitecturePath.length]
        using congrArg Nat.succ (left_length_eq_right_length rest)

end CompatibleLocalClockedPath

namespace BinarySFTModel

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable (model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI)

/-- Projecting a global clock tick yields a compatible local tick pair. -/
def projectClockedStepPairCompatible
    {g₀ g₁ : Global}
    (step :
      ClockedFieldStep model.globalSupport model.globalRelation g₀ g₁) :
    CompatibleLocalClockedStep model
      (left₀ := cover.restrictLeft g₀)
      (left₁ := cover.restrictLeft g₁)
      (right₀ := cover.restrictRight g₀)
      (right₁ := cover.restrictRight g₁) where
  leftStep := projectClockedStepLeft (model := model) step
  rightStep := projectClockedStepRight (model := model) step
  sourceCompatible := cover.global_compatible g₀
  targetCompatible := cover.global_compatible g₁
  interfaceStepAgreement := True
  nonConclusions := True

/--
Projected left and right paths from a global clocked path are tickwise
compatible.
-/
def projectedClockedPaths_tickwiseCompatible :
    {g₀ g₁ : Global} ->
    (path :
      ClockedFieldPath model.globalSupport model.globalRelation g₀ g₁) ->
      CompatibleLocalClockedPath model
        (projectClockedPathLeft (model := model) path)
        (projectClockedPathRight (model := model) path)
  | _, _, ArchitecturePath.nil g =>
      CompatibleLocalClockedPath.nil (cover.global_compatible g)
  | _, _, ArchitecturePath.cons step rest =>
      CompatibleLocalClockedPath.cons
        (projectClockedStepPairCompatible (model := model) step)
        (projectedClockedPaths_tickwiseCompatible rest)

end BinarySFTModel

/--
Step-level local-to-global gluing data for compatible local clock ticks.

The projection laws and active/idle case boundaries remain explicit `Prop`
fields at this stage; the concrete progress is that a global clock tick is
constructed from each compatible local tick pair.
-/
structure BinaryClockedStepGluingData
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) where
  glueStep :
    ∀ {left₀ left₁ : Left} {right₀ right₁ : Right}
      (hSource : cover.compatible left₀ right₀)
      (hTarget : cover.compatible left₁ right₁),
      CompatibleLocalClockedStep model
        (left₀ := left₀) (left₁ := left₁)
        (right₀ := right₀) (right₁ := right₁) ->
        ClockedFieldStep model.globalSupport model.globalRelation
          (cover.glue left₀ right₀ hSource)
          (cover.glue left₁ right₁ hTarget)
  left_projection_law : Prop
  right_projection_law : Prop
  idle_left_law : Prop
  idle_right_law : Prop
  active_active_boundary : Prop
  active_idle_boundary : Prop
  idle_active_boundary : Prop
  idle_idle_boundary : Prop
  nonConclusions : Prop

namespace BinaryClockedStepGluingData

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}

/-- The zero-length global path between the same glued local pair. -/
def gluedNilPath
    (_glueData : BinaryClockedStepGluingData model)
    {left₀ : Left} {right₀ : Right}
    (hSource hTarget : cover.compatible left₀ right₀) :
    ClockedFieldPath model.globalSupport model.globalRelation
      (cover.glue left₀ right₀ hSource)
      (cover.glue left₀ right₀ hTarget) := by
  have hEq :
      cover.glue left₀ right₀ hSource =
        cover.glue left₀ right₀ hTarget :=
    cover.glue_compatible_proof_irrel left₀ right₀ hSource hTarget
  cases hEq
  exact ArchitecturePath.nil (cover.glue left₀ right₀ hSource)

/-- Glue tickwise-compatible local clocked paths into one global clocked path. -/
def glueCompatibleLocalClockedPath
    (glueData : BinaryClockedStepGluingData model) :
    {left₀ left₁ : Left} ->
    {right₀ right₁ : Right} ->
    {leftPath :
      ClockedFieldPath model.leftSupport model.leftRelation left₀ left₁} ->
    {rightPath :
      ClockedFieldPath model.rightSupport model.rightRelation right₀ right₁} ->
    CompatibleLocalClockedPath model leftPath rightPath ->
    (hSource : cover.compatible left₀ right₀) ->
    (hTarget : cover.compatible left₁ right₁) ->
      ClockedFieldPath model.globalSupport model.globalRelation
        (cover.glue left₀ right₀ hSource)
        (cover.glue left₁ right₁ hTarget)
  | _, _, _, _, _, _, CompatibleLocalClockedPath.nil _hCompatible,
      hSource, hTarget =>
      gluedNilPath glueData hSource hTarget
  | _, _, _, _, _, _,
      CompatibleLocalClockedPath.cons stepPair rest, hSource, hTarget =>
      ArchitecturePath.cons
        (glueData.glueStep hSource stepPair.targetCompatible stepPair)
        (glueCompatibleLocalClockedPath glueData rest
          stepPair.targetCompatible hTarget)

/-- Gluing local paths preserves the left path's clock length. -/
@[simp] theorem glueCompatibleLocalClockedPath_length
    (glueData : BinaryClockedStepGluingData model) :
    {left₀ left₁ : Left} ->
    {right₀ right₁ : Right} ->
    {leftPath :
      ClockedFieldPath model.leftSupport model.leftRelation left₀ left₁} ->
    {rightPath :
      ClockedFieldPath model.rightSupport model.rightRelation right₀ right₁} ->
    (hPath : CompatibleLocalClockedPath model leftPath rightPath) ->
    (hSource : cover.compatible left₀ right₀) ->
    (hTarget : cover.compatible left₁ right₁) ->
      ArchitecturePath.length
          (glueCompatibleLocalClockedPath glueData hPath hSource hTarget) =
        ArchitecturePath.length leftPath
  | _, _, _, _, _, _, CompatibleLocalClockedPath.nil _, _, _ => by
      simp [glueCompatibleLocalClockedPath, gluedNilPath,
        ArchitecturePath.length]
  | _, _, _, _, _, _,
      CompatibleLocalClockedPath.cons stepPair rest, hSource, hTarget => by
      simp [glueCompatibleLocalClockedPath, ArchitecturePath.length,
        glueCompatibleLocalClockedPath_length glueData rest
          stepPair.targetCompatible hTarget]

end BinaryClockedStepGluingData

/-- Concrete compatible binary local cone family at one source and horizon. -/
structure CompatibleBinaryClockedConeFamily
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  leftTarget : Left
  rightTarget : Right
  compatibleTarget : cover.compatible leftTarget rightTarget
  leftPath :
    ClockedFieldPath model.leftSupport model.leftRelation
      (cover.restrictLeft source) leftTarget
  rightPath :
    ClockedFieldPath model.rightSupport model.rightRelation
      (cover.restrictRight source) rightTarget
  leftCone :
    ClockedForecastCone model.leftSupport model.leftRelation
      (cover.restrictLeft source) horizon leftTarget leftPath
  rightCone :
    ClockedForecastCone model.rightSupport model.rightRelation
      (cover.restrictRight source) horizon rightTarget rightPath
  interfaceEndpointAgreement :
    cover.leftInterface leftTarget = cover.rightInterface rightTarget
  tickwisePath :
    CompatibleLocalClockedPath model leftPath rightPath
  nonConclusions : Prop

namespace CompatibleBinaryClockedConeFamily

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}
variable {source : Global} {horizon : Nat}

/-- A compatible family exposes left exact clock membership. -/
theorem left_length_eq_horizon
    (family :
      CompatibleBinaryClockedConeFamily model source horizon) :
    ArchitecturePath.length family.leftPath = horizon :=
  ClockedForecastCone.length_eq_horizon family.leftCone

/-- A compatible family exposes right exact clock membership. -/
theorem right_length_eq_horizon
    (family :
      CompatibleBinaryClockedConeFamily model source horizon) :
    ArchitecturePath.length family.rightPath = horizon :=
  ClockedForecastCone.length_eq_horizon family.rightCone

end CompatibleBinaryClockedConeFamily

/-- Cast the source endpoint of a clocked path along a selected equality. -/
def castClockedFieldPathSource
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source₀ source₁ target : Field}
    (hSource : source₀ = source₁)
    (path : ClockedFieldPath support relation source₀ target) :
    ClockedFieldPath support relation source₁ target := by
  cases hSource
  exact path

/-- Casting the source endpoint of a clocked path preserves its clock length. -/
@[simp] theorem castClockedFieldPathSource_length
    {Field : Type u} {Operation : Type v}
    {support : OperationSupport Field Operation}
    {relation : StepRelation Field Operation}
    {source₀ source₁ target : Field}
    (hSource : source₀ = source₁)
    (path : ClockedFieldPath support relation source₀ target) :
    ArchitecturePath.length
        (castClockedFieldPathSource hSource path) =
      ArchitecturePath.length path := by
  cases hSource
  rfl

/-- Project a global cone point to a concrete compatible binary local family. -/
def projectGlobalConePointToBinaryFamily
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    {source : Global} {horizon : Nat}
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    CompatibleBinaryClockedConeFamily model source horizon where
  leftTarget := cover.restrictLeft point.target
  rightTarget := cover.restrictRight point.target
  compatibleTarget := cover.global_compatible point.target
  leftPath := model.projectClockedPathLeft point.path
  rightPath := model.projectClockedPathRight point.path
  leftCone := model.projectClockedForecastCone_left point.coneMember
  rightCone := model.projectClockedForecastCone_right point.coneMember
  interfaceEndpointAgreement :=
    (cover.compatible_iff_interface
      (cover.restrictLeft point.target)
      (cover.restrictRight point.target)).mp
        (cover.global_compatible point.target)
  tickwisePath :=
    model.projectedClockedPaths_tickwiseCompatible point.path
  nonConclusions := True

/--
Glue a compatible binary local cone family into a global clocked cone point
using concrete step-level gluing data.

The path itself is constructed by induction over the tickwise local path
compatibility witness.  Inverse laws for descent remain supplied separately by
`BinaryProjectionGluingEquivalenceLaws`.
-/
def glueCompatibleBinaryClockedConeFamily
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (glueData : BinaryClockedStepGluingData model)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    ClockedConePoint model.globalSupport model.globalRelation source horizon := by
  let hSource : cover.compatible
      (cover.restrictLeft source) (cover.restrictRight source) :=
    cover.global_compatible source
  let gluedTarget : Global :=
    cover.glue family.leftTarget family.rightTarget
      family.compatibleTarget
  let gluedPath :
      ClockedFieldPath model.globalSupport model.globalRelation
        (cover.glue (cover.restrictLeft source)
          (cover.restrictRight source) hSource)
        gluedTarget :=
    glueData.glueCompatibleLocalClockedPath
      family.tickwisePath hSource family.compatibleTarget
  have hSourceEq :
      cover.glue (cover.restrictLeft source)
        (cover.restrictRight source) hSource = source :=
    cover.glue_restricts_eq source
  let castedPath :
      ClockedFieldPath model.globalSupport model.globalRelation
        source gluedTarget :=
    castClockedFieldPathSource hSourceEq gluedPath
  refine
    { target := gluedTarget
      path := castedPath
      coneMember := ?_ }
  have hLength :
      ArchitecturePath.length gluedPath = horizon := by
    calc
      ArchitecturePath.length gluedPath =
          ArchitecturePath.length family.leftPath := by
        exact
          BinaryClockedStepGluingData.glueCompatibleLocalClockedPath_length
            glueData family.tickwisePath hSource family.compatibleTarget
      _ = horizon :=
        CompatibleBinaryClockedConeFamily.left_length_eq_horizon family
  simpa [ClockedForecastCone, ExactClockedFieldPath, castedPath] using hLength

/--
Selected binary descent assumptions.

Projection from global to local is constructed by `BinarySFTModel`.  The hard
local-to-global direction is supplied here as an explicit gluing function with
inverse laws up to selected equivalence relations.
-/
structure BinaryDescentAssumptions
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  glueLocalFamily :
    CompatibleBinaryClockedConeFamily model source horizon ->
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon
  globalConePointEquivalent :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      ClockedConePoint model.globalSupport model.globalRelation source horizon ->
        Prop
  localFamilyEquivalent :
    CompatibleBinaryClockedConeFamily model source horizon ->
      CompatibleBinaryClockedConeFamily model source horizon ->
        Prop
  globalConePointEquivalent_refl :
    ∀ point, globalConePointEquivalent point point
  globalConePointEquivalent_symm :
    ∀ {left right}, globalConePointEquivalent left right ->
      globalConePointEquivalent right left
  globalConePointEquivalent_trans :
    ∀ {left middle right},
      globalConePointEquivalent left middle ->
      globalConePointEquivalent middle right ->
        globalConePointEquivalent left right
  localFamilyEquivalent_refl :
    ∀ family, localFamilyEquivalent family family
  localFamilyEquivalent_symm :
    ∀ {left right}, localFamilyEquivalent left right ->
      localFamilyEquivalent right left
  localFamilyEquivalent_trans :
    ∀ {left middle right},
      localFamilyEquivalent left middle ->
      localFamilyEquivalent middle right ->
        localFamilyEquivalent left right
  projected_glued_related :
    ∀ point,
      globalConePointEquivalent
        (glueLocalFamily
          (projectGlobalConePointToBinaryFamily model point))
        point
  glued_projected_related :
    ∀ family,
      localFamilyEquivalent
        (projectGlobalConePointToBinaryFamily model
          (glueLocalFamily family))
        family
  interfaceGlueBoundary : Prop
  inverseLawBoundary : Prop
  nonConclusions : Prop

/--
Selected equivalence laws for the concrete step-glued local-to-global map.

This keeps the inverse laws as explicit assumptions while no longer assuming
the entire `glueLocalFamily` function.
-/
structure BinaryProjectionGluingEquivalenceLaws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (source : Global) (horizon : Nat) where
  globalConePointEquivalent :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      ClockedConePoint model.globalSupport model.globalRelation source horizon ->
        Prop
  localFamilyEquivalent :
    CompatibleBinaryClockedConeFamily model source horizon ->
      CompatibleBinaryClockedConeFamily model source horizon ->
        Prop
  globalConePointEquivalent_refl :
    ∀ point, globalConePointEquivalent point point
  globalConePointEquivalent_symm :
    ∀ {left right}, globalConePointEquivalent left right ->
      globalConePointEquivalent right left
  globalConePointEquivalent_trans :
    ∀ {left middle right},
      globalConePointEquivalent left middle ->
      globalConePointEquivalent middle right ->
        globalConePointEquivalent left right
  localFamilyEquivalent_refl :
    ∀ family, localFamilyEquivalent family family
  localFamilyEquivalent_symm :
    ∀ {left right}, localFamilyEquivalent left right ->
      localFamilyEquivalent right left
  localFamilyEquivalent_trans :
    ∀ {left middle right},
      localFamilyEquivalent left middle ->
      localFamilyEquivalent middle right ->
        localFamilyEquivalent left right
  projected_glued_related :
    ∀ point,
      globalConePointEquivalent
        (glueCompatibleBinaryClockedConeFamily glueData
          (projectGlobalConePointToBinaryFamily model point))
        point
  glued_projected_related :
    ∀ family,
      localFamilyEquivalent
        (projectGlobalConePointToBinaryFamily model
          (glueCompatibleBinaryClockedConeFamily glueData family))
        family
  interfaceGlueBoundary : Prop
  inverseLawBoundary : Prop
  nonConclusions : Prop

/--
Endpoint-based equivalence for global cone points.

This is intentionally weaker than dependent path equality: two global cone
points are related when they land at the same global target.
-/
def GlobalConePointTargetEquivalent
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (p q :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) : Prop :=
  p.target = q.target

/--
Endpoint-based equivalence for compatible binary local cone families.

This deliberately ignores dependent path equality and keeps strict path
reconstruction as a future proof obligation.
-/
def LocalFamilyTargetEquivalent
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (p q : CompatibleBinaryClockedConeFamily model source horizon) :
    Prop :=
  p.leftTarget = q.leftTarget ∧ p.rightTarget = q.rightTarget

/--
Selected path-level equivalence data for global cone points.

The relation is supplied explicitly instead of requiring definitional equality
of dependent paths.  Endpoint equality is recorded as a consequence of the
selected path relation so this surface can be strengthened later.
-/
structure GlobalConePointPathEquivalenceData
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  related :
    ClockedConePoint model.globalSupport model.globalRelation source horizon ->
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon ->
        Prop
  refl : ∀ point, related point point
  symm : ∀ {left right}, related left right -> related right left
  trans :
    ∀ {left middle right},
      related left middle -> related middle right -> related left right
  impliesEndpoint :
    ∀ {left right}, related left right -> left.target = right.target
  nonConclusions : Prop

/--
Selected path-level equivalence data for compatible local cone families.

The relation can remember path-level information while exposing endpoint
agreement as a theorem-bearing consequence.
-/
structure LocalFamilyPathEquivalenceData
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  related :
    CompatibleBinaryClockedConeFamily model source horizon ->
      CompatibleBinaryClockedConeFamily model source horizon ->
        Prop
  refl : ∀ family, related family family
  symm : ∀ {left right}, related left right -> related right left
  trans :
    ∀ {left middle right},
      related left middle -> related middle right -> related left right
  impliesEndpoint :
    ∀ {left right}, related left right ->
      left.leftTarget = right.leftTarget ∧
        left.rightTarget = right.rightTarget
  nonConclusions : Prop

/-- Endpoint equivalence for global cone points is reflexive. -/
theorem globalConePointTargetEquivalent_refl
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    GlobalConePointTargetEquivalent point point :=
  rfl

/-- Endpoint equivalence for global cone points is symmetric. -/
theorem globalConePointTargetEquivalent_symm
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    {left right :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon}
    (h : GlobalConePointTargetEquivalent left right) :
    GlobalConePointTargetEquivalent right left :=
  h.symm

/-- Endpoint equivalence for global cone points is transitive. -/
theorem globalConePointTargetEquivalent_trans
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    {left middle right :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon}
    (h₁ : GlobalConePointTargetEquivalent left middle)
    (h₂ : GlobalConePointTargetEquivalent middle right) :
    GlobalConePointTargetEquivalent left right :=
  Eq.trans h₁ h₂

/-- Endpoint equivalence for local families is reflexive. -/
theorem localFamilyTargetEquivalent_refl
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    LocalFamilyTargetEquivalent family family :=
  ⟨rfl, rfl⟩

/-- Endpoint equivalence for local families is symmetric. -/
theorem localFamilyTargetEquivalent_symm
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    {left right : CompatibleBinaryClockedConeFamily model source horizon}
    (h : LocalFamilyTargetEquivalent left right) :
    LocalFamilyTargetEquivalent right left :=
  ⟨h.1.symm, h.2.symm⟩

/-- Endpoint equivalence for local families is transitive. -/
theorem localFamilyTargetEquivalent_trans
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    {left middle right :
      CompatibleBinaryClockedConeFamily model source horizon}
    (h₁ : LocalFamilyTargetEquivalent left middle)
    (h₂ : LocalFamilyTargetEquivalent middle right) :
    LocalFamilyTargetEquivalent left right :=
  ⟨Eq.trans h₁.1 h₂.1, Eq.trans h₁.2 h₂.2⟩

/--
Projection/gluing laws used to instantiate endpoint-based inverse laws.

Step-level projection laws are kept as explicit boundary propositions here; the
endpoint laws are theorem-bearing and are enough to construct selected descent
equivalence at endpoint granularity.
-/
structure BinaryProjectionGluingLaws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model) where
  left_project_glued_step_law : Prop
  right_project_glued_step_law : Prop
  projected_glued_endpoint_left :
    ∀ {source : Global} {horizon : Nat}
      (family : CompatibleBinaryClockedConeFamily model source horizon),
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family)).leftTarget =
        family.leftTarget
  projected_glued_endpoint_right :
    ∀ {source : Global} {horizon : Nat}
      (family : CompatibleBinaryClockedConeFamily model source horizon),
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family)).rightTarget =
        family.rightTarget
  global_glued_projected_target :
    ∀ {source : Global} {horizon : Nat}
      (point :
        ClockedConePoint model.globalSupport model.globalRelation
          source horizon),
      (glueCompatibleBinaryClockedConeFamily glueData
        (projectGlobalConePointToBinaryFamily model point)).target =
        point.target
  strictPathInverseLawBoundary : Prop
  lawBoundary : Prop
  nonConclusions : Prop

/--
Path-level projection/gluing laws over the concrete step-glued map.

This strengthens the endpoint-law surface by requiring selected path-level
equivalence data for both global cone points and compatible local families.
The path relations remain explicit selected relations; this does not assert
definitional equality of dependent paths.
-/
structure BinaryProjectionGluingPathLaws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model) where
  endpointLaws : BinaryProjectionGluingLaws glueData
  globalPathEquiv :
    ∀ (source : Global) (horizon : Nat),
      GlobalConePointPathEquivalenceData model source horizon
  localPathEquiv :
    ∀ (source : Global) (horizon : Nat),
      LocalFamilyPathEquivalenceData model source horizon
  glue_project_after_projection_path :
    ∀ {source : Global} {horizon : Nat}
      (point :
        ClockedConePoint model.globalSupport model.globalRelation
          source horizon),
      (globalPathEquiv source horizon).related
        (glueCompatibleBinaryClockedConeFamily glueData
          (projectGlobalConePointToBinaryFamily model point))
        point
  project_after_glue_path :
    ∀ {source : Global} {horizon : Nat}
      (family : CompatibleBinaryClockedConeFamily model source horizon),
      (localPathEquiv source horizon).related
        (projectGlobalConePointToBinaryFamily model
          (glueCompatibleBinaryClockedConeFamily glueData family))
        family
  strictPathLawBoundary : Prop
  nonConclusions : Prop

namespace BinaryProjectionGluingPathLaws

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}
variable {glueData : BinaryClockedStepGluingData model}

/--
Forget selected path-level inverse laws back to their endpoint-law component.
-/
def toEndpointLaws
    (pathLaws : BinaryProjectionGluingPathLaws glueData) :
    BinaryProjectionGluingLaws glueData :=
  pathLaws.endpointLaws

/--
The selected global path inverse law entails the corresponding endpoint law.
-/
theorem glue_project_after_projection_endpoint
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat}
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    (glueCompatibleBinaryClockedConeFamily glueData
      (projectGlobalConePointToBinaryFamily model point)).target =
      point.target :=
  (pathLaws.globalPathEquiv source horizon).impliesEndpoint
    (pathLaws.glue_project_after_projection_path point)

/--
The selected local-family path inverse law entails the corresponding left and
right endpoint laws.
-/
theorem project_after_glue_endpoint
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat}
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    (projectGlobalConePointToBinaryFamily model
      (glueCompatibleBinaryClockedConeFamily glueData family)).leftTarget =
        family.leftTarget ∧
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family)).rightTarget =
        family.rightTarget :=
  (pathLaws.localPathEquiv source horizon).impliesEndpoint
    (pathLaws.project_after_glue_path family)

end BinaryProjectionGluingPathLaws

/-- Projection after gluing is endpoint-related to the original local family. -/
theorem projected_glued_target_related
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {glueData : BinaryClockedStepGluingData model}
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat}
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    LocalFamilyTargetEquivalent
      (projectGlobalConePointToBinaryFamily model
        (glueCompatibleBinaryClockedConeFamily glueData family))
      family :=
  ⟨laws.projected_glued_endpoint_left family,
    laws.projected_glued_endpoint_right family⟩

/-- Gluing after projection is endpoint-related to the original global point. -/
theorem glued_projected_target_related
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {glueData : BinaryClockedStepGluingData model}
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat}
    (point :
      ClockedConePoint model.globalSupport model.globalRelation
        source horizon) :
    GlobalConePointTargetEquivalent
      (glueCompatibleBinaryClockedConeFamily glueData
        (projectGlobalConePointToBinaryFamily model point))
      point :=
  laws.global_glued_projected_target point

namespace BinaryProjectionGluingEquivalenceLaws

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}

/--
Instantiate selected inverse laws from endpoint projection/glue laws.

The resulting relatedness is endpoint-based; strict path reconstruction remains
recorded by the law boundary.
-/
def ofEndpointLaws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    (source : Global) (horizon : Nat) :
    BinaryProjectionGluingEquivalenceLaws glueData source horizon where
  globalConePointEquivalent := GlobalConePointTargetEquivalent
  localFamilyEquivalent := LocalFamilyTargetEquivalent
  globalConePointEquivalent_refl :=
    globalConePointTargetEquivalent_refl
  globalConePointEquivalent_symm :=
    globalConePointTargetEquivalent_symm
  globalConePointEquivalent_trans :=
    globalConePointTargetEquivalent_trans
  localFamilyEquivalent_refl :=
    localFamilyTargetEquivalent_refl
  localFamilyEquivalent_symm :=
    localFamilyTargetEquivalent_symm
  localFamilyEquivalent_trans :=
    localFamilyTargetEquivalent_trans
  projected_glued_related :=
    glued_projected_target_related laws
  glued_projected_related :=
    projected_glued_target_related laws
  interfaceGlueBoundary := laws.lawBoundary
  inverseLawBoundary :=
    laws.left_project_glued_step_law ∧
      laws.right_project_glued_step_law ∧
        laws.strictPathInverseLawBoundary ∧ laws.lawBoundary
  nonConclusions := laws.nonConclusions

end BinaryProjectionGluingEquivalenceLaws

namespace BinaryDescentAssumptions

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable {cover : BinaryFieldCover Global Left Right Interface}
variable {OperationG : Type y} {OperationL : Type z}
variable {OperationR : Type a} {OperationI : Type b}
variable {model :
  BinarySFTModel cover OperationG OperationL OperationR OperationI}
variable {source : Global} {horizon : Nat}

/--
Build descent assumptions from concrete step-level gluing plus selected
projection/gluing inverse laws.
-/
def ofStepGluing
    (glueData : BinaryClockedStepGluingData model)
    (equivData :
      BinaryProjectionGluingEquivalenceLaws glueData source horizon) :
    BinaryDescentAssumptions model source horizon where
  glueLocalFamily := glueCompatibleBinaryClockedConeFamily glueData
  globalConePointEquivalent := equivData.globalConePointEquivalent
  localFamilyEquivalent := equivData.localFamilyEquivalent
  globalConePointEquivalent_refl :=
    equivData.globalConePointEquivalent_refl
  globalConePointEquivalent_symm :=
    equivData.globalConePointEquivalent_symm
  globalConePointEquivalent_trans :=
    equivData.globalConePointEquivalent_trans
  localFamilyEquivalent_refl :=
    equivData.localFamilyEquivalent_refl
  localFamilyEquivalent_symm :=
    equivData.localFamilyEquivalent_symm
  localFamilyEquivalent_trans :=
    equivData.localFamilyEquivalent_trans
  projected_glued_related := equivData.projected_glued_related
  glued_projected_related := equivData.glued_projected_related
  interfaceGlueBoundary := equivData.interfaceGlueBoundary
  inverseLawBoundary := equivData.inverseLawBoundary
  nonConclusions := equivData.nonConclusions

/--
Build descent assumptions from concrete step gluing and endpoint projection /
glue laws.
-/
def ofEndpointLaws
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    (source : Global) (horizon : Nat) :
    BinaryDescentAssumptions model source horizon :=
  ofStepGluing glueData
    (BinaryProjectionGluingEquivalenceLaws.ofEndpointLaws
      glueData laws source horizon)

/-- Glue a compatible local family to the selected global cone point. -/
def glueClockedPoint
    (assumptions :
      BinaryDescentAssumptions model source horizon)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    ClockedConePoint model.globalSupport model.globalRelation source horizon :=
  assumptions.glueLocalFamily family

/-- The path component of the selected glued global cone point. -/
def glueClockedPath
    (assumptions :
      BinaryDescentAssumptions model source horizon)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    ClockedFieldPath model.globalSupport model.globalRelation
      source (assumptions.glueClockedPoint family).target :=
  (assumptions.glueClockedPoint family).path

/-- The selected glued path has exact shared-clock length. -/
theorem glueClockedPath_length
    (assumptions :
      BinaryDescentAssumptions model source horizon)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    ArchitecturePath.length (assumptions.glueClockedPath family) =
      horizon :=
  ClockedConePoint.length_eq_horizon
    (assumptions.glueClockedPoint family)

/-- The selected glued point carries global clocked cone membership. -/
theorem glueClockedPath_coneMember
    (assumptions :
      BinaryDescentAssumptions model source horizon)
    (family : CompatibleBinaryClockedConeFamily model source horizon) :
    ClockedForecastCone model.globalSupport model.globalRelation
      source horizon
      (assumptions.glueClockedPoint family).target
      (assumptions.glueClockedPath family) :=
  (assumptions.glueClockedPoint family).coneMember

end BinaryDescentAssumptions

/--
Binary ForecastCone descent equivalence constructed from explicit assumptions.

This is the first substantive binary descent theorem surface: the global-to-
local direction is computed by path projection, and the local-to-global
direction is the selected glue function supplied by the assumptions.
-/
def forecastCone_descent_binary
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (assumptions :
      BinaryDescentAssumptions model source horizon) :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon) where
  toFun := projectGlobalConePointToBinaryFamily model
  invFun := assumptions.glueLocalFamily
  leftRelated := assumptions.globalConePointEquivalent
  rightRelated := assumptions.localFamilyEquivalent
  left_refl := assumptions.globalConePointEquivalent_refl
  left_symm := assumptions.globalConePointEquivalent_symm
  left_trans := assumptions.globalConePointEquivalent_trans
  right_refl := assumptions.localFamilyEquivalent_refl
  right_symm := assumptions.localFamilyEquivalent_symm
  right_trans := assumptions.localFamilyEquivalent_trans
  left_related := assumptions.projected_glued_related
  right_related := assumptions.glued_projected_related
  equivalenceBoundary :=
    assumptions.interfaceGlueBoundary ∧ assumptions.inverseLawBoundary
  nonConclusions := assumptions.nonConclusions

/--
Binary ForecastCone descent from concrete step gluing plus endpoint projection /
glue laws.
-/
def forecastCone_descent_binary_of_endpoint_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon) :=
  forecastCone_descent_binary
    (BinaryDescentAssumptions.ofEndpointLaws
      glueData laws source horizon)

/--
Binary ForecastCone descent from concrete step gluing plus selected path-level
projection/glue inverse laws.

The resulting equivalence uses the supplied path-level relatedness on both
sides.  It is still a selected equivalence, not definitional equality of all
projected and glued dependent paths.
-/
def forecastCone_descent_binary_of_path_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon) where
  toFun := projectGlobalConePointToBinaryFamily model
  invFun := glueCompatibleBinaryClockedConeFamily glueData
  leftRelated := (pathLaws.globalPathEquiv source horizon).related
  rightRelated := (pathLaws.localPathEquiv source horizon).related
  left_refl := (pathLaws.globalPathEquiv source horizon).refl
  left_symm := (pathLaws.globalPathEquiv source horizon).symm
  left_trans := (pathLaws.globalPathEquiv source horizon).trans
  right_refl := (pathLaws.localPathEquiv source horizon).refl
  right_symm := (pathLaws.localPathEquiv source horizon).symm
  right_trans := (pathLaws.localPathEquiv source horizon).trans
  left_related := pathLaws.glue_project_after_projection_path
  right_related := pathLaws.project_after_glue_path
  equivalenceBoundary :=
    pathLaws.endpointLaws.lawBoundary ∧
      pathLaws.endpointLaws.left_project_glued_step_law ∧
        pathLaws.endpointLaws.right_project_glued_step_law ∧
          pathLaws.endpointLaws.strictPathInverseLawBoundary ∧
            pathLaws.strictPathLawBoundary
  nonConclusions :=
    pathLaws.endpointLaws.nonConclusions ∧ pathLaws.nonConclusions

/-- A selected package wrapping the constructed binary descent equivalence. -/
structure BinarySelectedForecastConeDescentPackage
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI)
    (source : Global) (horizon : Nat) where
  descentEquivalence :
    ConeEquivalence
      (ClockedConePoint model.globalSupport model.globalRelation
        source horizon)
      (CompatibleBinaryClockedConeFamily model source horizon)
  packageBoundary : Prop
  nonConclusions : Prop

/-- Build the selected binary descent package from explicit descent assumptions. -/
def BinarySelectedForecastConeDescentPackage.ofAssumptions
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (assumptions :
      BinaryDescentAssumptions model source horizon) :
    BinarySelectedForecastConeDescentPackage model source horizon where
  descentEquivalence := forecastCone_descent_binary assumptions
  packageBoundary :=
    assumptions.interfaceGlueBoundary ∧ assumptions.inverseLawBoundary
  nonConclusions := assumptions.nonConclusions

/--
Build the selected binary descent package from endpoint projection/glue laws.
-/
def BinarySelectedForecastConeDescentPackage.ofEndpointLaws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    BinarySelectedForecastConeDescentPackage model source horizon where
  descentEquivalence :=
    forecastCone_descent_binary_of_endpoint_laws glueData laws
  packageBoundary :=
    laws.lawBoundary ∧ laws.left_project_glued_step_law ∧
      laws.right_project_glued_step_law ∧
        laws.strictPathInverseLawBoundary
  nonConclusions := laws.nonConclusions

/--
Build the selected binary descent package from selected path-level projection /
glue laws.
-/
def BinarySelectedForecastConeDescentPackage.ofPathLaws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    BinarySelectedForecastConeDescentPackage model source horizon where
  descentEquivalence :=
    forecastCone_descent_binary_of_path_laws glueData pathLaws
  packageBoundary :=
    pathLaws.endpointLaws.lawBoundary ∧
      pathLaws.endpointLaws.left_project_glued_step_law ∧
        pathLaws.endpointLaws.right_project_glued_step_law ∧
          pathLaws.endpointLaws.strictPathInverseLawBoundary ∧
            pathLaws.strictPathLawBoundary
  nonConclusions :=
    pathLaws.endpointLaws.nonConclusions ∧ pathLaws.nonConclusions

/-- Existence wrapper for the selected binary descent package. -/
theorem binaryForecastConeDescentPackage_of_assumptions
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    {source : Global} {horizon : Nat}
    (assumptions :
      BinaryDescentAssumptions model source horizon) :
  Nonempty (BinarySelectedForecastConeDescentPackage model source horizon) :=
  ⟨BinarySelectedForecastConeDescentPackage.ofAssumptions assumptions⟩

/-- Existence wrapper for binary descent under endpoint projection/glue laws. -/
theorem binaryForecastConeDescentPackage_of_endpoint_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (laws : BinaryProjectionGluingLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon) :=
  ⟨BinarySelectedForecastConeDescentPackage.ofEndpointLaws
    glueData laws⟩

/--
Existence wrapper for binary descent under selected path-level projection /
glue laws.
-/
theorem binaryForecastConeDescentPackage_of_path_laws
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    {model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI}
    (glueData : BinaryClockedStepGluingData model)
    (pathLaws : BinaryProjectionGluingPathLaws glueData)
    {source : Global} {horizon : Nat} :
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon) :=
  ⟨BinarySelectedForecastConeDescentPackage.ofPathLaws
    glueData pathLaws⟩

/-- Binary SFT module boundary, defined as selected descent at all sources and horizons. -/
def SFTModuleBoundary
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    Prop :=
  ∀ source horizon,
    Nonempty (BinarySelectedForecastConeDescentPackage model source horizon)

/-- The binary module-boundary representation is definitional descent for all horizons. -/
theorem moduleBoundary_iff_forecastConeDescent
    {Global : Type u} {Left : Type v} {Right : Type w}
    {Interface : Type x}
    {cover : BinaryFieldCover Global Left Right Interface}
    {OperationG : Type y} {OperationL : Type z}
    {OperationR : Type a} {OperationI : Type b}
    (model :
      BinarySFTModel cover OperationG OperationL OperationR OperationI) :
    SFTModuleBoundary model ↔
      ∀ source horizon,
        Nonempty
          (BinarySelectedForecastConeDescentPackage model source horizon) :=
  Iff.rfl

/-- A selected local family does not lift through a given global-to-local map. -/
def LocalFamilyDoesNotLift
    {GlobalCone : Type u} {LocalFamily : Type v}
    (toLocal : GlobalCone -> LocalFamily) (family : LocalFamily) : Prop :=
  ∀ global, toLocal global ≠ family

/-- Two globally distinct paths are identified by a selected local observation. -/
def GlobalPathsLocallyIdentified
    {GlobalCone : Type u} {LocalFamily : Type v}
    (toLocal : GlobalCone -> LocalFamily)
    (global₁ global₂ : GlobalCone) : Prop :=
  global₁ ≠ global₂ ∧ toLocal global₁ = toLocal global₂

end Formal.Arch
