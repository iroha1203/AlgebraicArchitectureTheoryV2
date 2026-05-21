import Formal.Arch.Evolution.SFTClockedCone

/-!
Binary field covers for the first substantive SFT descent theorem.

The cover is intentionally binary for the first descent step.  Finite Cech
covers can later be layered on top of this API.
-/

namespace Formal.Arch

universe u v w x

/--
A binary cover of a global field by left and right local regions with a shared
interface.

`global_ext` is the theorem-bearing uniqueness principle used by descent:
global states are equal when their left and right restrictions agree.
-/
structure BinaryFieldCover
    (Global : Type u) (Left : Type v) (Right : Type w)
    (Interface : Type x) where
  restrictLeft : Global -> Left
  restrictRight : Global -> Right
  leftInterface : Left -> Interface
  rightInterface : Right -> Interface
  compatible : Left -> Right -> Prop
  glue : (l : Left) -> (r : Right) -> compatible l r -> Global
  glue_left :
    ∀ l r h, restrictLeft (glue l r h) = l
  glue_right :
    ∀ l r h, restrictRight (glue l r h) = r
  compatible_iff_interface :
    ∀ l r, compatible l r ↔ leftInterface l = rightInterface r
  global_compatible :
    ∀ g, compatible (restrictLeft g) (restrictRight g)
  global_ext :
    ∀ g₁ g₂,
      restrictLeft g₁ = restrictLeft g₂ ->
        restrictRight g₁ = restrictRight g₂ ->
          g₁ = g₂
  coverBoundary : Prop
  nonConclusions : Prop

namespace BinaryFieldCover

variable {Global : Type u} {Left : Type v} {Right : Type w}
variable {Interface : Type x}
variable (cover : BinaryFieldCover Global Left Right Interface)

/-- Compatibility of a pair can be read as interface equality. -/
theorem compatible_iff_interface_eq (l : Left) (r : Right) :
    cover.compatible l r ↔
      cover.leftInterface l = cover.rightInterface r :=
  cover.compatible_iff_interface l r

/-- Every global state restricts to a compatible local pair. -/
theorem restricts_compatible (g : Global) :
    cover.compatible (cover.restrictLeft g) (cover.restrictRight g) :=
  cover.global_compatible g

/-- Gluing exposes the selected left restriction. -/
theorem restrictLeft_glue (l : Left) (r : Right)
    (h : cover.compatible l r) :
    cover.restrictLeft (cover.glue l r h) = l :=
  cover.glue_left l r h

/-- Gluing exposes the selected right restriction. -/
theorem restrictRight_glue (l : Left) (r : Right)
    (h : cover.compatible l r) :
    cover.restrictRight (cover.glue l r h) = r :=
  cover.glue_right l r h

/-- Gluing a global state's selected restrictions reconstructs that state. -/
theorem glue_restricts_eq (g : Global) :
    cover.glue (cover.restrictLeft g) (cover.restrictRight g)
      (cover.global_compatible g) = g := by
  apply cover.global_ext
  · exact cover.glue_left _ _ _
  · exact cover.glue_right _ _ _

/--
For a fixed compatible local pair, the selected glued global state is
independent of the particular compatibility proof.
-/
theorem glue_compatible_proof_irrel
    (l : Left) (r : Right)
    (h₁ h₂ : cover.compatible l r) :
    cover.glue l r h₁ = cover.glue l r h₂ := by
  apply cover.global_ext
  · calc
      cover.restrictLeft (cover.glue l r h₁) = l :=
        cover.glue_left l r h₁
      _ = cover.restrictLeft (cover.glue l r h₂) :=
        (cover.glue_left l r h₂).symm
  · calc
      cover.restrictRight (cover.glue l r h₁) = r :=
        cover.glue_right l r h₁
      _ = cover.restrictRight (cover.glue l r h₂) :=
        (cover.glue_right l r h₂).symm

/-- The cover-level modeling boundary remains explicit. -/
def RecordsCoverBoundary : Prop :=
  cover.coverBoundary

/-- Cover non-conclusions remain explicit. -/
def RecordsNonConclusions : Prop :=
  cover.nonConclusions

end BinaryFieldCover

end Formal.Arch
