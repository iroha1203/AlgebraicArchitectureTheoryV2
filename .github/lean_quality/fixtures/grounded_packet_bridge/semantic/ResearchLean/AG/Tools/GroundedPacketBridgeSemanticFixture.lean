import ResearchLean.Tools.MigrationAudit

/-!
Compiled semantic mutation pairs for the grounded-packet bridge audit.
Each bad declaration retains enough type shape to isolate the named mutation.
-/

namespace ResearchLean.AG.Tools.GroundedPacketBridgeSemanticFixture

def projectIdentity : Nat -> Nat := id
def projectConstant : Nat -> Nat := fun _ => 0

structure SkeletonChoice where
  selected : Nat
  arbitrary : Nat

def skeletonSelected (choice : SkeletonChoice) : Nat := choice.selected
def skeletonArbitrary (choice : SkeletonChoice) : Nat := choice.arbitrary

def bindersAllUsed (left right : Nat) : Nat := left + right
def binderRightUnused (left _right : Nat) : Nat := left

structure GeometrySource where
  left : Nat
  right : Nat

structure GeometryTarget where
  left : Nat
  right : Nat

def geometryFieldwise (source : GeometrySource) : GeometryTarget where
  left := source.left
  right := source.right

def geometrySwapped (source : GeometrySource) : GeometryTarget where
  left := source.right
  right := source.left

theorem conclusionsTen :
    True /\ True /\ True /\ True /\ True /\
      True /\ True /\ True /\ True /\ True := by
  simp

theorem conclusionMissing :
    True /\ True /\ True /\ True /\ True /\
      True /\ True /\ True /\ True := by
  simp

theorem premiseOriginal : True := by
  trivial

theorem premiseAdded (_extra : True) : True := by
  trivial

end ResearchLean.AG.Tools.GroundedPacketBridgeSemanticFixture
