import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawLocalDataCompositionNative
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRawRecovery
import Formal.Util.AssertStandardAxioms

/-!
# Complete primitive raw-query composition

Implementation notes: coordinate, relation, and dependent local-data point
compositions fill the original raw-query declaration. The common convention
keeps source/target order in both direction tags. The final comparison covers
all raw query constructors and candidates with the original native composite.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {A B C : ArchitectureObject U}

/-- Fill every common raw query from its direct coordinate, relation, or dependent local-data composition. -/
def composeRaw (s : IndependentRawCandidate.Table.{u, v} A) (t : IndependentRawCandidate.Table.{u, v} B)
    (r : IndependentRawCandidate.Table.{u, v} C) (h : Table.{u, v} U .explicit) (hp : PointLaws s t h)
    (k : Table.{u, v} U .explicit) (hq : ∀ Z : ArchCtx C, ∃! V : ArchCtx B, contextPoints k V Z = true)
    (kp : PointLaws t r k) : RawQuery A C .explicit → Bool
  | .coordinate d W Z a => InverseRows.fromInverse
      (IndependentIndexedInverseGraph.row (composeCoordinate s t r h hp k hq kp) W Z) d a
  | .relation d W Z a => InverseRows.fromInverse
      (IndependentIndexedInverseGraph.row (composeRelation s t r h hp k hq kp) W Z) d a
  | .localData d W Z D F x z a => InverseRows.fromInverse
      (composeLocalData s t r h hp k kp hq W Z D F x z) d a

variable {G H K : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (g : PackageTotalHom H.core K.core)
variable (a : G.Coefficient →+* H.Coefficient) (b : H.Coefficient →+* K.Coefficient)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h) (hp : NativePoints G H h)
variable (k : Table.{u, v} U .explicit) (km : Maps g b k) (kp : NativePoints H K k)
variable (hq : ∀ Z : ArchCtx K.core.object, ∃! V : ArchCtx H.core.object, contextPoints k V Z = true)

/-- Every directly composed raw query agrees with the reader of native raw-map composition. -/
theorem composeRaw_eq_native :
    composeRaw (IndependentRawCandidate.read G.site G.Coefficient G.raw)
      (IndependentRawCandidate.read H.site H.Coefficient H.raw)
      (IndependentRawCandidate.read K.site K.Coefficient K.raw) h hp k hq kp =
      readRaw (PackageTotalHom.comp f g) (b.comp a)
        ((assemble f a h hm hp).trans (assemble g b k km kp)) := by
  funext z
  cases z with
  | coordinate d W Z a =>
    exact congrArg (fun p => InverseRows.fromInverse p d a)
      (composeCoordinate_eq_native f g _ _ h hm hp k km kp hq W Z)
  | relation d W Z a =>
    exact congrArg (fun p => InverseRows.fromInverse p d a)
      (composeRelation_eq_native f g _ _ h hm hp k km kp hq W Z)
  | localData d W Z D F x z a =>
    exact congrArg (fun p => InverseRows.fromInverse p d a)
      (composeLocalData_eq_native f g _ _ h hm hp k km kp hq W Z D F x z)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
