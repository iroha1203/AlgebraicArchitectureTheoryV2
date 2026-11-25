import Formal.SHIGURE.Part1.StructureCategory
import Formal.SHIGURE.Part2.Realizations.CopyingMode

/-!
# Copying through the Part I coefficient reading

The existing coefficient scheme API reads designated points and their
primitive structure. The copying realization also retains all its
relative sections and their maps for the interpretation of positive Laws.

## Implementation notes

The relative test category indexes the components of sheaf arrows in a
larger universe than the designated states. Part I's coefficient scheme
uses a category whose arrows belong to the state universe. A map of
sections induced by a sheaf arrow is small, and its equality expresses
equality of the maps available to a reading. The functor from the sheaf
/-- Copying models inherit identities and composition from the structure-preserving sheaf maps. -/
structure category sends every preserving sheaf arrow to this actual map.
-/

open AlgebraicGeometry CategoryTheory Opposite

universe u

noncomputable section

namespace SHIGURE

open DeclarationContext

variable {P : PrimitivePresentation.{u}} {U : DeclarationContext P}

/-- The selected structural map carries atomic truth through the Part I reading. -/
private theorem ContextStructure.Hom.preservesAtomic {A B : ContextStructure U}
    (f : ContextStructure.Hom A B) :
    A.toRestrictedStructure.Preserves B.toRestrictedStructure f.onSort := by
  intro Γ a supported e held
  rw [A.toRestrictedStructure_evaluation] at held
  rw [B.toRestrictedStructure_evaluation]
  cases a with
  | eq x y =>
    exact congrArg (f.onSort _ _) held
  | rel r vars =>
    exact f.relation_mem r (supported (Declaration.relation_mem_atomicSupport r vars)) (e.pull vars) held
  | domain p vars =>
    exact f.domain_mem p (supported (Declaration.domain_mem_atomicSupport p vars)) (e.pull vars) held
  | graph op vars y =>
    exact f.graph_mem op (supported (Declaration.graph_mem_atomicSupport op vars y)) (e.pull vars) (e y) held

namespace Copying

/-- Copying objects as read by the coefficient observation interface. -/
def ReadCopying (sig : Signature.{u}) (S : Scheme.{u}) : Type (u + 1) :=
  SheafStructure sig (Scheme.zariskiTopology.over S)

/-- At the observation interface, identify sheaf arrows that give the
same structure map on the coefficient scheme's sections. -/
instance readCopyingCategory (sig : Signature.{u}) (S : Scheme.{u}) :
    Category.{u} (ReadCopying sig S) where
  Hom A B := {f : StructureMap (A.sections (op (Over.mk (𝟙 S)))) (B.sections (op (Over.mk (𝟙 S)))) //
    ∃ h : SheafStructure.Hom A B, h.sections (op (Over.mk (𝟙 S))) = f}
  id A := ⟨StructureMap.id _, ⟨SheafStructure.Hom.id A, StructureMap.ext (fun _ _ => rfl)⟩⟩
  comp f g := ⟨StructureMap.comp g.val f.val, by
    obtain ⟨f', hf⟩ := f.property
    obtain ⟨g', hg⟩ := g.property
    rw [← hf, ← hg]
    exact ⟨f'.comp g', StructureMap.ext (fun _ _ => rfl)⟩⟩
  id_comp _ := Subtype.ext (StructureMap.ext (fun _ _ => rfl))
  comp_id _ := Subtype.ext (StructureMap.ext (fun _ _ => rfl))
  assoc _ _ _ := Subtype.ext (StructureMap.ext (fun _ _ => rfl))

/-- Every structural sheaf arrow induces its actual arrow in the coefficient reading. -/
def readCopyingFunctor (sig : Signature.{u}) (S : Scheme.{u}) :
    SheafStructure sig (Scheme.zariskiTopology.over S) ⥤ ReadCopying sig S where
  obj A := A
  map f := ⟨f.sections (op (Over.mk (𝟙 S))), ⟨f, rfl⟩⟩
  map_id _ := Subtype.ext (StructureMap.ext (fun _ _ => rfl))
  map_comp _ _ := Subtype.ext (StructureMap.ext (fun _ _ => rfl))

/-- Compare the section carrier with the corresponding Part I state set. -/
private def sectionCarrierEquiv {S : Scheme.{u}}
    (A : SheafStructure (Selected.signature U) (Scheme.zariskiTopology.over S))
    (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations) :
    (readCopyingContext U A).carrier s ≃ (A.carrier ⟨s, kept⟩).val.obj (op (Over.mk (𝟙 S))) :=
  Selected.writeCarrierEquiv (A.sections (op (Over.mk (𝟙 S)))) s kept

/-- Read copying structures and their designated sections through the
Part I coefficient interface. The objects are primitive structures
before checking local splitting and the required Laws. Explicit point
choices are permitted on every retained sort. Its arrows are the
section maps induced by preserving sheaf arrows. -/
def copyingCoefficientScheme (U : DeclarationContext P) (base : CoefficientRing.{u}) :
    CoefficientScheme U base where
  Realization R := ReadCopying (Selected.signature U) R.scalars.spec
  structureOf _ A := (readCopyingContext U A).toRestrictedStructure
  structure_retained _ A := (readCopyingContext U A).omitted
  category _ := inferInstance
  mapPoints f := (Selected.writeStructureMap f.val).onSort
  mapPoints_preserves f := (Selected.writeStructureMap f.val).preservesAtomic
  mapPoints_id _ _ _ _ := by
    simp only [Selected.writeStructureMap_onSort, Selected.writeOnSort_apply]
    exact Equiv.symm_apply_apply _ _
  mapPoints_comp f g _ _ _ := by
    simp only [Selected.writeStructureMap_onSort, Selected.writeOnSort_apply,
      Equiv.apply_symm_apply]
    rfl
  permitsPoints _ _ _ _ _ := True
  permitsPoints_congr := by intros; rfl
  Native := ContextStructure U
  nativeStructure := ContextStructure.toRestrictedStructure
  native_retained A := A.omitted
  realizeNative R := realizeSelectedCopying R
  nativePoints R A s kept x := (sectionCarrierEquiv (realizeSelectedCopying R A) s kept).symm
    (nativeState R.scalars.spec (Over.mk (𝟙 R.scalars.spec)) (Selected.readCarrierEquiv A s kept x))
  nativePoints_permitted _ _ _ _ := trivial
  interpretLaw _ A law supported := A.holdsLaw (Selected.selectLaw law supported)
  change f := restrictStructure (CoefficientRing.specMap f)
  changePoints f A s kept x :=
    (sectionCarrierEquiv (restrictStructure (CoefficientRing.specMap f) A) s kept).symm
      (restrictState (CoefficientRing.specMap f) A ⟨s, kept⟩ (sectionCarrierEquiv A s kept x))

/-- The Part I scheme reads distinct native states as distinct points on any
coefficient scheme with a point. -/
theorem copyingCoefficientScheme_nativePoints_injective (U : DeclarationContext P)
    {base : CoefficientRing.{u}} (R : CoefficientAlgebra base) (p : R.scalars.spec)
    (A : ContextStructure U) (s : P.signature.SortType) (kept : Declaration.sort s ∈ U.declarations) :
    Function.Injective ((copyingCoefficientScheme U base).nativePoints R A s kept) := by
  intro x y h
  let e := sectionCarrierEquiv (realizeSelectedCopying R A) s kept
  apply (Selected.readCarrierEquiv A s kept).injective
  have hv := e.symm.injective h
  exact congrArg (fun a : LocallyConstant R.scalars.spec
    ((Selected.readStructure A).carrier ⟨s, kept⟩) => a p) hv

end Copying

end SHIGURE
