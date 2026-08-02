import ResearchLean.AG.AtomFoundation.LiftUniqueness
import Formal.AG.Examples.FiniteModel

/-!
# A finite refinement obstruction

This module gives the strict refinement witness required by G-101.  Its Atom
map is a nonidentity bijection on `FiniteModel.carrier`, and extraction is
preserved but not reflected.  The newly admitted Atom then contradicts the
`extraction_eq` field of every proposed exact upper lift, uniformly for every
package over the mapped target point.
-/

namespace AAT.AG.AtomFoundation

open CategoryTheory

/-- The existing nondegenerate finite package used as the refinement source. -/
noncomputable abbrev refinementSourcePackage : AATCorePackage FiniteModel.carrier :=
  FiniteModel.corePackage

/-- A nonidentity bijection which swaps two selected finite Atoms. -/
noncomputable def refinementAtomEquiv :
    FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom := by
  classical
  exact Equiv.swap FiniteModel.FiniteAtom.componentA FiniteModel.FiniteAtom.componentB

/-- The specified Atom function of the finite refinement. -/
noncomputable def refinementAtomMap :
    FiniteModel.carrier.Atom → FiniteModel.carrier.Atom :=
  refinementAtomEquiv

/-- The specified Atom map exchanges the first selected component. -/
@[simp]
theorem refinementAtomMap_componentA :
    refinementAtomMap FiniteModel.FiniteAtom.componentA =
      FiniteModel.FiniteAtom.componentB := by
  classical
  simp [refinementAtomMap, refinementAtomEquiv]

/-- The specified Atom map fixes the newly admitted component. -/
@[simp]
theorem refinementAtomMap_componentC :
    refinementAtomMap FiniteModel.FiniteAtom.componentC =
      FiniteModel.FiniteAtom.componentC := by
  classical
  exact Equiv.swap_apply_of_ne_of_ne
    (by exact FiniteModel.FiniteAtom.noConfusion)
    (by exact FiniteModel.FiniteAtom.noConfusion)

/-- The finite refinement does not use the identity Atom map. -/
theorem refinementAtomMap_nonidentity : refinementAtomMap ≠ id := by
  intro h
  have hA := congrFun h FiniteModel.FiniteAtom.componentA
  simp only [refinementAtomMap_componentA, id_eq] at hA
  exact FiniteModel.FiniteAtom.noConfusion hA

/-- The specified nonidentity Atom map is nevertheless bijective. -/
theorem refinementAtomMap_bijective : Function.Bijective refinementAtomMap :=
  refinementAtomEquiv.bijective

/-- A target doctrine which admits every Atom at every finite source. -/
def refinementTargetDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := FiniteModel.ExtractionSource
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

/--
A bijective, forward-only refinement from the selective finite doctrine to the
all-admitting target doctrine.
-/
noncomputable def finiteExtractionRefinement :
    RefinementDoctrineHom FiniteModel.extractionDoctrine refinementTargetDoctrine where
  sourceMap := id
  atomMap := refinementAtomMap
  atomMap_bijective := refinementAtomMap_bijective
  normalize_eq _ := rfl
  extraction_forward := by
    intro _source _atom _hextracts
    exact ⟨trivial, trivial, trivial, trivial⟩

/-- The refinement is strict: the mapped target admits an Atom rejected at the source. -/
theorem finiteExtractionRefinement_not_reflecting :
    refinementTargetDoctrine.extracts
        (finiteExtractionRefinement.sourceMap
          FiniteModel.ExtractionSource.withoutComponentC)
        (finiteExtractionRefinement.atomMap FiniteModel.FiniteAtom.componentC) ∧
      ¬ FiniteModel.extractionDoctrine.extracts
        FiniteModel.ExtractionSource.withoutComponentC
        FiniteModel.FiniteAtom.componentC := by
  constructor
  · exact ⟨trivial, trivial, trivial, trivial⟩
  · exact FiniteModel.componentC_not_extracted_withoutComponentC

/-- The mapped pointed doctrine selected by the refinement witness. -/
noncomputable def refinementTargetPoint : ExtractionInstance FiniteModel.carrier where
  doctrine := refinementTargetDoctrine
  source := finiteExtractionRefinement.sourceMap
    FiniteModel.ExtractionSource.withoutComponentC

/-- Nonempty target equation system; every residual is zero. -/
private noncomputable def refinementTargetEquationSystem
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitecturalEquationSystem (Site.contextMorphismPreorderCategory A) where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 0
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ _ _ _ => 0
  equationResidual_restrict := by intros; rfl

/-- A nonempty-index equation reading with a sound rejecting detector. -/
private noncomputable def refinementTargetEquationReading
    (A : ArchitectureObject FiniteModel.carrier) : EquationReading A where
  contextPreorder := Site.contextMorphismPreorderCategory A
  equationSystem := refinementTargetEquationSystem A
  circuits := {
    code := fun _ => .reject
  }
  circuitSound := by
    intro _index _object _datum _hmatches haccepts _hequation
    simp at haccepts

/-- An admissible core reading whose pointed doctrine is the mapped target. -/
private noncomputable def refinementTargetCoreReading :
    CoreReading FiniteModel.carrier where
  doctrine := refinementTargetDoctrine
  source := finiteExtractionRefinement.sourceMap
    FiniteModel.ExtractionSource.withoutComponentC
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := FiniteModel.compositionReading
  objectReading := FiniteModel.objectReading
  equationReading := refinementTargetEquationReading _
  invariantReading := FiniteModel.invariantFamily
  signatureReading := FiniteModel.signature
  operationReading := FiniteModel.operationReading

/-- A concrete package witnessing that the mapped target fiber is inhabited. -/
noncomputable def refinementTargetPackage :
    AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem refinementTargetCoreReading

/-- The generated target package lies over the selected mapped point. -/
@[simp]
theorem refinementTargetPackage_point :
    packagePoint refinementTargetPackage = refinementTargetPoint :=
  rfl

/-- The target equation index is concretely inhabited; no empty-index trick is used. -/
theorem refinementTargetPackage_equationIndex_nonempty :
    Nonempty refinementTargetPackage.algebra.equationSystem.Index :=
  ⟨PUnit.unit⟩

/-- The mapped target package contains the newly admitted concrete Atom. -/
theorem refinementTargetPackage_componentC_mem :
    refinementTargetPackage.family.mem FiniteModel.FiniteAtom.componentC := by
  rw [refinementTargetPackage.family_mem_iff_extracts]
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Equal package points determine the same canonical extracted family. -/
theorem package_family_eq_of_point_eq {U : AtomCarrier.{u}}
    {P Q : AATCorePackage U} (hpoint : packagePoint P = packagePoint Q) :
    P.family = Q.family := by
  exact congrArg
    (fun X : ExtractionInstance U => X.doctrine.atomize X.source) hpoint

/-- Every package in the mapped target fiber contains the newly admitted Atom. -/
theorem componentC_mem_of_refinementTargetPoint
    (Q : AATCorePackage FiniteModel.carrier)
    (hpoint : packagePoint Q = refinementTargetPoint) :
    Q.family.mem FiniteModel.FiniteAtom.componentC := by
  have htarget : packagePoint Q = packagePoint refinementTargetPackage :=
    hpoint.trans refinementTargetPackage_point.symm
  have hfamily : Q.family = refinementTargetPackage.family :=
    package_family_eq_of_point_eq htarget
  rw [hfamily]
  exact refinementTargetPackage_componentC_mem

/-- The source direct image still excludes `componentC`. -/
theorem refinementSource_transport_componentC_not_mem :
    ¬ (refinementSourcePackage.family.transport
      finiteExtractionRefinement.atomMap).mem
        FiniteModel.FiniteAtom.componentC := by
  rintro ⟨sourceAtom, hsource, hmap⟩
  have hsourceAtom : sourceAtom = FiniteModel.FiniteAtom.componentC := by
    apply refinementAtomEquiv.injective
    change refinementAtomMap sourceAtom = FiniteModel.FiniteAtom.componentC at hmap
    change refinementAtomMap sourceAtom =
      refinementAtomMap FiniteModel.FiniteAtom.componentC
    rw [hmap, refinementAtomMap_componentC]
  apply FiniteModel.corePackage_componentC_not_mem
  simpa [refinementSourcePackage, hsourceAtom] using hsource

/--
No exact upper lift with the specified bijective Atom map reaches any package
over the mapped target point.

The contradiction uses only `SignedExactCoreReadingHom.extraction_eq`: the
target contains `componentC`, while the direct image of the source does not.
-/
theorem finiteExtractionRefinement_no_exact_upper_lift
    (Q : AATCorePackage FiniteModel.carrier)
    (hpoint : packagePoint Q = refinementTargetPoint) :
    ¬ ∃ F : SignedExactCoreReadingHom refinementSourcePackage Q,
      (F.atomEquiv : FiniteModel.carrier.Atom → FiniteModel.carrier.Atom) =
        finiteExtractionRefinement.atomMap := by
  rintro ⟨F, hatom⟩
  have htarget : Q.family.mem FiniteModel.FiniteAtom.componentC :=
    componentC_mem_of_refinementTargetPoint Q hpoint
  have htransport :
      (refinementSourcePackage.family.transport F.atomEquiv).mem
        FiniteModel.FiniteAtom.componentC := by
    rw [← F.extraction_eq]
    exact htarget
  have hfamily :
      refinementSourcePackage.family.transport F.atomEquiv =
        refinementSourcePackage.family.transport
          finiteExtractionRefinement.atomMap :=
    congrArg (fun atomMap => refinementSourcePackage.family.transport atomMap) hatom
  apply refinementSource_transport_componentC_not_mem
  rw [← hfamily]
  exact htransport

end AAT.AG.AtomFoundation

#assert_standard_axioms_only AAT.AG.AtomFoundation
