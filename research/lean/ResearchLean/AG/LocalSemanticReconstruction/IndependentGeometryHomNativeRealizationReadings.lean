import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRecovery
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRealizationNative
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitRealizationNative
import Formal.Util.AssertStandardAxioms

/-!
# Native realization on the common Hom reader

Every fiber and actual-action comparison required by the native realization
converses follows from the common reader's realization projection. Directed
representative maps and explicit equivalences retain their original meanings.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

section Representative

variable (raw : RawQuery G.core.object H.core.object .representative → Bool)
variable (R : RealizationTransportSupply G.core H.core f)

/-- Context and Atom rows of the common reader are the original representative transport maps. -/
theorem readWith_representativeRealization_maps : RepresentativeRealization.Maps f
    (readWith .representative f a raw (representativeRealizationRead f R)) where
  context := readWith_context_point_iff .representative f a raw (representativeRealizationRead f R)
  atom := readWith_atom_point_iff .representative f a raw (representativeRealizationRead f R)

/-- All representative support candidates retain the original directed component graph. -/
theorem readWith_representativeSupport : RepresentativeRealization.support
    (readWith .representative f a raw (representativeRealizationRead f R)) =
      IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f) (fun W => R.supportComp ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .representative f a raw (representativeRealizationRead f R) (.representativeSupport W V x y)

/-- All representative axis candidates retain the original directed component graph. -/
theorem readWith_representativeAxis : RepresentativeRealization.axis
    (readWith .representative f a raw (representativeRealizationRead f R)) =
      IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f) (fun W => R.axisComp ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .representative f a raw (representativeRealizationRead f R) (.representativeAxis W V x y)

/-- All representative observable candidates retain the original directed component graph. -/
theorem readWith_representativeObservable : RepresentativeRealization.observable
    (readWith .representative f a raw (representativeRealizationRead f R)) =
      IndependentFixedIndexedPointGraph.read (RepresentativeRealization.forward f) (fun W => R.observableComp ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .representative f a raw (representativeRealizationRead f R) (.representativeObservable W V x y)

/-- The original directed supply gives every primitive realization law on this common reader. -/
theorem readWith_representativeRealization_points : RepresentativeRealization.NativePoints G.core H.core
    (readWith .representative f a raw (representativeRealizationRead f R)) :=
  RepresentativeRealization.points_of_native f _ (readWith_representativeRealization_maps f a raw R) R
    (readWith_representativeSupport f a raw R) (readWith_representativeAxis f a raw R)
    (readWith_representativeObservable f a raw R)

/-- Reassembly of the common representative reading restores every native directed realization component. -/
theorem readWith_representativeRealization_assemble : RepresentativeRealization.assemble f
    (readWith .representative f a raw (representativeRealizationRead f R))
    (readWith_representativeRealization_maps f a raw R) (readWith_representativeRealization_points f a raw R) = R :=
  RepresentativeRealization.assemble_points_of_native f _ (readWith_representativeRealization_maps f a raw R) R
    (readWith_representativeSupport f a raw R) (readWith_representativeAxis f a raw R)
    (readWith_representativeObservable f a raw R)

end Representative

section Explicit

variable (raw : RawQuery G.core.object H.core.object .explicit → Bool)
variable (R : ExplicitRealizationTransportSupply G.core H.core f)

/-- Context and Atom rows of the common reader are the original explicit transport maps. -/
theorem readWith_explicitRealization_maps : ExplicitRealization.Maps f
    (readWith .explicit f a raw (explicitRealizationRead f R)) where
  context := readWith_context_point_iff .explicit f a raw (explicitRealizationRead f R)
  atom := readWith_atom_point_iff .explicit f a raw (explicitRealizationRead f R)

/-- Both tags of every explicit support fiber retain the original equivalence graph. -/
theorem readWith_explicitSupport (d : Direction) : ExplicitRealization.support
    (readWith .explicit f a raw (explicitRealizationRead f R)) d =
      IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f) (fun W => R.supportEquiv ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.explicitSupport d W V x y)

/-- Both tags of every explicit axis fiber retain the original equivalence graph. -/
theorem readWith_explicitAxis (d : Direction) : ExplicitRealization.axis
    (readWith .explicit f a raw (explicitRealizationRead f R)) d =
      IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f) (fun W => R.axisEquiv ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.explicitAxis d W V x y)

/-- Both tags of every explicit observable fiber retain the original equivalence graph. -/
theorem readWith_explicitObservable (d : Direction) : ExplicitRealization.observable
    (readWith .explicit f a raw (explicitRealizationRead f R)) d =
      IndependentFixedIndexedPointGraph.read (ExplicitRealization.forward f) (fun W => R.observableEquiv ⟨W⟩) := by
  funext W V x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.explicitObservable d W V x y)

/-- Every actual support action retains the original context-morphism reading. -/
theorem readWith_actualSupport : ExplicitRealization.actualSupport (A := G.core.object) (B := H.core.object)
    (readWith .explicit f a raw (explicitRealizationRead f R)) = ExplicitRealization.readActualSupport f R := by
  funext W X V Y g x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.actualSupport W X V Y g x y)

/-- Every actual axis action retains the original context-morphism reading. -/
theorem readWith_actualAxis : ExplicitRealization.actualAxis (A := G.core.object) (B := H.core.object)
    (readWith .explicit f a raw (explicitRealizationRead f R)) = ExplicitRealization.readActualAxis f R := by
  funext W X V Y g x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.actualAxis W X V Y g x y)

/-- Every actual observable restriction retains its original contravariant reading. -/
theorem readWith_actualObservable : ExplicitRealization.actualObservable (A := G.core.object) (B := H.core.object)
    (readWith .explicit f a raw (explicitRealizationRead f R)) = ExplicitRealization.readActualObservable f R := by
  funext W X V Y g x y
  exact readWith_realization .explicit f a raw (explicitRealizationRead f R) (.actualObservable W X V Y g x y)

/-- The original explicit supply gives all inverse, reading, and actual-action laws on this reader. -/
theorem readWith_explicitRealization_points : ExplicitRealization.PointLaws G.core.object H.core.object
    (readWith .explicit f a raw (explicitRealizationRead f R)) :=
  ExplicitRealization.points_of_native f _ (readWith_explicitRealization_maps f a raw R) R
    (readWith_explicitSupport f a raw R) (readWith_explicitAxis f a raw R) (readWith_explicitObservable f a raw R)
    (readWith_actualSupport f a raw R) (readWith_actualAxis f a raw R) (readWith_actualObservable f a raw R)

/-- Reassembly restores the whole explicit supply, including the actual context-morphism action. -/
theorem readWith_explicitRealization_assemble : ExplicitRealization.assemble f
    (readWith .explicit f a raw (explicitRealizationRead f R))
    (readWith_explicitRealization_maps f a raw R) (readWith_explicitRealization_points f a raw R) = R :=
  ExplicitRealization.assemble_eq_native f _ (readWith_explicitRealization_maps f a raw R) R
    (readWith_explicitSupport f a raw R) (readWith_explicitAxis f a raw R) (readWith_explicitObservable f a raw R) _

end Explicit

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
