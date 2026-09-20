import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRawPreservation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRealizationPreservation
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeFullAssembly
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomExplicitFullAssembly
import ResearchLean.AG.RealizationReconstruction.CSAATExplicitExactGeometryCategory
import Formal.Util.AssertStandardAxioms

/-!
# Native recovery of both complete geometry Hom meanings

Every original Hom supplies all primitive laws on its actual common local
quotient. Reassembly restores every native computational field. The converse
recovery of an arbitrary lawful local quotient is a separate obligation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport RealizationReconstruction IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}}

/-- Base, coefficient, and whole directed realization equality determine the original representative Hom. -/
theorem representativeHom_ext {G H : GeometryPackage.{u, v} U} {F T : GeometryTotalHom G H}
    (hb : F.base = T.base) (hc : F.geometry.coefficientHom = T.geometry.coefficientHom)
    (hr : HEq (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry)
      (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry T.geometry)) : F = T := by
  rcases F with ⟨f, g⟩
  rcases T with ⟨f', g'⟩
  dsimp only at hb hc hr
  cases hb
  have he := eq_of_heq hr
  have hg : g = g' := by
    apply GeomReadHom.ext hc
    · exact heq_of_eq (congrArg (fun R => R.supportComp) he)
    · exact heq_of_eq (congrArg (fun R => R.axisComp) he)
    · exact heq_of_eq (congrArg (fun R => R.observableComp) he)
  cases hg
  rfl

variable (s t : ObjectData.{u, v} U)

/-- The common quotient of every native representative Hom satisfies all full primitive point laws. -/
theorem localRepresentative_points (F : GeometryTotalHom (assemble s) (assemble t)) :
    FullRepresentative.PointLaws s t (localRepresentative F) where
  inactiveObjects := readWith_inactive .representative F.base F.geometry.coefficientHom _ _
  package := localRepresentative_package s t F
  coverage := localWith_coverage s t .representative F.base F.geometry.coefficientHom _ _ F.geometry.coverage
  overlap := localWith_overlap s t .representative F.base F.geometry.coefficientHom _ _ F.geometry.overlap
  coefficient := localWith_coefficient s t .representative F.base F.geometry.coefficientHom _ _
  raw := localWith_representativeRaw s t F.base F.geometry.coefficientHom _ _ F.geometry.raw_eq
  realization := localWith_representativeRealization s t F.base F.geometry.coefficientHom _
    (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry)

/-- The common quotient of every native explicit Hom satisfies every full primitive point law. -/
theorem localExplicit_points (F : ExplicitExactGeometryHom (assemble s) (assemble t)) :
    FullExplicit.PointLaws s t (localExplicit F) where
  inactiveObjects := readWith_inactive .explicit F.base F.coefficientHom _ _
  package := localExplicit_package s t F
  coverage := localWith_coverage s t .explicit F.base F.coefficientHom _ _ F.coverage
  overlap := localWith_overlap s t .explicit F.base F.coefficientHom _ _ F.overlap
  coefficient := localWith_coefficient s t .explicit F.base F.coefficientHom _ _
  raw := localWith_explicitRaw s t F.base F.coefficientHom F.raw (explicitRealizationRead F.base F.realization)
  realization := localWith_explicitRealization s t F.base F.coefficientHom _ F.realization

/-- Full representative assembly restores the whole original Hom, with its directed realization and original coefficient map. -/
theorem localRepresentative_assemble (F : GeometryTotalHom (assemble s) (assemble t)) :
    FullRepresentative.assembleHom s t (localRepresentative F) (localRepresentative_points s t F) = F := by
  apply representativeHom_ext
  · exact localRepresentative_package_assemble s t F
  · exact localWith_coefficient_assemble s t .representative F.base F.geometry.coefficientHom _ _
  · exact localWith_representativeRealization_assemble_heq s t F.base F.geometry.coefficientHom _
      (CompleteGeometryGraphAssembly.realizationSupplyOfGeometry F.geometry)

/-- Full explicit assembly restores the whole original Hom, including typed raw data and every actual context action. -/
theorem localExplicit_assemble (F : ExplicitExactGeometryHom (assemble s) (assemble t)) :
    FullExplicit.assembleHom s t (localExplicit F) (localExplicit_points s t F) = F := by
  apply ExplicitExactGeometryHom.ext
  · exact localExplicit_package_assemble s t F
  · exact localWith_coefficient_assemble s t .explicit F.base F.coefficientHom _ _
  · exact localWith_explicitRaw_assemble_heq s t F.base F.coefficientHom F.raw
      (explicitRealizationRead F.base F.realization)
  · exact localWith_explicitRealization_assemble_heq s t F.base F.coefficientHom _ F.realization

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
