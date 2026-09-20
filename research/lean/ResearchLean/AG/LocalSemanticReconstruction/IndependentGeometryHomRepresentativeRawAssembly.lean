import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRepresentativeRawLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRepresentativeRawResponses
import Formal.Util.AssertStandardAxioms

/-!
# Exact representative raw equality from primitive point laws

Implementation notes: the strict raw equality is derived by comparing all
original candidate responses. Polynomial and image cases use coefficient
points and presence flags. The converse recovers every primitive law from
the original native equality, so the representative Hom meaning is retained
exactly. Native base and coefficient maps are only comparison parameters.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra IndependentRepresentativeHom

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}

/-- Comparison premises identify only inverse context points and directed coefficient points. -/
structure Maps (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
    (h : Table.{u, v} U .representative) : Prop where
  /-- Inverse context graph points select exactly the native inverse image. -/
  context : ∀ (W : ArchCtx G.core.object) (V : ArchCtx H.core.object),
    contextPoints h W V = true ↔ ((coreContextInverse f).obj ⟨V⟩).ctx = W
  /-- Coefficient graph points identify the original directed coefficient map. -/
  coefficient : ∀ x y, h (.coefficient (.edge G.Coefficient H.Coefficient x y)) = true ↔ a x = y

/-- The native comparison uses the original primitive raw, context, and coefficient-reference readings. -/
abbrev NativePoints (G H : GeometryPackage.{u, v} U) (h : Table.{u, v} U .representative) :=
  PointLaws (IndependentRawCandidate.read G.site G.Coefficient G.raw)
    (IndependentRawCandidate.read H.site H.Coefficient H.raw)
    (IndependentContextPrimitive.read H.core.contextPreorder)
    (IndependentRawCandidate.coefficientRef G.Coefficient) (IndependentRawCandidate.coefficientRef H.Coefficient) h

variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (h : Table.{u, v} U .representative) (hm : Maps f a h)

include hm in
/-- Derive the original strict raw equality from primitive carrier, presence, and coefficient point laws. -/
theorem assemble (hp : NativePoints G H h) : H.raw = rawTransport f a := by
  apply (raw_eq_iff_points f a).2
  intro q
  cases q with
  | coordinate V =>
    apply ULift.ext
    exact (hp.coordinate _ V.ctx ((hm.context _ _).2 rfl)).symm
  | relation V =>
    apply ULift.ext
    exact (hp.relation _ V.ctx ((hm.context _ _).2 rfl)).symm
  | label V C c =>
    apply ULift.ext
    exact (hp.label _ V.ctx C c ((hm.context _ _).2 rfl)).symm
  | localData V C c =>
    apply ULift.ext
    exact (hp.localData _ V.ctx C c ((hm.context _ _).2 rfl)).symm
  | polynomial V C I i =>
    apply ULift.ext
    have he := (IndependentPolynomialCoefficientPoints.optional_points_iff_map a _ hm.coefficient _ _).1
      (hp.polynomial _ V.ctx C I i ((hm.context _ _).2 rfl))
    exact (polynomial_candidate_read H.site H.Coefficient H.raw V.ctx C I i).symm.trans
      (he.trans (transport_polynomial_from_candidate f a V C I i).symm)
  | @image V Y g C D d =>
    apply ULift.ext
    have ht : (IndependentContextPrimitive.read H.core.contextPreorder (.le V.ctx Y.ctx)).down := leOfHom g
    have he := (IndependentPolynomialCoefficientPoints.optional_points_iff_map a _ hm.coefficient _ _).1
      (hp.image _ _ V.ctx Y.ctx C D d ((hm.context _ _).2 rfl) ((hm.context _ _).2 rfl) ht)
    exact (image_candidate_read H.site H.Coefficient H.raw g C D d).symm.trans
      (he.trans (transport_image_from_candidate f a g C D d).symm)

include hm in
/-- The original native raw equality supplies every representative primitive preservation rule. -/
theorem points_of_native (hr : H.raw = rawTransport f a) : NativePoints G H h := by
  have hp := (raw_eq_iff_points f a).1 hr
  constructor
  · intro W V hWV
    obtain rfl := (hm.context W V).1 hWV
    exact (congrArg ULift.down (hp (.coordinate ⟨V⟩))).symm
  · intro W V hWV
    obtain rfl := (hm.context W V).1 hWV
    exact (congrArg ULift.down (hp (.relation ⟨V⟩))).symm
  · intro W V C c hWV
    obtain rfl := (hm.context W V).1 hWV
    exact (congrArg ULift.down (hp (.label ⟨V⟩ C c))).symm
  · intro W V C c hWV
    obtain rfl := (hm.context W V).1 hWV
    exact (congrArg ULift.down (hp (.localData ⟨V⟩ C c))).symm
  · intro W V C I i hWV
    obtain rfl := (hm.context W V).1 hWV
    apply (IndependentPolynomialCoefficientPoints.optional_points_iff_map a _ hm.coefficient _ _).2
    exact (polynomial_candidate_read H.site H.Coefficient H.raw V C I i).trans
      ((congrArg ULift.down (hp (.polynomial ⟨V⟩ C I i))).trans
        (transport_polynomial_from_candidate f a ⟨V⟩ C I i))
  · intro W X V Y C D d hWV hXY ht
    obtain rfl := (hm.context W V).1 hWV
    obtain rfl := (hm.context X Y).1 hXY
    have hVY : H.site.contextPreorder.le V Y := ht
    let g : (⟨V⟩ : H.site.category) ⟶ ⟨Y⟩ := homOfLE hVY
    apply (IndependentPolynomialCoefficientPoints.optional_points_iff_map a _ hm.coefficient _ _).2
    exact (image_candidate_read H.site H.Coefficient H.raw g C D d).trans
      ((congrArg ULift.down (hp (.image g C D d))).trans (transport_image_from_candidate f a g C D d))

include hm in
/-- The independently stated representative raw laws have precisely the original native strict-equality meaning. -/
theorem points_iff_native : NativePoints G H h ↔ H.raw = rawTransport f a :=
  ⟨assemble f a h hm, points_of_native f a h hm⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.RepresentativeRaw
