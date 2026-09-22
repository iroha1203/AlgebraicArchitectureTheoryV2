import ResearchLean.AG.CrossStageCoherence.GlobalVanishing

/-!
# Recovering the intermediate strong cocartesian qualification

Issue #4857 (Rising Sea F19) fixes the inputs of §4.9 at manuscript commit
`719f81f47d410701fd82c2bc88613cc140c59377`: an edge is strong for the composite
projection, and its image is strong for the core projection.  Its qualification
for the geometry projection is derived from these two universal properties.

## Implementation notes

The general cancellation theorem uses Mathlib's `IsStronglyCocartesian` directly.
The composite universal property produces the factor, and uniqueness for the
projected edge proves that this factor has the required intermediate image.
Assuming faithfulness of the lower projection would strengthen the manuscript's
premises and is unnecessary.

The constructors retain the existing `TwoLayerLiftData` and
`TwoLayerTransportData` APIs.  They preserve the supplied objects, edges,
parallel-path equation, and authored comparators, while deriving the missing
geometry qualification.  The projection, decomposition, and joint-vanishing
results therefore apply to the original manuscript inputs.
-/

namespace AAT.AG.CrossStageCoherence

universe u v u₁ u₂ u₃ v₁ v₂ v₃

open CategoryTheory
open AtomFoundation GeometryTransport TransportCoherence

/-- F19's missing qualification: composite strength and strength of the image
imply strength for the first projection.  Both hypotheses are precisely the
strong-lift assumptions preceding manuscript Proposition 4.31. -/
theorem stronglyCocartesian_of_comp_projection
    {E : Type u₁} {C : Type u₂} {B : Type u₃}
    [Category.{v₁} E] [Category.{v₂} C] [Category.{v₃} B]
    (p : E ⥤ C) (q : C ⥤ B) {a b : E} (f : a ⟶ b)
    [(p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map f) f]
    [q.IsStronglyCocartesian (q.map (p.map f)) (p.map f)] :
    p.IsStronglyCocartesian (p.map f) f := by
  constructor
  intro c g ψ hψ
  letI : p.IsHomLift (p.map f ≫ g) ψ := hψ
  have hψmap := IsHomLift.eq_of_isHomLift p (p.map f ≫ g) ψ
  letI : (p ⋙ q).IsHomLift ((p ⋙ q).map f ≫ q.map g) ψ := by
    have hmap : (p ⋙ q).map f ≫ q.map g = (p ⋙ q).map ψ := by
      change q.map (p.map f) ≫ q.map g = q.map (p.map ψ)
      rw [← q.map_comp, hψmap]
    rw [hmap]
    infer_instance
  obtain ⟨χ, hχ, hχuniq⟩ :=
    Functor.IsStronglyCocartesian.universal_property
      (p ⋙ q) ((p ⋙ q).map f) f (q.map g)
      ((p ⋙ q).map f ≫ q.map g) rfl ψ
  letI : (p ⋙ q).IsHomLift (q.map g) χ := hχ.1
  letI : q.IsHomLift (q.map g) (p.map χ) := by
    have hmap := IsHomLift.eq_of_isHomLift (p ⋙ q) (q.map g) χ
    change q.map g = q.map (p.map χ) at hmap
    rw [hmap]
    infer_instance
  have hpχ : p.map χ = g := by
    apply Functor.IsStronglyCocartesian.ext q
      (q.map (p.map f)) (p.map f) (q.map g)
    calc
      p.map f ≫ p.map χ = p.map ψ := by rw [← p.map_comp, hχ.2]
      _ = p.map f ≫ g := hψmap.symm
  have liftχ : p.IsHomLift g χ := by
    rw [← hpχ]
    infer_instance
  refine ⟨χ, ⟨liftχ, hχ.2⟩, ?_⟩
  intro χ' hχ'
  letI : p.IsHomLift g χ' := hχ'.1
  have hg := IsHomLift.eq_of_isHomLift p g χ'
  have liftχ' : (p ⋙ q).IsHomLift (q.map g) χ' := by
    have hmap : q.map g = (p ⋙ q).map χ' := congrArg q.map hg
    rw [hmap]
    infer_instance
  exact hχuniq χ' ⟨liftχ', hχ'.2⟩

/-- API equivalence for F19: once the projected edge is strong, intermediate
and composite qualifications are equivalent.  The forward implication is the
existing composition theorem. -/
theorem stronglyCocartesian_iff_comp_projection
    {E : Type u₁} {C : Type u₂} {B : Type u₃}
    [Category.{v₁} E] [Category.{v₂} C] [Category.{v₃} B]
    (p : E ⥤ C) (q : C ⥤ B) {a b : E} (f : a ⟶ b)
    [q.IsStronglyCocartesian (q.map (p.map f)) (p.map f)] :
    p.IsStronglyCocartesian (p.map f) f ↔
      (p ⋙ q).IsStronglyCocartesian ((p ⋙ q).map f) f := by
  constructor
  · intro hf
    letI := hf
    exact stronglyCocartesian_comp_projection p q f
  · intro hf
    letI := hf
    exact stronglyCocartesian_of_comp_projection p q f

/-- F19's qualification at the actual geometry/core projection tower.
The two assumptions are manuscript §4.9's `qp` and `q` qualifications. -/
theorem geometryHom_isStronglyCocartesian_of_composite
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (f : GeometryTotalHom G H)
    [(crossStageProjection U).IsStronglyCocartesian f.base.base f]
    [(packageProjection U).IsStronglyCocartesian f.base.base f.base] :
    (geometryProjection U).IsStronglyCocartesian f.base f := by
  letI : (geometryProjection U ⋙ packageProjection U).IsStronglyCocartesian
      ((geometryProjection U ⋙ packageProjection U).map f) f := by
    simpa only [crossStageProjection, Functor.comp_map, geometryProjection_map,
      packageProjection_map] using inferInstanceAs
        ((crossStageProjection U).IsStronglyCocartesian f.base.base f)
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map ((geometryProjection U).map f))
      ((geometryProjection U).map f) := by
    simpa only [geometryProjection_map, packageProjection_map] using inferInstanceAs
      ((packageProjection U).IsStronglyCocartesian f.base.base f.base)
  exact stronglyCocartesian_of_comp_projection
    (geometryProjection U) (packageProjection U) f

/-- The fixed-core clause of manuscript Theorem 4.34: a coherent coordinate
over the chosen core coordinate is exactly a coherent kernel gauge relative
to that section.  The section is the input of Definition 4.32; no coherence
or surjectivity of the full projection is assumed. -/
theorem sectionRelativeCoherentizable_iff_exists_coherent_lift
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) (edgeSection : EdgeSectionFamily data) :
    SectionRelativeCoherentizable data edgeSection ↔
      ∃ reselection : UpperEdgeReselection data.lift,
        pushforwardEdgeReselection data.lift reselection = edgeSection.core ∧
        CrossStageCoherentAt data reselection := by
  constructor
  · rintro ⟨gauge, coherent⟩
    refine ⟨relativeUpperReselection edgeSection gauge, ?_, coherent⟩
    funext i j edge
    exact relativeUpperReselection_projects edgeSection gauge i j edge
  · rintro ⟨reselection, projects, coherent⟩
    let other := edgeSectionOfUpperReselection data reselection
    have sameCore : edgeSection.core = other.core := projects.symm
    apply (sectionRelativeCoherentizable_replacement_iff edgeSection other sameCore).2
    refine ⟨1, ?_⟩
    intro cell
    simpa only [other, relativeUpperReselection_edgeSection_identity] using coherent cell

section ManuscriptInputs

variable {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (geometry : P.Vertex → GeometryPackage.{u, v} U)
    (edgeLift : {i j : P.Vertex} → P.Edge i j →
      GeometryTotalHom (geometry i) (geometry j))
    (edgeCompositeStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
      (crossStageProjection U).IsStronglyCocartesian
        (edgeLift edge).base.base (edgeLift edge))
    (edgeCoreStrong : ∀ {i j : P.Vertex} (edge : P.Edge i j),
      (packageProjection U).IsStronglyCocartesian
        (edgeLift edge).base.base (edgeLift edge).base)

/-- Construct the existing lift API from F19's original edge assumptions.
`edgeGeometryStrong` is generated by cancellation, rather than supplied.
Implementation notes: retaining the original record keeps its path and
reselection operations available without a second representation. -/
noncomputable def TwoLayerLiftData.ofCompositeStrong : TwoLayerLiftData P U where
  geometry := geometry
  edgeLift := edgeLift
  edgeGeometryStrong edge := by
    letI := edgeCompositeStrong edge
    letI := edgeCoreStrong edge
    exact geometryHom_isStronglyCocartesian_of_composite (edgeLift edge)
  edgeCoreStrong := edgeCoreStrong

/-- Constructor API: F19's qualification conversion preserves every object.
The simp direction exposes the original geometry. -/
@[simp] theorem TwoLayerLiftData.ofCompositeStrong_geometry (i : P.Vertex) :
    (ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).geometry i =
      geometry i := rfl

/-- Constructor API: F19's qualification conversion preserves every edge.
The simp direction exposes the original edge lift. -/
@[simp] theorem TwoLayerLiftData.ofCompositeStrong_edgeLift
    {i j : P.Vertex} (edge : P.Edge i j) :
    (ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).edgeLift edge =
      edgeLift edge := rfl

/-- Constructor API: the projected edge is the supplied edge's core image.
The simp direction exposes that original image. -/
@[simp] theorem TwoLayerLiftData.ofCompositeStrong_core_edgeLift
    {i j : P.Vertex} (edge : P.Edge i j) :
    (ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).coreLiftData.edgeLift
      edge = (edgeLift edge).base := rfl

/-- Assemble F19's comparison input after deriving the geometry qualification.
The path equality and authored comparator are exactly the data of §4.9;
alignment and any vanishing conclusion are not constructor inputs.
Implementation notes: this reuses the established comparison API so the
canonical comparison is still generated by its universal property. -/
noncomputable def TwoLayerTransportData.ofCompositeStrong
    (pathBaseEq : ∀ cell : P.TwoCell,
      ((TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).pathLift
         (P.twoLeft cell)).base.base =
      ((TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).pathLift
         (P.twoRight cell)).base.base)
    (comparator : (cell : P.TwoCell) → CompositeFiberAut (geometry (P.twoTarget cell))) :
    TwoLayerTransportData P U where
  lift := TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong
  twoCellBase := pathBaseEq
  comparator := comparator

variable
    (pathBaseEq : ∀ cell : P.TwoCell,
      ((TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).pathLift
         (P.twoLeft cell)).base.base =
      ((TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong).pathLift
         (P.twoRight cell)).base.base)
    (comparator : (cell : P.TwoCell) → CompositeFiberAut (geometry (P.twoTarget cell)))

/-- Constructor API: the transport data retain the derived lift data.
The simp direction exposes the independently qualified lift constructor. -/
@[simp] theorem TwoLayerTransportData.ofCompositeStrong_lift :
    (TwoLayerTransportData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong
      pathBaseEq comparator).lift =
      TwoLayerLiftData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong := rfl

/-- Constructor API: the authored comparison is unchanged by qualification.
The simp direction exposes the supplied comparison, not the canonical one. -/
@[simp] theorem TwoLayerTransportData.ofCompositeStrong_comparator (cell : P.TwoCell) :
    (TwoLayerTransportData.ofCompositeStrong geometry edgeLift edgeCompositeStrong edgeCoreStrong
      pathBaseEq comparator).comparator cell = comparator cell := rfl

end ManuscriptInputs

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
