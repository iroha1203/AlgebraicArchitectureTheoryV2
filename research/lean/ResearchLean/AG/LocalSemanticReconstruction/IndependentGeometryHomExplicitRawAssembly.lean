import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomRawPointLaws
import ResearchLean.AG.LocalSemanticReconstruction.IndependentRawCandidatePoints
import ResearchLean.AG.LocalSemanticReconstruction.IndependentExplicitRawReadings
import Formal.Util.AssertStandardAxioms

/-!
# Full explicit raw maps from common primitive point laws

Implementation notes: the native base and coefficient maps occur only in the
comparison API. Their graph identifications select the primitive active rows.
Coordinate and local-data equivalences are built from those rows; polynomial
and variable-image preservation follow from finite exponent/coefficient point
laws. The full restriction equation is derived from variables and constants,
so neither a complete raw map nor its global equality is an input field.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport LawAlgebra RealizationReconstruction

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}

/-- Comparison premises identify the independently reconstructed inverse context and directed coefficient maps. -/
structure Maps (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
    (h : Table.{u, v} U .explicit) : Prop where
  /-- Backward context points select the original inverse functor's object. -/
  context : ∀ (W : ArchCtx G.core.object) (V : ArchCtx H.core.object),
    contextPoints h W V = true ↔ ((coreContextInverse f).obj ⟨V⟩).ctx = W
  /-- Every directed coefficient edge is exactly a native map point. -/
  coefficient : ∀ x y, h (.coefficient (.edge G.Coefficient H.Coefficient x y)) = true ↔ a x = y

/-- Original primitive raw readings are used only to state the native comparison theorem. -/
abbrev NativePoints (G H : GeometryPackage.{u, v} U) (h : Table.{u, v} U .explicit) :=
  PointLaws (IndependentRawCandidate.read G.site G.Coefficient G.raw)
    (IndependentRawCandidate.read H.site H.Coefficient H.raw) h

variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (h : Table.{u, v} U .explicit) (hm : Maps f a h) (hp : NativePoints G H h)

/-- The primitive source context selected at one target context. -/
def inverse (V : ArchCtx H.core.object) : ArchCtx G.core.object := ((coreContextInverse f).obj ⟨V⟩).ctx

/-- Construct the complete coordinate equivalence from its active primitive inverse graph. -/
def coordinateEquiv (V : ArchCtx H.core.object) :
    (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord ≃ (H.raw.coordFamily ⟨V⟩).Coord :=
  IndependentInverseGraph.assemble _ _ (InverseRows.coordinate h _ _ (inverse f V) V)
    (hp.coordinateRows _ V ((hm.context _ V).2 rfl))

/-- Every forward coordinate point is precisely the independently constructed coordinate image. -/
theorem coordinate_forward_iff (V : ArchCtx H.core.object)
    (c : (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)).Coord) (d : (H.raw.coordFamily ⟨V⟩).Coord) :
    coordinatePoint h (inverse f V) V _ _ c d = true ↔ coordinateEquiv f a h hm hp V c = d :=
  (IndependentCarrierGraph.graph _ _ _ (hp.coordinateRows _ V ((hm.context _ V).2 rfl)).forward.2).edge_eq_true_iff_target_eq c d

/-- Construct the relation-generator equivalence from its own active primitive inverse graph. -/
def relationEquiv (V : ArchCtx H.core.object) :
    (G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).Relation ≃ (H.raw.relationFamily ⟨V⟩).Relation :=
  IndependentInverseGraph.assemble _ _ (InverseRows.relation h _ _ (inverse f V) V)
    (hp.relationRows _ V ((hm.context _ V).2 rfl))

/-- Every forward relation point is precisely its constructed generator image. -/
theorem relation_forward_iff (V : ArchCtx H.core.object)
    (i : (G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).Relation)
    (j : (H.raw.relationFamily ⟨V⟩).Relation) :
    relationPoint h (inverse f V) V _ _ i j = true ↔ relationEquiv f a h hm hp V i = j :=
  (IndependentCarrierGraph.graph _ _ _ (hp.relationRows _ V ((hm.context _ V).2 rfl)).forward.2).edge_eq_true_iff_target_eq i j

/-- Recover labels and every dependent local-data equivalence from the original raw response points. -/
def coordinateTransport (V : ArchCtx H.core.object) :
    CoordinateFamilyExactEquiv (G.raw.coordFamily ((coreContextInverse f).obj ⟨V⟩)) (H.raw.coordFamily ⟨V⟩) where
  coordinateEquiv := coordinateEquiv f a h hm hp V
  label_eq c := by
    have he := hp.label (inverse f V) V _ _ c (coordinateEquiv f a h hm hp V c)
      ((hm.context _ V).2 rfl) ((coordinate_forward_iff f a h hm hp V c _).2 rfl)
    exact (Option.some.inj
      ((IndependentRawCandidate.read_label G.site G.Coefficient G.raw (inverse f V) c).symm.trans
        (he.trans (IndependentRawCandidate.read_label H.site H.Coefficient H.raw V _)))).symm
  localDataEquiv c := IndependentInverseGraph.assemble _ _ (InverseRows.localData h _ _ (inverse f V) V _ _ c _)
    (hp.localDataRows (inverse f V) V _ _ c (coordinateEquiv f a h hm hp V c) _ _
      ((hm.context _ V).2 rfl) ((coordinate_forward_iff f a h hm hp V c _).2 rfl)
      (IndependentRawCandidate.read_localData G.site G.Coefficient G.raw (inverse f V) c)
      (IndependentRawCandidate.read_localData H.site H.Coefficient H.raw V _))

/-- Finite polynomial point comparisons derive the original whole relation-generator equation. -/
theorem polynomial_eq (V : ArchCtx H.core.object)
    (i : (G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).Relation) :
    MvPolynomial.rename (coordinateEquiv f a h hm hp V)
      (MvPolynomial.map a ((G.raw.relationFamily ((coreContextInverse f).obj ⟨V⟩)).polynomial i)) =
        (H.raw.relationFamily ⟨V⟩).polynomial (relationEquiv f a h hm hp V i) := by
  apply (IndependentPolynomialPointTransport.points_iff_rename_map _ a _ _
    (coordinate_forward_iff f a h hm hp V) hm.coefficient _ _).1
  exact hp.polynomial (inverse f V) V _ _ _ _ (IndependentRawCandidate.coefficientRef G.Coefficient)
    (IndependentRawCandidate.coefficientRef H.Coefficient) i (relationEquiv f a h hm hp V i) _ _
    ((hm.context _ V).2 rfl) ((relation_forward_iff f a h hm hp V i _).2 rfl)
    (IndependentRawCandidate.read_polynomial G.site G.Coefficient G.raw (inverse f V) i)
    (IndependentRawCandidate.read_polynomial H.site H.Coefficient H.raw V _)

/-- Finite sparse image comparisons derive native naturality at each variable. -/
theorem image_eq {V Y : H.site.category} (g : V ⟶ Y)
    (c : (G.raw.coordFamily ((coreContextInverse f).obj Y)).Coord) :
    MvPolynomial.rename (coordinateEquiv f a h hm hp V.ctx)
      (MvPolynomial.map a ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.variableImage c)) =
        (H.raw.restrictionStable g).restriction.variableImage (coordinateEquiv f a h hm hp Y.ctx c) := by
  apply (IndependentPolynomialPointTransport.points_iff_rename_map _ a _ _
    (coordinate_forward_iff f a h hm hp V.ctx) hm.coefficient _ _).1
  have hs : G.site.contextPreorder.le (inverse f V.ctx) (inverse f Y.ctx) := leOfHom ((coreContextInverse f).map g)
  have ht : H.site.contextPreorder.le V.ctx Y.ctx := leOfHom g
  exact hp.image (inverse f V.ctx) (inverse f Y.ctx) V.ctx Y.ctx _ _ _ _
    (IndependentRawCandidate.coefficientRef G.Coefficient) (IndependentRawCandidate.coefficientRef H.Coefficient)
    c (coordinateEquiv f a h hm hp Y.ctx c) _ _ ((hm.context _ _).2 rfl) ((hm.context _ _).2 rfl)
    ((coordinate_forward_iff f a h hm hp Y.ctx c _).2 rfl)
    (IndependentRawCandidate.read_image G.site G.Coefficient G.raw hs c)
    (IndependentRawCandidate.read_image H.site H.Coefficient H.raw ht _)

/-- Assemble the entire native raw map, deriving restriction preservation on all polynomials. -/
def assemble : RawAmbientRestrictionSystemExactMapAgainst G.site H.site (coreContextInverse f) a G.raw H.raw where
  coordinate V := coordinateTransport f a h hm hp V.ctx
  relation V := {
    relationEquiv := relationEquiv f a h hm hp V.ctx
    polynomial_eq i := by
      simpa [CoordinateFamilyExactEquiv.polynomialEquiv, StructuralRelationFamily.baseChange, coordinateTransport]
        using polynomial_eq f a h hm hp V.ctx i }
  restriction_polynomial {V Y} g p := by
    have he : ((coordinateTransport f a h hm hp V.ctx).polynomialHom a).comp
        (G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.polynomialMap =
      (H.raw.restrictionStable g).restriction.polynomialMap.comp
        ((coordinateTransport f a h hm hp Y.ctx).polynomialHom a) := by
      apply MvPolynomial.ringHom_ext
      · intro x
        simp only [RingHom.comp_apply]
        calc
          _ = (coordinateTransport f a h hm hp V.ctx).polynomialHom a (MvPolynomial.C x) :=
            congrArg _ ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.polynomialMap_C x)
          _ = MvPolynomial.C (a x) := (coordinateTransport f a h hm hp V.ctx).polynomialHom_C a x
          _ = (H.raw.restrictionStable g).restriction.polynomialMap (MvPolynomial.C (a x)) :=
            ((H.raw.restrictionStable g).restriction.polynomialMap_C (a x)).symm
          _ = _ := congrArg _ ((coordinateTransport f a h hm hp Y.ctx).polynomialHom_C a x).symm
      · intro c
        simp only [RingHom.comp_apply]
        calc
          _ = (coordinateTransport f a h hm hp V.ctx).polynomialHom a
              ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.variableImage c) :=
            congrArg _ ((G.raw.restrictionStable ((coreContextInverse f).map g)).restriction.polynomialMap_X c)
          _ = (H.raw.restrictionStable g).restriction.variableImage (coordinateEquiv f a h hm hp Y.ctx c) :=
            image_eq f a h hm hp g c
          _ = (H.raw.restrictionStable g).restriction.polynomialMap
              (MvPolynomial.X (coordinateEquiv f a h hm hp Y.ctx c)) :=
            ((H.raw.restrictionStable g).restriction.polynomialMap_X _).symm
          _ = _ := congrArg _ ((coordinateTransport f a h hm hp Y.ctx).polynomialHom_X a c).symm
    exact RingHom.congr_fun he p

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ExplicitRaw
