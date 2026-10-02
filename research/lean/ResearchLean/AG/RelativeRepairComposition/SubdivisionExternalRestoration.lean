import ResearchLean.AG.RelativeRepairComposition.SubdivisionSharedValues

/-!
# All strict external objects and their full compatible native arrows

Every independent external object is kept unchanged. The actual strict object
set before collapse is the old strict object set times the entire new-object
kernel. For morphisms between arbitrary new objects, the unique full native
lift keeps the entire external morphism and every shared vertex label. These
are actual object and arrow constructions before any generated coordinates.

## Implementation notes

Strict objects and compatible arrows are subtypes of independently supplied actual pairs. The complete external object and arrow are unchanged; the full new kernel coordinate is retained. An existence-only comparison would omit both inverse constructions and the shared-label conditions.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uJ uE uB uD vE vB vD uX vX
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen) (W : ClosedRegion K) (hw : chosen ∉ W.edges)
variable (fixed : Set (EdgeName (K := K))) (hchosen : chosen ∉ fixed)

/-- Every strict external object has exactly its old strict actual object and an arbitrary full first-factor correction. -/
noncomputable def externalObjectEquiv {X : Type uX} (boundary : X → SharedValues T W) :
    ContextRelations.StrictJoin
      (fun R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) =>
        sharedNew T chosen F W hw R.1) boundary ≃
      ContextRelations.StrictJoin
        (fun R : SupportedRepair T fixed => sharedOld T W R.1) boundary ×
      Additive (Kernel p q F.middle) where
  toFun R := (⟨(collapseSupported T chosen F fixed hchosen R.1.1,R.1.2),
    (shared_collapse T chosen F W hw R.1.1.1).trans R.2⟩,
    (originalTower T chosen F).solutionCorrection R.1.1.1 (firstEdgeName K chosen))
  invFun R := ⟨(expandSupported T chosen F fixed R.1.1.1 R.2,R.1.1.2),
    (shared_expand T chosen F W hw R.1.1.1.1 R.2).trans R.1.2⟩
  left_inv R := by
    apply Subtype.ext
    apply Prod.ext
    · exact expand_collapse_supported T chosen F fixed hchosen R.1.1
    · rfl
  right_inv R := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact collapse_expand_supported T chosen F fixed hchosen R.1.1.1 R.2
      · rfl
    · change (originalTower T chosen F).solutionCorrection
        (expandSolution T chosen F R.1.1.1.1 R.2) (firstEdgeName K chosen) = R.2
      rw [expandSolution_correction,expandCorrection_first]

/-- Strict external collapse retains exactly the same external object. -/
theorem external_object_value {X : Type uX} (boundary : X → SharedValues T W)
    (R : ContextRelations.StrictJoin
      (fun R : SupportedRepair (originalTower T chosen F) (oldEdgeSet K chosen fixed) =>
        sharedNew T chosen F W hw R.1) boundary) :
    (externalObjectEquiv T chosen F W hw fixed hchosen boundary R).1.1.2 = R.1.2 := rfl

section ExternalCategory
variable (vertices : Set K.Vertex)
variable {X : Type uX} [Category.{vX} X]
variable (externalLabel : ∀ {x y : X}, (x ⟶ y) →
  ∀ v : W.vertices, T.toTower.localCoefficients.A v.1)

/-- Collapse's full native inverse restores each old original vertex label. -/
theorem hom_inverse_old
    (R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (f : (collapseFunctor T chosen F vertices fixed hchosen).obj R ⟶
      (collapseFunctor T chosen F vertices fixed hchosen).obj Q) (v : K.Vertex) :
    (Multiplicative.toAdd ((collapseHomEquiv T chosen F vertices fixed hchosen R Q).symm f).1).1
      (.inl v) = (Multiplicative.toAdd f.1).1 v := rfl

/-- Full compatible native arrows to every external category are bijective under collapse, keeping that external arrow literally. -/
noncomputable def externalHomEquiv
    (R Q : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (x y : X) :
    {f : (R ⟶ Q) × (x ⟶ y) // ∀ v : W.vertices,
      (Multiplicative.toAdd f.1.1).1 (.inl v.1) = externalLabel f.2 v} ≃
    {f : ((collapseFunctor T chosen F vertices fixed hchosen).obj R ⟶
      (collapseFunctor T chosen F vertices fixed hchosen).obj Q) × (x ⟶ y) // ∀ v : W.vertices,
      (Multiplicative.toAdd f.1.1).1 v.1 = externalLabel f.2 v} where
  toFun f := ⟨(collapseHomEquiv T chosen F vertices fixed hchosen R Q f.1.1,f.1.2),f.2⟩
  invFun f := ⟨((collapseHomEquiv T chosen F vertices fixed hchosen R Q).symm f.1.1,f.1.2),by
    intro v
    rw [hom_inverse_old]
    exact f.2 v⟩
  left_inv f := by
    apply Subtype.ext
    exact Prod.ext ((collapseHomEquiv T chosen F vertices fixed hchosen R Q).symm_apply_apply f.1.1) rfl
  right_inv f := by
    apply Subtype.ext
    exact Prod.ext ((collapseHomEquiv T chosen F vertices fixed hchosen R Q).apply_symm_apply f.1.1) rfl

/-- Collapse of the entire paired actual arrows commutes with composition and leaves the external composite unchanged. -/
theorem external_arrow_composition
    {R Q U : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed)}
    {x y z : X} (f : R ⟶ Q) (g : Q ⟶ U) (a : x ⟶ y) (b : y ⟶ z) :
    ((collapseFunctor T chosen F vertices fixed hchosen).map (f ≫ g),a ≫ b) =
      ((collapseFunctor T chosen F vertices fixed hchosen).map f ≫
        (collapseFunctor T chosen F vertices fixed hchosen).map g,a ≫ b) :=
  Prod.ext ((collapseFunctor T chosen F vertices fixed hchosen).map_comp f g) rfl

/-- Collapse of paired actual identity arrows retains the external identity. -/
theorem external_arrow_identity
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (x : X) :
    ((collapseFunctor T chosen F vertices fixed hchosen).map (𝟙 R),𝟙 x) =
      (𝟙 ((collapseFunctor T chosen F vertices fixed hchosen).obj R),𝟙 x) :=
  Prod.ext ((collapseFunctor T chosen F vertices fixed hchosen).map_id R) rfl

/-- The actual counit pairs with every external identity, and satisfies the strict full shared-label condition. -/
theorem external_counit_shared
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (x : X) (hid : ∀ v : W.vertices, externalLabel (𝟙 x) v = 0) :
    ∀ v : W.vertices,
      (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).counitIso.hom.app R).1).1
        (.inl v.1) = externalLabel (𝟙 x) v := by
  intro v
  rw [shared_counit_label T chosen F W vertices fixed hchosen R v,hid v]

end ExternalCategory
variable (vertices : Set K.Vertex)

/-- On every original actual external repair groupoid, the full identity label reads zero in every shared kernel. -/
theorem native_external_identity_zero {J : FiniteTransportPresentation.{uJ}}
    (Tenv : OriginalTowerPresentation J p q) (envVertices : Set J.Vertex)
    (envFixed : Set (EdgeName (K := J)))
    (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ T.toTower.localCoefficients.A v.1)
    (x : RepairGroupoid Tenv envVertices envFixed) (v : W.vertices) :
    readKernel v ((Multiplicative.toAdd (𝟙 x : x ⟶ x).1).1 (readVertex v)) = 0 :=
  map_zero (readKernel v)

/-- The actual subdivision counit agrees strictly with the unchanged actual external identity for every full native external repair. -/
theorem native_external_counit_shared {J : FiniteTransportPresentation.{uJ}}
    (Tenv : OriginalTowerPresentation J p q) (envVertices : Set J.Vertex)
    (envFixed : Set (EdgeName (K := J)))
    (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ T.toTower.localCoefficients.A v.1)
    (R : RepairGroupoid (originalTower T chosen F) (Sum.inl '' vertices) (oldEdgeSet K chosen fixed))
    (x : RepairGroupoid Tenv envVertices envFixed) (v : W.vertices) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).counitIso.hom.app R).1).1
      (.inl v.1) = readKernel v ((Multiplicative.toAdd (𝟙 x : x ⟶ x).1).1 (readVertex v)) := by
  rw [shared_counit_label T chosen F W vertices fixed hchosen R v,
    native_external_identity_zero T W Tenv envVertices envFixed readVertex readKernel x v]

/-- The actual subdivision unit also agrees strictly with each unchanged full native external identity. -/
theorem native_external_unit_shared {J : FiniteTransportPresentation.{uJ}}
    (Tenv : OriginalTowerPresentation J p q) (envVertices : Set J.Vertex)
    (envFixed : Set (EdgeName (K := J)))
    (readVertex : W.vertices → J.Vertex)
    (readKernel : ∀ v : W.vertices,
      Tenv.toTower.localCoefficients.A (readVertex v) →+ T.toTower.localCoefficients.A v.1)
    (R : RepairGroupoid T vertices fixed) (x : RepairGroupoid Tenv envVertices envFixed)
    (v : W.vertices) :
    (Multiplicative.toAdd ((equivalence T chosen F vertices fixed hchosen).unitIso.hom.app R).1).1 v.1 =
      readKernel v ((Multiplicative.toAdd (𝟙 x : x ⟶ x).1).1 (readVertex v)) := by
  change (Multiplicative.toAdd ((unitIso T chosen F vertices fixed hchosen).hom.app R).1).1 v.1 = _
  rw [unitIso_label T chosen F vertices fixed hchosen R,
    native_external_identity_zero T W Tenv envVertices envFixed readVertex readKernel x v]
  rfl

end AAT.AG.RelativeRepairComposition.Subdivision
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision
