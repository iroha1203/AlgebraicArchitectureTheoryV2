import ResearchLean.AG.RelativeRepairComposition.RangeMaps
import ResearchLean.AG.AbelianLiftingObstruction.ReferenceLiftInvariant

/-!
# Reference change with the original physical anchor

G-130 A / n1017 §2.2・2.5: actual repairs for a new lift of the same core retain
the original physical fixed arrows. Their new coordinates are h'=h-a, and their
fixed values are -a. Independent shifted equations reconstruct all actual
repairs. Native groupoid and orbit equivalences retain every original label.

## Implementation notes

The new defect itself need not vanish on the fixed region. Its anchored affine
term is added before forming the relative obstruction. The original full-kernel
coefficients are unchanged by the reference lift, so the tangent complex and
its support conditions use the same actual transports. The native action is
transported through the actual repair bijection and proved equal to the actual
new-reference vertex gauge; arbitrary original labels between anchored repairs
are recovered, rather than restricting the morphisms by definition alone.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace ActualRelative
variable (T : OriginalTowerPresentation K p q)
variable (other : ∀ {i j : K.Vertex} (_ : K.Edge i j), FiberAut (p ⋙ q) (T.original.object j))
variable (hother : ∀ {i j : K.Vertex} (e : K.Edge i j),
  fiberPushforward p q (T.original.object j) (other e) = T.core e)

/-- G-130 A: Derive the affine coordinate shift from actual lift differences in the full kernel. -/
theorem solution_correction_change_reference (R : Solution T) :
    (T.withAlternativeLift other hother).solutionCorrection
      (T.solutionChangeReference other hother R) =
    T.solutionCorrection R - T.alternativeCorrection other hother := by
  funext e
  rcases e with ⟨i,j,e⟩
  apply Additive.toMul.injective
  apply kernelInclusion_injective p q _
  change R.choice e * (other e)⁻¹ =
    (R.choice e * (T.lift e)⁻¹) * (other e * (T.lift e)⁻¹)⁻¹
  simp only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]

local notation "a" => T.alternativeCorrection other hother

/-- Each actual edge choice is retained when the coordinate reference changes. -/
theorem reference_solution_choice (R : Solution T) {i j : K.Vertex} (e : K.Edge i j) :
    (T.solutionChangeReference other hother R).choice e = R.choice e := rfl

/-- Actual repairs for the new reference, anchored to the old physical arrows. -/
def AnchoredRepair (fixed : Set (EdgeName (K := K))) :=
  {R : Solution (T.withAlternativeLift other hother) // ∀ e ∈ fixed,
    (selectedUpper K p q T.original R.choice).edgeLift e.2.2 =
      T.toTower.upper.edgeLift e.2.2}

/-- The actual repair bijection retains all original edge choices. -/
noncomputable def referenceRepairEquiv (fixed : Set (EdgeName (K := K))) :
    SupportedRepair T fixed ≃ AnchoredRepair T other hother fixed where
  toFun R := ⟨T.solutionChangeReference other hother R.1, R.2⟩
  invFun R := ⟨(T.solutionChangeReference other hother).symm R.1, R.2⟩
  left_inv R := Subtype.ext ((T.solutionChangeReference other hother).symm_apply_apply R.1)
  right_inv R := Subtype.ext ((T.solutionChangeReference other hother).apply_symm_apply R.1)

/-- G-130 A: Forward choice API of the actual physically anchored reference equivalence. -/
theorem reference_repair_equiv_choice (fixed : Set (EdgeName (K := K)))
    (R : SupportedRepair T fixed) {i j : K.Vertex} (e : K.Edge i j) :
    (referenceRepairEquiv T other hother fixed R).1.choice e = R.1.choice e := rfl

/-- G-130 A: Inverse choice API recovering every original actual repair choice. -/
theorem reference_repair_equiv_symm_choice (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) {i j : K.Vertex} (e : K.Edge i j) :
    ((referenceRepairEquiv T other hother fixed).symm R).1.choice e = R.1.choice e := rfl

/-- A fixed physical arrow has the transported coordinate h'=-a. -/
theorem anchored_correction_iff_edge
    (R : Solution (T.withAlternativeLift other hother)) {i j : K.Vertex} (e : K.Edge i j) :
    (T.withAlternativeLift other hother).solutionCorrection R ⟨i,j,e⟩ = -a ⟨i,j,e⟩ ↔
    (selectedUpper K p q T.original R.choice).edgeLift e = T.toTower.upper.edgeLift e := by
  let Q := (T.solutionChangeReference other hother).symm R
  have hQ := (T.solutionChangeReference other hother).apply_symm_apply R
  rw [← hQ, solution_correction_change_reference]
  change T.solutionCorrection Q ⟨i,j,e⟩ - a ⟨i,j,e⟩ = -a ⟨i,j,e⟩ ↔ _
  rw [sub_eq_iff_eq_add, neg_add_cancel]
  exact solution_correction_zero_iff_edge T Q e

/-- The new-reference equation with its transported physical boundary values. -/
def AnchoredCorrection (fixed : Set (EdgeName (K := K))) :=
  {h : C1 (T.withAlternativeLift other hother).toTower.localCoefficients // (∀ e ∈ fixed, h e = -a e) ∧
    d1 (T.withAlternativeLift other hother).toTower.localCoefficients h = -(T.withAlternativeLift other hother).toTower.defect}

/-- G-130 A: Construct shifted coordinates from each independent physically anchored actual solution. -/
noncomputable def anchoredCoord (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) : AnchoredCorrection T other hother fixed :=
  ⟨(T.withAlternativeLift other hother).solutionCorrection R.1,
    ⟨fun e he => (anchored_correction_iff_edge T other hother R.1 e.2.2).mpr (R.2 e he),
      (T.withAlternativeLift other hother).solutionCorrection_d1 R.1⟩⟩

/-- G-130 A: Reconstruct all actual edge choices from the independent shifted equation. -/
noncomputable def anchoredRec (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) : AnchoredRepair T other hother fixed :=
  ⟨(T.withAlternativeLift other hother).solutionOfCorrection h.1 h.2.2, by
    intro e he
    apply (anchored_correction_iff_edge T other hother _ e.2.2).mp
    rw [(T.withAlternativeLift other hother).solutionCorrection_solutionOfCorrection]
    exact h.2.1 e he⟩

/-- G-130 A: Left-inverse API for the anchored actual repair and coordinate constructions. -/
theorem anchored_rec_coord (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) :
    anchoredRec T other hother fixed (anchoredCoord T other hother fixed R) = R := by
  apply Subtype.ext
  exact (T.withAlternativeLift other hother).solutionOfCorrection_solutionCorrection R.1

/-- G-130 A: Right-inverse API for every independent shifted correction solution. -/
theorem anchored_coord_rec (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    anchoredCoord T other hother fixed (anchoredRec T other hother fixed h) = h := by
  apply Subtype.ext
  exact (T.withAlternativeLift other hother).solutionCorrection_solutionOfCorrection h.1 h.2.2

/-- G-130 A: Package the proved actual repair/shifted-equation inverses into an equivalence. -/
noncomputable def anchoredEquiv (fixed : Set (EdgeName (K := K))) :
    AnchoredRepair T other hother fixed ≃ AnchoredCorrection T other hother fixed where
  toFun := anchoredCoord T other hother fixed
  invFun := anchoredRec T other hother fixed
  left_inv := anchored_rec_coord T other hother fixed
  right_inv := anchored_coord_rec T other hother fixed

/-- G-130 A: Coordinate API expressing the shift of the same physically anchored actual repair. -/
theorem anchored_coord_reference (fixed : Set (EdgeName (K := K))) (R : SupportedRepair T fixed) :
    (anchoredCoord T other hother fixed (referenceRepairEquiv T other hother fixed R)).1 =
      (repairCoord T fixed R).1.1 - a := by
  exact solution_correction_change_reference T other hother R.1


/-- The transferred action is the same actual new-reference vertex gauge. -/
noncomputable def anchoredGauge (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    AnchoredRepair T other hother fixed :=
  referenceRepairEquiv T other hother fixed
    (repairGauge T vertices fixed b ((referenceRepairEquiv T other hother fixed).symm R))

/-- G-130 A: Connect the transported labeled action to the actual new-reference vertex gauge. -/
theorem anchored_gauge_solution (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    (anchoredGauge T other hother vertices fixed b R).1 =
      (T.withAlternativeLift other hother).vertexGauge b.1 R.1 := by
  change T.solutionChangeReference other hother (T.vertexGauge b.1 _) = _
  rw [T.vertexGauge_changeReference]
  change (T.withAlternativeLift other hother).vertexGauge b.1
    ((T.solutionChangeReference other hother) ((T.solutionChangeReference other hother).symm R.1)) = _
  rw [Equiv.apply_symm_apply]

/-- No original permitted vertex label is discarded by the reference change. -/
noncomputable instance anchoredAddAction (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) :
    AddAction (supportedC0 T vertices fixed) (AnchoredRepair T other hother fixed) :=
  (referenceRepairEquiv T other hother fixed).symm.addAction (supportedC0 T vertices fixed)

/-- G-130 A: Action API connecting the native additive action to anchoredGauge. -/
theorem anchored_vadd_eq (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    b +ᵥ R = anchoredGauge T other hother vertices fixed b R := rfl

/-- Actual repairs with the new coordinate reference and the original physical anchor. -/
abbrev AnchoredGroupoid (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  ActionCategory (Multiplicative (supportedC0 T vertices fixed)) (AnchoredRepair T other hother fixed)

/-- G-130 A: Generate equivariance from the actual repair bijection, retaining all gauge labels. -/
theorem reference_repair_equivariant (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K)))
    (b : Multiplicative (supportedC0 T vertices fixed)) (R : SupportedRepair T fixed) :
    referenceRepairEquiv T other hother fixed (b • R) =
      b • referenceRepairEquiv T other hother fixed R := by
  change _ = referenceRepairEquiv T other hother fixed
    (b • ((referenceRepairEquiv T other hother fixed).symm
      (referenceRepairEquiv T other hother fixed R)))
  rw [Equiv.symm_apply_apply]

/-- Reference change gives a native groupoid equivalence, retaining all labels. -/
noncomputable def referenceGroupoidEquiv (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) :
    RepairGroupoid T vertices fixed ≌ AnchoredGroupoid T other hother vertices fixed :=
  labeledActionEquivalence (referenceRepairEquiv T other hother fixed)
    (reference_repair_equivariant T other hother vertices fixed)

/-- G-130 A: Object API of the native physically anchored reference equivalence. -/
theorem reference_groupoid_equiv_obj (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R : RepairGroupoid T vertices fixed) :
    ((referenceGroupoidEquiv T other hother vertices fixed).functor.obj R).back =
      referenceRepairEquiv T other hother fixed R.back := rfl

/-- G-130 A: Forward morphism API retaining each original gauge label. -/
theorem reference_groupoid_equiv_map_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) {R Q : RepairGroupoid T vertices fixed} (b : R ⟶ Q) :
    ((referenceGroupoidEquiv T other hother vertices fixed).functor.map b).1 = b.1 := rfl

/-- G-130 A: Inverse morphism API recovering each original gauge label. -/
theorem reference_groupoid_equiv_inverse_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K)))
    {R Q : AnchoredGroupoid T other hother vertices fixed} (b : R ⟶ Q) :
    ((referenceGroupoidEquiv T other hother vertices fixed).inverse.map b).1 = b.1 := rfl

/-- Affine reference coordinates have exactly the original correction equation. -/
noncomputable def referenceCorrectionEquiv (fixed : Set (EdgeName (K := K))) :
    SupportedCorrection T fixed ≃ AnchoredCorrection T other hother fixed :=
  (repairEquiv T fixed).symm.trans
    ((referenceRepairEquiv T other hother fixed).trans (anchoredEquiv T other hother fixed))

/-- G-130 A: Forward coordinate API for the independent shifted correction equivalence. -/
theorem reference_correction_equiv_val (fixed : Set (EdgeName (K := K)))
    (h : SupportedCorrection T fixed) :
    (referenceCorrectionEquiv T other hother fixed h).1 = h.1.1 - a := by
  rw [show (referenceCorrectionEquiv T other hother fixed h).1 =
    (anchoredCoord T other hother fixed
      (referenceRepairEquiv T other hother fixed (repairRec T fixed h))).1 from rfl,
    anchored_coord_reference, repairCoord_rec]

/-- The actual new-reference defect is the full-kernel coordinate reconstructed from its arrows. -/
theorem reference_defect_value :
    (T.withAlternativeLift other hother).toTower.defect = T.alternativeDefect other hother := by
  exact T.defect_changeReference other hother

/-- Reanchoring the shifted defect gives the original defect coordinate by coordinate. -/
theorem anchored_defect_eq :
    T.alternativeDefect other hother +
      d1 T.toTower.localCoefficients (-a) = T.toTower.defect := by
  change T.toTower.correctedDefect a + d1 T.toTower.localCoefficients (-a) = _
  rw [T.toTower.correctedDefect_eq]
  change T.toTower.defect + (d1Hom T.toTower.localCoefficients) a +
    (d1Hom T.toTower.localCoefficients) (-a) = _
  rw [map_neg]
  abel

/-- Read the new-reference coordinate of an independent anchored repair. -/
theorem anchored_coord_val (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) :
    (anchoredCoord T other hother fixed R).1 =
      (T.withAlternativeLift other hother).solutionCorrection R.1 := rfl

/-- Identity on the actual full-kernel values, expressed in the original coefficient type. -/
noncomputable def referenceC1 : C1 (T.withAlternativeLift other hother).toTower.localCoefficients ≃+
    C1 T.toTower.localCoefficients where
  toFun h := h
  invFun h := h
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- G-130 A: Evaluation API of the full-kernel identity in the original coefficient type. -/
theorem reference_c1_apply (h : C1 (T.withAlternativeLift other hother).toTower.localCoefficients)
    (e : EdgeName (K := K)) : referenceC1 T other hother h e = h e := rfl

/-- The coordinate formula applies to every anchored repair, in both directions. -/
theorem anchored_coord_inv_reference (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) :
    (anchoredCoord T other hother fixed R).1 =
      (repairCoord T fixed ((referenceRepairEquiv T other hother fixed).symm R)).1.1 - a := by
  have h := anchored_coord_reference T other hother fixed
    ((referenceRepairEquiv T other hother fixed).symm R)
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- G-130 A: Inverse coordinate API recovering the old physically anchored correction. -/
theorem reference_correction_equiv_symm_val (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    ((referenceCorrectionEquiv T other hother fixed).symm h).1.1 = referenceC1 T other hother h.1 + a := by
  change ((referenceCorrectionEquiv T other hother fixed).symm h).1.1 =
    (referenceC1 T other hother h.1) + a
  have hval := reference_correction_equiv_val T other hother fixed
    ((referenceCorrectionEquiv T other hother fixed).symm h)
  rw [Equiv.apply_symm_apply] at hval
  exact (sub_eq_iff_eq_add.mp hval.symm)

/-- Every physical vertex gauge adds the same original coboundary in the shifted coordinates. -/
theorem anchored_gauge_coord (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    (anchoredCoord T other hother fixed (anchoredGauge T other hother vertices fixed b R)).1 =
      referenceC1 T other hother (anchoredCoord T other hother fixed R).1 + d0 T.toTower.localCoefficients b.1 := by
  change (anchoredCoord T other hother fixed
    (referenceRepairEquiv T other hother fixed
      (repairGauge T vertices fixed b ((referenceRepairEquiv T other hother fixed).symm R)))).1 = _
  rw [anchored_coord_reference, repairGauge_coord, anchored_coord_inv_reference]
  change ((repairCoord T fixed ((referenceRepairEquiv T other hother fixed).symm R)).1.1 +
    d0 T.toTower.localCoefficients b.1) - a =
    ((repairCoord T fixed ((referenceRepairEquiv T other hother fixed).symm R)).1.1 - a) +
      d0 T.toTower.localCoefficients b.1
  abel

/-- All original reidentifications between anchored repairs are exactly the retained labels. -/
noncomputable def anchoredOriginalHomEquiv (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R Q : AnchoredRepair T other hother fixed) :
    {b : C0 T.toTower.localCoefficients // (∀ v ∈ vertices, b v = 0) ∧
      (T.withAlternativeLift other hother).vertexGauge b R.1 = Q.1} ≃
    {b : supportedC0 T vertices fixed // anchoredGauge T other hother vertices fixed b R = Q} where
  toFun b := by
    have h_old : T.vertexGauge b.1 ((referenceRepairEquiv T other hother fixed).symm R).1 =
        ((referenceRepairEquiv T other hother fixed).symm Q).1 := by
      apply (T.solutionChangeReference other hother).injective
      rw [T.vertexGauge_changeReference]
      change (T.withAlternativeLift other hother).vertexGauge b.1
        ((T.solutionChangeReference other hother) ((T.solutionChangeReference other hother).symm R.1)) =
        (T.solutionChangeReference other hother) ((T.solutionChangeReference other hother).symm Q.1)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact b.2.2
    let c : supportedC0 T vertices fixed := ⟨b.1, gauge_between_supported T vertices fixed
      b.1 b.2.1 _ _ h_old⟩
    exact ⟨c, Subtype.ext ((anchored_gauge_solution T other hother vertices fixed c R).trans b.2.2)⟩
  invFun b := ⟨b.1.1, supportedC0_vertex_zero T vertices fixed b.1,
    (anchored_gauge_solution T other hother vertices fixed b.1 R).symm.trans
      (congrArg Subtype.val b.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- G-130 A: Label API for the equivalence from all original physical reidentifications. -/
theorem anchored_original_hom_equiv_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R Q : AnchoredRepair T other hother fixed)
    (b : {b : C0 T.toTower.localCoefficients // (∀ v ∈ vertices, b v = 0) ∧
      (T.withAlternativeLift other hother).vertexGauge b R.1 = Q.1}) :
    (anchoredOriginalHomEquiv T other hother vertices fixed R Q b).1.1 = b.1 := rfl

/-- The relative cocycle obtained after transporting the physical anchor. -/
noncomputable def anchoredObstructionCocycle (P : ClosedRegion K)
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) : RelativeComplex.Z2 T.toTower.localCoefficients P :=
  ⟨⟨T.alternativeDefect other hother + d1 T.toTower.localCoefficients (-a), by
    rw [anchored_defect_eq]
    exact defect_mem_relative T P hfixed⟩, by
      apply Subtype.ext
      change d2 T.toTower.localCoefficients
        (T.alternativeDefect other hother + d1 T.toTower.localCoefficients (-a)) = 0
      rw [anchored_defect_eq]
      exact T.toTower.defect_cocycle hsyzygy⟩

/-- G-130 A: Compare the generated anchored relative cocycle with the original actual defect cocycle. -/
theorem anchored_obstruction_cocycle_eq (P : ClosedRegion K)
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    anchoredObstructionCocycle T other hother P hfixed hsyzygy =
      obstructionCocycle T P hfixed hsyzygy := by
  apply Subtype.ext
  apply Subtype.ext
  exact anchored_defect_eq T other hother

/-- Include anchored actual repairs when the fixed-arrow set decreases. -/
def anchoredInclusion {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    AnchoredRepair T other hother larger → AnchoredRepair T other hother fixed :=
  fun R => ⟨R.1, fun e he => R.2 e (h he)⟩

/-- G-130 A: Solution API retaining the actual object under physical-anchor relaxation. -/
theorem anchored_inclusion_solution {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : AnchoredRepair T other hother larger) :
    (anchoredInclusion T other hother h R).1 = R.1 := rfl

/-- G-130 A: Compare the actual reference bijection with physical-anchor support relaxation. -/
theorem reference_repair_inclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : SupportedRepair T larger) :
    referenceRepairEquiv T other hother fixed (repairInclusion T h R) =
      anchoredInclusion T other hother h (referenceRepairEquiv T other hother larger R) := rfl

/-- G-130 A: Compare every physical vertex gauge under anchor support relaxation. -/
theorem anchored_gauge_inclusion (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    (b : supportedC0 T vertices larger) (R : AnchoredRepair T other hother larger) :
    anchoredInclusion T other hother h (anchoredGauge T other hother vertices larger b R) =
      anchoredGauge T other hother vertices fixed (gaugeInclusion T vertices h b)
        (anchoredInclusion T other hother h R) := rfl

/-- All gauge labels are included unchanged at every range after reanchoring. -/
noncomputable def anchoredInclusionFunctor (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    AnchoredGroupoid T other hother vertices larger ⥤
      AnchoredGroupoid T other hother vertices fixed where
  obj R := (anchoredInclusion T other hother h R.back : AnchoredGroupoid T other hother vertices fixed)
  map {R _} b := ⟨Multiplicative.ofAdd (gaugeInclusion T vertices h b.1.toAdd),
    (anchored_gauge_inclusion T other hother vertices h b.1.toAdd R.back).symm.trans
      (congrArg (anchoredInclusion T other hother h) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- G-130 A: Morphism API retaining all original vertex labels under anchor relaxation. -/
theorem anchored_inclusion_functor_label (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    {R Q : AnchoredGroupoid T other hother vertices larger} (b : R ⟶ Q) :
    ((anchoredInclusionFunctor T other hother vertices h).map b).1.toAdd.1 = b.1.toAdd.1 := rfl

/-- Isomorphism classes of the independently defined anchored actual repairs. -/
abbrev AnchoredOrbit (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  Quotient (AddAction.orbitRel (supportedC0 T vertices fixed) (AnchoredRepair T other hother fixed))

/-- G-130 A: Descend the actual reference bijection using its proved preservation of all gauge orbits. -/
noncomputable def referenceOrbitEquiv (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K))) :
    RepairOrbit T P candidates allowed ≃
      AnchoredOrbit T other hother P.vertices (fixedEdgesForRange P.edges candidates allowed) := by
  let F := fixedEdgesForRange P.edges candidates allowed
  let e := referenceRepairEquiv T other hother F
  apply Quotient.congr e
  intro R Q
  change (∃ b : supportedC0 T P.vertices F, b +ᵥ Q = R) ↔
    ∃ b : supportedC0 T P.vertices F, b +ᵥ e Q = e R
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨b, (reference_repair_equivariant T other hother P.vertices F
      (Multiplicative.ofAdd b) Q).symm.trans (congrArg e hb)⟩
  · rintro ⟨b,hb⟩
    exact ⟨b, e.injective ((reference_repair_equivariant T other hother P.vertices F
      (Multiplicative.ofAdd b) Q).trans hb)⟩

/-- G-130 A: Representative API retaining the same actual physical repair after reference change. -/
theorem reference_orbit_equiv_mk (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    (R : SupportedRepair T (fixedEdgesForRange P.edges candidates allowed)) :
    referenceOrbitEquiv T other hother P candidates allowed
      (⟦R⟧ : RepairOrbit T P candidates allowed) =
      ⟦referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed) R⟧ := rfl

/-- The same H1 classifies the reanchored actual repairs. -/
noncomputable def anchoredOrbitEquivH1 (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    (base : SupportedRepair T (fixedEdgesForRange P.edges candidates allowed)) :
    RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed ≃
      AnchoredOrbit T other hother P.vertices (fixedEdgesForRange P.edges candidates allowed) :=
  (repairOrbitEquivH1 T P candidates allowed base).trans
    (referenceOrbitEquiv T other hother P candidates allowed)

/-- G-130 A: API exposing the H1 classification through the actual orbit reference equivalence. -/
theorem anchored_orbit_equiv_h1_apply (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    (base : SupportedRepair T (fixedEdgesForRange P.edges candidates allowed))
    (z : RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed) :
    anchoredOrbitEquivH1 T other hother P candidates allowed base z =
      referenceOrbitEquiv T other hother P candidates allowed
        (repairOrbitEquivH1 T P candidates allowed base z) := rfl

/-- Native automorphism groups are carried by the fully faithful actual equivalence. -/
noncomputable def referenceAutEquiv (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R : RepairGroupoid T vertices fixed) :
    Aut R ≃* Aut ((referenceGroupoidEquiv T other hother vertices fixed).functor.obj R) :=
  (referenceGroupoidEquiv T other hother vertices fixed).fullyFaithfulFunctor.autMulEquivOfFullyFaithful R

/-- G-130 A: Label API for the native fully faithful transport of actual automorphisms. -/
theorem reference_aut_equiv_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R : RepairGroupoid T vertices fixed) (b : Aut R) :
    (referenceAutEquiv T other hother vertices fixed R b).hom.1 = b.hom.1 := rfl

/-- Every independently given anchored object's full native Aut is the same relative H0. -/
noncomputable def anchoredAutH0Equiv (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    (R : AnchoredGroupoid T other hother P.vertices (fixedEdgesForRange P.edges candidates allowed)) :
    Aut R ≃* Multiplicative (RelativeComplex.relativeH0 T.toTower.localCoefficients P) :=
  ((referenceGroupoidEquiv T other hother P.vertices
      (fixedEdgesForRange P.edges candidates allowed)).symm.fullyFaithfulFunctor.autMulEquivOfFullyFaithful R).trans
    (autH0Equiv T P candidates allowed
      ((referenceGroupoidEquiv T other hother P.vertices
        (fixedEdgesForRange P.edges candidates allowed)).inverse.obj R))

/-- G-130 A: Label API recovering the full original H0 label of each anchored native automorphism. -/
theorem anchored_aut_h0_equiv_label (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    (R : AnchoredGroupoid T other hother P.vertices (fixedEdgesForRange P.edges candidates allowed))
    (b : Aut R) :
    (anchoredAutH0Equiv T other hother P candidates allowed R b).toAdd.1 = b.hom.1.toAdd.1 := rfl

section Obstruction
variable (P : ClosedRegion K) (candidates allowed : Set (EdgeName (K := K)))
variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
  (K.threeLeft s) (K.threeRight s))

/-- The shifted equation's relative obstruction, including the transported physical anchor. -/
noncomputable def anchoredObstructionClass : RelativeComplex.H2 T.toTower.localCoefficients P candidates allowed :=
  QuotientAddGroup.mk (anchoredObstructionCocycle T other hother P hfixed hsyzygy)

/-- G-130 A: Compare the physically reanchored H2 class with the original obstruction at every range. -/
theorem anchored_obstruction_class_eq :
    anchoredObstructionClass T other hother P candidates allowed hfixed hsyzygy =
      obstructionClass T P candidates allowed hfixed hsyzygy := by
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [anchored_obstruction_cocycle_eq]

/-- Reference change preserves existence of all physically anchored repairs and their obstruction. -/
theorem anchored_repair_nonempty_iff_obstruction_zero :
    Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) ↔
      anchoredObstructionClass T other hother P candidates allowed hfixed hsyzygy = 0 := by
  rw [anchored_obstruction_class_eq]
  exact (referenceRepairEquiv T other hother
    (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.symm.trans
    (repair_nonempty_iff_obstruction_zero T P candidates allowed hfixed hsyzygy)

end Obstruction
/-- Reference transport commutes with support relaxation as native functors on all objects and arrows. -/
theorem reference_groupoid_inclusion (P : ClosedRegion K)
    (candidates : Set (EdgeName (K := K))) {S U : Set (EdgeName (K := K))} (h : S ⊆ U) :
    (referenceGroupoidEquiv T other hother P.vertices (fixedEdgesForRange P.edges candidates S)).functor ⋙
      anchoredInclusionFunctor T other hother P.vertices (fixedEdgesForRange_antitone P.edges candidates h) =
    rangeFunctor T P candidates h ⋙
      (referenceGroupoidEquiv T other hother P.vertices (fixedEdgesForRange P.edges candidates U)).functor := rfl

/-- Nonempty classes of reanchored actual repairs carry the same H1 torsor. -/
noncomputable instance anchoredOrbitAddTorsor (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    [Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed))] :
    AddTorsor (RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed)
      (AnchoredOrbit T other hother P.vertices (fixedEdgesForRange P.edges candidates allowed)) := by
  letI : Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates allowed)) :=
    (referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.mpr inferInstance
  let e := referenceOrbitEquiv T other hother P candidates allowed
  exact {
    vadd := fun c Q => e (c +ᵥ e.symm Q)
    zero_vadd := by intro Q; change e ((0 : RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed) +ᵥ e.symm Q) = Q; rw [zero_vadd, e.apply_symm_apply]
    add_vadd := by
      intro c d Q
      change e ((c+d) +ᵥ e.symm Q) = e (c +ᵥ e.symm (e (d +ᵥ e.symm Q)))
      rw [e.symm_apply_apply, add_vadd]
    vsub := fun Q R => e.symm Q -ᵥ e.symm R
    nonempty := ⟨e (Classical.choice inferInstance)⟩
    vsub_vadd' := by
      intro Q R
      change e ((e.symm Q -ᵥ e.symm R) +ᵥ e.symm R) = Q
      rw [vsub_vadd, e.apply_symm_apply]
    vadd_vsub' := by
      intro c Q
      change e.symm (e (c +ᵥ e.symm Q)) -ᵥ e.symm Q = c
      rw [e.symm_apply_apply, vadd_vsub] }

/-- G-130 A: Compare native H1 actions through the reference equivalence in the nonempty case. -/
theorem reference_orbit_equiv_vadd (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    [Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates allowed))]
    (c : RelativeComplex.H1 T.toTower.localCoefficients P candidates allowed)
    (Q : RepairOrbit T P candidates allowed) :
    letI : Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) :=
      (referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.mp inferInstance
    referenceOrbitEquiv T other hother P candidates allowed (c +ᵥ Q) =
      c +ᵥ referenceOrbitEquiv T other hother P candidates allowed Q := by
  letI : Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) :=
    (referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.mp inferInstance
  let e := referenceOrbitEquiv T other hother P candidates allowed
  change e (c +ᵥ Q) = e (c +ᵥ e.symm (e Q))
  rw [e.symm_apply_apply]

/-- G-130 A: Compare native torsor differences through the same physical reference equivalence. -/
theorem reference_orbit_equiv_vsub (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K)))
    [Nonempty (SupportedRepair T (fixedEdgesForRange P.edges candidates allowed))]
    (Q R : RepairOrbit T P candidates allowed) :
    letI : Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) :=
      (referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.mp inferInstance
    referenceOrbitEquiv T other hother P candidates allowed Q -ᵥ
      referenceOrbitEquiv T other hother P candidates allowed R = Q -ᵥ R := by
  letI : Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) :=
    (referenceRepairEquiv T other hother (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.mp inferInstance
  let e := referenceOrbitEquiv T other hother P candidates allowed
  change e.symm (e Q) -ᵥ e.symm (e R) = Q -ᵥ R
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- The tangent complex uses the same full actual kernel coefficients and differentials at every range. -/
theorem reference_cochain_complex_eq (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K))) :
    RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed =
      RelativeComplex.cochainComplex
        (T.withAlternativeLift other hother).toTower.localCoefficients P candidates allowed :=
  congrArg (fun M => RelativeComplex.cochainComplex M P candidates allowed)
    (T.localCoefficients_changeReference other hother)

/-- Restoration keeps the original correction formula on every actual edge name. -/
theorem anchored_rec_choice (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) {i j : K.Vertex} (e : K.Edge i j) :
    (anchoredRec T other hother fixed h).1.choice e =
      (T.withAlternativeLift other hother).correctionChoice h.1 e := rfl

/-- The independent shifted equation retains the transported fixed value. -/
theorem anchored_correction_fixed (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) (e : EdgeName (K := K)) (he : e ∈ fixed) :
    h.1 e = -a e := h.2.1 e he

/-- The independent shifted equation is the actual new-reference defect equation. -/
theorem anchored_correction_d1 (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    d1 (T.withAlternativeLift other hother).toTower.localCoefficients h.1 =
      -(T.withAlternativeLift other hother).toTower.defect := h.2.2

/-- Compatibility spelling for the G-130 A API `solution_correction_change_reference`; retained for declaration tracing. -/
@[deprecated solution_correction_change_reference (since := "2026-10-01")] alias solutionCorrection_changeReference := solution_correction_change_reference

/-- Compatibility spelling for the G-130 A API `reference_solution_choice`; retained for declaration tracing. -/
@[deprecated reference_solution_choice (since := "2026-10-01")] alias referenceSolution_choice := reference_solution_choice

/-- Compatibility spelling for the G-130 A API `reference_repair_equiv_choice`; retained for declaration tracing. -/
@[deprecated reference_repair_equiv_choice (since := "2026-10-01")] alias referenceRepairEquiv_choice := reference_repair_equiv_choice

/-- Compatibility spelling for the G-130 A API `reference_repair_equiv_symm_choice`; retained for declaration tracing. -/
@[deprecated reference_repair_equiv_symm_choice (since := "2026-10-01")] alias referenceRepairEquiv_symm_choice := reference_repair_equiv_symm_choice

/-- Compatibility spelling for the G-130 A API `anchored_rec_coord`; retained for declaration tracing. -/
@[deprecated anchored_rec_coord (since := "2026-10-01")] alias anchoredRec_coord := anchored_rec_coord

/-- Compatibility spelling for the G-130 A API `anchored_coord_rec`; retained for declaration tracing. -/
@[deprecated anchored_coord_rec (since := "2026-10-01")] alias anchoredCoord_rec := anchored_coord_rec

/-- Compatibility spelling for the G-130 A API `anchored_coord_reference`; retained for declaration tracing. -/
@[deprecated anchored_coord_reference (since := "2026-10-01")] alias anchoredCoord_reference := anchored_coord_reference

/-- Compatibility spelling for the G-130 A API `anchored_gauge_solution`; retained for declaration tracing. -/
@[deprecated anchored_gauge_solution (since := "2026-10-01")] alias anchoredGauge_solution := anchored_gauge_solution

/-- Compatibility spelling for the G-130 A API `reference_repair_equivariant`; retained for declaration tracing. -/
@[deprecated reference_repair_equivariant (since := "2026-10-01")] alias referenceRepair_equivariant := reference_repair_equivariant

/-- Compatibility spelling for the G-130 A API `reference_groupoid_equiv_obj`; retained for declaration tracing. -/
@[deprecated reference_groupoid_equiv_obj (since := "2026-10-01")] alias referenceGroupoidEquiv_obj := reference_groupoid_equiv_obj

/-- Compatibility spelling for the G-130 A API `reference_groupoid_equiv_map_label`; retained for declaration tracing. -/
@[deprecated reference_groupoid_equiv_map_label (since := "2026-10-01")] alias referenceGroupoidEquiv_map_label := reference_groupoid_equiv_map_label

/-- Compatibility spelling for the G-130 A API `reference_groupoid_equiv_inverse_label`; retained for declaration tracing. -/
@[deprecated reference_groupoid_equiv_inverse_label (since := "2026-10-01")] alias referenceGroupoidEquiv_inverse_label := reference_groupoid_equiv_inverse_label

/-- Compatibility spelling for the G-130 A API `reference_correction_equiv_val`; retained for declaration tracing. -/
@[deprecated reference_correction_equiv_val (since := "2026-10-01")] alias referenceCorrectionEquiv_val := reference_correction_equiv_val

/-- Compatibility spelling for the G-130 A API `reference_defect_value`; retained for declaration tracing. -/
@[deprecated reference_defect_value (since := "2026-10-01")] alias referenceDefect_value := reference_defect_value

/-- Compatibility spelling for the G-130 A API `anchored_defect_eq`; retained for declaration tracing. -/
@[deprecated anchored_defect_eq (since := "2026-10-01")] alias anchoredDefect_eq := anchored_defect_eq

/-- Compatibility spelling for the G-130 A API `anchored_coord_val`; retained for declaration tracing. -/
@[deprecated anchored_coord_val (since := "2026-10-01")] alias anchoredCoord_val := anchored_coord_val

/-- Compatibility spelling for the G-130 A API `reference_c1_apply`; retained for declaration tracing. -/
@[deprecated reference_c1_apply (since := "2026-10-01")] alias referenceC1_apply := reference_c1_apply

/-- Compatibility spelling for the G-130 A API `anchored_coord_inv_reference`; retained for declaration tracing. -/
@[deprecated anchored_coord_inv_reference (since := "2026-10-01")] alias anchoredCoord_inv_reference := anchored_coord_inv_reference

/-- Compatibility spelling for the G-130 A API `reference_correction_equiv_symm_val`; retained for declaration tracing. -/
@[deprecated reference_correction_equiv_symm_val (since := "2026-10-01")] alias referenceCorrectionEquiv_symm_val := reference_correction_equiv_symm_val

/-- Compatibility spelling for the G-130 A API `anchored_gauge_coord`; retained for declaration tracing. -/
@[deprecated anchored_gauge_coord (since := "2026-10-01")] alias anchoredGauge_coord := anchored_gauge_coord

/-- Compatibility spelling for the G-130 A API `anchored_original_hom_equiv_label`; retained for declaration tracing. -/
@[deprecated anchored_original_hom_equiv_label (since := "2026-10-01")] alias anchoredOriginalHomEquiv_label := anchored_original_hom_equiv_label

/-- Compatibility spelling for the G-130 A API `anchored_obstruction_cocycle_eq`; retained for declaration tracing. -/
@[deprecated anchored_obstruction_cocycle_eq (since := "2026-10-01")] alias anchoredObstructionCocycle_eq := anchored_obstruction_cocycle_eq

/-- Compatibility spelling for the G-130 A API `anchored_inclusion_solution`; retained for declaration tracing. -/
@[deprecated anchored_inclusion_solution (since := "2026-10-01")] alias anchoredInclusion_solution := anchored_inclusion_solution

/-- Compatibility spelling for the G-130 A API `reference_repair_inclusion`; retained for declaration tracing. -/
@[deprecated reference_repair_inclusion (since := "2026-10-01")] alias referenceRepair_inclusion := reference_repair_inclusion

/-- Compatibility spelling for the G-130 A API `anchored_gauge_inclusion`; retained for declaration tracing. -/
@[deprecated anchored_gauge_inclusion (since := "2026-10-01")] alias anchoredGauge_inclusion := anchored_gauge_inclusion

/-- Compatibility spelling for the G-130 A API `anchored_inclusion_functor_label`; retained for declaration tracing. -/
@[deprecated anchored_inclusion_functor_label (since := "2026-10-01")] alias anchoredInclusionFunctor_label := anchored_inclusion_functor_label

/-- Compatibility spelling for the G-130 A API `reference_orbit_equiv_mk`; retained for declaration tracing. -/
@[deprecated reference_orbit_equiv_mk (since := "2026-10-01")] alias referenceOrbitEquiv_mk := reference_orbit_equiv_mk

/-- Compatibility spelling for the G-130 A API `anchored_orbit_equiv_h1_apply`; retained for declaration tracing. -/
@[deprecated anchored_orbit_equiv_h1_apply (since := "2026-10-01")] alias anchoredOrbitEquivH1_apply := anchored_orbit_equiv_h1_apply

/-- Compatibility spelling for the G-130 A API `reference_aut_equiv_label`; retained for declaration tracing. -/
@[deprecated reference_aut_equiv_label (since := "2026-10-01")] alias referenceAutEquiv_label := reference_aut_equiv_label

/-- Compatibility spelling for the G-130 A API `anchored_aut_h0_equiv_label`; retained for declaration tracing. -/
@[deprecated anchored_aut_h0_equiv_label (since := "2026-10-01")] alias anchoredAutH0Equiv_label := anchored_aut_h0_equiv_label

/-- Compatibility spelling for the G-130 A API `anchored_obstruction_class_eq`; retained for declaration tracing. -/
@[deprecated anchored_obstruction_class_eq (since := "2026-10-01")] alias anchoredObstructionClass_eq := anchored_obstruction_class_eq

/-- Compatibility spelling for the G-130 A API `reference_groupoid_inclusion`; retained for declaration tracing. -/
@[deprecated reference_groupoid_inclusion (since := "2026-10-01")] alias referenceGroupoid_inclusion := reference_groupoid_inclusion

/-- Compatibility spelling for the G-130 A API `reference_orbit_equiv_vadd`; retained for declaration tracing. -/
@[deprecated reference_orbit_equiv_vadd (since := "2026-10-01")] alias referenceOrbitEquiv_vadd := reference_orbit_equiv_vadd

/-- Compatibility spelling for the G-130 A API `reference_orbit_equiv_vsub`; retained for declaration tracing. -/
@[deprecated reference_orbit_equiv_vsub (since := "2026-10-01")] alias referenceOrbitEquiv_vsub := reference_orbit_equiv_vsub

/-- Compatibility spelling for the G-130 A API `reference_cochain_complex_eq`; retained for declaration tracing. -/
@[deprecated reference_cochain_complex_eq (since := "2026-10-01")] alias referenceCochainComplex_eq := reference_cochain_complex_eq

/-- Compatibility spelling for the G-130 A API `anchored_rec_choice`; retained for declaration tracing. -/
@[deprecated anchored_rec_choice (since := "2026-10-01")] alias anchoredRec_choice := anchored_rec_choice

/-- Compatibility spelling for the G-130 A API `anchored_correction_fixed`; retained for declaration tracing. -/
@[deprecated anchored_correction_fixed (since := "2026-10-01")] alias anchoredCorrection_fixed := anchored_correction_fixed

/-- Compatibility spelling for the G-130 A API `anchored_correction_d1`; retained for declaration tracing. -/
@[deprecated anchored_correction_d1 (since := "2026-10-01")] alias anchoredCorrection_d1 := anchored_correction_d1

end ActualRelative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
