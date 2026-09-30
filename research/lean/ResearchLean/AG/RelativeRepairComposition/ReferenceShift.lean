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

theorem solutionCorrection_changeReference (R : Solution T) :
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
theorem referenceSolution_choice (R : Solution T) {i j : K.Vertex} (e : K.Edge i j) :
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

theorem referenceRepairEquiv_choice (fixed : Set (EdgeName (K := K)))
    (R : SupportedRepair T fixed) {i j : K.Vertex} (e : K.Edge i j) :
    (referenceRepairEquiv T other hother fixed R).1.choice e = R.1.choice e := rfl

theorem referenceRepairEquiv_symm_choice (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) {i j : K.Vertex} (e : K.Edge i j) :
    ((referenceRepairEquiv T other hother fixed).symm R).1.choice e = R.1.choice e := rfl

/-- A fixed physical arrow has the transported coordinate h'=-a. -/
theorem anchored_correction_iff_edge
    (R : Solution (T.withAlternativeLift other hother)) {i j : K.Vertex} (e : K.Edge i j) :
    (T.withAlternativeLift other hother).solutionCorrection R ⟨i,j,e⟩ = -a ⟨i,j,e⟩ ↔
    (selectedUpper K p q T.original R.choice).edgeLift e = T.toTower.upper.edgeLift e := by
  let Q := (T.solutionChangeReference other hother).symm R
  have hQ := (T.solutionChangeReference other hother).apply_symm_apply R
  rw [← hQ, solutionCorrection_changeReference]
  change T.solutionCorrection Q ⟨i,j,e⟩ - a ⟨i,j,e⟩ = -a ⟨i,j,e⟩ ↔ _
  rw [sub_eq_iff_eq_add, neg_add_cancel]
  exact solution_correction_zero_iff_edge T Q e

/-- The new-reference equation with its transported physical boundary values. -/
def AnchoredCorrection (fixed : Set (EdgeName (K := K))) :=
  {h : C1 (T.withAlternativeLift other hother).toTower.localCoefficients // (∀ e ∈ fixed, h e = -a e) ∧
    d1 (T.withAlternativeLift other hother).toTower.localCoefficients h = -(T.withAlternativeLift other hother).toTower.defect}

noncomputable def anchoredCoord (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) : AnchoredCorrection T other hother fixed :=
  ⟨(T.withAlternativeLift other hother).solutionCorrection R.1,
    ⟨fun e he => (anchored_correction_iff_edge T other hother R.1 e.2.2).mpr (R.2 e he),
      (T.withAlternativeLift other hother).solutionCorrection_d1 R.1⟩⟩

noncomputable def anchoredRec (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) : AnchoredRepair T other hother fixed :=
  ⟨(T.withAlternativeLift other hother).solutionOfCorrection h.1 h.2.2, by
    intro e he
    apply (anchored_correction_iff_edge T other hother _ e.2.2).mp
    rw [(T.withAlternativeLift other hother).solutionCorrection_solutionOfCorrection]
    exact h.2.1 e he⟩

theorem anchoredRec_coord (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) :
    anchoredRec T other hother fixed (anchoredCoord T other hother fixed R) = R := by
  apply Subtype.ext
  exact (T.withAlternativeLift other hother).solutionOfCorrection_solutionCorrection R.1

theorem anchoredCoord_rec (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    anchoredCoord T other hother fixed (anchoredRec T other hother fixed h) = h := by
  apply Subtype.ext
  exact (T.withAlternativeLift other hother).solutionCorrection_solutionOfCorrection h.1 h.2.2

noncomputable def anchoredEquiv (fixed : Set (EdgeName (K := K))) :
    AnchoredRepair T other hother fixed ≃ AnchoredCorrection T other hother fixed where
  toFun := anchoredCoord T other hother fixed
  invFun := anchoredRec T other hother fixed
  left_inv := anchoredRec_coord T other hother fixed
  right_inv := anchoredCoord_rec T other hother fixed

theorem anchoredCoord_reference (fixed : Set (EdgeName (K := K))) (R : SupportedRepair T fixed) :
    (anchoredCoord T other hother fixed (referenceRepairEquiv T other hother fixed R)).1 =
      (repairCoord T fixed R).1.1 - a := by
  exact solutionCorrection_changeReference T other hother R.1


/-- The transferred action is the same actual new-reference vertex gauge. -/
noncomputable def anchoredGauge (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    AnchoredRepair T other hother fixed :=
  referenceRepairEquiv T other hother fixed
    (repairGauge T vertices fixed b ((referenceRepairEquiv T other hother fixed).symm R))

theorem anchoredGauge_solution (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
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

theorem anchored_vadd_eq (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    b +ᵥ R = anchoredGauge T other hother vertices fixed b R := rfl

/-- Actual repairs with the new coordinate reference and the original physical anchor. -/
abbrev AnchoredGroupoid (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  ActionCategory (Multiplicative (supportedC0 T vertices fixed)) (AnchoredRepair T other hother fixed)

theorem referenceRepair_equivariant (vertices : Set K.Vertex)
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
    (referenceRepair_equivariant T other hother vertices fixed)

theorem referenceGroupoidEquiv_obj (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R : RepairGroupoid T vertices fixed) :
    ((referenceGroupoidEquiv T other hother vertices fixed).functor.obj R).back =
      referenceRepairEquiv T other hother fixed R.back := rfl

theorem referenceGroupoidEquiv_map_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) {R Q : RepairGroupoid T vertices fixed} (b : R ⟶ Q) :
    ((referenceGroupoidEquiv T other hother vertices fixed).functor.map b).1 = b.1 := rfl

theorem referenceGroupoidEquiv_inverse_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K)))
    {R Q : AnchoredGroupoid T other hother vertices fixed} (b : R ⟶ Q) :
    ((referenceGroupoidEquiv T other hother vertices fixed).inverse.map b).1 = b.1 := rfl

/-- Affine reference coordinates have exactly the original correction equation. -/
noncomputable def referenceCorrectionEquiv (fixed : Set (EdgeName (K := K))) :
    SupportedCorrection T fixed ≃ AnchoredCorrection T other hother fixed :=
  (repairEquiv T fixed).symm.trans
    ((referenceRepairEquiv T other hother fixed).trans (anchoredEquiv T other hother fixed))

theorem referenceCorrectionEquiv_val (fixed : Set (EdgeName (K := K)))
    (h : SupportedCorrection T fixed) :
    (referenceCorrectionEquiv T other hother fixed h).1 = h.1.1 - a := by
  rw [show (referenceCorrectionEquiv T other hother fixed h).1 =
    (anchoredCoord T other hother fixed
      (referenceRepairEquiv T other hother fixed (repairRec T fixed h))).1 from rfl,
    anchoredCoord_reference, repairCoord_rec]

/-- The actual new-reference defect is the full-kernel coordinate reconstructed from its arrows. -/
theorem referenceDefect_value :
    (T.withAlternativeLift other hother).toTower.defect = T.alternativeDefect other hother := by
  exact T.defect_changeReference other hother

/-- Reanchoring the shifted defect gives the original defect coordinate by coordinate. -/
theorem anchoredDefect_eq :
    T.alternativeDefect other hother +
      d1 T.toTower.localCoefficients (-a) = T.toTower.defect := by
  change T.toTower.correctedDefect a + d1 T.toTower.localCoefficients (-a) = _
  rw [T.toTower.correctedDefect_eq]
  change T.toTower.defect + (d1Hom T.toTower.localCoefficients) a +
    (d1Hom T.toTower.localCoefficients) (-a) = _
  rw [map_neg]
  abel

/-- Read the new-reference coordinate of an independent anchored repair. -/
theorem anchoredCoord_val (fixed : Set (EdgeName (K := K)))
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

theorem referenceC1_apply (h : C1 (T.withAlternativeLift other hother).toTower.localCoefficients)
    (e : EdgeName (K := K)) : referenceC1 T other hother h e = h e := rfl

/-- The coordinate formula applies to every anchored repair, in both directions. -/
theorem anchoredCoord_inv_reference (fixed : Set (EdgeName (K := K)))
    (R : AnchoredRepair T other hother fixed) :
    (anchoredCoord T other hother fixed R).1 =
      (repairCoord T fixed ((referenceRepairEquiv T other hother fixed).symm R)).1.1 - a := by
  have h := anchoredCoord_reference T other hother fixed
    ((referenceRepairEquiv T other hother fixed).symm R)
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem referenceCorrectionEquiv_symm_val (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    ((referenceCorrectionEquiv T other hother fixed).symm h).1.1 = referenceC1 T other hother h.1 + a := by
  change ((referenceCorrectionEquiv T other hother fixed).symm h).1.1 =
    (referenceC1 T other hother h.1) + a
  have hval := referenceCorrectionEquiv_val T other hother fixed
    ((referenceCorrectionEquiv T other hother fixed).symm h)
  rw [Equiv.apply_symm_apply] at hval
  exact (sub_eq_iff_eq_add.mp hval.symm)

/-- Every physical vertex gauge adds the same original coboundary in the shifted coordinates. -/
theorem anchoredGauge_coord (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : AnchoredRepair T other hother fixed) :
    (anchoredCoord T other hother fixed (anchoredGauge T other hother vertices fixed b R)).1 =
      referenceC1 T other hother (anchoredCoord T other hother fixed R).1 + d0 T.toTower.localCoefficients b.1 := by
  change (anchoredCoord T other hother fixed
    (referenceRepairEquiv T other hother fixed
      (repairGauge T vertices fixed b ((referenceRepairEquiv T other hother fixed).symm R)))).1 = _
  rw [anchoredCoord_reference, repairGauge_coord, anchoredCoord_inv_reference]
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
    exact ⟨c, Subtype.ext ((anchoredGauge_solution T other hother vertices fixed c R).trans b.2.2)⟩
  invFun b := ⟨b.1.1, supportedC0_vertex_zero T vertices fixed b.1,
    (anchoredGauge_solution T other hother vertices fixed b.1 R).symm.trans
      (congrArg Subtype.val b.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

theorem anchoredOriginalHomEquiv_label (vertices : Set K.Vertex)
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
    rw [anchoredDefect_eq]
    exact defect_mem_relative T P hfixed⟩, by
      apply Subtype.ext
      change d2 T.toTower.localCoefficients
        (T.alternativeDefect other hother + d1 T.toTower.localCoefficients (-a)) = 0
      rw [anchoredDefect_eq]
      exact T.toTower.defect_cocycle hsyzygy⟩

theorem anchoredObstructionCocycle_eq (P : ClosedRegion K)
    (hfixed : ∀ f ∈ P.faces,
      T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
        T.toTower.upper.pathLift (K.twoRight f))
    (hsyzygy : ∀ s : K.ThreeCell, AuthoredSyzygy T.toTower.toTransportData 1
      (K.threeLeft s) (K.threeRight s)) :
    anchoredObstructionCocycle T other hother P hfixed hsyzygy =
      obstructionCocycle T P hfixed hsyzygy := by
  apply Subtype.ext
  apply Subtype.ext
  exact anchoredDefect_eq T other hother

/-- Include anchored actual repairs when the fixed-arrow set decreases. -/
def anchoredInclusion {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    AnchoredRepair T other hother larger → AnchoredRepair T other hother fixed :=
  fun R => ⟨R.1, fun e he => R.2 e (h he)⟩

theorem anchoredInclusion_solution {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : AnchoredRepair T other hother larger) :
    (anchoredInclusion T other hother h R).1 = R.1 := rfl

theorem referenceRepair_inclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : SupportedRepair T larger) :
    referenceRepairEquiv T other hother fixed (repairInclusion T h R) =
      anchoredInclusion T other hother h (referenceRepairEquiv T other hother larger R) := rfl

theorem anchoredGauge_inclusion (vertices : Set K.Vertex)
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
    (anchoredGauge_inclusion T other hother vertices h b.1.toAdd R.back).symm.trans
      (congrArg (anchoredInclusion T other hother h) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

theorem anchoredInclusionFunctor_label (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    {R Q : AnchoredGroupoid T other hother vertices larger} (b : R ⟶ Q) :
    ((anchoredInclusionFunctor T other hother vertices h).map b).1.toAdd.1 = b.1.toAdd.1 := rfl

/-- Isomorphism classes of the independently defined anchored actual repairs. -/
abbrev AnchoredOrbit (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  Quotient (AddAction.orbitRel (supportedC0 T vertices fixed) (AnchoredRepair T other hother fixed))

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
    exact ⟨b, (referenceRepair_equivariant T other hother P.vertices F
      (Multiplicative.ofAdd b) Q).symm.trans (congrArg e hb)⟩
  · rintro ⟨b,hb⟩
    exact ⟨b, e.injective ((referenceRepair_equivariant T other hother P.vertices F
      (Multiplicative.ofAdd b) Q).trans hb)⟩

theorem referenceOrbitEquiv_mk (P : ClosedRegion K)
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

theorem anchoredOrbitEquivH1_apply (P : ClosedRegion K)
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

theorem referenceAutEquiv_label (vertices : Set K.Vertex)
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

theorem anchoredAutH0Equiv_label (P : ClosedRegion K)
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

theorem anchoredObstructionClass_eq :
    anchoredObstructionClass T other hother P candidates allowed hfixed hsyzygy =
      obstructionClass T P candidates allowed hfixed hsyzygy := by
  change QuotientAddGroup.mk _ = QuotientAddGroup.mk _
  rw [anchoredObstructionCocycle_eq]

/-- Reference change preserves existence of all physically anchored repairs and their obstruction. -/
theorem anchored_repair_nonempty_iff_obstruction_zero :
    Nonempty (AnchoredRepair T other hother (fixedEdgesForRange P.edges candidates allowed)) ↔
      anchoredObstructionClass T other hother P candidates allowed hfixed hsyzygy = 0 := by
  rw [anchoredObstructionClass_eq]
  exact (referenceRepairEquiv T other hother
    (fixedEdgesForRange P.edges candidates allowed)).nonempty_congr.symm.trans
    (repair_nonempty_iff_obstruction_zero T P candidates allowed hfixed hsyzygy)

end Obstruction
/-- Reference transport commutes with support relaxation as native functors on all objects and arrows. -/
theorem referenceGroupoid_inclusion (P : ClosedRegion K)
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

theorem referenceOrbitEquiv_vadd (P : ClosedRegion K)
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

theorem referenceOrbitEquiv_vsub (P : ClosedRegion K)
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
theorem referenceCochainComplex_eq (P : ClosedRegion K)
    (candidates allowed : Set (EdgeName (K := K))) :
    RelativeComplex.cochainComplex T.toTower.localCoefficients P candidates allowed =
      RelativeComplex.cochainComplex
        (T.withAlternativeLift other hother).toTower.localCoefficients P candidates allowed :=
  congrArg (fun M => RelativeComplex.cochainComplex M P candidates allowed)
    (T.localCoefficients_changeReference other hother)

/-- Restoration keeps the original correction formula on every actual edge name. -/
theorem anchoredRec_choice (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) {i j : K.Vertex} (e : K.Edge i j) :
    (anchoredRec T other hother fixed h).1.choice e =
      (T.withAlternativeLift other hother).correctionChoice h.1 e := rfl

/-- The independent shifted equation retains the transported fixed value. -/
theorem anchoredCorrection_fixed (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) (e : EdgeName (K := K)) (he : e ∈ fixed) :
    h.1 e = -a e := h.2.1 e he

/-- The independent shifted equation is the actual new-reference defect equation. -/
theorem anchoredCorrection_d1 (fixed : Set (EdgeName (K := K)))
    (h : AnchoredCorrection T other hother fixed) :
    d1 (T.withAlternativeLift other hother).toTower.localCoefficients h.1 =
      -(T.withAlternativeLift other hother).toTower.defect := h.2.2

end ActualRelative
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
