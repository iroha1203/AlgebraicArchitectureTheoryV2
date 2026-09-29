import ResearchLean.AG.AbelianLiftingObstruction.Defect

/-!
# Actual kernel corrections of the original selected arrows

Every correction is an arbitrary element of the same degree-one cochain group.
It acts on the original selected edge arrow, and the resulting comparisons
are constructed again from the reselected paths.
-/

namespace AAT.AG.AbelianLiftingObstruction

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary

universe uG uE uB uD vE vB vD

namespace TowerPresentation

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)

/-- An arbitrary C¹ correction, included into the actual composite fiber group. -/
def correctionReselection (h : C1 T.localCoefficients) :
    EdgeReselection T.upper :=
  fun i j e => kernelInclusion p q (T.upper.object j)
    (Additive.toMul (h ⟨i, j, e⟩))

/-- The corrected arrow is the original selected arrow followed by its actual kernel value. -/
theorem correctedEdge_eq (h : C1 T.localCoefficients)
    {i j : K.Vertex} (e : K.Edge i j) :
    reselectedEdgeLift T.upper (T.correctionReselection h) e =
      T.upper.edgeLift e ≫
        FiberAut.hom (kernelInclusion p q _ (Additive.toMul (h ⟨i, j, e⟩))) :=
  rfl

/-- Every corrected edge has the same image under the first projection. -/
theorem correctedEdge_core (h : C1 T.localCoefficients)
    {i j : K.Vertex} (e : K.Edge i j) :
    p.map (reselectedEdgeLift T.upper (T.correctionReselection h) e) =
      p.map (T.upper.edgeLift e) := by
  rw [T.correctedEdge_eq, p.map_comp, kernelInclusion_map, Category.comp_id]

/-- The endpoint factor of the corrected path is the inclusion of T_w(h). -/
theorem correctedPath_fac (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    T.upper.pathLift w ≫
      FiberAut.hom (kernelInclusion p q _
        (Additive.toMul (pathCorrection T.localCoefficients h w))) =
      reselectedPathLift T.upper (T.correctionReselection h) w := by
  induction w with
  | nil v =>
      simp [Arbitrary.reselectedPathLift, LiftData.pathLift,
        pathCorrection, Arbitrary.reselectLiftData]
      rfl
  | cons e tail ih =>
      let a : Kernel p q (T.upper.object _) := Additive.toMul (h ⟨_, _, e⟩)
      let b : Kernel p q (T.upper.object _) :=
        Additive.toMul (pathCorrection T.localCoefficients h tail)
      have htransport : Additive.toMul
          (T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩)) =
          T.pathKernelTransportHom tail a := by
        simpa only [a, ofMul_toMul, toMul_ofMul] using
          congrArg Additive.toMul (T.edgeCoefficients_pathTransport tail a)
      have hfac := kernelTransportHom_fac p q (T.upper.pathLift tail)
        (T.upper.pathLift_isStronglyCocartesian tail)
        (T.pathLowerStrong tail) a
      change T.upper.pathLift tail ≫
          FiberAut.hom (kernelInclusion p q _
            (T.pathKernelTransportHom tail a)) =
        FiberAut.hom (kernelInclusion p q _ a) ≫
          T.upper.pathLift tail at hfac
      change (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
          FiberAut.hom (kernelInclusion p q _
            (Additive.toMul
              (T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩) +
                pathCorrection T.localCoefficients h tail))) =
        (T.upper.edgeLift e ≫
            FiberAut.hom (kernelInclusion p q _ a)) ≫
          reselectedPathLift T.upper (T.correctionReselection h) tail
      have hproduct : Additive.toMul
          (T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩) +
            pathCorrection T.localCoefficients h tail) =
          T.pathKernelTransportHom tail a * b := by
        change Additive.toMul
          ((T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩) :
            Additive (Kernel p q (T.upper.object _))) +
            (pathCorrection T.localCoefficients h tail :
              Additive (Kernel p q (T.upper.object _)))) = _
        change (Additive.toMul
            (T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩)) :
              Kernel p q (T.upper.object _)) * b =
          T.pathKernelTransportHom tail a * b
        exact congrArg (fun x => x * b) htransport
      have hrewrite := congrArg
        (fun x => (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
          FiberAut.hom (kernelInclusion p q _ x)) hproduct
      dsimp only at hrewrite
      calc
        (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
          FiberAut.hom (kernelInclusion p q _
            (Additive.toMul
              (T.localCoefficients.pathTransport tail (h ⟨_, _, e⟩) +
                pathCorrection T.localCoefficients h tail))) =
          (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
          FiberAut.hom (kernelInclusion p q _
            (T.pathKernelTransportHom tail a * b)) := hrewrite
        _ = (T.upper.edgeLift e ≫
            FiberAut.hom (kernelInclusion p q _ a)) ≫
          reselectedPathLift T.upper (T.correctionReselection h) tail := by
          rw [T.kernelComm _ (T.pathKernelTransportHom tail a) b]
          rw [map_mul (kernelInclusion p q _) b (T.pathKernelTransportHom tail a)]
          change (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
              (FiberAut.hom (kernelInclusion p q _ (T.pathKernelTransportHom tail a)) ≫
                FiberAut.hom (kernelInclusion p q _ b)) =
            (T.upper.edgeLift e ≫
                FiberAut.hom (kernelInclusion p q _ a)) ≫
              reselectedPathLift T.upper (T.correctionReselection h) tail
          rw [← Category.assoc]
          calc
            ((T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
                FiberAut.hom (kernelInclusion p q _ (T.pathKernelTransportHom tail a))) ≫
              FiberAut.hom (kernelInclusion p q _ b) =
              ((T.upper.edgeLift e ≫
                  FiberAut.hom (kernelInclusion p q _ a)) ≫
                T.upper.pathLift tail) ≫
              FiberAut.hom (kernelInclusion p q _ b) := by
                have hpre : (T.upper.edgeLift e ≫ T.upper.pathLift tail) ≫
                    FiberAut.hom
                      (kernelInclusion p q _ (T.pathKernelTransportHom tail a)) =
                    (T.upper.edgeLift e ≫
                      FiberAut.hom (kernelInclusion p q _ a)) ≫
                        T.upper.pathLift tail := by
                  calc
                    _ = T.upper.edgeLift e ≫
                        (T.upper.pathLift tail ≫
                          FiberAut.hom (kernelInclusion p q _
                            (T.pathKernelTransportHom tail a))) :=
                              Category.assoc _ _ _
                    _ = T.upper.edgeLift e ≫
                        (FiberAut.hom (kernelInclusion p q _ a) ≫
                          T.upper.pathLift tail) :=
                            congrArg (fun x => T.upper.edgeLift e ≫ x) hfac
                    _ = _ := (Category.assoc _ _ _).symm
                exact congrArg (fun x => x ≫ FiberAut.hom
                  (kernelInclusion p q _ b)) hpre
            _ = (T.upper.edgeLift e ≫
                FiberAut.hom (kernelInclusion p q _ a)) ≫
              (T.upper.pathLift tail ≫ FiberAut.hom (kernelInclusion p q _ b)) :=
                Category.assoc _ _ _
            _ = _ := congrArg (fun x => (T.upper.edgeLift e ≫
              FiberAut.hom (kernelInclusion p q _ a)) ≫ x) ih

/-- Strong uniqueness identifies the existing endpoint transition with the same T_w(h). -/
theorem pathTransition_eq_correction (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    pathReselectionTransition T.upper 1 (T.correctionReselection h) w =
      kernelInclusion p q _
        (Additive.toMul (pathCorrection T.localCoefficients h w)) := by
  apply FiberAut.ext_of_strong_fac (T.upper.pathLift w)
    (T.upper.pathLift_isStronglyCocartesian w)
  rw [← Arbitrary.reselectedPathLift_one T.upper w]
  rw [Arbitrary.pathReselectionTransition_fac]
  rw [mul_one]
  rw [Arbitrary.reselectedPathLift_one]
  exact (T.correctedPath_fac h w).symm

/-- A kernel correction leaves the actual core image of every evaluated path unchanged. -/
theorem correctedPath_core (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    p.map (reselectedPathLift T.upper (T.correctionReselection h) w) =
      p.map (T.upper.pathLift w) := by
  have hfac := congrArg (fun x => p.map x) (T.correctedPath_fac h w)
  simpa only [p.map_comp, kernelInclusion_map, Category.comp_id] using hfac.symm

/-- The lower strong property is preserved because corrected paths have the same core arrow. -/
theorem correctedPathLowerStrong (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    q.IsStronglyCocartesian (T.upper.pathBase w)
      (p.map (reselectedPathLift T.upper (T.correctionReselection h) w)) := by
  rw [T.correctedPath_core h w]
  exact T.pathLowerStrong w

/-- The same original authored comparison remains aligned after every kernel correction. -/
theorem correctedCoreAlignment (h : C1 T.localCoefficients) (f : K.TwoCell) :
    p.map (reselectedPathLift T.upper (T.correctionReselection h) (K.twoLeft f)) ≫
      p.map (FiberAut.hom (T.comparator f)) =
    p.map (reselectedPathLift T.upper (T.correctionReselection h) (K.twoRight f)) := by
  rw [T.correctedPath_core h (K.twoLeft f),
    T.correctedPath_core h (K.twoRight f)]
  exact T.coreAlignment f

/-- Rebuild the B1 kernel element from the actually corrected left and right paths. -/
noncomputable def correctedFaceDefect (h : C1 T.localCoefficients)
    (f : K.TwoCell) : Kernel p q (T.upper.object (K.twoTarget f)) :=
  faceKernelDefect p q
    (reselectedPathLift T.upper (T.correctionReselection h) (K.twoLeft f))
    (reselectedPathLift T.upper (T.correctionReselection h) (K.twoRight f))
    (reselectedPathLift_isStronglyCocartesian T.upper
      (T.correctionReselection h) (K.twoLeft f))
    (by rw [T.faceBase f]
        exact reselectedPathLift_isStronglyCocartesian T.upper
          (T.correctionReselection h) (K.twoRight f))
    (T.correctedPathLowerStrong h (K.twoLeft f))
    (T.comparator f) (T.correctedCoreAlignment h f)

/-- The rebuilt kernel element is exactly the preexisting raw defect of those paths. -/
theorem correctedFaceDefect_eq_raw (h : C1 T.localCoefficients)
    (f : K.TwoCell) :
    kernelInclusion p q _ (T.correctedFaceDefect h f) =
      rawFaceDefect T.toTransportData (T.correctionReselection h) f := by
  unfold correctedFaceDefect
  rw [faceKernelDefect_inclusion]
  rfl

/-- The actually reconstructed defect is a cochain of the unchanged local coefficients. -/
noncomputable def correctedDefect (h : C1 T.localCoefficients) :
    C2 T.localCoefficients :=
  fun f => Additive.ofMul (T.correctedFaceDefect h f)

/-- The original noncommutative transition becomes a kernel equation under condition 3. -/
theorem correctedFaceDefect_eq (h : C1 T.localCoefficients)
    (f : K.TwoCell) :
    T.correctedFaceDefect h f =
      (Additive.toMul (pathCorrection T.localCoefficients h (K.twoLeft f)) :
        Kernel p q (T.upper.object (K.twoTarget f))) *
        T.faceDefect f *
          (Additive.toMul (pathCorrection T.localCoefficients h (K.twoRight f)) :
            Kernel p q (T.upper.object (K.twoTarget f)))⁻¹ := by
  let x : Kernel p q (T.upper.object (K.twoTarget f)) :=
    Additive.toMul (pathCorrection T.localCoefficients h (K.twoLeft f))
  let y : Kernel p q (T.upper.object (K.twoTarget f)) :=
    Additive.toMul (pathCorrection T.localCoefficients h (K.twoRight f))
  have hc := T.comparatorCentralizes f x
  have hraw := Arbitrary.rawFaceDefect_transition T.toTransportData 1
    (T.correctionReselection h) f
  rw [mul_one, T.pathTransition_eq_correction h (K.twoLeft f),
    T.pathTransition_eq_correction h (K.twoRight f)] at hraw
  change rawFaceDefect T.toTransportData (T.correctionReselection h) f =
      (T.comparator f * kernelInclusion p q _ x * (T.comparator f)⁻¹) *
        rawFaceDefect T.toTransportData 1 f *
          (kernelInclusion p q _ y)⁻¹ at hraw
  rw [← T.correctedFaceDefect_eq_raw h f, ← T.faceDefect_eq_raw f] at hraw
  have hconj : T.comparator f * kernelInclusion p q _ x *
      (T.comparator f)⁻¹ = kernelInclusion p q _ x := by
    rw [hc]
    simp [mul_assoc]
  rw [hconj] at hraw
  apply kernelInclusion_injective p q _
  calc
    kernelInclusion p q _ (T.correctedFaceDefect h f) =
        kernelInclusion p q _ x * kernelInclusion p q _ (T.faceDefect f) *
          (kernelInclusion p q _ y)⁻¹ := hraw
    _ = kernelInclusion p q _ (x * T.faceDefect f * y⁻¹) := by
      simp only [map_mul, map_inv]

/-- G-129 B2: all actual kernel corrections change the rebuilt defect by the same d¹. -/
theorem correctedDefect_eq (h : C1 T.localCoefficients) :
    T.correctedDefect h = T.defect + d1 T.localCoefficients h := by
  funext f
  have hface := T.correctedFaceDefect_eq h f
  let x : Additive (Kernel p q (T.upper.object (K.twoTarget f))) :=
    pathCorrection T.localCoefficients h (K.twoLeft f)
  let y : Additive (Kernel p q (T.upper.object (K.twoTarget f))) :=
    pathCorrection T.localCoefficients h (K.twoRight f)
  change Additive.ofMul (T.correctedFaceDefect h f) =
    Additive.ofMul (T.faceDefect f) + (x - y)
  apply Additive.toMul.injective
  change T.correctedFaceDefect h f = _
  rw [hface]
  simp only [toMul_add, toMul_sub, toMul_ofMul]
  rw [T.kernelComm _
    (Additive.toMul (pathCorrection T.localCoefficients h (K.twoLeft f)))
    (T.faceDefect f)]
  simp only [div_eq_mul_inv, mul_assoc]
  rfl

/-- Whiskering a centralizing authored value is unchanged by kernel correction. -/
theorem whisker_correction_invariant (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j)
    (u : FiberAut (p ⋙ q) (T.upper.object i))
    (hu : ∀ a : Kernel p q (T.upper.object i),
      u * kernelInclusion p q _ a = kernelInclusion p q _ a * u) :
    whiskerFiberAut T.upper (T.correctionReselection h) u w =
      whiskerFiberAut T.upper 1 u w := by
  let c : Kernel p q (T.upper.object j) :=
    Additive.toMul (pathCorrection T.localCoefficients h w)
  have hcompare := fiberTransport_comparison (p ⋙ q)
    (T.upper.pathLift w)
    (reselectedPathLift T.upper (T.correctionReselection h) w)
    (T.upper.pathLift_isStronglyCocartesian w)
    (reselectedPathLift_isStronglyCocartesian T.upper
      (T.correctionReselection h) w)
    (kernelInclusion p q _ c) (T.correctedPath_fac h w) u
  have hnew : fiberTransportHom (p ⋙ q)
      (reselectedPathLift T.upper (T.correctionReselection h) w)
      (reselectedPathLift_isStronglyCocartesian T.upper
        (T.correctionReselection h) w) u =
      whiskerFiberAut T.upper (T.correctionReselection h) u w := by
    exact congrArg (fun F => F u)
      (fiberTransportHom_eq_whisker (p ⋙ q) T.upper
        (T.correctionReselection h) w)
  have hold : fiberTransportHom (p ⋙ q)
      (T.upper.pathLift w) (T.upper.pathLift_isStronglyCocartesian w) u =
      whiskerFiberAut T.upper 1 u w := by
    simpa only [Arbitrary.reselectedPathLift_one] using
      congrArg (fun F => F u)
        (fiberTransportHom_eq_whisker (p ⋙ q) T.upper 1 w)
  rw [hnew, hold] at hcompare
  have hc := T.whisker_centralizes w u hu c
  apply mul_right_cancel (b := kernelInclusion p q _ c)
  exact hcompare.trans hc.symm

/-- Each authored oriented face retains exactly its original transported comparison. -/
theorem orientedAuthored_correction_invariant (h : C1 T.localCoefficients)
    {source target : K.Vertex}
    (f : WhiskeredFace K.toFiniteTransportTwoPresentation source target) :
    orientedFaceAuthoredComparator T.toTransportData
      (T.correctionReselection h) f =
    orientedFaceAuthoredComparator T.toTransportData 1 f := by
  rcases f with ⟨cell, incoming, outgoing, orientation⟩
  cases orientation with
  | forward =>
      change whiskerFiberAut T.upper (T.correctionReselection h)
          (T.comparator cell) outgoing =
        whiskerFiberAut T.upper 1 (T.comparator cell) outgoing
      exact T.whisker_correction_invariant h outgoing
        (T.comparator cell) (T.comparatorCentralizes cell)
  | backward =>
      change whiskerFiberAut T.upper (T.correctionReselection h)
          (T.comparator cell)⁻¹ outgoing =
        whiskerFiberAut T.upper 1 (T.comparator cell)⁻¹ outgoing
      apply T.whisker_correction_invariant h outgoing
      intro a
      exact (show Commute (T.comparator cell) (kernelInclusion p q _ a)
        from T.comparatorCentralizes cell a).inv_left.eq

/-- The original authored comparison of any typed pasting is independent of kernel correction. -/
theorem authoredPasting_correction_invariant (h : C1 T.localCoefficients)
    {source target : K.Vertex} {before after : K.Path source target}
    (P : RewritePasting K.toFiniteTransportTwoPresentation before after) :
    authoredPastingComparator T.toTransportData (T.correctionReselection h) P =
      authoredPastingComparator T.toTransportData 1 P := by
  induction P with
  | nil _ => rfl
  | cons step tail ih =>
      simp only [Arbitrary.authoredPastingComparator,
        Arbitrary.pastingComparator]
      change authoredPastingComparator T.toTransportData
          (T.correctionReselection h) tail *
            orientedFaceAuthoredComparator T.toTransportData
              (T.correctionReselection h) step.face =
        authoredPastingComparator T.toTransportData 1 tail *
          orientedFaceAuthoredComparator T.toTransportData 1 step.face
      rw [ih, T.orientedAuthored_correction_invariant h step.face]

/-- The designated authored 3-cell condition survives every actual kernel correction. -/
theorem authoredSyzygy_correction_invariant (h : C1 T.localCoefficients)
    (hsyzygy : ∀ s : K.ThreeCell,
      AuthoredSyzygy T.toTransportData 1 (K.threeLeft s) (K.threeRight s))
    (s : K.ThreeCell) :
    AuthoredSyzygy T.toTransportData (T.correctionReselection h)
      (K.threeLeft s) (K.threeRight s) := by
  unfold AuthoredSyzygy
  rw [T.authoredPasting_correction_invariant h (K.threeLeft s),
    T.authoredPasting_correction_invariant h (K.threeRight s)]
  exact hsyzygy s

/-- Strongly generated kernel transport along a corrected path is the original path map. -/
theorem correctedPathKernelTransport_eq (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j) :
    kernelTransportHom p q
        (reselectedPathLift T.upper (T.correctionReselection h) w)
        (reselectedPathLift_isStronglyCocartesian T.upper
          (T.correctionReselection h) w)
        (T.correctedPathLowerStrong h w) =
      T.pathKernelTransportHom w := by
  exact kernelTransport_eq_of_kernel_comparison p q
    (T.upper.pathLift w)
    (reselectedPathLift T.upper (T.correctionReselection h) w)
    (T.upper.pathLift_isStronglyCocartesian w)
    (reselectedPathLift_isStronglyCocartesian T.upper
      (T.correctionReselection h) w)
    (T.pathLowerStrong w) (T.correctedPathLowerStrong h w)
    (T.kernelComm j)
    (Additive.toMul (pathCorrection T.localCoefficients h w))
    (T.correctedPath_fac h w)

/-- The unchanged local coefficients evaluate every path by its newly generated kernel map. -/
theorem correctedPath_localCoefficients (h : C1 T.localCoefficients)
    {i j : K.Vertex} (w : K.Path i j)
    (a : Kernel p q (T.upper.object i)) :
    (T.localCoefficients.pathTransport w) (Additive.ofMul a) =
      Additive.ofMul
        (kernelTransportHom p q
          (reselectedPathLift T.upper (T.correctionReselection h) w)
          (reselectedPathLift_isStronglyCocartesian T.upper
            (T.correctionReselection h) w)
          (T.correctedPathLowerStrong h w) a) := by
  rw [T.correctedPathKernelTransport_eq h w]
  exact T.edgeCoefficients_pathTransport w a

end TowerPresentation

end AAT.AG.AbelianLiftingObstruction

#assert_standard_axioms_only AAT.AG.AbelianLiftingObstruction
