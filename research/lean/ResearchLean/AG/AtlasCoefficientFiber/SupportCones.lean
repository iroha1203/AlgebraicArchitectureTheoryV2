import ResearchLean.AG.AtlasCoefficientFiber.SupportConnecting
import ResearchLean.AG.AtlasCoefficientFiber.FiberCone

/-!
# G-135 D：同じ三錐と原合成triangleの台制限

## Implementation notes

元η・ε・独立uの可換正方形から標準mappingCone.mapを生成する。
全整数次数の二座標で三射とshift負号を保ち、元Q評価の図式を照合する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition CochainComplex
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)

/-- 元Unit正方形を標準零延長の全Homへ移す。 -/
theorem supportStandardUnit :
    zeroExtensionMap (unitHom M B) ≫ zeroExtensionMap (supportPushforwardHom M hab) =
      zeroExtensionMap (subsetRestrictHom Nc hab) ≫ zeroExtensionMap (unitHom M A) := by
  have hh := congrArg zeroExtensionMap (supportUnitHom M hab)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
  exact hh

/-- 元Evaluation正方形を標準零延長の全Homへ移す。 -/
theorem supportStandardEvaluation :
    zeroExtensionMap (evaluationHom M B) ≫ zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht)) =
      zeroExtensionMap (supportPushforwardHom M hab) ≫ zeroExtensionMap (evaluationHom M A) := by
  have hh := congrArg zeroExtensionMap (supportEvaluationHom M hab)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
  exact hh.symm

/-- 元Direct正方形を標準零延長の全Homへ移す。 -/
theorem supportStandardDirect :
    zeroExtensionMap (M.aSubnerveComparisonHom B) ≫ zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht)) =
      zeroExtensionMap (subsetRestrictHom Nc hab) ≫ zeroExtensionMap (M.aSubnerveComparisonHom A) := by
  have hh := congrArg zeroExtensionMap (supportDirectHom M hab)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
  exact hh

/-- 元coefficient錐を同じ原正方形から台制限する。 -/
def supportCoefficientCone : coefficientCone M B ⟶ coefficientCone M A :=
  mappingCone.map (zeroExtensionMap (unitHom M B)) (zeroExtensionMap (unitHom M A))
    (zeroExtensionMap (subsetRestrictHom Nc hab)) (zeroExtensionMap (supportPushforwardHom M hab)) (supportStandardUnit M hab)

/-- 同じ元coefficient錐制限は全次数で元二座標の台制限として作用する。 -/
theorem supportCoefficientCone_apply (n : ℤ) (z : (coefficientCone M B).X n) :
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) n ((supportCoefficientCone M hab).f n z) =
      ((zeroExtensionMap (supportPushforwardHom M hab)).f n (coneCoordinateEquiv (zeroExtensionMap (unitHom M B)) n z).1,
       (zeroExtensionMap (subsetRestrictHom Nc hab)).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (unitHom M B)) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (supportStandardUnit M hab) n z

/-- 元fiber錐を同じ原正方形から台制限する。 -/
def supportFiberCone : fiberCone M B ⟶ fiberCone M A :=
  mappingCone.map (zeroExtensionMap (evaluationHom M B)) (zeroExtensionMap (evaluationHom M A))
    (zeroExtensionMap (supportPushforwardHom M hab)) (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))) (supportStandardEvaluation M hab)

/-- 同じ元fiber錐制限は全次数で元二座標の台制限として作用する。 -/
theorem supportFiberCone_apply (n : ℤ) (z : (fiberCone M B).X n) :
    coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n ((supportFiberCone M hab).f n z) =
      ((zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))).f n (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M B)) n z).1,
       (zeroExtensionMap (supportPushforwardHom M hab)).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M B)) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (supportStandardEvaluation M hab) n z

/-- 元total錐を同じ原正方形から台制限する。 -/
def supportTotalCone : totalCone M B ⟶ totalCone M A :=
  mappingCone.map (zeroExtensionMap (M.aSubnerveComparisonHom B)) (zeroExtensionMap (M.aSubnerveComparisonHom A))
    (zeroExtensionMap (subsetRestrictHom Nc hab)) (zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))) (supportStandardDirect M hab)

/-- 同じ元total錐制限は全次数で元二座標の台制限として作用する。 -/
theorem supportTotalCone_apply (n : ℤ) (z : (totalCone M B).X n) :
    coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n ((supportTotalCone M hab).f n z) =
      ((zeroExtensionMap (subsetRestrictHom Nf (fun _ ht => hab ht))).f n (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom B)) n z).1,
       (zeroExtensionMap (subsetRestrictHom Nc hab)).f (n+1) (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom B)) n z).2) :=
  coneCoordinateEquiv_map _ _ _ _ (supportStandardDirect M hab) n z

/-- 元合成triangleの第一射は同じ三錐台制限と全次数で可換。 -/
theorem supportConeTriangle_first :
    (coefficientCompositionTriangle M B).mor₁ ≫ supportTotalCone M hab =
      supportCoefficientCone M hab ≫ (coefficientCompositionTriangle M A).mor₁ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (supportTotalCone M hab).f n ((coefficientCompositionTriangle M B).mor₁.f n z) =
    (coefficientCompositionTriangle M A).mor₁.f n ((supportCoefficientCone M hab).f n z)
  apply (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom A)) n).injective
  rw [supportTotalCone_apply, coefficientCompositionTriangle_first,
    coefficientCompositionTriangle_first, supportCoefficientCone_apply]
  apply Prod.ext
  · exact congrArg (fun f => f.f n (coneCoordinateEquiv (zeroExtensionMap (unitHom M B)) n z).1)
      (supportStandardEvaluation M hab)
  · rfl

/-- 元合成triangleの第二射も原η正方形から全次数で可換。 -/
theorem supportConeTriangle_second :
    (coefficientCompositionTriangle M B).mor₂ ≫ supportFiberCone M hab =
      supportTotalCone M hab ≫ (coefficientCompositionTriangle M A).mor₂ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (supportFiberCone M hab).f n ((coefficientCompositionTriangle M B).mor₂.f n z) =
    (coefficientCompositionTriangle M A).mor₂.f n ((supportTotalCone M hab).f n z)
  apply (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n).injective
  rw [supportFiberCone_apply, coefficientCompositionTriangle_second,
    coefficientCompositionTriangle_second, supportTotalCone_apply]
  apply Prod.ext
  · rfl
  · exact congrArg (fun f => f.f (n+1)
      (coneCoordinateEquiv (zeroExtensionMap (M.aSubnerveComparisonHom B)) n z).2)
      (supportStandardUnit M hab)

/-- 標準shiftの錐台射は同じ次数加算同型の下で元の次数射である。 -/
theorem supportConeShift_apply (n : ℤ) (z : ((coefficientCone M B)⟦(1 : ℤ)⟧).X n) :
    ((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((supportCoefficientCone M hab)⟦(1 : ℤ)⟧'.f n z) =
      (supportCoefficientCone M hab).f (n+1)
        (((coefficientCone M B).shiftFunctorObjXIso 1 n (n+1) rfl).hom z) := rfl

/-- 元合成triangleの第三射は同じ標準shift負号まで保って全次数で可換。 -/
theorem supportConeTriangle_third :
    (coefficientCompositionTriangle M B).mor₃ ≫ (supportCoefficientCone M hab)⟦(1 : ℤ)⟧' =
      supportFiberCone M hab ≫ (coefficientCompositionTriangle M A).mor₃ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (supportCoefficientCone M hab)⟦(1 : ℤ)⟧'.f n
      ((coefficientCompositionTriangle M B).mor₃.f n z) =
    (coefficientCompositionTriangle M A).mor₃.f n ((supportFiberCone M hab).f n z)
  apply (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).toLinearEquiv).injective
  apply (coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)).injective
  change coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
    (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
      ((supportCoefficientCone M hab)⟦(1 : ℤ)⟧'.f n
        ((coefficientCompositionTriangle M B).mor₃.f n z))) =
    coneCoordinateEquiv (zeroExtensionMap (unitHom M A)) (n+1)
      (((coefficientCone M A).shiftFunctorObjXIso 1 n (n+1) rfl).hom
        ((coefficientCompositionTriangle M A).mor₃.f n ((supportFiberCone M hab).f n z)))
  rw [supportConeShift_apply, supportCoefficientCone_apply, coefficientCompositionTriangle_third,
    coefficientCompositionTriangle_third, supportFiberCone_apply]
  apply Prod.ext
  · exact map_neg ((zeroExtensionMap (supportPushforwardHom M hab)).f (n+1)).hom _
  · exact map_zero ((zeroExtensionMap (subsetRestrictHom Nc hab)).f (n+1+1)).hom

/-- 元三錐の全三射から同じ実合成triangle間の台射を生成する。 -/
def supportConeTriangle : coefficientCompositionTriangle M B ⟶ coefficientCompositionTriangle M A where
  hom₁ := supportCoefficientCone M hab
  hom₂ := supportTotalCone M hab
  hom₃ := supportFiberCone M hab
  comm₁ := supportConeTriangle_first M hab
  comm₂ := supportConeTriangle_second M hab
  comm₃ := supportConeTriangle_third M hab

/-- 原fiber錐からQへの評価は全次数で同じ台制限と可換。 -/
theorem supportFiberConeDesc : fiberConeDesc M B ≫ zeroExtensionMap (supportQHom M hab) =
    supportFiberCone M hab ≫ fiberConeDesc M A := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (zeroExtensionMap (supportQHom M hab)).f n ((fiberConeDesc M B).f n z) =
    (fiberConeDesc M A).f n ((supportFiberCone M hab).f n z)
  rw [fiberConeDesc_apply, fiberConeDesc_apply, supportFiberCone_apply]
  have hh := congrArg zeroExtensionMap (supportRestrictionHom M hab)
  rw [zeroExtensionMap_comp, zeroExtensionMap_comp] at hh
  exact congrArg (fun f => f.f n (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M B)) n z).1) hh

/-- 原fiber錐からQへの全homology同型も同じ台射と自然。 -/
theorem supportFiberConeHomologyEquiv (n : ℤ) (z : (fiberCone M B).homology n) :
    HomologicalComplex.homologyMap (zeroExtensionMap (supportQHom M hab)) n
      (fiberConeHomologyEquiv M B n z) =
    fiberConeHomologyEquiv M A n (HomologicalComplex.homologyMap (supportFiberCone M hab) n z) := by
  rw [fiberConeHomologyEquiv_apply, fiberConeHomologyEquiv_apply,
    ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    supportFiberConeDesc]

/-- 原fiber錐の標準連結射は原Q評価と同じδを介して全整数次数で自然。 -/
theorem supportFiberConeConnecting (n : ℤ) (z : (fiberCone M B).homology n) :
    HomologicalComplex.homologyMap (zeroExtensionMap (supportPushforwardHom M hab)) (n+1)
      (coneConnecting (zeroExtensionMap (evaluationHom M B)) n z) =
    coneConnecting (zeroExtensionMap (evaluationHom M A)) n
      (HomologicalComplex.homologyMap (supportFiberCone M hab) n z) := by
  rw [fiberCone_connecting, fiberCone_connecting, ModuleCat.comp_apply, ModuleCat.comp_apply]
  have hh := supportConnecting_delta M hab n
    (fiberConeHomologyEquiv M B n z)
  rw [supportFiberConeHomologyEquiv, fiberConeHomologyEquiv_apply,
    fiberConeHomologyEquiv_apply] at hh
  exact hh

/-- 原Coefficient錐の台制限の恒等則。 -/
theorem supportCoefficientCone_refl (A : Set qc.Target) :
    supportCoefficientCone M (Set.Subset.refl A) = 𝟙 _ := by
  simp only [supportCoefficientCone, supportPushforwardHom_refl, subsetRestrictHom_refl, zeroExtensionMap_id, mappingCone.map_id]

/-- 原Coefficient錐の台制限の合成則。 -/
theorem supportCoefficientCone_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    supportCoefficientCone M hbc ≫ supportCoefficientCone M hab = supportCoefficientCone M (hab.trans hbc) := by
  have ha := congrArg zeroExtensionMap (subsetRestrictHom_comp Nc hab hbc)
  have hb := congrArg zeroExtensionMap (supportPushforwardHom_comp M hab hbc)
  rw [zeroExtensionMap_comp] at ha hb
  dsimp only [supportCoefficientCone]
  rw [← mappingCone.map_comp]
  simp only [ha, hb]

/-- 原Fiber錐の台制限の恒等則。 -/
theorem supportFiberCone_refl (A : Set qc.Target) :
    supportFiberCone M (Set.Subset.refl A) = 𝟙 _ := by
  simp only [supportFiberCone, supportPushforwardHom_refl, subsetRestrictHom_refl, zeroExtensionMap_id, mappingCone.map_id]

/-- 原Fiber錐の台制限の合成則。 -/
theorem supportFiberCone_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    supportFiberCone M hbc ≫ supportFiberCone M hab = supportFiberCone M (hab.trans hbc) := by
  have ha := congrArg zeroExtensionMap (supportPushforwardHom_comp M hab hbc)
  have hb := congrArg zeroExtensionMap (subsetRestrictHom_comp Nf
    (A := comparisonFactor qc qf h ⁻¹' A) (B := comparisonFactor qc qf h ⁻¹' B)
    (C := comparisonFactor qc qf h ⁻¹' C) (fun _ ht => hab ht) (fun _ ht => hbc ht))
  rw [zeroExtensionMap_comp] at ha hb
  dsimp only [supportFiberCone]
  rw [← mappingCone.map_comp]
  simp only [ha, hb]

/-- 原Total錐の台制限の恒等則。 -/
theorem supportTotalCone_refl (A : Set qc.Target) :
    supportTotalCone M (Set.Subset.refl A) = 𝟙 _ := by
  simp only [supportTotalCone, subsetRestrictHom_refl, zeroExtensionMap_id, mappingCone.map_id]

/-- 原Total錐の台制限の合成則。 -/
theorem supportTotalCone_comp {C : Set qc.Target} (hbc : B ⊆ C) :
    supportTotalCone M hbc ≫ supportTotalCone M hab = supportTotalCone M (hab.trans hbc) := by
  have ha := congrArg zeroExtensionMap (subsetRestrictHom_comp Nc hab hbc)
  have hb := congrArg zeroExtensionMap (subsetRestrictHom_comp Nf
    (A := comparisonFactor qc qf h ⁻¹' A) (B := comparisonFactor qc qf h ⁻¹' B)
    (C := comparisonFactor qc qf h ⁻¹' C) (fun _ ht => hab ht) (fun _ ht => hbc ht))
  rw [zeroExtensionMap_comp] at ha hb
  dsimp only [supportTotalCone]
  rw [← mappingCone.map_comp]
  simp only [ha, hb]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportStandardUnit
#print axioms AAT.AG.AtlasCoefficientFiber.supportStandardEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.supportStandardDirect
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientCone
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberCone
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportTotalCone
#print axioms AAT.AG.AtlasCoefficientFiber.supportTotalCone_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportConeTriangle_first
#print axioms AAT.AG.AtlasCoefficientFiber.supportConeTriangle_second
#print axioms AAT.AG.AtlasCoefficientFiber.supportConeShift_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportConeTriangle_third
#print axioms AAT.AG.AtlasCoefficientFiber.supportConeTriangle
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberConeHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberConeConnecting
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientCone_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportCoefficientCone_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberCone_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberCone_comp
#print axioms AAT.AG.AtlasCoefficientFiber.supportTotalCone_refl
#print axioms AAT.AG.AtlasCoefficientFiber.supportTotalCone_comp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
