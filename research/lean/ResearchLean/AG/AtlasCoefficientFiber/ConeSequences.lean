import ResearchLean.AG.AtlasCoefficientFiber.CoefficientCones
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence

/-!
# G-135 C：原三錐の全整数次数の実短完全列

## Implementation notes

原η・独立u・原εの同じ標準homology射へG133のcone_short_exactを適用する。
包含は実target包含から余核へ降ろし、射影は同じ標準連結射を次核へ制限する。
次数0の余核、次数2の核などを仮定で消去しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition CochainComplex HomologicalComplex
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原三射の各次数の余核・錐homology・次核は同時に短完全列をなす。 -/
theorem threeCones_shortExact (n : ℤ) :
    (coneShortComplex (zeroExtensionMap (unitHom M A)) n).ShortExact ∧
    (coneShortComplex (zeroExtensionMap (M.aSubnerveComparisonHom A)) n).ShortExact ∧
    (coneShortComplex (zeroExtensionMap (evaluationHom M A)) n).ShortExact :=
  ⟨cone_short_exact _ n, cone_short_exact _ n, cone_short_exact _ n⟩

/-- 同じ原coefficient錐の余核包含は全商代表で実target包含を返す。 -/
@[simp] theorem coefficientConeCokernelInclusion_mk (n : ℤ) (y : (zeroExtension (pushforwardComplex M A)).homology n) :
    coneCokernelInclusion (zeroExtensionMap (unitHom M A)) n
      ((LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) n).hom).mkQ y) =
        HomologicalComplex.homologyMap (mappingCone.inr (zeroExtensionMap (unitHom M A))) n y :=
  coneCokernelInclusion_mk _ n y

/-- 同じ原coefficient錐の次核射影は全元で標準連結射の値を保つ。 -/
@[simp] theorem coefficientConeKernelProjection_val (n : ℤ) (y : (coefficientCone M A).homology n) :
    (coneKernelProjection (zeroExtensionMap (unitHom M A)) n y).1 = coneConnecting (zeroExtensionMap (unitHom M A)) n y :=
  coneKernelProjection_val _ n y

/-- 同じ原coefficient錐の余核包含は全整数次数で単射。 -/
theorem coefficientConeCokernelInclusion_injective (n : ℤ) :
    Function.Injective (coneCokernelInclusion (zeroExtensionMap (unitHom M A)) n) :=
  coneCokernelInclusion_injective _ n

/-- 同じ原coefficient錐の核射影は全整数次数で全射。 -/
theorem coefficientConeKernelProjection_surjective (n : ℤ) :
    Function.Surjective (coneKernelProjection (zeroExtensionMap (unitHom M A)) n) :=
  coneKernelProjection_surjective _ n

/-- 同じ原coefficient錐の余核包含と核射影の完全性。 -/
theorem coefficientCone_function_exact (n : ℤ) :
    Function.Exact (coneCokernelInclusion (zeroExtensionMap (unitHom M A)) n) (coneKernelProjection (zeroExtensionMap (unitHom M A)) n) :=
  cone_short_function_exact _ n

/-- 原coefficient錐homologyの全次数加法式は余核と次核の両寄与を保つ。 -/
theorem coefficientCone_homology_dimension (n : ℤ) :
    Module.finrank ℚ ((coefficientCone M A).homology n) =
      Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology n ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) n).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) (n+1)).hom) :=
  cone_homology_dimension _ n

/-- 原coefficient錐の次数0もH⁰余核とH¹核の両寄与を保持する。 -/
theorem coefficientCone_H0_dimension :
    Module.finrank ℚ ((coefficientCone M A).homology (0 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (0 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) (0 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) (1 : ℤ)).hom) :=
  coefficientCone_homology_dimension M A 0

/-- 原coefficient錐の次数1もH¹余核とH²核の両寄与を保持する。 -/
theorem coefficientCone_H1_dimension :
    Module.finrank ℚ ((coefficientCone M A).homology (1 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) (1 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) (2 : ℤ)).hom) :=
  coefficientCone_homology_dimension M A 1

/-- 同じ原total錐の余核包含は全商代表で実target包含を返す。 -/
@[simp] theorem totalConeCokernelInclusion_mk (n : ℤ) (y : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n) :
    coneCokernelInclusion (zeroExtensionMap (M.aSubnerveComparisonHom A)) n
      ((LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) n).hom).mkQ y) =
        HomologicalComplex.homologyMap (mappingCone.inr (zeroExtensionMap (M.aSubnerveComparisonHom A))) n y :=
  coneCokernelInclusion_mk _ n y

/-- 同じ原total錐の次核射影は全元で標準連結射の値を保つ。 -/
@[simp] theorem totalConeKernelProjection_val (n : ℤ) (y : (totalCone M A).homology n) :
    (coneKernelProjection (zeroExtensionMap (M.aSubnerveComparisonHom A)) n y).1 = coneConnecting (zeroExtensionMap (M.aSubnerveComparisonHom A)) n y :=
  coneKernelProjection_val _ n y

/-- 同じ原total錐の余核包含は全整数次数で単射。 -/
theorem totalConeCokernelInclusion_injective (n : ℤ) :
    Function.Injective (coneCokernelInclusion (zeroExtensionMap (M.aSubnerveComparisonHom A)) n) :=
  coneCokernelInclusion_injective _ n

/-- 同じ原total錐の核射影は全整数次数で全射。 -/
theorem totalConeKernelProjection_surjective (n : ℤ) :
    Function.Surjective (coneKernelProjection (zeroExtensionMap (M.aSubnerveComparisonHom A)) n) :=
  coneKernelProjection_surjective _ n

/-- 同じ原total錐の余核包含と核射影の完全性。 -/
theorem totalCone_function_exact (n : ℤ) :
    Function.Exact (coneCokernelInclusion (zeroExtensionMap (M.aSubnerveComparisonHom A)) n) (coneKernelProjection (zeroExtensionMap (M.aSubnerveComparisonHom A)) n) :=
  cone_short_function_exact _ n

/-- 原total錐homologyの全次数加法式は余核と次核の両寄与を保つ。 -/
theorem totalCone_homology_dimension (n : ℤ) :
    Module.finrank ℚ ((totalCone M A).homology n) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) n).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (n+1)).hom) :=
  cone_homology_dimension _ n

/-- 原total錐の次数0もH⁰余核とH¹核の両寄与を保持する。 -/
theorem totalCone_H0_dimension :
    Module.finrank ℚ ((totalCone M A).homology (0 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (0 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (0 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (1 : ℤ)).hom) :=
  totalCone_homology_dimension M A 0

/-- 原total錐の次数1もH¹余核とH²核の両寄与を保持する。 -/
theorem totalCone_H1_dimension :
    Module.finrank ℚ ((totalCone M A).homology (1 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (1 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) (2 : ℤ)).hom) :=
  totalCone_homology_dimension M A 1

/-- 同じ原fiber錐の余核包含は全商代表で実target包含を返す。 -/
@[simp] theorem fiberConeCokernelInclusion_mk (n : ℤ) (y : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n) :
    coneCokernelInclusion (zeroExtensionMap (evaluationHom M A)) n
      ((LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) n).hom).mkQ y) =
        HomologicalComplex.homologyMap (mappingCone.inr (zeroExtensionMap (evaluationHom M A))) n y :=
  coneCokernelInclusion_mk _ n y

/-- 同じ原fiber錐の次核射影は全元で標準連結射の値を保つ。 -/
@[simp] theorem fiberConeKernelProjection_val (n : ℤ) (y : (fiberCone M A).homology n) :
    (coneKernelProjection (zeroExtensionMap (evaluationHom M A)) n y).1 = coneConnecting (zeroExtensionMap (evaluationHom M A)) n y :=
  coneKernelProjection_val _ n y

/-- 同じ原fiber錐の余核包含は全整数次数で単射。 -/
theorem fiberConeCokernelInclusion_injective (n : ℤ) :
    Function.Injective (coneCokernelInclusion (zeroExtensionMap (evaluationHom M A)) n) :=
  coneCokernelInclusion_injective _ n

/-- 同じ原fiber錐の核射影は全整数次数で全射。 -/
theorem fiberConeKernelProjection_surjective (n : ℤ) :
    Function.Surjective (coneKernelProjection (zeroExtensionMap (evaluationHom M A)) n) :=
  coneKernelProjection_surjective _ n

/-- 同じ原fiber錐の余核包含と核射影の完全性。 -/
theorem fiberCone_function_exact (n : ℤ) :
    Function.Exact (coneCokernelInclusion (zeroExtensionMap (evaluationHom M A)) n) (coneKernelProjection (zeroExtensionMap (evaluationHom M A)) n) :=
  cone_short_function_exact _ n

/-- 原fiber錐homologyの全次数加法式は余核と次核の両寄与を保つ。 -/
theorem fiberCone_homology_dimension (n : ℤ) :
    Module.finrank ℚ ((fiberCone M A).homology n) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) n).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) (n+1)).hom) :=
  cone_homology_dimension _ n

/-- 原fiber錐の次数0もH⁰余核とH¹核の両寄与を保持する。 -/
theorem fiberCone_H0_dimension :
    Module.finrank ℚ ((fiberCone M A).homology (0 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (0 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) (0 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) (1 : ℤ)).hom) :=
  fiberCone_homology_dimension M A 0

/-- 原fiber錐の次数1もH¹余核とH²核の両寄与を保持する。 -/
theorem fiberCone_H1_dimension :
    Module.finrank ℚ ((fiberCone M A).homology (1 : ℤ)) =
      Module.finrank ℚ ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
        LinearMap.range (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) (1 : ℤ)).hom) +
      Module.finrank ℚ (LinearMap.ker (HomologicalComplex.homologyMap (zeroExtensionMap (evaluationHom M A)) (2 : ℤ)).hom) :=
  fiberCone_homology_dimension M A 1

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.threeCones_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConeCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConeKernelProjection_val
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConeCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConeKernelProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_function_exact
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_homology_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_H0_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCone_H1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.totalConeCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.totalConeKernelProjection_val
#print axioms AAT.AG.AtlasCoefficientFiber.totalConeCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.totalConeKernelProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_function_exact
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_homology_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_H0_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.totalCone_H1_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeKernelProjection_val
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeKernelProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_function_exact
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_homology_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_H0_dimension
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_H1_dimension
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
