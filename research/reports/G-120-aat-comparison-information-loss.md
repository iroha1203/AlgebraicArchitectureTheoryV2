# G-120 — Comparison information preservation and loss

一次仕様は
[`research/goals/G-120-aat-comparison-information-loss.md`](../goals/G-120-aat-comparison-information-loss.md)
である。本 report は固定 target A--D の proof obligation、Lean 宣言、前提の出所、
proof-use、検証、査読結果を cycle ごとに記録する。

## Proof state

- fixed base: `b56be2b938dd8f7d62647111980d768a35527dde`
- fixed GOAL blob: `fdf55308582fabca2ffecf085a959e3be02fed43`
- common criteria base: `b56be2b938dd8f7d62647111980d768a35527dde`
- acceptance contract blob: `eb8e1b230e1106cc3d2c826a037578d8dfea7a1f`
- tracking Issue: [#4443](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4443)
- current proof obligation: B4, transport the generated-comparison observation-loss diagram across arbitrary fixed G-118 C1s presentation changes
- pending proof obligations: B--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B4, construct endpoint, kernel, compatible-kernel, quotient, and Psi transport with identity/inverse/composition coherence

## Cycle 1 — Observation kernel criterion and pointed quotient

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 1
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: b56be2b938dd8f7d62647111980d768a35527dde
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Issue #4443 initial proof state: A--D unproved"
  proof_dag_predecessors:
    - Mathlib.GroupTheory.Coset.Basic
    - Mathlib.Algebra.Group.Subgroup.Pointwise
  proof_obligation: "A1: prove the observation-kernel decision criterion, saturation formula, compatible fibers, and pointed left-coset singleton criterion"
  selection_reason: "A1 is the common predecessor for the endpoint-kernel classification in B and for every later observation-loss application."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean
    - AAT.AG.ComparisonInformationLoss.exists_observation_predicate_iff_ker_le
  risks:
    - "silently assuming observation surjectivity"
    - "requiring normality of the compatible-kernel subgroup"
    - "confusing the left-coset relation with a quotient group"
    - "replacing the set product Gamma K by an unrelated generated subgroup"
  unchecked:
    - "A2 observation-diagram transport and coherence"
    - "B--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Proved the kernel criterion without surjectivity, identified the observation saturation with both Gamma join ker(O) and the set product Gamma ker(O), computed fibers and compatible fibers, and identified the pointed left-coset obstruction with kernel containment and observation-only decision."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.compatibleKernel
    - AAT.AG.ComparisonInformationLoss.exists_observation_predicate_iff_ker_le
    - AAT.AG.ComparisonInformationLoss.preimage_image_eq_sup_ker
    - AAT.AG.ComparisonInformationLoss.preimage_image_eq_mul_ker
    - AAT.AG.ComparisonInformationLoss.observation_fiber_eq_leftCoset
    - AAT.AG.ComparisonInformationLoss.observation_fiber_inter_eq_leftCoset
    - AAT.AG.ComparisonInformationLoss.mul_mem_iff_kernel_coset_basepoint
    - AAT.AG.ComparisonInformationLoss.subsingleton_kernel_quotient_iff_ker_le
    - AAT.AG.ComparisonInformationLoss.subsingleton_kernel_quotient_iff_exists_observation_predicate
  claim_mapping:
    theorem_names:
      - exists_observation_predicate_iff_ker_le
      - preimage_image_eq_sup_ker
      - preimage_image_eq_mul_ker
      - observation_fiber_eq_leftCoset
      - observation_fiber_inter_eq_leftCoset
      - mul_mem_iff_kernel_coset_basepoint
      - subsingleton_kernel_quotient_iff_ker_le
      - subsingleton_kernel_quotient_iff_exists_observation_predicate
    source_labels:
      - "fixed target A: observation-only decision and saturation"
      - "fixed target A: fibers and pointed left-coset obstruction"
    conjuncts:
      - "existence of h with membership determined by O iff ker(O) <= Gamma"
      - "O^-1(O(Gamma)) = Gamma ker(O), with the product represented by the subgroup join because ker(O) is normal"
      - "O^-1({O(gamma)}) = gamma ker(O)"
      - "the compatible part of the fiber is gamma (ker(O) intersection Gamma)"
      - "gamma k is compatible iff k has the basepoint class"
      - "the left-coset set ker(O)/compatibleKernel is a singleton iff the kernel criterion holds"
    undischarged_assumptions: []
    acceptance_point: "A1 is universe-polymorphic, does not assume O surjective or compatibleKernel normal, and proves the stated set-level and pointed-set conclusions from group laws alone."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A observation-only decision criterion"
      - "A saturation, fiber, compatible-fiber, and pointed-singleton claims"
    remaining:
      - "A transport and identity/composition coherence"
      - "all B--D construction obligations"
  certificate_provenance:
    discharged: []
    unresolved: []
  proof_use:
    used:
      - "kernel membership in both directions of observation factorization"
      - "normality of a homomorphism kernel in the subgroup-product equality"
      - "Gamma membership of gamma in the compatible-fiber and basepoint criteria"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean; exit 0"
    - "all 10 declarations #print axioms: standard axioms only (propext, Classical.choice, Quot.sound as applicable)"
    - "git diff --check, placeholder, hidden/BiDi, privacy, and reverse-import scans; no findings"
  blocking_findings: []
  next_obligation: "A2: construct transport of kernels, intersections, observation fibers, and pointed quotient sets under commuting group equivalences, including identity and composition coherence"
```

### Cycle 1 acceptance spine

`compatibleKernel O Gamma` は `O.ker` の内部で `Gamma` を読む部分群であり、正規性を
仮定しない。判定述語の逆向きは観測値を持つ `Gamma` の元の存在として直接構成し、
全射性を用いない。saturation は `Gamma ⊔ O.ker` として部分群性を固定し、核の正規性から
その underlying set を積 `Gamma * O.ker` と同定する。最後に一般の左剰余類型
`O.ker ⧸ compatibleKernel O Gamma` を用い、群構造を要求せず基点クラスとの一致と
singleton条件を証明する。

Cycle 1 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の群 `Q,R`、群準同型 `O : Q →* R`、部分群 `Gamma ≤ Q`。
  fiber と基点の定理では、固定 target 由来の `gamma : Q`、`hgamma : gamma ∈ Gamma`、
  `k : O.ker` も入力として保持する。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加 premise なし。
- `conclusion-equivalent-risk`: 該当なし。

## Cycle 2 — Observation-diagram transport and coherence

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 2
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 5c4286fba0b15fad040aba911c2b960ccb8903df
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Issue #4443 Cycle 1: A1 discharged; A2 selected"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.compatibleKernel
    - Mathlib.GroupTheory.Coset.Basic
    - Mathlib.Algebra.Group.Subgroup.Map
  proof_obligation: "A2: transport kernels, intersections, observation fibers, compatible fiber parts, and pointed left-coset sets along commuting group equivalences, with identity and composition coherence"
  selection_reason: "A2 completes the general theorem package needed before the generated-comparison application in B can reuse its quotient and transport constructions."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv
  risks:
    - "stating kernel transport as a supplied certificate instead of deriving it from the commuting observation square"
    - "requiring normality of the compatible kernel"
    - "transporting only representatives without quotient well-definedness"
    - "recording pointwise formulas without identity/composition coherence"
  unchecked:
    - "B--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed observation-diagram identity and composition, induced equivalences on kernels and compatible kernels, observation fibers and their compatible parts, and the pointed left-coset set. Proved representative/basepoint evaluations and identity/composition coherence for every induced transport."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.kernelEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleKernelEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.fiberEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleFiberEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv_mk
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv_basepoint
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.kernelEquiv_refl
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.kernelEquiv_trans
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleKernelEquiv_refl
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleKernelEquiv_trans
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.fiberEquiv_refl
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.fiberEquiv_trans
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleFiberEquiv_refl
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.compatibleFiberEquiv_trans
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv_refl
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.quotientEquiv_trans
  claim_mapping:
    theorem_names:
      - ObservationEquiv.refl
      - ObservationEquiv.trans
      - ObservationEquiv.mem_compatible_iff
      - ObservationEquiv.kernelEquiv
      - ObservationEquiv.compatibleKernelEquiv
      - ObservationEquiv.fiberEquiv
      - ObservationEquiv.compatibleFiberEquiv
      - ObservationEquiv.quotientEquiv
      - ObservationEquiv.quotientEquiv_mk
      - ObservationEquiv.quotientEquiv_basepoint
      - ObservationEquiv.kernelEquiv_refl
      - ObservationEquiv.kernelEquiv_trans
      - ObservationEquiv.compatibleKernelEquiv_refl
      - ObservationEquiv.compatibleKernelEquiv_trans
      - ObservationEquiv.fiberEquiv_refl
      - ObservationEquiv.fiberEquiv_trans
      - ObservationEquiv.compatibleFiberEquiv_refl
      - ObservationEquiv.compatibleFiberEquiv_trans
      - ObservationEquiv.quotientEquiv_refl
      - ObservationEquiv.quotientEquiv_trans
    source_labels:
      - "fixed target A: transport under commuting group equivalences"
      - "fixed target A: identity and composition coherence"
    conjuncts:
      - "O' phi = psi O and phi(Gamma)=Gamma' imply kernel and compatible-kernel group equivalences"
      - "kL maps to phi(k)L' and the basepoint maps to the basepoint"
      - "observation fibers and their compatible parts are transported"
      - "kernel, intersection, fiber, compatible-fiber, and pointed-quotient transports respect identity and composition"
    undischarged_assumptions: []
    acceptance_point: "The only proof fields in ObservationEquiv are exactly the two commuting conditions from fixed target A. Every transported conclusion is constructed from them, and the quotient uses the general left-coset relation without a normality premise."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "A transport of kernels and compatible intersections"
      - "A transport of observation fibers and compatible parts"
      - "A pointed left-coset equivalence with representative and basepoint evaluations"
      - "A identity/composition coherence for all induced transports"
    remaining:
      - "all B--D construction obligations"
  certificate_provenance:
    discharged:
      - "kernel membership is derived from ObservationEquiv.observation_comm"
      - "compatible membership is derived from ObservationEquiv.compatible_map"
    unresolved: []
  proof_use:
    used:
      - "observation_comm in both directions of kernel and fiber transport"
      - "compatible_map in compatible-kernel and compatible-fiber transport"
      - "leftRel membership in both directions of quotient well-definedness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "direct predecessor targeted build: ResearchLean.AG.ComparisonInformationLoss.ObservationKernel; exit 0"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean; exit 0"
    - "permanent namespace audit: 40 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B1: construct Q_c, Gamma_c, O_c and endpoint observation conjugacy for each generated comparison"
```

### Cycle 2 acceptance spine

`ObservationEquiv` は固定 target A が仮定する `phi,psi,O,O',Gamma,Gamma'` と二つの
可換条件だけを保持する。`kernelEquiv` は観測可換式から核所属を導出し、
`compatibleKernelEquiv` は部分群のmap等式から交わりを輸送する。fiber と適合部分は
定義predicateのsubtypeとして両方向に運び、`quotientEquiv` は一般左剰余類relationの
well-definednessを両方向で証明して `kL` を `phi(k)L'` へ送る。核、交わり、fiber、
適合fiber、基点付き剰余類の各構成について恒等・合成との一致を別定理で固定した。

Cycle 2 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の群 `Q,R,Q',R'`、群準同型 `O,O'`、部分群 `Gamma,Gamma'`、
  群同型 `phi,psi`。
- `direction-hypothesis`: `O' phi = psi O` と `phi(Gamma)=Gamma'`。
- `discharge-required`: 追加 premise なし。
- `conclusion-equivalent-risk`: 可換条件が輸送結論を直接保持していないことを、核・fiber・
  quotientの各proof termで確認する。

## Cycle 3 — Generated-comparison observation diagram and endpoint kernels

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 3
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 613c1f7c535b46ca9d10f931fc43a111ed7e50fe
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 2 accepted A2; B--D remained"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.exists_observation_predicate_iff_ker_le
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.kernelEquiv
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedPairCoefficientObservationAt
    - AAT.AG.DoctrineFiberProduct.qualifiedComparisonSubgroup
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleProblemInputData.generatedCompatibleUpperGeometryMateAt_isIso
    - AAT.AG.DoctrineFiberProduct.CompositeFiberAut.conjugationMulEquiv
  proof_obligation: "B1: construct Q_c, Gamma_c, O_c, K_c, L_c and the pointed quotient for each generated comparison, and prove coefficient-observation conjugacy and the induced endpoint-kernel equivalence"
  selection_reason: "B1 supplies the concrete generated-comparison diagram and endpoint kernel transport required before the graph and quotient classification in B2."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/GeneratedComparisonObservation.lean
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointObservationKernelEquivAt
  risks:
    - "replacing the actual generated comparison coefficient map by a chosen identity"
    - "assuming the generated comparison itself fixes the base"
    - "storing endpoint-kernel transport as an input certificate"
    - "reversing the categorical conjugation order"
  unchecked:
    - "B2 product-kernel and graph identifications and Psi"
    - "B fixed witness and presentation-change compatibility"
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Instantiated the product change group, comparison-preserving subgroup, product coefficient observation, its kernel, compatible kernel, and pointed left-coset obstruction at every generated comparison. Constructed the actual coefficient-ring equivalence from the generated comparison and its inverse, proved endpoint conjugation commutes with coefficient observation, and restricted it to an endpoint-kernel group equivalence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/GeneratedComparisonObservation.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.compatibleSubgroupAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationKernelAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.compatibleKernelAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.exists_observation_predicate_iff_kernel_leAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.comparisonIsoAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.comparisonCoefficientIsoAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointChangeEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointObservationEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointObservation_commutesAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointObservationKernelEquivAt
  claim_mapping:
    theorem_names:
      - exists_observation_predicate_iff_kernel_leAt
      - comparisonCoefficientIsoAt_hom
      - coefficientObservation_conjugation
      - endpointChangeEquivAt_hom
      - endpointObservation_commutesAt
      - endpointObservationKernelEquivAt
      - endpointObservationKernelEquivAt_apply
    source_labels:
      - "fixed target B: generated-comparison observation diagram"
      - "fixed target B: comparison-induced endpoint observation conjugacy"
    conjuncts:
      - "Q_c is the product of the two generated endpoint CompositeFiberAut groups"
      - "Gamma_c is the existing qualifiedComparisonSubgroup and O_c is the existing product coefficient observation"
      - "K_c, L_c, and K_c/L_c are obtained by the general clause-A construction"
      - "the coefficient-ring isomorphism has the actual generated comparison coefficient map as its forward map"
      - "T_c has underlying ordinary composite c b c^-1 and commutes with coefficient observation through coefficient conjugation S_c"
      - "T_c restricts to a group equivalence of endpoint observation kernels"
    undischarged_assumptions: []
    acceptance_point: "The only isomorphism premise is the already proved generated-comparison IsIso theorem. The coefficient equivalence is constructed from the actual forward and inverse coefficient maps, and kernel transport is derived via ObservationEquiv.kernelEquiv."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B generated-comparison observation diagram"
      - "B endpoint coefficient-observation conjugacy"
      - "B induced endpoint observation-kernel group equivalence"
    remaining:
      - "B product kernel, graph subgroup, Psi, and fixed witness"
      - "B presentation-change compatibility"
      - "all C--D construction obligations"
  certificate_provenance:
    discharged:
      - "generated comparison invertibility comes from generatedCompatibleUpperGeometryMateAt_isIso"
      - "coefficient inverse laws come from the actual comparison Iso hom_inv_id and inv_hom_id"
      - "endpoint kernel membership is derived from the commuting observation square"
    unresolved: []
  proof_use:
    used:
      - "existing generatedPairCoefficientObservationAt as O_c"
      - "existing qualifiedComparisonSubgroup as Gamma_c"
      - "actual comparison hom and inverse coefficient maps in comparisonCoefficientIsoAt"
      - "existing composite-fiber conjugation in T_c"
      - "coefficient-observation commutation in the restriction to endpoint kernels"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted predecessor build: ResearchLean.AG.ComparisonInformationLoss.ObservationTransport; exit 0"
    - "targeted predecessor build: ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientTransport; exit 0"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/GeneratedComparisonObservation.lean; exit 0"
    - "permanent namespace audit: 20 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B2: identify K_c as the endpoint-kernel product and L_c as the graph of T_c, then construct Psi"
```

### Cycle 3 acceptance spine

`ChangeGroupAt`、`compatibleSubgroupAt`、`observationAt` は G-118 の生成端点対、既存の
`qualifiedComparisonSubgroup`、既存の `generatedPairCoefficientObservationAt` を変更せず
用いる。`comparisonIsoAt` は既存の生成比較そのものを `asIso` で包み、
`comparisonCoefficientIsoAt_hom` は係数環同型の forward map がその実係数写像であることを
固定する。`coefficientObservation_conjugation` は complete-geometry 共役と係数環共役の
可換式を実係数成分で証明し、その可換式から `endpointObservationKernelEquivAt` を導出する。
したがって、端点核同型は field や supplied certificate ではない。

Cycle 3 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U,ctx,P,k,input,i` と、それらから生成された比較・端点。
- `direction-hypothesis`: なし。
- `discharge-required`: 生成比較の同型性。既存の
  `generatedCompatibleUpperGeometryMateAt_isIso` で放電する。
- `conclusion-equivalent-risk`: 核同型を入力せず、比較共役と係数観測可換式から構成する。

## Cycle 4 — Endpoint-kernel graph and pointed quotient classification

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 4
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: b94bcaf00687ad26ce354b004947c73eb3afd861
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 3 accepted the generated-comparison observation diagram and endpoint kernel transport; B2 remained"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationKernelAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.compatibleKernelAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointObservationKernelEquivAt
    - AAT.AG.ComparisonInformationLoss.subsingleton_kernel_quotient_iff_ker_le
  proof_obligation: "B2: identify K_c with the endpoint-kernel product, identify L_c with the graph of comparison conjugation, construct Psi([a,b]) = b T_c(a)^-1 and its inverse, and derive the exact target-kernel criterion"
  selection_reason: "B2 is the fixed algebraic classification needed to read the concrete witness in B3 and to state presentation-change compatibility in B4."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt
  risks:
    - "silently replacing the actual product observation kernel by a definitionally different product"
    - "assuming normality of the compatible kernel or giving the coset set a quotient-group structure"
    - "orienting the graph relation or conjugation inverse incorrectly"
    - "proving only an abstract cardinality statement without the required representative and inverse formulas"
  unchecked:
    - "B3 fixed finite witness"
    - "B4 presentation-change compatibility"
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed an underlying-pair-preserving group equivalence K_X^obs x K_Y^obs ≃ K_c, proved that the pullback of L_c is exactly the graph of T_c, and classified its general pointed left-coset set by K_Y^obs with the required representative, inverse, and basepoint formulas. Derived that observation-only compatibility is possible exactly when every target endpoint kernel element is the identity."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.PointedLeftCoset.equivOfMapEq
    - AAT.AG.ComparisonInformationLoss.PointedLeftCoset.graphQuotientEquiv
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.endpointKernelProductEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.compatibleKernelInEndpointProductAt_eq_graph
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt_mk
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt_symm_apply
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt_basepoint
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.exists_observation_predicate_iff_targetKernel_eq_one
  claim_mapping:
    theorem_names:
      - endpointKernelProductEquivAt
      - compatibleKernelInEndpointProductAt_eq_graph
      - observationLossEquivTargetKernelAt
      - observationLossEquivTargetKernelAt_mk
      - observationLossEquivTargetKernelAt_symm_apply
      - observationLossEquivTargetKernelAt_basepoint
      - exists_observation_predicate_iff_targetKernel_eq_one
    source_labels:
      - "fixed target B: K_c endpoint-product and L_c graph identifications"
      - "fixed target B: pointed quotient classification Psi"
      - "fixed target B: observation-only iff target observation kernel trivial"
    conjuncts:
      - "K_c is identified with K_X^obs x K_Y^obs while preserving its actual endpoint pair"
      - "the transported L_c is exactly graph(T_c)"
      - "Psi sends [(a,b)] to b T_c(a)^-1, has inverse u maps to [(1,u)], and preserves the basepoint"
      - "an observation-only predicate exists iff every element of K_Y^obs equals 1"
    undischarged_assumptions: []
    acceptance_point: "The quotient remains the general left-coset set. The graph equality is proved from actual qualified-comparison membership, and both directions of Psi are explicit rather than inferred from cardinality."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B product observation-kernel identification"
      - "B compatible-kernel graph identification"
      - "B pointed quotient classification and exact target-kernel criterion"
    remaining:
      - "B3 fixed finite witness"
      - "B4 presentation-change compatibility"
      - "all C--D construction obligations"
  certificate_provenance:
    discharged:
      - "endpoint factor membership is projected from actual product-observation kernel membership"
      - "graph membership is derived from the existing qualifiedComparisonSubgroup equation"
      - "target kernel transport is the Cycle 3 equivalence derived from coefficient-observation conjugacy"
    unresolved: []
  proof_use:
    used:
      - "actual observationKernelAt and compatibleKernelAt subgroups"
      - "endpointObservationKernelEquivAt in the graph and representative formula"
      - "general leftRel membership for both quotient transports"
      - "Cycle 1 observation predicate and singleton quotient criterion"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean; exit 0"
    - "permanent namespace audits: PointedLeftCoset 5 declarations and GeneratedComparison 14 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "B3: construct the fixed q+/q- witness, prove a nonbasepoint loss class and nonfactorization, and exhibit a nonidentity Psi value"
```

### Cycle 4 acceptance spine

`endpointKernelProductEquivAt` は `K_c` の実要素から両端点への射影で核所属を導出し、
逆向きには二つの端点核所属から既存の積観測の核所属を構成する。
`compatibleKernelInEndpointProductAt_eq_graph` は `L_c` の既存
`qualifiedComparisonSubgroup` 方程式を両方向に使って graph 等式を証明する。
一般補題 `graphQuotientEquiv` は正規性を仮定せず、左剰余類 relation 上で
`[(a,b)] ↦ b * T(a)⁻¹` の well-definedness と逆写像 `u ↦ [(1,u)]` を直接証明する。
このため `observationLossEquivTargetKernelAt` は抽象的な濃度比較ではなく、固定 target の
代表元公式と基点を保持する `Psi` そのものである。

Cycle 4 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U,ctx,P,k,input,i` と、それらから生成された比較・端点。
- `direction-hypothesis`: なし。
- `discharge-required`: 追加 premise なし。Cycle 3 の実比較由来端点核同型を再利用する。
- `conclusion-equivalent-risk`: graph 等式や `Psi` を field として受け取らず、既存の
  product observation と qualified-comparison 方程式から構成する。

## Cycle 5 — Fixed coefficient-invisible loss witness

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 5
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 40439e15f3cf0872cf942a96b51a48898cde9052
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 4 accepted the endpoint-kernel quotient classification; B3 remained"
  proof_dag_predecessors:
    - AAT.AG.DoctrineFiberProduct.UpperDecisionWitness.fixedCoefficientObservation_positive_eq_negative
    - AAT.AG.DoctrineFiberProduct.UpperDecisionWitness.fixedPositiveQualifiedDecision
    - AAT.AG.DoctrineFiberProduct.UpperDecisionWitness.fixedNegativeNotQualifiedDecision
    - AAT.AG.ComparisonInformationLoss.mul_mem_iff_kernel_coset_basepoint
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt_mk
  proof_obligation: "B3: reuse the fixed q+/q- generated-comparison witness, construct k*=q+^-1 q- in K* outside Gamma*, prove its loss class is nonbasepoint, recover the fixed nonfactorization through A, and prove Psi*(k*L*) != 1"
  selection_reason: "B3 is the fixed finite witness required to show that the general B2 obstruction is realized by the existing G-118 example rather than by a replacement example."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/FixedWitness.lean
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_Psi_ne_one
  risks:
    - "replacing the fixed G-118 positive or negative pair"
    - "asserting kernel membership without using the coefficient-observation collision"
    - "deriving nonfactorization only by aliasing the predecessor theorem rather than through clause A"
    - "proving Psi nontriviality without connecting it to the explicit representative evaluation"
  unchecked:
    - "B4 presentation-change compatibility"
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Reused the exact fixed q+ and q- pairs, derived their actual generated observation collision and qualified/nonqualified separation, constructed k*=q+^-1 q- as an element of K* outside Gamma* and L*, proved k*L* differs from the basepoint, rederived the existing nonfactorization statement through the clause-A kernel criterion, and proved the explicitly evaluated Psi value is nonidentity."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/FixedWitness.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedPositiveChange_mem_compatible
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedNegativeChange_not_mem_compatible
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedObservation_positive_eq_negative
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_not_mem_compatible
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_not_mem_compatibleKernel
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_coset_ne_basepoint
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedQualifiedDecision_not_factor_via_observationKernel
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_Psi_value
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_Psi_formula_ne_one
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.fixedKernelChange_Psi_ne_one
  claim_mapping:
    theorem_names:
      - fixedPositiveChange_mem_compatible
      - fixedNegativeChange_not_mem_compatible
      - fixedObservation_positive_eq_negative
      - fixedKernelChange
      - fixedKernelChange_not_mem_compatible
      - fixedKernelChange_coset_ne_basepoint
      - fixedQualifiedDecision_not_factor_via_observationKernel
      - fixedKernelChange_Psi_value
      - fixedKernelChange_Psi_formula_ne_one
      - fixedKernelChange_Psi_ne_one
    source_labels:
      - "fixed target B: named q+/q- coefficient collision and qualified separation"
      - "fixed target B: k*=q+^-1q- in K* outside Gamma* and nonbasepoint loss class"
      - "fixed target B: nonfactorization via clause A and nonidentity Psi value"
    conjuncts:
      - "the exact pre-existing fixed positive and negative pairs are used"
      - "q+ is compatible, q- is not, and O*(q+)=O*(q-)"
      - "k*=q+^-1q- belongs to K* but not Gamma* or L*"
      - "k*L* is not the basepoint"
      - "the original fixed decision cannot factor through O*, derived from A's kernel criterion"
      - "the representative formula evaluates Psi*(k*L*) to a nonidentity target-kernel element"
    undischarged_assumptions: []
    acceptance_point: "The witness declarations are abbreviations of the exact existing G-118 pairs. Kernel membership is proved from their existing observation equality; all separation consequences are then derived rather than stored."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B fixed q+/q- coefficient collision and compatibility separation"
      - "B fixed kernel element outside Gamma and compatible kernel"
      - "B nonbasepoint loss class, nonfactorization, and nonidentity Psi value"
    remaining:
      - "B4 presentation-change compatibility"
      - "all C--D construction obligations"
  certificate_provenance:
    discharged:
      - "q+/q- are definitionally the pre-existing UpperDecisionWitness pairs"
      - "kernel membership is derived from fixedCoefficientObservation_positive_eq_negative"
      - "compatible separation is inherited from the existing literal qualified-subgroup membership proofs"
    unresolved: []
  accepted_dependencies:
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonCoefficientNonfactorization.lean"
      blob_at_base: fba42ec0a608b42696fecfa58edc7304fc62b73c
      accepted_head: 1f97320f378f4b301d507a969a88a939bcf50110
      accepted_pr: 4378
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4378#issuecomment-5550849734"
      use: "fixed q+/q- definitions, coefficient collision, and literal compatible/noncompatible proofs"
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean"
      blob_at_base: 68a333ba31071e6cef39dec171750e5e6ba1a454
      accepted_pr: 4445
      use: "clause-A kernel containment and basepoint criteria"
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean"
      blob_at_base: a5cf9d624e6f1b220b1065a219c111b74113d077
      accepted_pr: 4450
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4450#issuecomment-5622324810"
      use: "Psi representative and basepoint formulas"
  proof_use:
    used:
      - "fixed positive compatible membership and fixed negative nonmembership"
      - "fixed product coefficient-observation collision"
      - "clause-A basepoint and kernel-containment criteria"
      - "Cycle 4 Psi representative and basepoint evaluations"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted predecessor build: ResearchLean.AG.ComparisonInformationLoss.EndpointKernelClassification; exit 0"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/FixedWitness.lean; exit 0"
    - "permanent namespace audit: 15 declarations, standard axioms only"
    - "accepted fixed-witness predecessor: PR #4378 head 1f97320f378f4b301d507a969a88a939bcf50110, fixed-base blob fba42ec0a608b42696fecfa58edc7304fc62b73c"
  blocking_findings: []
  next_obligation: "B4: transport the generated comparison observation-loss diagram and Psi across arbitrary fixed G-118 C1s presentation changes, with identity, inverse, and finite-composition coherence"
```

### Cycle 5 acceptance spine

`fixedPositiveChange` と `fixedNegativeChange` は G-118 の既存固定対の abbreviation であり、
新しい有限例を選ばない。既存の係数観測衝突を群準同型の積・逆元へ適用して
`fixedKernelChange : K_*` を構成し、`q_+ k_* = q_-` と正負の membership separation から
`k_* ∉ Γ_*` を導く。A の基点判定は `k_*L_* ≠ L_*` を与え、A の kernel containment
判定は既存と同じ非因子化 statement を別経路で与える。最後に B2 の代表元評価式と
基点保存を用い、`Psi_*(k_*L_*) ≠ 1` を証明する。

Cycle 5 の material premise role は次のとおりである。

- `ambient-boundary`: G-118 で固定済みの `problem.data` と頂点 `PUnit.unit`。
- `direction-hypothesis`: なし。
- `discharge-required`: `q_+∈Γ_*`、`q_-∉Γ_*`、`O_*(q_+)=O_*(q_-)`。いずれも既存の
  `UpperDecisionWitness` 定理で放電する。
- `conclusion-equivalent-risk`: 非因子化を predecessor theorem の alias とせず、構成した
  `k_*` と A の必要十分条件から再導出する。
