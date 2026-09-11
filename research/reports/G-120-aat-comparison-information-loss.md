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
- current proof obligation: schema-complete final completion audit across A--D
- pending proof obligations: independent final Math 2 + Lean 2 completion review
- current target state: `target-theorem-completion-candidate`
- completion candidate: yes
- next proof obligation: assemble the final completion packet and run a fresh whole-GOAL `math-lean-review`

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

## Cycle 6 — Presentation-change transport and classification naturality

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 6
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 9fb71b290a5ecc41a4b87d59a48ce9033831c4a2
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 5 accepted the fixed nonbasepoint witness; B4 remained"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.observationLossEquivTargetKernelAt
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationChange.generatedEndpointPairMulEquivAt
    - AAT.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationChange.Chain.pastedEndpointPairMulEquivAt
  proof_obligation: "B4: transport the regenerated comparison observation diagram, K_c, L_c, pointed quotient, endpoint kernels, comparison conjugation, and Psi across arbitrary fixed G-118 C1s changes with identity, inverse, and finite typed-composition coherence"
  selection_reason: "B4 completes every generated-comparison obligation before the independent idempotent-image analysis in C."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/PresentationTransport.lean
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainObservationLossEquivTargetKernel_naturality
  risks:
    - "using a chosen coefficient identity without deriving it from the generated endpoint isomorphisms"
    - "transporting a supplied comparison rather than the comparison regenerated from changedInput"
    - "proving only one-step naturality without inverse or finite typed-composition coherence"
    - "replacing the general pointed left-coset set by a quotient group"
  unchecked:
    - "C--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the actual C1s endpoint and coefficient observation diagram from the regenerated comparison, transported K_c, L_c, and the pointed quotient, proved endpoint-kernel and comparison-conjugation naturality, and proved Psi naturality. Added identity, inverse, binary composition, and dependent finite-chain coherence for the observation diagram, both kernels, quotient, and target endpoint kernel."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationTransport.lean
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/PresentationTransport.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.symm
    - AAT.AG.ComparisonInformationLoss.ObservationEquiv.kernelEquiv_symm
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.coefficientObservationEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.coefficientObservationEquivAt_eq_refl
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.kernelEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.compatibleKernelEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.quotientEquivAt
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.endpointKernelConjugation_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.endpointKernelConjugation_inverse_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.endpointConjugation_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.endpointConjugation_inverse_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationLossEquivTargetKernel_equiv_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationLossEquivTargetKernel_inverse_equiv_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationEquivAt_identity
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationEquivAt_inverse
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.observationEquivAt_comp
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainObservationEquivAt_cons
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainKernelEquivAt_cons
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainCompatibleKernelEquivAt_cons
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainQuotientEquivAt_cons
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainTargetKernelEquivAt_cons
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainObservationLossEquivTargetKernel_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainObservationLossEquivTargetKernel_inverse_equiv_naturality
    - AAT.AG.ComparisonInformationLoss.GeneratedComparison.PresentationChange.chainEndpointConjugation_inverse_naturality
  claim_mapping:
    theorem_names:
      - coefficientObservationEquivAt_eq_refl
      - kernelEquivAt_product
      - endpointKernelConjugation_naturality
      - endpointConjugation_naturality
      - endpointConjugation_inverse_naturality
      - observationLossEquivTargetKernel_naturality
      - observationLossEquivTargetKernel_inverse_naturality
      - observationLossEquivTargetKernel_inverse_equiv_naturality
      - observationEquivAt_identity
      - observationEquivAt_inverse
      - observationEquivAt_comp
      - chainObservationEquivAt_eq_composite
      - chainKernelEquivAt_eq_composite
      - chainCompatibleKernelEquivAt_eq_composite
      - chainQuotientEquivAt_eq_composite
      - chainSourceEndpointEquivAt_coe_eq_recursive
      - chainTargetEndpointEquivAt_coe_eq_recursive
      - chainEndpointConjugation_naturality
      - chainEndpointConjugation_inverse_naturality
      - chainObservationLossEquivTargetKernel_naturality
      - chainObservationLossEquivTargetKernel_inverse_naturality
      - chainObservationLossEquivTargetKernel_inverse_equiv_naturality
    source_labels:
      - "fixed target B: arbitrary G-118 C1s presentation-change transport"
      - "fixed target B: theta_Y T_c = T_c' theta_X and Psi_c' phibar = theta_Y Psi_c"
      - "fixed target B: identity, inverse, and finite typed-composition coherence"
    conjuncts:
      - "the coefficient observation identification is induced by the two generated endpoint coefficient components and proved equal to identity from their hom/inv coefficient laws"
      - "the changed comparison is regenerated from changedInput, and its endpoint pair, product observation, K_c, L_c, and pointed quotient are transported"
      - "the full endpoint equivalences intertwine the changed and original comparison conjugations in both generated and inverse GOAL orientations; the kernel statement is their restriction"
      - "Psi naturality is proved in both directions, including the original-to-changed orientation and its finite-chain form"
      - "identity, inverse, binary composition, and every dependent finite chain agree with the actual generated/pasted endpoint actions"
    undischarged_assumptions: []
    acceptance_point: "All transports are constructed from existing C1s generated endpoint isomorphisms and their coefficient and qualified-subgroup theorems. No new hypothesis, chosen comparison, normality premise, or finite-carrier restriction is added."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "B4 transport of generated comparison observation diagram, K_c, L_c, and pointed quotient"
      - "B4 endpoint comparison-conjugation and Psi naturality"
      - "B4 identity, inverse, binary composition, and finite-chain coherence"
    remaining:
      - "all C--D construction obligations"
  certificate_provenance:
    discharged:
      - "coefficient identification comes from generated base and pulled endpoint coefficient conjugations"
      - "qualified-subgroup transport comes from the existing C1s image theorem"
      - "finite-chain action comes from the existing pasted-versus-recursive-versus-composite endpoint theorems"
    unresolved: []
  accepted_dependencies:
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF1.lean"
      blob_at_base: 3b708eab571efe393baad80ed555c18bf5d075e5
      accepted_pr: 4403
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097"
      use: "generated endpoint coefficient-component identity laws"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF3.lean"
      blob_at_base: 7871e33aee515fb6a723a402358d69da89e57c9b
      accepted_pr: 4403
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097"
      use: "one-step qualified-comparison subgroup transport"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF6.lean"
      blob_at_base: 489707c277a806afa509754a0eb15f0e08bcebff
      accepted_pr: 4391
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4391#issuecomment-5553257870"
      use: "one-step endpoint coefficient observation squares"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF7.lean"
      blob_at_base: 17f020105a0679f89bcc6320e44dcd3e3febeaf8
      accepted_pr: 4403
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097"
      use: "identity, inverse, and binary-composition laws for generated endpoint isomorphisms"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF8.lean"
      blob_at_base: b3127432aebc9529464ac0d25b102d19c9a6fe5b
      accepted_pr: 4403
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4403#issuecomment-5557145097"
      use: "structural change identity, inverse, composition, and dependent Chain.composite"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF9.lean"
      blob_at_base: bc26d4faeedab0fbfeda4ef2b7a896c969a1c5e8
      accepted_pr: 4394
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4394#issuecomment-5554932002"
      use: "identity, inverse, composition, and pasted/recursive finite endpoint actions"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF10.lean"
      blob_at_base: f1e749a2ea5e31844319819cd6d4289edc307ec1
      accepted_pr: 4395
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4395#issuecomment-5555031950"
      use: "composite-generated endpoint coherence"
    - source: "research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF12.lean"
      blob_at_base: 0b0fa838b3a2794b6be077c5780426c284568733
      accepted_pr: 4397
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4397#issuecomment-5555465539"
      use: "finite-chain coefficient and qualified-subgroup transport"
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean"
      blob_at_base: a5cf9d624e6f1b220b1065a219c111b74113d077
      accepted_pr: 4450
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4450#issuecomment-5622324810"
      use: "B2 endpoint-kernel product and Psi classification"
  proof_use:
    used:
      - "all four generated endpoint hom/inv coefficient identity theorems"
      - "one-step and pasted finite-chain coefficient-observation squares"
      - "one-step and pasted finite-chain qualified-comparison subgroup image theorems"
      - "generated endpoint comparison coherence and B2 representative formula"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted predecessor build: ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF12; exit 0"
    - "targeted predecessor build: ResearchLean.AG.ComparisonInformationLoss.ObservationTransport; exit 0 before the local inverse-API extension"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/PresentationTransport.lean; exit 0"
    - "permanent PresentationChange namespace audit: 95 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "C1: prove the reusable subgroup-restriction reflection criterion, restricted-fiber right torsor, and short-exact package"
```

### Cycle 6 acceptance spine

`coefficientObservationEquivAt` は base/pulled の生成端点同型の実係数成分による共役の積であり、
4本の係数恒等式を使って identity と一致することを別定理で証明する。主
`observationEquivAt` はこの構成と、既存の積観測可換式・qualified subgroup image を使う。
そこから一般 A2 API により `K_c`、`L_c`、基点付き左剰余類を運び、端点成分の核制限と
既存 B2 の代表元公式から comparison conjugation と `Psi` の自然性を証明する。

有限合成は endpoint action を再定義せず、G-118 C1s の pasted action、typed recursive action、
structural composite から新たに生成した action の三者一致を使う。このため chain の
`K_c`、`L_c`、quotient、target kernel、および `Psi` square は全リンクの実作用を保持する。

Cycle 6 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の `U,ctx,P,k,input,i` と任意の固定 G-118 C1s change / dependent chain。
- `direction-hypothesis`: なし。
- `discharge-required`: 係数観測と qualified subgroup の移送、比較共役の自然性。既存 C1s
  theorem と生成端点同型からすべて放電する。
- `conclusion-equivalent-risk`: transport や coherence を入力 field とせず、changed input の
  再生成器と pasted/composite coherence から構成する。

## Cycle 7 — Group-homomorphism restriction, reflection, fibers, and exactness

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 7
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 25d4500953d6f377e0cad7200230453143cb0405
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 6 discharged B4; C--D remained"
  proof_dag_predecessors:
    - Mathlib.Algebra.Exact
    - Mathlib.GroupTheory.Coset.Basic
  proof_obligation: "C1: prove the reusable subgroup-restriction reflection criterion, restricted-fiber right torsor, and short-exact package"
  selection_reason: "The same unrestricted group theorem supplies every reflection, lift-fiber, and short-exact conclusion required by C and D."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean
    - AAT.AG.ComparisonInformationLoss.comap_eq_iff_ker_le_and_map_eq_inf_range
    - AAT.AG.ComparisonInformationLoss.restrictedFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.restrictedSubgroupHom_shortExact_iff_map_eq
  risks:
    - "replacing ambient image intersection by surjectivity onto all of B"
    - "storing reflection or lift existence as an input field"
    - "using left multiplication while claiming the required right-kernel action"
    - "calling a fiber a torsor without proving freeness and transitivity"
  unchecked:
    - "C2 Karoubi specialization and C finite counterexamples"
    - "D normalization specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the subgroup restriction from preservation, proved the exact ambient reflection criterion, identified restricted-lift existence with subgroup image membership, constructed the literal right action of the restricted kernel on every fiber and proved unique transitivity, and proved the kernel short-exact sequence criterion."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.restrictedSubgroupHom
    - AAT.AG.ComparisonInformationLoss.comap_eq_iff_ker_le_and_map_eq_inf_range
    - AAT.AG.ComparisonInformationLoss.nonempty_restrictedFiber_iff_mem_map
    - AAT.AG.ComparisonInformationLoss.restrictedFiber_action_free
    - AAT.AG.ComparisonInformationLoss.restrictedFiber_action_transitive
    - AAT.AG.ComparisonInformationLoss.restrictedFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.restrictedKernelInclusion_mulExact
    - AAT.AG.ComparisonInformationLoss.restrictedSubgroupHom_shortExact_iff_map_eq
    - AAT.AG.ComparisonInformationLoss.isGroupShortExact_identity_top
    - AAT.AG.ComparisonInformationLoss.not_isGroupShortExact_identity_bot_top
  claim_mapping:
    theorem_names:
      - comap_eq_iff_ker_le_and_map_eq_inf_range
      - nonempty_restrictedFiber_iff_mem_map
      - restrictedFiber_existsUnique_smul_eq
      - restrictedSubgroupHom_shortExact_iff_map_eq
    source_labels:
      - "fixed target C.2: reflection iff kernel containment and image intersection"
      - "fixed target C.3: lift image, right-kernel torsor, and short exact sequence"
      - "fixed target D: reusable reflection, fiber, and exactness theorem"
    conjuncts:
      - "B.comap f = A iff ker f is contained in A and map A is B intersect range f"
      - "the restricted fiber over t is nonempty iff t belongs to the ambient image of A"
      - "the opposite restricted kernel acts by x times k on the right, with a unique displacement between any two fiber points"
      - "the literal kernel inclusion and restricted homomorphism form a short exact sequence iff A maps onto B"
      - "the short-exact predicate has a full-subgroup identity instance and fails for the bottom-to-full restriction in every nontrivial group"
    undischarged_assumptions: []
    acceptance_point: "Every conclusion is derived from arbitrary group laws, the homomorphism, the two subgroups, and the preservation inclusion. Reflection, lift existence, and exactness are theorem conclusions rather than supplied certificates."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "general reflection necessary-and-sufficient condition"
      - "general restricted-lift image condition"
      - "general right-kernel fiber torsor"
      - "general short-exact criterion"
    remaining:
      - "C Karoubi restriction construction and specialization"
      - "C two fixed finite counterexamples"
      - "D canonical normalization specialization"
  certificate_provenance:
    discharged:
      - "the restricted homomorphism is constructed from the supplied preservation inclusion"
      - "kernel elements acting on a fiber are proved from their defining kernel equation"
      - "the unique displacement is constructed as x inverse times y"
    unresolved: []
  proof_use:
    used:
      - "preservation inclusion constructs restrictedSubgroupHom"
      - "kernel containment and image-intersection equality prove the reverse comap inclusion"
      - "fiber equations prove the displacement lies in the restricted kernel"
      - "MonoidHom.mulExact_iff and Subgroup.range_subtype prove exactness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean; exit 0"
    - "permanent ComparisonInformationLoss namespace audit: 18 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "C2: construct the Karoubi endpoint restriction homomorphism and specialize the reflection, lift-fiber, and short-exact API"
```

### Cycle 7 acceptance spine

`restrictedSubgroupHom` は唯一の direction hypothesis である `A.map f ≤ B` から実際の
制限準同型を構成する。反映条件は ambient な `B.comap f = A` を、`ker f ≤ A` と
`A.map f = B ⊓ f.range` の連言へ同値変形し、全射性を仮定しない。

`RestrictedFiber` 上では `ker(restrictedSubgroupHom)ᵐᵒᵖ` が `x ↦ xk` により作用する。
任意の二点 `x,y` に対する元は `x⁻¹y` から構成され、自由性と合わせて一意性を得る。
短完全列は実際の kernel subtype inclusion、`Function.MulExact`、restriction の全射性から構成し、
全射性を `A.map f = B` と同値にしている。

Cycle 7 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の群 `G,H`、群準同型 `f:G→H`、部分群 `A≤G,B≤H`。
- `direction-hypothesis`: `A.map f ≤ B`。制限準同型の構成にのみ使用する。
- `discharge-required`: 反映条件、lift fiber の像、右核作用の自由かつ推移性、短完全列。
- `conclusion-equivalent-risk`: 反映、fiber 非空性、全射性、exactness を入力 record に保持しない。

## Cycle 8 — Karoubi endpoint restriction and the specialized C API

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 8
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 27a4530eef5ecfd3247e56af7c4608c5c51a6864
tracking_issue: 4443
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 7 accepted the generic restriction/reflection/fiber/exactness API; C2 remained"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.restrictedSubgroupHom
    - AAT.AG.ComparisonInformationLoss.comap_eq_iff_ker_le_and_map_eq_inf_range
    - AAT.AG.ComparisonInformationLoss.restrictedFiber_existsUnique_smul_eq
    - AAT.AG.RealizationComparisonIdempotents.karoubiArrowToArrowKaroubiObj
  proof_obligation: "C2: construct H, Gamma_0, the endpoint sandwich homomorphism r, preservation and rBar, then specialize reflection, lift fibers, the right torsor, and short exactness"
  selection_reason: "This connects the accepted generic group API to the exact Karoubi comparison of fixed target C and leaves only the two finite decisions in clause C."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestrictionHom
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestriction_preserves_comparison
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestriction_reflection_iff
    - AAT.AG.ComparisonInformationLoss.idempotentCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.idempotentCompatibleRestriction_shortExact
  risks:
    - "constructing a raw automorphism instead of an automorphism of the Karoubi object"
    - "omitting the explicit inverse sandwiches e b^-1 e and d p^-1 d"
    - "defining Gamma_0 in the ambient endpoint group instead of as a subgroup of H"
    - "assuming preservation, reflection, lift existence, or surjectivity as a new field"
    - "failing to connect d c e, represented by e ≫ c ≫ d, to the accepted Karoubi-arrow construction"
  unchecked:
    - "C two fixed finite counterexamples"
    - "D normalization specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed centralizer subgroups and their product H, Gamma_0 as a comap subgroup of H with ambient image H intersect Gamma_c, genuine Karoubi automorphisms with the prescribed hom/inverse sandwiches, their endpoint product homomorphism r, preservation and rBar, and all reflection/lift/right-torsor/short-exact conclusions by specializing Cycle 7."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.idempotentCentralizerAutSubgroup
    - AAT.AG.ComparisonInformationLoss.idempotentRestrictionAut
    - AAT.AG.ComparisonInformationLoss.idempotentRestrictionHom_hom_f
    - AAT.AG.ComparisonInformationLoss.idempotentRestrictionHom_inv_f
    - AAT.AG.ComparisonInformationLoss.idempotentComparisonKaroubiArrow
    - AAT.AG.ComparisonInformationLoss.idempotentImageComparison
    - AAT.AG.ComparisonInformationLoss.idempotentImageComparison_agrees_karoubiArrowEquivalence
    - AAT.AG.ComparisonInformationLoss.centralizingEndpointSubgroup
    - AAT.AG.ComparisonInformationLoss.centralizingCompatibleSubgroup_map_eq_inf
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestrictionHom
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestriction_preserves_comparison
    - AAT.AG.ComparisonInformationLoss.idempotentCompatibleRestrictionHom
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestriction_reflection_iff
    - AAT.AG.ComparisonInformationLoss.nonempty_idempotentCompatibleLiftFiber_iff_mem_map
    - AAT.AG.ComparisonInformationLoss.idempotentCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.idempotentCompatibleRestriction_shortExact
  claim_mapping:
    theorem_names:
      - idempotentRestrictionHom_hom_f
      - idempotentRestrictionHom_inv_f
      - centralizingCompatibleSubgroup_map_eq_inf
      - idempotentEndpointRestriction_preserves_comparison
      - idempotentEndpointRestriction_reflection_iff
      - nonempty_idempotentCompatibleLiftFiber_iff_mem_map
      - idempotentCompatibleLiftFiber_action_free
      - idempotentCompatibleLiftFiber_action_transitive
      - idempotentCompatibleLiftFiber_existsUnique_smul_eq
      - idempotentCompatibleRestriction_shortExact
    source_labels:
      - "fixed target C.1: H, Gamma_0, r(b,p)=(ebe,dpd), preservation, and rBar"
      - "fixed target C.2: reflection necessary-and-sufficient condition"
      - "fixed target C.3: lift image, right-kernel torsor, and short exactness under surjectivity"
    conjuncts:
      - "each centralizing endpoint automorphism produces a genuine Karoubi automorphism whose hom and inverse are the requested sandwiches"
      - "Gamma_0 is a subgroup of H and its ambient image is H intersect Gamma_c"
      - "the endpoint product homomorphism sends every Gamma_0 element into Gamma_a and restricts to rBar"
      - "reflection is exactly kernel containment together with Gamma_a intersect image(r)"
      - "a lift fiber is nonempty exactly on r(Gamma_0), and the kernel of rBar acts freely and transitively by right multiplication"
      - "r(Gamma_0)=Gamma_a produces the literal short exact sequence"
    undischarged_assumptions: []
    acceptance_point: "The categorical hypotheses are the two idempotence equations and d c = c e (represented by e ≫ c = c ≫ d) from the fixed target. The short-exact conclusion additionally uses exactly the target's stated condition r(Gamma_0)=Gamma_a. Preservation and every later conclusion are derived from the subgroup definitions and the accepted C1 API."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C general Karoubi endpoint sandwich homomorphism and explicit inverse maps"
      - "C comparison preservation and restricted homomorphism"
      - "C general reflection criterion"
      - "C general lift-fiber image, right torsor, and short exactness"
    remaining:
      - "C two fixed finite counterexamples"
      - "D canonical normalization specialization"
  certificate_provenance:
    discharged:
      - "Karoubi objects and comparison are constructed from X,Y,c,e,d and the three fixed equations"
      - "endpoint Karoubi inverses are constructed as e b^-1 e and d p^-1 d"
      - "preservation is proved from centralizer and raw comparison equations"
      - "rBar is constructed from the proved subgroup image inclusion"
    unresolved: []
  accepted_dependencies:
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean"
      blob_at_base: 8d2353328ebbb9f9270a51960b1f411be883efd3
      accepted_pr: 4453
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4453#issuecomment-5626440175"
      use: "generic subgroup restriction, reflection, lift fiber, right action, and short exactness"
    - source: "research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean"
      blob_at_base: 09401532e5b8852a9906d343a6f7256ad364e054
      accepted_pr: 4417
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4417#issuecomment-5588109222"
      use: "accepted construction of the normalized d c e comparison, represented by e ≫ c ≫ d, from an idempotent arrow square"
  proof_use:
    used:
      - "idempotence proves Karoubi object and sandwich morphism laws"
      - "centralizer equations prove inverse centralization, Karoubi inverse laws, and homomorphism multiplication"
      - "d c = c e, represented by e ≫ c = c ≫ d, constructs the actual idempotent arrow square and participates in the image comparison morphism proof"
      - "raw comparison preservation and both centralizer equations prove that r maps Gamma_0 into Gamma_a"
      - "the accepted generic reflection, lift-fiber, right-action, and short-exact theorems are applied to the constructed r and subgroup inclusion"
      - "the short-exact theorem uses its stated conditional hypothesis r(Gamma_0)=Gamma_a via the accepted generic short-exact equivalence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted predecessor build: ResearchLean.AG.RealizationComparisonIdempotents.KaroubiArrowEquivalence; exit 0"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean; exit 0"
    - "permanent ComparisonInformationLoss namespace audit: 37 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "C3: construct and decide the constant-zero reflection counterexample and unequal-fiber lift counterexample on Fin 3"
```

### Cycle 8 acceptance spine

`idempotentCentralizerAutSubgroup` は端点自己同型が冪等射と可換する条件を部分群として
保持する。各元から Karoubi 対象の自己同型を構成し、hom は `e b e`、inverse は
`e b⁻¹ e` に一致する。二端点の積 `H` から得る `idempotentEndpointRestrictionHom` は
これら二つの構成の積である。

`centralizingCompatibleSubgroup` は `H` の中の `Gamma_0` であり、ambient endpoint group
への像が `H ⊓ Gamma_c` に一致する。raw comparison equation と両端の centralizer equation
から `r(Gamma_0) ≤ Gamma_a` を証明し、その包含だけを使って `rBar` を構成する。
反映、lift fiber の像、右核作用、短完全列は Cycle 7 の一般定理をこの実構成へ適用した結果である。

`idempotentComparisonKaroubiArrow` は通常合成記法の `d c = c e`（Lean では
`e ≫ c = c ≫ d`）を Arrow square として保持し、既存
`karoubiArrowToArrowKaroubiObj` が作る比較の underlying morphism と
`idempotentImageComparison` の通常記法 `d c e`（Lean では `e ≫ c ≫ d`）が
一致する。したがって像比較を独立に選び直していない。

Cycle 8 の material premise role は次のとおりである。

- `ambient-boundary`: 任意の圏 `E`、対象 `X,Y`、射 `c,e,d`。
- `direction-hypothesis`: `e²=e`、`d²=d`、通常合成記法の `d c = c e`（Leanでは
  `e ≫ c = c ≫ d`）。また短完全列の定理にのみ、固定 target C.3 自身が述べる
  `r(Gamma_0)=Gamma_a` を条件仮定として用いる。
- `discharge-required`: Karoubi自己同型と逆射、群準同型 `r`、比較保存、反映条件、lift fiber、右核作用、短完全列。
- `conclusion-equivalent-risk`: 比較保存、反映、lift、全射性をstructure fieldとして受け取らず、入力射と部分群から構成する。

## Cycle 9 — Fixed finite Karoubi counterexamples

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 9
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: 1f57da1ae4730e4c73158490c192a4e522955897
goal_path: research/goals/G-120-aat-comparison-information-loss.md
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycle 8 accepted the general Karoubi restriction API; the two fixed finite examples remained"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.idempotentEndpointRestrictionHom
    - AAT.AG.ComparisonInformationLoss.nonempty_idempotentCompatibleLiftFiber_iff_mem_map
  proof_obligation: "C3: construct and decide the constant-zero reflection counterexample and the unequal-fiber no-lift counterexample on the fixed three-point object in FintypeCat"
  selection_reason: "These are the exact two finite decisions fixed by clause C and complete that clause before the canonical-normalization specialization."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestrictionFiniteWitness.lean
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZero_reflection_fails
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair_not_mem_restrictionRange
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair_has_no_compatibleLift
  risks:
    - "using a finite carrier in Type instead of the fixed object in the category of finite sets"
    - "showing only Gamma_0 nonmembership without proving membership of the restriction in Gamma_a"
    - "checking only a selected finite list of raw permutations instead of excluding every candidate lift"
    - "asserting that the image swap is an automorphism without constructing its Karoubi inverse laws"
  unchecked:
    - "D canonical normalization specialization"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed both fixed FintypeCat examples. The constant-zero pair lies in H, fails Gamma_0 at point 1, maps into Gamma_a, and witnesses reflection failure. The fold-image swap is a genuine Karoubi automorphism pair in Gamma_a but is outside the full range of r, hence outside r(Gamma_0) and has an empty compatible lift fiber."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestrictionFiniteWitness.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZero_idempotent
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZeroCentralizingPair_mem_H
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZeroCentralizingPair_raw_mismatch
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZeroCentralizingPair_not_mem_GammaZero
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZero_restriction_mem_GammaImage
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.constantZero_reflection_fails
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberFold_idempotent
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiber_imageComparison_f
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapAut
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair_not_mem_restrictionRange
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair_not_mem_compatibleImage
    - AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness.unequalFiberImageSwapPair_has_no_compatibleLift
  claim_mapping:
    theorem_names:
      - constantZeroCentralizingPair_mem_H
      - constantZeroCentralizingPair_not_mem_GammaZero
      - constantZero_restriction_mem_GammaImage
      - constantZero_reflection_fails
      - unequalFiber_imageComparison_f
      - unequalFiberImageSwapPair
      - unequalFiberImageSwapPair_not_mem_restrictionRange
      - unequalFiberImageSwapPair_has_no_compatibleLift
    source_labels:
      - "fixed target C finite example 1: constant-zero reflection failure on {0,1,2}"
      - "fixed target C finite example 2: unequal-fiber image swap with no raw lift"
    conjuncts:
      - "the first example proves idempotence, compatibility of the idempotents with c=id, H membership, Gamma_0 nonmembership, image compatibility, and reflection failure"
      - "the raw mismatch is evaluated at point 1 as the false equality 2=1"
      - "the second comparison has underlying morphism exactly the fold e, and the same image swap at both endpoints lies in Gamma_a"
      - "every raw centralizing source automorphism restricting to the image swap would send both 1 and 2 to 0, contradicting injectivity"
      - "the image swap is outside im r, therefore outside r(Gamma_0), and its specialized compatible-lift fiber is empty"
    undischarged_assumptions: []
    acceptance_point: "Both examples are closed computations on the fixed FintypeCat object Fin 3. The second proof quantifies over an arbitrary element of H and derives a contradiction; lift failure is not encoded as input or reduced to a sampled enumeration."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "C fixed constant-zero reflection counterexample"
      - "C fixed unequal-fiber no-lift counterexample"
    remaining:
      - "D canonical normalization specialization"
  certificate_provenance:
    discharged:
      - "both idempotents and compatibility equations are proved from the explicit Fin 3 maps"
      - "the image swap hom and inverse are constructed from the explicit two-point swap map and its square equals the Karoubi identity"
      - "reflection failure uses an explicit H element and pointwise raw mismatch"
      - "no-lift uses the sandwich equality, centralizer membership, and raw automorphism injectivity"
    unresolved: []
  accepted_dependencies:
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean"
      blob_at_base: e4e132de3cbac6b29d347bed16ba533b8134b385
      accepted_pr: 4454
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4454#issuecomment-5626713534"
      use: "the endpoint restriction, comparison subgroups, reflection equation, lift fiber, and lift-image criterion specialized by the two examples"
  proof_use:
    used:
      - "constant-zero idempotence and centralizer equations package the first pair as an element of H"
      - "evaluation of the raw comparison equation at 1 proves Gamma_0 nonmembership"
      - "the explicit sandwich evaluations prove that the same pair maps into Gamma_a"
      - "fold idempotence identifies the normalized comparison a with the fixed fold e"
      - "the image-swap square supplies both inverse laws in the Karoubi automorphism"
      - "restriction equality at 1 and centrality at 2 force a hypothetical raw lift to identify distinct raw points"
      - "the accepted lift-image iff converts nonmembership in r(Gamma_0) to emptiness of the compatible lift fiber"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/KaroubiRestrictionFiniteWitness.lean; exit 0"
    - "permanent finite-witness namespace audit: 25 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "D1: specialize reflection, lift fibers, right-kernel action, and short exactness to G-119 canonical normalization"
```

### Cycle 9 acceptance spine

第1例は `FintypeCat.of (Fin 3)` の恒等比較と定値0の冪等射を用いる。
入力側で `1` と `2` を交換し、出力側を恒等にする対は両方の中心化群に属する。
しかし raw 比較式は点 `1` で `2=1` を要求するため `Gamma_0` に属さない。
sandwich 後は両端が定値0に潰れて `Gamma_a` に属し、反映失敗を実元で示す。

第2例の冪等射は `0↦0, 1↦1, 2↦1` で、像側の2点 `0,1` を交換する
Karoubi 自己同型の hom と inverse を具体的に構成する。raw lift を任意に仮定すると、
sandwich 式の点 `1` での評価から `b(1)=0`、中心化式の点 `2` での評価から
`b(2)=0` を得る。raw 自己同型の単射性に反するため、全候補に対して lift は存在しない。

## Cycle 10 — Canonical normalization reflection and lifting

```yaml
ledger_type: target_cycle_result
goal: G-120-aat-comparison-information-loss
cycle: 10
goal_blob_sha: fdf55308582fabca2ffecf085a959e3be02fed43
base_oid: df2964a34e54d0e39c5f8dce1184d8b9d67f714d
goal_path: research/goals/G-120-aat-comparison-information-loss.md
report_path: research/reports/G-120-aat-comparison-information-loss.md
selection:
  proof_state_ref: "Cycles 1--9 discharged A--C; D canonical normalization was the sole remaining mathematical obligation"
  proof_dag_predecessors:
    - AAT.AG.ComparisonInformationLoss.comap_eq_iff_ker_le_and_map_eq_inf_range
    - AAT.AG.ComparisonInformationLoss.restrictedSubgroupHom
    - AAT.AG.ComparisonInformationLoss.RestrictedFiber
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphismHom
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphism_preserves_comparison
    - AAT.AG.RealizationComparisonIdempotents.normalizationEndpointAutomorphism_preserves_bottom
    - AAT.AG.RealizationComparisonIdempotents.normalizationBaseQualifiedComparisonSubgroupHom
  proof_obligation: "D: specialize reflection, lift image, right-kernel torsors, and conditional short exactness to canonical normalization on all endpoint groups and on the separately constructed base-fixing endpoint groups"
  selection_reason: "This is the last fixed mathematical clause and connects the general decision theorem to the accepted G-119 normalization and bottom-projection constructions without adding endpoint centralization conditions."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/CanonicalNormalizationRestriction.lean
    - AAT.AG.ComparisonInformationLoss.normalizationComparison_reflection_iff
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleRestriction_shortExact
    - AAT.AG.ComparisonInformationLoss.normalizationBaseComparison_reflection_iff
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleRestriction_hom_agrees_existing
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleRestriction_shortExact
  risks:
    - "routing through clause C centralizers and thereby adding a condition not present in canonical normalization"
    - "calling the existing comparison-first qualified subgroup Q_base instead of constructing base-fixing endpoint groups before intersecting comparison compatibility"
    - "asserting actual reflection or surjectivity rather than the fixed necessary-and-sufficient and conditional conclusions"
    - "claiming agreement with the G-119 homomorphism without an explicit underlying-pair-preserving identification of the opposite subgroup nestings"
  unchecked:
    - "fixed-head Cycle 10 Math 2 + Lean 2 review"
    - "fresh schema-complete final Math 2 + Lean 2 review across A--D"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Specialized the generic reflection, lift-image, right-torsor, and conditional short-exact theorems to the accepted full normalization endpoint homomorphism. Constructed Q_base and R_base as endpoint base-fixing subgroups, Gamma_base and Delta_base inside them, r_base and rBar_base, repeated all decision and fiber results, and identified rBar_base with the accepted G-119 comparison-first restriction by explicit underlying-pair-preserving group equivalences and a homomorphism equality."
  completion_candidate: yes
  lean_artifacts:
    - research/lean/ResearchLean/AG/ComparisonInformationLoss/CanonicalNormalizationRestriction.lean
  evidence:
    - AAT.AG.ComparisonInformationLoss.normalizationEndpointAutomorphism_map_le
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleRestrictionHom
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleRestrictionHom_eq_existing
    - AAT.AG.ComparisonInformationLoss.normalizationComparison_reflection_iff
    - AAT.AG.ComparisonInformationLoss.nonempty_normalizationCompatibleLiftFiber_iff_mem_map
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleLiftFiber_action_free
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleLiftFiber_action_transitive
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.normalizationCompatibleRestriction_shortExact
    - AAT.AG.ComparisonInformationLoss.rawNormalizationBaseEndpointSubgroup
    - AAT.AG.ComparisonInformationLoss.normalizedBaseEndpointSubgroup
    - AAT.AG.ComparisonInformationLoss.normalizationBaseEndpointHom
    - AAT.AG.ComparisonInformationLoss.rawBaseComparisonSubgroup
    - AAT.AG.ComparisonInformationLoss.normalizedBaseComparisonSubgroup
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleRestrictionHom
    - AAT.AG.ComparisonInformationLoss.rawBaseComparisonEquivExisting
    - AAT.AG.ComparisonInformationLoss.normalizedBaseComparisonEquivExisting
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleRestriction_hom_agrees_existing
    - AAT.AG.ComparisonInformationLoss.normalizationBaseComparison_reflection_iff
    - AAT.AG.ComparisonInformationLoss.nonempty_normalizationBaseCompatibleLiftFiber_iff_mem_map
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleLiftFiber_action_free
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleLiftFiber_action_transitive
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleLiftFiber_existsUnique_smul_eq
    - AAT.AG.ComparisonInformationLoss.normalizationBaseCompatibleRestriction_shortExact
  claim_mapping:
    theorem_names:
      - normalizationComparison_reflection_iff
      - nonempty_normalizationCompatibleLiftFiber_iff_mem_map
      - normalizationCompatibleLiftFiber_existsUnique_smul_eq
      - normalizationCompatibleRestriction_shortExact
      - rawBaseComparisonSubgroup_map_eq_inf
      - normalizedBaseComparisonSubgroup_map_eq_inf
      - normalizationBaseCompatibleRestriction_hom_agrees_existing
      - normalizationBaseComparison_reflection_iff
      - nonempty_normalizationBaseCompatibleLiftFiber_iff_mem_map
      - normalizationBaseCompatibleLiftFiber_existsUnique_smul_eq
      - normalizationBaseCompatibleRestriction_shortExact
    source_labels:
      - "fixed target D full canonical-normalization endpoint groups"
      - "fixed target D base-fixing endpoint groups and comparison subgroups"
    conjuncts:
      - "r_N is the accepted G-119 homomorphism on all raw endpoint automorphisms and preserves the raw comparison subgroup by functoriality"
      - "full reflection is exactly kernel containment plus normalized comparison subgroup intersect range, without a surjectivity premise"
      - "full compatible lift existence is the subgroup image condition and every nonempty fiber is a right torsor for the restricted kernel"
      - "full subgroup surjectivity implies the literal short exact sequence"
      - "Q_base and R_base are defined before comparison compatibility by the two endpoint bottom-kernel equations"
      - "Gamma_base and Delta_base are subgroups inside Q_base and R_base, with ambient images equal to the stated intersections"
      - "r_base preserves comparison compatibility and restricts to rBar_base"
      - "opposite subgroup nestings are identified by group equivalences preserving the complete endpoint pair"
      - "under those equivalences rBar_base equals normalizationBaseQualifiedComparisonSubgroupHom as a group homomorphism"
      - "base-qualified reflection, lift-image, right torsor, and conditional short exactness have the same exact forms as the general theorem"
    undischarged_assumptions: []
    acceptance_point: "Only G-119's canonical-normalization admissibility of P and Q is required. Reflection and lift surjectivity are conclusions or explicit conditional hypotheses where the fixed target states them; no endpoint centralization or normalization-commutation premise is introduced."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "D full normalization reflection condition, lift image, right-kernel action, and conditional short exactness"
      - "D Q_base, R_base, r_base, Gamma_base, Delta_base, and rBar_base"
      - "D agreement of rBar_base with the accepted G-119 base-qualified comparison restriction"
      - "D base-qualified reflection condition, lift image, right-kernel action, and conditional short exactness"
    remaining:
      - "fixed-head Cycle 10 independent review"
      - "fresh whole-GOAL final completion review"
  certificate_provenance:
    discharged:
      - "comparison preservation is inherited from the actual functor action N.mapIso and N.map_comp"
      - "base preservation is inherited endpointwise from the accepted equality pi_N N = piV"
      - "all reflection and fiber conclusions are obtained from the accepted generic group theorem applied to the constructed homomorphisms and subgroups"
      - "agreement with G-119 is an equality of homomorphisms after explicit subgroup reassociation, not a supplied compatibility field"
    unresolved: []
  accepted_dependencies:
    - source: "research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean"
      blob_at_base: 8d2353328ebbb9f9270a51960b1f411be883efd3
      accepted_pr: 4453
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4453#issuecomment-5626440175"
      use: "generic restriction, reflection, lift fiber, opposite-kernel action, and short exactness"
    - source: "research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean"
      blob_at_base: 070db1ae3cde4fca15c3531fd301f53b20909eab
      accepted_pr: 4440
      review_ref: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4440#issuecomment-5610736109"
      use: "accepted r_N, raw and normalized comparison subgroups, bottom projections, qualification preservation, and the comparison-first base-qualified restriction"
  proof_use:
    used:
      - "normalizationEndpointAutomorphism_preserves_comparison proves the full subgroup image inclusion used to construct the restriction"
      - "normalizationEndpointAutomorphism_preserves_bottom proves both endpoint components of Q_base map into R_base"
      - "membership of Gamma_base supplies the raw comparison equation used to prove r_base(Gamma_base) is contained in Delta_base"
      - "the subgroup reassociation equivalences use both base and comparison membership proofs and preserve the full endpoint pair"
      - "the generic reflection theorem is instantiated separately at r_N and r_base"
      - "the generic lift-image and right-action theorems are instantiated separately for full and base-qualified fibers"
      - "each short-exact theorem uses only its stated subgroup-image equality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "targeted predecessor build: ResearchLean.AG.RealizationComparisonIdempotents.NormalizationComparisonGroup; exit 0"
    - "cd research/lean && lake env lean ResearchLean/AG/ComparisonInformationLoss/CanonicalNormalizationRestriction.lean; exit 0"
    - "permanent ComparisonInformationLoss namespace audit: 40 new declarations at this module check, standard axioms only"
  blocking_findings: []
  next_obligation: "after Cycle 10 acceptance, assemble the schema-complete G-120 completion packet and run a fresh Math 2 + Lean 2 final review"
```

### Cycle 10 acceptance spine

全群版は G-119 の `normalizationEndpointAutomorphismHom` を変更せずに用いる。raw と
normalized の比較部分群の間の保存は `N.map_comp` 由来の既存定理で放電し、
generic restriction API から反映の必要十分条件、lift像、右核 torsor、条件付き短完全列を得る。

base-qualified 版は、raw 端点積の中で両投影が恒等になる部分群 `Q_base` と、
normalized 端点積の同様の部分群 `R_base` を先に構成する。その内部に
`Gamma_base` と `Delta_base` を置き、`pi_N N = piV` から `r_base` とその制限を構成する。
G-119 の既存実装は比較部分群を先に取る逆の入れ子であるため、underlying endpoint pair を
保つ群同値を raw/normalized の両側に構成し、その同定下で制限準同型が一致することを
点ごとおよび準同型の等式として証明する。
