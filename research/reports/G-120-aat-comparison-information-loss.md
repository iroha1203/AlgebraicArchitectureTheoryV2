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
- current proof obligation: B1, generated-comparison observation diagram and endpoint-kernel conjugacy
- pending proof obligations: B--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: B1, construct the generated comparison observation diagram and prove endpoint-kernel conjugacy

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
