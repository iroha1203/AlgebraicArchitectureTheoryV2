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
- current proof obligation: A2, observation-diagram transport and identity/composition coherence
- pending proof obligations: A2 and B--D
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: A2, transport kernels, intersections, fibers, and pointed quotient sets along commuting group equivalences

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
- `direction-hypothesis`: なし。
- `discharge-required`: 追加 premise なし。
- `conclusion-equivalent-risk`: 該当なし。
