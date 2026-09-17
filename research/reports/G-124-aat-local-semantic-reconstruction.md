# G-124 — 局所意味表示からの再構成と有限決定性

一次仕様は
[`research/goals/G-124-aat-local-semantic-reconstruction.md`](../goals/G-124-aat-local-semantic-reconstruction.md)
である。本 report は固定 target A--E の要求、Lean 宣言、前提の出所・使用先、
未完了 obligation を cycle ごとに追跡する。

## Proof state

- fixed activation head: `18540a67e277997376dc5833de4a608c6f526987`
- fixed GOAL blob: `4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`
- tracking Issue: [#4711](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711)
- Cycle 1 rejected PR: [#4714](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4714)
- Cycle 2 accepted PR: [#4715](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4715),
  merge commit `094151fda193acd169a08c6a65b8008ffb741b55`
- Cycle 3 accepted PR: [#4716](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4716),
  merge commit `5b421fe23fd20ed97b8d96645455d11315f197f1`
- current target state: `target-proof-checkpoint`
- completion candidate: no
- current proof obligation: E1 の source-choice morphism を actual automorphism として構成し、
  pointwise `C₂^Ω` とその像部分群の群同型を証明する
- next proof obligation: uniform flip の対応、および B の主同値との同定を与える

## Cycle 1 — rejected

一般 carrier と一般 law を量化した Hom-level 補題を二段階で harden したが、正式レビューの
再実行2回後にも中心 finding が残った。任意 carrier を許す型では carrier 自体を完成写像型に
選べ、`Prop`-valued nullary interpretation から全域延長命題を局所 equality proof に符号化できる。
したがって固定 GOAL A--B の no-global-value / no-extension 条件を一般型だけでは放電できない。
PR #4714 は mergeせず閉じ、Cycle 1 result を `rejected` とした。固定証拠は
PR comment `5717413267` と Issue comment `5717413246` にある。

## Cycle 2 selection

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 2
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 18540a67e277997376dc5833de4a608c6f526987
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 1 rejected evidence: PR comment 5717413267; Issue comment 5717413246"
  proof_dag_predecessors:
    - "RealizationReconstruction.taggedSourceChoiceTotal"
    - "RealizationReconstruction.readTaggedSourceChoice"
    - "RealizationReconstruction.readTaggedSourceChoice_taggedSourceChoiceTotal"
    - "RealizationReconstruction.architectureObjectInfinite"
  proof_obligation: "実際の TaggedArchitectureIndex 上の Bool source-choice を全有限 restriction の整合族と同値にし、同じ有限読み取りで任意有限集合の非分離 witness を構成する"
  selection_reason: "Cycle 1 blocker の任意 carrier/law surface を除き、固定 GOAL E1 が指定する実 index・Bool local table・受理済み source-choice constructor に直接接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReconstruction.lean"
  risks:
    - "coherent family に完成した global choice または extension witness を格納しないこと"
    - "function-level 同値だけで C₂ 群同型や全 ExplicitExactGeometryMorphism の分類を完了したと言わないこと"
    - "有限 local table の有限性と index 全体の有限性を混同しないこと"
  unchecked:
    - "標準 PR review は未実行"
```

## Cycle 2 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "actual tagged source-choice Bool functions are reconstructed from all finite restriction tables; coherent families assemble to accepted PackageTotalHom and ExplicitExactGeometry morphisms; every finite reading on the infinite actual index misses a distinct ExplicitExactGeometry source-choice morphism"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.taggedSourceChoiceEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.assembleTaggedSourceChoiceTotal"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.read_assembleTaggedSourceChoiceTotal_on_finite"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.assembleTaggedSourceChoiceExplicitExactGeometry"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.read_assembleTaggedSourceChoiceExplicitExactGeometry_on_finite"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.taggedSourceChoice_finite_reading_not_separating"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.taggedSourceChoiceExplicitExactGeometry_finite_reading_not_separating"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1b: C₂^Ω の全有限片からの再構成"
      - "固定 GOAL E1: 任意有限 S 上で恒等と一致する非恒等タグ変更"
    conjuncts:
      - "asm(read(choice))=choice -> assemble_read"
      - "read(asm(family))=family -> read_assemble"
      - "actual PackageTotalHom and ExplicitExactGeometry assembly with finite readback -> both assemble/readback theorem pairs"
      - "one distinct actual ExplicitExactGeometry source-choice morphism with identical readback on each finite S -> taggedSourceChoiceExplicitExactGeometry_finite_reading_not_separating"
    undischarged_assumptions: []
    acceptance_point: "局所値は finite subtype から Bool への table、整合 field は restriction equality のみ。実 global choice は singleton table から構成し、受理済み taggedSourceChoiceTotal へ渡す"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "Ω for the general restriction lemma"
      - "TaggedArchitectureIndex = ArchitectureObject FiniteModel.carrier for the actual E1 application"
    direction_hypothesis:
      - "CoherentFamily.coherent / restriction equality only"
    discharge_required:
      - "singleton assembly and both inverse laws / discharged"
      - "actual PackageTotalHom and ExplicitExactGeometry morphism construction and finite readback / discharged through accepted constructors and readback theorems"
      - "actual finite non-separation / discharged from architectureObjectInfinite and ExplicitExactGeometry source-choice injectivity"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "assembled choice values / singleton Bool tables"
      - "actual endomorphisms / taggedSourceChoiceTotal and taggedSourceChoiceExplicitExactGeometryMorphism applied to the assembled choice"
      - "finite non-separation witness / one point outside S"
    unresolved: []
  proof_use:
    used:
      - "CoherentFamily.coherent / read_assemble"
      - "readTaggedSourceChoice_taggedSourceChoiceTotal / actual readback"
      - "readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice / actual exact-geometry readback"
      - "taggedSourceChoiceExplicitExactGeometryMorphism_injective / distinct actual morphisms"
      - "architectureObjectInfinite / actual non-separation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReconstruction.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChange: 38 declarations, standard axioms only"
    - "targeted dependency build: ResearchLean.AG.RealizationReconstruction.MandatoryCExplicitExactGeometryObstruction: pass"
  blocking_findings: []
  next_obligation: "source-choice group structure, constant-false/categorical-identity identification, C₂^Ω group equivalence, and identification with B"
```

### Cycle 2 initial review remediation

初回4レーンのうち1レーンは、非分離定理が `Bool` choice の非自明性で止まり、固定 GOAL が
指定する `ExplicitExactGeometryMorphism` の同一 witness まで運ばれていない点を中心 finding とした。
修正では coherent family から実 ExplicitExactGeometry morphism を組み立て、その全有限 readback を
証明した。さらに外点 choice と constant-false choice の morphism が既存 injectivity により異なり、
同じ二 morphism の readback が指定有限 `S` 上で一致する定理を追加した。constant-false member と
categorical identity の同定、および群構造は次 obligation に残す。

Cycle 2 は固定 head `4130792c9ba38376744e8ba1fbb2bbdb58acdf75` の再査読1回目で
Math A/B・Lean A/B の全 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して
mergeした。最終監査は PR comment `5718237143`、次 cycle 選定は Issue comment
`5718244279` に固定した。

## Cycle 3 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 3
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 094151fda193acd169a08c6a65b8008ffb741b55
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 2 accepted evidence: PR comment 5718237143; Issue comment 5718244279"
  proof_dag_predecessors:
    - "RealizationReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism"
    - "RealizationReconstruction.taggedSourceChoiceTotal"
    - "ExplicitExactGeometryHom.id"
    - "ExplicitExactGeometryHom.comp"
  proof_obligation: "constant-false source-choice member を categorical identity と同定し、二つの実 ExplicitExactGeometryMorphism の合成が pointwise Bool xor choice に一致することを証明する"
  selection_reason: "Cycle 2 の concrete source-choice family を関数同値のままにせず、後続の C₂^Ω 群同型が読む実カテゴリの単位元と合成を先に固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean"
  risks:
    - "Bool の ring multiplication and ではなく xor を群演算として使うこと"
    - "PackageTotalHom-level の計算だけで exact-geometry morphism equality を主張しないこと"
    - "この cycle だけで automorphism group や C₂^Ω 群同型を完了したと数えないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "constant-false member is the categorical identity; composition of actual tagged ExplicitExactGeometry morphisms is the morphism induced by pointwise Bool xor"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism_false"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism_comp"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1a のための C₂^Ω の点ごとの C₂ 演算"
      - "固定 GOAL E1: source-choice endomorphism 族の categorical identity/composition law"
    conjuncts:
      - "neutral choice -> categorical identity theorem"
      - "pointwise xor -> actual morphism composition theorem"
    undischarged_assumptions: []
    port_status: unported
audits:
  proof_use:
    used:
      - "ExplicitExactGeometryHom.ext / all computational components"
      - "PackageTotalHom.ext and SignedExactCoreReadingHom.ext / base and operation action"
      - "dependent operationMap equality / endpoint-indexed tagged operation"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 2 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "package the source-choice members as actual automorphisms and prove the C₂^Ω group equivalence; identification with B remains later"
```

Cycle 3 は fixed head `08b5ae20831c2ec44059e40e07e4f8737a6fd1ad` の formal rerun 1/2 で
Math A/B・Lean A/B の全 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して
mergeした。最終監査は PR comment `5718381557`、Cycle 4 選定は Issue comment
`5718386793` に固定した。

## Cycle 4 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 4
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 5b421fe23fd20ed97b8d96645455d11315f197f1
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 3 accepted evidence: PR comment 5718381557; Issue comment 5718386793"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism_false"
    - "LocalSemanticReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism_comp"
    - "RealizationReconstruction.taggedSourceChoiceExplicitExactGeometryMorphism_injective"
  proof_obligation: "各 source-choice morphism を自己逆な actual Aut として構成し、pointwise xor を持つ C₂^Ω と source-choice automorphism image subgroup の群同型を証明する"
  selection_reason: "Cycle 3 で実 category の単位元・合成を固定したため、その同じ射を逆まで備えた Aut として package し、E1a の群同型を実 category 上で成立させられる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean"
  risks:
    - "Aut multiplication の composition orientation を xor の可換性で正しく処理すること"
    - "Bool ring multiplication and ではなく additive xor を Multiplicative で群演算へ移すこと"
    - "像部分群との群同型を B 全体の比較群同定として過大表示しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "every actual tagged source-choice morphism is packaged as a self-inverse Aut; the pointwise xor C₂-power maps injectively to Aut and is group-equivalent to its actual image subgroup"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_injective"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutHom"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutSubgroup"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceGroupEquiv"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1a: source-choice family の群構造と C₂^Ω 群同型"
    conjuncts:
      - "each source choice has an actual self-inverse exact-geometry automorphism -> taggedSourceChoiceAut"
      - "pointwise xor preserves Aut multiplication -> taggedSourceChoiceAutHom"
      - "choice recovery gives injectivity -> taggedSourceChoiceAutHom_injective"
      - "C₂^Ω is group-equivalent to the actual image subgroup -> taggedSourceChoiceGroupEquiv"
    undischarged_assumptions: []
    acceptance_point: "C₂^Ω is represented by Multiplicative (TaggedArchitectureIndex → Bool), where Bool addition is xor; the codomain is exactly the range subgroup in the actual ExplicitExactGeometry Aut group"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "self-inverse law / discharged from Cycle 3 xor composition and xor-self"
      - "group multiplication orientation / discharged by Aut multiplication definition and xor commutativity"
      - "faithfulness / discharged through existing actual-morphism injectivity"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "Aut inverse / the same constructed actual source-choice morphism"
      - "image subgroup membership / range witness of the constructed group hom"
    unresolved: []
  proof_use:
    used:
      - "Cycle 3 categorical identity and composition laws"
      - "taggedSourceChoiceExplicitExactGeometryMorphism_injective"
      - "MonoidHom.ofInjective for equivalence with the proved range"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 8 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "identify the uniform-true choice with the accepted uniform flip and then identify this E1a subgroup through the main equivalence B"
```

## 未完了 ledger

- A の `Σ,D,Λ`、四族を同じ実現圏へ収録する構成。
- B の対象・射を含む圏同値。Cycle 2 は E1 の指定族における function-level Hom reconstruction。
- C の投影・正規化・比較群回復。
- D の三定義と連結成分判定。
- E1 の uniform flip 対応、および source-choice subgroup と B の主同値との同定。
- E2 の lens・protocol 二層の決定性と既存 Karoubi 再構成との整合。
