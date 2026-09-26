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
- Cycle 4 accepted PR: [#4717](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4717),
  merge commit `1ce0071826c031fcbd8e5474ca80110078950c82`
- Cycle 5 accepted PR: [#4718](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4718),
  merge commit `74b6cfbeb83d494cb7ab43d9995e5df97158b006`
- Cycle 6 accepted PR: [#4719](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4719),
  merge commit `97b586063cb1d217ecdb015027e1ffa6cb9442c3`
- Cycle 7 accepted PR: [#4720](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4720),
  merge commit `be531fa3c355859cb6b3e28ad78960a3b14cf7c4`
- Cycle 8 accepted PR: [#4721](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4721),
  merge commit `41001713273f078bcef9f5b2c0711772d5b35ad0`
- Cycle 9 accepted PR: [#4722](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4722),
  merge commit `eb955775e918a5f5e37584e54ba87be14cd23580`
- Cycle 10 accepted PR: [#4723](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4723),
  merge commit `24154c67dc37f7a5f047d8dcb88c2181255d0aa4`
- Cycle 11 accepted PR: [#4724](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4724),
  merge commit `8f9c05ba23746a6644cdd7ef3e427d68a21f87d9`
- Cycle 12 accepted PR: [#4725](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4725),
  merge commit `828025931b76550faae107462ab5fd25d85928dd`
- Cycle 13 accepted PR: [#4726](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4726),
  merge commit `f487b782b7a35b90c5acde4935d9fe81164227eb`
- Cycle 14 accepted PR: [#4727](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4727),
  merge commit `cf1a3b4049daf15084169e8fa782a20d325833f2`
- Cycle 15 accepted PR: [#4728](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4728),
  merge commit `41d64b724274968199ba3b61aaeb8e22126dd4ee`
- Cycle 16 accepted PR: [#4729](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4729),
  merge commit `20d01d17bb1b1117be2cae412983472f2945761f`
- Cycle 17 accepted PR: [#4730](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4730),
  merge commit `d71fd9bda57fba4cfc182e4d3d245ba376907a6c`
- Cycle 18 accepted PR: [#4731](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4731),
  merge commit `04eaf8d985bbeb4f6cb1ed66597fb3030e0f1f14`
- Cycle 19 accepted PR: [#4732](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4732),
  merge commit `338eecddc2f80e3b60dc26f49b5218c954fe381e`
- Cycle 20 accepted PR: [#4733](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4733),
  merge commit `78a3fb497bd2807790850ba11cb6cbf9984830b0`
- Cycle 21 accepted PR: [#4734](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4734),
  merge commit `4534d6044697ec2ab27c8f176b0f7406cbeb1602`
- Cycle 22 accepted PR: [#4735](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4735),
  merge commit `a4622964b281f04fb2e66c2940a91a125dda1d21`
- Cycle 23 accepted PR: [#4736](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4736),
  merge commit `2b2ec81ed51cee17a1c89296712680bae294ca1b`
- Cycle 24 accepted PR: [#4737](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4737),
  merge commit `aa6811409a7f69203f33a741a69654606ba3cf37`
- Cycle 25 accepted PR: [#4738](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4738),
  merge commit `1a8f4694c1b80f0060feef449ea5b095e170e932`
- Cycle 26 accepted PR: [#4739](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4739),
  merge commit `d32e437efa4d0ff2f865ff577fc6d4c3c54dc671`
- Cycle 27 accepted PR: [#4740](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4740),
  merge commit `947038b5b33cb37971bab5c0a16f7b8954a5200d`
- Cycle 28 accepted PR: [#4741](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4741),
  merge commit `7275231b3815050a2d663b44178705639c958062`
- Cycle 29 accepted PR: [#4742](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4742),
  merge commit `7433561e506d5aef1d8312a18642e83bbaf70d16`
- Cycle 30 accepted PR: [#4743](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4743),
  merge commit `f7c3706b365d1b0f2cbeb25d890866f10d716c41`
- Cycle 31 accepted PR: [#4744](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4744),
  merge commit `5705fefcb1d53c7aea760d262d441b974d42f238`
- Cycle 32 accepted PR: [#4745](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4745),
  merge commit `af6037910ecf5466c7d02fbe52025402cf646503`
- Cycle 33 accepted PR: [#4746](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4746),
  merge commit `2a1c70fdbb680511a731e9d83e6b8b4131c942b1`
- Cycle 34 accepted PR: [#4747](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4747),
  merge commit `2523f2c8990273a1a5955c3e9ade83d925bfc8a9`
- Cycle 35 accepted PR: [#4748](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4748),
  merge commit `796e99d40e4b0ce44b2e7f3a3bd09f71483e0525`
- Cycle 36 accepted PR: [#4749](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4749),
  merge commit `8a7fb13571039012551efeef505d9980708a8196`
- Cycle 37 accepted PR: [#4750](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4750),
  merge commit `a4d2c26a731c1bdb17a89b664980faf18e698753`
- Cycle 38 accepted PR: [#4751](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4751),
  merge commit `9adad0f30d4b9de40bc264dc0194b32e1949e54b`
- Cycle 39 accepted PR: [#4752](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4752),
  merge commit `f052ef8f4dc79fd86530f041c4b8faef0866add4`
- Cycle 40 accepted PR: [#4753](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4753),
  merge commit `bcace0d2862020b3210d192321a7ab39bc25e13f`
- Cycle 41 accepted PR: [#4754](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4754),
  merge commit `07f9237f4706806de99988af1f4d6cca5e551086`
- Cycle 42 accepted PR: [#4755](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4755),
  merge commit `b307734dd05b5cb232cfb6f8e2a14c17e37bb053`
- Cycle 43 accepted PR: [#4756](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4756),
  merge commit `6d423825fc5931d377ca0160c9dc61bcee26c73a`
- Cycle 44 accepted PR: [#4757](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4757),
  merge commit `7e529b40a65ebf78cd866ba6426ce38670d623ef`
- Cycle 45 accepted PR: [#4758](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4758),
  merge commit `48d3c50a85722731eca7971cd54062c333dfc09d`
- Cycle 46 accepted PR: [#4759](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4759),
  merge commit `1e359cbae5eed78138782593b17da96b6a9e193a`
- Cycle 47 accepted PR: [#4760](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4760),
  merge commit `2bea07ef9d75a10812f2e5bde04e1500f58bef3f`
- Cycle 48 accepted PR: [#4761](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4761),
  merge commit `b07683e791c918ec43b282eb949e7b1555021366`
- Cycle 49 accepted PR: [#4762](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4762),
  merge commit `90adf1b8f30a65a0b41555d6e64280f7013e27fd`
- Cycle 50 accepted PR: [#4763](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4763),
  merge commit `7036cf07bbbf31add86972f36d46cf3ec093620f`
- Cycle 51 accepted PR: [#4764](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4764),
  merge commit `bcc839d940da9331ccaf1efc72858ed8bcbe10d0`
- Cycle 52 accepted PR: [#4765](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4765),
  merge commit `ca07c309f75a92b8a2d914f237495722cd3e285d`
- Cycle 53 accepted PR: [#4766](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4766),
  merge commit `664543be2520e146de13be12b7080ef7ba677018`
- Cycle 54 accepted PR: [#4767](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4767),
  merge commit `844cb74f6654c22f3110e369fcd9819a9f694c6d`
- Cycle 55 accepted PR: [#4768](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4768),
  merge commit `6fb9d587646a273d435e961aa0bc54e74f273c94`
- Cycle 56 accepted PR: [#4769](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4769),
  merge commit `6e0058d6e9ab25e7b4a8d6a1d7ef199754a012d5`
- Cycle 57 accepted PR: [#4770](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4770),
  merge commit `ff16abdfe07115726f3efd2e9e2782b964f7e2d9`
- Cycle 58 accepted PR: [#4771](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4771),
  merge commit `9b7e650ea5bde19219cf8203707f7ed23103b955`
- Cycle 59 accepted PR: [#4772](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4772),
  merge commit `7acbd8277b9ae8a6999f0ef807fddfc9bac6c8cb`
- Cycle 60 accepted PR: [#4773](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4773),
  merge commit `a3d22a582c20aa0b3ec726465856b1ec8f7651f8`
- Cycle 61 accepted PR: [#4774](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4774),
  merge commit `b635ffc87cb71e163619b6004ffb25878a3d9ef8`
- Cycle 62 accepted PR: [#4775](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4775),
  merge commit `bf71fc79d8093c6bd315e18a81c2f5429727eafd`
- Cycle 63 accepted PR: [#4776](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4776),
  merge commit `c31914db8437c1798cf5799b722b80b270d16927`
- Cycle 64 accepted PR: [#4778](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4778),
  merge commit `f7f9a4eca58417c82b017fa5fe465d175db13621`
- Cycle 65 accepted PR: [#4779](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4779),
  merge commit `900d73e14e70cacb37915602f3838bae46e75ac2`
- Cycle 66 accepted PR: [#4780](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4780),
  merge commit `197978ad348f382755e889e0400124f80a507103`
- Cycle 67 accepted PR: [#4781](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4781),
  merge commit `a507237a507df44914136a6f768b94173bf933ca`
- Cycle 68 accepted PR: [#4782](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4782),
  merge commit `b0a2d4b2690a1aabdf64f033c9fc6ca975f7445e`
- Cycle 69 accepted PR: [#4783](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4783),
  merge commit `871eb6dc7e7ad8abda857aef261b1f2e4131eb26`
- Cycle 70 accepted PR: [#4785](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4785),
  merge commit `c2e27b52fe60586579190af1267014d49cb65376`
- Cycle 71 accepted PR: [#4786](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4786),
  merge commit `f4d1dc2708a349186512b3bc0aadd3e50a3ac600`
- Cycle 72 accepted PR: [#4790](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4790),
  merge commit `4a01607b5bfa2fbb3f3a7956b4ab39d7e1232758`
- Cycle 73 accepted PR: [#4793](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4793),
  merge commit `cb7a659cd28d988fd4d5fd1ba9ad4eb35930459d`
- Cycle 74 accepted PR: [#4794](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4794),
  merge commit `f00e255b71d602498ad95ec683db1617bb5bebcf`
- Cycle 75 accepted PR: [#4795](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4795),
  merge commit `35f931ee50ef5ae91d226bbf3e37017e059ad308`
- Cycle 76 rejected PR: [#4796](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4796)
- Cycle 77 accepted PR: [#4797](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4797),
  merge commit `05c2bd89acda78aee16348cbd9a6ed0f42e26711`
- current target state: `target-proof-checkpoint`
- completion candidate: no
- current proof obligation: tagged・full G-122・lens・protocolを一つのbranch-indexed parameterへ
  収録し、各枝の直接assembly・両逆・圏同値と既存route接続を同時に示す
- next proof obligation: case分岐で束ねた四枝を、一つの独立な実現圏・局所モデル圏のfiberとして
  再構成し、object/Hom両逆と投影・正規化・比較群輸送まで同時に示す

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
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
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

Cycle 4 は fixed head `875f5c85ee4d48a066963e089befa9e8a1e471b2` の4-lane review で
全 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5718469541`、Cycle 5 選定は Issue comment `5718475885` に固定した。

## Cycle 5 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 5
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 1ce0071826c031fcbd8e5474ca80110078950c82
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 4 accepted evidence: PR comment 5718469541; Issue comment 5718475885"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.taggedSourceChoiceAut"
    - "RealizationReconstruction.taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base"
    - "RealizationReconstruction.taggedUniformFlipTotal_commutes_normalization"
    - "RealizationReconstruction.taggedNormalizationThenUniformFlip_ne_normalization"
  proof_obligation: "constant-true source-choice Aut の base を既存 uniform flip と同定し、actual Aut の t²=1 と既存 normalization 上の et=te・et≠e を同じ t で回収する"
  selection_reason: "Cycle 4 の C₂^Ω 群同型における constant-true の一様非自明元が、固定 GOAL E1 の既存 uniform-flip witness と同じ実射であることを明示する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean"
  risks:
    - "actual ExplicitExactGeometry Aut と既存 package/Karoubi normalization の層を混同しないこと"
    - "base equality を介さず既存 et=te・et≠e を新しい t の結果と呼ばないこと"
    - "この対応だけで B の主同値との同定を完了扱いしないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the constant-true actual source-choice Aut has taggedUniformFlipTotal as base, squares to one in ExplicitExactGeometry Aut, and its same base recovers the accepted normalization commutation and separation theorems"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_true_hom_base"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_true_square"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_true_base_commutes_normalization"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_true_normalization_comp_ne_normalization"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1: 一様flipの分離"
    conjuncts:
      - "constant true image t has accepted uniform-flip base"
      - "t²=1 in actual ExplicitExactGeometry Aut"
      - "the same base satisfies et=te and et≠e against accepted normalization e"
    undischarged_assumptions: []
    acceptance_point: "the Aut-level square is proved in the actual explicit exact geometry category; normalization commutation and separation are transported through the proved base equality to the already accepted package-level e and t"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "constant-true/base identification / discharged by accepted constructor computation"
      - "t²=1 / discharged by Cycle 3 composition and false identity"
      - "et=te and et≠e / discharged by base equality plus accepted normalization theorems"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "taggedSourceChoiceExplicitExactGeometryHom_uniformFlip_base"
      - "taggedSourceChoiceExplicitExactGeometryMorphism_comp and _false"
      - "taggedUniformFlipTotal_commutes_normalization"
      - "taggedNormalizationThenUniformFlip_ne_normalization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeGroupLaw.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "identify the E1b finite-restriction reconstruction with recovery through the main equivalence B"
```

Cycle 5 は final head `c671e97c803b3b69f3055ecc64e0e94bd80a073b` の formal rerun 1/2 で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5718579817`、Cycle 6 選定は Issue comment `5718586575` に固定した。

## Cycle 6 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 6
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 74b6cfbeb83d494cb7ab43d9995e5df97158b006
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 5 accepted evidence: PR comment 5718579817; Issue comment 5718586575"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.taggedSourceChoiceAut"
    - "LocalSemanticReconstruction.taggedSourceChoiceAut_injective"
    - "RealizationReconstruction.readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice"
    - "RealizationReconstruction.architectureObjectInfinite"
  proof_obligation: "finite reading の Separates・Extends を独立に定義し、Determining をその連言として置く。actual source-choice Aut 族では全有限 table が延長する一方、どの有限 S も区別せず、有限 determining set が存在しないことを証明する"
  selection_reason: "E1 の有限決定不能を function-level witness で止めず、Cycle 4 の actual Aut family と D の共通定義に同時に接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteDetermination.lean"
  risks:
    - "extension を separation から導かず別 theorem にすること"
    - "coherence を global extension の存在で定義しないこと"
    - "実効性を有限列挙入力なしに主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "common finite-reading separation and extension predicates are defined separately, with determining as their conjunction; every finite Bool table extends to an actual source-choice Aut, but no finite reading separates that family, so no finite determining set exists"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.Separates"
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.Extends"
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.Determining"
    - "AAT.AG.LocalSemanticReconstruction.TaggedSourceChoiceAutFamily"
    - "AAT.AG.LocalSemanticReconstruction.readTaggedSourceChoiceAutAt"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_finite_extends"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_finite_not_separates"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAut_no_finite_determining"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 区別・延長の独立な定義と、その連言としての決定集合"
      - "固定 GOAL E1: 有限決定不能"
    conjuncts:
      - "separation = injectivity of the finite restriction map"
      - "extension = every table satisfying the separately supplied coherence predicate has a global preimage; independence is checked at each application"
      - "determining = separation and extension"
      - "edge-free source-choice coherence is True and every finite Bool table extends"
      - "architectureObjectInfinite supplies an outside point, giving two distinct actual Aut with equal finite readings"
    undischarged_assumptions: []
    acceptance_point: "the target collection is the actual range of taggedSourceChoiceAut; local reading evaluates its actual ExplicitExactGeometry hom and recovers the choice through the accepted readback theorem"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "finite extension / explicit default-false global choice"
      - "finite non-separation / outside point from architectureObjectInfinite"
      - "actual Aut distinctness / taggedSourceChoiceAut_injective"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "actual ExplicitExactGeometry readback theorem"
      - "actual source-choice Aut injectivity"
      - "architectureObjectInfinite"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteDetermination.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "general graph criteria and effectiveness in D, or the common local-model equivalence B required to identify E1b recovery"
```

Cycle 6 は final head `2b17eb88c723e9eca349e4926b896c8dd80011b6` の formal rerun 2/2 で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5718717143`、Cycle 7 選定は Issue comment `5718728976` に固定した。

## Cycle 7 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 7
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 97b586063cb1d217ecdb015027e1ffa6cb9442c3
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 6 accepted evidence: PR comment 5718717143; Issue comment 5718728976"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.FiniteReading.Separates"
    - "LocalSemanticReconstruction.FiniteReading.Extends"
  proof_obligation: "写像 q に沿う component-indexed family の precomposition が injective であることと q の surjectivity、precomposition が surjective であることと q の injectivity を、非自明な値型についてそれぞれ同値として証明する"
  selection_reason: "D の一般グラフ判定を、グラフ固有の component map の性質と値族の restriction の性質に分離し、後者の set-theoretic core を先に固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ComponentRestrictionCriteria.lean"
  risks:
    - "Nontrivial Value は逆向きに本質的であり、無条件化しないこと"
    - "generic map q の判定を induced-subgraph component map の graph criterion と同一視しないこと"
    - "有限列挙入力下の実効性をこの周期で主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "for a nontrivial value type, precomposition along q is injective exactly when q is surjective, and it is surjective exactly when q is injective"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.ComponentRestriction.precompose"
    - "AAT.AG.LocalSemanticReconstruction.ComponentRestriction.precompose_injective_iff_surjective"
    - "AAT.AG.LocalSemanticReconstruction.ComponentRestriction.precompose_surjective_iff_injective"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: component-indexed family の restriction に対する区別・延長判定の set-theoretic core"
    conjuncts:
      - "separation of all global component families is injectivity of precomposition and is equivalent to surjectivity of q"
      - "extension of every local component family is surjectivity of precomposition and is equivalent to injectivity of q"
    undischarged_assumptions:
      - "q を有限頂点集合 S の induced-subgraph component map として構成し、その injectivity/surjectivity を graph conditions と同値化する"
    acceptance_point: "the two equivalences are proved for the actual function precomposition map; graph specialization remains an explicit next obligation"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "missed global index distinguishes two global families / discharged using Nontrivial Value"
      - "identified local indices obstruct arbitrary extension / discharged using Nontrivial Value"
      - "injective q extends any local family / discharged using Function.extend"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "pointwise function equality"
      - "Function.extend for the extension direction"
      - "two distinct values for both converse directions"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ComponentRestrictionCriteria.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ComponentRestriction: 3 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the induced-subgraph component map q_S and prove its surjectivity/injectivity equivalent to meeting every full component and retaining full-component connectivity inside S"
```

Cycle 7 は final head `f4698c8239bf4452396d9ac49b48f5596a521b84` の formal rerun 1/2 で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5718851609`、Cycle 8 選定は Issue comment `5718862415` に固定した。

## Cycle 8 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 8
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: be531fa3c355859cb6b3e28ad78960a3b14cf7c4
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 7 accepted evidence: PR comment 5718851609; Issue comment 5718862415"
  proof_dag_predecessors:
    - "RealizationReconstruction.FixedFComponentClassification"
    - "LocalSemanticReconstruction.ComponentRestriction.precompose_injective_iff_surjective"
    - "LocalSemanticReconstruction.ComponentRestriction.precompose_surjective_iff_injective"
  proof_obligation: "頂点述語 S が誘導する actual directed multigraph と、その component から full component への写像を構成する。写像の全射性を S が全 full component と交わること、単射性を S 内で full connectivity を保持することと同値化し、component-family restriction の区別・延長判定へ接続する"
  selection_reason: "Cycle 7 の generic precomposition criteria に、D が指定する vertices and edges inside S の actual graph map を供給する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/InducedComponentCriteria.lean"
  risks:
    - "full graph の辺ではなく、両 endpoint が S に属する named edges だけを induced graph に残すこと"
    - "full reachability から induced reachability を無条件には導かず、RetainsFullConnectivity として判定対象にすること"
    - "finiteness、decidability、effectiveness を graph equivalence へ暗黙に混入しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the actual S-induced directed multigraph and its component map are constructed; surjectivity is equivalent to meeting every full component, injectivity is equivalent to retaining full connectivity inside S, and the Cycle 7 precomposition criteria yield the corresponding separation and extension equivalences"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.graph"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.Reachable"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.Component"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.reachable_full"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.toFull"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.toFull_mk"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.MeetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.RetainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.toFull_surjective_iff_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.toFull_injective_iff_retainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.precompose_toFull_injective_iff_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.precompose_toFull_surjective_iff_retainsFullConnectivity"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 区別 iff S が全連結成分と交わる"
      - "固定 GOAL D: 延長 iff 同一 full component の S 頂点が S の頂点と辺だけで結ばれる"
    conjuncts:
      - "induced graph has vertex subtype S and exactly the named full edges whose source and target satisfy S"
      - "induced reachability maps to full reachability, so the component map is defined without representatives"
      - "component map surjectivity iff every full component has a retained vertex"
      - "component map injectivity iff every full-reachable pair of retained vertices is induced-reachable"
      - "for any Nontrivial Value, precomposition separation and extension specialize to those two graph conditions"
    undischarged_assumptions:
      - "specialize Value to Equiv.Perm K from the fixed GOAL premise |K|≥2 and connect to preservingEquivComponentPermutationFamilies"
      - "prove existence of a finite determining S iff the full component type is finite"
      - "supply the separately specified finite-enumeration effectiveness result"
    acceptance_point: "the graph is an actual FixedFDirectedMultigraph and both graph criteria are connected to the actual precomposition map; finiteness and effectiveness remain separate obligations"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "induced paths map to full paths / discharged by Relation.EqvGen induction on actual retained named edges"
      - "component-map surjectivity and injectivity / discharged by quotient representative elimination"
      - "separation and extension / discharged by the accepted Cycle 7 generic equivalences"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "fixedFComponentMk_eq_iff"
      - "ComponentRestriction.precompose_injective_iff_surjective"
      - "ComponentRestriction.precompose_surjective_iff_injective"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/InducedComponentCriteria.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.InducedComponent: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "prove the finite determining-set existence criterion, then specialize the value family to Equiv.Perm K and isolate finite-enumeration effectiveness"
```

Cycle 8 は final head `7241542d33326ca908ea522c03f93a9712035864` の initial formal review で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5718988569`、Cycle 9 選定は Issue comment `5719007843` に固定した。

## Cycle 9 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 9
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 41001713273f078bcef9f5b2c0711772d5b35ad0
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 8 accepted evidence: PR comment 5718988569; Issue comment 5719007843"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.InducedComponent.precompose_toFull_injective_iff_meetsEveryFullComponent"
    - "LocalSemanticReconstruction.InducedComponent.precompose_toFull_surjective_iff_retainsFullConnectivity"
  proof_obligation: "有限な頂点述語 S が MeetsEveryFullComponent と RetainsFullConnectivity を同時に満たすことと full component 型の有限性を同値化する。有限component側では各componentの quotient representative を一つずつ選ぶ有限集合を構成し、同じ同値を actual precomposition の separation-and-extension にも移す"
  selection_reason: "Cycle 8 の二つの graph criterion を連言し、固定 GOAL D の finite determining-set existence clause を代表元構成まで含めて放電する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteDeterminingComponents.lean"
  risks:
    - "vertex type 全体の有限性や DecidableEq を仮定せず、選ばれた代表元集合だけの有限性を証明すること"
    - "component representatives を入力certificateとして受け取らず、accepted quotient から構成すること"
    - "graph criteria と actual separation/extension の双方を記録し、片方だけを determining と呼ばないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "a finite subset meeting every component and retaining connectivity exists iff the full component type is finite; the chosen noncomputable Quotient.out representative range supplies one such subset, and for every nontrivial value type this is equivalent to existence of a finite restriction that is both injective and surjective on component families"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.representative"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.componentMk_representative"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.RepresentativeVertex"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.representativeVertex_finite"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.representativeVertex_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.representativeVertex_retainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.HasFiniteDeterminingVertices"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.hasFiniteDeterminingVertices_iff"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.HasFiniteDeterminingRestriction"
    - "AAT.AG.LocalSemanticReconstruction.InducedComponent.hasFiniteDeterminingRestriction_iff"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 決定集合の存在 iff π₀(Q) が有限"
      - "固定 GOAL D: 各componentから一頂点を選ぶ S が決定集合になる"
    conjuncts:
      - "a finite meeting-and-connectivity-retaining vertex predicate makes the component type finite through an explicit surjection"
      - "when the component type is finite, the range of Quotient.out is a finite vertex subset"
      - "the representative range meets every component and contains only one selected vertex in each component, hence retains connectivity"
      - "for Nontrivial Value, finite graph determining predicates are equivalent to finite restrictions that are both separating and extending"
    undischarged_assumptions:
      - "derive Nontrivial (Equiv.Perm K) from the fixed GOAL premise |K|≥2 and connect to preservingEquivComponentPermutationFamilies"
      - "supply the separately specified finite-enumeration coherence decision and computable extension"
    acceptance_point: "the finite subset and both directions are constructed from the actual component quotient and the accepted restriction map; no global vertex finiteness or decision procedure is assumed"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "finite determining subset implies finite components / discharged by a surjection from its finite subtype"
      - "finite components imply a finite representative subset / discharged by the finite range of Quotient.out"
      - "representative subset determining / discharged by Cycle 8 graph criteria and Cycle 7 precomposition criteria"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "noncomputable Quotient.out and Quotient.out_eq, with standard Classical.choice dependency"
      - "Finite.of_surjective"
      - "both Cycle 8 precomposition-to-graph equivalences"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteDeterminingComponents.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.InducedComponent: 10 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "specialize component values to Equiv.Perm K under |K|≥2 and then formalize the finite-enumeration effectiveness clause separately"
```

Cycle 9 は final head `f6752e313feecbbcaec8f0e76390a9a3d47c876a` の formal rerun 2/2 で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5719155816`、Cycle 10 選定は Issue comment `5719168582` に固定した。

## Cycle 10 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 10
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: eb955775e918a5f5e37584e54ba87be14cd23580
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 9 accepted evidence: PR comment 5719155816; Issue comment 5719168582"
  proof_dag_predecessors:
    - "RealizationReconstruction.FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies"
    - "LocalSemanticReconstruction.InducedComponent graph and finite determining criteria"
  proof_obligation: "[Nontrivial K] のもとで component value を Equiv.Perm K に特殊化し、full family を accepted FixedFComponentPermutationFamily と同定する。さらに accepted classification equivalence を通じて actual operation-preserving following changes の induced-component reading に区別・延長・有限determining存在判定を移す"
  selection_reason: "D の generic value-family theorem を、固定 GOAL が指定する hidden permutation family と actual preserving-change collection に接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/PermutationRestrictionCriteria.lean"
  risks:
    - "permutation family を新しいproxy構造へ包まず、accepted FixedFComponentPermutationFamily を直接使うこと"
    - "|K|≥2 を [Nontrivial K] として明示し、Equiv.Perm K の非自明性を型クラス推論だけで隠さないこと"
    - "family-level結果だけで止めず、accepted equivalence を通じて actual preserving changes へ移すこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the graph restriction is specialized to FixedFComponentPermutationFamily F K and transported through preservingEquivComponentPermutationFamilies; for actual operation-preserving following changes, separation, extension, and finite determining existence have exactly the accepted graph/component criteria"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.FullFamily"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.InducedFamily"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrict"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrict_injective_iff_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrict_surjective_iff_retainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.PreservingChange"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrictPreservingChange"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrictPreservingChange_injective_iff_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.restrictPreservingChange_surjective_iff_retainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.HasFiniteDeterminingPreservingRestriction"
    - "AAT.AG.LocalSemanticReconstruction.PermutationRestriction.hasFiniteDeterminingPreservingRestriction_iff"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: |K|≥2 での component-permutation family の区別・延長判定"
      - "固定 GOAL D: 各可視変更上の actual preserving following changes への適用"
      - "固定 GOAL D: finite determining set existence iff π₀(Q) finite"
    conjuncts:
      - "[Nontrivial K] supplies a nontrivial Equiv.Perm K value type"
      - "full families are definitionally the accepted FixedFComponentPermutationFamily F K"
      - "restriction injectivity and surjectivity have the Cycle 8 graph criteria"
      - "the accepted preserving-change equivalence preserves and reflects both properties"
      - "finite determining existence for actual preserving changes is equivalent to finiteness of FixedFComponent F"
    undischarged_assumptions:
      - "supply the separately specified finite-enumeration coherence decision and computable extension"
    acceptance_point: "the source is the actual subtype of operation-preserving FixedFFollowingStateChange and the bridge is the accepted classification equivalence, not a newly certified family"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "at least two hidden values / represented by [Nontrivial K] and the resulting Nontrivial (Equiv.Perm K) instance"
      - "classification of actual preserving changes / discharged by preservingEquivComponentPermutationFamilies"
      - "graph criteria and finite existence / discharged by Cycles 8 and 9"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "FixedFComponentPermutationFamily"
      - "FixedFFollowingStateChange.preservingEquivComponentPermutationFamilies"
      - "both induced-component restriction equivalences and finite determining criterion"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/PermutationRestrictionCriteria.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.PermutationRestriction: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "formalize the finite-enumeration coherence decision and computable extension required by D effectiveness"
```

Cycle 10 は final head `880bb47a6da25afd0cfe2f94b2cf57073eb931f7` の initial formal review で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して mergeした。
最終監査は PR comment `5719252080`、Cycle 11 選定は Issue comment `5719266626` に固定した。

## Cycle 11 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 11
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 24154c67dc37f7a5f047d8dcb88c2181255d0aa4
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 10 accepted evidence: PR comment 5719252080; Issue comment 5719266626"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.ComponentRestriction.precompose"
  proof_obligation: "明示的な Fintype local/global indices と decidable equality のもとで、injective index map に沿う local family の global extension を有限探索で計算し、restrictionが元のfamilyになることを証明する。index map のinjectivity・surjectivityをBoolで判定する"
  selection_reason: "Dの実効性を noncomputable Function.extend から分離し、finite table入力で実行可能なset-theoretic coreを先に固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FinitePrecompositionAlgorithm.lean"
  risks:
    - "Classical.choose や Finset.toList の noncomputable conversion を使わないこと"
    - "Fintype enumeration と DecidableEq を明示し、Finiteや古典的Fintype.ofFiniteで置換しないこと"
    - "generic finite-index resultをgraph-specific effectiveness completionと呼ばないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "finite enumeration and decidable equality compute unique preimages by Finset.choose under proved uniqueness, yielding a total extension program correct under injectivity; injectivity and surjectivity of the finite index map have executable Bool tests"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.uniquePreimageProof"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.preimageOfInjective"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.preimageOfInjective_spec"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.extensionOfInjective"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.extensionOfInjective_apply"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.precompose_extensionOfInjective"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.extension"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.precompose_extension"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.injectiveTest"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.injectiveTest_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.surjectiveTest"
    - "AAT.AG.LocalSemanticReconstruction.FinitePrecomposition.surjectiveTest_eq_true_iff"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: finite enumeration table と等号判定による extension の計算可能性"
    conjuncts:
      - "local indices are supplied as an explicit Fintype enumeration"
      - "global index equality is decidable, so image membership is finite-search decidable"
      - "injectivity makes every found preimage unique, allowing computable Finset.choose"
      - "the computed global family restricts definitionally/propositionally to the original local family"
      - "finite injectivity and surjectivity conditions are exposed as verified Bool tests"
    undischarged_assumptions:
      - "derive explicit Fintype and DecidableEq instances for full and induced component indices from finite vertex/edge tables"
      - "decide vertex-table edge coherence and descend coherent tables to induced-component families"
      - "specialize fallback and finite value enumeration to Equiv.Perm K from a finite K table"
    acceptance_point: "the extension is an executable finite-search definition using Finset.choose under uniqueness; no Classical.choose, noncomputable declaration, or Function.extend occurs"
    port_status: unported
audits:
  material_premises:
    discharge_required:
      - "finite local enumeration / explicit Fintype A"
      - "decidable global equality / explicit DecidableEq B"
      - "unique preimages / proved from Function.Injective q"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "Finset.univ and Finset.choose under an ExistsUnique proof"
      - "Fintype decidable injective and surjective instances"
      - "actual ComponentRestriction.precompose"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FinitePrecompositionAlgorithm.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePrecomposition: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct finite component enumerations and decidable reachability from finite graph tables, then connect vertex-edge coherence to the component-family extension algorithm"
```

Cycle 11 は final head `3ca118b80b14031bddcc067abc8057fd5d3dd681` の formal rerun 2/2 で
全4 lane が `Mergeable`、finding なしとなり、CI 7/7 success を確認して merge した。
最終監査は PR comment `5719438716`、Cycle 12 選定は Issue comment
`5719450317` に固定した。

## Cycle 12 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 12
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 8f9c05ba23746a6644cdd7ef3e427d68a21f87d9
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 11 accepted evidence: PR comment 5719438716; Issue comment 5719450317"
  proof_dag_predecessors:
    - "RealizationReconstruction.FixedFComponentClassification"
    - "LocalSemanticReconstruction.InducedComponent.graph"
    - "Mathlib SimpleGraph finite walk enumeration"
  proof_obligation: "明示的な有限 Vertex/Edge 列挙と頂点等号判定から FixedFUndirectedReachable の実行可能な判定を構成し、full graph と decidable S が作る actual induced graph の component に Fintype/DecidableEq を与え、component 等号判定が fixedFComponentMk_eq_iff と一致することを証明する"
  selection_reason: "Cycle 11 の finite precomposition algorithm が必要とする actual component index の列挙と等号判定を、D の finite graph table 入力から構成する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteComponentEnumeration.lean"
  risks:
    - "Finite や Fintype.ofFinite、Classical.decEq、component representative による noncomputable 構成で代替しないこと"
    - "loop を落とす SimpleGraph.fromRel と EqvGen の同値に reflexive case が正しく含まれること"
    - "proxy component ではなく既存の FixedFComponent と actual induced graph の component を列挙すること"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "finite path enumeration decides the EqvGen reachability generated by actual named directed edges; this supplies explicit Fintype and DecidableEq constructions for the accepted full and induced component quotients, with executable equality tests proved equivalent to the accepted reachability relations"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.relationGraph"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.eqvGen_iff_relationGraph_reachable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.finiteEqvGenDecidable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.directedEdgeStepDecidable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.undirectedReachableDecidable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.componentFintype"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.componentDecidableEq"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.componentEqualityTest"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.componentEqualityTest_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.inducedComponentFintype"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.inducedComponentDecidableEq"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.inducedComponentEqualityTest"
    - "AAT.AG.LocalSemanticReconstruction.FiniteComponent.inducedComponentEqualityTest_eq_true_iff"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: V・E の有限列挙 table と等号判定"
      - "固定 GOAL D: S 上の有限入力に対する整合判定と延長の計算可能性"
    conjuncts:
      - "finite named-edge search decides each directed endpoint step without DecidableEq Edge"
      - "SimpleGraph finite walk enumeration decides the generated undirected reachability relation"
      - "Quotient.fintype and Quotient.decidableEq apply to the existing FixedFComponent setoid"
      - "decidable S supplies explicit subtype enumerations for the actual induced vertices and retained named edges"
      - "both executable component equality tests agree with fixedFComponentMk_eq_iff"
    undischarged_assumptions:
      - "decide the S-vertex edge-coherence table and compute its descent to an induced-component family"
      - "connect that descent and Cycle 11 extension to actual Equiv.Perm K tables, including a finite value enumeration"
    acceptance_point: "the decision program uses the explicit vertex and named-edge Fintype tables, terminates through bounded finite path enumeration, and returns decisions about the accepted quotient components"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "finite vertex and named-edge enumerations / explicit Fintype inputs fixed by G-124(D)"
      - "decidable vertex equality / explicit DecidableEq input fixed by G-124(D)"
      - "induced vertex predicate and its decision / explicit S and DecidablePred input"
    discharge_required:
      - "directed endpoint-step and generated-reachability decisions / constructed from the finite tables"
      - "full and induced component Fintype and DecidableEq / constructed on the accepted quotients"
      - "agreement with accepted component relation / discharged through both equality-test iff theorems"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "SimpleGraph.fromRel and finite Reachable decision"
      - "Relation.EqvGen induction in both directions"
      - "Quotient.fintype and Quotient.decidableEq"
      - "fixedFComponentMk_eq_iff"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteComponentEnumeration.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteComponent: 13 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "decide vertex-table edge coherence and computationally descend coherent tables to induced-component families, then connect the result to Cycle 11 extension"
```

Cycle 12 は final head `f41ac8025f7099341f76d734fc5c35ed12ae2f3a` の formal rerun 1/2 で
全4 lane が `No major findings`、finding なしとなり、CI 7/7 success を確認して merge した。
最終監査は PR comment `5719806077`、Cycle 13 選定は Issue comment
`5719819091` に固定した。

## Cycle 13 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 13
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 828025931b76550faae107462ab5fd25d85928dd
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 12 accepted evidence: PR comment 5719806077; Issue comment 5719819091"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.FiniteComponent induced component enumeration and equality"
    - "LocalSemanticReconstruction.InducedComponent.toFull_injective_iff_retainsFullConnectivity"
    - "LocalSemanticReconstruction.FinitePrecomposition.extension and precompose_extension"
  proof_obligation: "finite actual retained-edge table 上の vertex-value coherence を Bool 判定し、coherent vertex table を actual induced-component family へ降下させる。RetainsFullConnectivity の下で Cycle 11 の finite extension を actual toFull に適用し、得られた full-component family が各 retained vertex で元tableを読み戻すことを証明する"
  selection_reason: "Cycles 11--12 の generic finite extension と actual component index を接続し、D の graph-table coherence/extension 計算経路を閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteCoherentExtension.lean"
  risks:
    - "coherence を component equality の supplied certificate に置換せず、actual retained named edges の等式として判定すること"
    - "quotient representative を選ばず、EqvGen 上の等値伝播で降下すること"
    - "extension の正しさに必要な injectivity を RetainsFullConnectivity から既存定理で生成すること"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "finite retained named-edge enumeration and decidable value equality compute the vertex-table coherence decision; coherent tables descend through the accepted induced-component quotient; when the actual component map retains full connectivity, the Cycle 11 finite extension computes a full-component family whose retained-vertex readback is the original table"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.VertexTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.EdgeCoherent"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.CoherentVertexTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.coherenceTest"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.coherenceTest_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.value_eq_of_reachable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.descend"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.descend_mk"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.componentFamilyEquivCoherentVertexTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.extendToFullComponents"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.extendToFullComponents_mk"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.exampleGraph"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.coherentExampleTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.coherentExampleTable_edgeCoherent"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.incoherentExampleTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension.incoherentExampleTable_not_edgeCoherent"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: S 上の整合条件は両端が S の辺の等式"
      - "固定 GOAL D: finite table の整合判定と延長の計算可能性"
    conjuncts:
      - "coherence is equality across every actual named edge retained by the induced graph"
      - "finite retained-edge enumeration and DecidableEq Value yield a verified Bool coherence test"
      - "one actual retained named edge gives concrete accepting and rejecting coherence-test examples"
      - "edge coherence propagates through the accepted EqvGen reachability relation"
      - "Quotient.lift descends the table without selecting component representatives"
      - "component families are equivalent to coherent retained-vertex tables"
      - "RetainsFullConnectivity generates injectivity of the actual toFull map"
      - "the Cycle 11 finite extension reads back to the original table at every retained vertex"
    undischarged_assumptions:
      - "construct finite enumeration and decidable equality for Equiv.Perm K from a finite K table"
      - "specialize the executable table route to accepted actual preserving following changes"
    acceptance_point: "the coherence equations are computed from the actual named-edge table and the extension is the accepted finite precomposition algorithm applied to the actual component map"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "finite graph enumerations, vertex equality, retained predicate decision, value equality, and fallback value"
    direction_hypothesis:
      - "RetainsFullConnectivity for extension correctness"
    discharge_required:
      - "edge coherence decision / constructed by finite universal search"
      - "coherent table descent / constructed by EqvGen induction and Quotient.lift"
      - "actual component-map injectivity / generated by toFull_injective_iff_retainsFullConnectivity"
      - "computed extension readback / discharged through the public Cycle 11 precompose_extension API"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "finite retained-edge enumeration and DecidableEq Value"
      - "EdgeCoherent at each EqvGen.rel step"
      - "RetainsFullConnectivity through the actual injectivity equivalence"
      - "FinitePrecomposition.extension and precompose_extension"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteCoherentExtension.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteCoherentExtension: 20 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "specialize finite value tables to Equiv.Perm K and actual operation-preserving following changes"
```

Cycle 13 は initial formal review の4 laneすべてで中心 finding なし、非中心 finding 2件となった。
具体的な coherent / incoherent permutation-free table 例と public `precompose_extension` API による
proofへ直接対応し、fresh reviewer が correspondence qualification 維持、finding 全解消、新規中心
finding なしを確認した。final head `1e4e2dbeae941afc643e366a5ae821529a8a8e21`、CI 7/7 success。
最終監査は PR comment `5720043025`、Cycle 14 選定は Issue comment `5720070426` に固定した。

## Cycle 14 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 14
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: f487b782b7a35b90c5acde4935d9fe81164227eb
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 13 accepted evidence: PR comment 5720043025; Issue comment 5720070426"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.FiniteCoherentExtension executable coherence and full-component extension"
    - "LocalSemanticReconstruction.PermutationRestriction accepted preserving-change classification"
    - "Mathlib.Data.Fintype.Perm finite enumeration and cardinality of Equiv.Perm K"
  proof_obligation: "finite K tableからactual value type Equiv.Perm Kの有限列挙・等号判定を得て、Cycle 13のcoherence判定とextensionを特殊化する。identity fallbackで得たfull component familyをaccepted classificationの逆写像によりactual operation-preserving following changeへ移し、successful raw-table computationのretained-vertex readbackを証明する"
  selection_reason: "固定GOAL Dが要求する有限value tableをactual hidden permutation valueへ具体化し、一般algorithmをaccepted preserving following-change typeまで接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationExtension.lean"
  risks:
    - "finite valueをarbitrary supplied listやproxy codeへ置換せずactual Equiv.Perm K全体を列挙すること"
    - "full familyで停止せずaccepted classificationを通じactual preserving changeを構成すること"
    - "raw input routeがcoherence certificateを外部供給として要求せずincoherent branchを明示的にrejectすること"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the finite K table induces the complete |K|! table and decidable equality of actual permutations; Cycle 13 coherence and extension specialize to permutation values; identity totalization followed by the accepted classification equivalence computes an actual preserving change; every successful raw-table computation reads back the original retained table"
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.permutationValues"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.mem_permutationValues"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.card_permutationValues"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.permutationCoherenceTest"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.permutationCoherenceTest_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.CoherentPermutationTable"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.extendPermutationFamily"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.extendPermutationFamily_mk"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.extendPreservingChange"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.extendPreservingChange_classification_mk"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.decideAndExtendPreservingChange"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.decideAndExtendPreservingChange_eq_none_iff"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.decideAndExtendPreservingChange_readback"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.coherentPermutationExampleTable"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.coherentPermutationExampleTable_edgeCoherent"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.incoherentPermutationExampleTable"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension.incoherentPermutationExampleTable_not_edgeCoherent"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: V・E・K の有限性を列挙tableと等号判定として入力に固定"
      - "固定 GOAL D: S上の整合判定の決定可能性と延長の計算可能性"
      - "受理済み分類: preserving following changes と component-indexed permutations の同値"
    conjuncts:
      - "Finset.univ enumerates every actual Equiv.Perm K value"
      - "the actual permutation table has cardinality |K|! and decidable equality"
      - "the specialized Bool test decides equality across every actual retained named edge"
      - "identity permutation supplies the explicit off-image fallback"
      - "the accepted classification inverse constructs an actual operation-preserving following change"
      - "the raw-table computation rejects exactly incoherent input and every success has retained-vertex readback"
      - "concrete identity/swap tables exercise both Bool coherence outcomes"
    undischarged_assumptions:
      - "connect the generic executable route to the existing fixed finite examples and following-change fiber cardinality declarations"
    acceptance_point: "the output is an actual PreservingChange classified by the accepted equivalence, not a supplied or proxy full-family witness"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "finite graph vertex/edge tables, vertex equality, decidable retained predicate"
      - "finite hidden carrier K and decidable equality on K"
      - "visible graph automorphism u"
    direction_hypothesis:
      - "RetainsFullConnectivity for retained-vertex readback"
    discharge_required:
      - "actual permutation enumeration and equality / generated from Fintype K and DecidableEq K"
      - "permutation coherence decision / specialized from Cycle 13"
      - "actual preserving change / constructed through the accepted classification inverse"
      - "raw successful computation readback / proved from Cycle 13 extension correctness"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "Fintype K and DecidableEq K in permutation enumeration, equality, and finite coherence"
      - "EdgeCoherent in the successful branch"
      - "RetainsFullConnectivity in full-family readback"
      - "preservingEquivComponentPermutationFamilies symm and apply_symm_apply"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationExtension.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationExtension: 19 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "connect the executable preserving-change route to fixed finite examples and following-change fiber cardinality evidence"
```

Cycle 14 は initial formal review の全4 laneで中心 finding なし、Math B / Lean B が同一の
非中心 docstring finding 1件を報告した。`Implementation notes` に actual enumeration、identity
fallback、classification inverse、internal coherence decision の採用理由と退けた代替案を追加し、
fresh reviewer が direct correspondence qualification 維持、finding 全解消、新規 finding なしを
確認した。final head `55c29e182d5195e417e436e23e1a624bfa919ca0`、CI 7/7 success。
最終監査は PR comment `5720278268`、Cycle 15 選定は Issue comment `5720299363` に固定した。

## Cycle 15 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 15
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: cf1a3b4049daf15084169e8fa782a20d325833f2
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 14 accepted evidence: PR comment 5720278268; Issue comment 5720299363"
  proof_dag_predecessors:
    - "LocalSemanticReconstruction.FinitePermutationExtension actual preserving-change output"
    - "RealizationReconstruction.FixedFSplitExactSequenceAndTorsor.componentGroupEquivProjectionFiber"
    - "RealizationReconstruction.FixedFFiberCardinality.natCard_componentGroup and natCard_projectionFiber"
    - "RealizationReconstruction.FixedFFiniteExamples accepted Bool-lens and protocol counts"
  proof_obligation: "Cycle 14 algorithmのactual PreservingChange codomainをindependently supplied visible subgroup上のactual ProjectionFiberと同値で同定し、一般fiber cardinalityを移送する。固定Bool product-lens identity/flipとtwo-session protocol identity/session-swapで既存count 2,2,4,4を同じactual preserving-change typeについて回復する"
  selection_reason: "固定GOAL D末尾の既存有限例・fiber個数宣言への接続を閉じ、effectiveness routeがaccepted actual fiber evidenceと同一対象を数えることを固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationExampleCardinality.lean"
  risks:
    - "algorithm outputとfiber countをcardinality coincidenceだけで結ばずactual equivalenceを構成すること"
    - "supplied component familyやproxy fiberを新設せずaccepted equivalencesを合成すること"
    - "fixed examplesの既存countを再計算した別証拠で置換せず、そのtheorem自体へ接続すること"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the exact actual preserving-change output type is equivalent to the accepted actual projection fiber; its generic cardinality is the accepted factorial-per-component count; the fixed Bool-lens and protocol outputs inherit the existing counts 2,2,4,4"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.preservingChangeEquivProjectionFiber"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.natCard_preservingChange_eq_projectionFiber"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.natCard_preservingChange"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.boolLens_preservingChange_count_identity"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.boolLens_preservingChange_count_flip"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.protocol_preservingChange_count_identity"
    - "AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality.protocol_preservingChange_count_sessionSwap"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 有限table上の整合判定と延長の計算可能性"
      - "固定 GOAL D: 既存の有限例・fiber個数の宣言に接続"
      - "受理済み following-change/component-family classification and projection-fiber torsor"
    conjuncts:
      - "the algorithm codomain is equivalent to the accepted actual projection fiber over the same visible automorphism"
      - "the actual preserving-change codomain has cardinality (|K|!)^|pi0(F)|"
      - "the fixed Bool-lens identity and flip codomains have the accepted count 2"
      - "the fixed protocol identity and session-swap codomains have the accepted count 4"
    undischarged_assumptions:
      - "define the third common FiniteReading Effectiveness property separately from Separates and Extends"
      - "prove that the executable coherence decision and preserving-change extension realize that common property"
    acceptance_point: "the equivalence identifies the exact PreservingChange subtype returned by Cycle 14 with the exact accepted ProjectionFiber; concrete results reuse the existing finite-example count theorems"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "independently supplied visible subgroup H and automorphism in H"
      - "finite graph vertices and finite hidden carrier for the generic cardinality formula"
    direction_hypothesis: []
    discharge_required:
      - "actual output/fiber identification / accepted equivalences composed"
      - "generic output cardinality / transported through the exact output/fiber equivalence and accepted projection-fiber cardinality"
      - "fixed example counts / transported from existing accepted theorems"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "preservingEquivComponentPermutationFamilies"
      - "componentGroupEquivProjectionFiber"
      - "natCard_preservingChange_eq_projectionFiber"
      - "FixedFFiberCardinality.natCard_projectionFiber"
      - "four FixedFFiniteExamples operation-count theorems"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FinitePermutationExampleCardinality.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FinitePermutationExampleCardinality: 7 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "define the common FiniteReading Effectiveness property and prove that the executable decision/extension route realizes it"
```

Cycle 15 は initial formal review で、generic cardinality の projection-fiber route 未使用と、
共通 `FiniteReading.Effectiveness` 欠落を無視した D completion 過大表示という中心 findingを受けた。
前者を exact output/fiber equivalence と `natCard_projectionFiber` のproof-useへ修正し、後者は
Dを未完了へ戻して次 obligationに固定した。formal rerun 1/2 の fresh Math A/B + Lean A/B は
全4 lane `No major findings`、final head `9932bf3820dc5339b7fcfc2e25dafbd3f8fb5ffd`、
CI 7/7 success。最終監査は PR comment `5720525362`、Cycle 16 選定は Issue comment
`5720545472` に固定した。

## Cycle 16 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 16
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 41d64b724274968199ba3b61aaeb8e22126dd4ee
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 15 accepted evidence: PR comment 5720525362; Issue comment 5720545472"
  proof_dag_predecessors:
    - "FiniteReading.restrict, Separates, Extends, Determining"
    - "FiniteCoherentExtension actual retained-edge coherence"
    - "FinitePermutationExtension raw Bool decision, Option PreservingChange extension, rejection and readback"
  proof_obligation: "separation/extensionから独立した第三の共通propertyとして、Bool coherence decision、raw Option extension、exact rejection、successful readbackを持つEffectivenessProgramとその存在Effectiveを定義する。finite graph/value tableとRetainsFullConnectivityの下でCycles 11--15のactual retained-edge / actual PreservingChange routeがそのprogramを構成することを証明する"
  selection_reason: "initial Cycle 15 reviewが発見した固定GOAL Dの共通effectiveness surface欠落を、既存algorithmを弱めず明示的に埋める"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean"
  risks:
    - "EffectiveをDeterminingの別名やSeparates/Extendsからの帰結にせず独立propertyにすること"
    - "coherence proofをraw inputに受け取らずBool decisionとOption extensionをprogram dataに持つこと"
    - "Finset index adapterがactual retained vertex subtypeとactual named-edge predicateを保存すること"
    - "outputをactual PreservingChangeからproxy familyへ弱めないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "a reusable EffectivenessProgram now carries the executable decision and raw extension laws; Effective is its independent existence property; the finite retained-permutation reading constructs this exact program from the accepted algorithms and proves successful actual-change readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.EffectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.Effective"
    - "AAT.AG.LocalSemanticReconstruction.FiniteReading.emptyGlobal_not_effective"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.retainedVertices"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.mem_retainedVertices"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.readPreservingChangeAt"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.toPermutationVertexTable"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.PermutationTableCoherent"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.permutationEffectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness.permutation_effective"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 区別・延長・実効の三性質を別個に定義"
      - "固定 GOAL D: finite table上の整合判定の決定可能性と延長の計算可能性"
      - "固定 GOAL D: A--BとEの各適用で共通surfaceを使う"
    conjuncts:
      - "EffectivenessProgram contains a Bool coherence decision with an iff specification"
      - "the raw extension program returns Option A and rejects exactly incoherent tables"
      - "every successful extension restricts to the supplied finite table"
      - "Effective is independent from Separates, Extends, and Determining"
      - "the graph specialization uses the actual retained named-edge coherence predicate"
      - "the graph specialization returns the actual operation-preserving following-change subtype"
      - "a concrete empty-global example proves that Effective is not automatic"
    undischarged_assumptions:
      - "apply the common FiniteReading surface in the remaining A--B and E reconstruction obligations"
    acceptance_point: "the named computational program itself is available; Effective records its existence without replacing it by separation, extension, or a supplied certificate"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "finite graph vertex/edge tables, vertex equality, decidable retained predicate"
      - "finite hidden carrier and decidable hidden equality"
      - "visible automorphism"
    direction_hypothesis:
      - "RetainsFullConnectivity for successful readback"
    discharge_required:
      - "coherence decision / Cycle 14 permutationCoherenceTest"
      - "raw extension and exact rejection / Cycle 14 decideAndExtendPreservingChange"
      - "successful readback / Cycle 14 classification readback with RetainsFullConnectivity"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "actual retained vertex membership conversion"
      - "permutationCoherenceTest_eq_true_iff"
      - "decideAndExtendPreservingChange_eq_none_iff"
      - "decideAndExtendPreservingChange_readback"
      - "RetainsFullConnectivity"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteEffectiveness.lean: pass"
    - "lake build ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteReading: 19 declarations, standard axioms only"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.FiniteEffectiveness: 7 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "place E1b finite-restriction reconstruction on the common FiniteReading surface and identify it with source-choice recovery through the main B equivalence"
```

Cycle 16 は initial formal review で `retainedVertices` の downstream direct unfolding という
非中心 finding 1件を受け、exact membership API `mem_retainedVertices` を追加して解消した。
formal rerun 1/2 の fresh Math A/B + Lean A/B は全4 lane `No major findings`、final head
`6c8c447780f8745fee21711bf3768f9adfa73559`、CI 7/7 success。最終監査は PR comment
`5720737583`、Cycle 17 選定は Issue comment `5720781859` に固定した。

## Cycle 17 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 17
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 20d01d17bb1b1117be2cae412983472f2945761f
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 16 accepted evidence: PR comment 5720737583; Issue comment 5720781859"
  proof_dag_predecessors:
    - "TagChange.globalTagChangeEquivCoherentFamily and read/assemble laws"
    - "actual TaggedSourceChoiceAutFamily, constructor, and readback"
    - "FiniteReading.restrict and EffectivenessProgram"
  proof_obligation: "actual tagged source-choice Aut imageと全finite restrictionのcoherent familyのexact equivalenceを構成し、各componentが共通FiniteReading.restrictそのものであること、inverseがaccepted actual constructorであること、同じfinite-readback lawを持つrecoveryの一意性を証明する。さらに各finite Sでraw Bool tableからactual Autへ延長するEffectivenessProgramとEffectiveを構成する"
  selection_reason: "独立候補探索によりBのlocal-model category・reading functor・main equivalenceが未構成と確認されたため、B同定を先取りせず、そのsource-choice Hom sliceと将来のB recoveryを固定する一意性criterionを構成する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReadingRecovery.lean"
  risks:
    - "actual source-choice Aut imageをall Autやfunction proxyへ置換しないこと"
    - "全finite Sでcommon FiniteReading.restrictとの可換性を証明すること"
    - "coherenceをglobal extendabilityで定義しないこと"
    - "B main equivalenceまたはgroup-level E1b isomorphismの完了を主張しないこと"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "the actual source-choice automorphism image is equivalent to coherent families of all finite readings; every component is exactly the common finite restriction, the inverse is the accepted actual constructor, and this recovery is unique under the finite-readback law. Raw finite tables have a computable global Bool extension under an explicit equality decision, while actual categorical inclusion is recorded only as a noncomputable semantic realization with exact readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutEquivGlobalTagChange"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutEquivCoherentFamily_value"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceAutEquivCoherentFamily_symm"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceRecovery_unique"
    - "AAT.AG.LocalSemanticReconstruction.readGlobalTagChangeAt"
    - "AAT.AG.LocalSemanticReconstruction.extendGlobalTagChange"
    - "AAT.AG.LocalSemanticReconstruction.globalTagChangeEffectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.globalTagChange_finite_effective"
    - "AAT.AG.LocalSemanticReconstruction.extendTaggedSourceChoiceAut"
    - "AAT.AG.LocalSemanticReconstruction.readTaggedSourceChoiceAutAt_extendTaggedSourceChoiceAut"
    - "AAT.AG.LocalSemanticReconstruction.restrict_extendTaggedSourceChoiceAut"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1b: 全finite restrictionからのsource-choice再構成"
      - "固定 GOAL D: Eの各適用で共通finite-reading surfaceを使う"
      - "固定 GOAL B: 将来のmain recoveryとの同定"
    conjuncts:
      - "forward map is actual source-choice readback and inverse is actual source-choice construction"
      - "every coherent-family component equals FiniteReading.restrict of actual readback"
      - "any recovery equivalence with that finite-readback law equals the constructed E1b recovery"
      - "raw finite Bool tables compute global source choices under an explicit equality decision"
      - "noncomputable categorical inclusion gives actual source-choice Aut extensions with exact readback, without being called executable effectiveness"
    undischarged_assumptions:
      - "construct the B local-model category, reading functor, and main equivalence before applying the uniqueness criterion"
      - "promote the E1b type equivalence to the requested group-level inverse-limit isomorphism"
      - "supply computable equality/membership for the actual tagged architecture index and computable actual categorical packaging before claiming actual-image Effective"
    acceptance_point: "the actual E1 source-choice Hom slice and its common finite-reading law are fixed; executable effectiveness is limited to the explicitly decidable global Bool representation"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "actual source-choice Aut image and actual Bool readback"
      - "finite S conditional on an explicitly supplied decidable equality for the tagged architecture index"
    direction_hypothesis:
      - "recovery uniqueness is conditional on the supplied all-finite component law hread"
    discharge_required:
      - "actual image recovery / accepted constructor and readback"
      - "all-finite-family recovery / accepted E1b read/assemble equivalence"
      - "conditional global Bool effectiveness / explicit piecewise extension"
      - "actual categorical extension correctness / exact readback only"
    conclusion_equivalent_risk: []
  proof_use:
    used:
      - "readTaggedSourceChoiceAutAt_element"
      - "TagChange.taggedSourceChoiceEquivCoherentFamily"
      - "TagChange.CoherentFamily.ext"
      - "FiniteReading.restrict"
      - "taggedSourceChoiceAutElement"
      - "extendGlobalTagChange"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual-image computable effectiveness remains unfinished"
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReadingRecovery.lean: pass"
    - "lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteReadingRecovery: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 12 declarations, standard axioms only"
  blocking_findings:
    - "initial formal review: actual categorical Aut packaging and its EffectivenessProgram were noncomputable; the actual-image Effective claim was removed rather than weakening computability to existence"
  next_obligation: "discharge or fix the actual-output computability blocker, then construct the group-level E1b inverse-limit isomorphism or begin the A--B local-model/read-functor infrastructure needed for literal B identification"
```

Cycle 17 は initial formal review で、actual Aut image の `EffectivenessProgram` が
`noncomputable` な categorical inclusion を返していたため、固定 GOAL D の計算可能性を
放電していないという中心 finding を受けた。actual-image `Effective` 宣言を削除し、
computable な raw/global Bool extension と noncomputable な actual categorical realization の
exact readback を明確に分離した。formal rerun 1/2 後の report finding と配置不整合を修正し、
formal rerun 2/2 の fresh Math A/B + Lean A/B は全4 lane `No major findings`、final head
`7928da17fb6473dcc60dead71688e77bacde6e96`、CI 7/7 success。最終監査は PR comment
`5721061186`、Cycle 18 選定は Issue comment `5721100741` に固定した。

## Cycle 18 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 18
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: d71fd9bda57fba4cfc182e4d3d245ba376907a6c
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 17 accepted evidence: PR comment 5721061186; Issue comment 5721100741"
  proof_dag_predecessors:
    - "TagChange.globalTagChangeEquivCoherentFamily and read/assemble laws"
    - "taggedSourceChoiceGroupEquiv onto the actual source-choice Aut subgroup"
    - "Cycle 17 actual subgroup readback and all-finite coherent-family recovery"
  proof_obligation: "coherent all-finite Bool familiesに明示的pointwise xor加法群を構成し、global read/assemble equivalenceをAddEquivおよびMultiplicative MulEquivへ強化する。さらにaccepted E1a group equivalenceと合成してactual source-choice Aut subgroupからcoherent familyへの群同型、actual readback component law、inverse provenanceを証明する"
  selection_reason: "actual subgroupをfunction proxyへ置換せず、Cycle 17に残ったE1b group-level obligationをaccepted E1a group equivalenceとの可換三角として直接放電する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteGroupReconstruction.lean"
  risks:
    - "coherent familyの群構造をopaque transportだけで与えずpointwise xorを明示すること"
    - "actual subgroupの乗法とpointwise xorの向きをaccepted taggedSourceChoiceGroupEquiv経由で保つこと"
    - "inverse-limit presentationをMathlib categorical limitまたはB main equivalenceと呼ばないこと"
    - "actual-output computability blockerを群同型で解消したと誤表示しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "coherent all-finite Bool readings now carry the explicit pointwise xor additive group; global choices are additively and multiplicatively equivalent to them; composing with the accepted E1a equivalence identifies the actual source-choice Aut subgroup with this coherent-family group, with exact actual readback and accepted-constructor inverse laws"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instZero"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instAdd"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instNeg"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instSub"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instSMulNat"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instSMulInt"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.instAddCommGroup"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_zero"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_add"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_neg"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_sub"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_nsmul"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.CoherentFamily.value_zsmul"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeAddEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeAddEquivCoherentFamily_apply"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeAddEquivCoherentFamily_symm_apply"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeMulEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeMulEquivCoherentFamily_apply"
    - "AAT.AG.LocalSemanticReconstruction.TagChange.globalTagChangeMulEquivCoherentFamily_symm_apply"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceSubgroupMulEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceSubgroupMulEquivCoherentFamily_apply"
    - "AAT.AG.LocalSemanticReconstruction.readTaggedSourceChoiceSubgroupAt"
    - "AAT.AG.LocalSemanticReconstruction.readTaggedSourceChoiceSubgroupAt_eq"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceSubgroupMulEquivCoherentFamily_value"
    - "AAT.AG.LocalSemanticReconstruction.taggedSourceChoiceSubgroupMulEquivCoherentFamily_symm"
  claim_mapping:
    source_labels:
      - "固定 GOAL E1a: actual source-choice subgroup ≃ C₂^Ω"
      - "固定 GOAL E1b: C₂^Ω ≅ inverse-limit presentation of all finite restrictions"
    conjuncts:
      - "coherent-family operation is pointwise Bool xor"
      - "read and singleton assembly are mutually inverse group homomorphisms"
      - "the domain is the accepted actual source-choice automorphism subgroup"
      - "each finite component is exactly FiniteReading.restrict of actual subgroup readback"
      - "the inverse is exactly accepted E1a construction after singleton assembly"
    undischarged_assumptions:
      - "construct the B local-model category, reading functor, and main equivalence before identifying this recovery through B"
      - "supply computable actual categorical packaging before claiming actual-image Effective"
    acceptance_point: "the group-level triangle uses the accepted actual subgroup and explicit pointwise xor; it does not claim a categorical limit universal property or B identification"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "actual tagged source-choice automorphism subgroup"
      - "all finite subsets of the actual TaggedArchitectureIndex"
    direction_hypothesis: []
    discharge_required:
      - "pointwise xor group laws / inherited through injective value projection with explicit operations"
      - "E1a actual subgroup classification / accepted taggedSourceChoiceGroupEquiv"
      - "E1b all-finite reconstruction / accepted global read/assemble equivalence"
      - "actual readback law / accepted source-choice exact-geometry readback"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "forward actual subgroup element / classified uniquely by accepted E1a inverse"
      - "inverse actual subgroup element / accepted E1a constructor applied to singleton assembly"
    unresolved: []
  proof_use:
    used:
      - "taggedSourceChoiceGroupEquiv and both inverse laws"
      - "TagChange.globalTagChangeEquivCoherentFamily and its read/assemble maps"
      - "readTaggedSourceChoiceExplicitExactGeometry_taggedSourceChoice"
      - "FiniteReading.restrict"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "group-level E1a/E1b triangle only; B identification and actual-image computability remain unfinished"
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteGroupReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeFiniteGroupReconstruction: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChange: 19 declarations, standard axioms only"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 25 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the A--B local-model category, reading functor, and main equivalence, while retaining the separate actual-output computability blocker"
```

Cycle 18 の initial formal review は中心 finding なし、非中心 finding として pointwise
operation instance の docstring、report artifact 収載、群同値の no-unfold API 不足を指摘した。
名指しされた docstring と8つの正規化 API だけを追加し、新規の history-free subagent による
直接対応で全 finding の実体解消、修正範囲、資格を確認した。final head
`28aecd3ebd66c6da34ce19c7cd52a05ac080765a`、CI 7/7 success。最終監査は PR comment
`5721324507`、Cycle 19 選定は Issue comment `5721402292` に固定した。

## Cycle 19 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 19
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 04eaf8d985bbeb4f6cb1ed66597fb3030e0f1f14
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 18 accepted evidence: PR comment 5721324507; Issue comment 5721402292"
  proof_dag_predecessors:
    - "RealizationReconstruction.ClosedFamilyParameter and FamilyRealization"
    - "RealizationReconstruction.closedFamilyRealizationCategory"
    - "Mathlib functor categories, full/faithful/essentially-surjective equivalence criterion"
  proof_obligation: "restriction category Λとlocal-value category Vから独立なlocal-model category Λᵒᵖ ⥤ Vを定義し、reading functorについてmorphism separation、morphism assembly、object separation、object assemblyを別々に定義する。morphism separation/assemblyからHom read/assemble equivalenceと両逆則、object-isomorphism recoveryを証明し、さらにobject assemblyからreading functorをfunctor部に持つ圏同値を構成する"
  selection_reason: "二つの独立候補探索が、E1 sliceの追加包装ではなく、actual AAT適用前に固定GOAL Bが許す非循環な一般原理を構成することを最小のliteral B前進として選んだ"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LocalModelCategory.lean"
  risks:
    - "local modelをsource category、essential image、image subtypeとして定義しないこと"
    - "local coherenceにglobal realization/morphismの存在またはextension witnessを含めないこと"
    - "分離・組立てを一つのIsEquivalence certificateだけで受け取らないこと"
    - "一般spineをactual N_ThetaまたはAAT-specific B completionと表示しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "local models are now an independently defined restriction-diagram category, and separately stated morphism uniqueness, morphism existence, and object existence produce explicit Hom read/assemble inverse laws, object-isomorphism recovery, and a categorical equivalence whose forward functor is the original reading"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.LocalModelCategory"
    - "AAT.AG.LocalSemanticReconstruction.ClosedFamilyLocalReading"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.MorphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.MorphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.ObjectSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.ObjectAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.identity_morphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.identity_morphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.identity_objectSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.identity_objectAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.faithfulOfMorphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.fullOfMorphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.essSurjOfObjectAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.homEquiv"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.homEquiv_apply"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.objectIsoOfLocalIso"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.mapIso_objectIsoOfLocalIso"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.objectSeparates_of_morphism_reconstruction"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.reconstructionEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.reconstructionEquivalence_functor"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.terminalLocalObject"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.collapseSingleObjBoolReading"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.collapseSingleObjBoolReading_not_morphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.collapseDiscreteBoolReading"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.collapseDiscreteBoolReading_not_morphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.collapseDiscreteBoolReading_not_objectSeparates"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.boolLocalObject"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.falseLocalReading"
    - "AAT.AG.LocalSemanticReconstruction.LocalReading.PredicateExamples.falseLocalReading_not_objectAssembles"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: 局所モデルの対象は整合局所値族、射は整合局所射族、identity/compositionは成分ごと"
      - "固定 GOAL B: 分離と組立てからHom read/asm両逆および圏同値"
    conjuncts:
      - "contravariant functor objects encode restriction-compatible local families"
      - "natural transformations encode componentwise local morphisms with naturality coherence"
      - "morphism separation and assembly remain distinct predicates"
      - "object separation and assembly remain distinct predicates"
      - "Hom equivalence forward map is exactly N.map and exposes read_assemble/assemble_read"
      - "the reconstructed equivalence has functor definitionally equal to N"
      - "identity reading supplies positive instances and bounded collapse/omission readings supply negative instances for all four predicates"
    undischarged_assumptions:
      - "construct the actual AAT restriction category Λ_Theta and finite typed local values from A"
      - "construct the actual primitive reading functor N_Theta on all accepted objects and noninvertible morphisms"
      - "discharge morphism separation, morphism assembly, and object assembly from A data"
      - "construct the final common D_Theta preservation interface"
    acceptance_point: "the general theorem assumes exactly the separation/assembly properties that fixed GOAL B permits at the general-principle level; no such assumption is counted as discharged for the AAT application"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "independently supplied restriction category Λ and local-value category V"
      - "source category R and a reading functor N"
    direction_hypothesis:
      - "MorphismSeparates N for uniqueness"
      - "MorphismAssembles N for Hom existence"
      - "ObjectAssembles N for object existence up to isomorphism"
    discharge_required:
      - "all three properties for the actual AAT N_Theta / unfinished and explicitly excluded from this general-cycle claim"
    conclusion_equivalent_risk:
      - "the general equivalence conclusion follows from these allowed B hypotheses, but they are not stored in the local-model definition and are not claimed for AAT"
  certificate_provenance:
    discharged:
      - "general Hom assembler / chosen only from the separately supplied surjectivity property"
      - "general object preimage / chosen only in Mathlib's equivalence construction from object assembly"
    unresolved:
      - "actual AAT provenance for every separation/assembly property"
  proof_use:
    used:
      - "MorphismSeparates and MorphismAssembles / Equiv.ofBijective and full/faithful interfaces"
      - "ObjectAssembles / essential-surjectivity interface"
      - "all three / reconstructionEquivalence"
    unused:
      - "ObjectSeparates is an independently named property and a proved consequence of Hom reconstruction; it is not an unused premise of the main equivalence"
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "general B spine only; actual Λ_Theta, local finite values, N_Theta, and A-derived discharge remain unfinished"
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LocalModelCategory.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.LocalModelCategory: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LocalReading: 29 declarations, standard axioms only"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 31 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct one actual branch-independent AAT local index/value declaration and primitive reading functor from A data, without storing completed global morphisms"
```

Cycle 19 の initial formal review は中心 finding なし、非中心 finding として4つの新規
predicate の正負例と object-iso lift の no-unfold readback API を要求した。identity reading の
正例、有限 collapse/omission reading の負例、`mapIso_objectIsoOfLocalIso` を追加し、新規の
history-free subagent による直接対応で全 finding の実体解消と修正範囲を確認した。final head
`192e97544a72b24bd18a8643acb62f06e9be2ac4`、CI 7/7 success。最終監査は PR comment
`5721617738`、Cycle 20 選定は Issue comment `5721667281` に固定した。

## Cycle 20 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 20
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 338eecddc2f80e3b60dc26f49b5218c954fe381e
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 19 accepted evidence: PR comment 5721617738; Issue comment 5721667281"
  proof_dag_predecessors:
    - "RealizationReconstruction.closedFamilyRealizationCategory"
    - "LensRealization.Fiber and res; package Hom identity/composition and semantic readback"
    - "ProtocolRealization.State, app, edge_naturality, and observation_app"
    - "LocalSemanticReconstruction.LocalModelCategory and ClosedFamilyLocalReading"
  proof_obligation: "lensの有限reference fiberとprotocolの各parameter-owned vertexの有限state carrierについて、accepted closed-family categoryの全objectと全morphismを読むactual FintypeCat-valued functorを構成し、一点restriction category上のlocal-model readingへ接続する。protocolではedge naturalityとobservation preservationをexact component APIとして示す"
  selection_reason: "二つの独立候補探索は、現存する四分枝共通primitive referenceがrealization Xに依存するため、それをΛ_Thetaに用いると固定量化順を破ると一致した。空のtagged/G-122 componentで四分枝readingを装わず、finite primitive valueとmap APIが既に揃うCS二枝の実在sliceを先に固定する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CSFiniteLocalReading.lean"
  risks:
    - "one-point sliceをfinal Λ_Thetaまたは全protocol restriction diagramと表示しないこと"
    - "Fintype.ofFiniteによる非計算的enumerationをDのeffectivenessと表示しないこと"
    - "empty tagged/G-122 branchesを追加してall-four coverageを主張しないこと"
    - "local valueにcompleted realizationまたはmorphismを保存しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the accepted lens reference fiber and every accepted protocol named-state carrier are now actual finite local values; every admitted closed-family morphism acts through the exact accepted restriction/component map, and protocol edge/observation coherence is exposed pointwise"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.finiteLocalValue"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberValueReading"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberLocalReading"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberLocalReading_obj"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberLocalReading_map_app"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexValueReading"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexLocalReading"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexLocalReading_obj"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexLocalReading_map_app"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexReading_edge_naturality"
    - "AAT.AG.LocalSemanticReconstruction.protocolVertexReading_observation"
  claim_mapping:
    source_labels:
      - "固定 GOAL A: lensの有限基準fiberとprotocolの有限carrierをprimitive local readingとして構成する"
      - "固定 GOAL A--B: arbitrary noninvertible admitted morphismsをlocal componentへ写しidentity/compositionを保つ"
    conjuncts:
      - "lens object value is exactly LensRealization.Fiber and is finite"
      - "lens morphism component is exactly LensRealization.res of the accepted semantic readback"
      - "protocol object value at each parameter-owned vertex is exactly ProtocolRealization.State and is finite"
      - "protocol morphism component is exactly ProtocolRealization.app of the accepted semantic readback"
      - "both value readings preserve identity and composition"
      - "protocol components obey accepted edge naturality and observation preservation"
    undischarged_assumptions:
      - "construct parameter-only non-discrete restriction/probe indices"
      - "construct tagged and G-122 finite typed local values and map-side readings"
      - "combine all required operation/Law/raw/coefficient/overlap readings into actual N_Theta"
      - "discharge separation and assembly from A data"
      - "construct final common D_Theta"
    acceptance_point: "this is an actual finite CS slice on all admitted CS morphisms, not the final four-branch local index or main reading"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed LensFamilyInput or ProtocolFamilyInput"
      - "accepted closed-family realization category"
    direction_hypothesis: []
    discharge_required:
      - "finite lens value / accepted finite_fiber premise"
      - "finite protocol value / accepted state_finite premise"
      - "map identity and composition / package Hom identity/composition and semantic readback compute definitionally"
      - "edge and observation coherence / accepted semantic naturality"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "lens local map / LensRealization.res on package Hom semantic readback"
      - "protocol local map / ProtocolRealization.app on package Hom semantic readback"
    unresolved:
      - "all-four primitive probe syntax and full local-model coherence"
  proof_use:
    used:
      - "LensRealization finite fiber and restriction API"
      - "ProtocolRealization finite state, naturality, and observation API"
      - "closed-family branch Hom semantic readback"
      - "Cycle 19 ClosedFamilyLocalReading target type"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual CS finite-value slices only; no all-four Λ_Theta or N_Theta claim"
  vacuity: "no empty tagged/G-122 components are defined or counted"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/CSFiniteLocalReading.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.CSFiniteLocalReading: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct parameter-only finite CS probes with nontrivial operation/observation restriction arrows, then extend the same non-owner-leaking design to tagged/G-122"
```

Cycle 20 の initial formal review は中心 finding なし、非中心 finding として protocol coherence
theorem を新設 local-reading component 自身の式にすることと、report の proof-use 訂正を要求した。
修正は theorem signature を変更したため直接対応資格を失い、formal rerun 1/2 を実施した。
fresh Math A/B・Lean A/B は final head `83660901b002f769b8a6f9101777cce77574e85d`
で全4 lane `No major findings`、CI 7/7 success。最終監査は PR comment `5721947532`、
Cycle 21 選定は Issue comment `5721982222` に固定した。

## Cycle 21 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 21
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 78a3fb497bd2807790850ba11cb6cbf9984830b0
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 20 accepted evidence: PR comment 5721947532; Issue comment 5721982222"
  proof_dag_predecessors:
    - "ProtocolSchema.ExecutionCategory, vertexObject, edgeMorphism, and pathMorphism"
    - "ProtocolRealization.toFunctor, state_finite, edgeAction, pathAction, and observation_app"
    - "Cycle 20 finiteLocalValue and accepted protocol closed-family Hom readback"
    - "Cycle 19 LocalModelCategory and ClosedFamilyLocalReading"
  proof_obligation: "protocolのparameter-owned quotient execution categoryのoppositeをrestriction indexとし、各execution objectの有限stateと全quotient path actionからFintypeCat-valued non-discrete local modelを構成する。全accepted closed-family morphismを自然変換として読み、vertex・named edge・arbitrary path・morphism component・observation preservationのexact APIを示す"
  selection_reason: "二候補探索は、Cycle 20の独立one-point slicesを実operation/path arrowで一つの非離散図式に統合でき、indexにrealizationを入れず全local valueを有限に保てる最小の前進としてprotocol execution diagramを選んだ"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolRestrictionReading.lean"
  risks:
    - "double-oppositeをfinal all-four Λ_Thetaと表示しないこと"
    - "observation targetは有限とは限らないためFintypeCat local valueへ偽装しないこと"
    - "state diagramがobservation-preserving natural transformationsを内在化しない以上、assembly/equivalenceを主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the protocol branch now has an actual parameter-owned non-discrete restriction diagram: every quotient execution object has its accepted finite state value, every quotient morphism acts by the actual execution map, and every admitted global morphism reads as a natural transformation with exact edge, path, component, and observation laws"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.ProtocolRestrictionIndex"
    - "AAT.AG.LocalSemanticReconstruction.protocolExecutionStateFinite"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionDiagram"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionMap"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionReading"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionDiagram_obj_vertex"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionDiagram_map_edge"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionDiagram_map_path"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionReading_map_app"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionReading_edge_naturality"
    - "AAT.AG.LocalSemanticReconstruction.protocolRestrictionReading_observation"
  claim_mapping:
    source_labels:
      - "固定 GOAL A: protocolの有限carrier、operation作用、restrictionをprimitive local readingとして構成する"
      - "固定 GOAL B: local modelの射をcomponentwise coherent familyとしidentity/compositionを保つ"
    conjuncts:
      - "restriction index depends only on the fixed protocol parameter"
      - "every execution object carries the accepted finite state value"
      - "named edges and arbitrary paths are read by exact accepted actions"
      - "every admitted morphism is read by its exact natural-transformation components"
      - "the reading preserves identity/composition and exposes edge/observation coherence"
    undischarged_assumptions:
      - "internalize observation preservation in the local-model morphism type"
      - "construct lens, tagged, and G-122 non-owner-leaking restriction diagrams"
      - "construct the final common N_Theta and D_Theta"
      - "discharge separation and assembly from A data"
    acceptance_point: "actual non-discrete protocol restriction reading only; the larger FintypeCat diagram category admits morphisms that need not preserve observation"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed ProtocolFamilyInput and its quotient execution category"
      - "accepted protocol realization category"
    direction_hypothesis: []
    discharge_required:
      - "all execution-object state values are finite / discharged by quotient-object representation and state_finite"
      - "restriction functor laws / discharged by the accepted semantic functor"
      - "local morphism naturality / discharged by the accepted semantic natural transformation"
      - "observation preservation / discharged externally by accepted observation_app"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "diagram maps / actual quotient execution maps"
      - "reading components / actual admitted morphism components"
    unresolved:
      - "observation-preserving local Hom category and all-four integration"
  proof_use:
    used:
      - "state_finite, Functor.map_id/map_comp, and NatTrans.naturality"
      - "edgeAction, pathAction, edge_naturality, and observation_app"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "protocol restriction diagram only; no final Λ_Theta, N_Theta, assembly, or equivalence claim"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolRestrictionReading.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolRestrictionReading: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct an observation-aware protocol local-model Hom surface without imposing observation finiteness or storing completed global morphisms"
```

Cycle 21 の fresh Math A/B・Lean A/B は final head
`00ea17c27116807d2e102685b5ca06a3ef7b9282` で全4 lane `No major findings`、
CI 7/7 success。最終監査は PR comment `5722068867`、merge commit は
`4534d6044697ec2ab27c8f176b0f7406cbeb1602`、Cycle 22 選定は Issue comment
`5722108979` に固定した。

## Cycle 22 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 22
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 4534d6044697ec2ab27c8f176b0f7406cbeb1602
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 21 accepted evidence: PR comment 5722068867; Cycle 22 selection: Issue comment 5722108979"
  proof_dag_predecessors:
    - "Cycle 21 ProtocolRestrictionIndex, protocolRestrictionDiagram, protocolRestrictionMap, and protocolRestrictionReading"
    - "ProtocolRealization.observation and its naturality"
    - "ProtocolRealization.Hom observation_naturality"
    - "accepted closed-family protocol Hom semantic readback and round-trip theorems"
    - "Cycle 19 morphism separation/assembly vocabulary"
  proof_obligation: "Cycle 21のfinite protocol restriction diagramをobject dataとし、固定observation functorへの観測と自然性を備えた独立local-model categoryを構成する。local Homをlocal natural transformationとobservation-preservation equationだけから定め、accepted closed-family protocol reading、local Homからのassembly、read/assemble両逆則を構成して、このprotocol readingのfull faithfulnessを証明する"
  selection_reason: "二つの独立候補探索は、Cycle 21で未内在化だったobservation preservationをlocal Homのmembership conditionへ移し、completed global Homをfieldに保存せずprotocol branchのmorphism separationとassemblyを同時に証明できる最短の前進として一致した"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionModel.lean"
  risks:
    - "local object/HomにProtocolRealization、ProtocolRealization.Hom、GeneratorMap、assembler、extension certificateをfieldとして保存しないこと"
    - "observation targetへ新しいfiniteness premiseを課さずFintypeCat local valueと表示しないこと"
    - "full faithfulnessをprotocol branchのmorphism separation/assemblyより強いobject assemblyまたはcategory equivalenceと表示しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the protocol branch now has an independent observation-aware finite restriction-model category; its local morphisms are local natural transformations satisfying the fixed observation equation, and the accepted closed-family reading has explicit read/assemble inverse laws"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.protocolFiniteDiagramUnderlying"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservationDiagram"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionModel"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionHom"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionModelCategory"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionForget"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionObject"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionMap"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionReading"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionAssemble"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestriction_read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestriction_assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionHomEquiv"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionReadingFaithful"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionReadingFull"
  claim_mapping:
    source_labels:
      - "固定 GOAL A: protocolの有限carrier、operation/restriction、Observableをprimitive local readingとして構成する"
      - "固定 GOAL B: local modelの射を局所射データの整合族として定め、identity/compositionを成分ごとに構成する"
      - "固定 GOAL B: protocol branchのmorphism separationとmorphism assemblyをAのprimitive dataから放電する"
    conjuncts:
      - "each local object contains a finite execution-state diagram and a parameter-referenced observation natural transformation"
      - "each local Hom contains only a local natural transformation and its observation-preservation equation"
      - "local identities and composition are componentwise"
      - "the accepted reading uses the exact Cycle 21 diagram/map and accepted observation"
      - "every observation-aware local Hom assembles to an admitted closed-family protocol Hom"
      - "read after assembly and assembly after reading are identity"
      - "the protocol reading is full and faithful"
    undischarged_assumptions:
      - "protocol local-object assembly and essential surjectivity"
      - "finite generator-table determination and effectiveness"
      - "Karoubi reconstruction coherence"
      - "corresponding lens, tagged, and G-122 local categories/readings"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "protocol-branch observation-aware local Hom category and full faithfulness only; no object assembly, protocol equivalence, finite-decision theorem, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed ProtocolFamilyInput, quotient execution category, and observation functor"
      - "accepted closed-family protocol realization category"
    direction_hypothesis: []
    discharge_required:
      - "finite local state values / Cycle 21 protocolRestrictionDiagram"
      - "object observation coherence / accepted ProtocolRealization.observation.naturality"
      - "reading-map observation preservation / accepted semantic Hom observation_naturality"
      - "local category laws / componentwise NatTrans identity and composition"
      - "assembly naturality and observation law / supplied local Hom fields"
      - "closed-family membership / accepted closedFamilyProtocolHom constructor"
      - "two inverse laws / local extensionality and accepted package semantic readback"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local object diagram / actual Cycle 21 quotient-execution restriction diagram"
      - "local object observation / actual accepted realization observation"
      - "assembled semantic Hom / constructed from the supplied independent local NatTrans and observation equation"
    unresolved:
      - "object assembly and essential surjectivity"
      - "finite generator-table and Karoubi reconstruction coherence"
      - "all-four local-model integration"
  proof_use:
    used:
      - "protocolRestrictionDiagram and protocolRestrictionMap"
      - "ProtocolRealization observation naturality"
      - "accepted closed-family protocol semantic readback"
      - "NatTrans extensionality, identity, composition, and naturality"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "direct protocol-branch discharge of observation-aware local Hom coherence, morphism separation, and morphism assembly"
  vacuity: "actual finite execution-state diagrams and observation equations are used; no empty branch or terminal filler is introduced"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionModel: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 45 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct protocol local-object assembly without a realizability or extension-certificate field, or connect the fully faithful local Hom reading to the finite generator-table/Karoubi reconstruction route"
```

Cycle 22 の fresh Math A/B・Lean A/B は final head
`b5ec68a984b49ec370cf94719456dd726ed08c8d` で全4 lane `No major findings`、
CI 7/7 success。最終監査は PR comment `5722236909`、merge commit は
`a4622964b281f04fb2e66c2940a91a125dda1d21`、Cycle 23 選定は Issue comment
`5722267343` に固定した。

## Cycle 23 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 23
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: a4622964b281f04fb2e66c2940a91a125dda1d21
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 22 accepted evidence: PR comment 5722236909; Cycle 23 selection: Issue comment 5722267343"
  proof_dag_predecessors:
    - "Cycle 22 ProtocolObservedRestrictionModel, protocolObservedRestrictionReading, explicit Hom assembly, and Full/Faithful witnesses"
    - "ProtocolRealization.toFunctor, state_finite, and observation"
    - "Cycle 21 finiteLocalValue and double-opposite quotient-execution restriction diagram"
    - "Mathlib Functor.EssSurj, Functor.IsEquivalence, and Functor.asEquivalence"
  proof_obligation: "任意のobservation-aware finite protocol restriction modelから、completed realizationまたはextension certificateをfieldとして要求せずProtocolRealizationを構成する。assembled realizationの再読取りが元のlocal objectとidentity-on-carriersで同型になることを示し、accepted readingのessential surjectivityを放電する。Cycle 22のFull/Faithfulと合わせ、functor部が同じaccepted readingであるprotocol branchの圏同値を構成する"
  selection_reason: "二候補探索は、observed local objectの有限state diagramとparameter-owned observationだけからProtocolRealizationを直接構成でき、既存Karoubi同値を先に使っても任意local objectのpreimageは得られず同じassembly義務を回避できないと一致した。したがってprotocol branchのobject assemblyを先に閉じる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionEquivalence.lean"
  risks:
    - "Fintype.ofFiniteで再選択されるFintype structureをobject equalityとせず、underlying carrier上の恒等写像によるIsoで比較すること"
    - "local objectまたはassemblerにProtocolRealization、semantic preimage、GeneratorMap、retract、extension certificateをfieldとして保存しないこと"
    - "custom observed-model categoryをCycle 19のLocalModelCategory-valued reconstruction theoremへ定義的に一致すると表示しないこと"
    - "protocol branchの圏同値をfinite generator-table決定、Karoubi整合、またはfinal all-four equivalenceへ拡張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "every observation-aware finite protocol restriction object assembles directly to a protocol realization; rereading is isomorphic to the original object by identity maps on the state carriers, so the accepted fully faithful reading is essentially surjective and yields a protocol-branch category equivalence"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionRealization"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionStateIso"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionRealizationIso"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionReadingEssSurj"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedRestrictionEquivalence_functor"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: 任意のprotocol local-model対象に対し、そのreadingが同型になる実現を構成する"
      - "固定 GOAL B: object assemblyをmorphism separation/assemblyと別個に放電する"
      - "固定 GOAL B: protocol branchのprimitive readingをfunctor部に持つ圏同値を構成する"
    conjuncts:
      - "an arbitrary local finite-state diagram is transported along double opposite to an execution functor"
      - "bundled Fintype structures supply the finite-state premise at every schema vertex"
      - "the local observation natural transformation becomes the assembled realization observation"
      - "rereading is isomorphic to the original local object by identity functions on state carriers"
      - "the object isomorphism handles different chosen Fintype structures without asserting object equality"
      - "the accepted protocol reading is essentially surjective"
      - "Cycle 22 Full/Faithful and Cycle 23 EssSurj produce a category equivalence with the accepted reading as functor"
    undischarged_assumptions:
      - "finite generator-table determination and effectiveness"
      - "compatibility with protocol Karoubi reconstruction, restriction Iso, retract generation, and Arrow equivalence"
      - "corresponding object assembly and equivalence for lens, tagged, and G-122"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "protocol-branch object assembly, essential surjectivity, and category equivalence only; no finite-decision, Karoubi-coherence, other-family, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed ProtocolFamilyInput, quotient execution category, and observation functor"
      - "Cycle 22 independent observation-aware finite restriction-model category"
      - "accepted closed-family protocol realization category and reading functor"
    direction_hypothesis: []
    discharge_required:
      - "assembled execution functor laws / stateDiagram.map_id and map_comp after double-op transport"
      - "assembled vertex-state finiteness / each bundled FintypeCat object"
      - "assembled observation naturality / supplied local observe natural transformation"
      - "readback comparison and Fintype-instance mismatch / componentwise identity Iso"
      - "essential surjectivity / explicit assembled realization and readback Iso"
      - "category equivalence / Cycle 22 Full/Faithful plus new EssSurj"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "assembled state functor / directly from the supplied local state diagram"
      - "assembled finiteness / inherited from local FintypeCat values"
      - "assembled observation / directly from the supplied local observation map"
      - "object preimage / explicit realization construction, not a stored witness"
      - "readback Iso / identity functions on the same underlying carriers"
    unresolved:
      - "finite generator-table and executable extension"
      - "Karoubi restriction and Arrow-level coherence"
      - "all-four local-model integration"
  proof_use:
    used:
      - "stateDiagram object/map data and functor laws"
      - "bundled FintypeCat finiteness"
      - "local observe components and naturality"
      - "Cycle 22 Full and Faithful witnesses"
      - "Mathlib essential-surjectivity and equivalence construction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "direct protocol-branch local-object assembly and category equivalence"
  vacuity: "every state object, restriction map, and observation component is consumed; no empty index, terminal filler, semantic object field, or chosen preimage certificate is introduced"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionEquivalence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionEquivalence: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 6 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "connect the protocol local-model equivalence to the finite generator-table decoder and accepted protocol Karoubi reconstruction, including restriction natural isomorphism, retract generation, and Arrow-level compatibility"
```

Cycle 23 の fresh Math A/B・Lean A/B は final head
`9a83a6c1eb49175122ad4cb58a828c1e6d951b55` で全4 lane `No major findings`、
CI 7/7 success。最終監査は PR comment `5722371088`、merge commit は
`2b2ec81ed51cee17a1c89296712680bae294ca1b`、Cycle 24 選定は Issue comment
`5722414921` に固定した。

## Cycle 24 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 24
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 2b2ec81ed51cee17a1c89296712680bae294ca1b
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 23 accepted evidence: PR comment 5722371088; Cycle 24 selection: Issue comment 5722414921"
  proof_dag_predecessors:
    - "Cycle 23 protocol observed-restriction category equivalence with explicit object assembly"
    - "ProtocolPresentation.decoder and accepted protocol Karoubi reconstruction equivalence"
    - "ProtocolPresentation.protocolRetractGeneratedBy and protocol Karoubi Arrow equivalence"
    - "accepted closed-family protocol package/semantic round trips"
  proof_obligation: "protocol observed local-model equivalenceをraw ProtocolRealizationと明示的に接続し、actual finite generator-table decoderのobject・edge・observation・morphism計算式を固定する。受理済みKaroubi reconstructionをobserved local categoryへtransportし、finite presentationへのrestriction natural isomorphism、任意observed objectのdecoder像からのretract、非可逆射を保つArrow equivalenceを構成する"
  selection_reason: "二候補探索は、Cycle 23で圏同値まで得たprotocol branchを途中で離れず、accepted finite presentation/Karoubi routeへ接続することが最短の未放電obligationであると一致した"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedKaroubiCoherence.lean"
  risks:
    - "closed-family fiberとraw ProtocolRealizationの同値をwrapper名だけで済ませず、accepted package/semantic round tripsから明示すること"
    - "retract witnessをlocal objectのfieldへ保存せず、Cycle 23 assemblyとaccepted semantic retract theoremから構成すること"
    - "arbitrary observation equalityのdecidabilityまたはeffective encodingをfinite carrierだけから主張しないこと"
    - "protocol branchの結果をlens・tagged・G-122またはfinal all-four equivalenceへ拡張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the protocol semantic category is explicitly equivalent to the observed local category; the actual finite presentation decoder has exact vertex, edge, observation, and morphism computation rules there; accepted Karoubi reconstruction transports with restriction Iso, retract generation, and Arrow-level equivalence"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.protocolSemanticClosedFamilyEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.protocolSemanticObservedRestrictionEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder_obj_vertex"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder_map_edge"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder_observe"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder_map_app_vertex"
    - "AAT.AG.LocalSemanticReconstruction.protocolKaroubiObservedRestrictionEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.protocolKaroubiObservedRestrictionRestrictionIso"
    - "AAT.AG.LocalSemanticReconstruction.protocolObservedFiniteDecoder_retractGeneratedBy"
    - "AAT.AG.LocalSemanticReconstruction.protocolKaroubiObservedRestrictionArrowEquivalence"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: primitive readingとfinite generator-table decoderをactual protocol local categoryで接続する"
      - "固定 GOAL B/E2: accepted Karoubi reconstructionとのrestriction・retract・Arrow-level coherenceを示す"
    conjuncts:
      - "raw semantic protocol realizations and the closed-family protocol fiber are equivalent by explicit accepted round trips"
      - "the resulting semantic-to-observed equivalence has the accepted primitive reading as its forward functor"
      - "finite presentation objects, edge tables, observation values, and morphism components compute exactly in the observed decoder"
      - "accepted protocol Karoubi reconstruction transports to the observed local category"
      - "restriction along toKaroubi is naturally isomorphic to the actual observed finite decoder"
      - "every observed local object is a retract of a decoded finite presentation"
      - "Arrow-level equivalence retains arbitrary observation-compatible noninvertible transformations"
    undischarged_assumptions:
      - "decidability or effective finite encoding of arbitrary observation equality"
      - "the three common FiniteReading effectiveness clauses"
      - "corresponding local-model equivalences and decoder/Karoubi coherence for lens, tagged, and G-122"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "protocol-branch finite decoder and Karoubi coherence only; no arbitrary-observation effectiveness, other-family, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed ProtocolFamilyInput and its finite protocol presentation category"
      - "Cycle 23 observation-aware local category equivalence"
      - "accepted protocol Karoubi reconstruction, restriction Iso, retract theorem, and Arrow equivalence"
    direction_hypothesis: []
    discharge_required:
      - "raw semantic/closed-family round trips / accepted package-semantic conversion equalities"
      - "finite decoder computations / actual presentation card, edgeTable, observationValue, and component fields"
      - "restriction coherence / associator plus whiskering of the accepted restriction Iso"
      - "observed retract generation / explicit Cycle 23 assembly/readback Iso plus mapped accepted semantic retract"
      - "Arrow coherence / mapArrowEquivalence applied to the actual semantic-observed equivalence"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "semantic/closed-family equivalence / explicit functors and accepted round-trip equalities"
      - "observed finite decoder / actual ProtocolPresentation.decoder followed by the established equivalence"
      - "observed retract / constructed per object from Cycle 23 assembly and accepted semantic retract data"
      - "Karoubi and Arrow equivalences / transported accepted equivalences"
    unresolved:
      - "effective arbitrary-observation comparison or encoding"
      - "common FiniteReading effectiveness"
      - "other three branches and all-four integration"
  proof_use:
    used:
      - "closedFamilyProtocolHom and package/semantic round-trip theorems"
      - "Cycle 23 protocolObservedRestrictionEquivalence and realization Iso"
      - "ProtocolPresentation.decoder computation data"
      - "accepted protocol Karoubi restriction Iso, retract generation, and Arrow equivalence"
      - "functor map laws, associator, whiskering, and mapArrowEquivalence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "direct protocol-branch finite-presentation/Karoubi coherence with exact observed computation APIs"
  vacuity: "actual finite presentation tables, observations, semantic morphisms, retract maps, and noninvertible Arrow morphisms are retained; no terminal filler or stored reconstruction certificate is introduced"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedKaroubiCoherence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedKaroubiCoherence: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 14 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the lens branch operation-aware local model and category equivalence, then connect its finite decoder to accepted Karoubi reconstruction without weakening the fixed all-four target"
```

Cycle 24 の fresh Math A/B・Lean A/B は final head
`4cc3c40011c3e366ef7b5144a7138eefc3b4ba40` で全4 lane `No major findings`、
CI 7/7 success。最終監査は PR comment `5722678059`、merge commit は
`aa6811409a7f69203f33a741a69654606ba3cf37`である。

## Cycle 25 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 25
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: aa6811409a7f69203f33a741a69654606ba3cf37
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 24 accepted evidence: PR comment 5722678059; Cycle 25 selection: Issue comment 5723845246"
  proof_dag_predecessors:
    - "Cycle 20 lensFiberValueReading on the actual finite reference fiber"
    - "accepted LensRealization.res/ext inverse laws and homEquivFiberMap"
    - "accepted product lens construction and productFiberEquiv"
    - "accepted closed-family lens package/semantic round trips"
  proof_obligation: "fixed LensFamilyInputに対し、有限reference fiberそのものを独立local modelとし、accepted resが全semantic Homを区別し、任意のlocal mapがputからextされることを示す。任意の有限local objectからproduct lensと実get/putを構成してobject assemblyを放電し、raw semantic categoryとclosed-family lens fiberの両方でprimitive fiber readingをforward functorとする圏同値を構成する"
  selection_reason: "protocol branchで放電したBのseparation/assemblyと対応するlens branchの最短の未放電nodeであり、後続のfinite decoder/Karoubi coherenceをactual local category上で述べる前提になる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberModelEquivalence.lean"
  risks:
    - "local objectにcompleted LensRealization、extension certificate、decoder membershipを保存しないこと"
    - "Full/Faithful/EssSurjを入力fieldではなくaccepted res/extとproduct constructionから構成すること"
    - "finite fiberだけで効果性または有限表示Karoubi coherenceまで主張しないこと"
    - "lens branchの圏同値をfinal all-four Lambda_Theta/M_Theta/N_Thetaと同定しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the actual semantic and closed-family lens readings are equivalences with the independently supplied finite reference-fiber category; Hom assembly is computed by ext from put, and every local object is assembled as a product lens with explicit get/put and canonical fiber readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.lensSemanticFiberReading"
    - "AAT.AG.LocalSemanticReconstruction.lensSemanticFiberReadingFull"
    - "AAT.AG.LocalSemanticReconstruction.lensSemanticFiberReadingFaithful"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberModelRealization"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberModelRealization_get"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberModelRealization_put"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberModelRealizationIso"
    - "AAT.AG.LocalSemanticReconstruction.lensSemanticFiberReadingEssSurj"
    - "AAT.AG.LocalSemanticReconstruction.lensSemanticFiberEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberValueReadingFaithful"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberValueReadingFull"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberValueReadingEssSurj"
    - "AAT.AG.LocalSemanticReconstruction.lensClosedFamilyFiberEquivalence"
  claim_mapping:
    source_labels:
      - "固定 GOAL A/B: lensの有限基準fiberとget/putからprimitive local readingのseparation・assemblyを放電する"
      - "固定 GOAL E2: lensの基準fiber tableが一般の意味保存射を区別・延長する"
    conjuncts:
      - "every semantic get/put-preserving Hom restricts to an actual finite-fiber map"
      - "every finite-fiber map assembles to the complete semantic Hom by the accepted ext construction"
      - "res/ext are inverse, so the primitive reading is full and faithful"
      - "every finite local object assembles to a product lens with exact get and put operations"
      - "productFiberEquiv supplies object readback and essential surjectivity"
      - "the closed-family primitive reading retains the same full Hom range through accepted package round trips"
    undischarged_assumptions:
      - "lens finite decoder computations and accepted Karoubi restriction/retract/Arrow coherence on the local category"
      - "common FiniteReading effectiveness and the D determining-set application to lens invertible changes"
      - "tagged and G-122 local-model equivalences"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "lens-branch primitive fiber category equivalence only; no decoder/Karoubi, effectiveness, other-family, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed LensFamilyInput view type and reference value"
      - "accepted total-lens laws and finite reference-fiber condition"
      - "accepted closed-family lens package/semantic round trips"
    direction_hypothesis: []
    discharge_required:
      - "morphism separation / homEquivFiberMap injectivity from ext_res"
      - "morphism assembly / LensRealization.ext and res_ext"
      - "object assembly / product lens construction"
      - "object readback / productFiberEquiv"
      - "closed-family Hom range / ofSemanticHom/toSemanticHom round trips"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "semantic local map assembly / constructed by LensRealization.ext from the supplied fiber function"
      - "local object realization / constructed by LensRealization.product from the supplied FintypeCat object"
      - "closed-family inclusion / constructed by closedFamilyLensHom from the assembled semantic Hom"
    unresolved:
      - "finite syntax decoder and Karoubi transport to the local category"
      - "common FiniteReading effectiveness and E2 invertible-change decision"
      - "other-family and all-four integration"
  proof_use:
    used:
      - "LensRealization.res_ext, ext_res, and homEquivFiberMap"
      - "LensRealization.product and productFiberEquiv"
      - "LensAATIndependentGeneratedPackageHom package/semantic round trips"
      - "Cycle 20 lensFiberValueReading"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "the local object is only the actual finite fiber; get/put and complete Homs are independently reconstructed"
  vacuity: "arbitrary finite fibers and arbitrary fiber maps are retained; the resulting semantic maps include noninvertible changes"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LensFiberModelEquivalence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.LensFiberModelEquivalence: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 17 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "connect the accepted lens finite decoder to the fiber local category with exact computation APIs, then transport Karoubi restriction, retract generation, and Arrow equivalence"
```

Cycle 25 / PR #4738 は、修正後 final head
`92f61f44e94f4146f1e40c08c81484ba69d45e73` で受理した。Math Aの非中心finding
1件によりProp-valued 6宣言を`def`から`theorem`へ修正し、freshな直接対応確認が
「有資格で解消」と判定した。他3 laneは`No major findings`、CI 7/7 success。
最終監査は PR comment `5724024182`、merge commit は
`1a8f4694c1b80f0060feef449ea5b095e170e932`である。

## Cycle 26 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 26
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 1a8f4694c1b80f0060feef449ea5b095e170e932
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 25 accepted evidence: PR comment 5724024182; Cycle 26 selection: Issue comment 5724049723"
  proof_dag_predecessors:
    - "Cycle 25 lensSemanticFiberEquivalence and explicit product-lens assembler/readback"
    - "accepted LensRealization.lensDecoder and finite-table computation laws"
    - "accepted lensKaroubiReconstructionEquivalence and restriction natural isomorphism"
    - "accepted lensRetractGeneratedBy and lensKaroubiArrowReconstructionEquivalence"
  proof_obligation: "accepted finite lens decoderをactual finite-fiber local readingと合成し、productFiberEquivを通じたobjectとmorphism tableの計算式を示す。accepted Karoubi equivalenceとrestriction natural isomorphismをFintypeCatへ移し、Cycle 25の明示的assembler/readbackからlocal retract generationを証明し、任意のlocal mapを保つArrow equivalenceを構成する"
  selection_reason: "Cycle 25が残した直接のE2 coherence nodeであり、他分枝との統合前にlens finite presentationを独立local category上で計算可能な形へ接続する"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberKaroubiCoherence.lean"
  risks:
    - "object computationにactual productFiberEquivを使い、subtype fiberとcomplementを断言で同一視しないこと"
    - "morphism computationが元のfinite generator tableを露出すること"
    - "retractを仮定せず、Cycle 25のlocal assembler/readbackとaccepted semantic retractから構成すること"
    - "非可逆local mapを保持し、Arrow coherenceをisomorphism-only statementへ弱めないこと"
    - "effectiveness、D、他分枝、final all-four completionを先取りしないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the accepted finite lens presentation decoder now computes in the independent FintypeCat local category, and the accepted Karoubi restriction, explicit retract generation, and Arrow reconstruction are transported along the actual Cycle 25 equivalence"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.lensFiberFiniteDecoder"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberFiniteDecoderObjectIso"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberFiniteDecoderObjectIso_hom_apply"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberFiniteDecoder_map_under_object_iso"
    - "AAT.AG.LocalSemanticReconstruction.lensKaroubiFiberEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.lensKaroubiFiberRestrictionIso"
    - "AAT.AG.LocalSemanticReconstruction.lensFiberFiniteDecoder_retractGeneratedBy"
    - "AAT.AG.LocalSemanticReconstruction.lensKaroubiFiberArrowEquivalence"
  claim_mapping:
    source_labels:
      - "固定 GOAL E2: lens finite determining tableと既存Karoubi reconstructionの整合"
      - "固定 GOAL B: primitive local readingのactual local-model categoryへの接続"
    conjuncts:
      - "the finite presentation decoder lands in the actual independent fiber local category"
      - "decoded objects are identified with their finite complements by productFiberEquiv"
      - "decoded morphisms compute as the original finite generator table under the object comparisons"
      - "the accepted Karoubi equivalence restricts to the local finite decoder"
      - "every local model is an explicitly constructed retract of a decoded presentation reading"
      - "Arrow reconstruction retains arbitrary local maps, including noninvertible maps"
    undischarged_assumptions:
      - "common FiniteReading effectiveness and the D determining-set application to lens invertible changes"
      - "tagged and G-122 independent local-model equivalences"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "lens-branch finite-decoder/Karoubi coherence on FintypeCat only; no effectiveness, other-family, or all-four completion claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed LensFamilyInput view type and reference value"
      - "accepted finite LensPresentation decoder and its semantic reconstruction"
      - "Cycle 25 semantic-to-fiber local equivalence"
      - "accepted semantic Karoubi restriction, retract generation, and Arrow equivalence"
    direction_hypothesis: []
    discharge_required:
      - "local decoder computation / productFiberEquiv and the actual LensPresentation morphism table"
      - "restriction coherence / associator plus whiskering of the accepted restriction Iso"
      - "local retract generation / explicit Cycle 25 product assembler/readback Iso plus mapped semantic retract"
      - "Arrow coherence / mapArrowEquivalence applied to the actual semantic-fiber equivalence"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local finite decoder / actual LensRealization.lensDecoder followed by lensSemanticFiberReading"
      - "object and map computation / actual productFiberEquiv and finite generator table"
      - "local retract / constructed per local object from lensFiberModelRealizationIso and accepted semantic retract maps"
      - "Karoubi and Arrow equivalences / transported accepted equivalences"
    unresolved:
      - "common FiniteReading effectiveness and D decision procedure"
      - "tagged/G-122 local-model equivalences and all-four integration"
  proof_use:
    used:
      - "LensRealization.lensDecoder and productFiberEquiv"
      - "Cycle 25 lensSemanticFiberEquivalence and lensFiberModelRealizationIso"
      - "accepted lens Karoubi restriction Iso, retract generation, and Arrow equivalence"
      - "functor map laws, associator, whiskering, and mapArrowEquivalence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "direct lens-branch finite-presentation/Karoubi coherence with actual local object and table computation APIs"
  vacuity: "arbitrary finite complements, generator maps, retract maps, and noninvertible Arrow morphisms are retained; no terminal filler or stored certificate is introduced"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LensFiberKaroubiCoherence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.LensFiberKaroubiCoherence: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 8 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the tagged or G-122 independent local-model equivalence and connect it to the common four-family reading without weakening the fixed target"
```

Cycle 26 / PR #4739 は final head
`c359460f357673e970a3a9ede4b412630c2db4d1` で受理した。fresh Math A/B +
Lean A/B はすべて `No major findings`、CI は 7/7 success。最終監査は PR comment
`5724206582`、merge commit は
`d32e437efa4d0ff2f865ff577fc6d4c3c54dc671` である。

## Cycle 27 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 27
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: d32e437efa4d0ff2f865ff577fc6d4c3c54dc671
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 26 accepted evidence: PR comment 5724206582; Cycle 27 selection: Issue comment 5724228773"
  proof_dag_predecessors:
    - "Cycle 25 lensSemanticFiberEquivalence and explicit product-lens assembler/readback"
    - "Cycle 26 finite-decoder/Karoubi coherence on the actual FintypeCat local category"
    - "accepted LensInvertibleChange hidden-permutation classification and complete-update-graph fiber permutation"
    - "common FiniteReading separation, extension, determining, and effectiveness surfaces"
  proof_obligation: "任意のvisible permutation上のactual product-lens invertible changeを基準fiberのhidden座標で読み、全有限fiberを明示的reading setとする。raw tableのbijectivityだけを独立coherenceとしてseparation・extension・effectivenessを別々に証明し、effectivenessは有限探索で逆写像を計算してnonbijective tableだけを拒否する"
  selection_reason: "Cycle 26までにlens local categoryとfinite presentation/Karoubi coherenceが揃ったため、固定GOAL D/E2の共通FiniteReading surfaceをactual lens invertible changeへ接続する直接の残余nodeである"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiniteDetermination.lean"
  risks:
    - "coherenceへglobal extendabilityを混入せず、raw tableのbijectivityだけを判定すること"
    - "reference fiberをproxy carrierへ置換せず、actual product-lens state changeのhidden座標を読むこと"
    - "separation、extension、effectivenessを一つの結論証明から循環的に導かないこと"
    - "effectivenessでEquiv.ofBijectiveの非計算的preimage choiceに逃げず、有限探索から逆写像を構成すること"
    - "all lenses、protocol branch、四分枝統合まで一般化しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the full finite reference fiber now determines actual product-lens invertible changes; intrinsic table coherence is decidable bijectivity, and a finite-search effectiveness program rejects exactly nonbijective tables and reconstructs the accepted hidden-permutation change with exact readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.readProductLensChangeAt"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.readProductLensChangeAt_eq_reference_evaluation"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.readProductLensChangeAt_eq_fiberPerm"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.fullReferenceFiber"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.TableCoherent"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.boolNegationTable_coherent"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.boolConstantFalseTable_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.finiteInverseOfBijective"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.finitePermutationOfBijective"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.fullReferenceFiber_separates"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.fullReferenceFiber_extends"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.fullReferenceFiber_determining"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.effectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination.fullReferenceFiber_effective"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: 有限readingのseparation・extension・effectivenessを独立に与える"
      - "固定 GOAL E2: lensの基準fiber tableがactual invertible changeを区別・延長する"
    conjuncts:
      - "the point reading is the hidden coordinate of the actual complete state change at the reference fiber"
      - "the same point reading is the accepted complete-update-graph fiber permutation"
      - "the full finite fiber separates actual invertible lens changes"
      - "every bijective raw table extends through the accepted hidden-permutation constructor"
      - "bijectivity is decided on the raw finite table"
      - "Boolean negation and a constant Boolean table provide explicit coherent and noncoherent instances on the same nontrivial finite carrier"
      - "finite search constructs the inverse permutation and successful extension reads back exactly"
      - "the program returns none exactly for nonbijective tables"
    undischarged_assumptions:
      - "the corresponding protocol finite-determination/effectiveness application"
      - "tagged and G-122 independent local-model equivalences"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "actual product-lens invertible-change finite determination only; no protocol, all-lens, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "arbitrary view and hidden types with a finite hidden carrier"
      - "fixed reference view and arbitrary visible permutation"
      - "accepted LensInvertibleChange hidden-permutation classification"
    direction_hypothesis: []
    discharge_required:
      - "actual reading identity / normalForm and complete-update-graph fiberPerm"
      - "separation / injectivity of equivHiddenPermutations"
      - "extension / ofHiddenPermutation applied to the raw table"
      - "effectiveness / decidable bijectivity and finite-search inverse"
      - "exact rejection and readback / EffectivenessProgram laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "global change / constructed by LensInvertibleChange.ofHiddenPermutation"
      - "permutation inverse / computed by Finset.choose over Finset.univ using unique bijective preimages"
      - "coherence decision / decide on Function.Bijective of the raw table function"
    unresolved:
      - "protocol E2 finite determination/effectiveness"
      - "tagged/G-122 local-model equivalences and all-four integration"
  proof_use:
    used:
      - "LensInvertibleChange.normalForm, equivHiddenPermutations, and ofHiddenPermutation"
      - "complete-update-graph fiberPerm identification"
      - "FiniteReading.Separates, Extends, Determining, and EffectivenessProgram"
      - "finite enumeration and decidable equality on the actual hidden carrier"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual product-lens invertible changes and the actual full reference fiber, with raw-table exact rejection"
  vacuity: "arbitrary finite hidden carriers, visible permutations, and bijective/nonbijective raw tables are retained; Boolean negation and the constant false table explicitly fire both coherence outcomes on the same two-point carrier, and no stored extension certificate or singleton filler is introduced"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LensFiniteDetermination.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.LensFiniteDetermination: pass (targeted dependency closure only)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination: 19 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the protocol-branch actual finite determination/effectiveness application, keeping its observation-aware local Hom and execution-state coherence distinct from the lens proof"
```

Cycle 27 / PR #4740 は final head
`24606707465e6d6b5b3c1f84d89bbd89f9092a88` で受理した。fresh Math A/B +
Lean A/B はすべて `No major findings`。非中心 finding だったcoherenceの正負例と
ledgerの適用範囲を同headで修正し、fresh direct checkで解消を確認した。CIは7/7
success、最終監査はPR comment `5724524278`、merge commitは
`947038b5b33cb37971bab5c0a16f7b8954a5200d` である。

## Cycle 28 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 28
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 947038b5b33cb37971bab5c0a16f7b8954a5200d
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 27 accepted evidence: PR comment 5724524278; Cycle 28 selection: Issue comment 5724541530"
  proof_dag_predecessors:
    - "accepted ProtocolInvertibleChange equivalence with operation-preserving fixed-F following changes"
    - "component-permutation restriction criteria and coherent finite extension"
    - "common FiniteReading separation, extension, determining, and effectiveness surfaces"
  proof_obligation: "actual ProtocolInvertibleChangeを各vertexのstateEquivで読み、retained named-edge上の等式を独立coherenceとする。separationとextensionの必要十分条件をそれぞれfull component meetingとinduced connectivity retentionに同定し、各full componentの選択代表集合をactual protocol決定集合へ適用する。既存の有限algorithmをactual protocol型へ戻してexact rejection/readbackを証明する"
  selection_reason: "Cycle 27でlens側を共通FiniteReading surfaceへ接続したため、固定GOAL D/E2で対になるprotocol可逆変更層が直接の残余nodeである"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolFiniteDetermination.lean"
  risks:
    - "結論をfixed-graph preserving changeで止めずactual protocol changeへ戻すこと"
    - "coherenceをglobal extensionの存在で定義せずactual retained edgeだけで定義すること"
    - "vertex tableとcomponent familyをquotientを介さず同一視しないこと"
    - "separation、extension、effectivenessを独立に保つこと"
    - "一般protocol Hom、comparison group、四分枝統合まで過大主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "actual protocol stateEquiv reading is identified with the accepted preserving-change reading; separation and extension have exact graph criteria, and the executable finite program returns an actual ProtocolInvertibleChange, rejects exactly edge-incoherent tables, and reads successful extensions back pointwise"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.readProtocolChangeAt"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.readProtocolChangeAt_eq_preservingReading"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.TableCoherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.coherentIdentityTable_coherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.incoherentSplitTable_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.separates_iff_meetsEveryFullComponent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.extends_iff_retainsFullConnectivity"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.determining_of_componentCriteria"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.representativeVertices_determining"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.effectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination.effective_of_retainsFullConnectivity"
  claim_mapping:
    source_labels:
      - "固定 GOAL D: finite readingのseparation・extension・effectivenessを独立に与える"
      - "固定 GOAL E2: protocolの有限局所tableがactual invertible changeを区別・延長する"
    conjuncts:
      - "actual stateEquiv point reading agrees with the accepted fixed-F preserving reading"
      - "separation holds exactly when retained vertices meet every full component"
      - "extension of every retained-edge coherent table holds exactly when induced connectivity is retained"
      - "the two criteria jointly give a finite determining set"
      - "the chosen representative vertex of every full component specializes those criteria to an actual protocol determining set"
      - "coherence has explicit positive and negative instances on one nontrivial witness graph"
      - "the finite program decides coherence, rejects exactly incoherent tables, and returns actual protocol changes with exact readback"
    undischarged_assumptions:
      - "general observation-aware protocol Hom finite determination"
      - "tagged and G-122 independent local-model equivalences"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "actual protocol invertible-change finite determination only; no general protocol Hom, comparison-group, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "finite fixed directed graph and finite hidden carrier"
      - "decidable equality on vertices and hidden values for the finite table algorithms"
      - "a decidable retained-vertex predicate for its explicit Finset presentation, including the chosen representative predicate in its specialization"
      - "Nontrivial K (the fixed |K| >= 2 boundary) for the converses in the two exact iff criteria"
      - "fixed graph automorphism and actual ProtocolInvertibleChange"
      - "accepted preserving-change/component-permutation classification"
    direction_hypothesis:
      - "MeetsEveryFullComponent for the forward separation construction"
      - "RetainsFullConnectivity for extension, determining, and effectiveness"
    discharge_required:
      - "actual stateEquiv/readPreservingChangeAt identification"
      - "separation iff full-component meeting"
      - "extension iff induced connectivity retention"
      - "exact rejection and protocol readback in EffectivenessProgram"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "component family / obtained through the accepted quotient classification"
      - "global change / computed by finite coherent extension then transported back through the protocol equivalence"
      - "coherence decision / equality on every actual retained named edge"
    unresolved:
      - "general protocol Hom finite determination and all-four integration"
  proof_use:
    used:
      - "ProtocolInvertibleChange.equivPreservingFollowingChanges"
      - "component restriction injectivity/surjectivity criteria"
      - "FinitePermutationExtension and FiniteEffectiveness executable APIs"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual protocol invertible changes and actual retained named edges, with exact graph criteria and raw-table rejection"
  vacuity: "the constructive separation/extension/effectiveness directions retain arbitrary finite hidden carriers; the converse exact criteria use the fixed |K| >= 2 boundary. A one-edge Boolean graph explicitly exhibits coherent and incoherent tables, and no stored extension certificate is accepted"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolFiniteDetermination.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination: pass (4357 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ProtocolFiniteDetermination: 19 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "connect the general observation-aware protocol local Hom to finite reading/effectiveness, without conflating it with the invertible state-change layer"
```

Cycle 28 / PR #4741 は final head
`ab2d74c44ced57bacc1314a5a591c9a60b0cf00e` で受理した。fresh Math A/B +
Lean A/B はすべて `No major findings`。中心 finding だった代表頂点への特殊化と
ledger premise の不一致を修正後、fresh Math A/B を再実行した。残った非中心 finding の
docstring と premise traceability は同headで修正し、fresh direct checkで解消を確認した。
CIは7/7 success、最終監査はPR comment `5724799580`、merge commitは
`7275231b3815050a2d663b44178705639c958062` である。

## Cycle 29 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 29
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 7275231b3815050a2d663b44178705639c958062
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 28 accepted evidence: PR comment 5724799580; Cycle 29 selection: Issue comment 5724817581"
  proof_dag_predecessors:
    - "Cycle 22 observation-aware protocol local Hom reading and full/faithful assembly"
    - "ProtocolRealization.GeneratorMap.ext and accepted quotient-execution extension"
    - "common FiniteReading separation, extension, determining, and effectiveness surfaces"
  proof_obligation: "general observation-preserving ProtocolRealization Homを全(vertex, source state)対で読み、vertex-tagged target stateを共通FiniteReading値とする。raw tableのcoherenceをtag decoding、named-edge square、observation equationだけで定義し、separation、extension、determiningを独立に証明する。明示的有限列挙と等値判定からexact rejection/readbackを持つEffectivenessProgramを構成し、Cycle 22のfull-faithful/assembly経路へ接続する"
  selection_reason: "Cycle 28でprotocol可逆変更層を閉じたため、固定GOAL D/E2に残るgeneral observation-aware protocol Homの有限決定性とeffectivenessが直接の残余nodeである"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedFiniteDetermination.lean"
  risks:
    - "dependent target statesを型消去せずvertex tagを保持すること"
    - "coherenceへcompleted Hom、component-family certificate、extension witnessを混入しないこと"
    - "observation carrierの有限性を要求せず、発生するtagged observation equalityだけを判定すること"
    - "semantic Finiteから非計算的Fintype.ofFiniteを導入せず、実効性の明示入力を列挙すること"
    - "lens一般Hom、comparison group、四分枝統合まで過大主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the full tagged vertex/state table now determines every actual observation-preserving protocol Hom; independently stated tag, named-edge, and observation coherence is decidable under explicit finite data, and the executable program rejects exactly incoherent tables and reconstructs an actual quotient-execution Hom with exact readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.readProtocolHomAt"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.fullInput"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.decodedAt"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.TableCoherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.read_table_coherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.not_tableCoherent_of_tag_mismatch"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.fullInput_separates"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.assembleTable"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.restrict_assembleTable"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.fullInput_extends"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.fullInput_determining"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.effectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.fullInput_effective"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.readProtocolHomAt_eq_observedRestrictionMap"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.coherentWitnessTable_coherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.incoherentTagWitnessTable_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination.cycle22_assemble_read_assembleTable"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: protocol branchのprimitive observation-aware Hom reading、separation、assembly"
      - "固定 GOAL D: finite readingのseparation・extension・effectivenessを独立に与える"
      - "固定 GOAL E2: protocolの有限局所tableがactual general Homを区別・延長する"
    conjuncts:
      - "the finite input contains every actual vertex/source-state pair and the value retains its dependent target-state tag"
      - "raw coherence consists only of successful tag decoding, all named-edge squares, and observation equations"
      - "every actual protocol Hom has a coherent table"
      - "a two-vertex Boolean protocol supplies concrete coherent and tag-mismatched incoherent raw tables"
      - "the full table separately separates and extends actual observation-preserving protocol morphisms"
      - "explicit finite enumerations and equality decisions make raw coherence decidable without finite observation carriers"
      - "the program rejects exactly incoherent input and successful extensions read back exactly"
      - "the point reading is definitionally the state component of the accepted Cycle 22 observed-restriction reading"
      - "the Hom extended from a coherent finite table is fixed by the accepted Cycle 22 read/assemble inverse"
    undischarged_assumptions:
      - "general observation-preserving lens Hom finite determination/effectiveness"
      - "tagged and G-122 independent local-model equivalences"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "general observation-aware protocol Hom finite determination only; no lens-general-Hom, comparison-group, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed finite protocol schema vertices and named edges"
      - "finite source state carrier at every vertex"
      - "decidable equality on vertices, target states, and the full tagged observation-value type"
      - "arbitrary observation carriers; no carrier Fintype is assumed"
    direction_hypothesis: []
    discharge_required:
      - "tag-safe decoding of the dependent raw output table"
      - "GeneratorMap.ext separation on every vertex/state pair"
      - "actual ProtocolRealization.ext assembly from local named-edge and observation equations"
      - "exact rejection and readback in EffectivenessProgram"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "typed components / computed by deterministic tag decoding from the raw table"
      - "global Hom / assembled by ProtocolRealization.ext from the accepted local equations"
      - "coherence decision / decide over explicit finite vertex, source-state, and named-edge enumerations"
    unresolved:
      - "lens general-Hom finite determination and all-four integration"
  proof_use:
    used:
      - "ProtocolRealization.GeneratorMap.ext and ProtocolRealization.ext"
      - "ProtocolRealization.edge_naturality and observation_app"
      - "FiniteReading.Separates, Extends, Determining, and EffectivenessProgram"
      - "Cycle 22 protocolObservedRestrictionMap and closedFamilyProtocolHom"
      - "Cycle 22 protocolObservedRestrictionAssemble and its assemble/read inverse"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual general observation-preserving protocol Hom and the full tagged vertex/state reading, with local raw-table exact rejection"
  vacuity: "arbitrary actual protocol realizations and observation carriers are retained; the two-vertex Boolean protocol supplies a concrete identity-Hom coherent table and a concrete constant-true-tag incoherent table, and no completed Hom or extension certificate occurs in TableCoherent"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedFiniteDetermination.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination: pass (4366 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination: 30 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the corresponding general observation-preserving lens Hom finite determination/effectiveness connection, then integrate the remaining tagged/G-122 branches without weakening the fixed target"
```

Cycle 29 / PR #4742 は final head
`5821c9aca927d2d42b1ef342b3274158d485bac5` で受理した。初回4 laneで
Cycle 22 assembly経路への接続不足と具体的coherence正負fixture不足を検出し、修正後の
fresh Math A/B + Lean A/Bでは中心findingなし。残ったProof state同期はfresh direct checkで
解消を確認した。CIは7/7 success、最終監査はPR comment `5725135405`、merge commitは
`7433561e506d5aef1d8312a18642e83bbaf70d16` である。

## Cycle 30 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 30
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 7433561e506d5aef1d8312a18642e83bbaf70d16
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 29 accepted evidence: PR comment 5725135405; Cycle 30 selection: Issue comment 5725155616"
  proof_dag_predecessors:
    - "Cycle 25 general LensRealization Hom restriction/extension and full-faithful fiber reading"
    - "LensRealization.homEquivFiberMap, res_ext, and ext_res"
    - "common FiniteReading separation, extension, determining, and effectiveness surfaces"
  proof_obligation: "actual LensRealization Homをsource reference fiberの全stateで読み、任意raw fiber tableがLensRealization.extで延長するtotal admissibilityをcertificateなしで固定する。separation、extension、determining、常時成功してexact readbackするEffectivenessProgramを独立に構成し、Cycle 25のsemantic/closed-family fiber readingへ接続する。二点fiberの非単射tableからactual noninvertible Homを与える"
  selection_reason: "Cycle 29でprotocol一般Homを共通FiniteReadingへ接続したため、固定GOAL D/E2に残るlens一般意味保存射層が対になる直接の残余nodeである"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean"
  risks:
    - "total admissibilityを未検証の空虚predicateにせず、LensRealization.extの全域性とreadbackから固定すること"
    - "product-lens proxyだけで止めず、任意のactual source/target LensRealization Homを結論型にすること"
    - "可逆性や全単射性をadmissibilityへ混入せず、非単射tableのactual例を保持すること"
    - "semantic FiniteからFintype.ofFiniteを導入せず、実効programでは明示Fintype入力を使うこと"
    - "protocol、tagged/G-122、comparison group、四分枝統合まで過大主張しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the full finite source fiber now determines every actual get/put-preserving lens Hom; every raw fiber table is intrinsically admissible and extends through LensRealization.ext, while an explicit program always returns the actual Hom with exact readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.readLensHomAt"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.fullFiber"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.TableAdmissible"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.tableAdmissible"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.no_inadmissible_table"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.fullFiber_separates"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.assembleTable"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.restrict_assembleTable"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.fullFiber_extends"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.fullFiber_determining"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.effectivenessProgram"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.fullFiber_effective"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.readLensHomAt_eq_semanticFiberReading"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.readLensHomAt_eq_closedFamilyFiberReading"
    - "AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination.constantFalseHom_res_not_injective"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: lens branchのprimitive fiber Hom reading、separation、assembly"
      - "固定 GOAL D: finite readingのseparation・extension・effectivenessを独立に与える"
      - "固定 GOAL E2: lensの有限局所tableがactual general Homを区別・延長する"
    conjuncts:
      - "the input is the entire actual source reference fiber and the value is the actual target fiber"
      - "every raw table is admissible because LensRealization.ext is total on fiber maps"
      - "no completed Hom or extension witness occurs in TableAdmissible"
      - "the full table separately separates and extends actual get/put-preserving morphisms"
      - "the explicit program never rejects and every successful extension reads back exactly"
      - "the point reading is definitionally the accepted Cycle 25 semantic and closed-family fiber reading"
      - "a constant table on a two-point fiber extends to an actual Hom whose fiber restriction is not injective"
    undischarged_assumptions:
      - "tagged and G-122 independent local-model equivalences"
      - "comparison-group recovery on the final common reading"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
    acceptance_point: "general get/put-preserving lens Hom finite determination only; no tagged/G-122, comparison-group, or all-four reconstruction claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed view type, reference value, and arbitrary actual source/target LensRealization"
      - "explicit Fintype enumeration of the source reference fiber"
    direction_hypothesis: []
    discharge_required:
      - "actual LensRealization.res point reading"
      - "homEquivFiberMap separation"
      - "actual LensRealization.ext assembly and res_ext readback"
      - "always-successful EffectivenessProgram with exact readback"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "global Hom / assembled directly by LensRealization.ext from the raw table"
      - "admissibility / theorem that all raw tables are accepted and no inadmissible table exists"
      - "effectiveness decision / constant true because total extension is already proved"
    unresolved:
      - "tagged/G-122 local-model equivalences and all-four integration"
  proof_use:
    used:
      - "LensRealization.homEquivFiberMap, res_ext, ext_res, and ext"
      - "Cycle 25 lensSemanticFiberReading and lensFiberValueReading"
      - "FiniteReading.Separates, Extends, Determining, and EffectivenessProgram"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual general get/put-preserving lens Hom and the full actual source reference fiber"
  vacuity: "arbitrary actual lens realizations and all raw fiber maps are retained; a concrete two-point constant table yields an admitted noninjective actual Hom, while total admissibility is separately justified by LensRealization.ext"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination: pass (4365 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination: 23 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct a tagged or G-122 independent local-model equivalence and connect its primitive reading to the common four-family reconstruction surface"
```

Cycle 30 / PR #4743 は final head
`bb01d1ae750721580783da4e02bfe402140c38c6` で受理した。fresh Math A/B + Lean A/Bで
中心findingはなく、Lean Aのみが指摘したdocstringのtraceability不足は限定修正後の
fresh direct checkで解消を確認した。CIは7/7 success、最終監査はPR comment `5725264524`、
merge commitは `f7c3706b365d1b0f2cbeb25d890866f10d716c41` である。

## Cycle 31 selection and result proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 31
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: f7c3706b365d1b0f2cbeb25d890866f10d716c41
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 30 accepted evidence: PR comment 5725264524; Cycle 31 selection: Issue comment 5725305206"
  proof_dag_predecessors:
    - "Cycle 17 actual tagged source-choice automorphism subgroup and its noncomputable effectiveness obstruction"
    - "Cycle 18 accepted group equivalence between the actual subgroup and coherent all-finite tables"
    - "Cycle 2 actual finite-subset tables, restriction equations, and singleton assembly"
  proof_obligation: "actual taggedSourceChoiceAutSubgroupをone-objectのglobal categoryとし、actual finite-subset posetをrestriction index、各成分を有限LocalTagTable、包含射をprimitive restrictionとする反変図式を構成する。global witnessを持たないcompatible section群とactual subgroupのaccepted MulEquivをdeloopし、Hom separation・assemblyとHom read/assembleのCycle 18 constructorへの一致を固定する"
  selection_reason: "Cycle 29--30でprotocol/lens一般Homの有限決定性を放電したため、固定GOAL B/E1に残るactual tagged branchの主同値への直接接続を次のnodeとする"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeLocalModelEquivalence.lean"
  risks:
    - "local objectやmorphismにactual global automorphismまたはextension witnessを格納しないこと"
    - "accepted subgroupを拡張してfull tagged normalization categoryまで放電したと言わないこと"
    - "noncomputableな同値とCycle 17のactual-output effectiveness blockerを混同しないこと"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the actual finite-subset poset now indexes a contravariant diagram whose component at S is the finite Bool table on S and whose arrows are primitive restrictions; its compatible-section group contains only those local tables and equations, and the accepted actual tagged source-choice subgroup is categorically equivalent to the delooping of that section group with Hom inverse fixed by the Cycle 18 constructor"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.restrictionHom"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.localTableDiagram"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.localTableDiagram_finite"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.localSection_naturality"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.reading"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.reading_map_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.morphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.morphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.objectAssembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.equivalence"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.homEquiv_apply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.homEquiv_symm"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence.homEquiv_symm_eq_accepted_constructor"
  claim_mapping:
    source_labels:
      - "固定 GOAL B: actual tagged source-choice Hom sliceの独立local modelとprimitive reading同値"
      - "固定 GOAL E1b: C2^Omega finite-restriction reconstructionとBの主同値によるsource-choice recoveryの同定"
    conjuncts:
      - "the outer restriction index is the actual poset of finite subsets"
      - "the local component at S is the finite type LocalTagTable S and inclusion maps are primitive restrictions"
      - "compatible sections contain only finite tables and restriction equations, with no global automorphism or extension witness"
      - "the accepted actual-subgroup/coherent-family MulEquiv supplies the categorical delooping equivalence"
      - "morphism separation, morphism assembly, and the explicitly limited one-object assembly are proved separately"
      - "Hom assembly is characterized both by the inverse accepted MulEquiv and by the Cycle 18 accepted constructor"
    undischarged_assumptions:
      - "canonical-normalization arrows and the full tagged category"
      - "the G-122 branch and its local-model equivalence"
      - "the final common Lambda_Theta, M_Theta, N_Theta, and D_Theta"
      - "computable actual-output effectiveness for source-choice assembly"
    acceptance_point: "actual tagged source-choice automorphism Hom slice only; no full tagged normalization, G-122, all-four equivalence, or computability claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "the accepted actual taggedSourceChoiceAutSubgroup"
      - "the actual finite-subset restriction poset and its finite LocalTagTable components"
      - "the compatible-section group defined by all restriction equations"
    direction_hypothesis: []
    discharge_required:
      - "injectivity and surjectivity of the primitive Hom reading"
      - "finite-valued contravariant restriction diagram and section naturality"
      - "identification of the Hom inverse with the accepted constructor"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "Hom reconstruction / the accepted taggedSourceChoiceSubgroupMulEquivCoherentFamily"
      - "finite-local diagram / actual finite subsets, finite Bool tables, and primitive restrictions"
    unresolved:
      - "full tagged normalization and all-four integration"
      - "actual-output computation"
  proof_use:
    used:
      - "taggedSourceChoiceSubgroupMulEquivCoherentFamily and its finite-value theorem"
      - "taggedSourceChoiceSubgroupMulEquivCoherentFamily_symm"
      - "TagChange.LocalTagTable.restrict, finite_value_type, and CoherentFamily.coherent"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual tagged source-choice automorphism subgroup Hom slice, actual finite-subset restriction index, finite local tables, and compatible sections"
  vacuity: "the global Hom type is the accepted actual automorphism subgroup; every local component is finite and only its compatible section family is delooped; fullness uses the inverse accepted equivalence rather than a stored witness"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeLocalModelEquivalence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence: pass (4353 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeLocalModelEquivalence: 21 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "extend the tagged reconstruction from the source-choice automorphism Hom slice to canonical-normalization arrows or construct the G-122 independent local-model branch, then integrate the common four-family reconstruction surface without weakening the fixed target"
```

Cycle 31 / PR #4744 は final head
`436e60bd8b6d288eed147e34c1a4f60569433189` で受理した。初回4 laneでPUnit唯一成分に
全整合族を格納する中心findingを検出し、actual finite-subset poset・有限table成分・
primitive restrictionの反変図式へ作り直した。修正後のfresh Math A/B + Lean A/Bは
すべてfindingなし、CIは7/7 success、最終監査はPR comment `5725554013`、
merge commitは `5705fefcb1d53c7aea760d262d441b974d42f238` である。

## Cycle 32 selection and blocker proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 32
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 5705fefcb1d53c7aea760d262d441b974d42f238
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 31 accepted evidence: PR comment 5725554013; Cycle 32 selection: Issue comment 5725567900"
  proof_dag_predecessors:
    - "Cycle 31 actual finite-subset local diagram and source-choice subgroup equivalence"
    - "AATUniformFlipKaroubi canonical normalized tagged object and uniform-flip automorphism"
    - "AATClosedFamilySignature arbitrary actual source-choice package maps"
  proof_obligation: "canonical normalization functorがfull actual source-choice族をsingle normalized Karoubi objectへ送るとき、元のchoiceをfaithfulに回復できるかを判定する"
  selection_reason: "Cycle 31のHom-sliceをcanonical normalizationを含むfull tagged branchへ接続する最短候補経路だったため"
  expected_result_type: blocker-fixed
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeKaroubiReconstruction.lean"
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: "normalization-invariant choices commute with canonical normalization and actual commutation forces invariance; independently, a choice supported at a moved source is distinct from false but their left-normalized actual package maps coincide, so the canonical normalized-image map is noninjective on the full source-choice family"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.NormalizationInvariant"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.normalizationInvariant_const"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.taggedSourceChoiceTotal_commutes_normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.normalizationInvariant_of_commutes"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.taggedCanonicalNormalization_not_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.exists_source_moved_by_normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.separatingChoice_not_invariant"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.moved_source_not_in_normalization_image"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.canonicalNormalization_sourceChoice_map_not_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction.exists_sourceChoice_not_commuting_normalization"
  claim_mapping:
    source_labels:
      - "fixed GOAL A/B tagged family must retain all source-choice members and canonical normalization"
      - "Cycle 32 attempted route: recover the whole family through the canonical normalized-image map on one normalized Karoubi object"
    conjuncts:
      - "normalization-invariant choices commute as actual PackageTotalHom values"
      - "actual commutation implies normalization invariance by tagged identity-operation evaluation"
      - "the actual tagged object normalization is noninjective"
      - "a moved source yields a concrete noninvariant choice and actual noncommuting source-choice map"
      - "a choice supported at a moved source and the false choice are distinct before normalization but have equal left-normalized actual package maps"
    undischarged_assumptions:
      - "choice of a faithful replacement route; retaining ambient tagged source objects and normalization arrows is one candidate"
      - "full tagged object and Hom reconstruction"
      - "G-122 and final all-four integration"
    acceptance_point: "nonfaithfulness of the canonical normalized-image route only; every source-choice automorphism can still have a Karoubi image, other single-object presentations are not excluded, and fixed G-124 remains active and unchanged"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "actual taggedOperationPackage and its accepted canonical normalization"
      - "arbitrary actual taggedSourceChoiceTotal choice"
    direction_hypothesis:
      - "NormalizationInvariant is used only for the sufficient direction and is derived from commutation in the converse"
    discharge_required:
      - "componentwise package commutation under invariance"
      - "readback of commutation at taggedIdentityOperation"
      - "actual noninjectivity and a moved-source witness"
      - "noninjectivity of left normalization on the actual source-choice family"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "invariance necessity / evaluation of the actual equality on the existing tagged identity operation"
      - "moved source / contradiction with actual canonical-normalization noninjectivity"
      - "counterexample choice / equality test against the moved source's normalized image"
      - "normalized-image collision / idempotence excludes the moved source from the normalization image"
    unresolved: []
  proof_use:
    used:
      - "canonicalObjectNormalization_eq_of_configuration_eq"
      - "finiteAxisFoldUnitObject_ne_boolObject and equal configurations"
      - "taggedSourceChoiceTotal and taggedIdentityOperation"
      - "taggedOperationCast_uniformFlip"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "actual full source-choice family and actual canonical normalization; proves only that the canonical normalized-image map loses source-choice information needed for reconstruction"
  vacuity: "the noncommuting witness is an actual unrestricted source choice constructed from an actual moved architecture object"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeKaroubiReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction: pass (4354 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeKaroubiReconstruction: 14 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct a faithful replacement route; the leading candidate retains ambient tagged source objects and canonical-normalization arrows and connects them to Cycle 31 finite-local readings"
```

## Cycle 33 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 33
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: af6037910ecf5466c7d02fbe52025402cf646503
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 32 accepted evidence: PR comment 5725808724; Cycle 33 selection: Issue comment 5725821086"
  proof_dag_predecessors:
    - "Cycle 31 actual source-choice subgroup and finite-local equivalence"
    - "Cycle 32 canonical normalized-image nonfaithfulness blocker"
    - "AATUniformFlipKaroubi admissible tagged package and canonical normalization"
  proof_obligation: "place the full source-choice family faithfully as automorphisms of the actual tagged admissible package while retaining canonical normalization as an endomorphism of that same object, and recover the constant-true t^2=1, et=te, et!=e laws"
  selection_reason: "avoids Cycle 32 information loss before Karoubi normalization and directly discharges the tagged-family coexistence checkpoint of fixed GOAL A/E1"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeAmbientCategory.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the accepted tagged admissible package now carries every actual source choice as a faithful automorphism family and carries canonical normalization as an endomorphism before applying the nonfaithful canonical normalized-image map; the constant-true member is identified with the accepted uniform flip and satisfies the required three laws in the same ambient category"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.TaggedPackage"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceMorphism"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceAut"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceAut_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceAutHom"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceAutHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceSubgroup"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceGroupEquiv"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceMorphism_true_square"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceMorphism_true_commutes_normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.normalization_comp_sourceChoiceMorphism_true_ne_normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory.sourceChoiceMorphism_true_comp_normalization_ne_normalization"
  claim_mapping:
    source_labels:
      - "fixed GOAL A tagged family: taggedOperationPackage, canonical normalization, uniform flip, and every source choice"
      - "fixed GOAL E1a and uniform-flip separation"
    conjuncts:
      - "all source choices are actual automorphisms of one accepted admissible package object"
      - "the source-choice map and its induced group homomorphism are injective before normalization"
      - "canonical normalization is an actual endomorphism of the same object"
      - "the constant-true source choice is the accepted uniform flip and satisfies square, commutation, and separation"
    undischarged_assumptions:
      - "the common four-family R_Theta and local model M_Theta"
      - "finite-local reconstruction of all ambient package morphisms"
      - "G-122, lens, and protocol integration"
    acceptance_point: "actual faithful tagged package-level family and normalization coexistence only; not the final full realization category or a reconstruction of every ambient Hom"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "the accepted taggedUniformFlipPackage object in CanonicalNormalizationAdmissiblePackage"
      - "the accepted actual taggedSourceChoiceTotal family"
    discharge_required:
      - "ambient identity and xor composition"
      - "source-choice involutivity and injectivity"
      - "constant-true identification and the three accepted normalization laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "automorphism inverse / pointwise xor self-cancellation"
      - "faithfulness / taggedSourceChoiceTotal readback injectivity"
      - "uniform-flip laws / accepted actual package equalities lifted through ObjectProperty.homMk"
    unresolved: []
  proof_use:
    used:
      - "taggedSourceChoiceExplicitExactGeometryMorphism_false and _comp"
      - "taggedSourceChoiceTotal_injective"
      - "taggedUniformFlipMorphism_square and _commutes_normalization"
      - "taggedNormalizationThenUniformFlip_ne_normalization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "the actual full source-choice family and actual canonical normalization coexist before applying the nonfaithful normalized-image map"
  vacuity: "injectivity is inherited from actual tagged identity-operation readback, and the constant-true member is separated from normalization by the accepted package-level inequality"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeAmbientCategory.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientCategory: pass (4355 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeAmbientCategory: 16 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "identify the ambient package-level source-choice subgroup with the Cycle 31 finite-local subgroup equivalence and state the boundary before extending readings to larger ambient Hom sets"
```

## Cycle 34 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 34
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 2a1c70fdbb680511a731e9d83e6b8b4131c942b1
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 33 accepted evidence: PR comment 5725960520; Cycle 34 selection: Issue comment 5725969652"
  proof_dag_predecessors:
    - "Cycle 31 finite-subset restriction diagram and compatible-section category"
    - "Cycle 33 faithful ambient package-level source-choice subgroup"
  proof_obligation: "identify the actual ambient package-level source-choice subgroup with compatible sections of the finite Bool-table diagram; verify every finite component against actual PackageTotalHom readback and identify inverse assembly with the ambient package automorphism constructor"
  selection_reason: "directly connects fixed GOAL E1b finite-restriction reconstruction to the actual family that coexists with canonical normalization"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeAmbientLocalEquivalence.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the faithful ambient package-level subgroup is now group-equivalent and categorically equivalent to Cycle 31 compatible finite-local sections; forward values are actual finite restrictions of package readback and inverse values are singleton-assembled actual ambient automorphisms"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.subgroupMulEquivCoherentFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.readAmbientSourceChoiceAt"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.readAmbientSourceChoiceAt_eq"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.subgroupMulEquivCoherentFamily_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.subgroupMulEquivCoherentFamily_symm"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.reading"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.reading_map_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.morphismSeparates"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.morphismAssembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.objectAssembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence.equivalence"
  claim_mapping:
    source_labels:
      - "fixed GOAL B Hom separation/assembly on the selected tagged source-choice slice"
      - "fixed GOAL E1b all-finite restriction reconstruction"
    conjuncts:
      - "ambient subgroup is group-equivalent to compatible finite Bool-table sections"
      - "each finite value is primitive restriction of actual package readback"
      - "inverse is singleton assembly followed by the actual ambient automorphism constructor"
      - "delooping gives Hom separation, Hom assembly, object assembly, and a category equivalence"
    undischarged_assumptions:
      - "local readings sufficient for canonical normalization and arbitrary ambient package Hom"
      - "common four-family R_Theta/M_Theta/N_Theta"
      - "G-122, lens, and protocol integration"
    acceptance_point: "actual ambient source-choice Hom slice only; canonical normalization coexists in the ambient category but is not encoded by Bool source-choice tables"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "Cycle 33 sourceChoiceSubgroup"
      - "Cycle 31 actual finite-table diagram and coherent families"
    discharge_required:
      - "actual package readback recovers the classified source choice"
      - "finite component values agree with primitive restriction"
      - "group and categorical inverse use singleton assembly"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "readback / existing taggedIdentityOperation evaluation on taggedSourceChoiceTotal"
      - "assembly / existing TagChange.assemble applied before sourceChoiceGroupEquiv"
      - "categorical equivalence / delooping of the constructed actual-group equivalence"
    unresolved: []
  proof_use:
    used:
      - "TagChangeAmbientCategory.sourceChoiceGroupEquiv"
      - "TagChange.globalTagChangeMulEquivCoherentFamily"
      - "readTaggedSourceChoice_taggedSourceChoiceTotal"
      - "TagChangeLocalModelEquivalence.LocalCategory and RestrictionIndex"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "connects the actual package-level family retained beside normalization to the accepted finite-local E1b presentation without claiming that the same Bool tables reconstruct normalization"
  vacuity: "the global side is the injective actual package automorphism subgroup and every local side component is a finite Bool table"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeAmbientLocalEquivalence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence: pass (4356 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeAmbientLocalEquivalence: 15 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "specify the additional local values and separation/assembly obligations needed to extend the tagged branch beyond source-choice automorphisms to normalization and the larger ambient Hom class"
```

## Cycle 35 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 35
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 2523f2c8990273a1a5955c3e9ade83d925bfc8a9
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 34 accepted evidence: PR comment 5726072482; Cycle 35 selection: Issue comment 5726082129"
  proof_dag_predecessors:
    - "Cycle 32 canonical normalized-image nonfaithfulness witness"
    - "Cycle 34 actual ambient package readback and finite-local reconstruction"
  proof_obligation: "construct canonical restriction of choices along object normalization, prove it is an idempotent retraction onto normalization-invariant choices, classify equality of left-normalized actual package maps exactly by equality of restricted choices, and recover faithfulness on invariant choices"
  selection_reason: "upgrades Cycle 32 from one collision to the exact kernel needed for a generated tagged endomorphism normal form"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeNormalizedChoiceKernel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "canonical source restriction is an idempotent retraction onto invariant choices; actual left-normalized package-map equality is equivalent to equality after that retraction; the normalized-image map is injective on invariant choices"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalizeChoice"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalizeChoice_invariant"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalizeChoice_idempotent"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalizeChoice_eq_iff"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.InvariantChoice"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.toInvariantChoice"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.toInvariantChoice_retract"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalization_comp_sourceChoice_eq_normalized"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.readTaggedSourceChoice_normalization_comp"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.normalization_comp_sourceChoice_eq_iff"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel.invariant_normalizedImage_injective"
  claim_mapping:
    source_labels:
      - "fixed GOAL A/E1 tagged source-choice family and canonical normalization"
      - "Cycle 32 normalized-image information-loss blocker"
    conjuncts:
      - "choice restriction along normalization lands in invariant choices and retracts them"
      - "actual normalized package readback is exactly the restricted choice"
      - "actual map collision iff restricted choices coincide"
      - "restriction to invariant choices restores injectivity"
    undischarged_assumptions:
      - "generated endomorphism normal form including raw choices and normalization"
      - "finite-local values and composition for that generated monoid"
      - "common four-family R_Theta/M_Theta/N_Theta"
    acceptance_point: "exact kernel of the canonical normalized-image map on the actual source-choice family only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "actual taggedOperationPackage normalization and taggedSourceChoiceTotal"
      - "existing tagged-identity-operation readback"
    discharge_required:
      - "restriction idempotence and fixed-point characterization"
      - "actual normalized-map readback"
      - "both directions of the exact collision classification"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "idempotence / canonicalObjectNormalization_idempotent"
      - "readback / evaluation of the actual composed PackageTotalHom"
      - "collision converse / componentwise actual package equality theorem from Cycle 32"
    unresolved: []
  proof_use:
    used:
      - "canonicalObjectNormalization_idempotent"
      - "cast_operation_snd and taggedIdentityOperation"
      - "canonicalNormalization_comp_taggedSourceChoiceTotal_eq_of_normalized"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "classifies precisely the information retained by canonical normalization without pretending the full source-choice family remains faithful"
  vacuity: "Cycle 32 supplies actual distinct choices in one retraction fiber, while this Cycle also proves injectivity on the nonempty invariant subtype"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeNormalizedChoiceKernel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel: pass (4357 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeNormalizedChoiceKernel: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct and prove composition laws for a faithful normal form of the tagged submonoid generated by raw source choices and canonical normalization"
```

## Cycle 36 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 36
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 796e99d40e4b0ce44b2e7f3a3bd09f71483e0525
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 35 accepted evidence: PR comment 5726210001; Cycle 36 selection: Issue comment 5726214168"
  proof_dag_predecessors:
    - "Cycle 33 actual ambient source-choice automorphisms and canonical normalization"
    - "Cycle 35 exact normalized-choice collision classification"
  proof_obligation: "construct a faithful normal form for the actual tagged endomorphism submonoid generated by all raw source choices and canonical normalization, prove its complete composition table and branch separation, and identify its represented image with the generated submonoid"
  selection_reason: "turns the retained ambient generators and Cycle 35 restriction law into an exact algebraic presentation before finite-local reconstruction"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedNormalForm.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "every generated actual tagged endomorphism has a unique raw or normalized normal form; multiplication is explicit and restricts the right choice exactly after normalization; the normal-form image equals the submonoid closure of the actual generators"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.NormalForm"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.evaluate"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.normalization_ne_identity"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.normalization_ne_sourceChoiceMorphism"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.read_sourceChoice_comp_normalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.raw_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.normalized_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.raw_ne_normalized"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.evaluate_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.normalization_comp_sourceChoice_rewrite"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.multiply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.evaluate_multiply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.evaluationHom"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.representedSubmonoid_eq_actualGenerated"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm.normalFormMulEquivGenerated"
  claim_mapping:
    source_labels:
      - "fixed GOAL A tagged source-choice family and canonical normalization"
      - "Cycle 35 canonical restriction and invariant-choice rewrite"
    conjuncts:
      - "raw and normalization-final constructors are each faithful and mutually disjoint"
      - "four-case composition is actual ambient categorical composition"
      - "normal forms carry the induced monoid structure without an assumed closure certificate"
      - "the faithful image is exactly the submonoid generated by the actual ambient generators"
    undischarged_assumptions:
      - "finite-local reading, composition, separation, and assembly for the normal-form monoid"
      - "common four-family R_Theta/M_Theta/N_Theta"
    acceptance_point: "exact generated tagged endomorphism submonoid only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "actual TagChangeAmbientCategory.TaggedPackage endomorphisms"
      - "actual sourceChoiceMorphism and canonical normalization"
    discharge_required:
      - "normalization is distinct from every raw source-choice automorphism"
      - "normalized constructor reads back the full source choice"
      - "all four composition cases agree with actual ambient composition"
      - "represented range equals the closure of the actual generators"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "branch separation / actual noncommutation witness plus source-choice involutions"
      - "normalized readback / evaluation of the actual composed PackageTotalHom"
      - "composition / Cycle 33 xor law, Cycle 35 restriction rewrite, and actual normalization idempotence"
      - "generated image / two inclusions against Submonoid.closure"
    unresolved: []
  proof_use:
    used:
      - "sourceChoiceMorphism_comp and sourceChoiceMorphism_false"
      - "canonicalPackageNormalization_idem"
      - "exists_sourceChoice_not_commuting_normalization"
      - "normalizeChoice_invariant and normalization_comp_sourceChoice_eq_normalized"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "classifies the actual generated ambient endomorphisms before constructing their finite-local presentation, without placing a global choice inside one local value"
  vacuity: "both constructors are inhabited; canonical normalization is proved nonidentity and disjoint from every raw source-choice morphism"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedNormalForm.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm: pass (4358 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedNormalForm: 41 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct a finite-local model of a normalization flag plus compatible finite Bool tables, prove its componentwise composition law, and identify it with the actual generated normal-form monoid"
```

## Cycle 37 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 37
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 8a7fb13571039012551efeef505d9980708a8196
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 36 accepted evidence: PR comment 5726407415; Cycle 37 selection: Issue comment 5726414042"
  proof_dag_predecessors:
    - "Cycle 31 compatible all-finite Bool-table families and singleton assembly"
    - "Cycle 36 faithful actual generated-endomorphism normal form"
  proof_obligation: "construct a finite-local model consisting of a normalization flag and compatible finite Bool tables, define normalization and composition directly on finite tables, prove separation and assembly, and identify the model with the actual generated tagged endomorphism submonoid"
  selection_reason: "discharges the finite-local obligation left by Cycle 36 without storing a global choice or completed morphism in one local value"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "local values are finite flag/table pairs on finite normalization closures; compatible sections contain only restriction-coherent finite tables; normalization and multiplication are same-index finite operations; componentwise multiplication is monoid-equivalent to the actual generated submonoid and the complete flag/table value is primitive actual package readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.LocalValue"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.localValue_finite"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.restrict"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.LocalSection"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.value_restrict"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalizationClosure"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalizeFamily"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalizeFamily_read"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalizeLocalTable"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalizeFamily_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalFormEquivLocalSection"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.multiply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.read_multiply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.normalFormMulEquivLocalSection"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.primitiveNormalizationFlag"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection_normalized"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection_localValue"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.separates"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.assembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel.multiply_value"
  claim_mapping:
    source_labels:
      - "fixed GOAL A finite local values and primitive restrictions"
      - "fixed GOAL B separation and assembly"
      - "Cycle 36 actual generated tagged endomorphism submonoid"
    conjuncts:
      - "each indexed value is a finite Bool flag/table pair"
      - "section compatibility is primitive finite-table restriction"
      - "normalization and multiplication are computed from the same finite normalization-closed component"
      - "finite local reading is bijective and multiplicative"
      - "the flag is read from the actual upper object map and each table from actual package operation readback"
    undischarged_assumptions:
      - "one-object categorical equivalence and object assembly for the generated branch"
      - "common four-family R_Theta/M_Theta/N_Theta"
    acceptance_point: "finite-local monoid reconstruction of the actual generated tagged endomorphisms only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "Cycle 36 actualGeneratedSubmonoid and faithful normal-form equivalence"
      - "independently defined all-finite CoherentFamily"
    discharge_required:
      - "finite value type and restriction compatibility"
      - "same-index normalization on a finite closure agrees with global normalization reading"
      - "componentwise composition agrees with actual composition"
      - "reading separation, assembly, and primitive actual readback"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local finiteness / Bool and finite-domain Bool table"
      - "assembly / singleton assembly of compatible finite tables"
      - "composition / same-index normalization-closure lookup and pointwise xor"
      - "actual identification / composition of Cycle 36 and finite-section monoid equivalences"
      - "primitive flag readback / actual upper objectMap evaluated at a fixed moved source"
      - "primitive table readback / raw and normalization-final actual PackageTotalHom operationMap evaluation"
    unresolved: []
  proof_use:
    used:
      - "TagChange.read_assemble and assemble_read"
      - "TagChangeGeneratedNormalForm.evaluate_injective and evaluate_multiply through the Cycle 36 equivalence"
      - "readTaggedSourceChoice_taggedSourceChoiceTotal"
      - "read_sourceChoice_comp_normalization"
      - "exists_source_moved_by_normalization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "uses actual finite indices and primitive restrictions; one local value contains no global choice, extension witness, or completed ambient morphism"
  vacuity: "raw and normalized flags are both represented, and every compatible finite family assembles to an actual generated endomorphism"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel: pass (4359 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedLocalModel: 57 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "deloop the actual generated submonoid/local-section monoid equivalence and state Hom reading, Hom assembly, and object assembly as an explicit one-object categorical equivalence"
```

### Cycle 37 initial review remediation

初回4レーンでは、二つの中心 finding が出た。第一に、旧 `LocalValue S` は `S` 上の表だけを
持つため、正規化後の参照先 `n(S)` を同じ成分から計算できず、合成則を成分ごとと呼べなかった。
第二に、正規化 flag は normal-form 同値の逆から得ており、actual morphism の原始 readback では
なかった。修正では `LocalValue S` の表を有限閉包 `S ∪ n(S)` 上に取り、冪等性から閉包内で
完結する `normalizeLocalTable` と `multiplyLocalValue` を定義した。さらに canonical normalization
で動く固定 source を選び、actual `upper.objectMap` のその点での値から flag を直接読み、
actual `operationMap` 由来の有限表と合わせた完全な local value readback を証明した。

## Cycle 38 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 38
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: a4d2c26a731c1bdb17a89b664980faf18e698753
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 37 accepted evidence: PR comment 5726786037; Cycle 38 selection: Issue comment 5726791876"
  proof_dag_predecessors:
    - "Cycle 36 actual generated tagged endomorphism normal form"
    - "Cycle 37 finite-local monoid equivalence and primitive full-value readback"
  proof_obligation: "deloop the actual generated submonoid/local-section monoid equivalence and state primitive Hom reading, Hom assembly, and object assembly as an explicit one-object categorical equivalence"
  selection_reason: "completes the categorical packaging left explicitly open by Cycle 37 without extending the claim to the common four-family category"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedCategoryEquivalence.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the actual generated tagged endomorphism submonoid and finite-local section monoid are delooped to equivalent one-object categories; the forward Hom map is primitive full-value reading, the inverse is normal-form assembly, and the sole local object is assembled"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.GlobalCategory"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.LocalCategory"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.reading"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.reading_map_value"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.morphism_separates"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.morphism_assembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.object_assembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.equivalence"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.homEquiv"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence.homEquiv_symm_eq_assemble"
  claim_mapping:
    source_labels:
      - "Cycle 38 branch-local categorical packaging obligation"
      - "Cycle 37 actual generated finite-local monoid reconstruction"
    conjuncts:
      - "the forward categorical Hom map is primitive actual flag/table reading"
      - "the Hom map is bijective and its inverse is explicit normal-form assembly"
      - "the one local object is in the essential image"
      - "the resulting functor is a categorical equivalence"
    undischarged_assumptions:
      - "common four-family R_Theta/M_Theta/N_Theta"
      - "fixed GOAL B object assembly for arbitrary objects of the common local-model category"
    acceptance_point: "one-object categorical equivalence for the actual generated tagged endomorphism branch only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "Cycle 37 actualGeneratedMulEquivLocalSection"
    discharge_required:
      - "primitive Hom reading"
      - "Hom separation and assembly"
      - "essential-image witness for the sole SingleObj local object"
      - "categorical equivalence"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "Hom reading / actual objectMap and operationMap through Cycle 37"
      - "Hom assembly / LocalSection.assemble followed by Cycle 36 normal-form evaluation"
      - "branch-local object witness / the unique object of SingleObj"
    unresolved:
      - "fixed GOAL B object assembly outside this one-object branch"
  proof_use:
    used:
      - "actualGeneratedMulEquivLocalSection_localValue"
      - "actualGeneratedMulEquivLocalSection.toSingleObjEquiv"
      - "normalFormMulEquivGenerated and LocalSection.assemble"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "packages the actual generated branch categorically while retaining primitive finite-local Hom values"
  vacuity: "both raw and normalized actual endomorphisms occur as Homs; the sole-object witness is only branch-local and is not counted as fixed GOAL B object assembly"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeGeneratedCategoryEquivalence.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence: pass (4360 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence: 13 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "connect the accepted tagged generated categorical equivalence to a common four-family local-reading surface without weakening the fixed target"
```

## Cycle 39 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 39
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 9adad0f30d4b9de40bc264dc0194b32e1949e54b
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 38 accepted evidence: PR comment 5726992284; Cycle 39 selection: Issue comment 5726997447"
  proof_dag_predecessors:
    - "Cycle 38 generated tagged one-object categorical equivalence"
    - "common tagged fiber FamilyRealization .taggedOperation with ExplicitExactGeometryHom"
    - "existing package-level canonical normalization"
  proof_obligation: "construct the missing ExplicitExactGeometryHom lift of canonical tagged normalization from actual coverage, overlap, coefficient, raw, and realization data, and place it as an actual Hom in the common tagged FamilyRealization fiber"
  selection_reason: "the Cycle 38 global Hom is package-level, whereas the common tagged Hom is explicit exact geometry; without this constructed lift the generated branch cannot be mapped to the common realization surface"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometry.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "canonical tagged package normalization now carries all six explicit exact-geometry components and is an actual Hom in FamilyRealization .taggedOperation, with its package base fixed to the accepted normalization"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry.normalizationExplicitExactGeometryHom_base"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry.closedFamilyTaggedNormalization"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry.closedFamilyTaggedNormalization_base"
  claim_mapping:
    source_labels:
      - "fixed GOAL A canonical normalization in the tagged family"
      - "common tagged FamilyRealization Hom surface"
    conjuncts:
      - "coverage and overlap are constructed on the unchanged tagged geometry"
      - "coefficient and raw transport are constructed as identity exact data"
      - "explicit realization transport retains every actual context morphism"
      - "the resulting common Hom has the accepted canonical package normalization as base"
    undischarged_assumptions:
      - "exact-geometry idempotence and source-choice composition laws"
      - "generated-image submonoid equivalence and faithful inclusion"
      - "common local-model category and primitive reading functor"
    acceptance_point: "canonical normalization lift into the common tagged global fiber only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "taggedOperationGeometryPackage"
      - "taggedOperationPackage_admissible"
      - "canonicalObjectNormalizationTotal"
    discharge_required:
      - "all ExplicitExactGeometryHom computational components"
      - "common FamilyRealization Hom packaging"
      - "base equality to accepted package normalization"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "coverage / primitive requirement predicates and identity index maps"
      - "overlap / identity overlap isomorphisms"
      - "coefficient / identity ring homomorphism on the fixed coefficient ring"
      - "raw / reflexive exact typed raw map"
      - "realization / explicit identity action on every retained context morphism"
    unresolved:
      - "exact-geometry algebraic laws and generated submonoid bridge"
  proof_use:
    used:
      - "canonicalObjectNormalizationTotal"
      - "RingHom.id"
      - "RawAmbientRestrictionSystemExactMapAgainst.refl"
      - "FamilyRealization tagged Hom definition"
      - "taggedCanonicalNormalization_not_injective"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "constructs the missing common-global morphism from primitive data rather than accepting an exact-geometry lift certificate"
  vacuity: "the base object map is the nonidentity, noninjective canonical normalization; the Hom is not the categorical identity"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometry.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometry.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry: pass (4368 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometry: 4 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "prove exact-geometry idempotence and source-choice composition laws, then construct the generated-image common-global bridge"
```

## Cycle 40 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 40
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: f052ef8f4dc79fd86530f041c4b8faef0866add4
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 39 audit: PR comment 5727284540; Cycle 40 selection: Issue comment 5727292903"
  proof_dag_predecessors:
    - "Cycle 35 package-level canonical restriction law"
    - "Cycle 39 canonical normalization as a common tagged exact-geometry Hom"
    - "existing common tagged source-choice exact-geometry Homs"
  proof_obligation: "prove canonical normalization idempotence and the source-choice canonical restriction composition law as equalities of actual Homs in the common tagged FamilyRealization fiber"
  selection_reason: "the generated package normal form cannot enter the common fiber faithfully until the normalization generator and its interaction with arbitrary source choices are proved at the exact-geometry level"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryLaws.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "canonical normalization is idempotent as a common tagged actual Hom, and its left composition with every source-choice Hom depends exactly on the accepted normalizeChoice restriction"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws.taggedExplicitRealizationSupply_hext"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws.closedFamilyTaggedNormalization_idempotent"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws.closedFamilyTaggedNormalization_comp_sourceChoice"
  claim_mapping:
    source_labels:
      - "fixed GOAL A canonical normalization law in the tagged family"
      - "Cycle 35 canonical restriction law for arbitrary source choices"
      - "Cycle 39 common tagged exact-geometry normalization Hom"
    conjuncts:
      - "idempotence holds as equality in the common tagged FamilyRealization fiber"
      - "left normalization composition depends only on normalizeChoice at the same actual Hom level"
      - "realization equality compares atom map, object map, equation transport, actual context action, and all three carrier equivalences"
    undischarged_assumptions:
      - "exact-geometry normal-form image and its equivalence with the package generated submonoid"
      - "common local-model category and primitive reading functor"
      - "four-family integration and arbitrary-object assembly"
    acceptance_point: "two exact-geometry generation laws in the common tagged fiber only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "canonicalObjectNormalizationTotal_comp"
      - "canonicalObjectNormalizationEquationTransport_comp_heq"
      - "normalization_comp_sourceChoice_eq_normalized"
    discharge_required:
      - "actual common-Hom idempotence"
      - "actual common-Hom source-choice restriction composition"
      - "dependent explicit realization equality beyond package-base equality"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "base / accepted package-level idempotence and canonical restriction laws"
      - "raw and coefficient / componentwise extensional equality"
      - "realization / heterogeneous extensionality from atom, object, equation transport, context action, support, axis, and observable data"
    unresolved:
      - "generated exact-geometry image and common-global bridge"
  proof_use:
    used:
      - "ExplicitExactGeometryHom.ext"
      - "canonicalObjectNormalizationTotal_comp"
      - "canonicalObjectNormalizationEquationTransport_comp_heq"
      - "canonicalObjectNormalization_idempotent"
      - "normalization_comp_sourceChoice_eq_normalized"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "lifts accepted generator laws to the common actual Hom surface without replacing dependent realization data by a package-base certificate"
  vacuity: "the normalization Hom is nonidentity, and the source-choice theorem quantifies over every source-indexed Boolean choice"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryLaws.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryLaws.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws: pass (4371 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryLaws: 3 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct an exact-geometry normal-form image and prove its faithful equivalence with the accepted generated package submonoid"
```

## Cycle 41 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 41
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: bcace0d2862020b3210d192321a7ab39bc25e13f
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 40 audit: PR comment 5727554438; Cycle 41 selection: Issue comment 5727561594"
  proof_dag_predecessors:
    - "Cycle 35 normalization_comp_sourceChoice_eq_normalized and normalizeChoice_invariant"
    - "accepted taggedSourceChoiceTotal_commutes_normalization for invariant choices"
    - "Cycle 39 exact-geometry canonical normalization Hom and Cycle 40 tagged explicit realization heterogeneous extensionality"
  proof_obligation: "lift the canonical rewrite normalization-then-choice = restricted-choice-then-normalization to an equality of actual Homs in the common tagged FamilyRealization fiber"
  selection_reason: "the exact normal-form multiplication cannot be defined and verified until normalization can be moved to the normalized-form position without forgetting dependent exact-geometry data"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryRewrite.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "for every source choice, common tagged normalization followed by that choice equals the canonically restricted choice followed by normalization as an actual exact-geometry Hom"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite.closedFamilyTaggedNormalization_comp_sourceChoice_rewrite"
  claim_mapping:
    source_labels:
      - "Cycle 35 package-level generated-normal-form rewrite"
      - "Cycle 40 common tagged exact-geometry generation laws"
    conjuncts:
      - "the rewrite quantifies over every source-indexed Boolean choice"
      - "both sides are actual Homs in the same common tagged fiber"
      - "base, coefficient, raw, equation transport, context action, support, axis, and observable data agree"
    undischarged_assumptions:
      - "exact-geometry normal-form evaluator and image"
      - "faithful equivalence with the generated package submonoid"
      - "common local-model category and primitive reading functor"
    acceptance_point: "one exact-geometry canonical rewrite theorem only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "taggedOperationGeometryPackage"
      - "closedFamilyTaggedNormalization"
      - "closedFamilyTaggedSourceChoice"
    proved_dependencies:
      - "normalization_comp_sourceChoice_eq_normalized"
      - "taggedSourceChoiceTotal_commutes_normalization"
      - "normalizeChoice_invariant"
      - "taggedExplicitRealizationSupply_hext"
      - "equationSystemExactTransport_hext"
    discharge_required:
      - "actual common-Hom rewrite"
      - "dependent equation and realization transport equality"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "base / accepted package canonical restriction plus invariant-choice commutation"
      - "raw and coefficient / componentwise extensional equality"
      - "realization / atom, object, equation transport, context action, support, axis, and observable comparison"
    unresolved:
      - "exact normal-form image and common-global generated bridge"
  proof_use:
    used:
      - "normalization_comp_sourceChoice_eq_normalized"
      - "taggedSourceChoiceTotal_commutes_normalization"
      - "normalizeChoice_invariant"
      - "taggedExplicitRealizationSupply_hext"
      - "equationSystemExactTransport_hext"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "proves the rewrite on the common actual Hom surface without projecting to package equality as the conclusion"
  vacuity: "the theorem covers arbitrary choices, including noninvariant choices, and relates two nontrivial composition orders"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryRewrite.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeCanonicalNormalizationGeometryRewrite.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite: pass (4373 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeCanonicalNormalizationGeometryRewrite: 1 declaration, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the exact-geometry normal-form evaluator/image and prove its faithful equivalence with the accepted generated package submonoid"
```

## Cycle 42 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 42
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 07f9237f4706806de99988af1f4d6cca5e551086
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 41 audit: PR comment 5727726088; Cycle 42 selection: Issue comment 5727735603"
  proof_dag_predecessors:
    - "Cycle 36 faithful package NormalForm and actualGeneratedSubmonoid"
    - "Cycles 39--41 common tagged exact-geometry generators and generation laws"
  proof_obligation: "evaluate NormalForm faithfully in the common tagged fiber, prove its four-case multiplication, and identify its actual image submonoid with the accepted package generated submonoid"
  selection_reason: "the generated tagged branch needs an actual common-global image before its accepted finite local reading can be factored through the shared FamilyRealization surface"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryNormalForm.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the accepted two-constructor normal form now evaluates faithfully to common tagged actual Homs, forms an actual image submonoid, and is monoid-equivalent to the accepted package generated submonoid with primitive base readback"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.evaluate"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.evaluate_base"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.evaluate_multiply"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.evaluate_injective"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.evaluationHom"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.representedSubmonoid"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.normalFormMulEquivRepresented"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.representedMulEquivPackageGenerated"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm.represented_normalForm_base"
  claim_mapping:
    source_labels:
      - "Cycle 36 accepted NormalForm multiplication and package generated submonoid"
      - "Cycles 39--41 common tagged exact-geometry generator laws"
    conjuncts:
      - "raw and normalized constructors evaluate to actual common tagged Homs"
      - "all four multiplication cases agree with actual Hom composition"
      - "evaluation is injective by primitive package-base readback"
      - "the actual exact image and package generated submonoid are monoid-equivalent through the same NormalForm"
      - "the bridge retains package-base readback on every normal form"
    undischarged_assumptions:
      - "primitive finite reading factored directly from common-fiber Homs"
      - "common local-model category and arbitrary-object assembly"
      - "four-family integration"
    acceptance_point: "generated tagged common-global image and package bridge only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "FamilyRealization.taggedOperation"
      - "closedFamilyTaggedSourceChoice"
      - "closedFamilyTaggedNormalization"
    proved_dependencies:
      - "taggedSourceChoiceExplicitExactGeometryMorphism_comp"
      - "closedFamilyTaggedNormalization_idempotent"
      - "closedFamilyTaggedNormalization_comp_sourceChoice_rewrite"
      - "TagChangeGeneratedNormalForm.evaluate_injective"
      - "TagChangeGeneratedNormalForm.normalFormMulEquivGenerated"
    discharge_required:
      - "four-case exact-geometry multiplication"
      - "faithful exact evaluation and actual image"
      - "monoid equivalence to the accepted package generated image"
      - "primitive package-base agreement"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "generator composition / exact source-choice xor, normalization idempotence, and canonical rewrite"
      - "faithfulness / computed package-base readback followed by accepted package evaluation injectivity"
      - "image equivalence / two faithful evaluations of the same NormalForm; exact faithfulness is derived through package-base readback"
    unresolved:
      - "common primitive finite reading and common local-model category"
  proof_use:
    used:
      - "closedFamilyTaggedSourceChoice_comp"
      - "closedFamilyTaggedNormalization_comp_sourceChoice_rewrite"
      - "closedFamilyTaggedNormalization_idempotent"
      - "TagChangeGeneratedNormalForm.evaluate_injective"
      - "TagChangeGeneratedNormalForm.normalFormMulEquivGenerated"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "constructs an actual common-global generated image and fixes its primitive projection instead of renaming the package generated submonoid"
  vacuity: "raw and normalized constructors remain distinct by faithful package-base readback, and evaluation quantifies over the full accepted NormalForm"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryNormalForm.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryNormalForm.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm: pass (4374 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryNormalForm: 12 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "factor the accepted finite local reading through the common exact-geometry image and construct its common local-model categorical connection"
```

## Cycle 43 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 43
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: b307734dd05b5cb232cfb6f8e2a14c17e37bb053
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 42 audit: PR comment 5727949234; Cycle 43 selection: Issue comment 5727962389"
  proof_dag_predecessors:
    - "Cycle 42 common exact representedSubmonoid and package generated bridge"
    - "Cycles 37--38 accepted finite LocalSection monoid and branch-local category equivalence"
  proof_obligation: "factor primitive finite reading through the common exact image and deloop the resulting monoid equivalence"
  selection_reason: "the common-global exact image must expose its own primitive package-base flag/table readback rather than rely on an abstract type equivalence"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the common exact represented image now has direct primitive finite reading, separation and assembly on Homs, and a one-object category equivalence with LocalSection"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.representedMulEquivLocalSection"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.represented_base"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.readExactChoice"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.readExactNormalizedFlag"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.representedMulEquivLocalSection_localValue"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.reading"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.morphism_separates"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.morphism_assembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.object_assembles"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel.equivalence"
  claim_mapping:
    source_labels:
      - "Cycle 42 represented exact image and primitive package-base agreement"
      - "Cycle 37 LocalSection primitive reading and monoid equivalence"
      - "Cycle 38 one-object category pattern"
    conjuncts:
      - "each exact evaluated NormalForm maps to its accepted finite-local read form"
      - "the normalization flag is read directly from the exact morphism's primitive upper object map"
      - "every finite table is read directly from the exact morphism's primitive operation map"
      - "primitive reading separates represented exact Homs and every local Hom assembles"
      - "the represented exact one-object category is equivalent to SingleObj LocalSection"
    undischarged_assumptions:
      - "arbitrary-object assembly in the fixed common local-model category"
      - "source, target, composition, and identity family integration"
    acceptance_point: "common exact generated Hom image and its finite-local category only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "TagChangeExactGeometryNormalForm.representedSubmonoid"
      - "TagChangeGeneratedLocalModel.LocalSection"
    proved_dependencies:
      - "TagChangeExactGeometryNormalForm.representedMulEquivPackageGenerated"
      - "TagChangeExactGeometryNormalForm.represented_normalForm_base"
      - "TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection"
      - "TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection_localValue"
    discharge_required:
      - "form-preserving exact-to-local monoid equivalence"
      - "direct exact package-base flag/table readback"
      - "Hom separation and assembly"
      - "one-object category equivalence"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "exact-to-local equivalence / exact-to-package bridge followed by accepted package-to-local equivalence"
      - "primitive reading / computed exact package base, upper object map, and operation map"
      - "categorical equivalence / delooping of the proved monoid equivalence"
    unresolved:
      - "fixed common local-model arbitrary objects and four-family integration"
  proof_use:
    used:
      - "representedMulEquivPackageGenerated_on_normalForm"
      - "represented_normalForm_base"
      - "actualGeneratedMulEquivLocalSection_normalized"
      - "actualGeneratedMulEquivLocalSection_value"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "reads finite data from the primitive base of actual common exact Homs and proves the categorical equivalence on their faithful image"
  vacuity: "the exact image is faithful to the full accepted NormalForm and direct flag/table readback separates every represented morphism"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel: pass (4376 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryLocalModel: 20 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "integrate the common exact source-choice branch with the fixed source/target/composition/identity family surface without weakening arbitrary-object assembly"
```

## Cycle 44 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 44
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 6d423825fc5931d377ca0160c9dc61bcee26c73a
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 43 audit: PR comment 5728136810; Cycle 44 selection: Issue comment 5729553312"
  proof_dag_predecessors:
    - "Cycle 43 common exact represented category and primitive finite-local equivalence"
    - "accepted ClosedFamilyRealizationHom tagged fiber with its identity and composition"
  proof_obligation: "include the represented exact one-object category in the tagged fiber of the common realization family and prove that endpoints, identity, composition, and accepted normal-form evaluation are retained"
  selection_reason: "the accepted exact-local equivalence must enter the already fixed common realization family before any four-branch local-model theorem can use it"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryCommonInclusion.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the common exact represented category now has a faithful functor into the actual tagged fiber, with definitional object/Hom mapping and exact preservation of every accepted normal-form evaluation"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion.inclusion"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion.inclusion_obj"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion.inclusion_map"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion.inclusion_map_normalForm"
    - "AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion.inclusion_faithful"
  claim_mapping:
    source_labels:
      - "Cycle 43 GlobalCategory"
      - "Cycle 42 exact normal-form evaluation"
      - "AATClosedRealizationCategory tagged fiber"
    conjuncts:
      - "the sole represented object maps to FamilyRealization.taggedOperation"
      - "each represented Hom maps to its underlying actual ClosedFamilyRealizationHom"
      - "identity and composition are preserved by the functor laws"
      - "each accepted normal form maps to the existing exact evaluation"
      - "the inclusion is faithful"
    undischarged_assumptions:
      - "arbitrary-object assembly in the fixed common local-model category"
      - "local-model integration for G-122, lens, and protocol"
      - "finite reconstruction of tagged Homs outside the represented image"
    acceptance_point: "faithful inclusion of the represented exact tagged branch into the common realization family only"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "TagChangeExactGeometryLocalModel.GlobalCategory"
      - "FamilyRealization ClosedFamilyParameter.taggedOperation"
    proved_dependencies:
      - "TagChangeExactGeometryNormalForm.normalFormMulEquivRepresented"
      - "TagChangeExactGeometryNormalForm.evaluate"
      - "closedFamilyRealizationCategory"
    discharge_required:
      - "common-family object and Hom mapping"
      - "identity and composition preservation"
      - "normal-form evaluation agreement"
      - "faithfulness"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "Hom inclusion / Submonoid membership is forgotten while the actual exact Hom is retained"
      - "functor laws / definitional agreement of common composition with represented-submonoid multiplication"
      - "faithfulness / injectivity of the subtype value map"
    unresolved:
      - "fixed common local-model arbitrary objects and remaining branch integration"
  proof_use:
    used:
      - "normalFormMulEquivRepresented"
      - "ClosedFamilyRealizationHom tagged category instance"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "places the accepted exact finite-local branch inside the actual common realization family without changing its Hom type or adding an image premise to the family definition"
  vacuity: "the source contains the full accepted representedSubmonoid, the map is faithful, and every accepted NormalForm evaluation is preserved"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryCommonInclusion.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryCommonInclusion.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion: pass (4377 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.TagChangeExactGeometryCommonInclusion: 5 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct the family-indexed local-model connection for another mandatory branch or the common local family itself, while keeping arbitrary-object assembly as an explicit proof obligation"
```

## Cycle 45 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 45
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 7e529b40a65ebf78cd866ba6426ce38670d623ef
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 44 audit: PR comment 5729817995; Cycle 45 selection: Issue comment 5729864050"
  proof_dag_predecessors:
    - "accepted AATClosedFamilySignature FamilyRealization G-122 original-cell fiber"
    - "accepted G122GeneratedGeometryObject with original, direct, and viaBase objects"
    - "accepted FiniteAxisFoldComparisonCode evaluation of the three fixed comparisons"
  proof_obligation: "include the common G-122 original-cell fiber fully faithfully in the generated-endpoint category and name the fixed direct/via-base endpoints and barAlpha, generated barBeta, and constant-one barBeta as actual Homs"
  selection_reason: "the common family currently contains only original G-122 cell inputs, while fixed target A and C require the generated direct/via-base endpoints and their three comparisons; a fully faithful expansion preserves every existing object and Hom without pretending that the final four-family category is already replaced"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122ClosedFamilyExpansion.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the common G-122 original-cell fiber now enters the existing generated-endpoint category fully faithfully, and the fixed two endpoints and three comparison cases are actual Homs there with their accepted equality and inequality retained"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.originalInclusion"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.originalInclusion_obj"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.originalInclusion_map"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.originalInclusionFullyFaithful"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldDirectObject"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldViaBaseObject"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldBarAlpha"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldGeneratedBarBeta"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldIdentityBarBeta"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldGeneratedBarBeta_ne_barAlpha"
    - "AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion.finiteAxisFoldIdentityBarBeta_eq_barAlpha"
  claim_mapping:
    source_labels:
      - "fixed target A: include the fixed G-122 generated comparison family"
      - "fixed target C: retain the three fixed comparison cases as actual morphisms"
    conjuncts:
      - "every original-cell object maps to the corresponding original object"
      - "every admitted original-cell complete-geometry Hom is retained"
      - "the inclusion is fully faithful"
      - "the fixed direct and via-base endpoints are objects of the expanded category"
      - "barAlpha, generated barBeta, and constant-one barBeta are actual Homs between those endpoints"
      - "generated barBeta differs from barAlpha, while constant-one barBeta equals barAlpha"
    undischarged_assumptions:
      - "replace the final four-family realization category by an expanded common category"
      - "construct finite G-122 probes and the G-122 local-model equivalence"
      - "recover the full and base-fixing comparison groups from local data"
      - "discharge four-family separation and assembly"
    acceptance_point: "fully faithful G-122 expansion and fixed actual comparisons only; no final common category, local equivalence, or GOAL completion claim"
    port_status: unported
audits:
  material_premises:
    ambient_scope:
      - "fixed G122FamilyInput"
      - "accepted original-cell FamilyRealization fiber"
      - "accepted generated-endpoint complete-geometry category"
    proved_dependencies:
      - "G122GeneratedGeometryObject category instance"
      - "FiniteAxisFoldComparisonCode.evaluate"
      - "generatedBarBeta_ne_barAlpha"
      - "evaluate_identityBarBeta_eq_barAlpha"
    discharge_required:
      - "object and Hom inclusion"
      - "identity and composition preservation"
      - "full faithfulness"
      - "fixed endpoint and comparison typing"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "original Hom preimage / ULift of the same complete-geometry Hom"
      - "fixed comparisons / accepted evaluation in the generated-endpoint category"
    unresolved:
      - "finite local probes, local assembly, and comparison-group recovery"
  proof_use:
    used:
      - "FamilyRealization G-122 Hom definition"
      - "G122GeneratedGeometryObject original/direct/viaBase constructors"
      - "FiniteAxisFoldComparisonCode evaluation and comparison laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds the missing fixed generated endpoints while preserving the entire accepted original-cell fiber fully faithfully"
  vacuity: "the source is the complete original-cell realization category, the preimage is explicit for every target Hom between included objects, and all three fixed comparison codes are evaluated"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122ClosedFamilyExpansion.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122ClosedFamilyExpansion.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion: pass (4327 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ClosedFamilyExpansion: 11 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct finite probe readings on the expanded G-122 category that separate the fixed comparison cases and feed an explicit local-model assembly theorem"
```

Cycle 45 の fresh Math A/B・Lean A/B は final head
`afc2393e76dc8fd33baf21f8f2324db303568ddd` で全4 lane `No major findings`、
CI 7/7 success。最終監査は PR comment `5730017275`、merge commit は
`48d3c50a85722731eca7971cd54062c333dfc09d`、Cycle 46選定は Issue comment
`5730046376` に固定した。

## Cycle 46 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 46
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 48d3c50a85722731eca7971cd54062c333dfc09d
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 45 audit: PR comment 5730017275; Cycle 46 selection: Issue comment 5730046376"
  proof_dag_predecessors:
    - "Cycle 45 expanded G-122 category with fixed direct/via-base endpoints and actual comparisons"
    - "accepted FiniteAxisFoldComparisonCode exact semantic fibers"
  proof_obligation: "construct a finite local value for the actual image of the three fixed comparison codes and mutually inverse read/assemble maps that retain exactly the two semantic morphisms"
  selection_reason: "barAlpha and constant-one barBeta are the same actual Hom, while generated barBeta is distinct; a sound local reading must recover the two semantic classes without pretending that the three provenance codes are three morphisms"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FixedComparisonLocalSlice.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the actual fixed comparison image in the expanded Hom is equivalent to a finite two-valued local type, with explicit reading and assembly inverse laws and exact readback for all three provenance codes"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.SemanticImage"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.LocalValue"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.read"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.generated_ne_alpha"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.read_barAlpha"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.read_generatedBarBeta"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.read_identityBarBeta"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice.semanticEquivLocal"
  claim_mapping:
    source_labels:
      - "fixed target A: finite local values for the fixed G-122 comparison case"
      - "fixed target B/C: Hom-level read/assemble and exact recovery of the three fixed cases"
    conjuncts:
      - "the global side is the actual image of all three fixed comparison codes"
      - "the local side is an explicit finite two-constructor type"
      - "read sends barAlpha and constant-one barBeta to the same class"
      - "read sends generated barBeta to the distinct class"
      - "read after assemble and assemble after read are identities"
    undischarged_assumptions:
      - "extend the local reading to arbitrary expanded G-122 Homs"
      - "construct source-generated finite probes that separate the required Hom range"
      - "construct object-level G-122 local assembly and a category equivalence"
      - "recover the full and base-fixing comparison groups from local data"
      - "discharge final four-family separation and assembly"
    acceptance_point: "finite equivalence for the fixed semantic Hom image only; no arbitrary-Hom or category-wide local equivalence claim"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "fixed finite-axis-fold direct/via-base Hom in the expanded category"
      - "accepted three-code semantic evaluator"
    proved_dependencies:
      - "finiteAxisFoldGeneratedBarBeta_ne_barAlpha"
      - "finiteAxisFoldIdentityBarBeta_eq_barAlpha"
    discharge_required:
      - "finite local value"
      - "exact readback of each fixed code"
      - "both inverse laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "semantic image membership / witness is one of the accepted three codes"
      - "local assembly / chooses the two actual representative Homs"
      - "global recovery / exact case analysis on semantic image provenance"
    unresolved:
      - "arbitrary expanded Hom separation and object assembly"
  proof_use:
    used:
      - "generated barBeta and barAlpha inequality"
      - "constant-one barBeta and barAlpha equality"
      - "Cycle 45 actual Hom aliases"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "provides an actual finite local Hom slice with two-sided reconstruction while preserving the evaluator's noninjectivity"
  vacuity: "both local constructors assemble to distinct actual Homs, and every semantic-image member is recovered by case analysis on its accepted code witness"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122FixedComparisonLocalSlice.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FixedComparisonLocalSlice.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice: pass (4328 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice: 33 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "extend from the fixed semantic image to a nontrivial arbitrary-Hom local reading and discharge separation and assembly without storing completed morphisms in local values"
```

## Cycle 47 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 47
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 1e359cbae5eed78138782593b17da96b6a9e193a
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 46 audit: PR comment 5730207022; Cycle 47 selection: Issue comment 5730309080"
  proof_dag_predecessors:
    - "Cycle 45 expanded G-122 category with actual fixed comparisons"
    - "Cycle 46 two-valued semantic image equivalence"
    - "accepted finite total probe and canonical-normalization APIs"
  proof_obligation: "construct a nonempty primitive finite probe that separates the two fixed semantic comparison classes, derive local read/assemble inverses from its restriction, and connect it to the expanded Hom and existing local surfaces"
  selection_reason: "Cycle 46 classified by equality of complete morphisms; the next sound step is to expose the actual primitive observation that detects the generated normalization"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveComparisonProbe.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "two inverse-barAlpha object points form a nonempty primitive probe; canonical normalization collapses their generated-barBeta images, the probe separates the fixed semantic image, and primitive read/assemble are mutually inverse"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.targetProjector_eq_endpointNormalization"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.targetProjector_collapses_probeObjects"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.coreProbe"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.coreProbe_generatedBarBeta_ne_barAlpha"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.totalProbe"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.totalProbe_not_agreement_generatedBarBeta_barAlpha"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.primitiveRead"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.primitiveRead_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.assemble_primitiveRead"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.primitiveSemanticEquivLocal"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.primitiveRead_eq_read"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe.totalProbe_separates_semanticImage"
  claim_mapping:
    source_labels:
      - "fixed target A: primitive finite reading for the fixed G-122 generated comparison"
      - "fixed target B/C: separation and two-sided reconstruction on the actual fixed semantic image"
    conjuncts:
      - "the probe has exactly two selected architecture objects and no completed morphism field"
      - "the actual generated target projector is endpoint canonical normalization"
      - "generated barBeta identifies the two probe points while barAlpha retains distinct images"
      - "complete probe agreement separates all morphisms in the fixed semantic image"
      - "primitive reading and assembly are inverse in both directions"
      - "primitive reading agrees with the accepted Cycle 46 classifier"
    undischarged_assumptions:
      - "extend finite separation and assembly to arbitrary expanded G-122 Homs and objects"
      - "recover the full and base-fixing comparison groups from local data"
      - "discharge final four-family separation and assembly"
    acceptance_point: "nonempty primitive finite reconstruction for the fixed semantic image only; no arbitrary-Hom or category-wide equivalence claim"
    port_status: unported
audits:
  material_premises:
    ambient_scope:
      - "fixed finite-axis-fold direct/via-base endpoints"
      - "actual barAlpha, generated barBeta, and constant-one barBeta"
      - "accepted finite total probe surface"
    proved_dependencies:
      - "barBeta factorization through barAlpha and barD"
      - "selected barD equals endpoint canonical normalization"
      - "two distinct finite-axis-fold objects share one configuration"
    discharge_required:
      - "nonempty primitive probe construction"
      - "actual negative agreement witness"
      - "fixed-image separation"
      - "both inverse laws and Cycle 46 compatibility"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "probe points / inverse images under the accepted barAlpha isomorphism"
      - "probe distinction / canonical normalization of same-configuration objects"
      - "local recovery / finite case split after primitive evaluation"
    unresolved:
      - "arbitrary expanded Hom and object assembly"
  proof_use:
    used:
      - "endpoint normalization classification"
      - "barAlpha inverse laws"
      - "barBeta factorization"
      - "primitive objectRestriction and complete Agreement"
      - "Cycle 45 expanded Homs and Cycle 46 LocalValue/assemble"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "replaces complete-Hom equality classification by an actual finite primitive reading on the fixed G-122 image"
  vacuity: "the probe has two points, explicitly rejects agreement of generated barBeta with barAlpha, and reconstructs both distinct semantic classes"
  four_lane_question: "Does the two-point primitive object restriction, rather than completed-Hom equality, separate the fixed comparison image and support both inverse laws?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveComparisonProbe.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe: pass (4333 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe: 27 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "enlarge primitive separation and assembly from the fixed comparison image to a substantial finite generated Hom range, including the comparison-group action in the same cycle"
```

## Cycle 48 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 48
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 2bea07ef9d75a10812f2e5bde04e1500f58bef3f
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 47 audit: PR comment 5730516406; Cycle 48 selection: Issue comment 5730710917"
  proof_dag_predecessors:
    - "Cycle 47 primitive fixed-comparison reconstruction"
    - "accepted source/actual displayed C2 equivalence"
    - "accepted two-point orbit and normalized-identity source lift"
  proof_obligation: "for every normalized bottom comparison, reconstruct the actual displayed lift orbit uniquely from source C2, prove action compatibility, and combine it with primitive fixed-comparison reconstruction in the same cycle"
  selection_reason: "the next step must include an actual two-sided or universal result and its common-surface connection rather than ending at an alias or a new definition"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedLiftOrbitLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "source C2 assembles bijectively into every displayed canonical-lift orbit; an independent two-constructor code reconstructs the source C2 without storing completed morphisms; every orbit point has a unique source term; multiplication agrees with the opposite-kernel action; identity-fiber assembly agrees with sourceLiftAtOne; the result combines with Cycle 47 into a product equivalence with both inverse laws"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.DisplayedOrbit"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.assembleOrbit"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.assembleOrbit_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.assembleOrbit_surjective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.sourceOrbitEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.SourceLocalValue"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.sourceEquivLocal"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.sourceActingElement_mul"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.assembleOrbit_mul"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.existsUnique_source_of_orbit"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.assembleOrbit_atOne_eq_sourceLiftAtOne"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.combinedRead_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.combinedAssemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel.combinedSemanticEquivLocal"
  claim_mapping:
    source_labels:
      - "fixed target B/C: source-generated displayed lift reconstruction and uniqueness"
      - "fixed target A/B/C: primitive comparison reading paired with displayed source-lift reading"
    conjuncts:
      - "the construction is uniform over every normalized bottom comparison"
      - "source assembly is injective and surjective onto the actual displayed orbit"
      - "each displayed-orbit lift has a unique source C2 preimage"
      - "an independent two-constructor local code and the source C2 have read/assemble inverse laws"
      - "source multiplication is intertwined with the opposite-kernel action"
      - "identity-fiber assembly is the accepted sourceLiftAtOne construction"
      - "primitive comparison and displayed lift admit joint read/assemble inverse laws"
    undischarged_assumptions:
      - "classify the full comparison group and full restriction kernel"
      - "classify the full lift fiber beyond the displayed C2 orbit"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "uniform simply transitive reconstruction of the accepted displayed C2 orbit and its joint local product with the fixed primitive comparison only"
    port_status: unported
audits:
  material_premises:
    ambient_scope:
      - "fixed finite-axis-fold source C2 and actual bottom restriction-kernel C2"
      - "canonical and shifted lifts over arbitrary normalized bottom comparison"
      - "Cycle 47 fixed semantic image and primitive reading"
    proved_dependencies:
      - "sourceActualEquiv and multiplication preservation"
      - "orbit_canonicalLift_eq_pair and shiftedLift_ne_canonicalLift"
      - "sourceLiftAtOne identity and generator equations"
      - "primitiveSemanticEquivLocal"
    discharge_required:
      - "orbit assembly injectivity and surjectivity"
      - "unique source preimage"
      - "action compatibility"
      - "identity-fiber connection and combined inverse laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "orbit membership / actual displayed subgroup action"
      - "surjectivity / accepted equality of orbit with the canonical-shifted pair"
      - "uniqueness / proved nonidentity action and source two-case carrier"
      - "joint reconstruction / product of two independently proved inverse pairs"
      - "no completed source morphism in the local product / source C2 is first reconstructed from SourceLocalValue"
    unresolved:
      - "full group, full fiber, arbitrary-Hom, and four-family reconstruction"
  proof_use:
    used:
      - "source-to-actual C2 evaluation and multiplication law"
      - "independent source-code read/assemble inverse laws"
      - "displayed subgroup orbit classification"
      - "canonical/shifted lift distinction"
      - "normalized-identity source lift"
      - "Cycle 47 primitive comparison inverse laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds a uniform source-generated lift reconstruction with uniqueness and action law, then connects it to the primitive fixed-comparison local model in the same cycle"
  vacuity: "every displayed orbit has two distinct actual lifts, both source constructors occur, and the universal uniqueness theorem quantifies over every orbit point"
  four_lane_question: "Does the source C2 act simply transitively on every actual displayed bottom-lift orbit, and does that inverse combine with the primitive fixed-comparison reading without storing completed semantics?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedLiftOrbitLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedLiftOrbitLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel: pass (4371 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedLiftOrbitLocalModel: 54 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "move beyond the displayed C2 orbit to a larger finite source-generated comparison range while retaining primitive separation, unique reconstruction, and action compatibility in one cycle"
```

## Cycle 49 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 49
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: b07683e791c918ec43b282eb949e7b1555021366
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 48 accepted PR 4761; Cycle 49 selection: Issue comment 5731034409"
  proof_dag_predecessors:
    - "accepted primitive three-axis normalized section"
    - "accepted source-generated comparison section Hom"
    - "accepted canonical lift and full actual restriction-kernel torsor theorem"
  proof_obligation: "recover the six-element actual normalized-comparison image from primitive three-axis codes, uniquely recover the source-generated canonical section code, and connect it to the full-kernel torsor theorem on every represented lift fiber"
  selection_reason: "this combines a new finite group equivalence, a substantive uniqueness theorem, and the existing actual-fiber universal action on one common surface rather than ending at a definition or adapter"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122AxisComparisonLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "primitive three-axis permutations assemble through the actual normalized comparison section into a six-element subgroup and read back with both inverse laws; every semantic image comparison has a unique primitive code whose source-generated section evaluates to its canonical lift; from that canonical lift, the full actual restriction kernel has a unique displacement to every lift in the represented fiber"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.axisComparisonSectionHom"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.AxisComparisonImage"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.assembleAxis"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.readAxis"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.readAxis_assembleAxis"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.assembleAxis_readAxis"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.axisComparisonMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.axisComparisonImage_card"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.canonicalSection_unique_axisCode"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.everyLift_unique_kernel_displacement"
    - "AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel.sourceGenerated_fullKernel_reconstruction"
  claim_mapping:
    source_labels:
      - "fixed target B/C: primitive source-axis recovery of an actual normalized comparison image"
      - "fixed target C: unique source-generated canonical section and full-kernel torsor on represented fibers"
    conjuncts:
      - "the local code is Equiv.Perm (Fin 3), not a stored completed semantic comparison"
      - "assemble/read are inverse and multiplicative on the six-element actual image subgroup"
      - "the actual image subgroup has cardinality six"
      - "each image comparison has exactly one primitive code producing its canonical source-generated lift"
      - "each lift over an image comparison has exactly one full actual kernel displacement from that canonical lift"
      - "the finite comparison inverse and full-fiber torsor are exposed by one connection theorem"
    undischarged_assumptions:
      - "recover normalized comparisons outside the six-element source-generated image"
      - "recover arbitrary full-kernel elements from independent local data"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "six-element source-generated comparison image plus the accepted full-kernel torsor on each represented fiber; not the full comparison group or an independent kernel local model"
    port_status: unported
audits:
  material_premises:
    ambient_scope:
      - "primitive permutations of Fin 3"
      - "actual source-generated normalized comparison section and its image subgroup"
      - "canonical lifts and actual restriction-kernel action above image comparisons"
    proved_dependencies:
      - "normalized axis section and source-generated comparison section Hom laws"
      - "actual source endpoint axis projection readback"
      - "canonical section evaluation theorem"
      - "full-kernel simply transitive action on each actual lift fiber"
    discharge_required:
      - "both inverse laws for primitive axis assembly/readback"
      - "multiplicative equivalence and cardinality six"
      - "unique primitive canonical-section code"
      - "unique full-kernel displacement for every represented lift"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "comparison code / independent finite permutation table"
      - "semantic comparison / actual normalized section evaluation"
      - "code uniqueness / actual source-axis projection readback"
      - "fiber displacement / accepted actual restriction-kernel torsor"
    unresolved:
      - "comparison image complement and independent full-kernel local recovery"
  proof_use:
    used:
      - "axis section multiplication and readback"
      - "source-generated comparison section evaluation"
      - "canonical lift section equation"
      - "full actual kernel action existence and uniqueness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "enlarges the two-element displayed orbit to all six primitive axis comparisons, proves a group-level two-sided reconstruction, and connects unique source section codes to every represented full-kernel fiber in the same cycle"
  vacuity: "the image has exactly six elements, every primitive code is recovered by readback, and the fiber theorem quantifies over every lift above every image comparison"
  four_lane_question: "Does primitive three-axis projection reconstruct exactly the six-element actual normalized-comparison image, uniquely recover the source-generated canonical section code, and support the full-kernel torsor theorem on every represented lift fiber without storing completed comparisons?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122AxisComparisonLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122AxisComparisonLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel: pass (4377 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122AxisComparisonLocalModel: 15 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover the full comparison group and full kernel from local data beyond the six-element axis image, then extend the same separation and reconstruction to arbitrary expanded Homs and the four-family surface"
```

## Cycle 50 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 50
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 90adf1b8f30a65a0b41555d6e64280f7013e27fd
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 49 audit: PR comment 5731209616; acceptance: Issue comment 5731216913; Cycle 50 selection: Issue comment 5731249887"
  proof_dag_predecessors:
    - "Cycle 49 six-element axis comparison reconstruction"
    - "accepted independent finite Extension table and intrinsic decoder equivalence"
    - "accepted stored backward-context faithfulness on the local-fiber kernel"
    - "accepted canonical lift and full actual restriction-kernel torsor theorem"
  proof_obligation: "reconstruct a 36-element actual normalized-comparison image from an independent axis table and an independent Fin 3 Extension table, prove both inverse laws and unique canonical-section code, and connect every represented lift fiber to the full-kernel torsor"
  selection_reason: "this enlarges the represented comparison family by an independent source component and bundles its two-projection separation, two-sided reconstruction, finite cardinality, section uniqueness, and fiber action in one cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122MixedAxisExtensionLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "an independent axis permutation and explicit Extension forward/backward table evaluate to actual normalized comparisons; the actual axis projection recovers the first table and the stored backward-context action after axis removal recovers the second uniquely; these readings and assembly are inverse, separate the image, and prove cardinality 36; every represented canonical section has one unique mixed code and every lift in its fiber has one unique full-kernel displacement"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.MixedCode"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedAut_axisProjection"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedAut_stripped"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedAut_backwardObservation"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.extensionBackwardAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.extensionTarget_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.readMixed_assembleMixed"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.assembleMixed_readMixed"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedComparisonEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedComparisonImage_card"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.readMixed_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.canonicalSection_unique_mixedCode"
    - "AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel.mixedCode_fullKernel_reconstruction"
  claim_mapping:
    conjuncts:
      - "the local code contains two independent finite tables and no actual automorphism, comparison, lift, range witness, or kernel element"
      - "axis projection and stripped stored-backward action independently recover the two code components"
      - "read/assemble are inverse in both directions and the reading separates every represented comparison"
      - "the actual represented image has exactly 36 elements"
      - "each represented canonical section has exactly one mixed finite code"
      - "each represented lift has exactly one displacement from that canonical lift by the full actual kernel"
    undischarged_assumptions:
      - "recover comparisons outside the 36-element mixed image"
      - "recover arbitrary full-kernel elements from independent local data"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "36-element mixed axis-and-Extension image plus the accepted full-kernel torsor on each represented fiber"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "normalized axis section/projection and axis-kernel remainder"
      - "independent Extension table decoder and stored backward-context characterization"
      - "backward-context faithfulness on the actual local-fiber kernel"
      - "canonical section right inverse and full-kernel simply transitive action"
    discharge_required:
      - "cross-component axis invisibility and exact axis removal"
      - "Extension observation existence and uniqueness"
      - "both inverse laws, separation, and cardinality 36"
      - "unique mixed canonical-section code and full-fiber connection"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local code / independent finite axis and Extension tables"
      - "Extension readback / actual stored backward-context observation after semantic axis removal"
      - "image separation / two actual projections"
      - "fiber displacement / accepted actual restriction-kernel torsor"
    unresolved:
      - "comparison image complement and independent full-kernel local recovery"
  proof_use:
    used:
      - "axis section readback and kernel remainder"
      - "Extension intrinsic decoder injectivity and backward projection"
      - "canonical section right inverse"
      - "full actual kernel action existence and uniqueness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "moves from one six-element factor to a 36-element mixed family and includes the two-projection inverse, separation, cardinality, section uniqueness, and fiber connection in the same cycle"
  vacuity: "both code factors have cardinality six, their product image has cardinality 36, and the inverse and fiber theorems quantify over every represented comparison and lift"
  four_lane_question: "Does the independent axis-and-Extension table pair reconstruct exactly a 36-element actual normalized-comparison image with both inverse laws, uniquely determine each source-generated canonical section, and connect every represented lift to the full-kernel torsor without storing completed semantics?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122MixedAxisExtensionLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122MixedAxisExtensionLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel: pass (4405 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122MixedAxisExtensionLocalModel: 37 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover a further independent residual component or the full comparison group and full kernel from local data, then extend the same reconstruction to arbitrary expanded Homs and the four-family surface"
```

## Cycle 51 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 51
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 7036cf07bbbf31add86972f36d46cf3ec093620f
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 50 audit: PR comment 5731518187; acceptance: Issue comment 5731528601; Cycle 51 selection: Issue comment 5731565896"
  proof_dag_predecessors:
    - "Cycle 50 axis-and-Fin-3-Extension comparison reconstruction"
    - "accepted Nat exact-support/parity normal form and actual intrinsic-image equivalence"
    - "accepted arbitrary-carrier source probe faithfulness"
    - "accepted canonical lift and full actual restriction-kernel torsor theorem"
  proof_obligation: "reconstruct a carrier-separated actual normalized-comparison image from independent axis, Fin 3 Extension, and Nat exact-support/parity data; prove both inverse laws, strict enlargement of Cycle 50, unique canonical-section code, and the represented-fiber full-kernel torsor"
  selection_reason: "this adds a genuinely independent carrier direction, proves cross-carrier noninterference and a strict image inclusion, and bundles reconstruction, separation, section uniqueness, and fiber action in one auditable cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122CarrierSeparatedComparisonLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "carrier-specific source probes prove that the Fin 3 and Nat actions do not interfere; axis projection and stripped backward observation recover all three independent components; assemble/read are inverse; the Cycle 50 image embeds through the identity Nat code and a source-owned Nat swap lies outside it; every represented canonical section has a unique carrier-separated code and every lift in its fiber has a unique full-kernel displacement"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.sourcePairAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.carrierBackwardAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.localAut_axisProjection"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.localAut_backwardObservation"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.localAut_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.localComparisonEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.mixedImageEmbedding"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.mixedImageEmbedding_not_surjective"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.canonicalSection_unique_localCode"
    - "AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel.carrierSeparated_fullKernel_reconstruction"
  claim_mapping:
    conjuncts:
      - "the local code contains independent axis, finite-carrier, and Nat exact-support/parity data, with no actual automorphism, comparison, lift, range witness, or kernel element"
      - "canonical Fin 3 and Nat probes prove cross-carrier noninterference and jointly separate the two Extension components"
      - "axis projection plus stripped stored-backward observation recover all three components, and read/assemble are inverse in both directions"
      - "the Cycle 50 image embeds through the identity Nat code"
      - "the explicit source-owned Nat zero-one swap proves that this embedding is not surjective"
      - "each represented canonical section has exactly one carrier-separated code"
      - "each represented lift has exactly one displacement from that canonical lift by the full actual kernel"
    undischarged_assumptions:
      - "recover comparisons outside the carrier-separated image"
      - "recover arbitrary full-kernel elements from independent local data"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "strict carrier-separated enlargement of the Cycle 50 image, with two-sided reconstruction, canonical-section uniqueness, and the accepted full-kernel torsor on each represented fiber"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "normalized axis section/projection and axis-removal equation"
      - "independent Fin 3 Extension table decoder and backward action"
      - "independent Nat exact-support/parity normal form and actual evaluation"
      - "fixed source-to-actual context equivalence and backward-action faithfulness"
      - "canonical section right inverse and full-kernel simply transitive action"
    discharge_required:
      - "Fin 3 actions fix Nat probes and Nat actions fix Fin 3 probes"
      - "joint carrier action injectivity and actual observation separation"
      - "both inverse laws and strict non-surjectivity of the Cycle 50 embedding"
      - "unique local canonical-section code and full-fiber connection"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local code / independent axis, Fin 3 finite table, and Nat exact-support/parity data"
      - "carrier separation / primitive source probes transported through the fixed context equivalence"
      - "semantic readback / actual axis projection and stripped stored-backward observation"
      - "strict enlargement / explicit source-owned Nat zero-one swap"
      - "fiber displacement / accepted actual restriction-kernel torsor"
    unresolved:
      - "comparison image complement and independent full-kernel local recovery"
  proof_use:
    used:
      - "axis section readback and removal"
      - "Fin 3 and Nat source-action faithfulness"
      - "Nat normal-form evaluation injectivity and surjectivity"
      - "canonical section right inverse"
      - "full actual kernel action existence and uniqueness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "strictly enlarges the finite mixed image by an independent carrier-relative family and includes cross-carrier separation, both inverse laws, strict inclusion, section uniqueness, and fiber connection in the same cycle"
  vacuity: "the Cycle 50 image embeds, while a concrete Nat zero-one swap is proved outside it; both carrier components are recovered from actual observations rather than stored semantic values"
  four_lane_question: "Does an independent three-axis table, Fin 3 Extension table, and faithful Nat exact-support/parity normal form reconstruct a carrier-separated actual normalized-comparison image with both inverse laws, strictly extend Cycle 50 by a source-owned Nat direction, uniquely determine canonical-section codes, and connect every represented lift to the full-kernel torsor without storing completed semantics?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122CarrierSeparatedComparisonLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122CarrierSeparatedComparisonLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel: pass (4417 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122CarrierSeparatedComparisonLocalModel: 59 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover a further independent carrier-relative component or the full comparison group and full kernel from local data, then extend reconstruction to arbitrary expanded Homs and the four-family surface"
```

## Cycle 52 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 52
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: bcc839d940da9331ccaf1efc72858ed8bcbe10d0
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 51 audit: PR comment 5731934405; acceptance: Issue comment 5731939293; Cycle 52 selection: Issue comment 5731956646"
  proof_dag_predecessors:
    - "Cycle 51 carrier-separated three-component comparison reconstruction"
    - "accepted independent finite-carrier Extension table decoder"
    - "accepted arbitrary-carrier source probe faithfulness"
    - "accepted canonical lift and full actual restriction-kernel torsor theorem"
  proof_obligation: "add an independent Fin 4 table to the axis, Fin 3, and Nat data; prove three-carrier noninterference, two-sided actual reconstruction, strict enlargement of Cycle 51, unique canonical-section code, and the represented-fiber full-kernel torsor"
  selection_reason: "this cycle adds a fourth independent source component and bundles its actual separation, inverse laws, strictness witness, section uniqueness, and fiber action rather than deferring common-surface connection"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FourComponentComparisonLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "carrier-specific probes separate Fin 3, Nat, and Fin 4 actions; axis projection and stripped backward observation recover all four source components; assemble/read are inverse; the Cycle 51 image embeds through the identity Fin 4 table and a source-owned Fin 4 transposition lies outside it; every represented canonical section has one code and every lift in its fiber has one full-kernel displacement"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.sourceTripleAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.carrierBackwardAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.localAut_axisProjection"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.localAut_backwardObservation"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.localAut_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.localComparisonEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.carrierSeparatedImageEmbedding"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.carrierSeparatedImageEmbedding_not_surjective"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.canonicalSection_unique_localCode"
    - "AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel.fourComponent_fullKernel_reconstruction"
  claim_mapping:
    conjuncts:
      - "the local code contains independent axis, Fin 3, Nat exact-support/parity, and Fin 4 source data, with no actual automorphism, comparison, lift, range witness, or kernel element"
      - "canonical probes prove pairwise noninterference and jointly separate all three carrier actions"
      - "axis projection plus stripped stored-backward observation recover all four components, and read/assemble are inverse in both directions"
      - "the Cycle 51 image embeds through the identity Fin 4 table"
      - "the explicit source-owned Fin 4 transposition proves that this embedding is not surjective"
      - "each represented canonical section has exactly one four-component code"
      - "each represented lift has exactly one displacement from its canonical lift by the full actual kernel"
    undischarged_assumptions:
      - "recover comparisons outside the four-component image"
      - "recover arbitrary full-kernel elements from independent local data"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "strict Fin 4 enlargement of the Cycle 51 image, with actual three-carrier separation, two-sided reconstruction, canonical-section uniqueness, and the accepted full-kernel torsor on each represented fiber"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "Cycle 51 axis, Fin 3, and Nat reconstruction"
      - "independent finite-carrier Extension table decoder and backward action"
      - "fixed source-to-actual context equivalence and backward-action faithfulness"
      - "canonical section right inverse and full-kernel simply transitive action"
    discharge_required:
      - "Fin 4 actions fix Fin 3 and Nat probes, while accepted actions fix Fin 4 probes"
      - "joint three-carrier action injectivity and actual observation separation"
      - "both inverse laws and strict non-surjectivity of the Cycle 51 embedding"
      - "unique local canonical-section code and full-fiber connection"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "local code / independent axis, Fin 3, Nat, and Fin 4 source data"
      - "carrier separation / primitive source probes transported through the fixed context equivalence"
      - "semantic readback / actual axis projection and stripped stored-backward observation"
      - "strict enlargement / explicit source-owned Fin 4 transposition"
      - "fiber displacement / accepted actual restriction-kernel torsor"
    unresolved:
      - "comparison image complement and independent full-kernel local recovery"
  proof_use:
    used:
      - "Cycle 51 axis and carrier readback"
      - "finite-carrier decoder multiplication and stored backward action"
      - "canonical section right inverse"
      - "full actual kernel action existence and uniqueness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds an independent fourth component and includes three-carrier separation, both inverse laws, strict inclusion, section uniqueness, and fiber connection in the same cycle"
  vacuity: "a concrete Fin 4 transposition is proved outside the embedded Cycle 51 image, and every component is recovered from actual observations rather than stored semantic values"
  four_lane_question: "Does independent axis, Fin 3, Nat exact-support/parity, and Fin 4 data reconstruct a strictly larger actual normalized-comparison image with carrier-probe separation, both inverse laws, unique canonical-section codes, and full-kernel torsor connection without storing completed semantics?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122FourComponentComparisonLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FourComponentComparisonLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel: pass (4418 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FourComponentComparisonLocalModel: 55 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover the full comparison group and full kernel from independent local data, then extend the reconstruction to arbitrary expanded Homs and the four-family surface"
```

## Cycle 53 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 53
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: ca07c309f75a92b8a2d914f237495722cd3e285d
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 52 audit: PR comment 5732256287; acceptance: Issue comment 5732261119; Cycle 53 selection: Issue comment 5732276406"
  proof_dag_predecessors:
    - "Cycle 52 four-component comparison reconstruction"
    - "source-constructed nonidentity comparison restriction-kernel element"
    - "source-proved involution law for the displayed kernel element"
    - "accepted full actual restriction-kernel torsor on every comparison lift fiber"
  proof_obligation: "reconstruct the canonical/shifted actual lift orbit from an independent Bool kernel code on every four-component comparison; prove separation, both inverse laws, xor compatibility, simultaneous comparison/kernel-code uniqueness, and connection to the full-kernel torsor"
  selection_reason: "this moves from comparison-only reconstruction to a nontrivial independently coded kernel fragment and bundles its actual orbit reconstruction, composition law, dependent comparison connection, and ambient torsor connection in one auditable cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelLiftLocalModel.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the independent Bool code evaluates to identity or the source-constructed full-kernel involution; actual action on each canonical lift separates the codes; every displayed orbit point has a unique code with read/assemble inverse laws; xor matches actual kernel multiplication and iterated lift action; comparison code, displayed kernel code, and the ambient full-kernel displacement are uniquely related on the same fiber"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.restrictionKernelElement_mul_self"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.kernelValue_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.kernelValue_xor"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.displayedLift_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.displayedLift_true_ne_false"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.displayedLift_xor"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.readDisplayed_assembleDisplayed"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.assembleDisplayed_readDisplayed"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.displayedLiftEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.comparisonAndDisplayedLift_unique_codes"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel.displayedOrbit_and_fullKernel_reconstruction"
  claim_mapping:
    conjuncts:
      - "the kernel syntax is one independent bit and stores no actual kernel value, lift, range witness, or orbit certificate"
      - "false and true evaluate to identity and the source-constructed nonidentity involution in the full comparison restriction kernel"
      - "free actual kernel action separates the two codes on every represented canonical lift"
      - "read and assemble are inverse on the actual displayed two-point orbit"
      - "Boolean xor agrees with actual kernel multiplication and iterated action"
      - "four-component comparison code and displayed kernel code are simultaneously unique on the same fiber"
      - "the displayed orbit sits inside the accepted full-kernel torsor, whose arbitrary displacement remains unique"
    undischarged_assumptions:
      - "recover every full-kernel element from independent local data"
      - "recover comparisons outside the four-component image"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "independent local recovery of a nontrivial actual C2 kernel orbit, with composition, comparison-code coupling, and full-torsor connection"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "four-component comparison read/assemble equivalence"
      - "source-constructed actual restriction-kernel element and nonidentity proof"
      - "source congruence giving its involution law"
      - "free and transitive full-kernel action on every actual lift fiber"
    discharge_required:
      - "kernel-code evaluation injectivity"
      - "actual displayed-lift separation and both inverse laws"
      - "xor/multiplication/action compatibility"
      - "simultaneous comparison and displayed-kernel code uniqueness"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "kernel syntax / independent Bool"
      - "nontrivial evaluation / source-generated restriction-kernel involution"
      - "orbit readback / actual free action"
      - "composition / source-proved square law transported to actual kernel multiplication"
      - "fiber connection / accepted full actual kernel torsor"
    unresolved:
      - "independent local presentation of kernel elements outside the displayed C2"
  proof_use:
    used:
      - "four-component comparison equivalence"
      - "displayed element nonidentity and involution law"
      - "full-kernel action freeness and transitivity"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds an independently coded nontrivial kernel direction and includes separation, two inverse laws, composition, dependent comparison uniqueness, and full-torsor connection in the same cycle"
  vacuity: "true and false act as provably distinct actual lifts in every represented fiber, and arbitrary displayed orbit points are reconstructed rather than stored"
  four_lane_question: "Does an independent Bool kernel code reconstruct the actual canonical/shifted lift orbit over every four-component comparison with separation, both inverse laws, xor-compatible action, simultaneous comparison-code uniqueness, and an honest connection to the full-kernel torsor without storing completed semantics?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelLiftLocalModel.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelLiftLocalModel.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel: pass (4419 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelLiftLocalModel: 26 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "enlarge independent kernel recovery beyond the displayed C2 or recover the full comparison group, then extend the reconstruction to arbitrary expanded Homs and the four-family surface"
```

## Cycle 54 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 54
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 664543be2520e146de13be12b7080ef7ba677018
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 53 audit: PR comment 5732431720; acceptance: Issue comment 5732439519; Cycle 54 selection: Issue comment 5732451077"
  proof_dag_predecessors:
    - "Cycle 53 independent Bool kernel evaluation and displayed orbit reconstruction"
    - "source-constructed nonidentity involution in the full actual restriction kernel"
    - "Cycle 52 four-component comparison read/assemble equivalence"
  proof_obligation: "promote a source-owned two-element group code to a multiplicative equivalence with its actual generated restriction-kernel subgroup; prove orbit separation and unique subgroup displacement between arbitrary displayed points; couple this torsor law to unique four-component comparison reconstruction"
  selection_reason: "this cycle does not stop at a group definition or republish Cycle 53; it includes all-elements subgroup readback and both inverse laws, the actual multiplicative equivalence, free and transitive displayed action, and the common comparison surface"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelGroupTorsor.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the independent two-element syntax carries a proved group law; evaluation is injective and multiplicative; every element of the actual generated subgroup has one source code with both read/assemble inverse laws; the resulting multiplicative equivalence acts on each represented displayed orbit with a unique actual subgroup displacement between any two points; comparison-code uniqueness and this torsor law hold on one theorem surface"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.GroupCode.instGroup"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.evaluate_mul"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.evaluate_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.code_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.sourceActualMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.orbitLift_range_eq_displayedLiftImage"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.orbitLift_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.displayedOrbit_existsUnique_subgroup_displacement"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor.comparisonCode_and_displayedSubgroup_torsor"
  claim_mapping:
    conjuncts:
      - "the source syntax stores neither actual kernel values nor subgroup membership witnesses"
      - "evaluation identifies the source group multiplicatively and injectively with its actual generated subgroup"
      - "all subgroup elements, not only named generators, have unique source readback with both inverse laws"
      - "the group-code orbit equals the Cycle 53 displayed image and separates its two points"
      - "any two displayed points have exactly one actual generated-subgroup displacement"
      - "four-component comparison reconstruction and displayed subgroup torsor reconstruction are coupled on the same represented fiber"
    undischarged_assumptions:
      - "recover every full-kernel element outside the displayed generated subgroup from independent local data"
      - "recover comparisons outside the four-component image"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "multiplicative equivalence with the actual generated kernel subgroup and its free transitive action on every represented displayed fiber, coupled to unique comparison reconstruction"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "Cycle 53 actual nonidentity involution and displayed orbit separation"
      - "Cycle 52 four-component comparison equivalence"
      - "source-proved square law for the actual kernel element"
    discharge_required:
      - "source group laws and multiplicative evaluation"
      - "all-elements subgroup readback and both inverse laws"
      - "orbit equality, separation, and unique actual subgroup displacement"
      - "simultaneous comparison reconstruction and subgroup torsor law"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "group presentation / explicit source multiplication table"
      - "actual subgroup / range of multiplicative evaluation"
      - "subgroup readback / existence witness plus evaluation injectivity"
      - "torsor uniqueness / orbit separation and group cancellation"
      - "comparison coupling / accepted four-component readback"
    unresolved:
      - "independent local presentation of full-kernel elements outside this generated subgroup"
  proof_use:
    used:
      - "Cycle 53 actual kernel element, square law, and displayed lift separation"
      - "Cycle 52 comparison-code uniqueness"
      - "actual kernel multiplication and action laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "strengthens the displayed kernel fragment to a genuine group/subgroup equivalence and proves a substantive free-transitive uniqueness result while including its common comparison connection in the same cycle"
  vacuity: "the shifted source code evaluates to a proved nonidentity actual kernel element; all generated-subgroup elements are read back; arbitrary pairs of displayed points, rather than only the canonical generator pair, receive a unique displacement"
  four_lane_question: "Does the source-owned two-element group identify multiplicatively with its actual generated restriction-kernel subgroup and act with one unique displacement between arbitrary displayed fiber points while remaining coupled to unique four-component comparison reconstruction?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelGroupTorsor.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedKernelGroupTorsor.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor: pass (4420 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedKernelGroupTorsor: 38 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover a strictly larger independently presented part of the actual full kernel or the full comparison group, including its substantive reconstruction law and common-surface connection in the same cycle"
```

## Cycle 55 selection and proposal

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 55
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 844cb74f6654c22f3110e369fcd9819a9f694c6d
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 54 audit: PR comment 5732654875; acceptance: Issue comment 5732663590; Cycle 55 selection: Issue comment 5732719669"
  proof_dag_predecessors:
    - "Cycle 52 four-component comparison read/assemble equivalence"
    - "Cycle 53 displayed actual lift orbit reconstruction"
    - "Cycle 54 source-group/actual-subgroup multiplicative equivalence and unique displacement"
  proof_obligation: "reconstruct the dependent total space of represented comparisons and displayed lifts from the product of comparison and source-kernel codes; close each displayed fiber under the actual generated subgroup; prove agreement with ambient actual action, freeness, transitivity, and equivariance with source left multiplication"
  selection_reason: "this is a dependent bundle theorem rather than an alias or a pointwise conjunction: it adds an actual MulAction, a principal-action theorem, an equivariant fiber equivalence, and two-sided total-space reconstruction together with the common comparison connection"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedFiberBundleReconstruction.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "every displayed fiber is equivalent to the source group code; the actual generated subgroup acts within that fiber and its transported action equals ambient restriction-kernel action on underlying lifts; every pair of displayed points has one acting subgroup value; source left multiplication is equivariant with orbit assembly; comparison and kernel codes reconstruct the whole dependent displayed total space with both inverse laws"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.orbitPointEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.displayedFiberMulAction"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.fiberAction_val"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.displayedFiber_existsUnique_smul_eq"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.orbitPointEquiv_equivariant"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.totalRead_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.totalAssemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.totalReconstructionEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.totalCode_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction.totalReconstruction_and_principalFiber"
  claim_mapping:
    conjuncts:
      - "comparison and kernel syntax remain independent source data and contain no actual lift or range witness"
      - "the displayed image is closed under a genuine actual generated-subgroup MulAction"
      - "the transported action agrees with ambient actual restriction-kernel action on underlying lifts"
      - "the action is free and transitive through one unique subgroup displacement for arbitrary displayed points"
      - "orbit assembly intertwines actual subgroup action and source left multiplication"
      - "the product of four-component comparison code and source group code is equivalent to the dependent total displayed space with both inverse laws"
    undischarged_assumptions:
      - "recover the full restriction kernel outside the displayed generated subgroup"
      - "recover comparisons outside the four-component image"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "principal generated-subgroup action on every represented displayed fiber and dependent two-sided reconstruction of the entire displayed comparison/lift bundle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "four-component comparison read/assemble both inverse laws"
      - "source-group/actual-subgroup multiplicative equivalence"
      - "actual orbit equality, separation, and unique displacement"
    discharge_required:
      - "closure and group action laws on the displayed subtype"
      - "agreement with ambient actual action"
      - "equivariance and principal-action uniqueness"
      - "dependent total-space read/assemble both inverse laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "fiber membership / previously proved orbit-range equality"
      - "group action / multiplicative subgroup readback"
      - "actual action equality / evaluation multiplication and orbit evaluation"
      - "dependent total reconstruction / independent comparison and orbit inverse laws"
    unresolved:
      - "independent local presentation of the full actual kernel and full comparison group"
  proof_use:
    used:
      - "Cycle 52 comparison equivalence"
      - "Cycle 54 subgroup multiplicative equivalence and unique displacement"
      - "Cycle 53 actual displayed-lift image"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds a substantive dependent reconstruction and principal action, then includes the common comparison connection in the same cycle"
  vacuity: "the total space quantifies over every represented comparison and every displayed lift in its dependent fiber; the subgroup action is proved equal to actual lift action and the shifted point remains distinct"
  four_lane_question: "Does the product of four-component comparison code and source kernel group code reconstruct the dependent actual displayed-lift total space with both inverse laws while the actual generated subgroup acts principally and equivariantly on every fiber?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedFiberBundleReconstruction.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122DisplayedFiberBundleReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction: pass (4421 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122DisplayedFiberBundleReconstruction: 26 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "move beyond the displayed two-point bundle by independently recovering a strictly larger actual kernel or comparison family, or connect a new arbitrary-Hom reconstruction with its substantive separation and assembly laws in the same cycle"
```

## Cycle 56 selection and proposal

```yaml
goal_id: G-124
cycle: 56
branch: codex/4711-g124-parametric-carrier-bundle
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 6fb9d587646a273d435e961aa0bc54e74f273c94
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 55 audit: PR comment 5732849494; acceptance: Issue comment 5732862874; Cycle 56 selection: Issue comment 5732884609"
  proof_dag_predecessors:
    - "Cycle 52 four-component comparison reconstruction"
    - "Cycle 54 source-group/actual-subgroup multiplicative equivalence"
    - "Cycle 55 dependent displayed-bundle reconstruction and principal action"
  proof_obligation: "adjoin an arbitrary finite Extension carrier distinct from Fin 3, Fin 4, and Nat; recover all accepted and fresh table components from actual observations; prove comparison read/assemble both ways, proper enlargement for every nontrivial such carrier, canonical-section uniqueness, displayed-orbit separation, principal equivariant subgroup action, and dependent total reconstruction in the same cycle"
  selection_reason: "this replaces isolated next-carrier repetition with a carrier-parametric theorem and includes the common displayed-bundle connection; the principal observation argument is fixed-route conjugation injectivity plus disjoint-carrier probes"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122ParametricCarrierDisplayedBundle.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "for every finite E distinct from the three accepted carriers, independent old-plus-E tables are separated by primitive source probes and their actual stored-backward observations and reconstruct the represented actual comparison image with both inverse laws; every nontrivial E supplies an explicit swap proving that the old actual comparison range is a proper subset of the new range, with Fin 5 as a concrete instance; canonical sections and the full dependent displayed bundle have unique source codes; the actual generated subgroup action equals ambient action, has one displacement between every displayed pair, and is equivariant with source left multiplication"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.sourceFreshAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.transportSourceActionHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.carrierBackwardAction_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.localAut_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.localComparisonEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.localComparison_embedFourCodeFor"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.embedFourImageFor_val"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.embedFourImageFor_not_surjective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.fourComponentRange_ssubset_parametricRange"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.embedFourImage_not_surjective"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.canonicalSection_unique_localCode"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.orbitEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.fiberAction_val"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.displayedFiber_existsUnique_smul_eq"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.orbitPoint_equivariant"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.totalReconstructionEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle.reconstruction_principal_and_equivariant"
  claim_mapping:
    conjuncts:
      - "the fresh finite carrier is a theorem parameter with explicit disjointness from Fin 3, Fin 4, and Nat, not a renamed Fin 5-only alias"
      - "carrier-specific primitive probes separate all four carrier permutations"
      - "whole-source action conjugation through the fixed context equivalence is injective, so actual stored-backward observations separate all independent tables"
      - "comparison read and assemble satisfy both inverse laws for every admissible fresh carrier"
      - "every nontrivial fresh-carrier instance strictly contains the accepted four-component actual image; Fin 5 is a concrete instance"
      - "every represented canonical section has one local code"
      - "source kernel codes are separated by actual lift action and reconstruct every displayed fiber in both directions"
      - "the transported subgroup action agrees with ambient actual action, is principal, and is equivariant"
      - "comparison and kernel codes reconstruct the dependent total displayed space with both inverse laws"
    undischarged_assumptions:
      - "recover comparisons outside the union of the carrier-parametric represented images"
      - "recover the full restriction kernel outside the displayed generated subgroup"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "carrier-parametric comparison separation and two-sided reconstruction, generic proper inclusion of actual comparison ranges, and principal equivariant dependent displayed-bundle reconstruction in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "accepted four-component actual comparison reconstruction"
      - "fixed source-to-actual context equivalence and stored-backward decoder law"
      - "source-group/actual-subgroup multiplicative equivalence"
      - "free action of the full restriction kernel on actual lift fibers"
    discharge_required:
      - "fresh-carrier probe noninterference and joint source-action injectivity"
      - "injectivity after actual fixed-route conjugation"
      - "comparison and dependent total-space inverse laws"
      - "proper inclusion of the old actual comparison range into every nontrivial fresh-carrier range"
      - "ambient-action equality, unique displacement, and equivariance"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "carrier separation / primitive Extension probe evaluation"
      - "actual observation separation / injective conjugation along a proved equivalence"
      - "comparison reconstruction / unique code derived after observation injectivity"
      - "displayed reconstruction / actual action freeness and source evaluation injectivity"
    unresolved:
      - "independent local presentation of the full actual comparison group and full kernel"
  proof_use:
    used:
      - "Cycle 52 four-component comparison code and actual observations"
      - "Cycle 54 multiplicative source/actual subgroup equivalence"
      - "Cycle 55 principal-action construction pattern"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "adds a parametric comparison theorem, strict actual enlargement, substantive separation, both inverse laws, principal action, and common dependent connection together"
  vacuity: "every nontrivial fresh carrier supplies an explicit swap outside the old actual comparison range; arbitrary displayed pairs have a unique acting actual subgroup value; the source syntax stores no actual comparison, lift, image witness, or conclusion-equivalent semantic certificate"
  four_lane_question: "Does adjoining an arbitrary nontrivial fresh finite Extension carrier to the accepted four-component code produce a strictly larger actual comparison family with observation-based separation, two-sided comparison and dependent displayed-bundle reconstruction, and a principal equivariant generated-kernel action on every represented fiber?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122ParametricCarrierDisplayedBundle.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122ParametricCarrierDisplayedBundle.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle: pass (4422 jobs)"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ParametricCarrierDisplayedBundle: 92 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "recover comparison values beyond the carrier-parametric represented family or deliver a new arbitrary-Hom reconstruction with substantive separation, assembly, and common-surface connection in the same cycle"
```

## Cycle 57: arbitrary-carrier kernel reconstruction

```yaml
cycle: 57
status: implementation-complete-review-pending
branch: codex/4711-g124-arbitrary-carrier-kernel-reconstruction
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 6e0058d6e9ab25e7b4a8d6a1d7ef199754a012d5
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 56 audit: PR comment 5733511615; acceptance: Issue comment 5733526143; Cycle 57 selection: Issue comment 5733557769"
  proof_dag_predecessors:
    - "Cycle 56 carrier-parametric comparison and dependent displayed-bundle reconstruction"
    - "accepted arbitrary Extension-permutation actual section and backward projection"
    - "accepted finite-carrier and exact-support noncoverage witnesses"
  proof_obligation: "remove the finite-carrier assumption from the primitive permutation section's faithfulness; reconstruct every carrier-relative actual local-fiber-kernel image multiplicatively from source permutations and from stored-backward observations; connect explicit Nat and Set Nat witnesses outside the prior represented unions"
  selection_reason: "this moves from finite comparison tables to an arbitrary-carrier actual kernel fragment, proves separation and two distinct inverse surfaces, and records strict noncoverage rather than adding one more isolated finite carrier"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122ArbitraryCarrierKernelReconstruction.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "canonical primitive probes separate Equiv.Perm E for every Type E; actual stored-backward projection then proves the arbitrary-carrier local-fiber-kernel section injective; source permutations reconstruct its actual range as a multiplicative equivalence, and the actual range reconstructs its observed-action range as a second multiplicative equivalence; the carrier-indexed union properly contains all finite-carrier lookup-table images via the Nat zero-one swap, while the represented Set Nat complement remains outside all exact-support carrier images"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.sourceContextObjectPermHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.localFiberKernelSection_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.source_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.sourceActualMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.backwardObservation_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.backwardObservationHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.actualObservedMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.observedRead_observe"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.observe_observedRead"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.finiteCarrierImage_ssubset_arbitraryCarrierImage"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.powerSetComplement_not_mem_exactSupportCarrierUnion"
    - "AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction.reconstruction_and_strict_noncoverage"
  claim_mapping:
    conjuncts:
      - "the primitive carrier is an arbitrary Type; no Fintype or DecidableEq premise is required for section faithfulness"
      - "canonical source probes separate all source permutations"
      - "stored-backward actual observations separate all values in the represented kernel image"
      - "source permutations and the actual image satisfy read/assemble both ways and form a multiplicative equivalence"
      - "actual image values and their observed-action image form a second multiplicative equivalence"
      - "the arbitrary-carrier family properly contains the union of all finite-carrier lookup-table images"
      - "the represented powerset-complement witness lies outside all exact-support carrier images"
    undischarged_assumptions:
      - "recover the full local-fiber kernel outside all arbitrary single-carrier permutation images"
      - "recover the full comparison group and comparison restriction kernel"
      - "extend reconstruction to arbitrary expanded G-122 Homs and objects"
      - "discharge final four-family separation and assembly"
    acceptance_point: "unrestricted carrier-relative kernel separation, multiplicative source/actual and actual/observation reconstruction, and two strict noncoverage connections in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "primitive Extension probe evaluation"
      - "fixed source-to-actual context equivalence"
      - "faithful full local-fiber backward projection"
      - "accepted Nat and Set Nat source-owned obstruction witnesses"
    discharge_required:
      - "source permutation injectivity without finiteness"
      - "actual section injectivity through stored-backward observation"
      - "both source/actual inverse laws and multiplicativity"
      - "actual/observed range inverse laws and multiplicativity"
      - "proper finite-carrier-union inclusion and exact-support nonmembership"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "source separation / evaluation on independently constructed canonical probes"
      - "actual separation / stored-backward projection and fixed-route conjugation"
      - "strictness / explicit Nat and Set Nat source recipes"
    unresolved:
      - "independent local presentation of the whole actual kernel"
  proof_use:
    used:
      - "Cycle 56 fixed-route conjugation injectivity"
      - "accepted arbitrary-carrier local-fiber-kernel section"
      - "accepted finite-carrier and exact-support obstruction theorems"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "removes an artificial finiteness premise, gives substantive multiplicative reconstruction on two actual surfaces, and proves explicit strict progress beyond both earlier represented unions"
  vacuity: "source syntax is only Equiv.Perm E; actual range witnesses occur only in codomain subtypes, and the separating Nat and Set Nat values are fixed source recipes already proved outside the older unions"
  four_lane_question: "Does removing finiteness from the primitive Extension carrier yield faithful multiplicative reconstruction of each actual permutation-kernel image from source permutations, with two-sided stored-backward observation recovery and explicit Nat and Set Nat witnesses outside the prior finite-carrier and exact-support unions?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122ArbitraryCarrierKernelReconstruction.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction: 23 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122ArbitraryCarrierKernelReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122ArbitraryCarrierKernelReconstruction: pass (4428 jobs)"
  blocking_findings: []
  next_obligation: "recover a multi-carrier or full actual kernel surface beyond single-carrier permutation images, or extend the same substantive separation and assembly to arbitrary expanded G-122 Homs in one cycle"
```

## Cycle 58: two-carrier expanded reconstruction

```yaml
cycle: 58
status: implementation-complete-review-pending
branch: codex/4711-g124-two-carrier-expanded-reconstruction
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: ff16abdfe07115726f3efd2e9e2782b964f7e2d9
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 57 audit: PR comment 5733834854; acceptance: Issue comment 5733842648; Cycle 58 selection: Issue comment 5733925828"
  proof_dag_predecessors:
    - "Cycle 57 arbitrary-carrier faithful kernel reconstruction"
    - "accepted primitive source actions and fixed-route context transport"
    - "accepted canonical normalization section and normalized barAlpha comparison section"
  proof_obligation: "combine two unequal primitive Extension-carrier permutation groups as a faithful commuting actual-kernel representation; reconstruct the source pair from kernel, stored-backward observation, expanded direct-endpoint, and normalized comparison images; prove strict progress beyond the complete single-carrier family"
  selection_reason: "this enlarges the represented actual family rather than re-exporting Cycle 57, supplies four multiplicative inverse surfaces, carries the new family through the expanded direct and comparison surfaces in the same cycle, and fixes one adversarial audit question"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122TwoCarrierExpandedReconstruction.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "unequal primitive carrier actions commute at source, transported-context, and actual-kernel levels; their product hom is faithful; source pairs are multiplicatively equivalent to their actual kernel range, observed-action range, canonical expanded direct range, and normalized barAlpha comparison range; the existential two-carrier family properly contains every single-carrier image, with the simultaneous Nat zero-one swap and Set Nat complement as a fixed separating witness"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.extensionValuePermutation_commute"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourceContextObjectPerm_commute"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.transportedSourceContextPermutation_commute"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.localFiberKernelSection_commute"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.pairKernelHom"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.pairKernelHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourcePairKernelMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.pairKernelObservedMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourcePairObservedMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourcePairExpandedDirectMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourcePairComparisonMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.sourcePairHom_ne_singleCarrier"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.natPowerSetPairKernel_not_arbitraryCarrierImage"
    - "AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction.arbitraryCarrierImage_ssubset_twoCarrierImage"
  claim_mapping:
    conjuncts:
      - "actions on unequal primitive Extension carriers commute before and after the accepted fixed transport"
      - "stored-backward faithfulness reflects that commutativity into the actual local-fiber kernel"
      - "the pair product hom is injective by independent carrier probes"
      - "source pairs and the actual kernel range form a multiplicative equivalence"
      - "the actual range and its stored-backward observed range form a multiplicative equivalence"
      - "source pairs reconstruct the canonical expanded direct-endpoint range"
      - "source pairs reconstruct the normalized barAlpha comparison range"
      - "the existential two-carrier family properly contains all single-carrier images"
    undischarged_assumptions:
      - "recover the full local-fiber kernel outside all finite multi-carrier products"
      - "recover every expanded G-122 Hom rather than the represented direct and comparison images"
      - "recover the full comparison group and both ambient and restriction kernels"
      - "discharge final four-family separation and assembly"
    acceptance_point: "faithful two-carrier product, four multiplicative reconstruction ranges, expanded direct/comparison connection, and proper enlargement of the full single-carrier family in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "primitive Extension carrier dispatch by classical type equality"
      - "fixed-route context conjugation and its injectivity"
      - "full local-fiber stored-backward projection injectivity"
      - "canonical normalization automorphism section right inverse"
      - "normalized barAlpha comparison source projection"
    discharge_required:
      - "cross-carrier commutativity through all three action levels"
      - "pair injectivity from independent primitive probes"
      - "kernel, observation, expanded direct, and comparison range equivalences"
      - "single-carrier inclusion using a provably unequal powerset carrier"
      - "strictness via the simultaneous Nat and Set Nat action"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "source pair / two independently supplied permutations only"
      - "separation / canonical primitive probes on each carrier"
      - "strictness / fixed Nat swap and powerset complement source recipes"
    unresolved:
      - "independent presentation of arbitrary full-kernel elements"
      - "surjectivity for arbitrary expanded G-122 Homs"
  proof_use:
    used:
      - "Cycle 57 arbitrary-carrier section and single-carrier image family"
      - "Cycle 56 fixed-route conjugation API"
      - "accepted canonical normalization and comparison sections"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "replaces the single-carrier family by a strictly larger actual two-carrier family and connects the same source data through kernel, observation, expanded direct, and comparison ranges"
  vacuity: "source syntax is a pair of primitive permutations; the actual range memberships are codomain subtypes created after evaluation, and strictness is proved by carrier probes rather than supplied as a certificate"
  four_lane_question: "Does the product of independent permutations on two distinct Extension carriers form a faithful commuting actual-kernel representation, reconstruct multiplicatively from stored-backward observations and from expanded direct/comparison images, and strictly enlarge the full single-carrier family via the Nat/Set Nat simultaneous action?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122TwoCarrierExpandedReconstruction.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction: 36 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122TwoCarrierExpandedReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122TwoCarrierExpandedReconstruction: pass (4429 jobs)"
  blocking_findings: []
  next_obligation: "extend finite multi-carrier products beyond two carriers with one coherent finite-family reconstruction and an additional strict witness, or discharge a nontrivial arbitrary expanded-Hom separation and assembly surface"
```

## Cycle 59: finite multi-carrier expanded reconstruction

```yaml
cycle: 59
status: implementation-complete-review-pending
branch: codex/4711-g124-finite-multicarrier-expanded-reconstruction
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 9b7e650ea5bde19219cf8203707f7ed23103b955
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 58 audit: PR comment 5734343459; Cycle 58 acceptance: Issue comment 5734789276; Cycle 59 selection: Issue comment 5734789954"
  proof_dag_predecessors:
    - "Cycle 58 faithful two-carrier reconstruction across four actual surfaces"
    - "Cycle 57 arbitrary single-carrier faithfulness"
    - "accepted fixed source-to-actual transport and stored-backward faithfulness"
  proof_obligation: "construct one coherent faithful actual-kernel representation for every finite family of pairwise unequal primitive carriers; reconstruct it multiplicatively on kernel, stored-backward, expanded direct, and normalized comparison ranges; prove strict enlargement of the entire two-carrier family"
  selection_reason: "this replaces a fixed pair by arbitrary finite support, includes separation and four inverse surfaces in the same cycle, carries the construction to both expanded surfaces, and adds a three-carrier strict witness rather than stopping at a common-surface re-export"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FiniteMultiCarrierExpandedReconstruction.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "pairwise unequal finite carrier actions admit an order-independent commuting product; canonical carrier probes separate its source code; an explicit opposite-inverse recovery hom identifies the actual kernel product with fixed transport of the source product and proves faithfulness; source codes are multiplicatively equivalent to the actual kernel, stored-backward, expanded direct, and normalized comparison ranges; every two-carrier product embeds as a Bool-indexed family, while the simultaneous Nat, Set Nat, and Set (Set Nat) action lies outside all two-carrier images"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.CarrierFamily"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyHom_probe"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.familyKernelHom_recovery"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.familyKernelHom_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyKernelMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyObservedMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyExpandedDirectMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.sourceFamilyComparisonMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.binary_familyKernelHom"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.tripleKernel_not_twoCarrierImage"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.twoCarrierImage_ssubset_finiteCarrierImage"
    - "AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction.finite_family_reconstruction_and_strict_progress"
  claim_mapping:
    conjuncts:
      - "finite pairwise unequal carrier actions commute and form a multiplicative source and actual product"
      - "canonical probes recover every component, so source and actual products are faithful"
      - "actual recovery is derived from stored-backward projection through unop and inversion"
      - "source families reconstruct four actual ranges multiplicatively"
      - "the accepted two-carrier family embeds definitionally through a Bool-indexed family"
      - "a fixed three-carrier action moves all three carriers and excludes every two-carrier representation"
    undischarged_assumptions:
      - "recover the full local-fiber kernel outside all finite multi-carrier products"
      - "recover every expanded G-122 Hom rather than the represented direct and comparison ranges"
      - "recover the full comparison group and both ambient and restriction kernels"
      - "discharge final four-family separation and assembly"
    acceptance_point: "arbitrary finite-support faithful kernel reconstruction, four multiplicative actual surfaces, pair inclusion, and a strict three-carrier witness in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "pairwise carrier inequality supplied as source-family data"
      - "primitive carrier action and canonical Extension probes"
      - "fixed source-to-actual transport injectivity"
      - "full stored-backward projection injectivity"
      - "canonical normalization and normalized comparison sections"
    discharge_required:
      - "noncommutative finite-product well-definedness and multiplicativity"
      - "componentwise probe separation"
      - "actual-to-source recovery for the whole finite product"
      - "four range equivalences"
      - "two-carrier inclusion and fixed three-carrier strictness"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "source syntax / a finite index, carrier family, pairwise inequality, and one independently supplied permutation per member"
      - "separation / canonical primitive probes"
      - "strictness / source-owned Nat swap and two powerset complements"
    unresolved:
      - "independent local presentation of arbitrary full-kernel elements"
      - "surjectivity for arbitrary expanded G-122 Homs"
  proof_use:
    used:
      - "Cycle 58 cross-carrier commutation and pair reconstruction"
      - "Cycle 57 arbitrary-carrier section"
      - "accepted canonical normalization and comparison sections"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "upgrades fixed pairs to arbitrary finite support, proves a strict support hierarchy, and keeps all four actual surfaces in one theorem package"
  vacuity: "family source syntax contains no actual value or range certificate; pairwise inequality is a carrier-side premise, and strictness is detected by a third independently moved primitive probe"
  four_lane_question: "Does every finite family of pairwise unequal Extension carriers admit a faithful commuting actual-kernel product representation with multiplicative reconstruction on kernel, stored-backward, expanded direct, and normalized comparison ranges, while a Nat / Set Nat / Set (Set Nat) simultaneous action proves that this finite-family image strictly contains the complete two-carrier image?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122FiniteMultiCarrierExpandedReconstruction.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction: 65 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FiniteMultiCarrierExpandedReconstruction.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122FiniteMultiCarrierExpandedReconstruction: pass (4430 jobs)"
  blocking_findings: []
  next_obligation: "recover an infinite locally finite carrier-support limit with substantive finite-restriction assembly, or discharge a nontrivial arbitrary expanded-Hom separation and assembly surface"
```

## Cycle 60: full comparison and kernel decomposition

```yaml
cycle: 60
status: implementation-complete-review-pending
branch: codex/4711-g124-full-comparison-kernel-decomposition
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 7acbd8277b9ae8a6999f0ef807fddfc9bac6c8cb
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 59 audit: PR comment 5734831359; Cycle 59 acceptance: Issue comment 5734839946; Cycle 60 selection: Issue comment 5734866822"
  proof_dag_predecessors:
    - "accepted surjective comparison restriction and canonical section"
    - "accepted normalized comparison source equivalence"
    - "accepted free transitive full-kernel action on every actual lift fiber"
  proof_obligation: "classify every full raw comparison by one normalized comparison and one unique full restriction-kernel displacement; expose the induced noncommutative multiplication; connect the normalized factor to the actual normalized source automorphism group and every full lift fiber"
  selection_reason: "this moves beyond represented finite-family images to the full raw comparison group, proves explicit two-sided reconstruction and uniqueness, includes the conjugation-twisted multiplication law, and carries the result through the normalized source automorphism and lift-fiber surfaces in the same cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FullComparisonKernelDecomposition.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "every full raw comparison is assembled from its restricted normalized comparison and the unique residual element of the full actual restriction kernel; explicit read and assemble maps satisfy both inverse laws; multiplication is governed by conjugation of the first kernel displacement by the second canonical lift; the normalized comparison factor is multiplicatively equivalent to the normalized direct source automorphism group; every full lift fiber has the same unique full-kernel displacement property"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.canonicalSectionHom"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.readKernel_mem"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.fullComparisonEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.normalizedComparisonSourceMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.readSource_assembleSource"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.assembleSource_readSource"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.fullComparisonSourceEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.assemble_mul_formula"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.read_mul_kernel"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.readKernel_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition.fullLiftFiber_existsUnique_kernel"
  claim_mapping:
    conjuncts:
      - "the canonical section followed by restriction supplies the normalized component of every raw comparison"
      - "the residual canonical-lift inverse times the raw comparison lies in the full restriction kernel"
      - "explicit read and assembly maps are mutually inverse on the full groups"
      - "the transported product has the stated conjugation-twisted kernel formula"
      - "the kernel displacement is unique both for raw comparisons and for every full lift fiber"
      - "the normalized factor is exactly the normalized direct source automorphism group"
    undischarged_assumptions:
      - "independently present every full-kernel element by primitive local syntax"
      - "recover arbitrary expanded G-122 Homs outside the comparison group"
      - "discharge final four-family separation and assembly"
    acceptance_point: "full raw-comparison two-sided reconstruction, unique full-kernel displacement, twisted multiplication, source-automorphism connection, and full-lift-fiber uniqueness in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "surjectivity of the full restriction homomorphism"
      - "canonical section right-inverse law"
      - "comparison equation forcing the normalized target automorphism from its source"
      - "full lift-fiber kernel torsor theorem"
    discharge_required:
      - "kernel membership of the residual displacement"
      - "both inverse laws on the full raw comparison group"
      - "conjugation-twisted multiplication formula"
      - "raw-comparison kernel uniqueness"
      - "source-automorphism reparameterization with both inverse laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "normalized component / actual restriction homomorphism"
      - "kernel component / residual computed from the canonical section"
      - "source component / projection from the normalized comparison equation"
    unresolved:
      - "primitive local syntax for arbitrary elements of the full actual kernel"
      - "surjectivity for arbitrary expanded G-122 Homs"
  proof_use:
    used:
      - "accepted canonical comparison section and right-inverse theorem"
      - "accepted full comparison restriction homomorphism"
      - "accepted generated comparison source equivalence"
      - "accepted full lift-fiber free transitive action"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "replaces finite-family comparison images by the complete fixed raw comparison group and gives an explicit reconstruction law without claiming a primitive presentation of the full kernel"
  vacuity: "the code contains only a genuine full-kernel element and a normalized comparison or source automorphism; kernel membership is derived from restriction and section laws, and both inverse equations are proved"
  four_lane_question: "Does the full fixed raw `barAlpha` comparison group admit an explicit two-sided reconstruction by its canonical normalized comparison and a unique full restriction-kernel displacement, with the correct conjugation-twisted multiplication law, full-lift-fiber uniqueness, and normalized-source automorphism connection?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122FullComparisonKernelDecomposition.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition: 25 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FullComparisonKernelDecomposition.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122FullComparisonKernelDecomposition: pass (4299 jobs)"
  blocking_findings: []
  next_obligation: "construct a primitive local presentation for arbitrary full-kernel elements and connect its own separation and assembly to this full comparison decomposition, or discharge a nontrivial arbitrary expanded-Hom reconstruction surface"
```

## Cycle 61: full source-kernel exact decomposition

```yaml
cycle: 61
status: accepted
branch: codex/4711-g124-full-source-kernel-exact-decomposition
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: a3d22a582c20aa0b3ec726465856b1ec8f7651f8
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 60 audit: PR comment 5735201319; Cycle 60 acceptance: Issue comment 5735210832; Cycle 61 selection: Issue comment 5735223007"
  proof_dag_predecessors:
    - "Cycle 60 full comparison and kernel decomposition"
    - "accepted source classification of comparison groups for an isomorphism"
    - "accepted endpoint normalization homomorphism"
  proof_obligation: "identify the full raw and normalized comparison groups with their complete direct-endpoint automorphism groups; prove that comparison restriction is endpoint normalization in source coordinates; identify the full comparison kernel multiplicatively with the direct normalization kernel; transport the full two-sided reconstruction, uniqueness, and twisted product to those source-kernel coordinates"
  selection_reason: "this replaces the opaque pair-valued comparison kernel by its exact source normalization kernel, proves a multiplicative kernel equivalence with explicit inverses, and carries the Cycle 60 reconstruction and product law to that common source surface in the same cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FullSourceKernelExactDecomposition.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "source projection gives a multiplicative equivalence from every raw comparison to the actual direct-endpoint automorphism group; the normalized analogue is reused on the complete normalized group; the restriction/source square commutes with direct normalization; explicit forward and inverse homomorphisms identify the full comparison kernel with the full direct normalization kernel; source-kernel read and assembly maps satisfy both inverse laws; every raw comparison has a unique source-kernel displacement over its restricted normalized source; multiplication obeys the transported conjugation-twisted formula"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.rawComparisonSourceMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.directNormalizationHom"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.source_restriction_commutes"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.fullKernelToSourceKernelHom"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.sourceKernelToFullKernelHom"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.fullKernelToSourceKernel_sourceKernelToFullKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.sourceKernelToFullKernel_fullKernelToSourceKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.fullKernelSourceMulEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.readSourceKernel_assembleSourceKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.assembleSourceKernel_readSourceKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.fullSourceKernelEquiv"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.sourceKernelCoordinate_existsUnique"
    - "AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition.assembleSourceKernel_mul_formula"
  claim_mapping:
    conjuncts:
      - "the full raw comparison group is multiplicatively classified by its direct source automorphism"
      - "comparison restriction and direct-endpoint normalization commute under source projection"
      - "the full comparison restriction kernel and full direct normalization kernel are multiplicatively equivalent"
      - "both kernel-equivalence inverse laws are explicit"
      - "source-kernel read and assembly are mutually inverse on every raw comparison"
      - "the source-kernel displacement over a fixed normalized source is unique"
      - "the noncommutative multiplication retains the Cycle 60 conjugation twist"
    undischarged_assumptions:
      - "present arbitrary direct normalization-kernel automorphisms by primitive local syntax"
      - "recover arbitrary expanded G-122 Homs outside the comparison group"
      - "discharge final four-family separation and assembly"
    acceptance_point: "full source classification, commuting normalization square, multiplicative kernel equivalence with explicit inverses, unique source-kernel coordinates, and transported twisted reconstruction in one cycle"
    port_status: unported
audits:
  material_premises:
    proved_dependencies:
      - "comparison source projection is an equivalence when the comparison arrow is an isomorphism"
      - "actual and normalized fixed barAlpha are isomorphisms"
      - "Cycle 60 full comparison read and assembly"
    discharge_required:
      - "source/restriction commuting square"
      - "kernel forward and inverse membership"
      - "both kernel inverse laws and multiplicativity"
      - "source-kernel read/assembly inverse laws"
      - "fixed-normalized-source uniqueness"
      - "transported twisted multiplication"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "comparison kernel membership / derived by applying restriction and the source commuting square"
      - "source kernel membership / derived by applying endpoint normalization and the inverse source equivalence"
      - "source-kernel coordinates / computed from Cycle 60 readback and the kernel equivalence"
    unresolved:
      - "primitive local syntax and assembly for arbitrary direct normalization-kernel elements"
      - "surjectivity for arbitrary expanded G-122 Homs"
  proof_use:
    used:
      - "Cycle 60 full comparison kernel decomposition"
      - "generated comparison source equivalence"
      - "functor-induced direct automorphism normalization"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "reduces the complete comparison-kernel problem to the exact direct source normalization kernel and transports all Cycle 60 reconstruction laws without treating completed automorphisms as primitive syntax"
  vacuity: "kernel memberships are derived from the commuting square and inverse source equivalences; both directions are proved, and the result quantifies over the complete raw comparison and direct normalization kernels rather than a selected image"
  four_lane_question: "Does source projection identify the full raw and normalized comparison groups with the complete direct-endpoint automorphism groups, intertwine comparison restriction with endpoint normalization, identify the full comparison kernel multiplicatively with the direct normalization kernel, and transport Cycle 60's two-sided twisted reconstruction into those source-kernel coordinates?"
  validation_refs:
    - "cd research/lean && lake env lean ResearchLean/AG/LocalSemanticReconstruction/G122FullSourceKernelExactDecomposition.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition: 19 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FullSourceKernelExactDecomposition.lean: pass"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122FullSourceKernelExactDecomposition: pass (4300 jobs)"
  blocking_findings: []
  next_obligation: "construct an independent primitive local presentation with separation and assembly for arbitrary direct normalization-kernel automorphisms and connect it to the full source-kernel equivalence, or discharge a nontrivial arbitrary expanded-Hom reconstruction surface"
```

## Cycle 62: primitive fiber-permutation graph and source-kernel object action

```yaml
cycle: 62
status: accepted
branch: codex/4711-g124-primitive-fiber-permutation-graph
pull_request: 4775
fixed_head: f94820916d7288d61caebd139720f370af6b48fa
merge_commit: bf71fc79d8093c6bd315e18a81c2f5429727eafd
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: b635ffc87cb71e163619b6004ffb25878a3d9ef8
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 61 audit: PR comment 5735614256; Cycle 61 acceptance: Issue comment 5735619932; Cycle 62 selection: Issue comment 5735760543"
  proof_dag_predecessors:
    - "Cycle 61 full source-kernel exact decomposition"
    - "canonical object normalization naturality"
    - "source-authored finite-axis-fold ambient-kernel recipe"
  proof_obligation: "construct an independent Bool-valued graph family for arbitrary normalization-fiber-preserving permutations; prove explicit assembly, both inverse laws, the full group equivalence, and relational multiplication; map every direct normalization-kernel automorphism multiplicatively to that primitive object-action model; exhibit a nonidentity source-authored graph and carry it through the full source-kernel comparison reconstruction"
  selection_reason: "this replaces a completed permutation by point-pair Bool readings with independent exact-one row and column laws, proves a genuine two-sided universal classification, and includes the G-122 kernel and raw-comparison connection in the same cycle rather than postponing the connection"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/PrimitiveFiberPermutationGraph.lean"
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveSourceKernelObjectGraph.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "an independent graph code stores only one Bool per ordered point pair and exact-one row/column plus fiber equations; unique witnesses assemble a permutation and inverse; read and assembly satisfy both inverse laws; transported multiplication is proved equal to relational graph composition; direct normalization-kernel automorphisms induce fiber-preserving object permutations and a multiplicative primitive graph reading; the source-authored direct ambient-kernel recipe has a nonidentity graph, transports to a nonidentity full comparison-kernel element with trivial restriction, and is recovered by Cycle 61 read/assembly at normalized identity"
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphData"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.IsExact"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphData.diagonal_isExact"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphData.falseBool_not_isExact"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.targetEquiv"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.assemble"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.read"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.graphMulEquivFiberPermutation"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph.GraphCode.mul_edge_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.sourceKernelObjectPermutationHom"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.sourceKernelObjectPermutationHom_coe"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.sourceKernelObjectGraphHom"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.assemble_sourceKernelObjectGraphHom"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.sourceKernelObjectGraph_mul_edge_iff"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.directAmbientSourceKernel_objectGraph_ne_one"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.directAmbientFullComparisonKernel_restriction"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.directAmbientFullComparisonKernel_eq_sourceKernelToFullKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.directAmbientFullComparisonKernel_ne_one"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.assembleSourceKernel_eq_canonicalSection_mul"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.assembleSourceKernel_directAmbient"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph.readSourceKernel_directAmbient"
  claim_mapping:
    conjuncts:
      - "each primitive local value is Bool, indexed by one ordered pair rather than a completed global map"
      - "exact-one outgoing and incoming laws assemble both a permutation and its inverse"
      - "read and assembly are mutually inverse for every fiber-preserving permutation"
      - "the transported group law is the local relational composition formula"
      - "every direct normalization-kernel automorphism yields a multiplicative primitive object graph"
      - "the source-authored ambient kernel is separated from identity by this graph"
      - "the same nonidentity value has trivial comparison restriction and explicit Cycle 61 source-kernel coordinates"
    undischarged_assumptions:
      - "object action does not yet separate complete geometry automorphisms with identical object maps"
      - "remaining atom, context, equation, operation, coefficient, raw, and local-realization readings require their own primitive graph surfaces"
      - "surjectivity of a joint primitive code onto the full direct normalization kernel remains unproved"
      - "arbitrary expanded G-122 Homs and final four-family assembly remain unproved"
    acceptance_point: "full two-sided and multiplicative classification of arbitrary fiber-preserving permutations by independent point-pair Bool local readings, plus a multiplicative G-122 object-action reading and a nontrivial full-comparison witness in one cycle"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "an arbitrary normalization map alpha to beta for the generic theorem"
      - "the fixed finite-axis-fold actual direct endpoint for the G-122 application"
    direction_hypotheses:
      - "exact-one outgoing and incoming laws on the raw Bool graph"
      - "fiber preservation for every true raw-graph edge"
    proved_dependencies:
      - "classical equality selection used internally by graph reading; Classical.decEq discharges it without a public DecidableEq premise"
      - "canonical object normalization naturality"
      - "Cycle 61 full source-kernel equivalence and reconstruction"
      - "source-authored ambient-kernel automorphism and normalization-kernel membership"
    discharge_required:
      - "permutation and inverse from exact-one graph laws"
      - "both graph inverse laws"
      - "group equivalence and relational multiplication"
      - "fiber preservation of the complete kernel object action"
      - "multiplicativity of the object graph reading"
      - "nonidentity of the ambient graph and raw comparison"
      - "trivial restriction and Cycle 61 read/assembly connection"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "positive exactness fixture / the diagonal raw Bool graph"
      - "negative exactness fixture / the constant-false Bool graph on Bool"
      - "assembled target and inverse / unique row and column witnesses"
      - "fiber preservation / local true-edge equation"
      - "G-122 graph / evaluation of the actual object map at each ordered pair"
      - "ambient witness / independent source recipe from the fixed original input"
    unresolved:
      - "joint primitive code for every computational component of a complete geometry automorphism"
      - "joint separation and assembly for the full direct normalization kernel"
  proof_use:
    used:
      - "row and column uniqueness in both inverse proofs"
      - "fiber equation in subgroup assembly"
      - "kernel equation and canonical normalization naturality in the G-122 object action"
      - "Cycle 61 kernel equivalence in the full comparison witness"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "introduces a reusable primitive local reading whose individual values are finite, proves its complete separation and assembly theorem, and applies it to a genuine component of every full G-122 source-kernel element without claiming that one component classifies the entire automorphism"
  vacuity: "row and column witnesses yield an actual permutation and inverse; the ambient recipe supplies an explicit nonidentity graph and nonidentity raw comparison"
  four_lane_question: "Does an independently defined Bool-valued exact graph family classify every normalization-fiber-preserving permutation with explicit inverse laws and relational multiplication, and does the direct normalization kernel map multiplicatively to this primitive object-action model while carrying a nontrivial ambient-kernel element through the full source-kernel comparison reconstruction?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/PrimitiveFiberPermutationGraph.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveSourceKernelObjectGraph.lean: pass"
  validation_evidence:
    - "#assert_standard_axioms_only PrimitiveFiberPermutationGraph: 64 declarations, standard axioms only"
    - "#assert_standard_axioms_only G122PrimitiveSourceKernelObjectGraph: 22 declarations, standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveSourceKernelObjectGraph: pass (4302 jobs)"
  blocking_findings: []
  next_obligation: "extend the independent graph presentation to the remaining primitive components of complete geometry automorphisms and prove joint separation plus assembly for the full direct normalization kernel, or discharge a nontrivial arbitrary expanded-Hom reconstruction surface"
```

## Cycle 63: arbitrary function graphs and G-122 primitive map reading

```yaml
cycle: 63
status: implementation-complete-review-pending
branch: codex/4711-g124-primitive-function-graph-category
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: bf71fc79d8093c6bd315e18a81c2f5429727eafd
tracking_issue: 4711
selection:
  proof_state_ref: "Cycle 62 final audit: PR comment 5736414350; Cycle 62 acceptance: Issue comment 5736419147; Cycle 63 selection: Issue comment 5736442436"
  proof_dag_predecessors:
    - "Cycle 62 primitive Bool graph discipline"
    - "arbitrary G-122 geometry morphisms and their computational component maps"
    - "Cycle 47 accepted fixed two-point comparison probe and local-image reconstruction"
  proof_obligation: "classify arbitrary functions by an independent Bool graph with total-functional laws, explicit inverse laws, identity, categorical composition, and relational composition; package the graph category as fully faithful over Type; in the same cycle read five ordinary maps of every G-122 geometry Hom compositionally and factor the accepted fixed comparison probe through the object graph with two-sided local-image reconstruction"
  selection_reason: "the cycle contains a genuine arbitrary-function classification and fully faithful categorical presentation rather than a new definition or alias, and bundles the G-122 common-surface connection and accepted finite reconstruction instead of postponing them"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/PrimitiveFunctionGraphCategory.lean"
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveFunctionGraphReading.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "raw graph data stores only a Bool edge relation while totality and functionality remain a Prop; unique targets assemble arbitrary functions; reading and assembly are mutually inverse; identity and graph composition assemble to ordinary identity and composition; graph composition is relational composition; the resulting graph category maps fully faithfully to Type with explicit preimages. Every G-122 geometry Hom yields source, Atom, object, raw-context, and coefficient graphs whose assembly recovers the five functions and whose readings preserve identity and composition. The accepted fixed two-point object probe factors through object-graph assembly, and the established local semantic image is reconstructed through this factorization with both inverse laws."
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphData"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.IsTotalFunctional"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphData.diagonal_isTotalFunctional"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphData.falseBool_not_isTotalFunctional"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode.graphEquivFunction"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode.assemble_comp"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.GraphCode.comp_edge_eq_true_iff"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.Object.toType"
    - "AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph.Object.toTypeFullyFaithful"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.PrimitiveMapGraphs"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.readPrimitiveMaps"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.assemble_readPrimitiveMaps"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.readPrimitiveMaps_id"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.readPrimitiveMaps_comp"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.graphProbeRestriction_eq_coreProbe_objectRestriction"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.graphPrimitiveRead_eq_primitiveRead"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.graphPrimitiveRead_assemble"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.assemble_graphPrimitiveRead"
    - "AAT.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading.graphPrimitiveSemanticEquivLocal"
  claim_mapping:
    conjuncts:
      - "each primitive local value is Bool and the raw data carries no completed target function or total-functional witness"
      - "total-functional laws assemble one target for every source"
      - "read and assembly are mutually inverse for arbitrary source and target types"
      - "identity, categorical composition, and relational graph composition agree"
      - "the graph category has a fully faithful functor to Type with explicit Hom preimages"
      - "five computational maps of every G-122 geometry Hom recover pointwise and preserve identity and composition"
      - "the accepted finite comparison probe factors through object-graph assembly and still reconstructs its fixed local image in both directions"
    undischarged_assumptions:
      - "the five graph maps do not separate complete geometry Homs with identical primitive maps"
      - "dependent operation, equation, invariant, axis, coordinate, support, observable, and raw-relation maps remain additional readings"
      - "joint primitive assembly onto the full direct normalization kernel remains unproved"
      - "arbitrary expanded G-122 Hom reconstruction and final four-family assembly remain unproved"
    acceptance_point: "arbitrary-function Bool graph classification with explicit inverse laws and a fully faithful categorical presentation, plus compositional five-map G-122 reading and fixed accepted probe reconstruction in one cycle"
    port_status: unported
audits:
  material_premises:
    ambient_boundary:
      - "arbitrary source and target types for the generic classification"
      - "arbitrary geometry packages over one Atom carrier for the five-map reading"
      - "the fixed finite-axis-fold comparison endpoints only for the final probe factorization"
    direction_hypotheses:
      - "total existence and target uniqueness for every raw graph row"
    proved_dependencies:
      - "Cycle 47 fixed comparison probe and local-image assembly"
      - "definitional identity and composition laws of geometry morphism components"
    discharge_required:
      - "unique-target function assembly and both inverse laws"
      - "relational formula for graph composition"
      - "category laws and fully faithful Hom equivalence"
      - "five component recovery plus identity and composition"
      - "fixed probe factorization and both local-image inverse laws"
    conclusion_equivalent_risk: []
  certificate_provenance:
    discharged:
      - "positive raw fixture / diagonal Bool graph"
      - "negative raw fixture / constant-false Bool graph on Bool"
      - "assembled target / unique witness from the total-functional Prop"
      - "five G-122 graphs / evaluation of actual component functions"
      - "fixed local equivalence / the accepted two-point core probe after proved graph factorization"
    unresolved:
      - "primitive graph readings for all dependent geometry fields"
      - "joint separation and assembly for complete geometry morphisms or the full direct normalization kernel"
  proof_use:
    used:
      - "totality supplies assembled targets and functionality proves uniqueness"
      - "both inverse laws prove the function equivalence and fully faithful Hom map"
      - "composition recovery proves the geometry reading is compositional in all five fields"
      - "probe factorization transports the accepted local-image inverse laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: "extends independent finite-valued local graph syntax from permutations to arbitrary functions, gives it a fully faithful categorical presentation, and immediately applies it to genuine maps of every G-122 geometry Hom and to the accepted finite reconstruction surface without claiming full-Hom separation"
  vacuity: "the positive and negative fixtures distinguish the Prop from raw data, arbitrary functions are recovered in both directions, and the fixed local image has both graph-factorized inverse laws"
  four_lane_question: "Does a data/Prop-separated Bool graph presentation classify arbitrary functions with explicit inverse laws and categorical composition, and do the source, Atom, object, context, and coefficient maps of every G-122 geometry Hom read compositionally through that presentation while the accepted finite comparison probe factors through and reconstructs its fixed local image?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/PrimitiveFunctionGraphCategory.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122PrimitiveFunctionGraphReading.lean: pass"
  validation_evidence:
    - "#assert_standard_axioms_only PrimitiveFunctionGraph: 66 declarations, standard axioms only"
    - "#assert_standard_axioms_only G122PrimitiveFunctionGraphReading: 35 declarations, standard axioms only"
    - "cd research/lean && lake build ResearchLean.AG.LocalSemanticReconstruction.G122PrimitiveFunctionGraphReading: pass (4335 jobs)"
  blocking_findings: []
  next_obligation: "add independent graph readings for the remaining dependent geometry fields and prove a substantive joint separation-and-assembly theorem for complete G-122 geometry morphisms or the full direct normalization kernel"
```

## Cycle 64: complete computational graph separation and full-kernel coordinates

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 64
status: result-proposed
branch: codex/4711-g124-complete-geometry-graph-separation
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: c31914db8437c1798cf5799b722b80b270d16927
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 63 acceptance: Issue comment 5737027956; Cycle 64 selection: Issue comment 5737051626"
  proof_dag_predecessors:
    - "Cycle 63 arbitrary-function total-functional Bool graph equivalence"
    - "literal GeometryTotalHom computational extensionality spine"
    - "Cycle 61 full direct normalization-kernel coordinate equivalence"
  proof_obligation: "read every computational component used by GeometryTotalHom extensionality as an independent total-functional Bool graph, encode dependent families through tagged sigma maps, prove joint separation for arbitrary complete geometry morphisms, and connect that separation to the accepted full direct normalization-kernel coordinates and their two-sided assembly on the fixed G-122 raw comparison group"
  selection_reason: "this cycle closes the dependent-map separation gap itself and includes the full-kernel coordinate connection; it is neither a definition-only step nor a later common-surface wrapper"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryFunctionGraphSeparation.lean"
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122CompleteGraphKernelReconstruction.lean"
  risks:
    - "tagged sigma equality might fail to recover dependent fiber maps"
    - "object actions might fail to determine the selected-context equivalence"
    - "a completed morphism or equivalent certificate might escape into graph data"
    - "the fixed raw-comparison specialization might be overstated as arbitrary graph assembly"
  unchecked:
    - "coherence conditions and assembly for arbitrary CompleteMapGraphs values are outside this cycle"
    - "an independent primitive syntax for the full direct normalization kernel is outside this cycle"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "the five Cycle 63 maps are enlarged by a separate lower Atom graph, bidirectional selected-context graphs, equation-index and equation-observable graphs, tagged operation and coordinate graphs, invariant and signature-axis graphs, and tagged geometry support/axis/observable graphs. Equality of this complete bundle reconstructs every literal computational condition and separates arbitrary GeometryTotalHom values. On the fixed G-122 raw comparison group, the source complete-graph reading is injective, graph equality determines the accepted full source-kernel coordinates, and assembled code graphs are equal exactly when the codes are equal; the accepted read/assemble inverse laws remain connected in the same module."
  completion_candidate: no
  section_completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.taggedMap"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.fiberMap_heq_of_taggedMap_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.fiberMap₂_heq_of_taggedMap_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.equivFamily_heq_of_taggedMap_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.ringEquivFamily_heq_of_taggedMap_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.contextEquivalence_eq_of_object_maps_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.CompleteMapGraphs"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.inputConditions_of_graph_eq"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryFunctionGraphSeparation.readCompleteMapGraphs_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.readRawComparisonGraphs"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.readRawComparisonGraphs_injective"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.readSourceKernel_eq_of_graph_eq"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.assembledGraphs_eq_iff"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.graphs_assembleSourceKernel_readSourceKernel"
    - "AAT.AG.LocalSemanticReconstruction.G122CompleteGraphKernelReconstruction.readSourceKernel_assembleSourceKernel_with_graph_separation"
  evidence:
    - "readCompleteMapGraphs_injective"
    - "readRawComparisonGraphs_injective"
    - "readSourceKernel_eq_of_graph_eq"
    - "assembledGraphs_eq_iff"
    - "graphs_assembleSourceKernel_readSourceKernel"
    - "readSourceKernel_assembleSourceKernel_with_graph_separation"
  claim_mapping:
    theorem_names:
      - "readCompleteMapGraphs_injective"
      - "readRawComparisonGraphs_injective"
      - "readSourceKernel_eq_of_graph_eq"
      - "assembledGraphs_eq_iff"
      - "graphs_assembleSourceKernel_readSourceKernel"
      - "readSourceKernel_assembleSourceKernel_with_graph_separation"
    source_labels:
      - "Cycle 64 fixed four-lane question"
      - "G-124 Section B actual local reading and separation/assembly"
    conjuncts:
      - "raw graph fields contain Bool relations and total-functional Props, never a completed geometry morphism"
      - "dependent operation, equation-observable, coordinate, support, geometry-axis, and geometry-observable families are ordinary tagged-sigma functions before graph reading"
      - "forward and backward context-object graphs determine the complete context equivalence by thinness"
      - "complete graph equality reconstructs the accepted literal computational conditions"
      - "the complete graph reading jointly separates arbitrary GeometryTotalHom values"
      - "fixed raw comparison graphs separate all raw comparisons and determine full source-kernel coordinates"
      - "complete graphs of assembled full source-kernel codes agree exactly when the codes agree"
      - "accepted source-kernel read and assembly retain both inverse laws"
    undischarged_assumptions: []
    acceptance_point: "the cycle discharges arbitrary complete-Hom joint separation and carries it through the accepted fixed raw-comparison coordinate equivalence with both inverse laws in the same change"
    port_status: not-applicable
  nonclaims:
    - "an arbitrary CompleteMapGraphs value satisfies the preservation and naturality laws"
    - "an arbitrary complete graph bundle assembles to a GeometryTotalHom"
    - "the full direct normalization kernel has an independent primitive local syntax"
audits:
  premise_delta:
    discharged:
      - "dependent tagged-map recovery / fiberMap_heq_of_taggedMap_eq and fiberMap₂_heq_of_taggedMap_eq"
      - "dependent equivalence recovery / equivFamily_heq_of_taggedMap_eq and ringEquivFamily_heq_of_taggedMap_eq"
      - "selected-context equivalence recovery / contextEquivalence_eq_of_object_maps_eq"
      - "arbitrary complete-Hom joint separation / readCompleteMapGraphs_injective"
      - "fixed raw-comparison and source-kernel-code graph separation / readRawComparisonGraphs_injective and assembledGraphs_eq_iff"
    remaining:
      - "arbitrary complete graph bundle coherence and assembly / not claimed"
      - "independent primitive full-kernel syntax / not claimed"
  certificate_provenance:
    discharged:
      - "all graph fields / direct evaluation of actual computational functions"
      - "all dependent family equalities / tagged sigma function equality"
      - "complete Hom equality / accepted computational extensionality spine"
      - "source-kernel coordinate recovery / accepted raw-comparison source equivalence and source-kernel equivalence"
    unresolved:
      - "independent coherence conditions and assembly for arbitrary complete graph bundles"
      - "primitive local presentation and assembly for arbitrary direct normalization-kernel elements"
  proof_use:
    used:
      - "GraphCode assemble/read recovery converts graph equality to equality of tagged functions"
      - "tagged sigma injectivity recovers dependent map families"
      - "thin selected-context categories recover functors and the complete context equivalence from object actions"
      - "the literal computational extensionality spine reconstructs complete GeometryTotalHom equality"
      - "the accepted raw-comparison source equivalence and source-kernel equivalence transport joint separation to full coordinates"
    unused:
      - "CompleteMapGraphs.primitive.context is retained for compatibility with the Cycle 63 five-map bundle; complete separation uses the independently stored bidirectional selected-context actions instead"
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the cycle supplies dependent computational graphs, proves arbitrary-Hom joint separation, and immediately connects it to accepted full-kernel reconstruction without claiming arbitrary-graph assembly"
  vacuity: none-found
  vacuity_reason: "the theorem quantifies over every complete geometry Hom and every fixed raw comparison, and proves injectivity through computational fields rather than a stored completed morphism"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do total-functional Bool graphs of every computational component jointly separate arbitrary complete geometry morphisms, including the dependent maps via tagged sums, and does that separation determine the accepted full direct normalization-kernel coordinates of every fixed G-122 raw comparison while retaining the existing two-sided assembly?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryFunctionGraphSeparation.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122CompleteGraphKernelReconstruction.lean: pass"
  blocking_findings: []
  next_obligation: "define independent coherence conditions and assembly for arbitrary complete graph bundles, or reconstruct the full direct normalization kernel itself from primitive local syntax without storing completed automorphisms"
```

## Cycle 65: separation-and-assembly reconstruction principle

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 65
status: result-proposed
branch: codex/4711-g124-local-reconstruction-principle
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: f7f9a4eca58417c82b017fa5fe465d175db13621
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 64 acceptance: Issue comment 5737339682; Cycle 65 selection: Issue comment 5737354553"
  proof_dag_predecessors:
    - "Cycle 63 primitive total-functional Bool graph category and Hom inverse"
    - "Cycle 64 arbitrary complete-geometry graph separation"
    - "fixed GOAL B separation-and-assembly characterization of reconstruction"
  proof_obligation: "prove that independent Hom separation, Hom assembly, and object assembly characterize categorical equivalence; realize the theorem for primitive Bool graphs; connect complete geometry graphs exactly as the separation half"
  selection_reason: "this discharges the general categorical reconstruction spine with explicit two-sided Hom recovery and object recovery, includes a concrete nontrivial equivalence, and records the exact remaining AAT assembly input in the same cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/LocalReconstructionEquivalence.lean"
  risks:
    - "Hom assembly might be smuggled into separation or an image subtype"
    - "essential surjectivity might be asserted without an explicit assembled object and isomorphism"
    - "the primitive graph application might only re-export full faithfulness"
    - "the complete-geometry connection might overstate separation as arbitrary graph assembly"
  unchecked:
    - "independent coherence equations and assembly for arbitrary complete-geometry graph bundles remain outside this cycle"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "HomFamilySeparation isolates pointwise separation for indexed global/local Hom families, and HomSeparation specializes it to functor maps. HomSeparation, HomAssembly, and ObjectAssembly then derive the second Hom inverse, explicit Hom equivalences, unique Hom preimages, fully faithful and essentially surjective witnesses, and a categorical equivalence; conversely every categorical equivalence supplies the same reconstruction data. Primitive total-functional Bool graphs instantiate all fields and yield an equivalence with Type. Complete geometry graph reading instantiates HomFamilySeparation for every package pair, leaving local-category composition, independent coherence, and assembly explicit."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReadingSeparation"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.HomFamilySeparation"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.constantUnitReading_not_separating"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.constantUnitHomFamilyReading_not_separating"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.HomSeparation"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.HomAssembly"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ObjectAssembly"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReconstructionData"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReconstructionData.assemble_map"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReconstructionData.homEquiv"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReconstructionData.existsUnique_preimage"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ReconstructionData.equivalence"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.ofEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.nonempty_reconstructionData_iff_isEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.primitiveGraphEquivalenceType"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.primitiveGraph_homEquiv_symm_apply"
    - "AAT.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence.completeGeometryGraphSeparation"
  evidence:
    - "ReconstructionData.assemble_map"
    - "ReconstructionData.existsUnique_preimage"
    - "ReconstructionData.equivalence"
    - "nonempty_reconstructionData_iff_isEquivalence"
    - "primitiveGraphEquivalenceType"
    - "completeGeometryGraphSeparation"
    - "constantUnitReading_not_separating"
    - "constantUnitHomFamilyReading_not_separating"
  claim_mapping:
    theorem_names:
      - "ReconstructionData.assemble_map"
      - "ReconstructionData.homEquiv"
      - "ReconstructionData.existsUnique_preimage"
      - "ReconstructionData.equivalence"
      - "ofEquivalence"
      - "nonempty_reconstructionData_iff_isEquivalence"
      - "primitiveGraphEquivalenceType"
      - "completeGeometryGraphSeparation"
    source_labels:
      - "G-124 fixed target B separation and assembly"
      - "Cycle 65 fixed four-lane question"
    conjuncts:
      - "Hom separation is stated independently from Hom assembly"
      - "read-after-assembly plus separation derives assembly-after-read"
      - "every local Hom has an explicit unique global preimage"
      - "explicit object assembly produces essential surjectivity"
      - "the three contracts produce a categorical equivalence"
      - "every categorical equivalence returns the three contracts"
      - "constant Bool-to-PUnit readings give explicit negative fixtures for both separation predicates"
      - "primitive Bool graphs realize the full contract and are categorically equivalent to Type"
      - "complete geometry graph reading realizes the indexed Hom-family separation half for every package pair"
    undischarged_assumptions: []
    acceptance_point: "the general B reconstruction implication and converse are proved, the primitive graph category supplies an actual full application, and the complete-geometry application is accurately limited to its accepted separation result"
    port_status: not-applicable
  nonclaims:
    - "arbitrary complete-geometry graph bundles satisfy independent coherence equations"
    - "arbitrary complete-geometry graph bundles assemble to GeometryTotalHom values"
    - "complete-geometry graph bundles already form the target category of a reading functor"
    - "G-124 target B is fully discharged for all four required families"
audits:
  premise_delta:
    discharged:
      - "second Hom inverse / derived from Hom separation and read-after-assembly"
      - "full faithfulness / derived from the explicit Hom equivalence"
      - "essential surjectivity / derived from explicit object assembly and its reading isomorphism"
      - "categorical equivalence / derived from full faithfulness and essential surjectivity"
      - "primitive graph application / GraphCode read and assembly plus carrier wrapping"
    remaining:
      - "AAT complete-geometry local category, coherence, and Hom/object assembly / independent construction still required"
      - "four-family common realization and local model / still required"
  certificate_provenance:
    discharged:
      - "primitive Hom assembly / GraphCode.read with existing two inverse laws"
      - "primitive object assembly / direct carrier wrapper with reflexive isomorphism"
      - "complete geometry separation / Cycle 64 readCompleteMapGraphs_injective"
    unresolved:
      - "complete geometry Hom assembly / no witness or image subtype introduced"
  proof_use:
    used:
      - "HomSeparation.injective derives assembly-after-read and uniqueness"
      - "HomAssembly.map_assemble supplies read-after-assembly and fullness"
      - "ObjectAssembly.readAssembledIso supplies essential surjectivity"
      - "GraphCode.assemble_injective, assemble_read, and read_assemble instantiate the primitive application"
      - "readCompleteMapGraphs_injective instantiates the complete-geometry separation application"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the theorem is the general B reconstruction spine itself and preserves the separate AAT discharge obligation"
  vacuity: none-found
  vacuity_reason: "primitive graphs provide positive separation and a genuine category equivalence, while constant Bool-to-PUnit readings refute both ReadingSeparation and HomFamilySeparation"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Does explicit hom-level separation and assembly together with object assembly characterize a categorical equivalence with two-sided Hom inverses and object isomorphisms, and does the primitive Bool graph category realize the theorem while Cycle 64 complete geometry graphs realize the underlying indexed Hom-family separation contract for every package pair without a local graph category or assembly claim?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/LocalReconstructionEquivalence.lean: pass"
    - "#assert_standard_axioms_only LocalReconstructionEquivalence: 75 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "define a complete-geometry local Hom category with independent graph coherence equations and construct Hom assembly from them, then apply the functor-level reconstruction principle without using an image subtype or completed morphism certificate"
```

## Cycle 66: raw complete-graph category and faithful reading

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 66
status: result-proposed
branch: codex/4711-g124-complete-graph-category
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 900d73e14e70cacb37915602f3838bae46e75ac2
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 65 acceptance: Issue comment 5737528107; Cycle 66 selection: Issue comment 5737538633"
  proof_dag_predecessors:
    - "Cycle 63 primitive function-graph category"
    - "Cycle 64 complete geometry graph separation"
    - "Cycle 65 separation-and-assembly reconstruction equivalence"
  proof_obligation: "construct an independent category of raw complete graph bundles, lift complete geometry reading to a faithful underlying-package-preserving functor across every dependent component, discharge object assembly, and identify missing Hom assembly exactly with fullness"
  selection_reason: "this adds the missing functorial local Hom surface and an exact universal characterization of its remaining assembly gap in one cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphCategory.lean"
  risks:
    - "backward context graphs might compose in the wrong order"
    - "dependent tagged maps might fail functorial composition"
    - "the local category might be defined as a global image"
    - "faithfulness might be overstated as fullness"
  unchecked:
    - "independent coherence equations selecting assemblable raw graph bundles remain for the next cycle"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "All thirteen top-level fields receive identity and composition operations, with reversed order for contextBackward, and satisfy category laws; the primitive field delegates to its five graph codes. Complete geometry reading preserves identity and composition in every primitive and dependent tagged field, giving an underlying-package-preserving faithful functor. Object assembly is reflexive. Nonempty HomAssembly is proved equivalent to fullness, and any independently supplied HomAssembly produces the Cycle 65 reconstruction data and a categorical equivalence. Fullness itself is not asserted."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.ext"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.id"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.comp"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.id_comp"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.comp_id"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.CompleteMapGraphs.assoc"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readCompleteMapGraphs_id"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readCompleteMapGraphs_comp"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readingFunctor"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readingFunctorHomSeparation"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readingFunctorFaithful"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.readingFunctorObjectAssembly"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.reconstructionDataOfHomAssembly"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.nonempty_homAssembly_iff_full"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphCategory.equivalenceOfHomAssembly"
  evidence:
    - "CompleteMapGraphs.id_comp"
    - "CompleteMapGraphs.comp_id"
    - "CompleteMapGraphs.assoc"
    - "readCompleteMapGraphs_id"
    - "readCompleteMapGraphs_comp"
    - "readingFunctorHomSeparation"
    - "nonempty_homAssembly_iff_full"
  claim_mapping:
    theorem_names:
      - "CompleteMapGraphs.id_comp"
      - "CompleteMapGraphs.comp_id"
      - "CompleteMapGraphs.assoc"
      - "readCompleteMapGraphs_id"
      - "readCompleteMapGraphs_comp"
      - "readingFunctorHomSeparation"
      - "readingFunctorObjectAssembly"
      - "nonempty_homAssembly_iff_full"
      - "equivalenceOfHomAssembly"
    source_labels:
      - "Cycle 66 raw complete-graph category and reading functor toward G-124 target B"
      - "Cycle 66 fixed four-lane question"
    conjuncts:
      - "raw complete graph bundles form an independent category"
      - "contextBackward composition uses the reverse component order"
      - "complete geometry reading preserves all primitive and dependent components"
      - "the reading functor is faithful by Cycle 64 joint separation"
      - "object assembly is exact because objects retain the same package"
      - "the missing Hom assembly is equivalent to fullness"
      - "an independently proved Hom assembly upgrades reading to an equivalence"
    undischarged_assumptions:
      - "HomAssembly, equivalently fullness, remains an explicit premise of the conditional reconstruction data and equivalence"
    acceptance_point: "the raw local Hom category and faithful reading functor are constructed without global-image data, while the exact remaining fullness obligation is exposed rather than assumed"
    port_status: not-applicable
  nonclaims:
    - "the raw complete-graph reading functor is full"
    - "every raw complete graph bundle satisfies geometry coherence"
    - "every raw complete graph bundle assembles to a GeometryTotalHom"
    - "G-124 target B is fully discharged for all required families"
audits:
  premise_delta:
    discharged:
      - "raw local graph identity, composition, and category laws / componentwise GraphCode operations"
      - "reading functoriality / explicit identity and composition theorems for all thirteen fields"
      - "functor-level separation / readCompleteMapGraphs_injective"
      - "object assembly / package identity and reflexive isomorphism"
      - "assembly gap classification / Nonempty HomAssembly iff Full"
    remaining:
      - "independent coherence conditions and assembly for the coherent raw graph subcategory"
      - "object assembly beyond the underlying-package-preserving complete-geometry branch"
  certificate_provenance:
    discharged:
      - "local category / raw GraphCode data and total-functional laws only"
      - "faithfulness / accepted Cycle 64 injectivity theorem"
    unresolved:
      - "conditional equivalence / explicit HomAssembly argument is not constructed in this cycle"
      - "fullness / deliberately not supplied in this cycle"
  proof_use:
    used:
      - "GraphCode assemble injectivity proves all componentwise category laws"
      - "dependent tagged map definitions are unfolded in readCompleteMapGraphs_comp"
      - "Cycle 64 injectivity supplies functor faithfulness"
      - "Cycle 65 ReconstructionData supplies the conditional equivalence"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the cycle constructs the B local Hom category and functorial reading surface while preserving the independent assembly obligation"
  vacuity: none-found
  vacuity_reason: "the raw category contains every total-functional component bundle, not only the image of global morphisms"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do raw complete graph bundles form an independent componentwise category, does complete geometry reading define a faithful underlying-package-preserving functor into it across all dependent tagged components, and is its missing fullness exactly the Hom-assembly obligation required by Cycle 65 without asserting it?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphCategory.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryGraphCategory: 38 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "define independent geometry coherence equations closed under identity and composition, form the coherent graph subcategory, and assemble every coherent graph into a GeometryTotalHom"
```

## Cycle 67: independent algebraic graph coherence

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 67
status: result-proposed
branch: codex/4711-g124-algebraic-graph-coherence
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 197978ad348f382755e889e0400124f80a507103
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 66 acceptance: Issue comment 5737842870; Cycle 67 selection: Issue comment 5737857578"
  proof_dag_predecessors:
    - "Cycle 63 primitive function-graph read/assemble equivalence"
    - "Cycle 64 complete geometry graph separation"
    - "Cycle 66 raw complete-graph category and faithful reading"
  proof_obligation: "construct independent graph-code presentations of equivalences and ring homomorphisms, prove two-sided read/assemble equivalences and composition closure, and connect them immediately to the algebraic components of complete geometry reading"
  selection_reason: "this discharges a reusable nontrivial coherence-and-assembly layer rather than ending at definitions or postponing the complete-geometry connection"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/AlgebraicGraphCoherence.lean"
  risks:
    - "a local code might store the completed Equiv or RingHom"
    - "the backward graph might compose in the forward order"
    - "preservation proofs might be asserted without read/assemble inverses"
    - "the complete-geometry connection might omit one selected algebraic component"
  unchecked:
    - "dependent fiber equivalences and geometry naturality remain for later cycles"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "EquivGraphData and RingHomGraphData keep raw graphs separate from the Prop-valued IsEquivGraphCode and IsRingHomGraphCode laws; their bundled codes are explicitly equivalent to Equiv and RingHom by two-sided read/assemble laws. Positive and negative fixtures show both predicates are substantive. Both presentations have identity, composition, the three category equations, and assembly formulas; equivalence backward graphs compose in reverse order. SelectedAlgebraicData is likewise separate from IsSelectedAlgebraicallyCoherent, and complete geometry reading supplies a positive identity fixture while assembly recovers the pointed Atom, upper Atom, equation-index, coefficient, and both context-object functions."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphData"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.IsEquivGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.equivEquiv"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.assemble_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.assemble_symm_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.comp_forward"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.comp_backward"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.EquivGraphCode.boolConstantData_not_isEquivGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphData"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.IsRingHomGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode.equivRingHom"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode.assemble_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.RingHomGraphCode.natSuccData_not_isRingHomGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicData"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.IsSelectedAlgebraicallyCoherent"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicCoherence"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.pointedAtomEquiv_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.atomEquiv_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.equationEquiv_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.coefficientHom_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.contextForward_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.contextBackward_read"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.pointedAtomEquiv_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.atomEquiv_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.equationEquiv_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.coefficientHom_apply"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.identitySelectedAlgebraicData_isCoherent"
    - "AAT.AG.LocalSemanticReconstruction.AlgebraicGraphCoherence.SelectedAlgebraicallyCoherentCompleteMapGraphs.coefficientZeroSelectedAlgebraicData_not_isCoherent"
  evidence:
    - "EquivGraphCode.read_assemble"
    - "EquivGraphCode.assemble_read"
    - "EquivGraphCode.comp_forward"
    - "EquivGraphCode.comp_backward"
    - "RingHomGraphCode.read_assemble"
    - "RingHomGraphCode.assemble_read"
    - "RingHomGraphCode.comp_graph"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.pointedAtomEquiv_read"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.atomEquiv_read"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.equationEquiv_read"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.coefficientHom_read"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.contextForward_read"
    - "SelectedAlgebraicallyCoherentCompleteMapGraphs.contextBackward_read"
  claim_mapping:
    theorem_names:
      - "EquivGraphCode.equivEquiv"
      - "EquivGraphCode.comp_forward"
      - "EquivGraphCode.comp_backward"
      - "EquivGraphCode.id_comp"
      - "EquivGraphCode.comp_id"
      - "EquivGraphCode.assoc"
      - "RingHomGraphCode.equivRingHom"
      - "RingHomGraphCode.comp_graph"
      - "RingHomGraphCode.id_comp"
      - "RingHomGraphCode.comp_id"
      - "RingHomGraphCode.assoc"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.pointedAtomEquiv_read"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.atomEquiv_read"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.equationEquiv_read"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.coefficientHom_read"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.contextForward_read"
      - "SelectedAlgebraicallyCoherentCompleteMapGraphs.contextBackward_read"
    source_labels:
      - "Cycle 67 independent algebraic graph coherence toward G-124 target B"
      - "Cycle 67 fixed four-lane question"
    conjuncts:
      - "mutually inverse graph codes assemble exactly to equivalences"
      - "operation-preserving graph codes assemble exactly to ring homomorphisms"
      - "both assemblies have explicit two-sided readback"
      - "identity and composition remain inside both local presentations"
      - "backward equivalence graphs compose in reverse order"
      - "complete geometry reading supplies the selected independent coherence"
      - "assembled algebraic components recover the original completed component maps"
    material_premises:
      source_derived:
        - "G-124(B) equivalence assembly requires mutual-inverse equations on the independently supplied forward/backward graphs"
        - "G-124(B) ring-hom assembly requires zero, one, addition, and multiplication preservation equations on the independently supplied graph"
      discharged:
        - "actual equivalence and ring-hom readings supply these laws, and both read/assemble composites are proved equal to identity"
        - "complete geometry reading supplies the selected laws from its actual component equivalences and coefficient homomorphism"
      undischarged: []
    undischarged_assumptions: []
    acceptance_point: "the algebraic coherence layer is defined without completed maps and has exact two-sided assembly before being connected to complete geometry reading"
    port_status: not-applicable
  nonclaims:
    - "a complete context category equivalence is assembled from object graphs alone"
    - "dependent equation-observable or coordinate fiber equivalences are assembled"
    - "operation, invariant, signature, support, axis, or observable naturality is discharged"
    - "an arbitrary algebraically coherent bundle assembles to GeometryTotalHom"
    - "the Cycle 66 reading functor is full"
audits:
  premise_delta:
    source_derived:
      - "generic equivalence graph assembly assumes the fixed-question mutual-inverse equations"
      - "generic ring-hom graph assembly assumes the fixed-question four operation-preservation equations"
    discharged:
      - "algebraic read/assemble / explicit left and right inverse laws"
      - "algebraic composition / ordinary forward order and reverse backward order"
      - "complete geometry selected algebraic components / explicit recovery theorems"
      - "predicate non-vacuity / positive and negative component fixtures plus combined identity and constant-zero-coefficient fixtures"
    remaining:
      - "dependent fiber equivalences and their tagged-map coherence"
      - "context functor action on morphisms and categorical unit/counit"
      - "operation, invariant, signature, support, axis, observable, and raw naturality"
      - "complete coherent subcategory and GeometryTotalHom assembly"
  certificate_provenance:
    discharged:
      - "EquivGraphCode / graph codes and mutual-inverse function equations only"
      - "RingHomGraphCode / graph code and four operation equations only"
      - "complete algebraic coherence / inverse graph codes and equations only"
    unresolved:
      - "full complete-geometry certificate / not constructed in this cycle"
  proof_use:
    used:
      - "Cycle 63 graph read/assemble inverses prove both algebraic code equivalences"
      - "assembled algebraic equality proves identity and composition laws"
      - "actual complete geometry component maps populate the independent equations"
      - "component recovery theorems unfold the graph read/assemble laws"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the cycle replaces selected completed algebraic fields by independently stated local graph equations and proves exact assembly, while leaving the rest of B explicit"
  vacuity: none-found
  vacuity_reason: "both local code types are explicitly equivalent to the full corresponding algebraic map types and are not restricted to maps arising from geometry morphisms"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do independent paired graph codes with mutual-inverse laws assemble equivalently to actual equivalences, do operation-preserving graph codes assemble equivalently to ring homomorphisms, and does complete geometry reading populate and recover its pointed-Atom, upper-Atom, context-object, equation-index, and coefficient components without storing any completed geometry morphism?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/AlgebraicGraphCoherence.lean: pass"
    - "#assert_standard_axioms_only AlgebraicGraphCoherence: 175 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "define independent dependent-fiber, context-functor, operation, invariant, signature, and geometry-naturality coherence closed under identity and composition, then assemble the complete coherent Hom"
```

## Cycle 68: dependent algebraic graph coherence

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 68
status: result-proposed
branch: codex/4711-g124-dependent-algebraic-coherence
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: a507237a507df44914136a6f768b94173bf933ca
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 67 acceptance: Issue comment 5738212052; Cycle 68 selection: Issue comment 5738223719"
  proof_dag_predecessors:
    - "Cycle 63 primitive function-graph read/assemble equivalence"
    - "Cycle 64 complete geometry graph separation"
    - "Cycle 67 ordinary equivalence and ring-hom graph coherence"
  proof_obligation: "construct an independent graph presentation of ring equivalences, lift ordinary and ring equivalence codes pointwise over arbitrary index maps, prove two-sided assembly, composition, and tagged-forward separation, and connect both families immediately to complete geometry coordinate and equation-observable reading"
  selection_reason: "this combines a new algebraic two-sided assembly, dependent-family universal equivalences, separation, composition, and actual complete-geometry connections in one auditable cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/DependentAlgebraicGraphCoherence.lean"
  risks:
    - "ring-equivalence data might retain a completed RingEquiv"
    - "fiber-family recovery might prove only one direction"
    - "tagged separation might lose dependent fiber values"
    - "the complete-geometry connection might be deferred to a later wrapper"
  unchecked:
    - "context-functor morphism action and remaining naturality are later obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "RingEquivGraphData separates two raw ring-hom graphs from IsRingEquivGraphCode, which contains both operation-preservation certificates and mutual-inverse equations; its bundled code is explicitly equivalent to RingEquiv and has identity/composition. IndexedEquivGraphCode and IndexedRingEquivGraphCode are explicitly equivalent to pointwise completed families over arbitrary index functions, are closed under dependent composition, expose compositional tagged forward functions, and are separated by their tagged Bool graphs. Complete geometry coordinate and equation-observable families are read into these independent codes; pointwise assembly recovers the actual families and their tagged graphs are literally the corresponding CompleteMapGraphs fields."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.RingEquivGraphData"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IsRingEquivGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.RingEquivGraphCode.equivRingEquiv"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.RingEquivGraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.RingEquivGraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.RingEquivGraphCode.natPairDiagonalData_not_isRingEquivGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedEquivGraphCode.equivFamily"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedEquivGraphCode.taggedForward_injective"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedEquivGraphCode.taggedFunction_comp"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.equivFamily"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.taggedForward_injective"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.taggedFunction_comp"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.CompleteGeometryDependentAlgebraicCode.coordinate_assemble"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.CompleteGeometryDependentAlgebraicCode.coordinate_taggedForward"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.CompleteGeometryDependentAlgebraicCode.equationObservable_assemble"
    - "AAT.AG.LocalSemanticReconstruction.DependentAlgebraicGraphCoherence.CompleteGeometryDependentAlgebraicCode.equationObservable_taggedForward"
  evidence:
    - "RingEquivGraphCode.equivRingEquiv"
    - "RingEquivGraphCode.natPairIdentityData_isRingEquivGraphCode"
    - "RingEquivGraphCode.natPairDiagonalData_not_isRingEquivGraphCode"
    - "IndexedEquivGraphCode.equivFamily"
    - "IndexedEquivGraphCode.taggedForward_injective"
    - "IndexedRingEquivGraphCode.equivFamily"
    - "IndexedRingEquivGraphCode.taggedForward_injective"
    - "CompleteGeometryDependentAlgebraicCode.coordinate_taggedForward"
    - "CompleteGeometryDependentAlgebraicCode.equationObservable_taggedForward"
  claim_mapping:
    theorem_names:
      - "RingEquivGraphCode.equivRingEquiv"
      - "RingEquivGraphCode.assemble_comp"
      - "IndexedEquivGraphCode.equivFamily"
      - "IndexedEquivGraphCode.taggedForward_injective"
      - "IndexedEquivGraphCode.taggedFunction_comp"
      - "IndexedRingEquivGraphCode.equivFamily"
      - "IndexedRingEquivGraphCode.taggedForward_injective"
      - "IndexedRingEquivGraphCode.taggedFunction_comp"
      - "CompleteGeometryDependentAlgebraicCode.coordinate_assemble"
      - "CompleteGeometryDependentAlgebraicCode.coordinate_taggedForward"
      - "CompleteGeometryDependentAlgebraicCode.equationObservable_assemble"
      - "CompleteGeometryDependentAlgebraicCode.equationObservable_taggedForward"
    source_labels:
      - "Cycle 68 dependent algebraic graph coherence toward G-124 target B"
      - "Cycle 68 fixed four-lane question"
    conjuncts:
      - "bidirectional operation-preserving graphs assemble exactly to ring equivalences"
      - "ordinary and ring equivalence graph families have pointwise two-sided readback"
      - "tagged forward graphs separate both dependent code families"
      - "dependent composition agrees with composition of tagged functions"
      - "coordinate and equation-observable families recover actual complete geometry components"
    material_premises:
      source_derived:
        - "G-124(B) ring-equivalence assembly requires operation laws in both directions and mutual-inverse equations"
        - "G-124(B) dependent assembly fixes the index function and supplies one coherent equivalence code per source index"
      discharged:
        - "actual RingEquiv reading supplies both ring-hom laws and inverse equations, with both read/assemble composites proved"
        - "actual coordinate and observable families supply pointwise codes whose assembly and tagged graphs are recovered"
      undischarged: []
    undischarged_assumptions: []
    acceptance_point: "dependent algebraic families are independently graph-presented, jointly separated by tagged readings, composition-compatible, and connected to actual complete geometry fields"
    port_status: not-applicable
  nonclaims:
    - "the context category equivalence is assembled from object graphs alone"
    - "observable restriction naturality or coordinate compatibility is assembled"
    - "operation, invariant, support, geometry-axis, or geometry-observable coherence is discharged"
    - "an arbitrary complete coherent bundle assembles to GeometryTotalHom"
    - "G-124 target B or the whole GOAL is complete"
audits:
  premise_delta:
    source_derived:
      - "generic ring-equivalence graph assembly assumes the fixed-question bidirectional operation and inverse equations"
      - "generic indexed assembly assumes a fixed index map and a graph code at every source index"
    discharged:
      - "ring-equivalence read/assemble / explicit left and right inverse laws"
      - "dependent-family read/assemble / explicit pointwise left and right inverse laws"
      - "dependent-family separation / tagged graph equality recovers every fiber code"
      - "dependent composition / tagged functions compose over composed index maps"
      - "complete geometry coordinates and equation observables / pointwise and tagged recovery"
      - "predicate non-vacuity / identity and noninvertible diagonal fixtures"
    remaining:
      - "context functor morphism action and unit/counit"
      - "equation-observable restriction naturality and coordinate compatibility"
      - "operation, invariant, support, axis, observable, and raw naturality"
      - "complete coherent subcategory and GeometryTotalHom assembly"
  certificate_provenance:
    discharged:
      - "RingEquivGraphCode / two raw ring-hom graphs plus separate equations only"
      - "indexed codes / pointwise independent graph codes only"
      - "tagged graphs / derived from assembled pointwise codes"
    unresolved:
      - "full complete-geometry certificate / not constructed in this cycle"
  proof_use:
    used:
      - "Cycle 67 ring-hom and equivalence graph inverses build ring and indexed equivalence assembly"
      - "sigma equality of tagged outputs recovers each dependent fiber output"
      - "actual complete geometry coordinateEquiv and observableEquiv populate the independent codes"
      - "Cycle 64 complete graph fields identify the same tagged forward graphs"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the cycle adds independent dependent algebraic coherence and exact assembly without retaining completed families, while leaving naturality and complete Hom assembly explicit"
  vacuity: none-found
  vacuity_reason: "ring-equivalence coherence has positive and negative raw fixtures, and both indexed code types are equivalent to arbitrary pointwise completed families rather than geometry-image subtypes"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do operation-preserving forward/backward graph codes with mutual-inverse laws assemble equivalently to actual ring equivalences, and do indexed equivalence and ring-equivalence graph families assemble pointwise, remain separated by their tagged forward graphs, and recover complete geometry coordinate and equation-observable families without storing completed family maps?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/DependentAlgebraicGraphCoherence.lean: pass"
    - "#assert_standard_axioms_only DependentAlgebraicGraphCoherence: 83 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "add independent context-functor morphism action and the remaining operation, invariant, support, axis, observable, and raw naturality laws; then assemble the complete coherent Hom"
```

## Cycle 69: thin-context and observable naturality coherence

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 69
status: result-proposed
branch: codex/4711-g124-context-observable-coherence
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: b0a2d4b2690a1aabdf64f033c9fc6ca975f7445e
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 68 acceptance: Issue comment 5738448890; Cycle 69 selection: Issue comment 5738459322"
  proof_dag_predecessors:
    - "Cycle 63 primitive total-functional graph equivalence"
    - "Cycle 64 complete geometry context and observable graph reading"
    - "Cycle 68 indexed ring-equivalence graph coherence"
  proof_obligation: "assemble bidirectional context-object graphs, thin morphism preservation, and unit/counit inequalities into an actual context-category equivalence with two-sided readback; assemble indexed observable ring graphs plus restriction naturality into a presheaf natural isomorphism; connect both results to complete geometry"
  selection_reason: "this combines a new category-level two-sided assembly, unit/counit, identity/composition closure, observable naturality assembly, and both complete-geometry connections in one auditable cycle"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/ContextObservableGraphCoherence.lean"
  risks:
    - "literal object equality might incorrectly replace isomorphism in a preorder category"
    - "a completed functor, equivalence, or natural isomorphism might be retained in the code"
    - "observable components might be assembled without restriction naturality"
    - "complete-geometry connection might be deferred"
  unchecked:
    - "remaining operation, invariant, geometry-family, and raw naturality laws are later obligations"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "ThinEquivalenceGraphData stores only forward/backward Bool graphs. IsThinEquivalenceGraphCode separately requires total-functionality, monotonicity, and both directions of unit/counit inequalities. ThinEquivalenceGraphCode assembles the two functors and natural isomorphisms, is explicitly equivalent to actual preorder-category equivalences, and proves componentwise graph composition, unit laws, and associativity. ContextObservableGraphCode binds indexed observable ring graphs and restriction naturality to the forward functor assembled from its own context code, then assembles the presheaf natural isomorphism. Actual equation transport and complete geometry reading recover the joint context equivalence, both complete context graph fields, every observable component, and the existing observable presheaf iso."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphData"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.IsThinEquivalenceGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.equivEquivalence"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.assemble_comp"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.comp_forward"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.comp_backward"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.id_comp"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.comp_id"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ThinEquivalenceGraphCode.assoc"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.boolConstantData_not_isThinEquivalenceGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.boolIntPairFamily_not_restrictionNatural"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ObservablePresheafGraphCode.assembleIso"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ContextObservableGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.ContextObservableGraphCode.read_observable_assembleIso"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.CompleteGeometryContextObservableCode.context_forward_graph"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.CompleteGeometryContextObservableCode.context_backward_graph"
    - "AAT.AG.LocalSemanticReconstruction.ContextObservableGraphCoherence.CompleteGeometryContextObservableCode.observable_assembleIso"
  acceptance:
    fixed_question: "Do bidirectional total-functional context-object graphs that preserve thin morphisms and carry both directions of the unit and counit inequalities assemble equivalently to actual context-category equivalences, including functorial morphism action, and can the observable ring-family compatibility assemble into and recover the actual presheaf natural isomorphism without storing the completed equivalence or natural isomorphism?"
    statement_status: implemented
    proof_status: focused-pass
    premise_status:
      discharged:
        - "context graphs / exact read-assemble equivalence with actual category equivalences"
        - "thin morphism preservation / forward and backward functor actions"
        - "unit and counit / natural isomorphisms assembled from both local inequalities"
        - "observable restriction compatibility / natural iso assembly and actual iso recovery"
        - "complete geometry connection / context forward/backward graph fields and observable presheaf iso"
        - "predicate non-vacuity / Boolean identity, constant-forward context failure, and non-natural integer-product ring family"
      undischarged: []
    undischarged_assumptions: []
    acceptance_point: "thin context equivalence is graph-presented with two-sided readback and composition; observable restriction naturality is bound to the assembled context functor, assembles a natural iso, recovers the actual iso, and both parts connect to actual complete geometry"
    port_status: not-applicable
  nonclaims:
    - "operation, invariant, support, geometry-axis, or geometry-observable naturality is discharged"
    - "raw restriction-system naturality is discharged"
    - "an arbitrary complete coherent bundle assembles to GeometryTotalHom"
    - "G-124 target B or the whole GOAL is complete"
audits:
  premise_delta:
    source_derived:
      - "generic context assembly assumes total-functional graphs, monotonicity, and both unit/counit inequalities"
      - "generic observable assembly assumes indexed ring-equivalence codes and explicit restriction naturality"
    discharged:
      - "context equivalence read/assemble / explicit left and right inverse laws"
      - "functorial morphism action and unit/counit natural isomorphisms"
      - "observable presheaf natural isomorphism assembly and actual recovery"
      - "complete geometry forward/backward context graph recovery"
      - "context positive and negative fixtures; observable positive instances from actual transport and a non-natural negative fixture"
    remaining:
      - "operation and invariant coherence"
      - "support, axis, geometry-observable, and raw naturality"
      - "complete coherent subcategory and GeometryTotalHom assembly"
  certificate_provenance:
    discharged:
      - "ThinEquivalenceGraphCode / two raw graphs plus separate preorder equations only"
      - "ContextObservableGraphCode / context graphs plus indexed ring graphs bound to the assembled forward functor and a separate restriction equation"
    unresolved:
      - "full complete-geometry certificate / not constructed in this cycle"
  proof_use:
    used:
      - "total-functional graph assembly supplies both object functions"
      - "monotonicity supplies the two functor map actions"
      - "four local preorder inequalities supply unit and counit isomorphisms"
      - "observable restriction equations supply naturality of assembled components"
      - "actual complete geometry context equivalence and observable transport populate both readings"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the joint code derives its context functor from its own raw graphs; completed equivalences and natural isomorphisms are outputs, while the actual complete geometry connection is proved in the same module"
  vacuity: none-found
  vacuity_reason: "the Boolean constant-forward fixture fails the inverse counit inequality, and a pointwise integer-product ring-equivalence family fails restriction naturality; actual transport supplies positive instances"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do bidirectional total-functional context-object graphs that preserve thin morphisms and carry both directions of the unit and counit inequalities assemble equivalently to actual context-category equivalences, including functorial morphism action, and can the observable ring-family compatibility assemble into and recover the actual presheaf natural isomorphism without storing the completed equivalence or natural isomorphism?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/ContextObservableGraphCoherence.lean: pass"
    - "#assert_standard_axioms_only ContextObservableGraphCoherence: 114 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "assemble operation, invariant, support, axis, geometry-observable, and raw naturality coherence with identity/composition, connect all actual fields, then construct the complete coherent Hom"
```

## Cycle 70: remaining dependent component graph coherence

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 70
status: result-proposed
branch: codex/4711-g124-complete-component-coherence
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 871eb6dc7e7ad8abda857aef261b1f2e4131eb26
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 69 acceptance: Issue comment 5738871900; Cycle 70 selection: Issue comment 5738881990"
  proof_dag_predecessors:
    - "Cycle 63 primitive total-functional graph equivalence"
    - "Cycle 64 complete geometry graph reading and separation"
    - "Cycle 68 dependent equivalence graph families"
    - "Cycle 69 context equivalence and observable naturality coherence"
  proof_obligation: "assemble operation, invariant, signature, realization, and raw-transport graph codes with local laws, substantive inverses and separation, identity/composition closure, and same-cycle complete-map graph recovery"
  selection_reason: "the cycle closes all remaining computational fields below complete Hom assembly while keeping the four-lane question to one componentwise coherence claim"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/RemainingComponentGraphCoherence.lean"
  risks:
    - "dependent signature coordinates might hide a completed axis map through casts"
    - "realization naturality might be stated pointwise without identity/composition closure"
    - "a GeometryTotalHom might be stored inside the unified code"
    - "common complete-map graph recovery might be deferred"
  unchecked:
    - "assembly of the full coherent Hom including coverage and overlap"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "One-index and two-index total-functional graph families now have exact read/assemble equivalences, tagged separation, no-unfold evaluation APIs, and identity/composition laws. Lawful operation and invariant codes compose from their own local laws. RealizationGraphCode is equivalent to RealizationTransportSupply and has law-bearing identity/composition. SignatureGraphCode is exactly equivalent to SignatureTransportSupply and has identity/composition. Raw coherence composes from two independent endpoint equalities, without reading a GeometryTotalHom. RemainingComponentCode is exactly equivalent to its completed local supply and has componentwise identity/composition relative to the explicit ambient PackageTotalHom and coefficient map. It stores no GeometryTotalHom. CompleteGraphRecovery recovers operation, invariant, signature axis/coordinate, support, geometry axis, and geometry observable fields on the existing complete-map graph surface. Reviewed finite packages provide closed positive and negative instances for every new law certificate and for CompleteGraphRecovery."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.IndexedFunctionGraphCode.equivFamily"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.IndexedFunctionGraphCode.taggedFunction_apply"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.IndexedFunctionGraphCode.taggedForward_injective"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.equivFamily"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.taggedFunction_apply"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.BiIndexedFunctionGraphCode.taggedForward_injective"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.RealizationGraphCode.equivSupply"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.RealizationGraphCode.assemble_comp"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.SignatureGraphCode.equivSupply"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.LawfulOperationGraphCode.comp"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.LawfulInvariantGraphCode.comp"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.equivSupply"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.RemainingComponentCode.comp"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.readRemaining_completeGraphRecovery"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.operation_not_natural"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.invariant_not_transported"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.realization_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.signature_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.rawTransport_not_coherent"
    - "AAT.AG.LocalSemanticReconstruction.RemainingComponentGraphCoherence.CompleteGeometryRemainingComponentCode.ConcreteNegativeFixtures.completeGraphRecovery_not_for_alternate"
  acceptance:
    fixed_question: "Do raw graph codes for the remaining operation, invariant, signature, support, geometry-axis, geometry-observable, and raw-transport components, equipped only with endpoint equations and preservation/naturality laws, assemble componentwise with identity/composition and recover every corresponding field of actual complete geometry morphisms without storing a GeometryTotalHom?"
    statement_status: implemented
    proof_status: focused-pass
    premise_status:
      discharged:
        - "one-index and two-index dependent function families / exact read-assemble equivalences"
        - "dependent family separation / tagged forward graphs"
        - "operation naturality and invariant transport / independent law predicates"
        - "support, axis, and observable realization / supply equivalence plus identity and composition"
        - "signature axis and coordinates / dependent recovery over the assembled axis"
        - "raw transport / actual, identity, and composition coherence"
        - "unified relative code / exact supply equivalence and componentwise identity/composition"
        - "common surface / all remaining graph-valued fields recovered together"
        - "instance-pair audit / closed finite failures for every new law certificate and CompleteGraphRecovery"
      undischarged: []
    undischarged_assumptions: []
    acceptance_point: "all remaining computational fields below complete Hom assembly are graph-presented, law-bearing, composition-compatible where applicable, and recovered on the accepted common graph surface"
    port_status: not-applicable
  nonclaims:
    - "the ambient PackageTotalHom is reconstructed from Cycle 67 and Cycle 69 independent graph codes in this cycle"
    - "an arbitrary unified remaining-component code already assembles coverage and overlap"
    - "an arbitrary complete coherent bundle already assembles to GeometryTotalHom"
    - "G-124 target B or the whole GOAL is complete"
audits:
  premise_delta:
    source_derived:
      - "generic graph assembly assumes primitive total-functionality and explicit local preservation or naturality laws"
      - "the relative unified API is indexed by the existing G-101 PackageTotalHom because realization and rawTransport are defined over that API; replacing this ambient index by independent core assembly remains explicit"
    discharged:
      - "dependent read/assemble inverses and tagged separation"
      - "law-bearing realization supply equivalence and composition"
      - "law-bearing operation, invariant, and signature composition"
      - "signature and unified relative-code read/assemble inverses"
      - "raw composition from two independent endpoint equations"
      - "actual complete-map graph recovery for every remaining computational field"
    remaining:
      - "full complete coherent Hom assembly with coverage and overlap"
      - "replacement of the ambient PackageTotalHom index by assembly from Cycle 67 and Cycle 69 codes"
  certificate_provenance:
    discharged:
      - "RemainingComponentCode / raw graph codes plus separate local laws only"
    unresolved:
      - "full GeometryTotalHom assembly / successor obligation"
  proof_use:
    used:
      - "primitive graph read/assemble laws build dependent family equivalences"
      - "tagged sigma evaluation proves family separation"
      - "reading and naturality premises build RealizationTransportSupply"
      - "axis equality reindexes coordinate graph assembly"
      - "actual complete geometry laws populate operation, invariant, signature, realization, and raw components"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "the unified relative code contains no completed GeometryTotalHom; its PackageTotalHom index is explicitly classified as an inherited ambient API rather than claimed as independently reconstructed, and common graph recovery is proved in the same cycle"
  vacuity: none-found
  vacuity_reason: "the generic family codes are equivalent to arbitrary dependent functions, tagged graphs are injective, realization/signature/unified codes have exact supply equivalences, and reviewed finite packages give closed negative instances for operation naturality, invariant transport, realization, signature, raw transport, and the seven-field CompleteGraphRecovery certificate"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Do raw graph codes for the remaining operation, invariant, signature, support, geometry-axis, geometry-observable, and raw-transport components, equipped only with endpoint equations and preservation/naturality laws, assemble componentwise with identity/composition and recover every corresponding field of actual complete geometry morphisms without storing a GeometryTotalHom?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/RemainingComponentGraphCoherence.lean: pass"
    - "#assert_standard_axioms_only RemainingComponentGraphCoherence: 280 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "replace the relative ambient PackageTotalHom with assembly from Cycle 67 and Cycle 69 independent codes, combine coverage and overlap, and prove GeometryTotalHom read/assemble inverses"
```

## Cycle 71: complete geometry graph assembly

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 71
status: result-proposed
branch: codex/4711-g124-full-geometry-graph-assembly
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: c2e27b52fe60586579190af1267014d49cb65376
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 70 acceptance: Issue comment 5739475931; Cycle 71 selection: Issue comment 5739492817"
  proof_dag_predecessors:
    - "Cycle 67 independent equivalence and ring-hom graph coherence"
    - "Cycle 69 context equivalence and observable naturality coherence"
    - "Cycle 70 remaining-component graph coherence"
    - "Cycle 64 common complete-map graph separation"
  proof_obligation: "assemble the complete package and geometry Hom from independent graph codes plus local coverage and overlap, prove exact two-sided recovery and separation, and connect the result to the accepted common graph surface in the same cycle"
  selection_reason: "this closes the inherited PackageTotalHom index and the complete Hom assembly together, rather than splitting assembly, inverse laws, and common-surface integration across small cycles"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphAssembly.lean"
  risks:
    - "a PackageTotalHom or GeometryTotalHom might be retained inside the independent code"
    - "dependent coordinate and realization fields might recover only after an untracked cast"
    - "coverage or overlap might be silently inferred rather than explicit local input"
    - "the new code might not be separated by the accepted common graph reading"
  unchecked:
    - "identity and composition laws for the complete independent code category"
    - "object assembly and the final four-family local-model equivalence"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "PackageGraphData reuses the law-bearing graph-code APIs of Cycles 67, 69, and 70, whose own raw data and certificates are already separated; IsPackageGraphCode contains only the new Cycle 71 cross-component laws. Their subtype constructs configuration morphisms, EquationSystemExactTransport, and PackageTotalHom with exact read/assemble inverses. CompleteGeometryGraphData likewise reuses lawful package, coefficient, and realization codes, while IsCompleteGeometryGraphCode separates the outer coverage preservation, two overlap order comparisons, and raw coherence. Assembly constructs the thin-category overlap isomorphism and GeometryTotalHom. Neither code retains a completed computational submorphism, overlap isomorphism, or Hom, nor assumes that the whole input is a canonical reader image. Both complete-code inverse laws, assembly injectivity, concrete rejected package and complete certificates, and the readCompleteMapGraphs connection are proved in this cycle. Generation of predecessor or outer supplied laws is not claimed."
  completion_candidate: no
  lean_artifacts:
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.PackageGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.PackageGraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.PackageGraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.assembleOverlap"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphData"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.IsCompleteGeometryGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.assemble_read"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.read_assemble"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.equivGeometryTotalHom"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.assemble_injective"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.completeMapGraphs_read"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.completeMapGraphs_injective"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.PackageGraphNegativeFixture.not_isPackageGraphCode_mismatchedPointed"
    - "AAT.AG.LocalSemanticReconstruction.CompleteGeometryGraphAssembly.CompleteGeometryGraphCode.CompleteGraphCertificateFixtures.not_isCompleteGeometryGraphCode_incoherentData"
  acceptance:
    fixed_question: "Given law-bearing predecessor graph codes and the supplied cross-component package, coverage, overlap, and raw-coherence laws, do their computational maps assemble package and geometry transports with exact two-sided recovery and common-surface separation, without retaining completed computational substructures or assuming canonical-reader membership?"
    statement_status: implemented
    proof_status: focused-pass
    premise_status:
      discharged:
        - "ambient package Hom / assembled from independent package graph data and local laws"
        - "equation transport / assembled from independent equation, context, and observable graph data plus local laws"
        - "configuration morphisms / constructed from the Atom graph and object-configuration equation"
        - "overlap isomorphism / assembled from the two order comparisons in the thin context category with exact two-sided recovery"
        - "complete geometry Hom / assembled from package code, coefficient and realization graphs, raw coherence, coverage, and overlap"
        - "dependent base transport / exact read-assemble and assemble-read laws"
        - "code separation / injectivity of complete assembly"
        - "common surface / immediate readCompleteMapGraphs recovery and injectivity"
      undischarged:
        - "local-law generation / package, coefficient, realization, coverage, overlap, and raw-coherence laws remain supplied premises"
    undischarged_assumptions:
      - "GraphCode.row_existsUnique / source, object, invariant, signature-axis, and each indexed operation/support/axis/observable graph / supplies the decoded functions used by lower, upper, and realization assembly"
      - "EquivGraphCode forward.row_existsUnique, backward.row_existsUnique, left_inv, right_inv / pointed Atom, upper Atom, equation index, and each signature-coordinate family / supplies the assembled equivalences and their inverses"
      - "RingHomGraphCode graph.row_existsUnique, map_zero, map_one, map_add, map_mul / every equation-observable direction and the coefficient graph / supplies ring maps used by equation and geometry assembly"
      - "IsThinEquivalenceGraphCode.forward_total, backward_total, forward_mono, backward_mono, unit_hom, unit_inv, counit_hom, counit_inv / context code / supplies both functors and unit/counit isomorphisms"
      - "IsRingEquivGraphCode.forward_isRingHom and backward_isRingHom, each containing graph.row_existsUnique, map_zero, map_one, map_add, map_mul; plus left_inv and right_inv / each observable fiber / supplies the observable ring equivalence"
      - "IsObservablePresheafGraphCode.observable_naturality / observable family / supplies the presheaf natural isomorphism in equationTransport"
      - "IsSignatureGraphCode.axis_selected_iff and coordinate_eq / signature code / used directly by upper; no duplicate outer premise remains"
      - "IsPackageGraphCode.equation_role_eq, violationCoordinate_eq, equationResidual_eq / package cross-component predicate / used by equationTransport"
      - "IsPackageGraphCode.normalize_eq, extraction_iff, source_eq / package cross-component predicate / used by lower"
      - "IsPackageGraphCode.atom_eq, extraction_eq, composition_eq, object_formation_eq, configuration_eq, detectorCode_eq / package cross-component predicate / used by upper and assembled package agreement"
      - "IsPackageGraphCode.operation_naturality and invariant_transport / package cross-component predicate / used by upper"
      - "IsRealizationGraphCode.supportReads, axisReads, observableReads / realization code / used by geometry support, axis, and observable reading fields"
      - "IsRealizationGraphCode.support_naturality, axis_naturality, observable_naturality / realization code / used by geometry naturality fields"
      - "CoverageTransport.requiredSupport, requiredEquationCoordinate, selectedViolationWitness, requiredAxis / coverage certificate / copied to the assembled geometry coverage field"
      - "CoverageTransport.supportVisibleOn, equationCoordinateVisibleOn, violationWitnessVisibleOn, axisReadableOn, boundaryVisibleOn / coverage certificate / copied to the assembled geometry coverage field"
      - "IsCompleteGeometryGraphCode.overlapForward and overlapBackward / outer complete predicate / construct the overlap isomorphism through homOfLE"
      - "IsCompleteGeometryGraphCode.rawCoherent / outer complete predicate / used as the assembled geometry raw_eq field"
    acceptance_point: "relative to all listed predecessor and cross-component laws, independent complete graph codes and actual GeometryTotalHom values are equivalent, and the accepted common graph surface separates those codes"
    port_status: not-applicable
  nonclaims:
    - "complete graph codes already carry direct identity and composition operations"
    - "the Hom equivalence is already packaged as a category equivalence"
    - "fixed target B object assembly or the four-family local-model equivalence is complete"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    source_derived:
      - "package, coefficient, realization, coverage, overlap, and raw-coherence laws remain supplied direction hypotheses"
      - "the dependent realization graph is indexed only by the package map assembled from independent code"
    discharged:
      - "independent PackageTotalHom assembly and exact recovery"
      - "independent GeometryTotalHom assembly and exact recovery"
      - "complete-code separation"
      - "same-cycle connection to the common complete-map graph surface"
    remaining:
      - "complete-code category structure and functorial category equivalence"
      - "fixed target B object assembly and four-family integration"
  certificate_provenance:
    discharged:
      - "package and complete Hom certificates arise from named local laws; the coverage certificate is explicit and the overlap isomorphism is assembled rather than retained"
      - "a finite pointed-Atom swap paired with the unchanged upper Atom graph is rejected by atom_eq"
      - "the complete-level outer predicate is separated from the bundle of predecessor law-bearing codes, has an identity positive instance, and rejects the reviewed raw-incoherent coefficient swap"
    unresolved:
      - "successor categorical and object-level obligations"
  proof_use:
    used:
      - "every nested and outer material premise is named with its assembly destination in acceptance.premise_status.undischarged_assumptions"
      - "Cycle 67 algebraic graph inverses reconstruct equivalences and coefficient maps"
      - "Cycle 69 context/observable inverses reconstruct the equation transport"
      - "Cycle 70 operation, invariant, signature, and realization graph inverses reconstruct their computational fields"
      - "dependent equality transports realization graphs across reconstructed package equality"
      - "Cycle 64 common graph injectivity separates assembled complete morphisms"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  target_fitting_reason: "neither independent code stores a completed computational configuration submorphism, equation transport, overlap isomorphism, package Hom, or geometry Hom; coverage is honestly exposed as a Prop premise certificate; no whole-code canonical-image premise is accepted; both complete-code inverse directions and the common-surface connection are proved together"
  vacuity: none-found
  vacuity_reason: "the equivalence is quantified over arbitrary GeometryPackage endpoints and actual GeometryTotalHom values, the reverse law recovers every independent graph and supplied local condition, the finite mismatched-Atom fixture rejects an altered package component, and the complete-level fixture rejects a coefficient graph that violates raw coherence"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  four_lane_question: "Given law-bearing predecessor graph codes and the supplied cross-component package, coverage, overlap, and raw-coherence laws, do their computational maps assemble package and geometry transports with exact two-sided recovery and common-surface separation, without retaining completed computational substructures or assuming canonical-reader membership?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphAssembly.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryGraphAssembly: 139 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "define identity and composition directly on complete graph codes, prove the category laws and read/assemble compatibility, and lift the Hom equivalence to the actual geometry category before connecting fixed target B object assembly"
```

## Cycle 72: lawful complete-code category equivalence

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 72
status: result-proposed
branch: codex/4711-g124-complete-code-category-equivalence
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: f4d1dc2708a349186512b3bc0aadd3e50a3ac600
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 71 acceptance: Issue comment 5740395556; Cycle 72 selection: Issue comment 5740402899"
  proof_dag_predecessors:
    - "Cycle 71 lawful complete graph assembly and exact Hom equivalence"
    - "Cycle 65 separation/assembly reconstruction theorem"
    - "Cycle 66 raw common graph category and faithful reading"
  proof_obligation: "make lawful CompleteGeometryGraphCode values the Homs of the local category, prove identity/composition/category laws and exact read/assemble compatibility, derive the actual geometry category equivalence with explicit object assembly, and connect the lawful category functorially to the accepted common graph surface in the same cycle"
  selection_reason: "this bundles code operations, category laws, Hom reconstruction, object reconstruction, the categorical equivalence, and common-surface integration instead of leaving the next cycle as a wiring-only step"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphCategoryEquivalence.lean"
  risks:
    - "category operations might be mere aliases without a unique code-level assembly property"
    - "the local Hom type might be weakened to raw graphs or a global-image subtype"
    - "object assembly might be omitted after the Hom equivalence"
    - "the accepted common graph surface might be deferred to a later cycle"
  unchecked:
    - "four-family target B integration"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "LawfulCode.id and LawfulCode.comp transport the actual category operations along the Cycle 71 Hom equivalence and are uniquely characterized by their assembly formulas. Assembly injectivity proves both unit laws and associativity. The resulting package-indexed category uses lawful independent codes as Homs; readingFunctor and assemblyFunctor preserve identities and composition, and explicit HomSeparation and HomAssembly give exact Hom recovery. The reflexive object bridge only records that both sides are indexed by the same GeometryPackage and does not discharge independent local-object assembly. The same category maps faithfully to the Cycle 66 raw common graph category, and reading an actual morphism commutes with that map."
  completion_candidate: no
  lean_artifacts:
    - "CompleteGeometryGraphCategoryEquivalence.LawfulCode.eq_id_iff_assemble_eq"
    - "CompleteGeometryGraphCategoryEquivalence.LawfulCode.eq_comp_iff_assemble_eq"
    - "CompleteGeometryGraphCategoryEquivalence.PackageIndexedObject.instCategory"
    - "CompleteGeometryGraphCategoryEquivalence.readingFunctor"
    - "CompleteGeometryGraphCategoryEquivalence.assemblyFunctor"
    - "CompleteGeometryGraphCategoryEquivalence.reconstructionData"
    - "CompleteGeometryGraphCategoryEquivalence.equivalence"
    - "CompleteGeometryGraphCategoryEquivalence.commonSurfaceFunctor"
    - "CompleteGeometryGraphCategoryEquivalence.commonSurfaceFunctorFaithful"
  evidence:
    - "both transported code operations have exact assembly formulas and uniqueness iff theorems"
    - "category laws are proved through Cycle 71 assembly separation"
    - "the reconstruction Hom equivalence computes as read/assemble in both directions"
    - "the package-indexed bridge selects the already stored package and returns a reflexive isomorphism"
    - "commonSurfaceFunctor preserves identity/composition and is faithful"
  claim_mapping:
    theorem_names:
      - "LawfulCode.eq_id_iff_assemble_eq"
      - "LawfulCode.eq_comp_iff_assemble_eq"
      - "reconstructionData"
      - "equivalence"
      - "commonSurface_map_read"
    source_labels:
      - "G-124 fixed target B / Hom reconstruction checkpoint"
    conjuncts:
      - "package-indexed category / lawful complete codes are Homs with transported identity and composition"
      - "identity, composition, and associativity / LawfulCode category laws"
      - "separation and assembly / explicit reconstructionData fields"
      - "two-sided Hom recovery / homEquiv_apply and homEquiv_symm_apply"
      - "package-indexed object bridge / objectAssembly"
      - "package-indexed categorical equivalence / equivalence"
      - "accepted graph connection / commonSurfaceFunctor and commonSurface_map_read"
    undischarged_assumptions:
      - "Cycle 71 predecessor and cross-component law certificates remain the supplied direction hypotheses of each lawful CompleteGeometryGraphCode"
      - "componentwise closure of identity and composition has not been constructed"
      - "independently supplied coherent local objects have not been assembled"
      - "no new premise is added by Cycle 72"
    acceptance_point: "the lawful complete-code Hom family now has a package-indexed categorical presentation with exact Hom recovery and a same-cycle faithful common-surface connection; direct certificate-level operations and independent local-object assembly remain open"
    port_status: not-applicable
  nonclaims:
    - "transported identity and composition discharge fixed-target B componentwise closure"
    - "the reflexive package wrapper discharges fixed-target B independent local-object assembly"
    - "the four required G-124 families already share this one local-model category"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    discharged:
      - "transported complete-code identity and composition"
      - "category laws for the transported operations"
      - "read/assemble functoriality and categorical Hom equivalence"
      - "same-cycle faithful connection to the accepted common graph category"
    remaining:
      - "componentwise identity and composition closed directly from local certificates"
      - "fixed-target B object assembly from an independently supplied coherent local object"
      - "four-family target B integration"
  certificate_provenance:
    discharged:
      - "category operations are transported along the reviewed Cycle 71 Hom equivalence and uniquely determined by their assembly equations"
    unresolved:
      - "direct local-certificate provenance for identity and composition"
      - "independent local-object provenance rather than a GeometryPackage wrapper"
      - "cross-family common object and Hom construction"
  proof_use:
    used:
      - "Cycle 71 assemble_read and read_assemble supply both Hom inverse directions"
      - "Cycle 71 assemble_injective proves all three category equations and uniqueness"
      - "Cycle 65 ReconstructionData turns Hom separation, Hom assembly, and object assembly into a categorical equivalence"
      - "Cycle 66 readCompleteMapGraphs identity/composition laws define the common-surface functor"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: found-and-bounded
  target_fitting_reason: "the local Hom type remains the independent lawful code and no completed morphism field or reader-image membership is added, but the operations are transported through assembled global morphisms and the object is a GeometryPackage wrapper; both are explicitly bounded as checkpoint results rather than fixed-target B discharge"
  vacuity: none-found
  vacuity_reason: "the Hom equivalence is quantified over every geometry package pair and every lawful code, and Cycle 71 supplies concrete positive and rejected certificates for the Hom predicate; no claim is made for independent local objects"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: "initial fixed-target B discharge claim withdrawn after formal review; retained result is an explicitly package-indexed proof checkpoint"
  four_lane_question: "Does the revised Cycle 72 honestly prove only a package-indexed category equivalence with exact Hom recovery and a faithful common-surface connection, while leaving componentwise certificate closure and independent local-object assembly open?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphCategoryEquivalence.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryGraphCategoryEquivalence: 36 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "replace transported complete-code operations by componentwise constructors with local-certificate closure, then construct and assemble an independently supplied coherent local object before four-family integration"
```

## Cycle 73: explicit package data and reader-mediated lawful operations

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 73
status: result-proposed
branch: codex/4711-g124-direct-code-object-assembly
base_oid: 4a01607b5bfa2fbb3f3a7956b4ab39d7e1232758
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 72 acceptance: Issue comment 5740604727; Cycle 73 selection: Issue comment 5740612889"
  proof_dag_predecessors:
    - "Cycle 67 algebraic graph identity/composition"
    - "Cycle 69 context/observable graph assembly"
    - "Cycle 70 dependent operation and signature composition"
    - "Cycle 71 lawful package read/assemble equivalence"
    - "Cycle 72 transported lawful category operations"
  proof_obligation: "construct package identity and composition from predecessor code fields, close their package certificates, prove assembly and category laws, and connect the result to the Cycle 72 complete-code operation in the same cycle"
  selection_reason: "identity, composition, dependent reindexing, separation, universal characterization, category laws, and the complete-code package projection are one reviewable unit"
  expected_result_type: proof-checkpoint
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean"
  unchecked:
    - "componentwise coefficient and realization composition at CompleteGeometryGraphCode level"
    - "independently supplied coherent local-object assembly"
    - "four-family target B integration"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "idData and compData display all nine package fields. Eight fields use predecessor operations, while context/observable is read from an equation transport obtained through package assembly. Fieldwise separation proves equality with the canonical reader, including dependent operation and signature reindexing; the lawful certificate is then transported from that reader. The resulting id and comp have exact assembly formulas, a unique-composite iff theorem, both unit laws, associativity, and identity/composition equalities with the Cycle 72 package projections. The standalone direct context/observable comp constructs naturality from its input laws but is not yet used by compData. Direct package context/certificate closure, complete outer fields, and independent object assembly remain open."
  completion_candidate: no
  lean_artifacts:
    - "CompleteGeometryDirectCategory.ContextObservableGraphCode.comp"
    - "CompleteGeometryDirectCategory.PackageGraphCode.idData"
    - "CompleteGeometryDirectCategory.PackageGraphCode.compData"
    - "CompleteGeometryDirectCategory.PackageGraphCode.idData_eq_canonical"
    - "CompleteGeometryDirectCategory.PackageGraphCode.compData_eq_canonical"
    - "CompleteGeometryDirectCategory.PackageGraphCode.eq_comp_iff_assemble_eq"
    - "CompleteGeometryDirectCategory.PackageGraphCode.id_comp"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_id"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_assoc"
    - "CompleteGeometryDirectCategory.PackageGraphCode.id_eq_complete_package"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_eq_complete_package"
  evidence:
    - "identity and composition expose PackageGraphData values rather than aliasing PackageGraphCode.read"
    - "eight fields use predecessor operations; context/observable is reader-mediated through assembled equation transport"
    - "operation and signature comparisons discharge both dependent reindexings"
    - "compData_eq_canonical separates all nine computational fields"
    - "eq_comp_iff_assemble_eq gives a substantive universal characterization"
    - "unit and associativity laws are proved through package assembly separation"
    - "id_eq_complete_package and comp_eq_complete_package supply both Cycle 72 connections"
  nonclaims:
    - "all nine package fields are composed directly from local component codes"
    - "the output IsPackageGraphCode certificate is proved directly from local laws"
    - "the standalone direct context/observable constructor is the context field used by compData"
    - "complete-geometry coefficient, realization, coverage, overlap, and raw-coherence composition are discharged"
    - "an independently supplied local object has been assembled"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    discharged:
      - "explicit reader-mediated nine-field package identity and composition data"
      - "dependent operation and signature reindexing comparison"
      - "package assembly formulas, uniqueness, units, and associativity"
      - "same-cycle identity and composition comparisons with the Cycle 72 package projections"
    remaining:
      - "direct package context/observable construction and direct IsPackageGraphCode certificate closure"
      - "complete-geometry outer component composition"
      - "independent local-object assembly"
      - "four-family target B integration"
  certificate_provenance:
    discharged:
      - "the only inputs to id and comp are packages or lawful package codes; no completed PackageTotalHom is stored or accepted as an argument"
      - "fieldwise equality precisely identifies the result with the Cycle 71 canonical reader"
    unresolved:
      - "the package context field passes through package assembly and the equation-transport reader"
      - "the output package certificate is transported from the canonical reader rather than closed directly from local laws"
      - "complete-geometry outer certificate provenance"
      - "independent local-object provenance"
  proof_use:
    used:
      - "Cycle 67 primitive and algebraic graph identity/composition laws"
      - "Cycle 69 equation-transport context/observable reader"
      - "Cycle 70 dependent operation and signature identity/composition"
      - "Cycle 71 read/assemble inverse and dependent HEq APIs"
      - "Cycle 72 complete-code assembly formula for the same-cycle projection comparison"
  structure_field_escape: none-found
  route_integrity: checkpoint-reader-mediated
  target_fitting: found-and-bounded
  target_fitting_reason: "the cycle exposes nine-field data, proves a universal property and category laws, and connects both Cycle 72 projections; it records rather than discharges the remaining reader-mediated context and certificate route"
  vacuity: none-found
  vacuity_reason: "the results quantify over arbitrary geometry-package endpoints and arbitrary lawful package codes, and the universal property separates every lawful candidate"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: "the selected direct-certificate obligation is not discharged; Cycle 73 is downgraded to a reader-mediated proof checkpoint without claiming a formal impossibility result"
  four_lane_question: "Does Cycle 73 honestly prove only explicit reader-mediated package data, exact assembly/universality/category laws, and both Cycle 72 package-projection comparisons, while leaving direct context/certificate closure and independent object assembly open?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryDirectCategory: 30 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "first replace the reader-mediated package context and certificate by direct local-law closure; then extend through complete outer fields and assemble an independent local object before four-family integration"
```

## Cycle 74: direct package category and common-surface closure

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 74
status: result-proposed
branch: codex/4711-g124-direct-package-certificate
base_oid: cb7a659cd28d988fd4d5fd1ba9ad4eb35930459d
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 73 acceptance: PR #4793; Cycle 74 selection: Issue comment 5740967778"
  proof_dag_predecessors:
    - "Cycle 67 algebraic graph identity/composition"
    - "Cycle 69 direct context/observable graph constructors and coherence"
    - "Cycle 70 dependent operation and signature composition"
    - "Cycle 71 lawful package laws and canonical read/assemble comparison"
    - "Cycle 72 complete-code category and common graph surface"
    - "Cycle 73 package assembly, universality, and category laws"
  proof_obligation: "replace the reader-mediated joint context field and transported package certificate by direct local identity/composition and direct proofs of all fourteen package laws, retaining exact assembly, universality, category laws, and both Cycle 72/common-surface connections in the same cycle"
  selection_reason: "direct joint construction, dependent reindexing, fourteen local laws, universal characterization, and accepted-surface connections form one auditable package-category step"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean"
  unchecked:
    - "direct complete-geometry coefficient, realization, coverage, overlap, and raw-coherence identity/composition"
    - "independently supplied coherent local-object assembly"
    - "four-family target B integration"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "ContextObservableGraphCode.id and comp now construct joint context/observable codes from local graph operations and naturality laws. idData and compData use those constructors, while idData_lawful and compData_lawful prove all fourteen IsPackageGraphCode fields from endpoint data and input certificates without importing canonicalIdentity.2 or canonicalComposite.2. The direct lawful operations retain exact assembly, composite uniqueness, unit and associativity laws, canonical comparisons, and bundled equalities with both the Cycle 72 package projection and accepted common graph identity/composition. Complete outer fields and independent object assembly remain open."
  completion_candidate: no
  lean_artifacts:
    - "CompleteGeometryDirectCategory.ContextObservableGraphCode.id"
    - "CompleteGeometryDirectCategory.ContextObservableGraphCode.comp"
    - "CompleteGeometryDirectCategory.PackageGraphCode.idData_lawful"
    - "CompleteGeometryDirectCategory.PackageGraphCode.compData_lawful"
    - "CompleteGeometryDirectCategory.PackageGraphCode.eq_comp_iff_assemble_eq"
    - "CompleteGeometryDirectCategory.PackageGraphCode.id_comp"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_id"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_assoc"
    - "CompleteGeometryDirectCategory.PackageGraphCode.id_cycle72_and_commonSurface"
    - "CompleteGeometryDirectCategory.PackageGraphCode.comp_cycle72_and_commonSurface"
  evidence:
    - "the joint context/observable identity and composition are constructed locally and used by idData and compData"
    - "idData_lawful and compData_lawful discharge each of the fourteen package laws from local component laws and input certificates"
    - "the lawful id and comp definitions do not use the canonical reader certificate"
    - "eq_comp_iff_assemble_eq is the substantive package-level universal characterization"
    - "unit and associativity laws follow through package assembly separation"
    - "id_cycle72_and_commonSurface and comp_cycle72_and_commonSurface bundle both predecessor and common-graph connections"
  nonclaims:
    - "direct complete-geometry outer identity and composition are discharged"
    - "an independently supplied local object has been assembled"
    - "the four mandatory families are integrated into the fixed target B equivalence"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    discharged:
      - "direct joint context/observable identity and composition"
      - "all fourteen direct IsPackageGraphCode laws"
      - "exact package assembly, uniqueness, units, and associativity"
      - "same-cycle Cycle 72 package-projection and accepted common-graph connections"
    remaining:
      - "direct complete-geometry outer component closure"
      - "independent local-object assembly"
      - "four-family target B integration"
  certificate_provenance:
    discharged:
      - "identity uses only the endpoint package and predecessor identity laws"
      - "composition uses only the two input package codes, their certificates, and predecessor composition laws"
      - "canonical reader values are comparison targets only and do not provide the output package certificate"
    unresolved:
      - "complete-geometry outer certificate provenance"
      - "independent local-object provenance"
  proof_use:
    used:
      - "Cycle 67 primitive and algebraic graph identity/composition laws"
      - "Cycle 69 context/observable coherence and local naturality"
      - "Cycle 70 dependent operation, invariant, and signature laws"
      - "Cycle 71 package law fields and read/assemble comparison APIs"
      - "Cycle 72 complete-code and common-graph identity/composition formulas"
      - "Cycle 73 package assembly separation, universality, and category laws"
  structure_field_escape: none-found
  route_integrity: direct-package-local-laws
  target_fitting: found-and-bounded
  target_fitting_reason: "the cycle removes the selected canonical-certificate route, proves a universal property and category laws, and connects both predecessor surfaces without claiming complete outer or object assembly"
  vacuity: none-found
  vacuity_reason: "the direct certificates quantify over arbitrary geometry-package endpoints and arbitrary composable lawful package codes, and the universal property separates every lawful candidate"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  four_lane_question: "Do direct joint context/observable identity and composition and all fourteen package laws close from local graph data and input certificates, with exact assembly, package universality/category laws, and Cycle 73/Cycle 72/common-surface comparisons, while leaving complete outer closure and independent object assembly open?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryDirectCategory: 49 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct dependent base-reindex APIs and direct complete-level coefficient, realization, coverage, overlap, and raw identity/composition together with exact assembly, universality, category laws, and same-cycle Cycle 72/common-surface comparisons; then combine independent object assembly with its Hom connection rather than deferring a connection-only cycle"
```

## Cycle 75: direct complete-geometry category and outer-law closure

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 75
status: result-proposed
branch: codex/4711-g124-direct-complete-category
base_oid: f00e255b71d602498ad95ec683db1617bb5bebcf
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 74 acceptance: Issue comment 5741210094; Cycle 75 selection: Issue comment 5741215781"
  proof_dag_predecessors:
    - "Cycle 67 coefficient graph-code identity/composition"
    - "Cycle 70 realization and raw-coherence identity/composition"
    - "GeometryTransport.Categories coverage and overlap identity/composition constructors"
    - "Cycle 71 complete graph-code assembly separation"
    - "Cycle 72 transported complete-code category and common graph surface"
    - "Cycle 74 direct package identity/composition and all fourteen package laws"
  proof_obligation: "construct dependent package-base reindexing and direct complete-geometry identity/composition for coefficient, realization, coverage, overlap, and raw coherence, then retain exact assembly, universality, category laws, and Cycle 72/common-surface comparisons in the same cycle"
  selection_reason: "the dependent reindex layer, all outer certificate closures, substantive complete-code uniqueness, category laws, and accepted-surface connections form one reviewable complete-level step"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean"
  unchecked:
    - "independently supplied coherent local-object assembly"
    - "four-family target B integration"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "CompleteGeometryGraphCode.idData and compData combine the Cycle 74 direct package operations with coefficient and realization graph identity/composition under explicit package-base reindexing. idData_lawful and compData_lawful close coverage, both overlap directions, and raw coherence from local identity/composition constructors and the two input certificates. Direct local component calculations prove actual assembly before comparison with Cycle 72. Arbitrary-candidate identity/composition characterizations, unit and associativity laws, and bundled Cycle 72/common-graph comparisons are included. Independent local-object assembly and four-family integration remain open."
  completion_candidate: no
  lean_artifacts:
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.reindexRealization"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.reindexCoverage"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.reindexOverlap"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.reindexRaw"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.idData_lawful"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.compData_lawful"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_id_local"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.assemble_comp_local"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.eq_id_iff_assemble_eq"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.eq_comp_iff_assemble_eq"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_comp"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_id"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_assoc"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.id_cycle72_and_commonSurface"
    - "CompleteGeometryDirectCategory.CompleteGeometryGraphCode.comp_cycle72_and_commonSurface"
  evidence:
    - "the lawful complete id and comp definitions contain direct data and direct outer certificates rather than Cycle 72 aliases"
    - "coverage, overlap, and raw coherence are generated by local identity/composition laws and reindexed only along proved package/coefficient equalities"
    - "assemble_id_local and assemble_comp_local compare coefficient and all three realization maps componentwise before any Cycle 72 comparison"
    - "eq_id_iff_assemble_eq and eq_comp_iff_assemble_eq quantify over arbitrary lawful candidates"
    - "unit and associativity laws follow through complete-code assembly separation"
    - "id_cycle72_and_commonSurface and comp_cycle72_and_commonSurface bundle both predecessor and common-graph connections"
  nonclaims:
    - "an independently supplied coherent local object has been assembled"
    - "the four mandatory families are integrated into the fixed target B equivalence"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    discharged:
      - "dependent package-base reindexing for realization, coverage, overlap, and raw coherence"
      - "direct complete identity/composition computational data and outer certificates"
      - "exact local-component assembly, arbitrary-candidate uniqueness, units, and associativity"
      - "same-cycle Cycle 72 and accepted common-graph connections"
    remaining:
      - "independent local-object and Hom assembly"
      - "four-family target B integration"
  certificate_provenance:
    discharged:
      - "identity uses Cycle 74 package identity and local outer identity constructors"
      - "composition uses Cycle 74 package composition, the two input complete certificates, and local outer composition constructors"
      - "Cycle 72 transported operations are comparison targets only and do not provide the output complete certificate"
    unresolved:
      - "independent local-object provenance"
  proof_use:
    used:
      - "Cycle 67 coefficient graph-code identity/composition"
      - "Cycle 70 realization and raw-coherence identity/composition"
      - "GeometryTransport.Categories coverage and overlap identity/composition constructors"
      - "Cycle 71 complete assembly separation and dependent cast APIs"
      - "Cycle 72 transported complete-code and common-graph formulas for comparison only"
      - "Cycle 74 direct package identity/composition and exact assembly"
  structure_field_escape: none-found
  route_integrity: direct-complete-local-laws
  target_fitting: found-and-bounded
  target_fitting_reason: "the cycle closes every selected complete outer field, proves local-component assembly and universality, and includes both accepted connections without claiming object assembly"
  vacuity: none-found
  vacuity_reason: "the operations quantify over arbitrary geometry-package endpoints and arbitrary composable lawful complete graph codes, while uniqueness quantifies over every lawful candidate"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  four_lane_question: "Do direct complete-geometry identity and composition close all coefficient, realization, coverage, overlap, and raw-coherence fields from Cycle 74 package operations and input certificates, with exact assembly, complete-code universality/category laws, and Cycle 72/common-surface comparisons in the same cycle, while leaving independent local-object assembly and four-family integration open?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean: pass"
    - "#assert_standard_axioms_only CompleteGeometryDirectCategory: 75 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "construct independently supplied coherent local objects and Hom families together with their assembly, separation, essential-surjectivity/equivalence result, and common-surface connection in one cycle; then apply that result to the four mandatory families"
```

## Cycle 76: rejected copied-object reconstruction

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 76
status: rejected
branch: codex/4711-g124-independent-object-category
base_oid: 35f931ee50ef5ae91d226bbf3e37017e059ad308
tracking_issue: 4711
pull_request: 4796
rejected_head: 163740bd17f48b663ea8d5afd6831a413686db62
reason: "ObjectCode copied the five ReadingCore fields exactly; because GeometryPackage is an abbreviation of ReadingCore, read/assemble reduced to eta rewrapping and did not assemble an independently specified local object"
retained_evidence:
  - "PR audit comment 5741551609"
  - "Issue rejection comment 5741555139"
nonclaims:
  - "Cycle 76 contributes to fixed target B"
  - "the rejected branch is part of main"
```

## Cycle 77: simultaneous CS branch reconstruction and finite-route connection

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 77
status: result-proposed
branch: codex/4711-g124-cs-paired-reconstruction
base_oid: 35f931ee50ef5ae91d226bbf3e37017e059ad308
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 75 acceptance: Issue comment 5741395911; Cycle 76 rejection: Issue comment 5741555139; Cycle 77 selection: Issue comment 5741575501"
  proof_dag_predecessors:
    - "Cycle 23 protocol observed-restriction object/Hom reconstruction"
    - "Cycle 24 protocol finite decoder, Karoubi restriction, retract, and Arrow coherence"
    - "Cycle 25 lens finite-fiber object/Hom reconstruction"
    - "Cycle 26 lens finite decoder, Karoubi restriction, retract, and Arrow coherence"
    - "Cycle 65 separation/Hom assembly/object assembly reconstruction theorem"
  proof_obligation: "place lens and protocol independent local categories under one branch-indexed parameter declaration; directly assemble every selected Hom and object, prove both inverse laws and the category equivalence, and connect the global decoder through the branch reading to each accepted finite decoder and Karoubi/Arrow route in the same cycle"
  selection_reason: "this advances from separate branch equivalences through both simultaneous product closure and a common dependent branch declaration, bundles explicit commuting finite-presentation comparisons, and avoids the copied-global-object construction rejected in Cycle 76"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CSPairedReconstruction.lean"
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/CSBranchReconstruction.lean"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The product construction simultaneously reconstructs both accepted CS families and proves paired retract generation. In addition, CSBranchParameter is one common declaration whose arbitrary parameter determines the global category, independent local category, primitive reading, Hom assembler, and object assembler. csBranch_read_assemble and csBranch_assemble_read prove the two Hom inverse laws by cases from the primitive assemblers; csBranchRealize builds the selected product lens or double-opposite protocol realization, yielding ReconstructionData, unique Hom preimages, and a category equivalence for every branch parameter. Separate global lens/protocol decoders now precede the common reading, and explicit natural isomorphisms identify their readings with the accepted finite decoders. The Karoubi and Arrow routes are composed through the inverse common branch reconstruction, rather than merely sharing a local codomain."
  completion_candidate: no
  lean_artifacts:
    - "csPairedReading"
    - "csPairedAssemble"
    - "csPaired_read_assemble"
    - "csPaired_assemble_read"
    - "csPairedHomEquiv"
    - "csPairedRealize"
    - "csPairedRealizeIso"
    - "csPairedReconstructionData"
    - "csPairedReconstructionEquivalence"
    - "csPaired_existsUnique_preimage"
    - "csPairedFiniteDecoder"
    - "csPairedFiniteDecoder_retractGeneratedBy"
    - "csPairedKaroubiEquivalence"
    - "csPairedKaroubiRestrictionIso"
    - "csPairedKaroubiArrowEquivalence"
    - "CSBranchParameter"
    - "CSBranchGlobal"
    - "CSBranchLocal"
    - "csBranchReading"
    - "csBranchAssemble"
    - "csBranch_read_assemble"
    - "csBranch_assemble_read"
    - "csBranchRealize"
    - "csBranchRealizeIso"
    - "csBranchReconstructionData"
    - "csBranchReconstructionEquivalence"
    - "csBranch_existsUnique_preimage"
    - "lensClosedFamilyFiniteDecoderReadingIso"
    - "protocolClosedFamilyFiniteDecoderReadingIso"
    - "lensKaroubiClosedFamilyViaBranchEquivalence"
    - "protocolKaroubiClosedFamilyViaBranchEquivalence"
    - "lensKaroubiClosedFamilyArrowViaBranchEquivalence"
    - "protocolKaroubiClosedFamilyArrowViaBranchEquivalence"
  evidence:
    - "the local object is FintypeCat times ProtocolObservedRestrictionModel and contains no completed global realization or extension certificate"
    - "both Hom inverse laws are proved from the primitive branch assemblers rather than from a supplied category equivalence"
    - "the object assembler constructs a product lens and a protocol realization from local data"
    - "unique Hom preimages and the category equivalence are consequences of the explicit ReconstructionData"
    - "paired decoder retract generation combines two independently proved retract witnesses componentwise"
    - "Karoubi restriction and Arrow connections are included in the same cycle"
    - "one dependent branch parameter selects both families without replacing them by a product-only wrapper"
    - "global-decoder reading is naturally isomorphic to each accepted local decoder"
    - "Karoubi and Arrow equivalences explicitly pass through the inverse branch reconstruction"
  nonclaims:
    - "tagged operation and G-122 branches are integrated into this paired category"
    - "the final four-family parameter declaration and fixed target B equivalence are complete"
    - "G-124 as a whole is complete"
audits:
  premise_delta:
    discharged:
      - "simultaneous lens/protocol Hom separation and assembly"
      - "simultaneous lens/protocol independent local-object assembly"
      - "two-sided Hom recovery, unique preimages, and category equivalence"
      - "same-cycle paired finite decoder, Karoubi restriction, retract, and Arrow connections"
      - "common branch parameter, branch-indexed reading, direct Hom/object assembly, and category equivalence"
      - "global-decoder/branch-reading/local-decoder natural isomorphisms"
      - "Karoubi and Arrow routes through the common branch reconstruction"
    remaining:
      - "tagged and G-122 branch integration on the same common local-model surface"
      - "fixed target A common parameter declaration and target B four-family equivalence"
  certificate_provenance:
    discharged:
      - "lens Hom assembly is constructed by LensRealization.ext from the supplied fiber map"
      - "protocol Hom assembly is constructed from state-map naturality and observation preservation"
      - "lens object assembly is the product lens; protocol object assembly is constructed from the local diagram and observation"
    unresolved:
      - "cross-family common object/Hom construction for tagged and G-122"
  proof_use:
    used:
      - "LensRealization.res_ext and ext_res"
      - "protocolObservedRestriction read/assemble inverse laws"
      - "lensFiberModelRealizationIso and protocolObservedRestrictionRealizationIso"
      - "Cycle 65 ReconstructionData equivalence and unique-preimage theorem"
      - "accepted lens/protocol finite decoder retract and Karoubi/Arrow coherence"
  structure_field_escape: none-found
  route_integrity: direct-paired-branch-assembly
  target_fitting: found-and-bounded
  target_fitting_reason: "the cycle proves a genuine two-family object/Hom reconstruction with both inverse laws and all finite-route connections; it does not claim the missing tagged/G-122 integration"
  vacuity: none-found
  vacuity_reason: "the statements quantify over arbitrary lens and protocol inputs, every paired realization endpoint, every coherent paired local Hom, and every paired local object"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  four_lane_question: "Does Cycle 77 reconstruct every lens/protocol branch selected by one common parameter from independent local objects and Homs, with explicit two-sided assembly and commuting global-decoder/finite-decoder/Karoubi/Arrow connections, while leaving tagged and G-122 integration open?"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CSPairedReconstruction.lean: pass"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/CSBranchReconstruction.lean: pass"
    - "#assert_standard_axioms_only CSBranchReconstruction: 44 declarations, standard axioms only"
  finding_resolution:
    - "initial formal math lane found the product-only surface too weak; CSBranchParameter and its dependent global/local reading surface were added"
    - "initial formal math lane found no commuting comparison from the new reading to finite routes; both global-decoder reading isomorphisms and Karoubi/Arrow factorizations through branch reconstruction were added"
  blocking_findings: []
  next_obligation: "extend the accepted simultaneous reconstruction by adjoining the tagged and G-122 branches through independent local categories and direct assemblers, retaining one reviewable four-family equivalence and common connections"
```

## Cycle 78: full G-122 twisted group and four-family branch reconstruction

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 78
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 05c2bd89acda78aee16348cbd9a6ed0f42e26711
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 77 acceptance: Issue comment 5741748590; Cycle 77 report next_obligation"
  proof_dag_predecessors:
    - "Cycle 37 tagged finite-local monoid equivalence"
    - "Cycle 38 tagged one-object category equivalence"
    - "Cycle 60 full G-122 comparison/kernel coordinate equivalence"
    - "Cycle 77 simultaneous lens/protocol branch reconstruction"
  proof_obligation: "construct a case-indexed checkpoint containing tagged, full fixed G-122, lens, and protocol branches; give the already established full G-122 coordinates their correct twisted group law; prove branchwise Hom/object assembly, both inverse laws, uniqueness, category equivalence, and explicit connections to accepted family surfaces in the same cycle"
  selection_reason: "this tests the four mandatory branches behind one dependent API and strengthens the accepted full G-122 coordinate equivalence to a multiplicative and categorical result; it does not claim to close the fixed target A-B common-category obligation"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "G122FullComparisonTwistedGroup.lean"
    - "AATFourFamilyBranchReconstruction.lean"
  risks:
    - "the ordinary product group would state the wrong G-122 kernel law"
    - "tagged and G-122 object universes must coexist with CS Hom universes without hiding actual Homs"
    - "a case-indexed union is not yet one non-case-defined realization-category construction"
  unchecked:
    - "formal four-lane review of the fixed PR head"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "TwistedCode gives the already established normalized/full-kernel coordinates their conjugation-twisted multiplication and inverse formulas. Assembly preserves multiplication, identity, and inverse; the two inverse laws prove separation, the group laws, a multiplicative equivalence with every raw comparison, a one-object category equivalence, and unique Hom preimages. AATBranchParameter case-selects tagged, full G-122, lens, or protocol data under one dependent declaration. Each selected branch has a reading, direct Hom assembler, explicit object realization, both Hom inverse laws, ReconstructionData, unique preimages, and a category equivalence. The same file connects tagged finite tables and normal forms, identifies the G-122 branch kernel coordinate with the unique full lift-fiber torsor displacement, and factors lifted lens/protocol finite decoders plus Karoubi and Arrow routes through the branch reconstruction. This is a case-indexed proof checkpoint, not discharge of the fixed target A-B common-category obligation."
  completion_candidate: no
  lean_artifacts:
    - "G122FullComparisonTwistedGroup.TwistedCode"
    - "G122FullComparisonTwistedGroup.multiply"
    - "G122FullComparisonTwistedGroup.inverse"
    - "G122FullComparisonTwistedGroup.assemble_multiply"
    - "G122FullComparisonTwistedGroup.assemble_inverse"
    - "G122FullComparisonTwistedGroup.twistedCodeMulEquiv"
    - "G122FullComparisonTwistedGroup.equivalence"
    - "G122FullComparisonTwistedGroup.existsUnique_preimage"
    - "AATBranchParameter"
    - "AATBranchGlobal"
    - "AATBranchLocal"
    - "aatBranchReading"
    - "aatBranchAssemble"
    - "aatBranch_read_assemble"
    - "aatBranch_assemble_read"
    - "aatBranchRealize"
    - "aatBranchRealizeIso"
    - "aatBranchReconstructionData"
    - "aatBranchReconstructionEquivalence"
    - "aatBranch_existsUnique_preimage"
    - "aatBranchG122LiftHom"
    - "aatBranchG122ReadingKernel_smul_canonicalLift"
    - "aatBranchG122FullLiftFiber_unique_kernel_eq_reading"
    - "aatBranchLensFiniteDecoderReadingIso"
    - "aatBranchProtocolFiniteDecoderReadingIso"
    - "aatBranchLensKaroubiArrowEquivalence"
    - "aatBranchProtocolKaroubiArrowEquivalence"
  evidence:
    - "the G-122 local multiplication is the explicit conjugation formula, not the pre-existing ordinary product instance"
    - "assembly is injective by the established read/assemble laws and is used to prove all group axioms"
    - "the G-122 branch covers the full RawComparison group rather than a chosen finite subgroup"
    - "all four branches use direct assemblers and explicit object realizations before ReconstructionData derives equivalence"
    - "the G-122 reading kernel acts from the canonical lift to every supplied lift, and torsor uniqueness identifies any such displacement with that branch coordinate"
    - "tagged finite values and CS finite/Karoubi/Arrow routes are attached in the same module"
  claim_mapping:
    theorem_names:
      - "twistedCodeMulEquiv"
      - "aatBranchReconstructionEquivalence"
      - "aatBranch_existsUnique_preimage"
      - "aatBranchG122ReadingKernel_smul_canonicalLift"
      - "aatBranchG122FullLiftFiber_unique_kernel_eq_reading"
    source_labels:
      - "Cycle 78 case-indexed four-family checkpoint"
      - "fixed target C full G-122 comparison group and lift fibers, limited to the fixed input"
    conjuncts:
      - "G-122 full comparison multiplication and inverse -> TwistedCode group and twistedCodeMulEquiv"
      - "branchwise separation and assembly -> aatBranchReconstructionData and equivalence"
      - "same-cycle accepted connections -> tagged value/normal-form, G-122 branch-coordinate/torsor identification, CS decoder/Karoubi/Arrow declarations"
    undischarged_assumptions:
      - "the four branches remain selected by cases rather than being fibers of one independently defined common realization category; fixed target A-B is therefore not discharged"
      - "TwistedCode retains actual full-kernel and normalized-comparison values; primitive G-122 local syntax remains open"
      - "fixed target C comparison-group transport for every comparison in the final common category remains open"
    acceptance_point: "the case-indexed four-family API, the full G-122 twisted group, and explicit family connections form a proof checkpoint; fixed target A-B and the final common category are not claimed"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "full G-122 comparison coordinates carry the correct group and one-object category structure"
      - "tagged, G-122, lens, and protocol are selected by one parameter declaration"
      - "every selected branch has direct two-sided Hom reconstruction, object realization, uniqueness, and category equivalence"
      - "family-specific accepted surfaces are connected in the same cycle, including equality of the G-122 branch kernel coordinate with the unique torsor displacement"
    remaining:
      - "one non-case-defined R_Theta and M_Theta whose fibers realize the four branches"
      - "projection, normalization, and comparison-group naturality across that final common category"
  certificate_provenance:
    discharged:
      - "G-122 kernel membership is proved through restrictionHom and canonical-section right inversion"
      - "group laws follow from explicit formulas plus injective semantic assembly"
      - "CS and tagged assemblers reuse reviewed primitive constructors and their inverse laws"
    unresolved:
      - "common cross-branch data condition D_Theta outside the branch-indexed declaration"
  proof_use:
    used:
      - "Cycle 60 full comparison read/assemble and multiplication formula"
      - "Cycle 37 tagged actual/local multiplicative equivalence"
      - "Cycle 77 CS direct assemblers and finite/Karoubi/Arrow connections"
      - "Cycle 65 ReconstructionData theorem"
  structure_field_escape: "found-and-bounded: TwistedCode is a full coordinate presentation, not primitive G-122 local syntax"
  route_integrity: pass
  target_fitting: bounded-proof-checkpoint
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: "corrected after review: case-indexed branch reconstruction is not counted as fixed target A-B discharge"
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/G122FullComparisonTwistedGroup.lean: pass; 40 declarations, standard axioms only"
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/AATFourFamilyBranchReconstruction.lean: pass; 58 declarations, standard axioms only"
  four_lane_question: "Does Cycle 78 provide a correctly bounded case-indexed checkpoint for all four selected families, equip the accepted full G-122 coordinates with the correct twisted group, identify the branch kernel with the unique lift-fiber torsor displacement, and factor the tagged, finite-decoder, Karoubi, and Arrow connections through the branch API without counting fixed target A-B as discharged?"
  blocking_findings: []
  review_finding_resolutions:
    - "the torsor wrapper was replaced by a branch Hom, a theorem that its read kernel acts to the supplied lift, and a uniqueness theorem identifying every torsor displacement with that branch coordinate"
    - "the result was downgraded from proof-obligation-discharged to proof-checkpoint, and fixed target A-B mapping was removed"
    - "the full-coordinate nature of TwistedCode is now recorded as bounded rather than classified as no structure-field escape"
  next_obligation: "construct one independently defined realization/local-model category whose fibers recover all four Cycle 78 branches, prove its direct object/Hom assembly and both inverse laws, and simultaneously transport projections, normalization, and full comparison groups through that equivalence"
```

## Cycle 79: total four-family reconstruction and same-cycle routes

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 79
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 8dd01cbce46be3e6e143e488e8ef7a2d25af9b28
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Cycle 78 acceptance: Issue comment 5742157667; Cycle 79 selection: Issue comment 5742162241"
  proof_dag_predecessors:
    - "Cycle 78 case-indexed branch reconstruction for all four mandatory families"
    - "Cycle 78 full G-122 twisted coordinates and lift-fiber torsor identification"
    - "Cycle 78 tagged and CS finite-decoder/Karoubi/Arrow routes"
    - "Cycle 65 ReconstructionData equivalence theorem"
  proof_obligation: "construct one indexed total global category and one indexed total local category over all four admitted parameters, with Homs only inside a common fiber; define a total reading, direct Hom assembly, both inverse laws, object realization, category equivalence, exact fiber recovery, and the parameter projection; in the same module route tagged formulas, full G-122 coordinates and torsor uniqueness, and lens/protocol finite-decoder, Karoubi, and Arrow maps through the total categories"
  selection_reason: "Cycle 78 supplied all branch data but left totalization and its accepted family connections to a later step; combining the total equivalence, exact fiber recovery, and every route prevents a connection-only follow-up cycle"
  expected_result_type: proof-checkpoint
  lean_targets:
    - "AATFourFamilyTotalReconstruction.lean"
  risks:
    - "a coproduct category can totalize the branches without yet constructing the fixed target global realization data from primitive input"
    - "the G-122 local fiber still contains full accepted coordinates rather than independent primitive syntax"
    - "cross-family Homs must not be manufactured by the totalization"
  unchecked:
    - "formal four-lane review of the fixed PR head"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "IndexedTotalObject and IndexedTotalHom form single total global and local categories with no cross-family Homs. The total reading has a direct assembler whose read-after-assemble and assemble-after-read laws hold for every total Hom; explicit object realization yields ReconstructionData, unique Hom preimages, and a category equivalence. Each branch inclusion has an exact Hom equivalence, restriction of the total reading is naturally isomorphic to the accepted branch reading, and both total projections agree. The same file recovers the tagged value and assembly formulas, the normalized/full-kernel G-122 reading and its torsor action/uniqueness, and routes both CS finite decoders, Karoubi equivalences, and Arrow equivalences into the total category. This is a larger totalization checkpoint, not fixed target A-B discharge."
  completion_candidate: no
  lean_artifacts:
    - "IndexedTotalObject"
    - "IndexedTotalHom"
    - "aatTotalReading"
    - "aatTotalAssemble"
    - "aatTotal_read_assemble"
    - "aatTotal_assemble_read"
    - "aatTotalRealizeIso"
    - "aatTotalReconstructionData"
    - "aatTotalReconstructionEquivalence"
    - "aatTotal_existsUnique_preimage"
    - "aatGlobalFiberHomEquiv"
    - "aatLocalFiberHomEquiv"
    - "aatTotal_noCrossFamilyHom"
    - "aatFiberReadingIso"
    - "aatTotalReading_comp_projection"
    - "aatTotalTaggedReadingValue"
    - "aatTotalG122ReadingKernel_smul_canonicalLift"
    - "aatTotalG122FullLiftFiber_unique_kernel_eq_reading"
    - "aatTotalLensFiniteDecoderReadingIso"
    - "aatTotalProtocolFiniteDecoderReadingIso"
    - "aatTotalLensKaroubiArrowRoute"
    - "aatTotalProtocolKaroubiArrowRoute"
  evidence:
    - "total Homs have one constructor whose endpoints carry the same parameter"
    - "both total Hom inverse laws are proved directly before deriving separation and equivalence"
    - "total object realization is explicit and its readback is an indexed lift of the accepted branch isomorphism"
    - "the fiber Hom equivalences and the no-cross-family theorem characterize the total Hom space"
    - "the total reading commutes with the discrete parameter projection"
    - "tagged, G-122, finite-decoder, Karoubi, and Arrow statements all occur in the totalization module"
  claim_mapping:
    theorem_names:
      - "aatTotalReconstructionEquivalence"
      - "aatTotal_existsUnique_preimage"
      - "aatTotal_noCrossFamilyHom"
      - "aatFiberReadingIso"
      - "aatTotalReading_comp_projection"
      - "aatTotalG122FullLiftFiber_unique_kernel_eq_reading"
    source_labels:
      - "Cycle 79 total four-family reconstruction checkpoint"
      - "Cycle 79 family-parameter projection compatibility and full G-122 recovery on the accepted fixed input"
    conjuncts:
      - "one total global/local category plus direct two-sided Hom and object reconstruction -> aatTotalReconstructionData and aatTotalReconstructionEquivalence"
      - "exact branch recovery -> fiber Hom equivalences, no-cross-family theorem, and fiber reading natural isomorphism"
      - "same-cycle connections -> projection equality, tagged formulas, G-122 torsor theorems, and CS decoder/Karoubi/Arrow routes"
    undischarged_assumptions:
      - "the total fibers reuse the Cycle 78 branch categories rather than deriving the fixed target global realization category from Sigma, D, and Lambda"
      - "the G-122 local fiber retains normalized comparison and full-kernel coordinate values rather than independent primitive syntax"
      - "the fixed target data condition D_Theta and its uniform primitive reading remain open"
    acceptance_point: "the indexed total categories, their reconstruction equivalence, exact fibers, projection, and all accepted family routes form one checkpoint; fixed target A-B is not claimed"
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "all four accepted branch categories occur as exact fibers of one total global and one total local category"
      - "the total reading has direct Hom/object assembly, both Hom inverse laws, unique preimages, and category equivalence"
      - "cross-family Homs are absent and the family parameter projection commutes with reading"
      - "accepted tagged, G-122, finite-decoder, Karoubi, and Arrow routes are connected in the totalization module"
    remaining:
      - "derive the fixed target R_Theta and M_Theta from primitive Sigma, D, and Lambda data rather than accepted branch types"
      - "construct primitive G-122 local syntax and discharge the final common D_Theta"
      - "construct fixed target C base, observation, and coefficient projections, normalization compatibility, and comparison-group transport"
  certificate_provenance:
    discharged:
      - "total category laws reduce to accepted category laws in the unique common fiber"
      - "total reconstruction laws reduce to the direct Cycle 78 branch inverse laws"
      - "G-122 torsor statements reuse the accepted full-coordinate read and unique displacement theorem"
    unresolved:
      - "primitive provenance for the full G-122 local coordinate syntax"
  proof_use:
    used:
      - "Cycle 78 branch reading, direct assemblers, object realizations, and both inverse laws"
      - "Cycle 78 tagged formulas and G-122 full-coordinate torsor theorems"
      - "Cycle 78 lens/protocol finite-decoder, Karoubi, and Arrow routes"
      - "Cycle 65 ReconstructionData theorem"
  structure_field_escape: "found-and-bounded: totalization is exact over accepted branches, but the G-122 fiber still uses full accepted coordinates"
  route_integrity: pass
  target_fitting: bounded-proof-checkpoint
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "cd research/lean && ./check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/AATFourFamilyTotalReconstruction.lean: pass; 69 declarations, standard axioms only"
  four_lane_question: "Does Cycle 79 construct one indexed total global/local category with no cross-family Homs, direct two-sided Hom and object reconstruction, exact fiber recovery and projection compatibility, while transporting tagged, full G-122 torsor, finite-decoder, Karoubi, and Arrow routes without counting primitive G-122 syntax or fixed target A-B as discharged?"
  blocking_findings: []
  next_obligation: "replace the accepted-coordinate G-122 local fiber by independent primitive syntax, derive the fixed common data condition and reading from the target Sigma, D, and Lambda inputs, and construct target C base, observation, coefficient, normalization, and comparison-group compatibility"
```

## 未完了 ledger

- A の `Σ,D,Λ`、四族を同じ実現圏へ収録する構成。
- B の actual `Λ_Theta`・原始 reading `N_Theta` と、A由来の separation/assembly 放電。
  Cycle 19 は独立な restriction-diagram category と一般同値 spine、Cycle 20 は lens fiber と
  protocol named-state の actual finite slice、Cycle 21 は protocol 全executionのnon-discrete
  finite-state diagram、Cycle 22 は protocol branch の observation-aware local Hom と
  full faithfulness、Cycle 23 は同branchのobject assemblyと圏同値、Cycle 24 はactual finite
  decoderの計算式とKaroubi restriction・retract・Arrow coherence、Cycle 25はlens branchの
  finite-fiber Hom/object assemblyと圏同値、Cycle 26はlens branchのfinite decoder計算と
  Karoubi restriction・retract・Arrow coherence、Cycle 27はactual lens invertible changeの
  finite determinationと有限探索effectiveness、Cycle 28はactual protocol invertible
  changeのexact graph criteriaとeffectiveness、Cycle 29はgeneral observation-aware protocol
  Homのfull tagged tableによるfinite determinationと明示的有限data下のeffectiveness、
  Cycle 30はlens一般Homのfull fiber determinationとtotal effectiveness、Cycle 31はactual tagged
  source-choice Aut subgroupのone-object Hom sliceと独立local modelの同値に限る。Cycle 32では
  canonical normalization functorによるsingle normalized Karoubi object上の像がfull source-choice族を
  区別できないことをactual反例で固定した。Karoubi像の存在や他のsingle-object表現は棄却していない。
  Cycle 33では、正規化前のactual admissible-package categoryでfull source-choice族をfaithfulな
  自己同型族として収録し、同じ対象のcanonical normalizationと一様flipの三法則を接続した。
  Cycle 34では、そのambient package-level subgroupを全有限Bool-table整合族と直接同定し、
  actual package readbackの有限制限とsingleton assemblyによる逆をone-object圏同値まで接続した。
  Cycle 35では、canonical normalized-image mapの衝突をchoice restriction retractionの核として
  完全分類し、normalization-invariant choice上でのfaithfulnessを回復した。Cycle 36では、
  raw source-choiceとcanonical normalizationが生成するactual endomorphism submonoidを二構成子の
  一意なnormal formで完全表示し、四ケースの合成則と生成部分モノイドとの一致を証明した。Cycle 37では、
  normalization flagと全有限Bool-table整合族からなるfinite-local sectionを構成し、有限像上の
  normalization、成分ごとの合成、actual readback、separation/assembly、generated monoidとの同型を証明した。
  Cycle 38でこれをbranch-localなone-object圏同値へ持ち上げ、Cycle 39でcanonical normalizationに
  coverage・overlap・coefficient・raw・explicit realizationを与えてcommon tagged global fiberの
  actual Homとして構成した。Cycle 40でそのactual Homの冪等性と、任意source-choiceに対する
  canonical restriction合成則をexact-geometry全成分で証明した。Cycle 41でnormalizationを
  restricted source-choiceの後ろへ移すcanonical rewriteもcommon actual Hom等式として証明した。
  Cycle 42でtwo-constructor normal formをcommon tagged actual Homへfaithfulに評価し、そのactual
  image submonoidをpackage generated submonoidと同値にした。Cycle 43ではそのcommon exact imageから
  normalization flagと全有限tableをprimitive package base経由で直接読み、Hom separation/assemblyと
  one-object圏同値まで接続した。fixed common local-model categoryの任意対象assemblyは未完了である。
  Cycle 44では、そのrepresented exact圏をcommon realization familyのtagged fiberへ忠実に埋め込み、
  対象・射・恒等・合成とnormal-form評価の一致を固定した。represented image外のtagged Hom、
  arbitrary observation carrier全体の有限encoding、残る三族との統合は未完了である。Cycle 45では、
  common G-122 original-cell fiberをgenerated endpointsを持つ圏へ充満忠実に埋め、固定比較の
  direct/via-base対象と3比較をactual Homとして固定した。これはfinal four-family categoryの
  置換ではなく、G-122 finite probe、local-model同値、四族assemblyは未完了である。Cycle 46では、
  固定3コードのactual imageを意味上の2クラスからなる有限local valueと同値にし、Hom slice上の
  read/assemble両逆を放電した。Cycle 47では、`barAlpha`の逆像に取った2対象だけを読む
  primitive object probeを構成し、generated `barBeta`との実分離、complete probe agreementからの
  fixed image分離、primitive read/assemble両逆、Cycle 46 classifierとの一致を同じsurfaceへ接続した。
  任意のexpanded Homと対象に対する同値は未完了である。
- C の投影・正規化・比較群回復。Cycle 45で固定G-122の3比較はexpanded category内の
  actual Homになり、Cycle 46でその固定semantic imageの有限local recoveryを構成したが、
  Cycle 47でそのrecoveryをprimitive object restrictionから導出した。full comparison groupと
  base-fixing subgroupのlocal recoveryは未完了である。Cycle 48では、accepted source C2から
  任意のnormalized bottom comparison上のactual displayed lift orbitへの一意な組み立て、
  source乗法とlift作用の整合、identity fiberの既存source liftとの一致を証明し、
  Cycle 47のprimitive comparison復元と積の両逆へ接続した。full comparison group、full
  restriction kernel、full lift fiber全体の分類は未完了である。Cycle 49では、三軸のprimitive
  permutation codeとactual source-generated normalized-comparison imageの群同型、像の位数6、
  各像のcanonical section codeの一意性を証明し、各represented fiber上のfull actual kernel
  torsorへ同じ定理面で接続した。六要素像の外側を含むfull comparison group、full kernel要素の
  独立local recovery、arbitrary Hom、四族統合は未完了である。Cycle 50では、独立な三軸tableと
  `Fin 3` Extension forward/backward tableを組み合わせ、actual axis projectionとaxis除去後の
  stored backward-context actionから両成分を一意に読み戻した。read/assemble両逆、36要素性、
  canonical sectionのmixed code一意性、各represented fiberのfull-kernel torsor接続を同梱した。
  Cycle 51では、さらに独立な`Nat` exact-support/parity normal formを加え、carrier固有probeによる
  `Fin 3`成分との非干渉、actual observationからの三成分分離、read/assemble両逆を証明した。
  Cycle 50像をidentity `Nat` codeで埋め込み、source-owned `Nat` zero-one swapがその像外にあること、
  canonical section code一意性、各represented fiberのfull-kernel torsor接続まで同梱した。
  Cycle 52では独立な`Fin 4` tableをさらに加え、三carrierのprobe非干渉、actual観測からの
  四成分read/assemble両逆、Cycle 51像を保存する埋込みと明示的`Fin 4` swapによる非全射性、
  canonical section code一意性、各represented fiberのfull-kernel torsor接続を同梱した。
  Cycle 53では各four-component comparison fiberに独立なBool kernel codeを加え、source由来の
  actual restriction-kernel involutionによるcanonical/shifted orbitの分離、read/assemble両逆、
  xorとactual kernel乗法・lift作用の整合、comparison codeとの同時一意性、full torsor接続を同梱した。
  Cycle 54ではこの二要素codeにsource-ownedな群構造を与え、actual生成部分群との乗法同値、
  全部分群要素のread/assemble両逆、displayed orbit上の任意2点間の一意なactual変位、
  comparison code一意性との共通surfaceを同梱した。
  Cycle 55ではactual displayed imageを生成部分群作用の下で閉じ、ambient actual作用との一致、
  自由推移性、source左正則作用とのequivarianceを証明した。さらにfour-component comparison
  codeとsource kernel group codeの積から、comparison依存のdisplayed lift総空間全体への
  read/assemble両逆を構成した。
  Cycle 56では追加Extension carrierを特定の一型に固定せず、`Fin 3`、`Fin 4`、`Nat`と異なる
  任意の有限型へparameter化した。carrier固有probeと固定context同値による共役の単射性から
  actual stored-backward観測が全tableを分離することを証明し、comparison read/assemble両逆、
  任意の非自明な追加carrier上のswapによる旧像のproper inclusion、`Fin 5`具体例、
  canonical section code一意性を得た。同じmoduleで
  displayed orbit分離・両逆、ambient actual作用との一致、任意二点間の一意変位、equivariance、
  dependent total-space両逆まで接続した。
  Cycle 57ではprimitive Extension carrierの有限性を外し、任意の型`E`上の全置換がactual
  local-fiber kernelへ忠実に入ることをcanonical probeとstored-backward観測から証明した。
  source置換とactual像、actual像とobserved-action像の二つの乗法同値と両逆を構成し、
  `Nat` zero-one swapによる全finite-carrier像unionのproper inclusion、`Set Nat` complementが
  全exact-support像unionの外に残ることまで同じsurfaceへ接続した。
  Cycle 58では相異なる二つのprimitive carrier作用の可換性をsource・transport・actual kernelで
  証明し、その積群をactual kernel像、stored-backward観測像、canonical section後のexpanded direct像、
  normalized `barAlpha` comparison像のそれぞれと乗法同値にした。さらに任意single-carrier像を
  powerset carrier上の恒等作用を加えたtwo-carrier像へ収録し、`Nat` zero-one swapと`Set Nat`
  complementの同時作用が全single-carrier像unionの外にあることからproper inclusionを証明した。
  Cycle 59ではpairwiseに相異なる任意の有限carrier族について、非可換有限積としてsource作用と
  actual kernel作用を構成した。canonical probeによる全成分分離と、stored-backwardのopposite規約を
  unop・逆で戻すrecovery homからactual積の忠実性を証明し、kernel・stored-backward・expanded direct・
  normalized comparisonの四像へ乗法同値を構成した。さらに全two-carrier像をBool-index familyとして
  収録し、`Nat`、`Set Nat`、`Set (Set Nat)`を同時に動かす固定witnessでproper inclusionを証明した。
  Cycle 60ではfull raw comparisonをcanonical normalized comparisonと一意なfull restriction-kernel
  変位から明示的に組み立て、read/assemble両逆、共役で捻れた積公式、raw comparisonと全lift fiberでの
  kernel変位一意性を証明した。normalized factorをactual normalized source automorphism群へ接続し、その
  座標でも両逆を同梱した。full kernel要素の独立なprimitive local presentation、arbitrary expanded Hom、
  四族統合は未完了である。Cycle 61ではfull raw/normalized comparison群をdirect endpointの全自己同型群へ
  乗法同値で同定し、comparison restrictionとdirect normalizationの可換式を証明した。これによりfull
  comparison kernelとdirect normalization kernelの明示的な乗法同値・両逆を構成し、Cycle 60の
  read/assemble両逆、一意なkernel変位、共役で捻れた積をsource-kernel座標へ移した。direct normalization
  kernelのarbitrary要素をprimitive local syntaxから独立に再構成する義務は未完了である。Cycle 62では
  任意のnormalization fiberを保つ置換を、点対ごとのBool値と行・列の一意存在から独立に表示した。
  read/assemble両逆、全群との乗法同値、関係合成による積公式を証明し、direct normalization kernelの
  object作用をこの表示へ乗法的に接続した。source-authored ambient kernel元が非恒等graphを持つこと、
  trivial restrictionを持つ非恒等full comparison kernel元へ移ること、Cycle 61座標から両逆に回収される
  ことも同梱した。object作用が同じcomplete automorphismを分離する追加readingと、full kernelへのjoint
  assemblyは未完了である。Cycle 63では任意の型間の関数をdata/Prop分離したBool graphから両逆に
  再構成し、恒等・関係合成・graph圏・Typeへのfully faithful functorまで構成した。同じmodule群で
  任意G-122 geometry Homのsource・Atom・object・raw context・coefficientの5写像をgraphとして読み、
  pointwise recoveryと恒等・合成を証明した。固定有限比較ではaccepted object probeがgraph assemblyを
  経由することを示し、既存local imageのread/assemble両逆まで接続した。dependent operation・equation・
  invariant・axis・coordinate・support・observable・raw-relation成分を含むjoint separation/assemblyは
  未完了である。Cycle 64では、`GeometryTotalHom.ext`が使用する残りの計算成分をtagged sigma mapとして
  total-functional Bool graphへ載せ、bidirectional context actionからcontext equivalenceを回収し、
  graph族の一致が任意complete geometry Homを分離することを証明した。固定G-122 raw comparisonでは
  source complete-graph readingが全raw comparisonを分離し、full direct normalization-kernel座標を決定し、
  assembled codeのgraph一致とcode一致の同値を既存read/assemble両逆へ接続した。arbitraryな整合graph族の
  独立coherence条件とassembly、direct normalization kernel自体のprimitive local syntaxは未完了である。
  Cycle 65ではHom分離、Hom組立て、対象組立てを独立fieldにした一般再構成contractを構成し、
  Homの両逆・一意preimage・fully faithful・essentially surjective・圏同値と、その逆向きの特徴付けを
  証明した。primitive total-functional Bool graph圏をTypeと圏同値にする完全な適用を同梱し、Cycle 64の
  complete geometry graphは全package対に対するindexed Hom-family分離を放電することを明示した。
  Cycle 66では最上位十三fieldを持つraw complete graph bundleへ恒等射と合成を定め、primitive fieldの
  五graph codeへ成分別演算を委譲し、
  backward contextだけ順序を反転した成分別の圏を構成した。complete geometry readingが全dependent
  tagged成分で恒等射と合成を保存するunderlying-package-preserving functorであること、Cycle 64の分離から
  faithfulであること、対象組立て、および残るHom組立てがfullnessと同値であることを証明した。
  Cycle 67ではforward/backward Bool graphからなる`EquivGraphData`と相互逆式のPropを分離し、一つの
  graphからなる`RingHomGraphData`とzero/one/add/mul保存式のPropも分離して、それぞれ正負fixtureを
  与えた。bundled codeと`Equiv`、`RingHom`との
  read/assemble両逆、型同値、恒等・合成閉性を証明した。backward graphの逆順合成も明示し、raw
  complete graphへinverse graphだけを加えたdataと係数保存式を含むPropを分離したcoherenceからpointed Atom、upper Atom、
  equation-index、coefficientを組み立て、完成geometry射のreadingが各成分とforward/backward context
  object作用を回収することまで同梱した。Cycle 68では二方向のraw ring-hom graphと演算保存・相互逆式を
  分離して`RingEquiv`とのread/assemble両逆、正負fixture、恒等・合成を構成した。任意のindex関数上で
  ordinary equivalenceとring equivalenceのgraph code族をpointwise familyと型同値にし、dependent合成、
  sigma型上のtagged forward graphによる全fiber分離を証明した。同じmoduleでcomplete geometryの
  coordinate familyとequation-observable ring familyをこのcodeへ読み、pointwise assemblyとCycle 64の
  tagged graph fieldを同時に回収した。任意raw bundleのfullnessは主張せず、
  Cycle 69では双方向context graphのtotality・monotonicity・unit/counit四不等式からfunctorの射作用と
  圏同値を組み立て、read/assemble両逆、raw graph合成則、左右単位律、結合律まで閉じた。
  observable ring familyも同じcontext codeのassembled functorへ結び、restriction naturalityから
  presheaf natural isoを組み立ててactual complete geometry成分まで回収した。Cycle 70では
  operation・invariant・signature・support・axis・geometry-observable・raw transportを
  dependent graph codeと独立lawへ分け、一添字/二添字familyのread/assemble両逆とtagged分離、
  realization supplyの両逆・恒等・合成、actual complete-map graph七成分の一括回収まで同梱した。
  Cycle 71ではCycle 67・69・70ですでに内部data/Prop分離されたlaw-bearing codeを再利用し、Cycle 71固有の外側法則を別predicateに置いた。明示的なcoverage保存certificate、overlapの双方向比較をまとめ、
  overlap isomorphismを保持せずに組み立て、`PackageTotalHom`と
  `GeometryTotalHom`のread/assemble両逆、assemblyの単射性、accepted common complete-map graph面での
  分離まで同梱した。Cycle 72ではlawful complete code自体をHomとするpackage-indexed圏を構成し、
  輸送された恒等・合成のassemblyによる一意特徴づけ、圏法則、read/assemble関手、Hom分離・Hom組立てから
  actual geometry圏とのpackage-indexed圏同値を導いた。同じ圏からaccepted common graph圏への忠実関手も
  同梱した。Cycle 73ではpackageの9計算成分に対する恒等・合成dataを明示した。8成分はpredecessor演算、
  context/observableはassembled equation transportのreaderを使い、dependent operation・signatureの
  再添字付けを含むfieldwise分離後にcanonical certificateを輸送した。assembly公式、一意性、単位律・
  結合律、Cycle 72 complete恒等・合成のpackage射影との一致を同梱した。package context/certificateの
  direct closureはCycle 74で放電した。Cycle 74ではjoint context/observableの恒等・合成をlocal graph
  operationから構成し、packageの14法則を入力certificateから直接証明した。canonical readerはfieldwise
  comparisonだけに限定し、exact assembly・普遍性・圏法則とCycle 72/common graph接続まで同梱した。
  complete geometry外側のcoefficient・realization・coverage・overlap・raw coherenceはCycle 75で
  放電した。dependent package-base再添字付け、直接恒等・合成data、入力certificateからの外側法則閉性、
  local component計算によるexact assembly、任意candidateに対する普遍性、圏法則、Cycle 72/common graph
  接続を同梱した。Cycle 77でlens・protocolの独立local object/Hom assemblyを、Cycle 78で
  tagged・full G-122を含む四枝の直接assembly・両逆・圏同値を同じparameter面へ収録した。
  Cycle 79で四枝をexact fiberとするindexed total global/local category、直接Hom/object
  assembly、両逆、圏同値、投影、family接続を一つのmoduleへ収録した。
  ただしこれはaccepted branch typeの総和であり、固定targetの`Sigma,D,Lambda`から
  `R_Theta,M_Theta,N_Theta,D_Theta`を直接導く義務と、direct normalization kernel自体の
  primitive local syntaxは未完了である。
- D の共通 `FiniteReading` surface を A--B と E2 の各具体的 reconstruction obligation で使用する接続。
- E1 の actual source-choice Aut outputについて、index equality/membershipとcategorical packagingを含む計算可能な延長。
- E1b の finite-restriction reconstruction と B の主同値による source-choice recovery の
  package-level Hom-slice同定はCycle 34で接続した。Cycle 37のgenerated finite-local monoid同型を
  one-object圏同値として明示する義務はCycle 38で放電した。Cycle 78でcanonical-normalizationを含む
  full tagged generated categoryを四枝共通parameterへ接続し、同枝の直接Hom/object assemblyと両逆を
  放電した。case分岐ではない最終common local-model categoryへの統合は未完了である。Cycle 43で
  generated branchのcommon exact imageにも同じfinite-local one-object圏同値を移したが、四族統合や
  任意対象assemblyを代替するものではない。Cycle 44でそのexact imageからcommon tagged fiberへの
  忠実なinclusionを構成したが、common local-model category全体の同値はまだ主張しない。
- E2 の product-lens / protocol 可逆変更層はCycle 27--28で共通
  `FiniteReading`/Dへ接続済み。Cycle 29でgeneral observation-aware protocol Homも
  full tagged table上の決定性・effectivenessへ接続し、Cycle 30でlens一般意味保存射層も
  full fiber上の決定性・total effectivenessへ接続した。Cycle 77で両CS枝、Cycle 78で四枝parameterへ
  統合し、Cycle 79でindexed total categoryのprojectionと各fiberの正確な回収、tagged・
  G-122・decoder・Karoubi・Arrow経路の輸送を同梱した。固定targetからのprimitive
  common readingとdata condition、Cが求める底・観測・係数投影、正規化、全比較群輸送は未完了である。

## 独立検証：依存するraw局所表示（2026-09-20）

人間の指示により、Cycleには数えない設計検証として実施した。
Cycle 79の受理・停止状態を維持する。検証対象は
[承認済み設計コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711#issuecomment-5742767034)
の3節・4.2節にある、型参照を含むraw対象の組立てとraw等式の導出である。
GOALの固定target A–Eと最初の検証点全体の達成条件は維持する。

### 検証した構成と証拠

Lean file:
`research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentRawLocalValidation.lean`。
namespace: `AAT.AG.LocalSemanticReconstruction.IndependentRawLocal`。

| 検証項目 | 宣言と実体 |
| --- | --- |
| 対象の選択に先行する添字と値型 | `Query`、`Query.Value`。固定したsite上のcontext、候補の座標型・関係型、原始引数から添字を作る。値は型参照、label、有限supportの多項式とそのOption/ULift |
| 依存する型の有効・無効判定 | `IsTyped`。選択された型と一致するqueryだけが値を持つ。`read_isTyped`が任意のnative rawから条件を導く |
| 原始値からのraw対象の構成 | `coordinates`、`relations`、`variableImage`、`restriction`、`assemble`。完成したraw、relation family、restriction homを局所値には置かず、点値から組み立てる |
| 局所法則からnative法則への導出 | `IsLawful`、`maps_ideal`。生成関係式ごとの有限多項式和から全ideal保存を導き、変数上の恒等・合成式から全多項式上の式を導く |
| native法則から局所法則への逆方向 | `mem_JStruct_iff_finite_sum`、`read_isLawful`。ideal所属を有限和へ戻す。有限和の選択はProp内にあり、余分な対象データにならない |
| 依存するデータの復元 | `relation_heq_of_points`、`stable_heq_of_points`、`assemble_read`。座標familyの等式を使ってrelation/restrictionの依存を揃え、データ全体を復元する |
| 局所値の復元 | `read_assemble`。active値だけでなくinactive値も復元する。`rawTableEquiv`が両逆を束ねる |
| 有限片の貼り合わせ | `Fragment`、`Compatible`、`glue`、`fragments_glue`。singletonから組み立て、任意の有限片を回復する。`rawLocalEquiv`がnative rawと独立な局所族の同値を与える |
| 原始評価の有限support | `fragment_addresses_finite`、`polynomialMap_eq_of_vars`。各片の添字は有限であり、一つの多項式のrestriction評価はその有限な変数集合で決まる |
| G-122の厳密なraw等式への接続 | `raw_transport_eq_iff_points`。全queryの値の一致と`H.raw = rawTransport f h`が同値。`rawCoherent`に残っていた等式を原始評価から導くための補題 |

`rawLocalEquiv`の入力は任意のsite `S`と係数環 `k`であり、対象の量化は
`RawAmbientRestrictionSystem S k`の全体である。座標型や関係型を固定したり、
有限型だけへ縮小したりしていない。`S`自体はこの検証では入力として保持しており、
core・選択幾何からの再構成は未完了である。

### 成立・不成立の証拠

- `unitRaw`は任意のsite上で、整数係数、一つの座標、関係式`X = 0`を持つraw系を与える。
  `unitRaw_typing_witness`と`unitRaw_law_witness`が成立する条件を実際に発火させる。
- `eraseLabels_not_typed`は、選択された座標に必要なlabelが欠けるtableを排除する。
  このtableの有限制限同士は整合し得るため、restriction整合だけでは十分でないことも分かる。
- `replaceImages_isTyped`は、全変数像を`1`に変えても型条件は満たすことを示す。
  `replaceImages_not_lawful`は、整数係数で関係式`X = 0`の像が`1`になるため、
  **生成関係式の条件そのものから**このtableを排除する。証明は有限和の定数項を取って
  `0 = 1`を導き、恒等則の破壊だけには依存しない。
- `inconsistentFragments_not_compatible`は、singletonと大きい片でlabelを変える族を排除する。
- `read_assemble`は、inactive候補の任意応答や型の証明の選び方による余分な自由度を排除する。

### 前提の出所・使用先

| 前提・構成 | この検証での扱い | G-124に対する状態 |
| --- | --- | --- |
| `U`、`A`、site `S`、係数型`k`と`CommRing k` | raw構造の既存型が要求する入力。型・演算・restrictionの定義に使う | `U`等の入力の由来はAの宣言へ接続が必要。`A`・site・係数構造の局所再構成は未完了 |
| `IsTyped` | 原始型参照の一致を述べる局所条件。`read_isTyped`でnative側から放電 | raw部分の両方向を検証済み |
| `IsLawful` | 生成関係式・変数上の恒等・合成という局所条件。`read_isLawful`でnative側から放電し、`assemble`でnative全体の法則を構成 | raw部分の両方向を検証済み |
| 有限ideal witness | mathlibの`Finsupp.mem_span_range_iff_exists_finsupp`から導出。選択を対象のfieldに保存しない | 新しい有限性仮定を追加していない |
| `Compatible` | 有限片同士の原始値の等式。`fragments_compatible`と`fragments_glue`で両方向を示す | 完成対象や延長可能性を条件に使っていない |
| `PackageTotalHom f`、係数`RingHom h` | `raw_transport_eq_iff_points`で比較先を定めるための既存入力 | これらの全成分を局所Homから構成する接続は未完了 |
| 古典論理・選択 | 型の等号判定と依存するOptionの読取りに使用 | Dの実効性はこの構成から結論せず、別の証明義務として保持 |

基礎APIはnativeな`RawAmbientRestrictionSystem.ext`、
`TypedCoordinateRestriction.polynomialMap`、`GeometryTransport.rawTransport`、
mathlibのideal生成・多項式外延性・有限supportを使う。
受理済みの四族の枝同値や`ReconstructionData`は、このraw同値の入力に使っていない。

### 未完了の検証項目

最初の検証点全体は未完了である。残る作業は次のとおり。

1. 同じ型参照方式をcore、抽出、object formation、context、Law、coverage/overlapへ適用し、
   今回入力にしたsiteとその依存先を局所データから構成する。
2. 完全幾何の全許容Homを局所族から構成し、対象の同型、Hom両逆、恒等・合成まで接続する。
   taggedのexplicit方式のraw/realization輸送も接続する。
3. `raw_transport_eq_iff_points`の右辺を、局所Homのquery間の式として構成する。
   現在の補題は既存の`f,h`を受け取るため、この構成を代行したことにはならない。
4. 共通の`Σ,D,Λ`へ組み込み、四族の必須入力の由来・全対象・全射の対応を証明する。

今回の同値はraw対象の型の同値である。完全幾何の圏同値やG-124 A–Bの放電は未完了であり、
Cycle 79からの研究状態の昇格は行わない。PR・独立査読・検証ログの記録はtracking Issueへ接続する。

### 検証記録

- 検証開始base: `78534435b39c58cc94aaad65d38b3f30cc0913f7`。
- Lean: `4.28.0`、mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`。
- `research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentRawLocalValidation.lean`: pass。
- 明示した54宣言の`#print axioms`: 標準公理のみ。
- namespace全体の`#assert_standard_axioms_only`: 114宣言、標準公理のみ。
- 差分・未追跡fileを含むplaceholder、hidden/BiDi、privacy、語彙、Research import方向、
  `git diff --check`: pass。Research全体buildは実行していない。

### 継続実装：core生成の原始reading

人間から最初の検証点全体の完了とPR/Issue操作の許可を受け、同じ独立検証として継続する。
完了条件は承認済み設計の検証点I全体に置き、raw部分や以下のcore部品だけへ縮小しない。
Cycleは加算しない。

`IndependentCorePrimitiveReadings.lean`に、native coreの生成順序に沿う原始queryと構成を追加した。
以下はfocused Lean検証済みの実装証拠であり、正式PR査読による受理はまだ行っていない。
namespaceは`AAT.AG.LocalSemanticReconstruction.IndependentCorePrimitive`。

| 構成 | 原始値と局所条件 | Nativeへの接続 |
| --- | --- | --- |
| `Extraction` | Source・vocabulary・semantic reading・resolutionの選択値と型参照、4つのadmissionの点評価、normalizeの点評価。選択外の候補型ではpredicateはfalse、normalizeはnone | `readingEquiv`が選択sourceを含む全`ExtractionDoctrine`と両逆。`atomize_mem_iff`が4条件の連言からAtom族を生成 |
| `Composition` | 任意の有限Atom族とAtom対に対するrelation・identificationの評価。局所含意で両端のfamily所属を要求 | `readingEquiv`が全`CompositionReading`と両逆。供給されたfamilyそのものからconfigurationを作る |
| `ObjectFormation` | 各configurationに対するStructureMapsとSelectedQuantitiesの選択値・型参照 | `readingEquiv`が全`ObjectReading`と両逆。入力configurationを保持してarchitecture objectを構成 |
| `Operations` | 両端objectごとのoperation型参照と各Atomへの作用。family・relation・identification保存を点ごとに要求 | `readingEquiv`が全`OperationReading`と両逆。完成した`ConfigurationHom`を局所値に保存しない |
| `Generation` | 上記の抽出・composition・object formationを依存順に合成 | `object_read`が任意のnative `CoreReading`の生成objectそのものを回復。family・relation・identificationの評価式も明示 |

`SelectedValue`は一つのnativeな選択値とそのcarrier参照の依存対であり、完成coreや完成射ではない。
各queryのconstructorが元のfieldと評価引数を固定する。source型を任意関数として実行する汎用APIや、
任意のLean命題を法則として受け入れるconstructorは持たない。

生成familyの`ListFinite`はnative core readingにも要求される条件であり、`Generation.family_read_listFinite`
が元の条件を再構成先へ運ぶ。新たな有限carrierや選択済み有限列を対象データに追加しない。
有限familyの証明の選び方も両逆で消える。`Composition.trueTable_not_lawful`は空familyの外にrelationを
作るtableを排除し、`Extraction.eraseNormalization_not_typed`は選択sourceのnormalizeが欠けるtableを排除する。

この段階でLaw/observable系・circuit・invariant・signature、coverage/overlapの原始組立ては未完了である。
全core/siteの組立て、rawとの依存する接続、局所Homからの厳密なraw等式、
完全幾何の対象/Hom両逆・恒等・合成、G-122/tagged両方式、共通宣言・有限片への接続を引き続き構成する。

検証開始baseはraw独立検証のmerge commit `27a844fdd8812035c73575078a7ac6ed02b6a305`。
単一fileのfocused check、明示63宣言の`#print axioms`、namespace211宣言の標準公理監査を実行した。
Research全体buildは実行していない。

#### Context preorderと可変carrierの環

`IndependentContextPrimitiveReadings.lean`では、architecture object `A`上の全native contextを
queryの引数とし、preorderを選ぶ前にrefinementのpredicateとsupport・axis・observableの点評価を定義した。
3つのmapはrefinementが成り立つpairでのみactiveになる。反射・推移と各点の読み取り保存から、
nativeな`ContextPreorderCategory A`を構成する。非生成条件はcontext自身のfamily所属条件から導く。
`assemble_read`・`read_assemble`・`readingEquiv`は、refinementだけでなく選択された3つのmapをすべて回復する。
`noRefinement_not_lawful`は全falseのrefinementを、`eraseSupport_not_typed`は必要なsupport像の欠損を排除する。

`IndependentRingPrimitiveReadings.lean`は0・1・加法・乗法・負号の原始評価を用いる。
`IsLawful`の7つの等式からmathlibの`CommRing.ofMinimalAxioms`で全可換環構造を作り、
`CommRing.ext`により自然数/整数作用・べき・差などの補助演算も含めてnative構造を回復する。
`Carrier.readingEquiv`は型参照を局所値に含め、任意のcarrierを持つ全native可換環との両逆を与える。
完成した`CommRing`を局所値には置かず、候補型の各原始演算をOptionで読み、選択外の型はinactiveにする。

同fileの`Hom.readingEquiv`は任意の環準同型を、その点評価と0・1・加法・乗法の保存式から回復する。
`Hom.assemble_id`・`Hom.assemble_comp`により、点ごとの恒等・合成がnativeな恒等・合成へ写る。
係数写像の可逆性は要求しない。`eraseMultiplication_not_lawful`は、非自明環の乗法を全て0へ変えた入力を
単位元の式で排除する。

Contextの既存入力は`A`、固定carrier版の環の既存入力は型`K`であり、どちらも任意に量化する。
可変carrier版は`K`自体もtype-reference queryから構成する。今後、前段で生成した`A`へcontext構成を適用し、
各contextの可変observable環、restriction、violation、residualを組み合わせてequation systemを構成する。
この接続と最初の検証点全体の完了は未達であり、上記部品の正式PR査読も未実施である。

単一file検証と次段のimport用の単一module出力は両fileでpass。
明示宣言の公理監査はcontext 29件、ring 38件、namespace全体の監査はそれぞれ81件・108件である。
新規sourceのplaceholder・hidden/BiDi・privacy・語彙・整形scanを行った。Research全体buildは実行していない。

#### 方程式・回路・invariant・signature・選択幾何の原始評価

以下は同じ独立検証の継続であり、Cycleを加算しない。対象は任意のnativeな各構造であり、
特定fixtureの生成像へ限定していない。各componentの検証は通過したが、正式PR査読は未実施である。

| Source / namespace末尾 | 構成と証明 |
| --- | --- |
| `IndependentEquationPrimitiveReadings.lean` / `IndependentEquationPrimitive` | equation index/role、各contextのobservable carrierと環演算、restriction、violation、residualを点評価から構成。環保存・恒等・合成・二つの自然性からnative equation systemを作り、`assemble_read`・`read_assemble`・`readingEquiv`で全fieldの両逆を証明 |
| 同fileの`Circuit` | 有限detector codeだけを読む。`IsLawful`はaccepted matching datumごとのcontext/Atomにおける非零residualの存在条件。`assemble_sound`・`read_isLawful`・`lawful_iff_sound`がnative `Sound`との対応を証明。witness自体は対象dataに残さない |
| `IndependentInvariantSignaturePrimitiveReadings.lean` / `IndependentInvariantSignaturePrimitive` | `Invariants`はindex、function/predicateの種別、value carrier、各objectでの点評価を、`Signature`はaxis、依存coordinate carrier、selected、coordinateの点評価を読む。両namespaceの`readingEquiv`・両逆・`read_injective`が全native構造を回復 |
| `IndependentContextObjectPrimitiveReadings.lean` / `IndependentContextObjectPrimitive` | Support/Axis/Observableの型参照、原始Extensionの型と選択値、3種類のpredicate点評価からnative contextを作る。queryの宣言自体はarchitecture objectの選択に先行し、family所属条件を`IsLawful`に置く。`readingEquiv`が全context fieldを回復 |
| 同fileの`Overlap` | overlapの返すcontextを上記queryへ展開。support所属と4つの順序条件から`ContextOverlapPullback`を作り、`assemble_read`・`read_assemble`・`readingEquiv`で全選択を回復 |
| `IndependentCoveragePrimitiveReadings.lean` / `IndependentCoveragePrimitive` | 元の9述語を保持。candidate equation index/axisとrequired roleによるactive条件を明示し、`readingEquiv`が全`CoverageRequirements`を回復 |

namespaceの共通prefixは`AAT.AG.LocalSemanticReconstruction`である。
Equation/Coverageのqueryはarchitecture objectを既存parameterとし、選んだequation systemやsignatureを
query型へ埋め込まない。Overlapの順序条件は前段で構成したcontextの値を引数にする。
これらの依存するinstanceを共通有限queryへ接続する義務は後段に残る。

誤入力の検査として、Equationの`eraseRestrictions_not_typed`は反射context上で必要なrestriction応答の欠損を、
Signatureの`eraseCoordinates_not_typed`は宣言済みcoordinateの欠損を、Invariantsの
`eraseFunctionValues_not_typed`はfunction種別のvalue欠損を排除する。
Coverageの`nonrequired_rejected`はrequired以外のequationをrequired coordinateとして選ぶtableを排除する。
設計で指定された全反証scenarioの統合検査は未完了である。

#### 完全なcoreとrawを含むgeometry objectへの依存する接続

`IndependentCoreTableAssembly.lean`のnamespace `IndependentCoreTableAssembly`に、次の接続を置いた。

- `equationReadingEquiv`: primitive context、equation、circuit tableを依存順に組み合わせ、完全な
  `EquationReading`と対応させる。circuit側の条件は上記の非零witness条件を用いる。
- `finiteExtractionEquiv`・`foundationEquiv`: 選択sourceの元の有限family条件をPropとして保持し、
  extraction・composition・object formation・invariant・signature・operationの原始tableを組み合わせる。
- `generatedObject_eq`: この組合せが`IndependentCorePrimitive.Generation.object`そのものであることを示す。
- `coreEquiv`・`assemble_read`・`read_assemble`: 全`CoreReading`と依存primitive tableの両逆。
- `packageEquiv`・`assemblePackage_readPackage`・`readPackage_assemblePackage`: 元の2つのAtom法則を含む
  全`AATCorePackage`との両逆。`package_object`は生成objectとequation tableの添字objectの一致を示す。

`IndependentGeometryTableAssembly.lean`のnamespace `IndependentGeometryTableAssembly`では、このcore構成に
原始coverage/overlap、可変carrierの係数環、受理済み`IndependentRawLocal.rawTableEquiv`を依存順で接続した。
`objectEquiv : ReadingCore.{u,v} U ≃ ObjectData.{u,v} U`は任意のAtom carrier `U`、任意の係数universe `v`について
成り立つ。`assemble_read`・`read_assemble`がrawを含む全fieldの厳密な両逆を、`read_injective`が全fieldの分離を示す。
`core_assemble`・`geometry_assemble`・`coefficient_assemble`は実際のcomponent構成への評価式である。

この`ObjectData`は、完成したcore/geometry/ring/rawを値として保持する五fieldの再包装ではない。
保持するdataは各原始queryへの点応答であり、上記component assemblerからnative構造を作る。
`nativeEquiv`等のnative構造の分解は比較証明だけに使い、局所response型には入れない。
依存するSigmaの添字変更にはmathlibの`Equiv.sigmaCongrLeft'`・`sigmaCongrRight`を用いた。

ただし、現在の`ObjectData`は前段の組立結果に依存するtableの型である。
実現の選択に先行する共通宣言・有限図式・局所値型は未完成であり、これをその代用として受理しない。
最初の検証点Iを閉じるには、この依存する構成への共通有限tableからの接続、各原始式の有限support、
局所Homからの元と同じ厳密なraw等式、G-122/taggedの両Hom方式と全Hom両逆・恒等・合成、
指定反証scenarioと正式査読が引き続き必要である。外側のtotal categoryやrouting wrapperは追加していない。

6つの新規sourceを個別に検証した。明示宣言の`#print axioms`は順に47・44・33・13・36・24件、
namespace監査は123・137・114・75・36・24件で、標準公理のみである。
既存のResearch module manifestとaggregate importへ登録したが、aggregate自体のelaborationと
Research全体buildは実行していない。新規sourceのplaceholder・hidden/BiDi・privacy・語彙・整形scanも行った。

#### 両方式の全Hom再構成と有限なcontext作用の合成

同じ独立検証の継続として、次の5つのsourceを追加した。Cycle 79を維持する。
以下のLean検証は通過したが、正式PR査読による受理は未実施である。
各namespaceのprefixは`AAT.AG.LocalSemanticReconstruction`。

| Source / namespace末尾 | 構成と証明 |
| --- | --- |
| `IndependentRepresentativeHomReadings.lean` / `IndependentRepresentativeHom` | `transportTable`がinverse context作用と係数mapから各raw応答を直接計算。`raw_eq_iff_points`で元の厳密なraw等式を導く。package・係数・representative realizationの既存graph構成と接続し、`homEquiv`・`assemble_read`・`read_assemble`で全`GeometryTotalHom`を回復。`assemble_id`・`assemble_comp`は既存の直接graph合成との接続 |
| `IndependentExplicitRawReadings.lean` / `IndependentExplicitRaw` | coordinate・依存LocalData・relationの両方向graph、labelとrelation polynomialの点等式、variable imageのsquareからnative raw mapを構成。多項式の自由性で全多項式の自然性へ延長。`readingEquiv`・両逆・`read_injective`が全`RawAmbientRestrictionSystemExactMapAgainst`に成り立つ |
| `IndependentExplicitRealizationReadings.lean` / `IndependentExplicitRealization` | 3つのcarrierの両方向の点値と、実際の`ContextMorphism`への3成分の作用を保持。局所逆式・reading保存・自然性からrestriction保存も導く。`readingEquiv`・両逆で全native supplyを回復。`identityTable`・`composeTable`と`assemble_id`・`assemble_comp`が点合成をnative合成へ接続 |
| `IndependentExplicitHomAssembly.lean` / `IndependentExplicitHom` | package graph、係数graph、上記raw/realizationの局所データ、9つのcoverage含意、overlapの両順序比較を依存順に接続。`homEquiv`・両逆・`read_injective`で全`ExplicitExactGeometryHom`を回復。`base_assemble`・`coefficient_assemble`・`raw_assemble`・`realization_assemble`が各component assemblerへの評価式 |
| `IndependentHomRefutations.lean` / `IndependentHomRefutations` | 任意のcore・選択幾何上に、関係式`X=0`を持つrawを構成。`ℤ × ℤ → ℤ`の第一射影が非単射であり、両Hom方式の読み取り・組立て後にもそのまま残ることを証明 |

representative方式の`Code`はraw全体系の等式をfieldに保存せず、各原始queryの比較を保持する。
`complete`はその比較から旧certificateの厳密なraw等式を導く。
explicit方式の`Data`は完成したbase Hom、raw map、realization supplyをfieldに保存しない。
nativeな依存Sigmaの分解は比較証明で使い、出力の各fieldは原始graph・点tableとその局所条件から作る。
両方式のraw/realizationの意味を同一化していない。

explicit realizationの合成では、次の射のqueryへ前のcontext作用全体を渡さない。
例えばsupport作用は、後段の逆support像、前段の実際のcontext作用の一点、後段のsupport像という
3点から計算する。`read_comp`が自然性と両逆からnativeの合成との一致を示す。
`composeTable_finite_support`は、9種類のqueryの各constructorについて、2つの入力tableの
合計3点以下が一致すれば合成結果が一致することを証明する。
この定理は任意のtableを比較し、比較先tableのlawfulnessを追加仮定にしない。
ただしbase Hom `f,g`は固定しており、共通queryへのbase成分の有限support接続は後段に残る。

反証検査は以下を追加した。

- `changedPolynomialData_not_lawful`: 同じcoordinate・LocalData・relation名のidentity graphでも、
  元の関係式`X`を`1`へ変えたtargetではrelation保存を満たさない。両端raw対象自体はlawfulである。
- `finite_support_action_rejected`: 任意のcore上の2-support contextで、実際のswap射への作用だけを
  identityへ変えると自然性で落ちる。carrier同値はidentityのまま保つ。
- `coefficient_swap_not_lawful`: 受理済みの非対称raw fixtureの係数swapを、新しいraw点比較で排除する。
- `explicit_reconstruction_noninjective`・`representative_reconstruction_noninjective`: 係数の
  `(0,0)`と`(0,1)`を区別しない射影が両方式の再構成で保持される。

現在の全Hom両逆は任意のnativeな完全幾何の両端をparameterとする。
前段の`ObjectData`から構成した両端にも適用できるが、それだけでは共通有限tableからの
対象/Hom再構成の完了根拠にならない。最初の検証点Iを閉じるための未完了項目は次である。

1. 実現の選択より前に共通query・有限図式・局所値型を宣言し、型参照のactive/inactive条件と
   全原始式の有限supportから、既存の依存するobject/Hom構成へ接続する。
2. 共通の局所射について恒等・合成と両逆を接続する。explicit側ではraw・baseの合成も含む
   全Homの局所合成が未接続であり、realization単独の点合成では代行しない。
3. 共通の宣言に対して指定反証scenarioを統合し、完成fieldの混入、全Homの分離、
   witness選択による余分な対象/自己同型がないことを検査する。
4. 固定headのPR、標準の独立4本査読、root acceptance、CI、merge、Issue記録を完了する。

外側のtotal categoryやrouting wrapperは追加していない。GOALカードは変更していない。

5つのsourceの単一file検証はpass。明示宣言の`#print axioms`は表の順に27・33・29・21・11件
(計121件)、namespace監査は35・52・107・28・11件(計233件)で、標準公理のみである。
Research module manifestとaggregate importへの登録、placeholder・hidden/BiDi・privacy・語彙・
整形scanも確認した。aggregateのelaborationとResearch全体buildは実行していない。

#### 多項式の閉じた原始式と有限support

`IndependentPolynomialExpressions.lean`は、共通有限queryへ接続するための算術部分を構成する。
namespaceは`AAT.AG.LocalSemanticReconstruction.IndependentPolynomialExpressions`。
`Query C k R`は原始carrierだけをparameterとし、係数像・変数像・zero・one・add・mulの6種類を持つ。
tableの各値は`R`の一点であり、`Expr C k`はその6種類だけからなる有限構文である。
完成した環、写像、任意の関数・命題を式のconstructorへ渡すfieldは持たない。

`evaluate`と`support`を構文再帰で定義し、`evaluate_eq_of_support`をconstructorへの帰納法で証明した。
supportは途中の加算・乗算の引数も含む。比較するtableには環法則を仮定しない。
したがって係数像と変数像だけを固定し、実際に使う環演算を無条件に固定扱いする証明にはなっていない。

`compile`はnative polynomialの有限supportから式を生成する。
`evaluate_compile`は任意の係数準同型と変数像についてnative `MvPolynomial.eval₂Hom`との一致を示す。
`polynomial_finite_support`は、そのnative評価を回復する有限な原始query集合を構成する。
`evaluate_rename_map`は係数base change後のcoordinate renameも同じ評価式に接続する。
有限リストは元のpolynomialから生成し、局所対象の追加選択として保持しない。

さらに`Sparse C k z`は、原始carrier `C,k`とcandidate zero `z : k`だけで有限多項式の値型を定義する。
宣言時に完成した`CommRing k`や`CommSemiring k`を要求しない。
`sparseEquiv`と`Sparse.toNative`・両逆は、candidate zeroと実際のzeroの一致後に
元のnative polynomialを全係数・指数込みで回復する。これにより、後続の共通raw queryで
係数環を選ぶ前に値型を宣言するための部品を得た。

この算術部分は単一file検証済みである。共通queryの全体宣言、core/contextの型参照、
有限図式からの全object/Hom構成への接続は引き続き未完了であり、最初の検証点Iは未達である。
明示25宣言の`#print axioms`とnamespace108宣言の監査は標準公理のみ。
module登録と差分scanを確認し、Research全体buildは実行していない。

#### 実現の選択に先行する共通queryと完全対象の有限片

同じ独立検証の継続として、共通queryの添字・値型を、選択されたcore/site/係数環から切り離した。
Cycle 79と固定GOALカードを維持し、正式PR査読による受理はまだ行っていない。
先の「共通queryとobject接続は未完成」という進捗記録に対し、この節が追加の証拠を記録する。
各namespaceのprefixは`AAT.AG.LocalSemanticReconstruction`。

| Source / namespace末尾 | 構成と証明 |
| --- | --- |
| `IndependentRawCandidateReadings.lean` / `IndependentRawCandidate` | `Query A`はcandidate architecture参照だけを受け、site・preorder arrow・係数環を受けない。raw polynomial値はraw carrierとcandidate zeroによる`Sparse`。imageの添字はcontextの対とし、readabilityは後から点のactive条件で判定。`lower`・`raise`・両逆、`rawTableEquiv`・`assemble_read`・`read_assemble`が元の全raw系を回復 |
| `IndependentGeneratedObjectMatching.lean` / `IndependentGeneratedObjectMatching` | family・configuration・architecture-object候補との一致を、原始admission・relation・選択値の点条件で判定。不一致には具体的な点の反証を要求。`family_iff`・`configuration_iff`・`object_iff`で生成参照との一致を導き、`eq_read`・`unique`で照合表の自由度を排除。`generated_object_active`で全域の存在条件をfieldに置かずactive参照を導く |
| `IndependentOverlapCandidateReadings.lean` / `IndependentOverlapCandidate` | overlap結果を原始context fieldに分解し、candidate contextとの一致を各点で検査。`ContextMatch.matches_iff`・`eq_read`で照合flagを一意に決定。4つの順序条件はcandidate contextを直接引数に取り、`originalLaws`で元のoverlap条件へ戻す。`readingEquiv`・両逆で全native overlapを回復 |
| `IndependentGeometryPrimitiveDeclaration.lean` / `IndependentGeometryPrimitive` | `Query U`はextraction・composition・formation・invariant・signature・operation・circuit・coefficient・matching・candidate objectの原始点という固定constructor群を持つ。全native実現で同じ添字・値型を使う。candidate objectの応答は単一flagでactiveになり、`inactive_eq_none`で非active応答を一意に固定 |
| `IndependentGeometryPrimitiveAssembly.lean` / `IndependentGeometryPrimitive` | `FoundationLaws`・`DependentLaws`・`IsLawful`は各原始投影の型条件と元の法則を検査。`stages`が全fieldを構成し、`flatten_stages`・`stages_flatten`で既存の依存する段階別表示と両逆を証明。`objectEquiv`・`assemble_read`・`read_assemble`・`read_injective`がraw込みの全native対象へ成り立つ |
| `IndependentGeometryFiniteFragments.lean` / `IndependentGeometryPrimitive` | 同じ`Query U`上の有限な依存tableを`Fragment`とし、包含の共有点一致を`Compatible`で定義。singletonの`glue`と`fragments`が両逆。`finiteObjectEquiv`と両逆が、全てのlawfulな有限片の族と元の完全対象を対応させる |
| `IndependentOverlapFiniteExpressions.lean` / `IndependentOverlapFinite` | refinement・matching・context一点比較・guard付きsupport admission・論理結合という閉じた`Expr`を定義。`evaluate_iff_of_support`をconstructorへの帰納法で証明。`lawful_iff_expressions`は新しいoverlapの全法則をこの有限式の各instanceと正確に同定し、`evaluate_iff_of_commonSupport`が共通query上の有限supportへ接続 |

`IndependentGeometryTableAssembly.GeometryData`と`RawData`も、上のcandidate overlap/raw表へ接続した。
この段階別表示は比較証明に用い、共通の局所値型には完成core・site・係数環・raw系を格納しない。
`ArchitectureObject`・contextなどのcandidate参照は、設計が指定したnativeな原始引数の参照であり、
選択済みの`ReadingCore`や`GeometryPackage`を共通queryのparameterにしていない。

照合の局所条件には、完成した対象やcontextの組立て結果への全体等式を置かない。
一致は各原始点の比較、不一致は一つの異なる原始点で検査し、その後で参照の一致を定理として導く。
対象の両逆は照合flagと非active応答も回復するので、照合のためのmetadataや存在証明の選択が
元の意味にない対象の区別を生まない。

有限片の存在・整合性から法則を自動的に結論していない。
`eraseMatching_fragments_compatible`と`eraseMatching_not_lawful`は、照合flagを全falseにした場合、
全ての有限restrictionは整合していても局所法則を満たさないことを同じ共通宣言上で示す。
`LocalObject`は`Compatible`と、singletonから読んだ原始値に対する`IsLawful`を別々に要求する。

overlapの各順序instanceは、結果contextを無限個のpredicate値から式中で組み立てる必要がなくなった。
そのcandidate参照のmatching flagと、有限個のrefinement queryから評価する。
`supportAdmission`はcandidate support carrierの宣言と、そのsupport/Atomの一点だけを読む。
`lawful_iff_expressions`はsupport・正の照合・負の照合の反証witness・4つの順序条件を全て含む。
個々の式の有限性を示しており、全引数に量化した法則全体の有限性やcarrier全体の有限性は主張しない。

最初の検証点Iは引き続き未完了である。残る主要項目は次である。

1. 共通宣言上で、overlapと算術以外を含む全原始式の有限supportを固定し、各object/Hom局所法則の
   全instanceへ接続する。有限族のgluingだけでは、この義務を代行しない。
2. 両Hom方式の原始query・型参照をnativeな完成両端や選択済みbase Homより前に宣言し、
   既に証明した全Hom両逆へ接続する。共通object宣言の完成だけではHomの共通宣言を代行しない。
3. 共通局所射の恒等・合成、特にexplicit raw・baseを含む全成分の点合成と有限片の合成を接続する。
4. 指定反証scenarioを共通宣言へ統合し、全Hom分離・型不一致・片側overlap・witness選択などを検査する。
5. 固定headのPR、標準の独立4本査読、root acceptance、CI、merge、Issue記録を完了する。

今回の8つの対象sourceは単一fileで検証した。明示宣言の`#print axioms`はraw candidate 27、
generated matching 17、共通宣言24、更新したgeometry stage 24、共通assembly 43、finite fragments 20、
overlap candidate 21、overlap有限式21件の計197件。namespace監査は同順79・54・130・24・74・20・57・77件の
計515件で、標準公理のみである。module manifestとaggregate importに登録し、aggregateのelaborationは
行っていない。Research全体build、外側のtotal category、routing wrapperは追加していない。

#### Homのcarrier選択に先行する点対graph

`IndependentCarrierGraphReadings.lean`は、Homの共通宣言へ接続する点対graphの部品を構成する。
namespaceは`AAT.AG.LocalSemanticReconstruction.IndependentCarrierGraph`。
`Query`はsource/targetのcandidate raw carrierと一点対だけを持ち、全応答はBoolである。
選択された二つのcarrierはquery型のparameterにせず、`IsTyped`の非active条件と
`IsTotal`の行ごとの唯一出力条件に現れる。

`graphEquiv`が受理済みの`PrimitiveFunctionGraph.GraphCode`と接続し、`functionEquiv`・
`assemble_read`・`read_assemble`が任意の有向写像との両逆を与える。
単射・全射・可逆性を要求しない。`mismatched_carrier_rejected`・`duplicate_outputs_rejected`・
`false_table_rejected`が、それぞれcarrier不一致・二重出力・入力点がある場合の全falseを排除する。

`compose`は第一のgraphの唯一出力を中間点として、第二のgraphの一点を読む。
`compose_finite_support`は全queryについて、二つのtableの合計2点以下を構成する。
比較する第一のgraphには同じcarrier上のtotality/uniquenessを要求するが、第二のtableにはlawfulnessを
仮定しない。第一のgraphで中間点への辺が真であることが、その点の選択に依存しない根拠である。
`compose_isLawful`・`assemble_compose`・`read_compose`、恒等の両単位則、`compose_assoc`まで接続した。

この部品は単一file検証済みで、明示39宣言の`#print axioms`とnamespace52宣言の監査は標準公理のみ。
module登録とsource scanを行った。各native Hom roleの型参照、保存則、全Homの共通宣言への接続は
後続の義務であり、この任意写像の部品を全Hom再構成の完了とは扱わない。Cycle 79を維持する。

#### 共通Hom宣言とAtom・生成則・context・operationの接続

独立検証の継続として、nativeな完成両端やbase Homを選ぶ前に、両Hom方式の共通queryを宣言した。
`IndependentGeometryHomPrimitiveDeclaration.lean`の`Query U mode`は、source、pointed/upper Atom、
object、invariant、operation、signature、coefficient、輸送照合、候補objectに依存する各点を持つ。
全応答はBoolである。representativeのrealizationは有向写像、explicit側はcarrier同値と
実際の`ContextMorphism`への点作用を持ち、後者にだけraw同値のqueryを用意する。
この宣言自体は`defined only`であり、全Homとの両逆は後続の接続義務である。

| Source / namespace末尾 | 証明した対応 |
| --- | --- |
| `IndependentInverseGraphReadings.lean` / `IndependentInverseGraph` | 二つのcandidate carrier graphと一点対のinverse条件からnative同値を構成。`readingEquiv`・両逆は非active carrier応答も回復。`inverse_iff_of_support`は任意tableの二点一致からinverse instanceの一致を導く |
| `IndependentGeometryHomAtomReadings.lean` / `IndependentGeometryHomPrimitive.Atom` | 共通Homのpointed/upper Atomをそれぞれ行の唯一出力と二点inverse条件から構成。`pointed_eq_upper`が点の一致からnative同値の全体一致を導く。`mismatch_rejected`が一つの異なる点を排除 |
| `IndependentGeometryHomTransportMatching.lean` / `IndependentGeometryHomPrimitive.TransportMatch` | family/configuration輸送のflagを、membership・relation・identificationの点比較と不一致witnessで検査。`family_iff`・`configuration_iff`が元のdirect-image輸送との一致を導く。`completeMatching_isLawful`・`completeMatching_eq_self`で照合metadataの選択自由度を排除 |
| `IndependentGeometryHomCoreLaws.lean` / `IndependentGeometryHomPrimitive.CoreLaws` | source行と正規化点、四つのadmission、compositionのrelation/identification、formationの二つの選択値から、元のnormalize/extraction・family・composition・object formation・configuration保存を導く。`extractionLaws_of_native`・`generationLaws_of_native`が逆方向も示す |
| `IndependentGeometryHomContextReadings.lean` / `IndependentGeometryHomPrimitive.Context` | 共通context queryの両方向行、単調性、unit/counitの両向き順序比較を旧thin-equivalence graphへ接続。`readingEquiv`・両逆で全native context圏同値を回復。object上の逆写像等式を追加していない |
| `IndependentGeometryHomContextExpressions.lean` / `IndependentGeometryHomPrimitive.ContextFinite` | source/target refinementとHom context点、論理結合だけからなる閉じた式を構成。`evaluate_iff_of_support`は共通object/object/Hom queryの三つの有限集合上の一致から任意tableで評価一致を示す。`lawful_iff_expressions`がcontext Homの全局所法則を各instanceへ接続 |
| `IndependentIndexedCarrierGraphs.lean` / `IndependentIndexedCarrierGraph` | 候補index対のgraphがdependent carrierの行をactiveにする。`readingEquiv`・両逆が全有向fiber写像と、非active index/carrierのfalse応答を回復 |
| `IndependentGeometryHomOperationReadings.lean` / `IndependentGeometryHomPrimitive.Operation` | 共通object graphの両端像からoperation行を選び、全native有向operation familyへ両逆を接続。単射・全射は要求しない。operation自然性はこのfamily再構成とは別の保存則として残る |
| `IndependentRingCarrierGraphs.lean` / `IndependentRingCarrierGraph` | candidate carrier graphにzero/one/add/mulの点保存則を課して全native環準同型との両逆を証明。inverse点条件を追加した場合は全native環同型との両逆を証明。環演算を原始点tableから作る場合も`function_laws`で接続。共通Homのcoefficient/observable roleへの組込みは後続 |

coreの抽出条件は、native定義の`normalize source`に対する四つのadmissionを比較する。
未正規化sourceでのadmission保存を要求する強化はしていない。
whole family/configuration輸送等式は局所条件のfieldに置かず、点の比較から証明する。
各有限witnessの存在はPropに置き、選んだwitnessを追加データにしない。

この段階では共通宣言への主要な接続が進んだが、最初の検証点Iは未完了である。
残る主な義務は、equation/observable・invariant/signature・coefficient・coverage/overlap・
両方式のraw/realizationを同じ共通Hom tableから組み立て、全Homとの両逆を統合すること、
全原始法則の有限support、共通の恒等・合成、指定反証scenarioの統合、およびPR査読・CIである。
既存のnative両端に相対的な全Hom両逆を、その共通table接続の代わりには扱わない。
Cycle 79と固定GOALカードを維持し、外側のtotal categoryは追加していない。

今回の10 sourceはそれぞれ単一fileで検証した。明示151宣言の`#print axioms`と
namespace内534宣言の監査は標準公理のみであり、warningは残していない。
module登録、placeholder・hidden/BiDi・privacy・語彙・差分整形scanを確認した。
aggregateのelaborationとResearch全体buildは実行していない。

#### 依存するinverse行とobservable family

`IndependentIndexedInverseGraphs.lean`は、有向index graphで選んだfiberごとの同値を、
candidate carrierの両方向graphと一点対のinverse条件から構成する。
index map自身の単射性・全射性は要求しない。`readingEquiv`・両逆は、activeな両方向graphと、
非activeなindex/carrierのfalse応答を全て回復する。

`IndependentGeometryHomInverseRows.lean`は、共通Homのbackward queryがsource/target順を保つことと、
独立inverse graphのbackward queryがtarget/source順を取ることを、一点対の`reverse`で接続する。
`asInverse_fromInverse`・`fromInverse_asInverse`がこの変換の両逆を証明する。
equation、observable、signature coordinate、explicit rawのcoordinate/local data/relationの各roleを
この変換へ明示的に接続した。queryの向きを完成した写像の引数へ隠していない。

`IndependentIndexedRingGraphs.lean`は、この依存するinverse行にprimitiveなring点保存則を加え、
全native環同型familyとの両逆を証明する。
`IndependentGeometryHomObservableReadings.lean`は共通Homのobservable行へこれを適用する。
`context_index_eq`は、contextの唯一出力で選んだraw contextと、復元したnative functorの像との
一致を示す。`nativeFamilyEquiv`で依存する型を輸送し、`readingEquiv`・`assemble_read`・
`read_assemble`・`read_injective`が全native observable環同型familyと共通候補行を対応させる。

`atPair_forward_iff`・`atPair_backward_iff`は、各true context対で復元した環同型と
共通Homの両方向点を同定する。`assemble_eq_atPair`によりnative familyの成分も同じ点対へ接続する。

#### Observableの自然性とequation transportの全field

| Source / namespace末尾 | 局所条件からの構成と逆方向 |
| --- | --- |
| `IndependentGeometryHomObservableNaturality.lean` / `IndependentGeometryHomPrimitive.ObservableNatural` | `PointLaws`はsource/target restrictionの各1点、contextの2点、observableの入力・出力各1点だけを比較する。candidate carrierの正しさは元のequation typingから導く。`points_iff_nativeNaturality`が、復元したcontext functorと二つのequation systemのnative restriction自然性との同値を示す |
| `IndependentGeometryHomObservableExpressions.lean` / `IndependentGeometryHomPrimitive.ObservableFinite` | 閉じた`Expr`と共通object/object/Hom query上の`support`を構成する。`evaluate_iff_of_support`は任意tableでの有限support上の一致から評価一致を示し、`pointLaws_iff_expressions`が全restriction instanceをその式へ接続する |
| `IndependentGeometryHomEquationLaws.lean` / `IndependentGeometryHomPrimitive.EquationLaws` | `RolePoints`・`ViolationPoints`・`ResidualPoints`はcandidate carrier、原始応答、Homのtrue点対だけを使う。`role_points_iff`・`violation_points_iff`・`residual_points_iff`が、復元したequation/Atom/object/context/observable作用のnative保存式との両方向を示す。object作用には単射・全射を追加しない |
| `IndependentGeometryHomEquationAssembly.lean` / `IndependentGeometryHomPrimitive.EquationAssembly` | 4つの点保存則と各成分の原始行から、`assemble`がnativeな`EquationSystemExactTransport`の全fieldを構成する。`contextObservableCode`で既存package assemblerのcontext/observable graphへ接続し、context選択とobservable familyの評価一致を証明する。3つの`read_assemble_*`がcontext・equation・observableの全候補行を回復する |
| `IndependentGeometryHomEquationExpressions.lean` / `IndependentGeometryHomPrimitive.EquationFinite` | 原始equation応答と共通Hom点だけをleafとする閉じた式を構成する。role・violation・residualの全instanceを有限supportに接続し、activeな共通object行で元の点保存則と一致することを示す |

この構成で使うequation objectのtyping/ring/restriction法則は、共通object再構成で既に対応した
native objectの法則である。Hom側のcontext・equation・Atom・object・observable行の条件は、
各成分の全native写像との両逆で対応を確認した方向仮定である。
新たな4つの点保存則はnativeのrole・自然性・violation・residualの各fieldと同値であり、
native保存式を追加の未放電fieldとして持たせてはいない。
全Homへの適用では、これらの行を同じ共通tableから取得する接続を引き続き完了させる必要がある。

最初の検証点Iは未完了である。残る主要項目は、invariant/signature・operation自然性・
detector code・coefficient・coverage/overlap・両方式のraw/realizationを共通Homへ統合すること、
全Hom両逆、残る全原始式の有限support、共通の恒等・合成、指定反証scenario、PR査読・CIである。
Cycle 79と固定GOALを維持し、今回の作業は独立検証として扱う。

今回の9 sourceは単一fileで検証した。明示宣言の`#print axioms`は、上の依存inverse・
inverse row変換・依存ring・observable family・自然性・自然性の有限式・equation保存則・
equation assembly・equation有限式の順に11・12・7・16・11・8・17・11・16件、計109件である。
namespace監査は同順28・12・13・16・11・58・17・19・60件、計234件で、全て標準公理のみ。
warning、placeholder、hidden/BiDi、privacy、追加文の語彙、差分整形、module登録を確認した。
aggregateのelaborationとResearch全体buildは行っていない。

#### Signatureの候補軸・座標行と保存則

`IndependentCandidateIndexedInverseGraphs.lean`は、外側indexのcandidate carrierもqueryへ含め、
内側fiberのcandidate carrierと合わせて二段階の型参照を扱う。
`readingEquiv`・両逆が、選択された外側carrier上の全fiber同値と、その他のfalse応答を回復する。

`IndependentGeometryHomSignatureReadings.lean`はこの構成を共通Homのsignature座標行に適用する。
`axisMap`は有向graphから構成し、軸の単射性・全射性を課さない。
`atPair_forward_iff`・`atPair_backward_iff`・`assemble_eq_atPair`により各true軸対の座標同値を
native familyへ接続し、`readingEquiv`・`read_assemble`・`assemble_read`・`read_injective`が
外側の軸carrierと内側の座標carrierを含む全候補行との両逆・分離を与える。

`IndependentGeometryHomSignatureLaws.lean`の`SelectedPoints`・`CoordinatePoints`は、
selected述語、座標の原始応答、object/axis/coordinateのHom点だけを比較する。
`selected_points_iff`・`coordinate_points_iff`は復元したnative写像の二つの保存fieldと同値である。
`IndependentGeometryHomSignatureExpressions.lean`はそれらを閉じた式へ接続し、
`evaluate_iff_of_support`で任意tableに対する共通query上の有限supportを証明する。

この段階でsignatureの計算成分と保存則は共通Homの点行へ接続した。
全package/Homの統合、invariant、operation自然性、detector code、coefficient、
coverage/overlap、両raw/realization方式、全体の両逆・恒等・合成・指定反証と査読は引き続き未完了である。

今回の4 sourceは単一fileで検証済みである。明示宣言の`#print axioms`は上記順に
11・14・10・8件、計43件。namespace監査は28・14・10・70件、計122件で、標準公理のみである。
warningを残さず、placeholder・hidden/BiDi・privacy・語彙・差分整形・module登録を確認した。
Cycleは追加せず、外側のtotal categoryとResearch全体buildにも進んでいない。

#### Operation自然性の原始作用式への接続

`IndependentGeometryHomOperationPoints.lean`は、二つのobject graphのtrue対で選ばれた
operation行と、既に復元したnative有向operation familyの評価を接続する。
`assemble_eq_atPair`・`assemble_point`は、依存する両端の型輸送後も同じ原始点を読むことを示す。

`IndependentGeometryHomOperationNaturality.lean`の`PointLaws`は、二つのobject点、
operation点、入力Atom点、source/targetのaction応答から出力Atom点を比較する。
`points_iff_nativeSquare`がnativeの作用自然性との両方向を示す。
`native_configuration_square_iff`は、構成したconfiguration mapのAtom作用との一致を使い、
作用の一点ずつの等式から元の`ConfigurationHom.comp`全体の等式を導く。
この補題のconfiguration mapとその作用一致は接続APIの引数であり、局所lawのfieldではない。
全package組立てでは、既存の`PackageGraphData.configurationMap_atomMap`がこの一致を与える。

`IndependentGeometryHomOperationExpressions.lean`は、同じ保存則の全instanceを閉じた式へ接続する。
各式の`support`は共通object/object/Hom queryの有限集合であり、action squareは
source/target応答の2点とHomの5点を使う。
`evaluate_iff_of_support`は任意tableで評価一致を示す。

残る主要項目はinvariant、detector code、coefficient、coverage/overlap、両方式のraw/realizationと、
全Hom両逆・共通の恒等/合成・残る有限式・指定反証・PR査読/CIの統合である。
Cycle 79を維持し、最初の検証点I全体を完了とは扱わない。

今回の3 sourceは単一fileで検証した。明示宣言は各6件、計18件の`#print axioms`を確認した。
namespace監査は順に6・6・50件、計62件で、標準公理のみである。
warning・placeholder・hidden/BiDi・privacy・追加文の語彙・差分整形・module登録を確認した。

#### Invariantの存在witness：二つの代替案の反証と未完了事項

人間の指示により、パートIはAstraで完了・PR・査読・mergeまで進め、II以降はSolへ引き継ぐ。
この担当分担は、以下の未証明事項の受理や検証点Iの縮小を意味しない。Cycle 79を維持する。

`IndependentInvariantTransportCandidates.lean`は、nativeなfunction invariantの
`∃ e : I.Value ≃ J.Value, ∀ A, e (I.evaluate A) = J.evaluate (f A)`を扱う設計検証である。
この`e`は元のHomではProp内のwitnessであり、計算用fieldではない。
以下の証拠は完成した局所Homの実装ではなく、その未解決点を明示する。

- `FiniteApproximation.native_finite_constraints_do_not_imply_transport`は、有限部分ごとの
  同値の存在から全体の同値の存在を導く案を反証する。受理済みの自然数からarchitecture objectへの
  単射を使って全射の自然数readingを作り、各有限部分では有限巡回置換がsuccessorと一致する。
  全体では0の原像がなく、元の`Invariant.TransportedAlong`は成立しない。readingの全射性は
  `naturalReading_surjective`で放電しており、新たな入力仮定ではない。
- `FiniteApproximation.chosen_constant_witness_forget_not_injective`は、0を返す`Fin 3`の
  readingに対し、恒等と1・2の交換という二つのwitnessを示す。選択した同値を別々のHomデータに
  残してから忘れる写像は単射でない。選択の違いを元の射の違いにしてはならない。
- `InfiniteWitness.hasWitness_iff_transported`は、双方向graphの有限片の整合族全体について
  Prop内で存在量化する候補と、nativeな存在条件との同値を証明する。
  `transportEquiv`はそのwitnessを消去したときに対象作用の選択肢が増えないことを示す。
  ただし`HasWitness`は有限witnessではなく、整合族全体の存在を条件としている。
  承認済み設計3.2の「原始値や有限witness」との適合を証明しておらず、局所lawに採用しない。

この二つの反証は指定した代替案への反証に限る。別の局所構成の不可能性、固定target A–Eの
不成立、設計変更の論理的必然性は証明していない。native Hom・固定GOAL・承認済み設計は変更しない。
対象/Hom assemblerはこの候補moduleを使用しない。

次の中心義務は、nativeな存在条件を保ったまま、選択をHomデータに残さず、承認済みの局所存在条件へ
落とすことである。ここは未放電であり、検証点Iの完了・PR査読・mergeはまだ行っていない。
detector code、coefficient、coverage/overlap、両raw/realization方式と全Homの統合も引き続き未完了である。
新規16明示宣言の個別公理監査とnamespace17宣言の監査、単一file検証を実施し、標準公理のみを確認した。

#### Invariantの商による設計補足と原始行の再構成

人間は「商を使う設計補足を認めて検証を進める」、続いて「GOALの固定ターゲットを変えずに、
設計を変更することを許可します」と承認した。これを受け、当初設計3.2・4.1の局所Homの
表示方法を次のように補足する。固定GOAL A–E、native Homの定義、Cycle 79は変更しない。

1. 元の共通Hom全queryの有限Bool tableの整合族を保持する。
2. function invariantの存在witnessは、候補index対と候補value型の双方向graph点を
   補助queryとして宣言し、その有限Bool tableの整合族を**データとして**構成する。
   行の存在・一意性、逆向き点との一致、元の評価の保存を点ごとの法則とする。
3. この整合条件を満たすpresentationを作った後に、元の共通Hom全queryが一致するものを
   同一視する。補助対応の選択だけが消え、context、coefficient、raw等の差は残る。

商を各有限片で先に取る構成ではない。また、前節の`InfiniteWitness.HasWitness`を
局所lawへ移す構成でもない。局所lawに全域の同値・射・整合族の存在条件を置かず、
補助graphから全域の存在証明を組み立てる。補助点は元のHomの観測成分に追加せず、
商の上の`point`と`fragment`は元の全queryだけを読む。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomInvariantWitnesses.lean` / `IndependentGeometryHomPrimitive.InvariantWitness` | `Query`はfamily選択前の候補index対とvalue graph点を宣言する。`Presentation`は元の全queryの`Retained`、補助整合族、原始行法則を持つ。`transported_of_row`・`assemblePresentation`はfunction/predicateの両種から元の`Invariant.TransportedAlong`を構成する。`readPresentation`・`assemble_readPresentation`は任意のnative不変量族を回復し、index/objectの可逆性やvalueの有限性を追加しない |
| `IndependentGeometryHomInvariantQuotient.lean` / 同namespace | `presentationSetoid`・`Local`は整合後の商。`readingEquiv`・`assemble_read`・`read_assemble`が不変量保存条件との両逆を証明する。`retained_injective`・`point_ext`は分離、`auxiliary_choice_independent`は補助選択の消去、`retained_point_separates`は元の全成分の差を保持する。`fragment_coherent`で有限片の制限整合も保つ |
| `IndependentGeometryHomInvariantPoints.lean` / 同namespaceの`Primitive` | `Row`は原始tableのkind応答で分岐し、完成したInvariantをlawの入力にしない。`row_iff`は組立てたnative行法則との両方向、`transports_of_rows`は全indexのnative保存証明への接続を与える。`FunctionPoint`は4セル、`PredicatePoint`は3セルを使い、両`*_of_same_cells`はその応答が同じなら評価も同じと示す。kind判定の2セル、index対の1セル、inverse/totalityの点則はこれらと別の原始instanceである |
| `IndependentInverseGraphComposition.lean` / `IndependentInverseGraph` | `compose`はforwardを順方向、backwardを逆順の点合成で定める。`compose_isLawful`・`assemble_compose`は逆行法則とnative合成を保つ。forward/backwardの両support定理は各2セルで合成値を決め、`compose_inactive`は候補型不一致をfalseに固定する |
| `IndependentGeometryHomInvariantComposition.lean` / `IndependentGeometryHomPrimitive.InvariantWitness` | `identityRow_law`・`composeRow_law`が不変量行の恒等・合成での閉性を証明する。合成の引数は元のobject点合成の中間値であり、完成したHomではない。種別不一致を両方向で拒否し、`successor_row_rejected`は有限片の各々が延長できても全体のwitnessが存在しない既存反例を拒否する。`package_transport`は商から既存package assemblerの`IsInvariantTransport` fieldを導く |

`Native`は、この段階では「共通Homのobject/index行条件を満たす全tableに、元の不変量保存条件を
課した型」である。これを完全なGeometry Homそのものと同定したとは扱わない。
今回解いたのは、不変量の存在witnessを局所点から組み立て、選択だけを消して元の保存条件を
厳密に保つ設計とその成分証明である。`Retained`には全queryを残しているため、後続の
他成分の保存則を、補助対応の選択に依存させず同じtableへ課せる。

パートIでは、全Hom組立てでこの商を使用する接続、共通の恒等・合成、detector code、coefficient、
coverage/overlap、両raw/realization方式、全体の両逆・残る有限式・指定反証・PR査読/CIが残る。
特にGOAL Bの全局所モデル圏への適合は、これらの統合後の標準査読でも確認する。

新規5 sourceを一つずつfocused checkした。明示66宣言の個別`#print axioms`と、各sourceの
namespace監査67・17・8・7・9件(計108件)は標準公理のみだった。warning・placeholder・
hidden/BiDi・privacy・追加文の語彙・差分整形・module登録を確認した。Research全体buildは行わない。
GOAL fileのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。

#### 原始保存則からのcore Hom組立てと幾何成分への接続

不変量の商を実際のpackage Hom組立てに接続した。入力は独立なobject tableの依存stageと、
共通Hom全queryを保持する不変量の局所商である。source・Atom・operation・Law・signatureの
保存則を原始点で課し、これらから`PackageTotalHom`の全fieldを構成する。
固定target、native Homの定義、Cycle 79は変更しない。

| Source / namespace末尾 | 今回の証拠と実際の使用先 |
| --- | --- |
| `IndependentGeometryHomDetectorLaws.lean` / `IndependentGeometryHomPrimitive.Detector` | `QueryMatch`・`ListMatch`・`CodeMatch`は有限detector構文の葉でAtom点を比較する。`codeMatch_iff`・`native_of_points`・`points_of_native`により、元のdetector保存等式との両方向を示す。`PackageAssembly.upper.detectorCode_eq`へ使用する |
| `IndependentGeometryHomDetectorFinite.lean` / 同namespace | `querySupport`・`listSupport`・`codeSupport`は構文だけから有限supportを作る。各`*_iff_of_support`と`point_instance_iff_of_support`は任意tableで同じセル応答なら同じ保存判定となることを示す |
| `IndependentGeometryHomCoefficientLaws.lean` / `IndependentGeometryHomPrimitive.Coefficient` | 原始環演算とdirected graphの`PointLaws`から`assemble`で環準同型を作る。`read_assemble`・`point_iff`は全候補carrierの点を回復し、`assemble_eq_native`は任意の元の環準同型を回復する。逆写像の条件は課さない |
| `IndependentGeometryHomCoverageLaws.lean` / `IndependentGeometryHomPrimitive.Coverage` | 九つの原始含意を`PointLaws`で定め、`assemble`・`points_of_native`・`points_iff_native`で元の九つのcoverage条件との同値を示す。`Maps`は比較APIの前提であり、後述の`GeometryComponents.coverage_maps`で実際の組立てから放電する |
| `IndependentGeometryHomOverlapLaws.lean` / `IndependentGeometryHomPrimitive.Overlap` | 三つの逆context点、二つのoverlap matching応答、順方向context点と両順序比較から`assemble`で元のoverlap同型を作る。`points_iff_native`は元の同型の存在との同値、`assemble_points_of_native`は同型全体の回復を示す。contextの同型を対象の等号へ強めない |
| `IndependentGeometryHomPackageAssembly.lean` / `IndependentGeometryHomPrimitive.PackageAssembly` | `PointLaws`は原始点条件を統合する。`configurationMap`・`lower`・`upper`・`assemble`は全core fieldを構成する。`upper.invariant_transport`は不変量の商の`package_transport`を使用し、operation・equation・signatureの既存原始保存則と今回のdetector保存則も実際のfield生成へ使用する |
| `IndependentGeometryHomPackagePoints.lean` / 同namespace | `read_source`・`read_pointedAtom`・`read_atom`・`object_point_iff`・`read_equation`・`read_context`・`read_operation`・`read_invariant`・`read_axis`・`read_signatureCoordinates`・`read_observables`は、組み立てたnative core Homから各計算成分の元の点tableを回復する。Atom・equation・axis・context両方向のpoint iffを幾何成分へ渡す |
| `IndependentGeometryHomGeometryComponents.lean` / `IndependentGeometryHomPrimitive.GeometryComponents` | 独立object stageのcoverage・overlap・contextの読み戻しを使い、`coverage_points_iff`・`overlap_points_iff`を証明する。`coverage_maps`・`overlap_maps`はpackageのpoint定理で比較前提を放電する。`coverage`・`overlap`・`coefficientMap`は同じ組立てたcore Hom上で元の幾何保存条件と係数写像を構成する |

今回の主要な依存は、原始Hom行 → 成分ごとの保存定理 → `PackageAssembly.upper/lower` →
`PackageAssembly.assemble` → `PackagePoints`の点回復 → `GeometryComponents`の三成分である。
元の保存等式を`PointLaws`のfieldに移す経路は取っていない。

残る中心義務は、raw・realizationの両方式を同じ共通Hom tableへ接続し、完全幾何のHomについて
読み取りと組立ての両逆を閉じることである。coreの各成分の読み戻しは証明済みだが、任意の
native完全幾何Homから局所法則を満たす共通tableを生成する逆方向、全Homの分離、共通の
恒等・合成、残る有限式・指定反証は引き続き未完了である。パートIのPR作成・独立査読・CI・
merge・Issue同期を済ませるまで、パートI完了として扱わない。

新規8 sourceをそれぞれ単一fileで検証した。各sourceのnamespace監査は順に
13・7・7・27・14・26・16・15件(計125件)で標準公理のみだった。
明示77宣言の個別`#print axioms`も標準公理のみで、warning・errorはなかった。
placeholder・hidden/BiDi・privacy・追加文の語彙・差分整形・module登録を確認した。
Research全体buildは行っていない。固定GOALのblobは引き続き
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`である。

#### 共通Hom点からの両realization方式の組立てと回復

代表方式のSupport・Axis・Observableのdirected mapと、明示方式の三つのfiber同値・
実際のcontext射への作用を、共通Homの原始点から構成した。各成分の全query読み戻しと、
任意のnative realizationを読み取って組み立て直す逆方向を証明した。
独立object stageから構成したcore Homへも接続し、比較APIのcontext・Atom前提を放電した。
固定GOAL、元のHomの範囲、Cycle 79は変更しない。

明示方式では、元の自然性とfiber同値から、実際のcontext射への作用が一意に定まる。
Support・Axisは「逆fiber写像 → 元の射 → 順fiber写像」、Observableはrestrictionの
逆方向に対応する同じ式で構成する。別の全域写像を局所lawに要求せず、元のactual-action
queryはすべて保持する。そのセルが対応するfiber graphのセルと一致する法則と、
不一致context対のセルをfalseにする法則を、読み戻し証明で使用する。
この補足は人間が許可した固定target内の設計変更であり、nativeな射を制限しない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentFixedIndexedPointGraphs.lean` / `IndependentFixedIndexedPointGraph` | 原始context参照から値carrierが定まる行の`IsLawful`・`InverseLaws`を宣言する。`assemble`・`assembleEquiv`は既存の全域・一意graph構成を使用し、`read_assemble`・`assemble_read`・`read_assembleEquiv`・`read_assembleEquiv_backward`・`assembleEquiv_read`でactive/inactive双方の全点を回復する |
| `IndependentGeometryHomRepresentativeRealization.lean` / `IndependentGeometryHomPrimitive.RepresentativeRealization` | `PointLaws`は三つのdirected graph、一方向のreading保存、原始restriction応答の自然性を持つ。`assemble`は元の`RealizationTransportSupply`を構成し、`read_support`・`read_axis`・`read_observable`で全候補context対を回復する |
| `IndependentGeometryHomRepresentativeRealizationNative.lean` / 同namespace | `points_of_native`は任意の元の代表方式supplyから全原始法則を導き、`assemble_points_of_native`は三つの計算成分を含むsupply全体の等号を示す。全行の読み取り一致はnative readerの比較前提であり、局所lawのfieldには入らない |
| `IndependentGeometryHomExplicitRealization.lean` / `IndependentGeometryHomPrimitive.ExplicitRealization` | `PointLaws`は両向きのfiber graph、readingの同値、全actual-actionセルの法則を持つ。`supportEquiv`・`axisEquiv`・`observableEquiv`から`valueTable`を作り、`valueTable_isLawful`・`assemble`で元の全supplyを構成する。actual restrictionの保存も既存の原始value-table定理から導く |
| `IndependentGeometryHomExplicitRealizationPoints.lean` / 同namespace | `readActualSupport`・`readActualAxis`・`readActualObservable`は両候補contextの等号で値を移し、不一致ならfalseを返す。三つの`read_*`は両向きのfiber点、三つの`read_actual*`は全actual-action点を回復する。後者はaction法則とinactive法則を実際に使用する |
| `IndependentGeometryHomExplicitRealizationNative.lean` / 同namespace | `points_of_native`は任意の元の明示方式supplyが全局所lawを満たすことを示す。`assemble_eq_native`・`assemble_points_of_native`はfiberの両方向と実際のcontext作用を含むsupply全体を回復する。native自然性が作用の式を強制することを逆方向の証明で使用する |
| `IndependentGeometryHomRealizationComponents.lean` / `IndependentGeometryHomPrimitive.GeometryComponents` | `representative_maps`・`explicit_maps`は実際の`PackageAssembly`の点定理を使用する。`RepresentativePoints`は元のobject stageのcontext応答を参照し、`representative_points_iff`でnative読み取りとの一致を証明する。`representativeRealization`・`explicitRealization`は独立objectと局所商から組み立てたcore Hom上に元のsupplyを構成する |

今回閉じたのはrealization成分の構成・回復と、実際のcore Homへの接続である。
任意のnative完全幾何Homから全局所法則を満たす共通tableを生成するreader、その全Homの両逆・
分離、rawの両方式の原始点接続、共通の恒等・合成、残る有限式・指定反証は未完了である。
パートIのPR・独立査読・CI・merge・Issue同期も継続義務として残す。

新規7 sourceの単一file検証が通り、namespace監査は順に31・34・2・42・12・3・7件
(計131件)で標準公理のみだった。明示73宣言の個別`#print axioms`も標準公理のみで、
最終検証にwarning・errorはない。placeholder・hidden/BiDi・privacy・語彙・差分整形・
module登録を確認した。Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。

#### 原始raw保存則と完全な明示方式Homの構成

明示方式について、元の独立object stageと不変量の局所商を入力に、core・coverage・overlap・
係数・raw・realizationの全6成分を持つ`ExplicitExactGeometryHom`を構成した。
各成分は同じ組立て済みcore Homと係数写像に接続される。今回は局所条件からnative Homを
作る方向の証拠であり、全Homのreaderと両逆の完了は主張しない。
固定target、元のHomの意味、Cycle 79は変更しない。

rawの多項式保存では、座標が同値であることを使い、単項式の有限な指数supportの対応と、
一つの係数graph点へ条件を分解した。係数写像はdirectedのままであり、非零係数が0へ写る
場合も扱う。元の多項式の非零supportだけを確認すると余分なtarget単項式を見逃すため、
各単項式対について有限な点条件を課す。完成した多項式写像やその保存等式は局所lawに入れない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentPolynomialPointTransport.lean` / `IndependentPolynomialPointTransport` | `sparseCoefficient`は原始zeroを持つSparse値から係数を読む。`MonomialMatch`は両指数support内の座標点と指数を比較し、`monomialMatch_iff`で同値によるrenameと一致する。`PointLaws`・`points_iff_rename_map`は原始係数点と元の係数変換・rename等式との両方向を証明する。`monomialMatch_iff_of_points`・`point_instance_iff_of_cells`は任意tableで各instanceの有限性を示す |
| `IndependentPolynomialPointTransportControls.lean` / 同namespaceの`Controls` | `coordinate`・`coefficient`は一座標の恒等対応と整数積環の第一成分への射影を読む。`distinct_coefficients_share_image`・`annihilated_coefficient_admitted`で異なる係数が同じ値へ写り、非零係数が消える多項式を受理する。`extra_target_monomial_rejected`はsource supportが空でも余分なtarget単項式を拒否する |
| `IndependentRawCandidatePoints.lean` / `IndependentRawCandidate` | 六つの`read_*`が座標carrier、relation carrier、label、local-data carrier、Sparse関係多項式、Sparse変数像のactive応答を公開する。raw Hom側はcandidate readerの実装を展開せず、このAPIを使用する |
| `IndependentGeometryHomRawPointLaws.lean` / `IndependentGeometryHomPrimitive.ExplicitRaw` | `contextPoints`・`coordinatePoint`・`relationPoint`は共通Homの原始点を読む。`PointLaws`は逆context対での座標・relation・依存local-dataのinverse graph、labelの点保存、Sparse関係多項式・変数像の原始条件を持つ。site射、完成した環準同型、全多項式保存式をfieldにしない |
| `IndependentGeometryHomExplicitRawAssembly.lean` / 同namespace | `Maps`は比較APIで逆contextと係数点だけを同定する。`coordinateEquiv`・`relationEquiv`・`coordinateTransport`がinverse graphから全carrier写像を作る。`polynomial_eq`・`image_eq`は原始Sparse条件を使用する。`assemble`は全多項式のrestriction保存を定数と変数から導き、元のraw map全体を構成する |
| `IndependentGeometryHomRawComponents.lean` / `IndependentGeometryHomPrimitive.GeometryComponents` | `read_raw`は独立object stageの全原始raw応答を回復し、`explicitRaw_points_iff`で元のstage条件に戻す。`explicitRaw_maps`は実際のpackage・係数組立ての点定理を使用して比較前提を放電する。`explicitRaw`は同じcore Homと係数写像の上でnative raw mapを構成する |
| `IndependentGeometryHomExplicitFullAssembly.lean` / `IndependentGeometryHomPrimitive.FullExplicit` | `PointLaws`は全6成分の原始条件を統合する。`assembleHom`は独立object stageと共通点を保持する不変量の商から、元の`ExplicitExactGeometryHom`の全fieldを構成する |

この時点でも、代表方式のrawを同じ原始点へ接続する義務、明示rawの全候補query回復、任意の
native完全幾何Homから局所法則を満たす共通tableを生成するreader、両方式の全Homの両逆・
分離、共通の恒等・合成、残る有限式・指定反証が未完了である。今回の多項式controlはその
成分を対象とし、完全な局所Homの非空性・全native Homの包含を代替しない。
パートI全体のPR・独立査読・CI・merge・Issue同期まで継続する。

新規7 sourceの単一file検証が通り、namespace監査は順に7・5・6・17・20・5・12件
(計72件)で標準公理のみだった。明示40宣言の個別`#print axioms`も標準公理のみで、
最終検証にwarning・errorはない。placeholder・hidden/BiDi・privacy・語彙・差分整形・
module登録を確認し、Research全体buildは行っていない。固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### 代表方式rawの原始条件との同値と全Hom構成への接続

代表方式のraw保存を、元のraw候補応答の比較と係数graphの点条件で記述した。
座標名を同値で移す明示方式と異なり、代表方式は元の座標・relation・local-dataの型参照を
そのまま保存する。多項式と変数像では候補応答の有無を比較し、各単項式の係数点を検査する。
変数像の条件はtargetの原始refinement応答を前提とし、完成したsite射を局所lawに置かない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentPolynomialCoefficientPoints.lean` / `IndependentPolynomialCoefficientPoints` | `PointLaws`は各指数の一つの係数graph点、`OptionalPoints`は応答の有無とactive係数点を比較する。`points_iff_map`・`optional_points_iff_map`は元の係数変換等式との同値を証明する |
| `IndependentRepresentativeRawResponses.lean` / `IndependentRepresentativeHom` | `polynomial_candidate_read`・`image_candidate_read`で元の候補応答へ接続し、`transport_polynomial_from_candidate`・`transport_image_from_candidate`で代表方式transportの評価をその応答と係数変換から回復する |
| `IndependentGeometryHomRepresentativeRawLaws.lean` / `IndependentGeometryHomPrimitive.RepresentativeRaw` | `PointLaws`は型参照・label・local-data・多項式・変数像の原始保存条件を宣言する。係数参照は原始carrierとzeroから得る |
| `IndependentGeometryHomRepresentativeRawAssembly.lean` / 同namespace | `assemble`は原始条件から元の厳密な`raw_eq`を構成する。`points_of_native`は任意の元のraw等式から全候補の原始条件を回復し、`points_iff_native`で両方向を統合する。context・係数の比較前提は次のstage接続で放電する |
| `IndependentGeometryHomRepresentativeRawComponents.lean` / `IndependentGeometryHomPrimitive.GeometryComponents` | `primitiveCoefficientRef`・`coefficientRef_assemble`は元のcarrier/zeroを保持する。`representativeRaw_maps`は実際のcore・係数写像の点回復から比較前提を導き、`representativeRaw_points_iff`・`representativeRaw`で元の独立object stageへ接続する |
| `IndependentGeometryHomRepresentativeFullAssembly.lean` / `IndependentGeometryHomPrimitive.FullRepresentative` | `PointLaws`は各成分の原始条件を統合する。`assembleHom`は同じ独立object stageと不変量の局所商から、元の`GeometryTotalHom`のcore・coverage・overlap・係数・厳密raw等式・三つのrealization成分と自然性を構成する |

全query回復へ進む前の点検で、`atObjects A B`のうち実際の両端に一致しない候補への
応答を、全Homの局所法則で固定していない箇所を見つけた。任意の値を残すとnative Homには
現れない情報が局所tableに残るため、両方式の`PointLaws.inactiveObjects`でfalseへ固定した。
これは設計§3.1の未使用候補の一意性を反映する補足であり、固定GOALやnative Homの定義は
変更していない。この法則を含む全局所Homとnative Homとの両逆は、引き続き証明対象である。

ここまでで、両方式の完全なnative Homを原始局所条件から構成する接続が揃う。
任意のnative Homから全局所条件を満たす共通tableを生成するreader、明示rawの全候補query回復、
両方式の全Homの両逆・分離、共通の恒等・合成、残る有限式・指定反証は未完了である。
成分の比較同値は完全な局所Homの正負instanceや全射性の代用にしない。
パートI全体のPR・独立査読・CI・merge・Issue同期まで継続し、Cycleは79のままとする。

新規6 sourceとinactive条件を補った明示方式sourceの単一file検証が通った。
namespace監査は順に4・4・12・11・6・13・13件(計63件)で標準公理のみだった。
新規・変更した明示25宣言の個別`#print axioms`も標準公理のみで、最終検証にwarning・errorはない。
placeholder・hidden/BiDi・privacy・語彙・差分整形・module登録を確認した。
Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。


#### 明示rawの全候補query回復と任意native raw mapの回復

明示方式rawの三つの計算成分を、全候補context・座標carrier・local-data carrierを含む
原始readerへ接続した。`read_coordinate`・`read_relation`・`read_localData`は、原始点から
構成した写像を読んで元のtableが戻ることを示す。`read_raw`は両方向のqueryを元の
source/target順へ戻し、共通宣言の全raw queryを回復する。

任意のnative raw mapから進む逆方向では、同じbase・係数写像の点対応と、三つの全候補
readerが共通tableの各行に一致することを比較前提とした。`points_of_native`は、この前提で
nativeな型宣言・label・relation polynomial・restriction保存から全原始法則を導く。
`assemble_points_of_native`は、得た法則を実際のassemblerに渡し、依存するlocal-dataと
relationの成分を含めて元のraw map全体を回復する。完成したraw mapや全域保存等式を局所lawへ
追加してはいない。これらの比較前提を一つの完全Hom readerから放電する接続は残る。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomExplicitRawReadings.lean` / `IndependentGeometryHomPrimitive.ExplicitRaw` | `readCoordinate`・`readRelation`・`readLocalData`が全候補のinverse graphを読む。各active APIとinactive APIにより、context・座標型・座標像が一致しない行をfalseへ固定する |
| `IndependentGeometryHomExplicitRawPoints.lean` / 同namespace | `read_coordinate`・`read_relation`・`read_localData`は、実際に組み立てたraw mapから全行を回復する。原始inactive法則と候補carrierの型法則を回復証明で使用する |
| `IndependentGeometryHomExplicitRawNative.lean` / 同namespace | `coordinate_rows_of_read`・`relation_rows_of_read`・二つの`*_point_iff_of_read`を経由し、`points_of_native`が全原始法則を導く。候補応答が存在することから元のcarrier/zero宣言を回復し、native多項式保存とrestriction自然性を係数点へ移す |
| `IndependentGeometryHomExplicitRawRecovery.lean` / 同namespace | `readRaw`・`read_raw`は共通の全raw queryへ接続する。`inverse_read_heq`は座標像の等号から得るtarget fiberの等号を使い、`coordinateEquiv_eq_native`・`relationEquiv_eq_native`・`coordinateTransport_eq_native`で各成分を回復する。`assemble_eq_native`・`assemble_points_of_native`で元のraw map全体の回復を示す |

今回の証拠により、明示raw成分の全query回復とnative成分回復が揃った。次の中心義務は、
core・係数・raw・realizationを一つの共通Hom readerへまとめ、そのreaderから各比較前提と
全局所法則を導くことである。全Homの両逆・分離、共通の恒等・合成、残る有限式・指定反証、
パートI全体のPR・独立査読・CI・merge・Issue同期は未完了である。
固定GOAL、native Homの範囲、Cycle 79は変更しない。

新規4 sourceの単一file検証が通り、namespace監査は順に10・3・5・8件(計26件)で
標準公理のみだった。明示26宣言の個別`#print axioms`も標準公理のみで、最終検証に
warning・errorはない。placeholder・hidden/BiDi・privacy・語彙・登録・差分整形を確認した。
Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。


#### 共通native Hom readerと不変量の商への接続

両方式の元の完全幾何Homを、一つの共通Boolean tableへ読み取る構成を追加した。
まずobject・axis・contextの添字点を読み、その復元等式に沿ってoperation・signature座標・
observableの依存する型を同定する。その後、同じtableへrawとrealizationの全queryを入れる。
実際のsource/target object対に一致しない`atObjects`候補はfalseへ固定する。
依存写像を完成した局所値として保持する方式は採らず、既存の候補点readerでBooleanへ読む。

共通readerを有限部分集合へ制限した整合族は、元のobject/index作用を復元する。
元の`invariant_transport`をその作用へ接続し、既存の補助対応付きpresentationと商を構成した。
`point_localWith`・`point_localRepresentative`・`point_localExplicit`により、補助対応を消した後も
元の全query値が保持される。これは不変量部分の法則とquery保持の接続であり、全Homの局所法則を
満たすことと全体の両逆は引き続き未完了である。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomNativeIndices.lean` / `IndependentGeometryHomPrimitive.NativeReader` | `liftDependent`のactive/inactive APIが候補object対の応答を固定する。`indices`は元のsource・Atom・object・invariant・axis・係数・equation・context点を読み、`objectMap_indices`・`axisMap_indices`・`context_assemble_indices`で依存先の添字を回復する |
| `IndependentGeometryHomNativeFamilies.lean` / 同namespace | 三つの`*Family`が証明済み添字等式に沿って元の依存写像を移す。各`*_heq`が値の保持を証明し、既存のindexed reading equivalenceから全候補の`*Rows`と法則を得る |
| `IndependentGeometryHomNativeReader.lean` / 同namespace | `readWith`は共通宣言の全roleを一つのtableへ統合する。各projection APIが成分readerとの一致を示す。`readRepresentative`は元のdirected realizationを、`readExplicit`は明示rawと全actual context-actionを保持する |
| `IndependentGeometryHomNativeInvariant.lean` / 同namespace | `retainedWith`が有限整合族を作り、object/index作用を回復する。`nativeWith`は元の不変量存在条件を使用し、`localWith`が既存の商へ接続する。`assemble_localWith`は不変量部分を回復し、両方式の`point_local*`が全query保持を証明する |
| `IndependentGeometryHomNativeRows.lean` / 同namespace | 同じ完全readerのAtom一致、derived matching、source・equation・context・operation・axis・signature・observableの行法則を証明する。source・Atom・object・context・axisの復元等式と、operation/signatureの依存写像全体の復元を得る |

今回の比較前提は元のnative Homの計算成分・元の不変量存在条件から放電した。
`readWith`のraw/realization引数はmodeごとの既存readerを差し込むための共通構成であり、
その任意引数から完全な局所Homの適法性を主張してはいない。次の中心義務は、独立object stageの
原始保存則と、係数・raw・realizationを含む全局所法則を、この同じreaderから導くことである。
続いて全Homの両逆・分離、共通の恒等・合成、残る有限式・指定反証を閉じる。
パートI全体のPR・独立査読・CI・merge・Issue同期は未完了であり、パートIIは開始しない。
固定GOAL、native Homの範囲、Cycle 79は変更していない。

新規5 sourceの単一file検証が通った。namespace監査は順に19・12・22・14・18件
(計85件)で標準公理のみであり、明示85宣言の個別`#print axioms`も全件を照合した。
最終検証にwarning・errorはない。placeholder・hidden/BiDi・privacy・語彙・docstring・
module登録・差分整形を確認した。Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。


#### 共通readerからの全core局所法則とnative core Hom全体の回復

独立object stageから組み立てた両端の間の任意のnative core Homについて、共通readerが
既存の全core局所法則を満たすことと、その局所商から元のcore Hom全体が戻ることを証明した。
extraction・generation・operation・signatureに加え、equationのrole・restriction自然性・
violation・residual・detectorを同じtable上へ接続している。不変量は既存の商に保持された
object/index作用を使い、補助対応の選択を元のHomの計算成分へ追加していない。

依存する写像の保存則では、添字写像とその上のfamilyをSigma対として比較した。
`readWith_contextObservable_eq`が元のcontextとobservable族を同時に回復し、その等号を
restriction・violation・residualの各原始保存則の導出に使用する。完成した保存則を
局所lawのfieldへ移す変更は行っていない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomNativeRecovery.lean` / `IndependentGeometryHomPrimitive.NativeReader` | equation-index同値とobservable族を回復し、`readWith_contextObservable_eq`で依存する対の一致を得る。Atom・equation・axis・係数・context両方向の真の点と元の像の対応も公開する |
| `IndependentGeometryHomNativeCorePreservation.lean` / 同namespace | `readWith_extraction`・`readWith_generation`・`readWith_selected`・`readWith_operation_preservation`・`readWith_coordinate_preservation`が、元のHomの保存則から独立stageの全候補に対する原始条件を導く |
| `IndependentGeometryHomNativeEquationPreservation.lean` / 同namespace | role・restriction自然性・violation・residual・detectorの原始条件を導く。`readWith_equation_preservation`が既存の四つのequation局所条件を統合する |
| `IndependentGeometryHomNativePackage.lean` / 同namespace | `readWith_package`・`localWith_package`が、同じreaderと局所商に全core条件を与える。`localWith_package_assemble`がlower/upper双方の計算成分と全依存familyを回復する。両方式の`local*_package`・`local*_package_assemble`が元の完全幾何Homのbaseへ接続する |
| `IndependentGeometryHomNativeGeometryPreservation.lean` / 同namespace | coreの回復等式で既存のcoverage/overlap比較前提を放電する。`localWith_coverage`・`localWith_overlap`が元の幾何保存から独立stageの条件を導き、`localWith_coefficient`・`localWith_coefficient_assemble`が非可逆性を制限せず元の環準同型を回復する |

新しい入力前提を追加せず、元のnative Homと独立object stageの既存条件からこの接続を得た。
`readWith`のraw/realization引数は引き続き共通構成の差し込み口であり、今回閉じたのはcore全条件と
coreのnative側回復、およびcoverage・overlap・係数の接続である。完全幾何のraw・realizationを
同じ局所商の全条件へ接続し、全Homのnative側回復と全query側回復を閉じる義務が残る。
全Homの分離、共通の恒等・合成、残る有限式・指定反証、パートI全体のPR・独立査読・CI・mergeも
継続対象である。パートIIには進まず、固定GOAL・元のHomの範囲・Cycle 79を維持する。

新規5 sourceの単一file検証が通り、namespace監査は順に9・5・6・7・4件(計31件)で
標準公理のみだった。明示31宣言の個別`#print axioms`も全件を照合した。最終検証に
warning・errorはなく、placeholder・hidden/BiDi・privacy・語彙・docstring・module登録・
差分整形を確認した。Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### 共通局所商の全幾何法則と両方式のnative Hom全体の回復

独立object stageから組み立てた両端の間の任意のnative Homについて、raw・realizationを
同じ共通readerと不変量の局所商へ接続した。両方式の`localRepresentative_points`・
`localExplicit_points`は、実際の全Hom assemblerが要求する全局所条件を導く。
続く`localRepresentative_assemble`・`localExplicit_assemble`は、そのassemblerへ渡すと
元の完全幾何Hom全体が戻ることを示す。今回閉じた方向はnative Homから局所商を経た回復である。

明示rawでは、全候補の座標・relation・依存local-data行が共通readerのraw行に一致する。
既存のnative raw converseの比較前提をこれらの等式で放電し、core・係数写像の回復を使って
実際のstage assemblerの出力全体を元のraw mapと比較した。代表方式では、元のstrict raw等式から
既存の原始条件を導く。代表方式のrawを明示raw mapへ置き換える変更は行っていない。

realizationでは、代表方式の三つのdirected成分と、明示方式の三つのfiber同値・三つの
actual context-action行を共通readerへ接続した。元のnative supplyから全原始法則を導き、
core回復等式に沿って実際のstage assemblerのパラメータを同定してsupply全体を回復する。
全Homの回復には既存のnative extensionalityを使い、coverageのproof-valued性と既存の
thin-context overlapのsubsingleton性もその既存APIのまま使用する。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomNativeRawReadings.lean` / `IndependentGeometryHomPrimitive.NativeReader` | `readWith_explicitRaw_maps`と三つの`readWith_raw_*`がraw converseの比較前提を放電する。`readWith_explicitRaw_points`・`readWith_explicitRaw_assemble`が全原始法則とnative raw回復を与える |
| `IndependentGeometryHomNativeRawPreservation.lean` / 同namespace | `localWith_explicitRaw`・`localWith_representativeRaw`が両方式の独立stage法則を導く。`localWith_explicitRaw_assemble_heq`はcore・係数の回復から実際の依存raw map全体を回復する |
| `IndependentGeometryHomNativeRealizationReadings.lean` / 同namespace | 各fiberとactual-actionのprojection APIが元のreaderとの一致を示す。両方式の`readWith_*Realization_points`・`readWith_*Realization_assemble`が全法則と元のsupplyの回復へ接続する |
| `IndependentGeometryHomNativeRealizationPreservation.lean` / 同namespace | 両方式の`localWith_*Realization`が独立stage法則を与える。対応する`*_assemble_heq`がcore回復を使用し、実際のstage assemblerから元のsupply全体を回復する |
| `IndependentGeometryHomNativeFullRecovery.lean` / 同namespace | 両方式の`local*_points`が同じ局所商の全条件を統合し、`local*_assemble`が元の完全Hom全体を回復する。`representativeHom_ext`は既存native extensionalityをsupply全体の比較へ接続する |

入力は既存の独立object stageと元のnative Homである。raw・realizationのmap・row比較前提は
共通readerのprojectionから、assemblerのパラメータ一致は前節のcore・係数回復から放電した。
完成した写像・保存証明を局所lawへ追加していない。非可逆な係数準同型も元の範囲で保持する。

逆方向、すなわち任意の適法な局所商から組み立てたHomを読み直して全query値と局所商全体を
回復する証明は未完了である。全Homの分離、共通の恒等・合成、残る有限式・指定反証も残る。
今回の任意native Homからの法則導出を、完全な正負instance検査や全Homの両逆の代用にはしない。
パートI全体のPR・独立査読・CI・merge・Issue同期まで継続し、パートIIは開始しない。
固定GOAL・元のHomの範囲・Cycle 79は維持する。

新規5 sourceの単一file検証が通った。namespace監査は順に6・4・15・6・5件(計36件)で
標準公理のみだった。明示36宣言の個別`#print axioms`も全件を照合し、標準公理のみを確認した。
最終検証にwarning・errorはなく、placeholder・hidden/BiDi・privacy・語彙・docstring・
module登録・差分整形を確認した。Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。


#### 任意の適法な局所商の全query回復と完全Homの両逆・分離

独立object stageから組み立てた両端について、前節と逆の方向を閉じた。
`readRepresentative_assemble`・`readExplicit_assemble`は、任意の適法な共通局所商から
実際の全Hom assemblerで作ったHomを読み直すと、元の全query値が戻ることを示す。
`localRepresentative_read_assemble`・`localExplicit_read_assemble`は、これを既存の
`InvariantWitness.point_ext`へ渡し、補助不変量対応を消した商全体の回復を得る。

この証明では、元の局所条件を満たす任意のtableを出発点とする。native readerの像であることを
先に仮定していない。まずsource・両Atom・object・不変量・axis・contextと派生照合値を回復する。
依存するoperation・signature・observableのreaderには、その添字点の等号と元のnative familyの
異種等号を渡す。既存の成分ごとの両逆から、activeだけでなく全候補carrier・endpoint行を回復する。
実際の両端に一致しないobject対では、全Hom局所法則の`inactiveObjects`を明示的に使用する。

raw・realizationの比較を前提とする`readWith_assemble`へ、実際の両方式のraw/realization
assemblerの全候補readbackを接続した。この最後の比較前提は`readRepresentative_assemble`・
`readExplicit_assemble`で放電しており、完成したraw mapや保存証明を局所lawへ追加していない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomLocalIndexRecovery.lean` / `IndependentGeometryHomPrimitive.NativeReader` | `indices_assemble_*`が任意の適法な局所商のscalar・index・派生照合値を回復し、依存行のactivation比較を与える |
| `IndependentGeometryHomReadingCongruence.lean` / `IndependentGeometryHomPrimitive.ReadingCongruence` | 既存のindexed function・candidate inverse・indexed ring readerの合同性を示す。`operation`・`signature`・`observable`は、対応する添字点と依存familyが等しければ全候補tableが等しいことを示す |
| `IndependentGeometryHomLocalFamilyRecovery.lean` / `IndependentGeometryHomPrimitive.NativeReader` | `operationRows_assemble`・`signatureRows_assemble`・`observableRows_assemble`が、native readerの添字表現と元の局所tableを比較して全依存行を回復する |
| `IndependentGeometryHomLocalTableRecovery.lean` / 同namespace | `readWith_assemble`が共通Queryの全constructorを場合分けし、両向きの点対順序、全依存行、inactive object対、raw/realizationの比較を使ってtable全体を回復する |
| `IndependentGeometryHomLocalFullRecovery.lean` / 同namespace | 両方式の全query回復と局所商回復を示す。`representativeHomReadingEquiv`・`explicitHomReadingEquiv`は、前節のnative側回復と合わせ、元の完全Homと適法な局所商との同値を与える |
| `IndependentGeometryHomFullSeparation.lean` / 同namespace | 両方式の`*_eq_iff_queries`・`*_distinct_query`が全Homの分離を示す。`*_unique_preimage`が任意の適法な局所商の一意なnative preimageを与える。`local_fragment_point`が有限fragmentの値を同じ元のqueryへ接続する |

入力前提は既存の独立object stageと、原始条件を満たす局所商である。共通Hom宣言、各原始法則、
商で同一視する条件を変更せずに、全fieldの両逆と分離が得られた。元の非可逆な係数・object・
operation写像も同値の対象に残り、代表方式と明示方式のraw/realizationの違いも保持する。
全queryの分離は、同じobject作用を持つ異なるHomにも適用される。

パートIでは、共通の局所恒等・合成とその有限片への接続、残る原始式の有限support、指定反証scenarioの
共通宣言への統合、PR・独立査読・CI・mergeが残る。このHom同値をパートI全体や主Nの完了とは扱わない。
パートIIは開始せず、固定GOAL・元のHomの範囲・Cycle 79を維持する。

新規6 sourceの単一file検証が通った。namespace監査は順に9・6・3・1・8・7件(計34件)で
標準公理のみだった。明示34宣言の個別`#print axioms`も全件を照合し、標準公理のみを確認した。
最終検証にwarning・errorはなく、placeholder・hidden/BiDi・privacy・語彙・docstring・
module登録・差分整形を確認した。Research全体buildは行わず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`を維持している。


#### 原始点による共通index・operation合成と有限fragmentへの接続

承認済み設計§4.1の局所合成を、原始graphの点から構成した。最初の行の一意な像を中間値として
選び、次のtableをその点で読む。Atom・contextのbackwardは順序を逆転する。contextには元の
preorder同値の比較を保持し、context objectの全単射を新たに要求しない。両成分の恒等は対角点から
定義し、適法性と元のnative恒等への組立てを証明した。

共通Homでは、source・pointed/upper Atom・object・invariant index・signature axis・係数・
family/configuration照合値・equation/context indexを同じQuery上で合成した。
`Composition.indices_eq_native`は、それらが元のcore Homと係数準同型の合成を読む値に
一致することを示す。係数・source・objectの可逆性は要求しない。依存する値の行は別に埋めるため、
このindex table単独の完全Hom適法性を主張してはいない。

operationでは、最初のobject graphから中間の両端を選び、そのoperation graphから中間の値を選ぶ。
`Composition.operationRows_eq_native`が全候補endpoint/carrier行について元のnative合成との一致を
証明する。添字同定と値の異種等号をSigma対で比較し、型の移し替えでoperationの値が変わらないことを
導いた。完成したnative Homの合成は比較定理の右辺に現れ、直接tableを定義する入力には使わない。

有限性は、一般の依存graphで一つのindex点と最大二つの値点に分解した。共通宣言のoperationでは
index点が二つのobject点になるため、両入力を合わせて最大四つのqueryで各出力が決まる。
`Composition.operationRows_finite_fragment`は、この主張を補助対応の商を取った後の実際の
`InvariantWitness.fragment`へ接続する。支持集合は評価する元の入力とqueryに応じて選ぶ。
最初の比較入力には既存の原始行法則を要求し、任意の不適法tableに対する有限決定性へ拡張しない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentIndexedCarrierComposition.lean` / `IndependentCarrierGraph`, `IndependentIndexedCarrierGraph` | `composeIndex`・`composeRows`が中間の原始添字・値を使う。`composeIndex_iff`は関係合成との一致、`composeRows_isLawful`はinactive/active行法則、`assemble_composeRows_heq`は依存写像の合成との一致を与える |
| `IndependentGeometryHomAtomComposition.lean` / `IndependentGeometryHomPrimitive.Atom` | `identity`・`compose`を両方向の原始点から定義する。適法性・native assemblyとの一致と各方向二点のsupportを証明し、共通index合成へ使用する |
| `IndependentGeometryHomContextComposition.lean` / `IndependentGeometryHomPrimitive.Context` | 対角恒等と前後のcontext graph合成を定義する。`compose_eq_read`・`assemble_compose`が元のthin-category同値へ接続し、両方向の二点supportを与える |
| `IndependentGeometryHomCompositionIndices.lean` / `IndependentCarrierGraph`, `IndependentGeometryHomPrimitive.Composition` | `compose_eq_read`がdirected graphの比較APIを与える。`dependentIndices`・`indices`が共通Queryの添字部分を直接合成し、両`*_eq_native`が元のcore/係数合成との一致を示す |
| `IndependentGeometryHomOperationComposition.lean` / `IndependentGeometryHomPrimitive.Operation`, `NativeReader`, `Composition` | operation値の型同定を`assemble_value_heq`・`indexed_comp_heq`・`operationIndexedFamily_heq`で処理する。`operationRows`が原始合成を共通宣言へ接続し、`operationRows_eq_native`が全候補値を元の合成と比較する |
| `IndependentGeometryHomOperationCompositionFinite.lean` / `IndependentIndexedCarrierGraph`, `IndependentGeometryHomPrimitive.Composition` | `composeRows_finite_support`が一つのindex点と最大二つの値点を構成する。`operationRows_finite_support`・`operationRows_finite_fragment`が共通queryと実際の有限fragmentで最大四点の決定を証明する |

入力前提は既存の独立object stage、補助対応を消した局所商、その原始行法則である。
`operation_endpoints`が共通index合成と依存する両端の合成を同定し、native readerの型比較を放電する。
対象条件・Homの意味・商の同一視条件を変更せず、同じHom同値へ接続する合成を構成している。

残りはsignature/observable・raw・realizationの直接合成、それらの共通tableへの統合と商上の
全局所法則、全Homの恒等・単位・結合則、各有限片との整合、残る原始式の有限support、指定反証の
統合である。今回のoperation単独の四点決定を、全Homの合成やDの有限決定性とは扱わない。
パートI全体のPR・独立査読・CI・merge・Issue同期まで継続し、パートIIは開始しない。
固定GOAL・元のHomの範囲・Cycle 79を維持する。

新規6 sourceを一つずつfocused checkし、全て通った。各fileのnamespace監査の合計は順に
11・10・10・5・7・4件(計47件)で標準公理のみだった。47宣言全ての個別`#print axioms`を
出力名まで照合した。最終検証にwarning・errorはなく、placeholder・hidden/BiDi・privacy・
語彙・docstring・module登録・差分整形・保護領域を確認した。Research全体buildは実行せず、
固定GOALのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### signature・observableの原始合成と共通core tableへの統合

前節のscalar/index・operation合成に、signature座標とobservableの両方向の原始合成を接続した。
最初の添字graphから中間添字を選び、次の添字点がtrueなら二つのfiber graphを合成する。
次の添字点がfalseなら行全体をfalseに固定する。signatureの候補axis型が一致しない場合もfalseとし、
添字写像の可逆性を追加していない。forward/backwardの点は元の向きで合成する。

`Composition.signatureRows_eq_native`は、全候補axis・coordinate行を元のnative座標同値の合成と
比較する。`Composition.observableRows_eq_native`は、全候補context・値carrier行を元の環同値の
合成と比較する。observableではcontextの添字とring-equivalence familyをSigma対で比較し、
型の移し替えが両方向の値を変えないことを導いた。必要な環構造は既存の独立object stageから得ている。

有限性は、二つの添字点と最大二つのfiber点に分解した。`signatureRows_finite_support`・
`observableRows_finite_support`は、共通宣言の両入力を合わせて最大四つのqueryで各出力が決まる
ことを示す。各`*_finite_fragment`が補助対応を消した商の実際の有限fragmentへ接続する。
その支持集合は元の入力と評価queryに依存し、指定した既存の行法則を満たす比較入力について使う。

続く`Composition.composeWith`は、scalar/index・operation・signature・observableを同じ共通Queryの
tableへ統合する。`composeWith_eq_native`は、元のcore Homと係数準同型の合成を共通readerで読んだ
値との全queryの一致を証明する。raw・realizationには両辺で同じ点callbackを渡す段階であり、
それらの合成や幾何法則はまだ導いていない。完全Homの合成の代わりにcoreだけで完了とはしない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentIndexedInverseComposition.lean` / `IndependentIndexedInverseGraph`, `IndependentCandidateIndexedInverseGraph` | `composeRows`が添字点と両方向のfiber点を合成する。`composeRows_isLawful`・`assemble_composeRows_heq`が元の依存同値に接続する。`extend`・`project_extend`・`extend_read`は外側carrier候補を保持した完全readerへ接続する |
| `IndependentGeometryHomSignatureComposition.lean` / `IndependentGeometryHomPrimitive.Composition` | `signatureRows`が元のaxis/coordinate行を直接合成する。`signature_indices`が共通index tableとactivationを同定し、`signatureRows_eq_native`が全候補行を元のnative合成と比較する |
| `IndependentGeometryHomObservableComposition.lean` / `IndependentGeometryHomPrimitive.Observable`, `NativeReader`, `Composition` | contextの型同定を両方向のfiberデータまで証明する。`observableRows`・`observable_indices`・`observableRows_eq_native`が原始の合成、共通activation、native環同値合成を接続する |
| `IndependentIndexedInverseCompositionFinite.lean` / `IndependentInverseGraph`, `IndependentIndexedInverseGraph`, `IndependentCandidateIndexedInverseGraph` | 非依存の二点supportと、依存する二つの添字点・二つの値点を構成する。`composeRows_lifted_finite_support`が点projectionとの一致を使い、元のqueryへの埋込みでも最大四点であることを示す |
| `IndependentGeometryHomAlgebraicCompositionFinite.lean` / `IndependentGeometryHomPrimitive.InvariantWitness`, `Composition` | `fragment_eq_iff_points`が有限fragmentの等号を元のqueryの等号と同定する。signature/observableの`*_finite_support`・`*_finite_fragment`が同じ共通宣言と商で四点の決定を与える |
| `IndependentGeometryHomCoreComposition.lean` / `IndependentGeometryHomPrimitive.Composition` | `dependentWith`・`composeWith`が直接合成したcoreの全計算成分を統合する。各`*_eq_native`が任意の同じraw/realization点callbackの下で、元のcore/係数合成の共通readerとの一致を示す |

入力前提は既存の独立object stage、局所商、原始行法則、係数の原始保存則である。
有限supportの埋込み補題が要求する点projection等式は、実際の共通queryのconstructorを場合分けして
放電した。native Homの合成は比較証明で使用し、直接合成するtableの値に完成した射を保持しない。
対象条件・Homの意味・商の同一視条件は変更していない。

残りはraw・realizationの直接合成、共通tableの全幾何法則と商上の合成への接続、全Homの恒等・
単位・結合則・有限片との整合、残る原始式の有限support、指定反証の統合、パートI全体の
PR・独立査読・CI・mergeである。パートIIは開始せず、固定GOAL・元のHomの範囲・Cycle 79を維持する。

新規6 sourceを一つずつfocused checkし、全て通った。各fileのnamespace監査の合計は順に
9・3・7・6・5・4件(計34件)で標準公理のみだった。34宣言全ての個別`#print axioms`も出力名まで
照合した。最終検証にwarning・errorはなく、placeholder・hidden/BiDi・privacy・語彙・docstring・
module登録・差分整形・保護領域を確認した。Research全体buildは実行せず、固定GOALのblobは
`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### rawの原始合成と共通core/raw tableの保存則

明示方式のrawについて、coordinate・relation・local-dataの全queryを原始点から直接合成した。
rawの添字は逆向きなので、後段のbackward context graphから中間contextを選び、前段の
context点がtrueなら二つの値の行をsourceからtargetの順に合成する。falseなら行全体を
falseに固定する。`composeAgainst`はこの構成と両方向の逆写像法則を一般の依存graphで証明する。

local-dataでは、さらに前段のcoordinate点から中間座標を一つ選ぶ。後段のcoordinate点がtrueで、
三つの元のlocal-data型応答が存在する場合に、その二つの値の行を合成する。context不一致、
source coordinate carrier不一致、後段coordinate点不一致では全候補値をfalseにする。
`composeLocalData_eq_native`は、これらの候補も含めて元のraw mapの合成との一致を示す。

`ExplicitRaw.composeRaw`が三種類を元のraw queryへ統合し、`composeRaw_eq_native`が全queryの一致を
証明する。続く`Composition.explicitRawRows`は、native rawを読み直したtableではなく、元の独立object
stageと局所商のretained tableから直接定義する。`explicitRawRows_eq_native`では、既存のobject
readingの両逆と実際のcore・係数assemblerから比較前提を放電した。

`Composition.composeExplicitWith`は、既存のscalar/index・operation・signature・observable合成に
このraw合成を接続する。`composeExplicitWith_eq_native`がcore・係数・rawの元の合成との一致を、
`composeExplicitWith_raw_points`が合成後の全raw原始法則(逆写像、label、多項式、restriction)の保持を
証明する。realizationには指定した点callbackを残しており、完全Homの合成と商上の全条件は未完了である。

coordinate・relationの各出力は、両入力の二つのbackward context点と最大二つの値点で決まる。
各`*_finite_support`は共通queryで最大四点、`rawCoordinate_finite_fragment`・
`rawRelation_finite_fragment`は商の実際の有限fragmentで同じ決定性を示す。
支持集合は元の入力と評価queryに依存し、比較入力には既存の原始行法則を要求する。
local-dataの有限supportはまだ未証明であり、今回の四点決定に含めない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentIndexedInverseAgainstComposition.lean` / `IndependentIndexedInverseGraph` | `composeAgainst`・`*_at_pair`・`*_false_at_pair`・`*_isLawful`が後段の逆向き添字選択と原始fiber合成を構成し、rawのcoordinate・relation行へ使用する |
| `IndependentGeometryHomRawCompositionRows.lean` / `IndependentGeometryHomPrimitive.ExplicitRaw` | `coordinateTable`・`relationTable`と各行法則を共通queryから得る。`composeCoordinate`・`composeRelation`と各active/inactive比較が元のraw stageを直接合成する |
| `IndependentGeometryHomRawCompositionNative.lean` / 同namespace | `composeCoordinate_eq_native`・`composeRelation_eq_native`が全context・carrier候補を元のraw mapの合成と比較する |
| `IndependentGeometryHomRawLocalDataComposition.lean` / 同namespace | `composeLocalDataFiber`・`composeLocalData`が元の型応答と一つの中間座標を使う。各active/inactive APIが型候補と点候補の全場合を扱う |
| `IndependentGeometryHomRawLocalDataCompositionNative.lean` / 同namespace | `readLocalData_inactive_carriers`・`composeLocalData_eq_native`が依存する値の全候補を元のnative raw合成へ接続する |
| `IndependentGeometryHomRawComposition.lean` / 同namespace | `composeRaw`・`composeRaw_eq_native`が三種類と両方向を元のraw query上で統合する |
| `IndependentGeometryHomCoreRawComposition.lean` / `IndependentGeometryHomPrimitive.Composition` | `explicitRawRows`・`*_eq_native`が元の独立stageとの比較を放電する。`composeExplicitWith`・`*_eq_native`・`*_raw_points`がcore/raw全体の比較とraw原始法則の保存を与える |
| `IndependentIndexedInverseAgainstCompositionFinite.lean` / `IndependentIndexedInverseGraph` | `composeAgainst_finite_support`・`composeAgainst_lifted_finite_support`が二つの逆向き添字点と最大二つの値点を構成し、元のqueryへの埋込みに接続する |
| `IndependentGeometryHomRawCompositionFinite.lean` / `IndependentGeometryHomPrimitive.ExplicitRaw`, `Composition` | coordinate・relationの`*_finite_support`と`rawCoordinate_finite_fragment`・`rawRelation_finite_fragment`が同じ共通宣言と実際の商の有限片で最大四点の決定を証明する |

入力前提は既存の独立object stage、局所商、package・係数・rawの原始法則である。完成したraw mapは
直接tableを定義する入力にせず、元の写像の合成は比較と法則保持の証明で使う。対象条件・Homの意味・
商の同一視条件を変更していない。

残りは両方式のrealizationの直接合成、両方式の全幾何法則と商上の合成、全Homの恒等・単位・結合則・
有限片との整合、local-data合成を含む残る原始式の有限support、指定反証の統合、パートI全体の
PR・独立査読・CI・mergeである。パートIIは開始せず、固定GOAL・元のHomの範囲・Cycle 79を維持する。

新規9 sourceを一つずつfocused checkし、全て通った。各fileのnamespace監査の合計は順に
4・10・2・8・2・2・5・2・4件(計39件、生成されたmatch宣言1件を含む)で標準公理のみだった。
明示38宣言全ての個別`#print axioms`も出力名まで照合した。最終検証にwarning・errorはなく、
placeholder・hidden/BiDi・privacy・語彙・docstring・module登録・差分整形・保護領域を確認した。
Research全体buildは実行せず、固定GOALのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### realizationの原始合成と全計算queryの統合

代表方式のSupport・Axis・Observableの三つの有向写像と、明示方式の同じ三種類の両方向の
fiber写像を、元のcontext点と値点から合成した。前向きでは前段の中間値から後段の値点を読み、
後ろ向きでは後段の逆像から前段の逆向きの点を読む。候補contextが不一致の場合も含め、
両方式の`composeRealization_eq_native`が元のrealization合成の読み取りとの一致を証明する。

明示方式のactual context-actionは、既存の原始action法則に従い、合成したfiberの後ろ向きの
一点、元のsource context-operationの一点評価、前向きの一点から構成する。Observableだけは
restrictionの向きに合わせてcontextの順を逆にする。`action_point_iff`が元のnaturalityを使って
この式とnative作用の一致を示す。完成したcontext作用や全域Homを局所値に追加していない。

`representativeRealizationRows`・`explicitRealizationRows`は、独立object stageと局所商のretained
queryからこの合成を定義する。比較定理は既存のobject readingの両逆と実際のpackage assemblerを
使い、元のcontext表・Atom作用との比較前提を放電する。

`composeRepresentative`・`composeExplicit`がcore・係数・raw・realizationの全計算queryを統合する。
両`*_eq_native`は、元の各成分の合成を`NativeReader.readWith`で読んだtableとの全query一致を示す。
両方式のrealization原始法則と、明示方式のraw原始法則も同じtable上で保持する。
ここで定義したのは全計算queryのtableであり、全法則を備えた商上のHom合成は引き続き未完了である。

代表方式では、任意の一出力は前段のcontext点一つ、前段の値点一つ、後段の値点一つで決まる。
`representativeRealization_finite_fragment`は、同じ局所商の実際の二つの有限fragment上で、
合計最大三点の決定を証明する。支持集合は元の入力と出力queryに依存し、比較入力には元の
原始行法則を要求する。明示方式のactual-action合成の有限supportは今回の三点決定に含めない。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentFixedIndexedPointComposition.lean` / `IndependentFixedIndexedPointGraph` | `compose`・`compose_at_pair`・`compose_isLawful`・`compose_eq_read`・`compose_index_iff`・`assemble_compose`が、依存する中間contextと中間値から合成し、元の写像に接続する |
| `IndependentFixedIndexedInverseComposition.lean` / 同namespace | `composeBackward`・active/inactive比較・`composeBackward_eq_forward`・`compose_inverseLaws`が逆順の値合成と両方向の逆写像法則を与える |
| `IndependentFixedIndexedPointAction.lean` / 同namespace | `action`・`action_active`・`action_inactive`・`action_point_iff`が一点ごとのcontext作用を構成し、native自然性に接続する |
| `IndependentGeometryHomRepresentativeRealizationComposition.lean` / `IndependentGeometryHomPrimitive.RepresentativeRealization` | `composeRealization`と全候補queryのnative比較が、元の三つの有向写像を保持する |
| `IndependentGeometryHomExplicitRealizationCompositionFibers.lean` / `IndependentGeometryHomPrimitive.ExplicitRealization` | Support・Axis・Observableの各`compose*`・`*_inverseLaws`・`*_eq_native`が両方向を元の同値合成へ接続する |
| `IndependentGeometryHomExplicitRealizationComposition.lean` / 同namespace | `composeRealization`、三つのnative inactive API、`composeRealization_eq_native`がactual-actionを含む全候補値を扱う |
| `IndependentGeometryHomRealizationCompositionRows.lean` / `IndependentGeometryHomPrimitive.Composition` | 両`*RealizationRows`と`*_eq_native`が、元の独立object stageと実際のassemblerへ接続する |
| `IndependentGeometryHomFullTableComposition.lean` / 同namespace | 両`compose*`・`*_eq_native`・`*_realization_points`と`composeExplicit_raw_points`が、全計算queryの合成とrealization/raw法則保持を同じtableに統合する |
| `IndependentFixedIndexedPointCompositionFinite.lean` / `IndependentFixedIndexedPointGraph` | `compose_lifted_finite_support`が元のquery型で最大三点の支持集合を構成する |
| `IndependentGeometryHomRepresentativeRealizationCompositionFinite.lean` / `IndependentGeometryHomPrimitive.RepresentativeRealization`, `Composition` | `composeRealization_finite_support`と`representativeRealization_finite_fragment`が代表方式の共通query・実際の商fragmentへ三点決定を接続する |

入力前提は既存の独立object stage、局所商、package・係数・raw・realizationの原始法則である。
context/Atomのnative比較、元のnaturality、合成後のinverse/realization/raw法則は既存の
assembler・readerおよび今回の証明から得た。GOAL・元のHomの範囲・商の同一視条件を変更していない。

残りは全幾何法則と商上の合成、全Homの恒等・単位・結合則・有限片との整合、明示realizationと
local-data合成を含む残る有限support、指定反証の統合、パートI全体のPR・独立査読・CI・mergeである。
パートIIは開始せず、Cycle 79を維持する。

新規10 sourceを一つずつfocused checkし、全て通った。各fileのnamespace監査は順に
6・6・4・2・9・5・4・7・1・2件(計46件、生成されたmatch宣言1件を含む)で標準公理のみだった。
明示45宣言全ての個別`#print axioms`も出力名まで照合した。最終検証にwarning・errorはなく、
placeholder・hidden/BiDi・privacy・語彙・docstring・module登録・差分整形・保護領域を確認した。
Research全体buildは実行せず、固定GOALのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### 原始の整合族からの商上の全Hom合成と結合則

前節の全計算queryの合成tableから、商上の局所Homを構成した。`composeRetained`が元の有限tableを
そのまま保持し、object行と不変量のindex行の合成法則を証明する。`composePresentation`は、
前段の一意なindex像を中間添字として二つの補助graphを直接合成する。不一致のcarrier、inactiveな
index対、predicateの補助点をfalseに保ち、object点の中間対象による分解から評価の整合性を示す。

`exists_compositePresentation`は両入力の商の帰納法でこの構成を適用する。`composeLocal`は、
構成済みの整合presentationを選んだ後で補助対応を消す。`composeLocal_table`・`composeLocal_point`が
元の全queryを、`composeLocal_fragment`が任意の有限fragmentを保持する。`composeLocal_choice_independent`は
同じ元のquery値を持つ任意の整合presentationが同じ合成結果になることを証明する。
完成したnative Homやnative transportの存在条件を、補助行の定義に使用していない。

`representativeLocal`・`explicitLocal`が、実際の独立object stageと完全局所法則を持つ二つのHomへ
この構成を適用する。各`*_table`・`*_fragment`は原始合成tableとの正確な一致を与える。
`*_eq_native`は元の完全Homの合成の読み取りとの一致を示し、`*_points`がinactive object、package、
coverage、overlap、係数、raw、realizationの全局所法則を放電する。`*_assemble`はその合成を組み立てると
元の完全Homの合成に戻ることを、全Homの両逆を使って証明する。

`*_read_comp`は任意の元の完全Homの読み取りが局所合成と可換であることを示す。`*_assoc`は、
局所側の直接構成と全成分の比較を証明した後で、元の完全Homの結合則を使い、商上の結合則を示す。
代表方式の有向realization、明示方式のrawとactual context-action、非可逆な係数・object・operation
写像を同じ範囲で保持する。

| Source / namespace末尾 | 証拠と使用先 |
| --- | --- |
| `IndependentGeometryHomRetainedComposition.lean` / `IndependentGeometryHomPrimitive.InvariantWitness` | `composeRetained`・`composeRetained_table`・`composite_index_point`・`composite_object_factor`が、元の全有限tableと原始object/index合成をつなぐ |
| `IndependentGeometryHomInvariantPresentationComposition.lean` / 同namespace | `composeRow_inactive`、`compositeAuxRow`とactive/inactive比較、`composeAux`とcarrier/row/typing比較、`composePresentation`・`composePresentation_table`が、商を取る前の補助対応の整合性を構成する |
| `IndependentGeometryHomInvariantLocalComposition.lean` / 同namespace | `exists_compositePresentation`・`composeLocal`とtable/point/fragment比較・`composeLocal_choice_independent`が、原始合成の整合証明後に補助対応を消す |
| `IndependentGeometryHomFullCompositionNative.lean` / `IndependentGeometryHomPrimitive.Composition` | `composeRepresentative_eq_full_native`・`composeExplicit_eq_full_native`が、全計算queryを元の完全Homの合成に接続する |
| `IndependentGeometryHomFullLocalComposition.lean` / 同namespace | 両方式の`*Local`・`*_table`・`*_fragment`・`*_eq_native`・`*_points`・`*_assemble`が、実際の局所商での合成・全法則・全成分の組立てを統合する |
| `IndependentGeometryHomLocalCompositionLaws.lean` / 同namespace | 両方式の`*_read_comp`・`*_assoc`が、任意の元のHomの合成との可換性と局所商の結合則を示す |

一般補題のobject/index合成条件は、この補題の明示した適用条件であり、完全Homへの適用では原始
合成tableの定義から放電する。入力の完全局所法則から元のassemblerを得て、合成後の全法則を証明する。
出力の法則・native比較・結合則を入力fieldへ移していない。補助対応の消去条件と固定GOALは変更していない。
有限fragmentとの一致は、原始合成tableの制限との一致である。全出力の有限入力supportが完了した
という主張ではなく、未証明の明示realization・local-data等のsupportは残す。

残りは原始恒等と単位則、残る有限support・有限式・指定反証の統合、パートI全体のPR・独立査読・
CI・mergeである。パートIIは開始せず、Cycle 79を維持する。

新規6 sourceを一つずつfocused checkし、全て通った。各fileのnamespace監査は順に
4・11・6・2・12・6件(計41件、生成された補助宣言3件を含む)で標準公理のみだった。
明示38宣言全ての個別`#print axioms`も出力名まで照合した。最終検証にwarning・errorはなく、
placeholder・hidden/BiDi・privacy・語彙・docstring・module登録・差分整形・保護領域を確認した。
Research全体buildは実行せず、固定GOALのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。


#### 例外フローにおけるパートIの恒等・有限support・反証統合

この節はCycleを加算しない難所突破の例外フローであり、Cycleは79のままとする。固定GOAL A–E、
native Homの定義、代表方式と明示方式の違い、元の全query値による商の同一視条件は変更していない。
パートII以後の四族統合、三投影・normalization、共通有限読み取りDとEは開始していない。

原始恒等は、共通query table全体を完成Homの`NativeReader`から定義せず、各constructorを原始graphと
component恒等mapから構成した。source・Atom・object・invariant index・operation・signature・context・
observable・係数は対角の原始graphと各候補の
active/inactive条件から作る。代表方式のrawと三つの有向realizationを保持し、明示方式ではrawの
coordinate・relation・依存local-dataの両方向、realizationの両方向fiberと実際のcontext作用を保持する。
明示rawの三成分も、完成したraw恒等mapのreaderを経由せず、context/carrier/coordinateの一致判定と
各carrier上の対角inverse graphから直接構成する。
明示方式の実際の作用は元の`ContextMorphism`のSupport・Axis・Observable各成分を評価し、単なる対角
Boolには置き換えていない。

`presentationIdentity`はfunction invariantの対角補助graph、predicateとinactive行のfalse正規化、
typingとrow lawを備えた整合presentationを作る。その後に`localIdentity`で補助対応を消す。
`localIdentity_point`と`localIdentity_fragment`は元の全queryと任意の有限fragmentを直接恒等tableへ戻し、
`localIdentity_choice_independent`は同じretained宣言を持つ別の補助presentationが別の恒等射を作らない
ことを示す。両方式のnative恒等との一致、全`PointLaws`、全Hom assembly、左右単位則を証明した。

| Source / namespace末尾 | 主な証拠 |
| --- | --- |
| `IndependentGeometryHomIdentityTable.lean` / `IndependentGeometryHomPrimitive.Identity` | `identityWith`、両`*Table_eq_native`、raw/realizationを含む全queryの直接恒等table |
| `IndependentGeometryHomLocalIdentity.lean` / `IdentityLocal` | `presentationIdentity`、`localIdentity`、point/fragment/choice比較、両方式の`*_points`と`*_assemble` |
| `IndependentGeometryHomLocalCategoryLaws.lean` / `CategoryLaws` | 代表・明示の`*_id_comp`と`*_comp_id` |
| `IndependentGeometryHomLocalCompositionLaws.lean` / `Composition` | `representativeLocal_assoc`、`explicitLocal_assoc` |

有限supportでは、明示realizationの全9 queryについて両方向fiberとactual-actionを分解した。
actual-actionの一つの元の作用点は最大4個の原始cellで決まり、合成fiberの支持集合と有限和を取る。
raw local-dataでは、後段のbackward context、前段のcoordinate像、三つの型応答、依存fiber値を別々に
追跡し、missing response・inactive context・carrier/coordinate不一致も扱う。

`composeWith_finite_support`は共通queryの全constructorを網羅する。source・Atom・object・invariant・
equation・contextに加え、operation・signature・observable・両raw・両realizationの既存supportを統合した。
family/configurationは無限のAtom写像を入力にせず、一つの真なtransport点から中間像を一意に回復し、
後段の一セルと合わせて決定する。`composeRepresentative_finite_fragment`と
`composeExplicit_finite_fragment`は一出力を実際の二つの`InvariantWitness.fragment`へ接続する。
有限出力集合については各支持集合の`Finset.biUnion`を取り、両`*_finite_fragment_set`から最終的に
`representativeLocal_finite_fragment_support`と`explicitLocal_finite_fragment_support`で、完成した
局所Homの有限fragmentが二つの有限入力fragmentだけで決まることを示した。

| Source / namespace末尾 | 主な証拠 |
| --- | --- |
| `IndependentFixedIndexedPointActionFinite.lean` / `IndependentFixedIndexedPointGraph` | `action_lifted_finite_support` |
| `IndependentGeometryHomExplicitRealizationCompositionFinite.lean` / `ExplicitRealization`, `Composition` | fiber・actual-actionの全supportと`explicitRealization_finite_fragment` |
| `IndependentGeometryHomRawLocalDataCompositionFinite.lean` / `ExplicitRaw`, `Composition` | local-data/raw全体のsupportと`explicitRaw_finite_fragment` |
| `IndependentGeometryHomFullCompositionFinite.lean` / `Composition` | 全constructorの一出力・有限出力集合・完成局所Hom fragmentの有限決定 |

有限式は、定義を目視して有限と判断せず、source object・target object・Homの三表を読む閉じた構文へ
置き換えた。`IndependentFiniteLawFormula`の真偽を担うleafは、一つの正確な表セルとその応答値に
限定した。型・添字・供給値の一致や不一致は式に格納せず、量化されたinstance側の前提または有限な
構文分岐に置いた。`typeMarker`は構文のユニバースを保つための単位値で、評価は定数真であり、
任意の型・命題・表応答を引数に取らない。
これにより、表セルと無関係な任意の命題・値等式・完成したlaw certificateをleafから注入する経路はない。
`Formula.support`は三表それぞれの`Finset`を返し、`Formula.evaluate_iff_of_support`は任意の比較表について、その
三support上の一致だけで評価が保存されることを示す。carrier graphのtypingは型の不一致を外側の前提とし、
totalityとuniquenessは選択した真witnessセルと異なるchallengerの偽セルで表した。inverse rowと依存rowを
含むそれぞれについて、元の量化法則との同値を証明した。

object側では、foundationのextraction・有限family・composition・invariant・signature・operation・Atom・
coefficient、generated-object matching、active row、さらに各active objectのcontext・equation・circuit・
coverage・overlap・rawを全て有限式族へ写し、逆向きに元の`IndependentGeometryPrimitive.IsLawful`を再構成した。
rawのgenerator・identity・compositionは完成した命題をleafへ入れず、選択されたrelation/image row、有限
`Finsupp` witness、有限変数集合を明示する。多項式は専用の`CellFormula`で6種類のAST queryセルを固定し、
`expressionFormula_evaluate`と`evaluate_eq_expected_of_expressionFormula`が`support`上の一致から
`IndependentPolynomialExpressions.evaluate_eq_of_support`を使って元の多項式値を回復する。identityにも
`IndependentPolynomialExpressions.compile`と同じsupport評価を使う。`DependentLaws`とobject全体の集約も、
前段の有限式族から再構成したlaw proofだけを後段へ渡し、完成したdependent/object certificateを
instance dataとして保持しない。

Hom側では、Atom coherence、extraction、transport matching、generation、object row、equation/context/
observable、detector、operation、signatureを`PackageAssembly.PointLaws`の有限式族へ集約した。coverageの
9条件、係数のzero/one/add/mul、overlap、代表・明示raw、代表・明示realizationを同じ三表構文へ接続し、
`FullRepresentative.PointLaws`と`FullExplicit.PointLaws`の全fieldを両向きに復元した。inactive object rowも
object参照の不一致を外側の前提とし、式自体は一つの正確な偽Homセルだけを読む。係数graphの型不一致と
唯一性、代表・明示realizationのreading条件も量化法則側へ移し、式には対応するHomセルを残した。
量化法則全体に単一supportを要求せず、引数・witness・challenger・monomialを固定した各instanceの有限性と、一つの
合成出力queryの有限性を区別する。

| Source / namespace末尾 | 主な証拠 |
| --- | --- |
| `IndependentFiniteLawFormula.lean`、`IndependentFiniteGraphLawFormula.lean`、`IndependentPolynomialExpressions.lean` | 三表`Formula`、多項式`CellFormula`、各`evaluate_iff_of_support`、total/inverse/dependent rowの`lawful_iff_instances` |
| `IndependentGeometryObjectFoundation*LawFinite.lean`、`IndependentGeometryObjectMatchingLawFinite.lean` | `foundationLaws_iff_instances`、`Matching.lawful_iff_instances`、`Active.activeTyped_iff_instances` |
| `IndependentGeometryObjectDependent*LawFinite.lean`、`IndependentGeometryObjectLawFinite.lean` | 6 dependent stage、`dependentLaws_iff_instances`、object全体の`lawful_iff_instances` |
| `IndependentGeometryHomCoreLawFinite.lean`、`IndependentGeometryHomPackageLawFinite.lean` | core各成分と`PackageAssembly.PointLaws`の`pointLaws_iff_instances` |
| `IndependentGeometryHomJointLawFinite.lean`、`IndependentGeometryHomRawLawFinite.lean`、`IndependentGeometryHomRealizationLawFinite.lean` | coverage・overlap・coefficient・raw・realizationの各`pointLaws_iff_instances` |
| `IndependentGeometryHomLawFinite.lean` / `IndependentGeometryHomPrimitive.LawFinite` | `representativePointLaws_iff_instances`、`explicitPointLaws_iff_instances` |

指定反証と非自明例は、部品だけの反証と共通宣言への適用を次のように区別して照合した。

| 検査 | 証拠 |
| --- | --- |
| 全false、重複出力、carrier不一致 | `false_table_rejected`、`duplicate_outputs_rejected`、`mismatched_carrier_rejected`と、対象宣言の`eraseMatching_not_lawful` |
| pointed/upper Atom不一致 | `IndependentGeometryHomPrimitive.Atom.mismatch_rejected` |
| invariantの種別・native失敗・successor | `mixed_kind_rejected`、`reverse_mixed_kind_rejected`、`native_failure_rejected`、`successor_row_rejected` |
| ring乗法の改変 | 成分反証`IndependentRingPrimitive.eraseMultiplication_not_lawful`に加え、実際の局所Hom要素を一セルだけ変更した`coefficientMultiplicationMutation_not_full` |
| context restriction自然性の改変 | 成分反証`IndependentExplicitRealization.finite_support_action_rejected`に加え、具体的actual axis cellを変更した`axisActionMutation_not_full` |
| overlap片側の改変 | `Overlap.one_sided_order_rejected`と、実際の局所Hom要素へ持ち上げた`overlapForwardMutation_not_full` |
| raw relation polynomial / variable imageの改変 | 成分反証`not_lawful_of_polynomial_mismatch`・`not_lawful_of_image_mismatch`に加え、異なるlawful endpoint間の局所Homとして構成した`polynomialMismatch_not_full`・`imageMismatch_not_full` |
| 同じbase・係数・object作用を持つ異なる全Hom | `boolRawSwapHom`と明示恒等HomはrawのBoolean座標交換だけが異なり、`boolRawSwapHom_distinct_query`が同じ具体的raw coordinate queryで分離する |
| 非可逆係数写像 | `projection_not_injective`と両`*_reconstruction_noninjective`。今回の共通局所Hom同値はその完全Homを入力として保持する |
| 補助選択による余分な区別 | `auxiliary_choice_independent`、`composeLocal_choice_independent`、新規`localIdentity_choice_independent`。対象側は`objectEquiv`の両逆とProp内のlaw witnessを使い、列挙を対象データへ追加しない |

係数射影2本による既存の分離例に加え、`boolRawSwapHom`はbase・係数・object作用を恒等Homと定義上同じに
保ち、raw座標だけで異なる。有限fixtureの同一contextで`false ↦ true`を問う具体的queryは交換Homでtrue、
恒等Homでfalseになる。したがって一般の条件付き分離定理や係数差だけに依存せず、observable/raw/realization
を含む全queryのうちraw成分が実際に別の完全Homを識別する。
局所構造には完成した`GeometryPackage`、完成したHom、raw系全体の等式を新しいdata fieldとして追加して
いない。完成fieldは比較定理とnative法則の回復にだけ現れる。

| Source / namespace末尾 | 主な証拠 |
| --- | --- |
| `IndependentGeometryHomIntegratedRefutations.lean` / `IndependentHomRefutations` | 五つの`*_not_full`、`boolRawSwapHom_*_eq`、`boolRawSwapHom_ne_identity`、`boolRawSwapHom_distinct_query` |

以上により、承認済み設計のパートIについて、原始対象、両方式の全Hom両逆、全fieldの保持と分離、
恒等・合成・左右単位・結合則、有限局所式、指定反証、補助選択の消去が同じ共通宣言と局所商で接続した。
これは固定GOAL全体の完了ではなく、パートIIへ渡す技術的検証点Iのcompletion candidateである。
固定GOALカードのblobは`4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`のままである。

例外フローの既存10 sourceに加え、閉じた有限式、object各段、Hom各段と集約の18 sourceを追加し、
`IndependentGeometryHomLawFinite.lean`を安全な三表構文の全Hom集約へ書き換えた。各sourceは単一fileの
focused checkを通し、埋込みのnamespace監査は全て標準公理のみだった。中心集約であるraw dependent、
`DependentLaws`、object `IsLawful`、代表・明示`PointLaws`も依存順に再検証した。
基底式の`.olean`を更新した後に、基礎から完全Hom集約まで依存順に再コンパイルした。
今回の有限式修正に関わる三表support保存、多項式`CellFormula`、raw・dependent・object・package・両方式の
raw・realization・完全Hom集約の中心13宣言を個別`#print axioms`でも照合し、公理集合は
`propext`・`Classical.choice`・`Quot.sound`だけだった。
placeholder・hidden/BiDi・privacy・語彙・import方向・module登録・差分整形・保護領域を確認し、
任意命題を受け取る旧constructorまたは同等経路が残っていないことも検索した。
Research全体buildとaggregate rootのelaborationはhard ruleに従って実行せず、Cycleは79のままである。


#### 第4査読後のproof-checkpoint判定

PR #4830は、パートIのcompletion candidateではなく、原始対象、両方式の全Hom、恒等・合成・圏法則、
有限fragment、指定反証までの基盤を固定する`proof-checkpoint`として受理する。Cycleは79のままとし、
このPRのmergeをパートI完了またはG-124全体の完了とは扱わない。

exact head `c491d273df2184d05646b94cf12f5d630b7b6b48`に対する第4査読は、Math A/BがReject、
Lean A/Bが`No major findings`となった。親統合では、任意のLean命題から構文を選べるという一般論だけを
失格理由にはしない。一方、実際に公開するlaw builderについて、次の有限provenanceが未接続であるため、
completion判定はRejectとする。

1. circuitの非零residual条件とcoverageの`Active`条件は、元のlawとの論理同値には含まれるが、
   現在のformula評価そのものには含まれていない。これらが参照する具体的な原始cellから決まることを、
   専用formulaまたはbuilder単位のsupport保存定理で示す必要がある。
2. rawのgenerator・identity・compositionはcanonicalなsynthetic polynomial table上ではAST式へ接続したが、
   原始object tableからそのsynthetic tableへのsupport bridgeが本番のlaw経路に未接続である。
   係数のzero/one/add/mul、relation polynomial、variable image、必要な型参照を原始supportへ含め、
   `evaluate_eq_expected_of_expressionFormula`を実際の三法則から使用する必要がある。
3. 「任意命題を構文上注入する経路がない」という一般的な主張は撤回する。以後の受入条件は、
   実際に公開するlaw builderの引数が許可された原始dataに限られることと、そのbuilderについて
   support保存・native law回復・全aggregateへの接続が証明されることとする。

次PRは上記だけを扱う。恒等・合成・左右単位・結合則、局所商の選択非依存、完成Homとの両逆、
合成fragmentの有限決定、指定改変反証、raw-only分離はこのcheckpointの受理済み基盤として再実装しない。
修正後の小さい差分に新規4レーン査読を行い、全laneと親統合が`No major findings`となった場合にだけ、
パートI完了を宣言する。パートII以後は未着手のままである。


#### パートI completion candidateの有限provenance修正

checkpoint後の小さい差分では、第4査読で残った三点だけを修正した。固定GOAL、元のHomの範囲、
局所商、恒等・合成・圏法則、指定反証は変更していない。Cycleは79のままであり、パートII以後は
開始していない。

1. circuitの`witnessFormula`は、residual cellがobservableのzero cellと一致する場合に偽となる含意を
   持つ。`witnessFormula_evaluate`は式の評価と元の非零条件の同値を証明し、`LawInstances`から式外の
   非零fieldを削除した。
2. coverageの`activationFormula`は、required equationのrole cell、selected witnessのindex cell、
   required axisのaxis cellを読む。`pointFormula`はcoverage cellからこの式への含意となり、
   `pointFormula_evaluate`は式の評価と元の`coverageRows q → Active q`の同値を証明する。
   `Instances`から式外の`Active`結論を削除した。
3. rawではnative tableと別のcomparison tableをinstance dataとして持つ。
   `substitutionObjectFormula`と`witnessObjectFormula`は、ASTの実supportに現れる全queryについて、
   元のraw image / relation polynomial cellと係数operation cellからcomparison tableの値を固定する。
   relation polynomialは係数literalへ畳み込まずASTのvariableとして残すため、選択したrelation rowが
   generatorの回復に実際に使われる。variable imageも期待多項式を持つ正確なraw cellとして固定する。
   zero / one / coefficient / addは有限monomial support上の係数cellを読み、mulは各monomialの
   `Finset.antidiagonal`にある全積cellと右結合の有限和cellを読む。

`substitutionBridge_sound`と`witnessBridge_sound`は、object formulaからnative tableとcomparison tableの
support上の一致を得る。その上でroot formulaを同じcomparison tableへ評価し、
`IndependentPolynomialExpressions.evaluate_eq_expected_of_expressionFormula`をcomparison tableに適用する。
最後に`evaluate_eq_of_support`でnative評価へ戻す。identity・composition・generatorの本番経路は全て
この二つのbridgeを使用し、generatorのsubstitutionとwitnessは別table上で同じ`result`へ接続する。

Leanという言語一般について、任意命題を参照できないとは主張しない。今回の受入根拠は、実際に公開する
builderが上記の原始cellと有限ASTだけから式を作り、式の評価から元のnative lawを回復することに限定する。

変更した三sourceのfocused checkは順に26・21・120宣言を監査し、標準公理だけを使用した。
この節はパートIのcompletion candidateを記録する。新規4レーン査読、CI、merge、Issue同期が完了するまで
パートI完了とは扱わない。


## 特例パートII PR 1/4 selection — geometry局所圏と圏同値

この作業単位はユーザー指定の特例であり、正規Cycleを追加しない。Cycleは79のまま維持する。
一次仕様は固定GOAL A/Bと、Issue #4711の
[実装設計](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711#issuecomment-5754509275)
§3・§7である。

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 79
special_work_unit: part2-pr1
cycle_increment: false
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 17f61dcc6d58afb4ec9d8a2568981de9002dfac6
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Issue comment 5752520031 records Part I completion; implementation design is Issue comment 5754509275 sections 3 and 7"
  proof_dag_predecessors:
    - "Part I PR 4835 at reviewed head a82165fbf0ddd368170712180498da2a305b3c5c"
    - "Cycle 65 LocalReconstructionEquivalence.ReconstructionData.equivalence"
    - "IndependentGeometryPrimitive.finiteObjectEquiv"
    - "NativeReader.representativeHomReadingEquiv and NativeReader.explicitHomReadingEquiv"
    - "IdentityLocal, Composition, and CategoryLaws for both geometry modes"
  proof_obligation: "Construct the representative and explicit primitive local categories, reading functors, concrete separation and assembly data, and both category equivalences for arbitrary geometry objects and all original Homs."
  selection_reason: "Part I already proves object and Hom inverse laws plus direct local identity, composition, and category laws; this PR only supplies the categorical connection required before the lens and protocol branches."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean"
    - "RepresentativeLocalObject and ExplicitLocalObject category instances"
    - "representativeReadingFunctor and explicitReadingFunctor"
    - "representativeReconstructionData and explicitReconstructionData"
    - "representativeEquivalence and explicitEquivalence"
  risks:
    - "Endpoint transport could conceal a restriction of the native object or Hom types."
    - "A local Hom definition could accidentally retain a completed GeometryTotalHom or ExplicitExactGeometryHom."
    - "Functoriality could be proved for transported operations instead of the direct primitive identity and composition."
  unchecked:
    - "Lens primitive reading is PR 2/4."
    - "Protocol primitive reading is PR 3/4."
    - "The common declaration, mandatory inputs, and Cycle 79 comparison are PR 4/4."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Both geometry modes now have primitive local categories, full Hom reading equivalences after exact endpoint conversion, concrete separation and assembly data, and category equivalences obtained from the Cycle 65 general theorem."
  completion_candidate: no
  lean_artifacts:
    - "IndependentGeometryCategoryReconstruction.RepresentativeLocalObject"
    - "IndependentGeometryCategoryReconstruction.ExplicitLocalObject"
    - "IndependentGeometryCategoryReconstruction.representativeReadObject_injective"
    - "IndependentGeometryCategoryReconstruction.explicitReadObject_injective"
    - "IndependentGeometryCategoryReconstruction.representativeEndpointHomEquiv_read"
    - "IndependentGeometryCategoryReconstruction.explicitEndpointHomEquiv_read"
    - "IndependentGeometryCategoryReconstruction.representativeReadingFunctor"
    - "IndependentGeometryCategoryReconstruction.explicitReadingFunctor"
    - "IndependentGeometryCategoryReconstruction.representativeReconstructionData"
    - "IndependentGeometryCategoryReconstruction.explicitReconstructionData"
    - "IndependentGeometryCategoryReconstruction.representativeEquivalence"
    - "IndependentGeometryCategoryReconstruction.explicitEquivalence"
  evidence:
    - "representativeEndpointHomEquiv_read and explicitEndpointHomEquiv_read identify the complete primitive tables before and after endpoint conversion"
    - "representativeReadingHomEquiv_point and explicitReadingHomEquiv_point identify every local query with the original native Hom reader"
    - "representativeReadObject_injective and explicitReadObject_injective connect Part I object separation to both new object readers"
    - "representative_assemble_read and explicit_assemble_read"
    - "representative_read_assemble and explicit_read_assemble"
    - "representative_existsUnique_preimage and explicit_existsUnique_preimage"
    - "representativeReadingHomEquiv_id/comp and explicitReadingHomEquiv_id/comp use the direct Part I local operations"
  claim_mapping:
    theorem_names:
      - "representativeEquivalence"
      - "explicitEquivalence"
      - "representativeReadObject_injective"
      - "explicitReadObject_injective"
      - "representativeEndpointHomEquiv_read"
      - "explicitEndpointHomEquiv_read"
      - "representative_existsUnique_preimage"
      - "explicit_existsUnique_preimage"
    source_labels:
      - "fixed GOAL A and B geometry branch"
      - "Issue comment 5754509275 sections 3 and 7, implementation order 1"
    conjuncts:
      - "Part I LocalObject -> RepresentativeLocalObject and ExplicitLocalObject"
      - "Part I readFragments_injective -> both native object readers are injective"
      - "all GeometryTotalHom -> representativeReadingHomEquiv"
      - "all ExplicitExactGeometryHom -> explicitReadingHomEquiv"
      - "endpoint conversion preserves both complete native primitive tables"
      - "Hom separation, Hom assembly, and object assembly -> both ReconstructionData values"
      - "Cycle 65 general reconstruction -> both category equivalences"
    undischarged_assumptions: []
    acceptance_point: "This is the PR 1/4 obligation candidate. Fixed-head review, CI, and merge remain before acceptance."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "Object separation comes from readFragments_injective and is connected to both new object readers."
      - "Object assembly comes from finiteObjectEquiv and readFragments_assembleFragments."
      - "Hom separation and assembly come from both Part I Hom reading equivalences."
      - "Endpoint conversion preserves the complete primitive tables by equality-isomorphism reduction in both modes."
      - "Essential surjectivity uses the concrete finite-fragment assembler, not an assumed witness."
    remaining: []
  certificate_provenance:
    discharged:
      - "Object law proofs are the existing LocalObject IsLawful fields."
      - "Hom law proofs are the existing FullRepresentative.PointLaws and FullExplicit.PointLaws constructors."
      - "Identity and composition certificates are produced by the Part I IdentityLocal and Composition theorems."
    unresolved: []
  proof_use:
    used:
      - "assembleFragments_readFragments and readFragments_assembleFragments"
      - "readFragments_injective"
      - "representativeEndpointHomEquiv_read and explicitEndpointHomEquiv_read"
      - "representativeHomReadingEquiv and explicitHomReadingEquiv"
      - "representativeLocalIdentity_eq_native and explicitLocalIdentity_eq_native"
      - "representativeLocal_read_comp and explicitLocal_read_comp"
      - "ReconstructionData.equivalence and ReconstructionData.existsUnique_preimage"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean: 81 declarations, standard axioms only"
    - "module registered in research/lean/research-modules.txt and ResearchLean/AG.lean"
    - "individual #print axioms on 12 central declarations after review remediation: propext, Classical.choice, Quot.sound only"
    - "git diff --check: pass"
    - "hidden and bidirectional Unicode scan: no match"
    - "Research import direction gate: 228 modules scanned, pass"
    - "fixed GOAL blob: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088"
  blocking_findings: []
  next_obligation: "Part II PR 2/4: lens primitive reading, laws, finite reference fiber, all preserving Homs, and category equivalence."
```

`RepresentativeLocalObject`と`ExplicitLocalObject`が保持する対象dataは、パートIの`LocalObject`一つだけである。
局所Homは`InvariantWitness.Local`と既存の全`PointLaws`からなり、完成済みHomをfieldに追加しない。
任意のnative対象は`assemble_objectData_readFragments`で組立て後の対象と一致させ、`Iso.homCongr`でHomの
型を合わせた後、パートIの全Hom同値へ渡す。`representativeEndpointHomEquiv_read`と
`explicitEndpointHomEquiv_read`が変換前後のtable全体を同一視し、二つの`*_ReadingHomEquiv_point`は
各primitive queryを変換前のnative Hom readerへ接続する。対象側も二つの`*ReadObject_injective`により、
パートIの`readFragments_injective`を新しいobject readerへ接続する。

恒等射と合成は`representativeIdentity` / `representativeComp`および`explicitIdentity` / `explicitComp`として
直接定義し、Category instanceも同じ構成を使う。reading functorの恒等・合成保存は、端点の型変換と
パートIの`*_Local_read_comp`を接続して証明した。両`ReconstructionData`の分離、Hom組立て、対象組立てに
追加仮定はなく、`ReconstructionData.equivalence`を一度適用して両modeの圏同値を得た。


## 特例パートII PR 2/4 selection — lens原始読取りと圏同値

この作業単位はユーザー指定の特例であり、正規Cycleを追加しない。Cycleは79のまま維持する。
一次仕様は固定GOAL A/Bと、Issue #4711の実装設計§2・§4.1・§4.2・§4.4・§7実装順2である。

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 79
special_work_unit: part2-pr2
cycle_increment: false
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 12884419d705624be39e8a87393ed50385395469
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Part I and Part II PR 1/4 are accepted; implementation design is Issue #4711 sections 2, 4.1, 4.2, 4.4, and 7 order 2"
  proof_dag_predecessors:
    - "IndependentCarrierGraph read/assemble, identity/compose, and inverse laws"
    - "IndependentFiniteLawFormula.BoolFormula support and support-preservation theorem"
    - "LensSemantics IsTotalLens, res/ext, homEquivFiberMap"
    - "LensFiberModelEquivalence lensSemanticFiberReading"
    - "LocalReconstructionEquivalence.ReconstructionData.equivalence"
  proof_obligation: "Construct the fixed-input primitive lens object and Hom category, derive all total-lens and preservation laws from finite Boolean formulas, recover every native object and all preserving Homs, and obtain the category equivalence."
  selection_reason: "The geometry branches are connected in PR 1/4; this work supplies the lens branch before protocol and common four-family integration."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentFiniteFragments.lean"
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean"
    - "IndependentLensPrimitiveReconstruction.Object and Hom"
    - "IndependentLensPrimitiveReconstruction.readingFunctor"
    - "IndependentLensPrimitiveReconstruction.equivalence_functor"
    - "IndependentLensPrimitiveReconstruction.reconstructionData and equivalence"
  risks:
    - "A primitive object or Hom could retain a completed native value."
    - "Finite formulas could omit cells used by the native laws."
    - "Local identity or composition could be defined by native readback."
    - "The Hom range could accidentally exclude noninvertible preserving maps."
  unchecked:
    - "Protocol primitive reading is PR 3/4."
    - "The common declaration, mandatory inputs, and Cycle 79 comparison are PR 4/4."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The lens branch uses compatible finite fragments over one dependent carrier/get/put query, computes carrier-match law cells from the unique Type-valued declaration, derives graph laws from closed row instances, carries fiber finiteness as a list cover, and connects direct local assembly to the general reconstruction theorem."
  completion_candidate: no
  lean_artifacts:
    - "IndependentFiniteFragments.FragmentFamily and Compatible"
    - "IndependentFiniteFragments.glue_fragments and fragments_glue"
    - "IndependentLensPrimitiveReconstruction.Object"
    - "IndependentLensPrimitiveReconstruction.Hom"
    - "IndependentLensPrimitiveReconstruction.readObject"
    - "IndependentLensPrimitiveReconstruction.readHom"
    - "IndependentLensPrimitiveReconstruction.assembleObject"
    - "IndependentLensPrimitiveReconstruction.assembleReadHom"
    - "IndependentLensPrimitiveReconstruction.readingFunctor"
    - "IndependentLensPrimitiveReconstruction.reconstructionData"
    - "IndependentLensPrimitiveReconstruction.equivalence"
    - "IndependentLensPrimitiveReconstruction.primitiveFiberEquiv"
    - "IndependentLensPrimitiveReconstruction.readObjectFiberIso"
    - "IndependentLensPrimitiveReconstruction.assembleHom_eq_homEquivFiberMap_symm"
    - "IndependentLensPrimitiveReconstruction.fiberCover_iff_finite"
    - "IndependentLensPrimitiveReconstruction.objectFormula_evaluate_iff_of_base_support"
    - "IndependentLensPrimitiveReconstruction.homFormula_evaluate_iff_of_base_support"
    - "IndependentFiniteFragments.incompatibleBoolFamily_not_compatible"
    - "IndependentLensPrimitiveReconstruction.infiniteFiberTable_not_fiberCover"
  evidence:
    - "IndependentGeometryFiniteFragments keeps its public API as wrappers over the dependent generic fragment construction"
    - "Object and Hom retain compatible finite FragmentFamily values; their tables are defined by singleton glue"
    - "ObjectQuery carries one Type-valued stateCarrier cell and lifted Boolean get and fixed-view put cells"
    - "ObjectLawQuery carrierMatches cells are computed from the unique stateCarrier declaration and are not free primitive data"
    - "putGetFormula, getPutFormula, and putPutFormula include the derived carrier-match cell and graph cells"
    - "getPreservationFormula and putPreservationFormula are closed finite BoolFormula instances over endpoint cells and one state-map graph"
    - "objectFormulaBaseSupport maps every derived object-law support cell to the dependent ObjectTable cell that determines it"
    - "homFormulaBaseSupport maps endpoint and state-map law support cells to one tagged dependent HomPrimitiveTable"
    - "all five formula families preserve evaluation from agreement on their primitive base cells and expose bidirectional assembled point-law APIs"
    - "objectFormula_evaluate_iff_of_base_support uses BoolFormula.evaluate_iff_of_support and the stateCarrier equality bridge for computed carrier matches"
    - "homFormula_evaluate_iff_of_base_support connects source and target carrier declarations, endpoint graph cells, and map graph cells to the derived Hom law table"
    - "readObject_assembleObject and assembleObjectReadIso recover primitive and native objects"
    - "assembleReadHom_readHom and readHom_assembleReadHom prove both Hom inverse laws for all preserving Homs"
    - "identityHom and composeHom use IndependentCarrierGraph.identity and IndependentCarrierGraph.compose directly"
    - "readFiberEquiv_primitiveFiberMap_readHom identifies the primitive fiber action with LensRealization.res"
    - "readObjectFiberIso_naturality compares the primitive object and map readings with lensSemanticFiberReading"
    - "constantFalsePrimitiveHom_fiber_not_injective connects the existing noninvertible fixture"
    - "booleanToUnitPrimitiveHom reads a noninvertible Hom between distinct state-carrier types"
    - "ignoredUpdateTable_rejected gives a concrete failed total-lens formula instance"
    - "flipVisibleTable_getPreservation_rejected gives a concrete failed Hom-preservation formula instance"
    - "incompatibleBoolFamily_not_compatible rejects a Boolean fragment family that changes under finite-set inclusion"
    - "infiniteFiberData_point_laws verifies all three raw lens equations while infiniteFiberTable_not_fiberCover rejects its Nat reference fiber"
  claim_mapping:
    theorem_names:
      - "putGetFormula_evaluate_iff"
      - "getPutFormula_evaluate_iff"
      - "putPutFormula_evaluate_iff"
      - "getPreservationFormula_evaluate_iff"
      - "putPreservationFormula_evaluate_iff"
      - "readObject_assembleObject"
      - "assembleObjectReadIso"
      - "assembleReadHom_readHom"
      - "readHom_assembleReadHom"
      - "existsUnique_preimage"
      - "equivalence"
    source_labels:
      - "fixed GOAL A and B lens branch"
      - "Issue #4711 implementation design sections 2, 4.1, 4.2, 4.4, and 7 order 2"
    conjuncts:
      - "fixed LensFamilyInput -> dependent stateCarrier/get/put ObjectQuery and derived Boolean ObjectLawQuery"
      - "compatible finite fragments -> glued primitive object and state-map tables"
      - "CarrierRows.Instances plus three finite formula families -> IsTotalLens"
      - "primitive reference edges <-> LensRealization.Fiber"
      - "one state-map graph plus two finite formula families -> every LensRealization.Hom"
      - "direct primitive identity and composition -> local Category"
      - "Hom separation, Hom assembly, and object assembly -> ReconstructionData"
      - "ReconstructionData.equivalence -> lens category equivalence"
      - "primitive fiber action -> LensRealization.res and homEquivFiberMap"
      - "readObjectFiberIso -> lensSemanticFiberReading object and map APIs"
    undischarged_assumptions: []
    acceptance_point: "This is the PR 2/4 obligation candidate. Fixed-head review, CI, and merge remain before acceptance."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "CarrierRows.Instances supplies typed total rows for get, every fixed-view put, and state maps through lawful_iff_instances."
      - "The three object formula families derive put_get, get_put, and put_put."
      - "The two Hom formula families derive get_naturality and put_naturality."
      - "FiberCover transfers to native finite reference fibers through fiberCover_iff_finite and primitiveFiberEquiv."
      - "Native finite reference fibers produce FiberCover through fiberCover_iff_finite and readFiberEquiv."
    remaining: []
  certificate_provenance:
    discharged:
      - "Object and Hom store closed formula evaluations and CarrierRows.Instances over glued primitive cells."
      - "Formula support uses BoolFormula.support_finite and evaluation preservation uses BoolFormula.evaluate_iff_of_support."
      - "The five public support-preservation theorems require dependent primitive-cell agreement through objectFormulaBaseSupport or homFormulaBaseSupport."
      - "The compatibility and fiber-cover premises each have a concrete rejection theorem."
      - "Native read, identity, and composition convert graph lawfulness to row instances with lawful_iff_instances.mp."
    unresolved: []
  proof_use:
    used:
      - "IndependentCarrierGraph.read/assemble and both inverse laws"
      - "IndependentCarrierGraph.identity/compose and category-law theorems"
      - "IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support and support_finite"
      - "IndependentFiniteFragments restrictions, compatibility, singleton glue, and both inverse laws"
      - "IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances"
      - "LensRealization.res, ext_res, homEquivFiberMap, and LensRealization.Fiber"
      - "lensSemanticFiberReading and its exact LensRealization.res map"
      - "LocalReconstructionEquivalence.ReconstructionData.equivalence and existsUnique_preimage"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentFiniteFragments.lean: 12 declarations, standard axioms only"
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryFiniteFragments.lean: 20 declarations, standard axioms only"
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean: 303 declarations, standard axioms only"
    - "IndependentFiniteFragments and the lens module are registered in research/lean/research-modules.txt and ResearchLean/AG.lean"
    - "git diff --check and the new-file whitespace check: pass"
    - "placeholder and axiom/admit/sorry/unsafe scan: no match"
    - "hidden and bidirectional Unicode scan: no match"
    - "new Japanese prose forbidden-word scan: no match"
    - "Research import direction gate: 228 modules scanned, pass"
    - "fixed GOAL blob: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088"
  blocking_findings: []
  next_obligation: "Part II PR 3/4: protocol primitive reading, finite path and observation laws, all preserving Homs, and category equivalence."
```

`Object`は、単一のType-valued state carrier宣言とlifted Bool graph cellからなるdependent tableの
compatible finite fragments、row instances、三法則の有限式、primitive reference fiberのlist coverだけを保持する。
候補型の一致Boolは宣言cellから`objectLawTable`が計算し、primitive dataには加えない。
`Hom`はcandidate state-map graphのfinite fragmentsと二つの保存式だけを
保持する。完成した`LensRealization`、完成した`LensRealization.Hom`、decoder像、extension証拠はfieldに
含めない。

対象の三法則とHomの二保存則は、固定pointごとの`BoolFormula`として定義した。5族すべてについて、
derived carrier-match cellを含む`support_finite`、保存済みdependent tableのbase cell一致から導く評価保存、
graph assembly上のpoint lawとの双方向対応を証明した。carrier matchはstate carrier宣言cellの一致から計算し、
Hom側はsource、target、mapのprimitive cellを一つのdependent tableへtagして評価式へ接続する。
対象組立てはこれらの式から`IsTotalLens`を作り、Hom組立ては保存式から既存の`Hom`を作る。
恒等射と合成は`IndependentCarrierGraph.identity` / `compose`を直接使い、同APIの左右単位則・結合則から
Category instanceを得た。

`primitiveFiberEquiv`と`readFiberEquiv`はprimitive reference edge subtypeと既存`LensRealization.Fiber`を
同一のstate上で対応させる。`readFiberEquiv_primitiveFiberMap_readHom`はprimitive Homのfiber作用が既存
`LensRealization.res`とpointwiseに一致することを示し、`assembleHom_eq_homEquivFiberMap_symm`は既存
`homEquivFiberMap`の逆写像へ接続する。既存の非可逆`constantFalseHom`も同じreaderへ渡し、fiber作用が
非単射のまま局所Homに含まれることを確認した。さらに異なるstate carrier型を結ぶ
`booleanToUnitPrimitiveHom`と、Hom保存を破る`flipVisibleTable_getPreservation_rejected`を置いた。

`homSeparation`、`homAssembly`、`objectAssembly`に追加仮定はなく、`reconstructionData`を構成した。
主同値`equivalence`はこの値へ一般`ReconstructionData.equivalence`を一度適用して得る。
`incompatibleBoolFamily_not_compatible`は包含で値が変わるfinite fragment familyを拒否する。
`infiniteFiberData_point_laws`はNat carrierのraw get/putが三法則を満たすことを示し、
`infiniteFiberTable_not_fiberCover`は同じtableをreference fiberの非有限性だけで拒否する。

## 特例パートII PR 3/4 selection — protocol原始読取りと圏同値

この作業単位はユーザー指定の特例であり、正規Cycleを追加しない。Cycleは79のまま維持する。
一次仕様は固定GOAL A/Bと、Issue #4711の実装設計§2・§4.1・§4.3・§4.4・§7実装順3である。

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 79
special_work_unit: part2-pr3
cycle_increment: false
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 5f4f10f75ca78023d3a57b3de94939e599cca6be
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Part II PR 2/4 is present at the selected base; implementation design is Issue #4711 sections 2, 4.1, 4.3, 4.4, and 7 order 3"
  proof_dag_predecessors:
    - "IndependentCarrierGraph read/assemble, identity/compose, and inverse laws"
    - "IndependentFiniteFragments compatible singleton gluing"
    - "IndependentFiniteLawFormula.BoolFormula support preservation"
    - "IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances"
    - "ProtocolSchema pathFunctorOfEdgeAction and evaluatePath"
    - "ProtocolRealization GeneratorMap, res/ext, ext_res/res_ext, res_id/res_comp"
    - "LocalReconstructionEquivalence.ReconstructionData.equivalence"
  proof_obligation: "Construct the fixed-input primitive protocol object and Hom category, derive schema relations and observation squares from finite formulas over existing paths, recover every native object and all preserving Homs, and obtain the category equivalence."
  selection_reason: "The geometry and lens branches are connected; this work supplies the protocol branch before the common four-family integration."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean"
    - "IndependentProtocolPrimitiveReconstruction.Object and Hom"
    - "IndependentProtocolPrimitiveReconstruction.readingFunctor"
    - "IndependentProtocolPrimitiveReconstruction.reconstructionData and equivalence"
  risks:
    - "Dependent Quiver.Path recursion and quotient-lift endpoint inference require focused elaboration."
    - "The readObject constructor must identify graph assembly with native edge and observation functions under proof irrelevance."
    - "The ProtocolPresentation two-to-one fixture uses lifted Fin carriers and requires inferred endpoint reduction."
  unchecked:
    - "Protocol primitive reading review, CI, and merge are pending."
    - "The common declaration, mandatory inputs, and Cycle 79 comparison remain PR 4/4."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The protocol branch uses one dependent carrier/edge/observation query, existing Quiver.Path recursion for finite relation formulas, list covers for vertex finiteness, direct vertex-map graph Homs, and the general reconstruction theorem."
  completion_candidate: no
  lean_artifacts:
    - "IndependentProtocolPrimitiveReconstruction.Object"
    - "IndependentProtocolPrimitiveReconstruction.Hom"
    - "IndependentProtocolPrimitiveReconstruction.pathTraceFormula"
    - "IndependentProtocolPrimitiveReconstruction.pathToFormula"
    - "IndependentProtocolPrimitiveReconstruction.relationFormula"
    - "IndependentProtocolPrimitiveReconstruction.observationFormula"
    - "IndependentProtocolPrimitiveReconstruction.readObject"
    - "IndependentProtocolPrimitiveReconstruction.assembleObject"
    - "IndependentProtocolPrimitiveReconstruction.readHom"
    - "IndependentProtocolPrimitiveReconstruction.assembleReadHom"
    - "IndependentProtocolPrimitiveReconstruction.identityHom"
    - "IndependentProtocolPrimitiveReconstruction.composeHom"
    - "IndependentProtocolPrimitiveReconstruction.readingFunctor"
    - "IndependentProtocolPrimitiveReconstruction.reconstructionData"
    - "IndependentProtocolPrimitiveReconstruction.equivalence"
  evidence:
    - "ObjectQuery contains one Type-valued stateCarrier cell per vertex, named-edge graph cells, and vertex-observation graph cells."
    - "ObjectLawQuery carrierMatches values are computed from stateCarrier cells and are not independent local data."
    - "relationFormula recursively reads existing Quiver.Path edges; pathToFormula requires the second path to end at the first path evaluation."
    - "observationFormula reads the named edge, source observation, and target observation at the mapped source value."
    - "relationFormula_evaluate_iff_raw and observationFormula_evaluate_iff_raw connect finite formulas in both directions to native point laws."
    - "edgePreservationFormula_evaluate_iff_raw and observationPreservationFormula_evaluate_iff_raw characterize Hom formulas directly on raw endpoint and map tables before any Hom is constructed."
    - "objectFormula_evaluate_iff_of_base_support and homFormula_evaluate_iff_of_base_support include derived carrier checks and all graph cells in primitive support."
    - "StateCover is Prop-valued and stateCover_iff_finite connects it to the existing finite carrier premise without adding enumerations to object data."
    - "assembledPathFunctor_relation, assembledFunctor, assembledPathObservation, and assembledObservation use pathFunctorOfEdgeAction, Paths.liftNatTrans, and Quotient.lift."
    - "Hom stores only finite vertex-map graph fragments and edge/observation preservation formulas."
    - "assembleHom and assembleReadHom build the existing GeneratorMap and call ProtocolRealization.ext."
    - "assembleReadHom_readHom and readHom_assembleReadHom use the existing res/ext inverse API and primitive graph inverse laws."
    - "identityHom and composeHom use IndependentCarrierGraph.identity and compose directly."
    - "Hom.ext_table, the table and vertexMapTable evaluation APIs, and assembleEdge_readObject expose semantic readings without unfolding constructors; Category laws, reader functoriality, and observed path comparison use these APIs."
    - "observedRestriction_state, observedRestriction_edge, observedRestriction_path, observedRestriction_observation, and observedRestriction_map compare actual primitive evaluations with the accepted observed restriction reading."
    - "togglingRelationFormula_rejected reuses the existing togglingProtocolLawStructure relation failure."
    - "infiniteProtocol_relation_formula and infiniteProtocol_observation_formula keep the native laws true while infiniteProtocol_not_stateCover rejects the Nat state carrier only through StateCover."
    - "booleanFlipEdge_observationFormula_rejected applies observationFormula_rejected to a finite Bool carrier with lawful flip-edge and identity-observation graphs."
    - "booleanIdentityMap_observationPreservation_rejected applies observationPreservationFormula_rejected to lawful finite identity-map, identity-observation, and flip-observation graphs."
    - "booleanIdentityMap_edgePreservation_rejected applies edgePreservationFormula_rejected to lawful finite flip-edge, identity-edge, and identity-map graphs."
    - "twoToOnePrimitiveHom reads a noninvertible Hom between lifted Fin 2 and lifted Fin 1 state carriers."
  claim_mapping:
    theorem_names:
      - "relationFormula_evaluate_iff_raw"
      - "observationFormula_evaluate_iff_raw"
      - "edgePreservationFormula_evaluate_iff_raw"
      - "observationPreservationFormula_evaluate_iff_raw"
      - "Hom.ext_table"
      - "table_readHom"
      - "table_identityHom"
      - "table_composeHom"
      - "vertexMapTable_readHom"
      - "vertexMapTable_identityHom"
      - "vertexMapTable_composeHom"
      - "assembleEdge_readObject"
      - "booleanFlipEdge_observationFormula_rejected"
      - "booleanIdentityMap_observationPreservation_rejected"
      - "booleanIdentityMap_edgePreservation_rejected"
      - "readObject_assembleObject"
      - "assembleObjectReadIso"
      - "assembleReadHom_readHom"
      - "readHom_assembleReadHom"
      - "existsUnique_preimage"
      - "equivalence"
      - "observedRestriction_path"
      - "twoToOnePrimitiveHom_not_injective"
    source_labels:
      - "fixed GOAL A and B protocol branch"
      - "Issue #4711 implementation design sections 2, 4.1, 4.3, 4.4, and 7 order 3"
    conjuncts:
      - "fixed ProtocolFamilyInput -> dependent vertex carrier, named edge, and observation queries"
      - "compatible finite fragments -> glued primitive object and vertex-map tables"
      - "CarrierRows.Instances plus relation and observation formulas -> ProtocolRealization"
      - "one map graph per vertex plus edge and observation formulas -> every GeneratorMap and semantic Hom"
      - "direct primitive identity and composition -> local Category"
      - "Hom separation, Hom assembly, and object assembly -> ReconstructionData"
      - "ReconstructionData.equivalence -> protocol category equivalence"
      - "primitive vertex, edge, observation, and map evaluation -> protocolObservedRestrictionObject and protocolObservedRestrictionMap"
    undischarged_assumptions: []
    acceptance_point: "This is the PR 3/4 implementation candidate. Focused elaboration, fixed-head review, CI, and merge remain before acceptance."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "CarrierRows.Instances produces lawful total functions for every named edge, observation, and vertex map."
      - "The pointwise relation formulas discharge the quotient relation premise through the existing relation_sound equations."
      - "The pointwise observation formulas discharge naturality through the existing ProtocolRealization observation transformation."
      - "StateCover supplies exactly the existing finite-state premise through stateCover_iff_finite."
      - "The Hom formulas discharge GeneratorMap edge and observation preservation for every state."
    remaining: []
  certificate_provenance:
    discharged:
      - "Object and Hom retain finite fragments, closed formula evaluations, graph-row instances, and state list covers over their glued primitive cells."
      - "Derived carrier-match queries are computed from stateCarrier cells and are included in primitive support through objectFormulaBaseSupport and homFormulaBaseSupport."
      - "Native read, identity, and composition derive row instances from IndependentCarrierGraph lawfulness rather than accepting completed semantic maps as local fields."
      - "The relation, observation, edge-preservation, and observation-preservation formulas each have direct raw evaluation equivalences and concrete finite lawful rejection fixtures."
    unresolved: []
  proof_use:
    used:
      - "IndependentCarrierGraph read/assemble, identity/compose, and inverse and category laws"
      - "IndependentFiniteFragments restriction, compatibility, singleton glue, and inverse laws"
      - "IndependentFiniteLawFormula.BoolFormula support and evaluation preservation"
      - "IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances"
      - "ProtocolSchema evaluatePath, pathFunctorOfEdgeAction, relation_sound, Paths.liftNatTrans, and Quotient.lift"
      - "ProtocolRealization res/ext, naturality, and category APIs"
      - "LocalReconstructionEquivalence.ReconstructionData.equivalence and existsUnique_preimage"
      - "Protocol observed-restriction object and map APIs"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  completion_scope: "Part II PR 3/4 only; A/B common integration, mandatory inputs, and Cycle 79 comparison are not claimed."
  validation_refs:
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean: 327 declarations, standard axioms only"
    - "module registered in research/lean/research-modules.txt and ResearchLean/AG.lean"
    - "git diff --check and the new-file whitespace check: pass"
    - "placeholder and axiom/admit/sorry/unsafe scan: no match"
    - "hidden and bidirectional Unicode scan: no match"
    - "privacy scan: no match"
    - "new Japanese prose forbidden-word scan: no match"
    - "Research import direction gate: 228 modules scanned, pass"
    - "fixed GOAL blob unchanged: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088"
  blocking_findings: []
  next_obligation: "Part II PR 4/4: common declaration, mandatory inputs, the main equivalence, and specified route comparisons."
```

`Object`は各頂点のcarrier宣言、生成辺graph、観測graphのcompatible finite fragments、各graphのrow
instances、relationと観測squareのpointwise有限式、各carrierのlist coverだけを保持する。relation式は
既存`Quiver.Path`を直接再帰し、左pathの実評価と同じ終点へ右pathが到達するセル列を要求する。
`Hom`は各頂点mapのgraph fragmentsと、生成辺・観測を保存する式だけを保持する。

対象組立ては生成辺作用からfree-path functorを作り、relation式からquotientへ降ろす。観測squareは
`Paths.liftNatTrans`で全pathへ延長し、`Quotient.lift`で得たfunctor上の自然変換へ接続する。Hom組立ては
各頂点graphから既存`GeneratorMap`を作り、`ProtocolRealization.ext`へ渡す。恒等射と合成はgraphの
`identity`と`compose`から直接定義する。主同値は`ReconstructionData.equivalence`を一度適用して得る。

既存protocol observed restrictionとの比較は、頂点carrier、生成辺評価、観測値、Homの頂点mapを個別の
定理で固定した。成立例は任意のnative object/Homの`readObject`/`readHom`で与える。具体的な拒否例は
既存のtoggle relation fixtureに加え、Bool carrier上のlawfulなedge・observation・map graphだけを使う
`booleanFlipEdge_observationFormula_rejected`、
`booleanIdentityMap_observationPreservation_rejected`、
`booleanIdentityMap_edgePreservation_rejected`で与えた。異なるstate型間の非可逆Homは`Fin 2`から`Fin 1`への
既存decoder経路で構成し、そのprimitive componentが非単射であることを示す。

## 特例パートII PR 4/4 selection — 共通宣言・必須入力・既存経路比較

一次仕様は固定GOAL A/Bと、Issue #4711の実装設計§2・§5–§7である。

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 79
special_work_unit: part2-pr4
cycle_increment: false
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: a162077b5b937834aef8f71b6141347adc0edb64
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Part II PR 1/4--3/4 are present at the selected base; implementation design is Issue #4711 sections 2, 5, 6, and 7 order 4"
  proof_dag_predecessors:
    - "IndependentGeometryCategoryReconstruction representative and explicit reconstruction data"
    - "IndependentLensPrimitiveReconstruction reconstruction data and existing finite-fiber reader"
    - "IndependentProtocolPrimitiveReconstruction reconstruction data and observed-restriction reader"
    - "IndependentFiniteFragments restriction, compatibility, glue, and inverse laws"
    - "LocalReconstructionEquivalence.ReconstructionData.equivalence"
    - "Mandatory-C tagged source choices and canonical normalization"
    - "G122OriginalInput generated endpoints, comparisons, projectors, and raw comparison group"
    - "AATFourFamilyTotalReconstruction Cycle 79 fiber inclusions and reading squares"
  proof_obligation: "Connect the four accepted branch reconstructions through one parameter and reader, construct one reconstruction datum and main equivalence, include the mandatory tagged and G-122 inputs, and compare the accepted routes without rebuilding their internals."
  selection_reason: "The four branch readers and their direct assembly data are available; the remaining Part II work is their common dependent interface and the fixed A/B route connections."
  expected_result_type: proof-checkpoint
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean"
    - "IndependentAATPrimitiveReconstruction.Parameter"
    - "IndependentAATPrimitiveReconstruction.reading"
    - "IndependentAATPrimitiveReconstruction.reconstructionData"
    - "IndependentAATPrimitiveReconstruction.equivalence"
  risks:
    - "The four native Hom universes differ; the common family must add only the required ULiftHom wrappers."
    - "The main equivalence must use direct branch assembly data rather than selecting four completed equivalences."
    - "The G-122 Arrow comparison must retain both endpoint automorphisms."
  unchecked:
    - "The final scoped Part II/A/B completion decision and merge evidence are recorded in tracking Issue #4711 for this ledger head."
    - "G-124 targets C--E remain later work."
result:
  reviewed_head: dcf3e951d533f8d2530c3ea0dc0a5be2e7dcf79b
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Common object, Hom, and packed tables now carry branch-specific independent data through compatible finite families. Geometry Hom certificates retain the full Part I presentation as data, while lens and protocol certificates retain their existing proof packages. Two-sided family equivalences connect those families to the four accepted primitive local categories, and one common ReconstructionData uses their inverse laws. Tagged and G-122 readers connect to their Cycle 79 fibers through direct lifts; lens and protocol decoder, retract, Karoubi, and Arrow routes reuse the accepted comparisons."
  completion_candidate: no
  milestone_completion_candidate: "Part II and fixed targets A/B"
  lean_artifacts:
    - "IndependentAATPrimitiveReconstruction.Parameter"
    - "IndependentAATPrimitiveReconstruction.Query"
    - "IndependentAATPrimitiveReconstruction.FragmentFamily"
    - "IndependentAATPrimitiveReconstruction.ObjectTable"
    - "IndependentAATPrimitiveReconstruction.HomTable"
    - "IndependentAATPrimitiveReconstruction.ObjectTableLaws"
    - "IndependentAATPrimitiveReconstruction.GeometryHomTableCertificate"
    - "IndependentAATPrimitiveReconstruction.HomTableCertificate"
    - "IndependentAATPrimitiveReconstruction.LawfulObjectFamily"
    - "IndependentAATPrimitiveReconstruction.LawfulHomFamily"
    - "IndependentAATPrimitiveReconstruction.localObjectFamilyEquiv"
    - "IndependentAATPrimitiveReconstruction.localHomFamilyEquiv"
    - "IndependentAATPrimitiveReconstruction.reading"
    - "IndependentAATPrimitiveReconstruction.assembleObject"
    - "IndependentAATPrimitiveReconstruction.assembleHom"
    - "IndependentAATPrimitiveReconstruction.reconstructionData"
    - "IndependentAATPrimitiveReconstruction.equivalence"
    - "IndependentAATPrimitiveReconstruction.taggedRepresentedReadingIso"
    - "IndependentAATPrimitiveReconstruction.finiteAxisFoldRawComparisonReadingIso"
    - "IndependentAATPrimitiveReconstruction.lensFiberComparisonIso"
    - "IndependentAATPrimitiveReconstruction.protocolObservedComparisonIso"
    - "IndependentAATPrimitiveReconstruction.lensFiniteDecoder_retractGeneratedBy"
    - "IndependentAATPrimitiveReconstruction.protocolFiniteDecoder_retractGeneratedBy"
    - "IndependentAATPrimitiveReconstruction.lensKaroubiEquivalence"
    - "IndependentAATPrimitiveReconstruction.protocolKaroubiEquivalence"
    - "IndependentAATPrimitiveReconstruction.lensKaroubiArrowEquivalence"
    - "IndependentAATPrimitiveReconstruction.protocolKaroubiArrowEquivalence"
    - "IndependentAATPrimitiveReconstruction.cycle79TaggedRepresentedTotalReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79G122RawTotalReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79LensPrimitiveFiniteDecoderReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79ProtocolPrimitiveFiniteDecoderReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79LensPrimitiveKaroubiReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79ProtocolPrimitiveKaroubiReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79LensPrimitiveKaroubiArrowReadingIso"
    - "IndependentAATPrimitiveReconstruction.cycle79ProtocolPrimitiveKaroubiArrowReadingIso"
  evidence:
    - "Parameter has representative geometry, explicit geometry, lens, and protocol input forms; NativeCategory and LocalCategory retain the accepted branch object and Hom conditions."
    - "Query tags source-object, target-object, and Hom queries; ObjectTable, HomTable, packTable, localTable, and nativeTable expose the common finite cells."
    - "ObjectTableLaws selects the existing object predicates. GeometryHomTableCertificate stores the full Part I Presentation, its retained table, point laws, and canonical readback; HomTableCertificate stores this geometry data or the existing lens and protocol proof packages without existential selection."
    - "LawfulObjectFamily and LawfulHomFamily combine compatible finite fragments with the selected tables and certificates; localObjectFamilyEquiv and localHomFamilyEquiv prove both inverse directions to the existing local categories."
    - "assembleObjectFamily and assembleHomFamily compose the family adapters with the PR 1--3 assemblers, and reconstructionData uses those family inverse laws."
    - "homSeparation and existsUnique_preimage expose uniqueness and existence separately."
    - "The lens certificate rejects mismatched carriers, an all-false table on an inhabited source, and duplicate outputs. The common lens reader retains a constant-false noninjective Hom, and the common explicit geometry reader separates two coefficient projections with the same base action."
    - "lensPackageInclusion and protocolPackageInclusion retain the accepted fully faithful semantic package functors and all their Homs."
    - "taggedSourceChoiceNativeHom ranges over every source choice; taggedUniformFlipNativeHom_base identifies the constant-true choice, and taggedNormalizationNativeHom_idempotent retains canonical normalization."
    - "taggedRepresentedInclusion retains the old generated exact Homs, and taggedRepresentedReadingIso compares them through the common reader."
    - "The fixed G-122 objects retain the original, direct, and via-base packages; barAlpha, both cochain-selected barBeta values, barE, and barD are native Homs with factorization, idempotence, and point-evaluation theorems."
    - "finiteAxisFoldRawComparisonInclusion maps every old raw comparison to Arrow(NativeCategory), and its left and right theorems retain the two endpoint automorphisms separately."
    - "taggedRepresentedReadingIso and finiteAxisFoldRawComparisonReadingIso use the accepted old equivalence inverse and Equivalence.funInvIdAssoc."
    - "lensFiniteDecoder and protocolFiniteDecoder compose the accepted semantic decoders with the new primitive equivalence; their retract-generation theorems transport the accepted semantic retract witnesses."
    - "The Karoubi and Arrow equivalences reuse the accepted semantic equivalences, and their comparison isomorphisms recover the existing finite-fiber and observed routes."
    - "The tagged represented reader and raw G-122 reader are lifted directly into their existing Cycle 79 branches; cycle79TaggedTotalReading_common and cycle79G122TotalReading_common identify their total readings with the common readers on each Hom."
    - "The lens and protocol decoder, Karoubi, and Arrow routes are connected by natural isomorphisms to the existing Cycle 79 total reading; no Cycle 79 category or decoder is rebuilt."
  claim_mapping:
    theorem_names:
      - "fragments_compatible"
      - "glue_fragments"
      - "fragments_glue"
      - "read_assembleHom"
      - "assembleHom_read"
      - "readAssembledObjectIso"
      - "localObjectTable_read"
      - "localTable_read"
      - "localObjectFamilyEquiv"
      - "localHomFamilyEquiv"
      - "localHomFamily_read_assemble"
      - "assembleHomFamily_read"
      - "lawfulHomFamily_existsUnique_preimage"
      - "homSeparation"
      - "existsUnique_preimage"
      - "equivalence"
      - "lensHomTableCertificate_mismatched_carrier_rejected"
      - "lensHomTableCertificate_false_table_rejected"
      - "lensHomTableCertificate_duplicate_outputs_rejected"
      - "lensConstantFalseNativeHom_family_recovery"
      - "lensConstantFalseNativeHom_fiber_not_injective"
      - "explicitCoefficientProjection_commonReading_distinct"
      - "taggedUniformFlipNativeHom_base"
      - "taggedNormalizationNativeHom_idempotent"
      - "finiteAxisFoldBarBetaNativeHom_factor"
      - "finiteAxisFoldBarBetaNativeHom_source_factorization"
      - "finiteAxisFoldBarBetaNativeHom_target_factorization"
      - "finiteAxisFoldIdentityCochain_barBeta_eq_barAlpha_common"
      - "finiteAxisFoldRawComparisonInclusion_left"
      - "finiteAxisFoldRawComparisonInclusion_right"
      - "finiteAxisFoldTwistedComparison_left"
      - "finiteAxisFoldTwistedComparison_right"
      - "finiteAxisFoldTwistedComparison_read_raw"
      - "finiteAxisFoldTwistedComparison_multiply"
      - "lensFiberComparisonIso_hom_app_apply"
      - "protocolObservedComparisonIso_hom_app_vertex"
      - "lensFiniteDecoder_retractGeneratedBy"
      - "protocolFiniteDecoder_retractGeneratedBy"
      - "cycle79TaggedTotalReading_common"
      - "cycle79G122TotalReading_common"
    source_labels:
      - "fixed GOAL A and B"
      - "Issue #4711 implementation design sections 2, 5, 6, and 7 order 4"
    conjuncts:
      - "one fixed parameter family -> four existing native and local category forms"
      - "one tagged query family -> existing dependent finite fragments"
      - "direct concrete assembly and separation -> one common ReconstructionData"
      - "ReconstructionData.equivalence -> main category equivalence"
      - "mandatory tagged and G-122 inputs -> actual common native objects and Homs"
      - "old generated, Arrow, finite-fiber, observed, and Cycle 79 routes -> explicit comparison APIs"
    undischarged_assumptions: []
    acceptance_point: "This is the Part II PR 4/4 and fixed A/B implementation candidate. Fixed-head four-lane review and CI passed at dcf3e951d533f8d2530c3ea0dc0a5be2e7dcf79b. The final scoped completion decision and merge evidence are recorded in Issue #4711."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "The four branch assembly and separation results are supplied by the accepted PR 1--3 reconstruction data."
      - "No decoder image, finite presentation, invertibility, or extension premise is added to the native categories."
      - "The fixed tagged and G-122 witnesses use their accepted semantic objects and Homs."
    remaining: []
  certificate_provenance:
    discharged:
      - "The common reconstruction datum is built in this module from direct branch assembly functions and their inverse proofs."
      - "The geometry Hom certificate keeps the complete Part I Presentation, including retained and auxiliary finite families, as input data; localHomOfFamily consumes that value directly without Classical.choose."
      - "Lens and protocol Hom certificates lift their existing proof packages into data and add no completed semantic Hom."
      - "The tagged source-choice, normalization, G-122 comparison, and endpoint maps are existing semantic Homs lifted into the common categories."
      - "The Arrow inclusion reads both endpoint maps from each raw comparison rather than replacing them with a selected subgroup code."
    unresolved: []
  proof_use:
    used:
      - "PR 1 representative and explicit geometry reconstruction data"
      - "PR 2 lens primitive reconstruction data and finite-fiber reading"
      - "PR 3 protocol primitive reconstruction data and observed-restriction reading"
      - "LocalReconstructionEquivalence reconstruction theorem"
      - "Mandatory-C tagged source-choice and normalization theorems"
      - "G122OriginalInput generated comparison and projector theorems"
      - "AATFourFamilyTotalReconstruction Cycle 79 APIs"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  completion_scope: "Part II and fixed targets A/B only. The overall G-124 result remains proof-checkpoint at Cycle 79 because C--E are still open."
  validation_refs:
    - "check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean: 379 declarations, standard axioms only"
    - "fixed-head math A/B and Lean A/B review at dcf3e951d533f8d2530c3ea0dc0a5be2e7dcf79b: four No major findings decisions"
    - "PR #4842 CI at dcf3e951d533f8d2530c3ea0dc0a5be2e7dcf79b: all 7 checks succeeded; merge state CLEAN"
    - "module registered in research/lean/research-modules.txt and ResearchLean/AG.lean"
    - "git diff --check: pass"
    - "placeholder and axiom/admit/sorry/unsafe scan: no match"
    - "hidden and bidirectional Unicode scan: no match"
    - "privacy scan: no match"
    - "Research import direction gate: pass"
    - "fixed GOAL blob unchanged: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088"
  blocking_findings: []
  next_obligation: "After acceptance of this Part II/A/B milestone, G-124 target C is projections, normalization, and comparison-group compatibility, including the three fixed G-122 cases."
```

`IndependentAATPrimitiveReconstruction.lean`は、PR 1–3で確定した四つの圏と原始readerを
一つの`Parameter`から選ぶ。共通部はqueryの役割付け、有限片、reading、直接組立て、両逆に限る。
四つの完成済み同値を主結果として選ぶのではなく、各枝の組立てデータから一つの
`reconstructionData`を作り、`ReconstructionData.equivalence`を一度適用する。

必須入力では、タグ付きsource-choiceの全元、一様flip、canonical正規化をexplicit形へ収録した。
G-122では固定した三対象、`barAlpha`、生成cochainと定数1 cochainの`barBeta`、左右の冪等射を
representative形へ収録し、原始評価と因子化を示した。旧raw比較は両端の自己同型を保ったまま
`Arrow`へ送る。geometryのHom certificateはPart Iの`Presentation`をデータとして保持し、
そのretained familyとauxiliary familyを選び直さず組立てに渡す。lensとprotocolは既存の
証明packageをデータとして保持する。carrier不一致、all-false、出力重複を拒否するfixture、
非単射なconstant-false lens Hom、同じbase actionを持つ異なるgeometry Homも共通reader上で確認した。

tagged represented readerとG-122 raw readerは既存Cycle 79の各枝へ直接liftし、total readingと
共通readerのHom評価が一致することを示した。lensの有限fiber、protocolのobserved reading、
decoder・Karoubi・Arrowの既存APIも作り直さず比較に接続した。

この単位はパートIIと固定target A/Bの完了候補である。共通有限族から四つの局所圏への両逆、
旧経路の成分評価、CSのdecoder・retract・Karoubi・Arrow、Cycle 79のtotal readingへの自然同型を
focused checkで確認した。固定head `dcf3e951d533f8d2530c3ea0dc0a5be2e7dcf79b`に対する
数学A/B・Lean A/Bの4本査読は全て`No major findings`、CIは7件全て成功した。最終の
A/B・パートII限定完了判定とmerge証拠は、この台帳headを対象にIssue #4711へ記録する。
G-124全体はC–Eが残るため、Cycle 79の`proof-checkpoint`を維持する。

## Cycle 81 — Part III-1 direct component projections (proposal)

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 81
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: b6e60f2c42acf551659d7b064bae416c982fbdc6
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Fixed A/B main reader is accepted; Issue #4711 and the G-124 design III-1 identify direct bottom, observation, and coefficient projections as the next C obligation. Rejected Cycle 80 IV-1 remains separate and unmerged."
  proof_dag_predecessors:
    - "IndependentAATPrimitiveReconstruction.Parameter, reading, localObjectTable, localHomTable"
    - "IndependentCoreTableAssembly.finiteExtractionEquiv and IndependentGeometryHomPrimitive.PackageAssembly.lower"
    - "IndependentGeometryHomPrimitive Context, Observable, and realization point assemblers"
    - "IndependentLensPrimitiveReconstruction and IndependentProtocolPrimitiveReconstruction direct primitive graph readers"
    - "CSAATArchitectureObjects exact doctrine and source-map formulas"
    - "FullGeometryNormalization.rawGeometryBottomProjection"
  proof_obligation: "Construct bottom, observation, and coefficient component categories and direct primitive local functors for all four fixed parameters; prove three natural isomorphisms along the one main reader and preserve the original component evaluation and bottom-fixed condition."
  selection_reason: "The main A/B reader exists; III-1 supplies the component maps and naturality required before C comparison groups and normalization can be transported."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "G124ProjectionBottom and G124ProjectionCoefficient"
    - "G124ProjectionObservationComponents and G124ProjectionCS"
    - "G124ProjectionLift, G124ProjectionCSLift, and G124ProjectionGlobal"
    - "G124ProjectionBottomNormalization"
  risks:
    - "A projection target must retain its actual component data and laws without requiring full realization liftability."
    - "Local functor definitions must select primitive rows; complete assemblers may occur only in comparison proofs."
    - "Explicit context action, CS noninjective state maps, path naturality, and directed coefficient maps must survive."
    - "Universe presentation must be categorically equivalent to each original component target."
  unchecked:
    - "Fixed-head standard PR review and independent mathematical/Lean lane decisions."
    - "PR CI and Issue synchronization after review."
    - "The remaining III-2/III-3 and IV-1/IV-2/IV-3 work is outside this one design part."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Direct geometry and CS component categories and primitive local functors now evaluate bottom, observation, and coefficient data. Each parameter has three natural comparisons with the fixed main reader; bottom fixedness is preserved and reflected by canonical conjugation."
  completion_candidate: no
  lean_artifacts:
    - "G124ProjectionGlobal.bottomReadingIso"
    - "G124ProjectionGlobal.observationReadingIso"
    - "G124ProjectionGlobal.coefficientReadingIso"
    - "G124ProjectionBottomNormalization.bottom_fixed_iff"
    - "G124ProjectionGlobal.componentEquivalence"
  evidence:
    - "G124ProjectionBottom representative/explicit direct lower and core functors, natural isomorphisms"
    - "G124ProjectionObservationComponents representative/explicit retained observation target categories and natural isomorphisms"
    - "G124ProjectionCS direct lens/protocol get and path observation, pointed source maps, and natural isomorphisms"
    - "G124ProjectionCoefficient directed CommRingCat maps; CS fixed integer identity"
    - "G124ProjectionLift original local object/Hom table point evaluations and auxiliary choice independence"
  claim_mapping:
    theorem_names:
      - "G124ProjectionGlobal.bottomReadingIso"
      - "G124ProjectionGlobal.observationReadingIso"
      - "G124ProjectionGlobal.coefficientReadingIso"
      - "G124ProjectionBottomNormalization.bottom_fixed_iff"
    source_labels:
      - "Fixed GOAL C first sentence: bottom, observation, coefficient projections and main N natural comparisons"
      - "Design III-1: original component evaluation, geometry modes, CS readers, and canonical bottom conjugation"
    conjuncts:
      - "Every Parameter branch -> exact component category, native functor, direct local functor, and natural iso"
      - "Bottom -> pointed extraction/source action; geometry core intermediate; admissible raw bottom agreement"
      - "Observation -> context/restriction/observable ring and realization actions, including explicit actual context action and CS slices"
      - "Coefficient -> directed geometry ring hom; fixed CS integer identity"
      - "Bottom-fixed endomorphism -> preservation and reflection through canonical conjugation"
    undischarged_assumptions: []
    acceptance_point: "Proposal for the complete III-1 design part only. Fixed-head independent review and CI remain required before acceptance or merge."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "The four branch native/local categories and main reader are the accepted fixed A/B predecessors."
      - "Projection target objects and Homs are constructed with retained components and their original preservation laws."
    remaining: []
  certificate_provenance:
    discharged:
      - "Geometry lower/source, coefficient, context, observable, and realization maps consume the retained common primitive table and point laws."
      - "CS bottom/observation maps consume carrier, get, state, edge, and observe point graphs; path naturality is proved from generators and quotient extension."
      - "ULiftHom/ULift are equivalences of the exact component categories, not image or liftability restrictions."
    unresolved: []
  proof_use:
    used:
      - "Primitive extraction, package, context, observable, and realization assemblers"
      - "CS exact doctrine and direct point graph/path APIs"
      - "The one main IndependentAATPrimitiveReconstruction.reading"
      - "Raw geometry bottom and canonical normalization predecessor"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "G124ProjectionBottomNormalization targeted build, including all eight new projection dependencies: pass; all namespace audits standard axioms only."
    - "Global focused check: pass; six spine #print axioms: propext, Classical.choice, Quot.sound only."
    - "git diff --cached --check, placeholder/privacy/Unicode/import-direction scans: pass."
    - "Review and CI: pending PR."
  blocking_findings: []
  next_obligation: "After acceptance of III-1, design III-2 normalization, Karoubi/Arrow, and arbitrary comparison-group transport."
```

III-1は一つのPR単位として固定する。`BottomTarget`、`ObservationTarget`、`CoefficientTarget`は
元の成分圏を`ULift`と`ULiftHom`で表示し、`componentEquivalence`で元の全対象・全射へ戻る。
局所関手の対象・射の定義は原始表の対応する成分を選び、完成した幾何やCSの逆組立ては
自然同型や関手則の証明にのみ使う。全体G-124の完了判定はCの残部とD・Eの証拠を要する。

## Cycle 82 — Part III-2 normalization and comparison transport (proposal)

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 82
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: ed962bae2677474676ea14f50cff8ecfd9e3a7b9
tracking_issue: 4711
selection:
  proof_state_ref: "III-1 was accepted and merged as PR #4936; the fixed design III-2 is the next C obligation. The rejected IV-1 Cycle 80 remains separate."
  proof_dag_predecessors:
    - "Accepted A/B main reader and fully faithful comparison transport"
    - "Accepted III-1 direct bottom, observation, and coefficient natural isomorphisms"
    - "CanonicalNormalization and independent primitive object/Hom assemblies"
    - "G-119 Karoubi/Arrow naturality and G-120 ObservationEquiv/GroupHomRestriction"
  proof_obligation: "Construct primitive canonical normalization and the local projector, connect it to main N, evaluate Karoubi/Arrow on all parameters, and transport arbitrary comparison groups and qualified observation diagrams through direct projection squares."
  selection_reason: "III-2 composes the accepted component projections with normalization and comparison transport before III-3 kernel analysis."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "G124PrimitiveNormalization"
    - "G124KaroubiProjection"
    - "G124ComparisonTransport"
    - "G124ProjectionGroupSquare"
    - "G124ComparisonObservationTransport"
    - "G124TaggedNormalization"
  risks:
    - "Canonical admissibility is an object condition only; all original local Homs remain available."
    - "Projector equality must use the accepted main reader, not a replacement equivalence."
    - "Arbitrary comparison arrows need no inverse, section, or surjectivity premise."
    - "Restricted kernels must be distinguished from ambient kernels."
  unchecked:
    - "Revised fixed-head standard PR review, including the local projector construction-strength question raised on the first head."
    - "PR CI and Issue synchronization after review."
    - "The remaining III-3 and IV-1/IV-2/IV-3 obligations remain open."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The primitive object condition is equivalent to native canonical admissibility. The local projector is formed first by localWith from the normalized core map, identity coefficient map, and three direct identity-comparison realization point families of the assembled primitive object; its all-query evaluation and equality to the accepted native reader are proved separately. The local projector is idempotent and is the main reader image of native normalization. General Karoubi/Arrow and all comparison groups use the same reader. Direct projection natural isomorphisms give exact arbitrary component-subgroup map equations and the qualified squares used for G-120 kernel, fiber, lift, and exactness transport."
  completion_candidate: no
  lean_artifacts:
    - "G124PrimitiveNormalization.representative_read_projector"
    - "G124PrimitiveNormalization.representativeProjector_primitive_point"
    - "G124PrimitiveNormalization.main_read_projector"
    - "G124PrimitiveNormalization.main_canonicalKaroubi_projector"
    - "G124PrimitiveNormalization.representativeProjector_idem"
    - "G124PrimitiveNormalization.localNormalizationFunctor"
    - "G124KaroubiProjection.karoubiArrowReaderNaturality"
    - "G124KaroubiProjection.karoubiComparisonHomEquiv"
    - "G124ComparisonTransport.comparisonMulEquiv"
    - "G124ProjectionGroupSquare.bottom_comparison_mem_iff"
    - "G124ProjectionGroupSquare.qualifiedComparison_map_eq"
    - "G124ComparisonObservationTransport.bottomRestrictedKernelEquiv"
    - "G124ComparisonObservationTransport.bottomRestricted_shortExact_iff"
    - "G124TaggedNormalization.taggedLocalProjector_generation"
  claim_mapping:
    source_labels:
      - "Fixed GOAL C: normalization, Karoubi/Arrow, arbitrary comparison groups, G-120"
      - "Design III-2: all four parameters and three direct projections"
    conjuncts:
      - "Primitive five-law admissibility iff accepted native condition; corresponding full subcategories"
      - "Local projector point/object evaluation, main reader image, complete-Hom idempotence, absorption, and normalized identity"
      - "General Kar/Arr/Kar(Arr) reader and three projection evaluations"
      - "Any-arrow comparison group isomorphism, source and iso-section compatibility"
      - "Endpoint/pair squares; bottom-fixed and arbitrary specified component subgroup preservation, reflection, and exact map equalities"
      - "Normalized Karoubi comparisons are preserved and reflected on all Homs by the main reader"
      - "The tagged explicit normalization and source-choice rewrite are read by the same main reader"
      - "G-120 compatible kernels, fibers, actions, reflection criterion, lifts, and conditional short exactness"
    undischarged_assumptions:
      - "CanonicalObjectNormalizationAdmissible is an explicit object condition of the normalization full subcategory; it is not asserted for every geometry."
    acceptance_point: "Proposal for the complete III-2 design part. Fixed-head independent review and CI are required before acceptance."
audits:
  premise_delta:
    discharged:
      - "The canonical normalization five laws are identified with the same primitive object predicate; no arbitrary-object existence is claimed."
      - "The main reader, component natural isomorphisms, and fully faithful comparison transport are accepted predecessors."
    remaining: []
  certificate_provenance:
    discharged:
      - "The projector Hom value is constructed by localWith from normalized core, identity coefficient map, and direct identity-comparison realization point readers. The native normalization ReadHom appears only in the separate equality proof, which supplies the complete-Hom law witness; all-query and component evaluations are separate."
      - "Comparison transport uses the accepted main equivalence and direct component squares."
    unresolved: []
  proof_use:
    used:
      - "Independent primitive assembly and NativeReader point laws"
      - "CanonicalNormalization, G-119 Karoubi/Arrow, G-120 ObservationEquiv and GroupHomRestriction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "Targeted G124TaggedNormalization and G124ComparisonObservationTransport builds: pass; all six namespace audits standard axioms only."
    - "The third PR fixed-head review found that localWith still extracted coefficient and realization fields from a completed native ReadHom. The next revision constructs those point values directly; fixed-head review, CI, and final scans remain pending."
  blocking_findings: []
  next_obligation: "After III-2 acceptance, prove design III-3 primitive kernel and G-122 three-case connection."
```

## Cycle 83 — Part III-3 primitive kernel and fixed G-122 three cases (proposal)

```yaml
ledger_type: target_cycle_result
goal: G-124
cycle: 83
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: c4d1b933c67c9f87163bf02708b46459a37d2ac2
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "III-1 PR #4936 and III-2 PR #4937 were accepted and merged; the fixed design III-3 is the remaining C obligation."
  proof_dag_predecessors:
    - "Accepted A/B main reader and III-2 local canonical normalization"
    - "G-122 full restricted comparison/kernel/section and ambient-kernel separation"
    - "G-120 group restriction, fiber, and observation transport"
    - "G-122 three generated comparisons in the same fixed parameter"
  proof_obligation: "Classify the fixed G-122 comparison kernel by independent primitive local Hom conditions, commute native/local normalization, distinguish restricted and ambient kernels, transport section and every fiber, and connect the three fixed comparison cases."
  selection_reason: "The fixed C classification requires full local kernel and all-comparison transport, beyond the general III-2 comparison equivalence."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "G124PrimitiveKernel"
  risks:
    - "The primitive code must store local forward/backward Homs and point equations, not a native FullKernel."
    - "Restricted and ambient kernels must remain distinct; the ambient counterexample must use the same local element at both endpoints."
    - "The generated barBeta is not invertible, so the conjugation section applies only to barAlpha and the equal constant-one case."
  unchecked:
    - "Fixed-head standard PR review, root acceptance audit, CI, and Issue synchronization."
    - "IV-1/IV-2/IV-3/IV-4 remain separate design parts."
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "The G-122 full comparison normalization commutes with primitive local normalization. An independent four-Hom primitive kernel code classifies all restricted-kernel elements in both directions. The full ambient endpoint kernel is separately transported, with one local bottom/coefficient-fixed element outside the restricted image. The local section, split short exact sequence, twisted coordinates, and all lift fibers retain the original opposite-kernel/right-action convention."
  completion_candidate: no
  lean_artifacts:
    - "G124PrimitiveKernel.primitiveKernelPoints_iff"
    - "G124PrimitiveKernel.fixedG122Normalization_commutes"
    - "G124PrimitiveKernel.fixedG122MainReading_barAlpha"
    - "G124PrimitiveKernel.fixedG122MainReading_generatedBarBeta_not_isIso"
    - "G124PrimitiveKernel.fixedG122MainReading_generatedFactor"
    - "G124PrimitiveKernel.fixedG122PrimitiveKernelMulEquiv"
    - "G124PrimitiveKernel.fixedG122PrimitiveAmbientKernelMulEquiv"
    - "G124PrimitiveKernel.fixedG122PrimitiveAmbientElement_not_restricted_range"
    - "G124PrimitiveKernel.fixedG122Local_shortExact"
    - "G124PrimitiveKernel.fixedG122LocalSection_sourcePoint"
    - "G124PrimitiveKernel.fixedG122LocalSection_sourceCoefficientPoint"
    - "G124PrimitiveKernel.fixedG122LocalSection_targetSourcePoint"
    - "G124PrimitiveKernel.fixedG122LocalSection_targetCoefficientPoint"
    - "G124PrimitiveKernel.fixedPrimitiveTwistedMulEquiv"
    - "G124PrimitiveKernel.fixedG122FiberEquiv_smul"
  claim_mapping:
    source_labels:
      - "Fixed GOAL C: G-122 three cases, comparison groups, restricted/ambient kernels, section, short exactness, lift fibers"
      - "Design III-3: independent primitive kernel and fixed G-122 three-case connection"
    conjuncts:
      - "Raw and normalized full comparison groups: fixedG122RawComparisonEquiv, fixedG122NormalizedComparisonEquiv, fixedG122Normalization_commutes"
      - "Same main reader: fixedG122MainReading_barAlpha, fixedG122MainReading_identityBarBeta, fixedG122MainReading_generatedBarBeta_ne_barAlpha, fixedG122MainReading_rawSource/rawTarget"
      - "Restricted kernel: PrimitiveKernelPoints, primitiveKernelPoints_iff, fixedG122PrimitiveKernelMulEquiv, both inverse laws"
      - "Ambient endpoint kernel: primitiveEndpointKernelMulEquiv, fixedG122PrimitiveAmbientKernelMulEquiv, inclusion square and counterexample outside restricted image"
      - "Section/split/fibers: fixedG122LocalSectionHom, fixedG122MainReading_sectionSource/sectionTarget, four fixedG122LocalSection component point equations, fixedG122Local_shortExact, fixedG122LocalDisplacement_formula/mul, fixedPrimitiveTwistedMulEquiv, fixedG122FiberEquiv_smul, fixedG122LocalFiber_existsUnique_kernel"
      - "Three fixed cases: direct main-reader point evaluation and existing generated/constant-one/five-factor results listed in the table below"
    undischarged_assumptions: []
    acceptance_point: "Proposal for the entire III-3 design part; independent review and CI are required before acceptance."
audits:
  premise_delta:
    discharged:
      - "Fixed G-122 data are the existing finiteAxisFoldBCDatumSquare, second cell, integer coefficient, and fixed geometry family."
      - "All existing G-122 comparison and section results apply to the actual barAlpha isomorphism; no new invertibility is asserted for generated barBeta."
    remaining: []
  certificate_provenance:
    discharged:
      - "PrimitiveKernelCode retains four local Homs with inverse equations, the comparison square, and all normalized query equations."
      - "PrimitiveEndpointKernelCode is obtained from independently stated local endpoint conditions, not from restricted-kernel membership."
      - "The local ambient element is the image of the accepted fixed G-122 native ambient pair, with source and target bottom/coefficient query equations."
    unresolved: []
  proof_use:
    used:
      - "G-122 restrictionHom, canonicalSectionHom, FullKernel and native ambient witness"
      - "G-120 RestrictionKernelFiberTransport.kernelMulEquiv/fiberEquiv/fiberEquiv_smul and short-exact predicate"
      - "IndependentAATPrimitiveReconstruction fixed generated Homs and main-reader point equations"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "Focused G124PrimitiveKernel check: 194 namespace declarations, standard axioms only."
    - "Targeted G124PrimitiveKernel module build: pass on the revised 194-declaration head."
    - "git diff --check, placeholder, hidden/BiDi Unicode, and local-path/privacy scans: pass."
    - "Twenty-two reported and revised spine declarations #print axioms: propext, Classical.choice, Quot.sound only; namespace macro audits all 194 declarations."
    - "First fixed-head PR review identified main-reader and section-component gaps; the revised head awaits fresh four-lane review and CI."
  blocking_findings: []
  next_obligation: "After III-3 acceptance, design IV-1 common finite-reading criterion and D cases."
```

The case connection uses the same fixed G-122 family, cell, coefficient and geometry in every row. Its main-N comparison is `IndependentAATPrimitiveReconstruction.reading finiteAxisFoldGeometryParameter`. `fixedG122MainReading_barAlpha` identifies its five-factor Hom with the fixed admissible local arrow; `fixedG122MainReading_rawSource/rawTarget` identify every source and target automorphism of the old full comparison with the same local group used by the kernel, section, and fiber results. `finiteAxisFoldTwistedComparison_left/right/read_raw/multiply` is the preexisting path from old twisted coordinates into the main reader's Arrow object.

| Fixed case and premise | Original declaration and common local reading | Classification used |
| --- | --- | --- |
| `initialRawDefectCochain` `barBeta`; no inverse premise | `finiteAxisFoldBarBetaNativeHom`, `finiteAxisFoldBarBeta_read_point`; `finiteAxisFoldBarBetaNativeHom_factor`, source/target factorization and `barE/barD` idempotence; `finiteAxisFoldBarBetaKaroubiHom` and `primitiveKaroubiReading_barBeta_f` give its original comparison square. | `fixedG122MainReading_generatedBarBeta_ne_barAlpha` proves the distinction in the common local Hom by main-N separation; `fixedG122MainReading_generatedBarBeta_not_isIso` reflects a hypothetical local inverse to the fixed G-122 noninvertibility witness. For this native arrow and its image under the main reading, III-2's `G124ComparisonObservationTransport.bottomObservationEquiv` transports the bottom-qualified comparison and observation diagrams; `G124ComparisonObservationTransport.nativeBottomSource_reflection_iff` and `localBottomSource_reflection_iff` give the corresponding source-reflection criterion, whose right side requires both kernel inclusion and image equality with the bottom-fixed subgroup intersected with the source-projection range. These declarations quantify over every arrow and require no inverse; the isomorphism-only G-122 section applies only to the later two cases. |
| Constant-one cochain `barBeta`; same geometry and endpoints | `finiteAxisFoldIdentityCochainBarBetaNativeHom`, `finiteAxisFoldIdentityCochainBarBeta_read_point`; `finiteAxisFoldIdentityCochain_barBeta_eq_barAlpha_common` and `fixedG122MainReading_identityBarBeta`. | The local equality gives the actual `barAlpha` comparison and section. `fixedG122MainReading_sectionSource/sectionTarget` and the four `fixedG122LocalSection_*Point` equations read the section's two bottom and two coefficient components. |
| Actual five-factor `barAlpha`; canonical object admissibility | `finiteAxisFoldBarAlphaNativeIso`, `finiteAxisFoldBarAlpha_read_point`, `fixedG122LocalIso`, `fixedG122NormalizedLocalIso`. | Raw/normalized full groups, bottom-fixed subgroup via III-2 `bottom_comparison_mem_iff`, split short exact sequence, restricted and ambient kernels, the ambient counterexample, and all lift fibers via the Cycle 83 declarations above. |

The local ambient witness fixes source and target bottom/coefficient point evaluations by `fixedG122PrimitiveAmbient_sourcePoint`, `fixedG122PrimitiveAmbient_source_coefficientPoint`, `fixedG122PrimitiveAmbient_target_sourcePoint`, and `fixedG122PrimitiveAmbient_target_coefficientPoint`. Its failure to preserve the comparison square is witnessed by `fixedG122PrimitiveAmbientElement_not_restricted_range`. These statements use one and the same local ambient element.
