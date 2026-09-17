# G-124 — 局所意味表示からの再構成と有限決定性

一次仕様は
[`research/goals/G-124-aat-local-semantic-reconstruction.md`](../goals/G-124-aat-local-semantic-reconstruction.md)
である。本 report は固定 target A--E の要求、Lean 宣言、前提の出所・使用先、
未完了 obligation を cycle ごとに追跡する。

## Proof state

- fixed activation head: `18540a67e277997376dc5833de4a608c6f526987`
- fixed GOAL blob: `4e6fdacf8b3de5865d5f1f14b058fc0774c1f088`
- common criteria base: `18540a67e277997376dc5833de4a608c6f526987`
- acceptance contract blob: `eb8e1b230e1106cc3d2c826a037578d8dfea7a1f`
- target-theorem-loop blob: `941ee0b9bf6692f3812204ab74383361eff5b048`
- tracking Issue: [#4711](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4711)
- current proof obligation: Cycle 1 constructs the finite-evaluation-diagram `read` / `asm`
  equivalence for dependent point maps with finitely supported primitive preservation laws
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: dependent total-map reconstruction and forward/inverse evaluation for equivalence-valued primitive components

## Requirement ledger

| 条項 | 要求 | 対応する定義・Lean 宣言 | 入力前提 | 構成する証拠 | 使用先 | 未完了部分 |
| --- | --- | --- | --- | --- | --- | --- |
| A--B Cycle 1 delta | 有限個の原始評価と有限個の型付き operation-preservation 等式からなる図式を定義し、整合族から全域 Hom の計算成分と保存則を組み立て、`read` / `asm` の両逆を証明する | `ResearchLean.AG.LocalSemanticReconstruction.FiniteEvaluation` | sort-indexed source/target algebra `X,Y`、finitary signature、primitive operation と具体的 source arguments の有限 support。延長可能性、decoder 像、完成射、全域証人、任意の table predicate・任意の二項比較は入力しない | 一点図式から依存関数を組み立て、各 `h(ω_X(x)) = ω_Y(h(x))` をその有限 constraint 図式から回収し、任意図式で整合性により元の局所表を回復する | 共通局所宣言の Hom 部分、後続の依存写像・可逆成分、タグ・lens・protocol 適用 | AAT 固有 `Σ,D,Λ,M,N`、対象の組立て、共通証人、raw、必須四族、C--E は未接続。Cycle 1 は B 全体でも completion でもない |

## Cycle 1 selection

```yaml
ledger_type: target_cycle_result
goal: G-124-aat-local-semantic-reconstruction
cycle: 1
goal_blob_sha: 4e6fdacf8b3de5865d5f1f14b058fc0774c1f088
base_oid: 18540a67e277997376dc5833de4a608c6f526987
tracking_issue: 4711
report_path: research/reports/G-124-aat-local-semantic-reconstruction.md
selection:
  proof_state_ref: "Issue #4711 active化記録 comment 5715599052; 紙上実装ガイド comment 5716561012"
  proof_dag_predecessors: []
  proof_obligation: "有限評価図式と局所整合族を定義し、finitely supported primitive preservation laws を満たす全域依存関数との read/asm 両逆を構成する"
  selection_reason: "A--B の分離・組立てを一般仮定の包装ではなく実構成へ変える最初の node であり、依存写像・raw・四族への接続の共通入力になる"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEvaluation.lean"
  risks:
    - "局所値へ完成した全域写像または完成 Hom を格納しないこと"
    - "保存条件を全域延長可能性として定義しないこと"
    - "各片の有限構文性と局所値型そのものの有限性を混同しないこと"
    - "共通証人を含む条件、対象の組立て、AAT 適用まで証明したと言い換えないこと"
  unchecked:
    - "Lean 実装、focused check、公理監査、標準 PR review は未実行"
```

## Cycle 1 result proposal

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "finite address/law diagrams, a controlled primitive-operation preservation schema, directed finite union, functorial restriction, coherent local families, singleton assembly, preservation recovery, and both read/asm inverse laws are constructed"
  completion_candidate: no
  lean_artifacts:
    - "research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteEvaluation.lean"
    - "AAT.AG.LocalSemanticReconstruction.FiniteEvaluation.preservingMapEquivCoherentFamily"
  evidence:
    - "Diagram.union with le_union_left/le_union_right"
    - "LocalModel.restrict_refl and LocalModel.restrict_trans"
    - "PrimitiveLaw and PrimitiveLaw.Accepts generate only h(source.interpret op args) = target.interpret op (h applied to args)"
    - "FiniteEvaluation.assemble_read"
    - "FiniteEvaluation.read_assemble"
    - "FiniteEvaluationExample.natIdentityPreserving and natConstantZero_rejected"
  claim_mapping:
    theorem_names:
      - FiniteEvaluation.assemble_read
      - FiniteEvaluation.read_assemble
      - FiniteEvaluation.preservingMapEquivCoherentFamily
    source_labels:
      - "固定 GOAL B: Hom read/asm と両逆"
      - "紙上実装ガイド §2: 有限評価図式による Hom 再構成"
    conjuncts:
      - "分離 asm(read(f))=f -> assemble_read"
      - "組立て read(asm(a))=a -> read_assemble"
      - "有限 support の保存則 -> assemble.preserves"
      - "有限図式の共通拡大 -> Diagram.union"
    material_premises:
      ambient_boundary:
        - "I, X, Y, finitary signature, source/target algebras, law index K, and concrete operation evaluations"
      direction_hypothesis:
        - "PreservingMap.preserves on the read side"
        - "LocalModel.satisfies and CoherentFamily.coherent on the assembly side"
      discharge_required:
        - "singleton values assemble a total point map"
        - "each local equation yields global preservation"
        - "assemble_read and read_assemble"
      conclusion_equivalent_risk:
        - "none after restricting each law to the generated operation-preservation schema"
    undischarged_assumptions: []
    acceptance_point: "一般 Hom 補題そのものには extension/decoder/global-Hom certificate がない。PrimitiveLaw は任意 Prop や任意の二項比較ではなく、source/target algebra の同一 primitive operation に対する具体的な保存式であり、coherence と各有限 law table から計算成分・保存則を構成する。AAT 適用は別 obligation として残す"
    port_status: unported
audits:
  premise_delta:
    discharged:
      - "global preservation of each primitive law / LocalModel.satisfies on Diagram.ofLaw"
      - "all finite-table recovery / CoherentFamily.coherent from singleton diagram"
    remaining:
      - "AAT 固有 Σ,D,Λ,M,N への instantiation"
      - "対象の組立てと本質的全射性"
      - "依存写像、可逆成分、raw、必須四族、C--E"
  certificate_provenance:
    discharged:
      - "assembled map values / singleton local tables"
      - "assembled preservation proofs / selected finite law diagrams"
      - "law provenance / PrimitiveLaw.Accepts is generated by the controlled source/target operation-preservation schema"
    unresolved: []
  proof_use:
    used:
      - "CoherentFamily.coherent / read_assemble and assemble.preserves"
      - "LocalModel.satisfies / assemble.preserves"
      - "Diagram.support_subset / local restriction typing"
    unused: []
  structure_field_escape: "none-found after restricting PrimitiveLaw to concrete primitive-operation preservation instances"
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "research/lean/check_research_modules.sh --focused ResearchLean/AG/LocalSemanticReconstruction/FiniteEvaluation.lean: pass"
    - "#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction: 154 declarations, standard axioms only"
    - "#print axioms key spine: propext, Classical.choice, Quot.sound only"
  blocking_findings: []
  next_obligation: "dependent total-map reconstruction and forward/inverse evaluation for equivalence-valued primitive components"
```

### Cycle 1 initial review remediation

初回の独立4レーン査読では、3レーンが旧
`PrimitiveLaw.accepts : PartialTable ... → Prop` に中心 finding を認定した。この型は
有限 table を引数に取りながら、内部で完成した `GlobalPointMap` や全域延長可能性を量化できたため、
固定 GOAL B の禁止条件を型レベルでは放電していなかった。残る1レーンはこれを局所 model の
membership として許容したが、固定仕様の anti-weakening 条件を優先して Major revisions と統合した。

修正後は `FinitarySignature`、`TargetAlgebra`、帰納的 `LocalTerm` を導入し、
`PrimitiveLaw` を同一 sort の二つの有限局所項へ限定した。`PrimitiveLaw.Accepts` はその二項の
評価値の等式としてのみ生成される。したがって law の構文には任意命題、全域写像、全域延長の
存在量化を置く constructor がない、という第一修正を行った。

この第一修正に対する再査読では、3レーンが `Prop` carrier と二つの零項演算を使えば、
`TargetAlgebra.interpret` に任意命題を置いてその二項を比較できるという中心 finding を認定した。
このため第一修正の完了主張を撤回し、汎用 `LocalTerm` と任意二項比較を削除した。

第二修正の `PrimitiveLaw` は primitive operation と具体的 source arguments、およびその入力・
source result を含む有限 support だけを持つ。`Accepts` が生成する式は常に
`h(ω_X(x)) = ω_Y(h(x))` であり、異なる零項演算の比較や任意命題を law として選ぶ surface はない。
source/target algebra は Hom の ambient boundary であり、各 local certificate はその同一 primitive
operation の保存に限定される。

## 共通証人の必須四族監査

`Invariant.TransportedAlong` の function 分岐は
`∃ e, ∀ A, ...` という全域共通証人を要求するため、Cycle 1 の finitely supported
`PrimitiveLaw` へそのまま入らない。固定 commit の必須四族を source 上で照合した結果は次のとおり。

| 族 | 実際の Hom / invariant | 共通証人問題 |
| --- | --- | --- |
| タグ付き operation | `ExplicitExactGeometryHom` の `base` は `taggedOperationPackage` の `PackageTotalHom`。package は `finiteAxisFoldSupportPackage` の invariant を変更せず継承する | 継承元は `FiniteModel.invariantFamily` の singleton predicate `True`。`TransportedAlong` は pointwise `Iff` 分岐であり、function invariant の `∃ e` はこの固定族には現れない |
| G-122 固定生成比較例 | original-cell Hom は `GeometryTotalHom`。固定 support package は同じ `FiniteModel.invariantFamily` を持つ | 同じく predicate 分岐。固定例の実 morphism では全域共通 `Equiv` witness の非一意選択は現れない |
| lens | `LensAATIndependentGeneratedPackageHom` は `stateMap`, `get_map`, `put_map` だけを持ち、全 semantic Hom と既存同値 | generated core の invariant index は `PEmpty`。独立 lens Hom に `TransportedAlong` field はない |
| protocol | `ProtocolAATIndependentGeneratedPackageHom` は vertexwise `stateMap`, `edge_map`, `observation_map` だけを持ち、全 semantic Hom と既存同値 | generated core の invariant index は `PEmpty`。独立 protocol Hom に `TransportedAlong` field はない |

したがって、共通証人の障害は必須四族の固定 instance を Cycle 1 の一般補題へ接続する段階では
発火しない。一方、最終の共通 `Σ,D` が function-valued invariant を許す一般 branch では依然として
未解決であり、有限片ごとの `∃ e_S` へ弱めてはならない。後続では、まず計算 data として
保持される `Equiv` 成分の forward/inverse 一点評価を構成し、命題内の非一意な existential witness
とは別 obligation として扱う。
