# G-129：可換核と持ち上げ障害の証拠対応

一次仕様は [固定GOAL](../goals/G-129-aat-abelian-lifting-obstruction.md)、
実行・査読・mergeの記録は [tracking Issue #5082](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5082) を参照する。

## 固定参照と第1Cycleの選定

GOALと共通受入基準の適用版は `ed8f19fc6095b61fe0a40d5984af62c5acabd1ba`。
人間が指定した序盤の一括実装を第1Cycleとし、Cycleの粒度と終了条件の記録には
作業開始版 `0ff52f382c5f71c5016d0755f88ec7db34fed14f` のcycle ledgerを用いる。
GOALの数学的要求と受入基準は変更しない。

```yaml
ledger_type: target_cycle_result
goal: G-129-aat-abelian-lifting-obstruction
cycle: 1
goal_blob_sha: 9f93a9a1c2ebd9ccd53362e878363144a934b4b8
base_oid: 0ff52f382c5f71c5016d0755f88ec7db34fed14f
tracking_issue: 5082
report_path: research/reports/G-129-aat-abelian-lifting-obstruction.md
selection:
  proof_state_ref: "Issue #5082 初期proof state"
  proof_dag_predecessors:
    - TransportCoherence.Arbitrary.FiberAut
    - TransportCoherence.Arbitrary.whiskerFiberAutHom
    - CrossStageCoherence.compositeFiberPushforward
    - CrossStageCoherence.InnerFiberAut
    - CrossStageCoherence.FiniteCrossStageWitness
  milestone: "A・Dの実際の核と核輸送を構成し、完了条件4に使う幾何核の可換性と非自明性を証明する"
  proof_obligations:
    - "有限Atom carrier・非空site・実際の被覆・非零raw関係式を持つ幾何入力の核全体の可換性と非自明性"
    - "任意の圏の塔の実際の射影、核、核への包含と核所属の特徴づけ"
    - "強いopcartesian輸送と射影の可換式、核への制限、準同型性、全単射性からの同型"
    - "核の可換性の下で同じcoreの持ち上げに対する輸送の独立性と面の共役・中心化条件"
    - "一般側の核・包含・輸送と第4章の実際の核・射の対応"
  exit_criteria:
    - "採用幾何入力の全計算成分を含む核の可換性・非自明性が追加仮定なしでLeanに受理される"
    - "一般の核輸送が原始射から構成され、射影可換性・核所属・特徴づけ・独立性・面条件が証明される"
    - "第4章との同型が元の自己同型と射影を保ち、同じ輸送を回復する"
    - "対象宣言のfocused check・axiom監査・共通scanと独立PRレビューが合格する"
  selection_reason: "具体的な核の成立と一般側への接続を先に確定し、後続の複体・障害・分類に安定した入力とAPIを渡す"
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/AbelianLiftingObstruction/GeometryKernel.lean
    - ResearchLean/AG/AbelianLiftingObstruction/Tower.lean
    - ResearchLean/AG/AbelianLiftingObstruction/KernelTransport.lean
    - ResearchLean/AG/AbelianLiftingObstruction/CrossStageKernel.lean
  risks:
    - "係数写像だけで全幾何自己同型を同一視しない"
    - "選択された文脈射と任意のrestriction witnessを同一視しない"
    - "核上の全単射性は一般定理の仮定であり、準同型の構成は放電義務"
    - "射影・自己同型・輸送の対応を元の射で示す"
  unchecked:
    - "選定した証明義務は実装・検証前"
```

## 第1Cycleの構成と証拠

このCycleはAの核・輸送、Bのdefectの核所属、Dの核と輸送の対応を扱う。
A–D全体や完了条件4全体の完了判定ではない。成果は `unported (Research-proved)` とする。

### 具体的な幾何入力

`GeometryInput.package` は既存の有限Atom carrierと `FiniteModel.coreReadingFor` を使う。
文脈の対象とrestrictionの存在関係は既存構成と同じであり、
`PointedContexts.contextPreorder_le_iff` が関係の一致を証明する。
その関係の証人として選ぶrestrictionの各成分は、support・axis・observableの点を
`ArchitectureContext.Extension` に記録したprobe上で指定した値を返す。
これにより、全ての文脈間の自然性を満たす自己写像の各成分が恒等であることを証明する。
`GeomReadHom` の射の型や自然性条件は変更しない。

既存の `FiniteCrossStageWitness.package` が選ぶrestriction witnessと任意の指定した射は、
その存在だけでは同一視できない。このため、既存候補の核が非可換であるという主張はせず、
完了条件4が許す具体入力の選択として上のpackageを構成する。
係数環と非零raw関係式には既存候補の `Int × Int` と対角係数の `X²-X` を再利用する。
siteの非空性、実際の被覆、係数の非自明性、raw関係式の非零性を別々に証明する。

`GeometryKernel.inner_ext` は係数写像の一致から元の全幾何自己同型の一致を導く。
`PairCoefficients.comp_comm` と合わせて、選んだ部分群ではなく実際の
`InnerFiberAut GeometryInput.package` 全体の可換性を証明する。
係数交換 `innerSwap` は元の全幾何射として構成され、非恒等である。
同じ元が核全体と可換であり、どの核元の平方でもないことも証明する。

### 固定targetとの対応

以下のpathは `research/lean/ResearchLean/AG/AbelianLiftingObstruction/` からの相対、
一般宣言のnamespaceは `AAT.AG.AbelianLiftingObstruction` である。

| 条項・選定義務 | 宣言・構成 | 保持する対象と結論 |
| --- | --- | --- |
| A1の実際の射影と核 | `Tower.lean`: `fiberPushforward`, `Kernel`, `kernelInclusion`, `fiberPushforward_eq_one_iff`, `kernelEquivFiberAut` | 任意の圏の塔で、関手の元の自己同型への作用とそのkernelを使用。核所属は実際の `p.map` が恒等であることと同値 |
| A条件2の輸送写像の生成 | `StrongTransport.lean`: `fiberTransportHom`, `fiberTransportHom_fac`, `fiberTransport_unique` | 強いopcartesian射から生成し、因子分解の一意性と準同型性を証明 |
| 射影と輸送の整合、核所属 | `KernelTransport.lean`: `fiberPushforward_transport`, `kernelTransportHom`, `kernelTransportHom_fac`, `kernelTransportHom_unique` | 上下の強いopcartesian性から射影可換性を導き、生成済み輸送を実際の核へ制限 |
| A条件2の同型・加法化 | `kernelTransportEquiv`, `KernelTransportLaws.lean`: `KernelCoefficient`, `kernelTransportAddEquiv` | 同じ生成済み写像の全単射性をGOALの仮定として保持。`Additive` 型タグは核元と包含を保つ |
| 同じcoreを持ち上げる選択からの独立性 | `KernelTransportLaws.lean`: `kernelTransport_independent_lift` | 同じ元の辺への二つの補正の射影が等しいとき、差は核に属し、核の可換性で輸送が一致 |
| A2とB1の核所属 | `KernelComparison.lean`: `canonical_comparison_pushforward`, `faceKernelDefect`, `faceKernelDefect_inclusion` | 同じ元の射のcore整列から `p(m)=p(u)` を導き、消滅を仮定せず `u*m⁻¹` を実際の核へ戻す |
| Aの面の共役式と条件3の同値 | `kernelTransport_face_conjugacy`, `centralizes_iff_kernelTransport_eq` | 元の指定比較による共役式。逆方向には生成済み核輸送の全射性を使用 |
| Dの元の核・包含・射影 | `CrossStageKernel.lean`: `compositeFiberEquiv`, `compositeFiberEquiv_pushforward`, `innerKernelEquiv`, `innerKernelEquiv_hom`, `innerKernelEquiv_inv` | 既存の全自己同型とその逆射をそのまま保持し、`compositeFiberPushforward` と `InnerFiberAut` を回復 |
| Dの元の道の輸送 | `innerKernelEquiv_transport` | 任意の `TwoLayerLiftData`、辺の再選択、道について、同じ原始射の因子分解から既存の `upperWhiskerCompositeFiberAut` と一致 |
| 完了条件4のpackageと核 | `PointedContexts.lean`, `GeometryInput.lean`, `PairCoefficients.lean`, `GeometryKernel.lean` | 有限Atom carrier、非空site、被覆、非零raw関係式と、核全体の可換性・非自明性 |
| 同じ具体入力での条件1–3 | `GeometryKernelTransport.lean`: `actualKernelCommGroup`, `authoredKernelElement_ne_one`, `identityTransport_bijective`, `authored_centralizes` | `innerKernelEquiv` で一般側の実際の核へ渡す。恒等辺の強いopcartesian性、同じ一般写像の全単射性、非恒等比較と核全体の可換性を証明 |

### 前提の出所と使用

| 前提・証拠 | 分類・生成元 | 実際の使用先 |
| --- | --- | --- |
| 任意の圏・関手と上段・下段の強いopcartesian性 | Aの原始入力 | comparatorの構成と一意性、輸送準同型、射影可換性 |
| 同じcoreの二つの持ち上げ、A2の射影整列 | Aの原始入力・方向仮定 | `liftDifference` の核所属、`canonical_comparison_pushforward`、`faceKernelDefect` |
| 核全体の可換性 | 一般側ではA条件1、具体側では `GeometryKernel.inner_mul_comm` から放電 | `kernelTransport_eq_of_kernel_comparison` とauthored intertwiningの核元の交換 |
| 生成済み核輸送の全単射性 | 一般側ではA条件2、具体側では `kernelTransport_identity` から放電 | `kernelTransportEquiv` の逆写像、中心化同値の逆方向では全射性 |
| 面比較と核全体の可換性 | A条件3との同値を証明、具体側では核元の包含と可換性から放電 | 面の二つの輸送の一致 |
| 文脈restrictionの証人 | 元のrestriction関係から生成。probeでは明示構成 | 自然性からsupport・axis・observable成分が恒等になる証明 |
| 幾何射のraw関係保存・可換square | `GeometryInput` の対角係数と係数交換から構成 | 全幾何同型 `innerSwap` の実在と非自明性 |
| 3-cellのsyzygy | 後続Cycleの原始入力・具体例の証明義務 | 今回は複体・コサイクルを主張しないため未使用 |

既存依存として、G-109の第4章構成(受理PR #4029)、F18の任意関手上の輸送
(受理PR #4901)、既存の幾何packageと有限Atom構成を使う。
このCycleでは依存APIの型と呼出箇所を確認し、元の射を保つ接続を新たに証明する。
既存の受理済み定理そのものを再包装して新しい中心成果とはしない。

## 第1Cycleの結果と監査提案

正式な受理判定は固定headに対するPR監査コメントに置く。

```yaml
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta:
    - "具体packageの全幾何核の可換性と非自明性を構成から証明"
    - "任意の塔の実際の射影・核・包含・核所属同値を構成"
    - "強いopcartesian射から準同型を生成し、射影可換性と核所属を証明"
    - "同じcoreの持ち上げによる輸送の独立性、面共役式、中心化との両方向を証明"
    - "第4章の元の全自己同型、射影、包含、任意の道の輸送への対応を証明"
  exit_criteria_status:
    - "全幾何核: GeometryKernel.inner_mul_comm と GeometryInput.innerSwap_ne_one"
    - "一般の核輸送: KernelTransport・KernelComparison・KernelTransportLaws"
    - "第4章の射の保存: CrossStageKernelのhom/inv・pushforward・transport定理"
    - "機械検証は下記。独立PRレビューによる最終判定は固定headの監査コメント"
  split_reason: none
  completion_candidate: no
  lean_artifacts:
    - AbelianLiftingObstruction/Tower.lean
    - AbelianLiftingObstruction/PointedContexts.lean
    - AbelianLiftingObstruction/GeometryInput.lean
    - AbelianLiftingObstruction/PairCoefficients.lean
    - AbelianLiftingObstruction/GeometryKernel.lean
    - AbelianLiftingObstruction/StrongTransport.lean
    - AbelianLiftingObstruction/KernelTransport.lean
    - AbelianLiftingObstruction/KernelComparison.lean
    - AbelianLiftingObstruction/CrossStageKernel.lean
    - AbelianLiftingObstruction/KernelTransportLaws.lean
    - AbelianLiftingObstruction/GeometryKernelTransport.lean
  evidence:
    - "上の固定target対応表と各Lean証明本体"
    - "各file末尾のstandard axiom guardと全136宣言のprint axioms"
  claim_mapping:
    theorem_names:
      - GeometryKernel.inner_mul_comm
      - GeometryInput.innerSwap_ne_one
      - fiberPushforward_transport
      - kernelTransport_independent_lift
      - centralizes_iff_kernelTransport_eq
      - innerKernelEquiv_transport
    source_labels: [A1, A2, "A条件1–3", B1, "Dの核・輸送", "完了条件4の入力と核"]
    conjuncts: ["上の固定target対応表に記載"]
    undischarged_assumptions: ["このCycleの選定義務にはなし。一般定理が保持するAの明示仮定は前提表を参照"]
    acceptance_point: "選定した5義務を同じ実際の核・射で接続した。正式受理は独立PR監査"
    port_status: unported

audits:
  premise_delta:
    discharged: ["核輸送の生成・準同型・核所属", "具体幾何核全体の可換性と非自明性", "具体恒等辺の強いopcartesian性と核輸送の全単射性", "具体非恒等比較と核全体の可換性"]
    remaining: ["一般側のA条件1–4は固定targetの仮定として保持", "3-cell付き具体有限表示への統合とsyzygyの評価は後続義務"]
  certificate_provenance:
    discharged: ["canonicalFiberComparatorの生成と一意性", "元の射影のkernel", "probe restrictionの明示構成", "係数交換の全幾何同型", "Arrow-preserving innerKernelEquiv"]
    unresolved: []
  proof_use:
    used: ["上下の強いopcartesian性で輸送と射影の一意性", "core整列でdefectの核所属", "核可換性で基準独立性と面共役", "輸送全射性で中心化同値の逆方向", "全幾何成分の自然性で核の可換性", "元のpathの因子分解で第4章輸送との一致"]
    unused: ["3-cell syzygyはこのCycleのclaimの前提にしていない"]
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "11個の非aggregate fileの個別Lean check"
    - "追加136宣言すべてのprint axioms: 標準公理のみ"
    - "Research import方向・package方向、placeholder、hidden/bidi、privacy、diff check"
  blocking_findings: []
  next_obligation: "同じ核輸送から道の関係への降下・A3の複体を構成し、B–CとDのdefect/解への対応、指定された3例を証明"
```

### 再現可能な検証

対象を一つずつ指定する。Research全体、aggregate、全file loopのbuildは行わない。

```sh
research/lean/check_research_modules.sh --focused ResearchLean/AG/AbelianLiftingObstruction/GeometryKernelTransport.lean
.github/lean_quality/check_research_import_direction.sh
.github/lean_quality/check_research_package_direction.sh
git diff --check
```

他の10fileも実装時に個別指定で検証する。依存のcompiled cacheはtoolchain・manifest・
ソースの一致を確認したものを用い、不足した二つの依存fileだけを個別に検証する。
各fileの `#assert_standard_axioms_only` に加え、全136宣言の `#print axioms` を
単一のscratchから確認する。実行結果とログのhashはPRの検証記録に置く。

## 後続の証明義務

Aの道の関係への降下、同じ有限表示の `C⁰`–`C³` と微分、二つの複体の等式は未実装。
Bのdefect変換則・コサイクル条件・障害類・実際の解との両方向、Cの二つのtorsorと
頂点での再同定、Dの既存defect・解・G-127群拡大への全対応も後続義務である。
完了条件2・3の指定例、および完了条件4の3-cell付き表示・core整列・syzygy・障害評価は、
今回の幾何入力と核のAPIを用いて証明する。G-129全体の状態はactiveのままとする。
