# Research 成果索引(research evidence index)

Research 側(`research/lean/ResearchLean/`)で受理された成果の1行台帳。
本体実装・レビューが「Research 側にすでに到達点があるか」を、巨大 Lean
ファイルの実読なしに grep で検索するための索引であり、Research 下限原則
(`docs/aat/guideline.md` の Lean status discipline)の検索基盤である。

## 記載契約

- 1行 = 1受理成果。受理時に追記し、後から書き換えるのは
  `移植状況` 列と `本体対応` 列のみ(受理内容の遡及修正はしない。
  誤記の訂正は可)。
- `research-loop` / `target-theorem-loop` は、成果の受理
  (accepted / target-theorem-proved)時にこの索引への登録を**出力義務**
  として負う(各 SKILL の ledger 手順を参照)。
- 列の意味:
  - `theorem`: Research 側の宣言名(コードブロック表記)
  - `file`: `research/lean/ResearchLean/` 配下のファイル
  - `本文ラベル`: 対応する数学本文の部・定理番号(無ければ `-`)
  - `conjuncts 要旨`: 結論一覧の要約。移植時の下限照合で結論の
    数え漏れが出ない粒度で書く
  - `未放電仮定`: 受理時点の material premise 三分類
    (`docs/aat/lean_quality_standard.md` §1.1)で未放電に分類された
    仮定の一覧。無ければ `なし`。受理済みであることと未放電仮定が
    無いことは別であり、蒸留・下限照合時はこの欄を必ず読む
  - `受理`: GOAL / cycle / PR などの受理点
  - `移植状況`: `ported` / `unported` / `not-for-porting`。
    列値 `unported` は guideline の status `unported (Research-proved)` の
    略記であり同義。`not-for-porting` は scaffolding・探索残骸など
    本体化を意図しないもので、理由を `本体対応` に書く。
    **`unported` → `not-for-porting` への書き換えは下限原則の解除を
    意味するため、ユーザー承認またはレビュー承認済みの根拠を
    `本体対応` に必ず残す**(乱用すると Research 下限原則が空洞化する)
  - `本体対応`: `ported` なら本体側の宣言名、`unported` なら追跡 Issue、
    `not-for-porting` なら理由
- 検索の作法(実装・レビュー側): まずこの索引を `rg` で検索し、
  該当が無ければ `research/lean/ResearchLean/` を直接 `rg` する。索引に無いことは
  「Research に無い」ことを意味しない。

## 索引

| theorem | file | 本文ラベル | conjuncts 要旨 | 未放電仮定 | 受理 | 移植状況 | 本体対応 |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `ChartCircuitLocus.AffineSplitConstantRankData.range_projective` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual chart responseの明示range sectionとallowed-operation moduleのprojectivityからresponse rangeのprojectivityを構成 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.AffineSplitConstantRankData.cokernel_projective` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | finite-free response targetのprojectivityと明示quotient sectionからresponse cokernelのprojectivityを構成 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.chartLabeledResponse_eq_labeledResponse_app` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | selected chart response familyが既存`labeledResponse.app`のactual componentそのものであることを固定 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.chartProtectedKernel_finite` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual allowed-operation chart moduleのfinite/projective性と明示split dataからprotected kernelの有限性を証明 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.chartProtectedKernel_projective` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual allowed-operation chart moduleのprojectivityと明示range sectionからprotected kernelのprojectivityを証明 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.chartKernelBaseChangeEquiv` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual chart protected-response kernelについてcanonical `tensorKer` comparisonが任意の可換scalar extensionで線形同値になることを証明 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.mem_support_chartResponseCokernel_iff_exists_supportMinimalCircuit` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual chart response componentから作るsection-module response-cokernel support所属とtarget-containing support-minimal residue-field tensor circuitの存在を双方向に証明 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `ChartCircuitLocus.chartCircuitLocus_eq_support` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ChartCircuitLocus.lean` | - | actual labeled response componentから定義したsection-module tensor-fiber circuit locusとresponse-cokernel supportの集合等式を証明 | なし | G-aat-quality-surface-08 Cycle 14 | unported | #3557 |
| `CircuitLocus.kernel_finite` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | finite moduleから有限protected response mapのkernelがfiniteであることを、projective imageによるsplitから証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.kernel_projective` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | projective operation moduleとprojective protected-response imageから、そのkernelがprojectiveであることを証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.kernelBaseChangeMap` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | 任意の可換scalar extensionに対するprotected-response kernelの比較写像をmathlibのcanonical `LinearMap.tensorKer`として固定 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.kernelBaseChangeEquiv` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | projective image/cokernelから得るsplittingを用い、canonical kernel base-change mapが任意の可換scalar extensionで線形同値になることを証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.mem_support_responseCokernel_iff` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | response cokernelのprime support所属とresidue-field上のtarget-on-kernel scalar mapが非全射であることの同値を証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.exists_fiber_normalizedRepair_iff_exists_scalarOnKernel` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | residue-field fiberにおけるactual normalized repair vectorの存在とbase-changed protected kernel上のtarget scalar値1 witnessの存在が同値であることを証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.mem_support_responseCokernel_iff_no_fiber_normalizedRepair` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | response cokernelのprime support所属とresidue-field fiberでnormalized repairが存在しないことの同値を証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `CircuitLocus.mem_support_responseCokernel_iff_exists_supportMinimalCircuit` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/CircuitLocus.lean` | - | response cokernelのprime support所属とtargetを含む有限support-minimal response dependenceの存在が同値であることをloop/nonloop両branchで証明 | なし | G-aat-quality-surface-08 Cycle 13 | unported | #3282 |
| `LinearRepair.exists_normalizedRepair_iff_not_mem_protectedResponseSpan` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/LinearRepair.lean` | - | 有限protected response familyに対し、protected responseを零、target responseを1にするactual repair vectorの存在と、target response functionalのprotected span非所属が同値であることを証明 | なし | G-aat-quality-surface-08 Cycle 12 / PR #3324 | unported | #3282 |
| `LinearRepair.no_normalizedRepair_and_singleton_circuit_of_target_eq_zero` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/LinearRepair.lean` | - | target responseが零のloop branchではnormalized repairが存在せず、target singletonが有限support-minimal linear dependenceであることを証明 | なし | G-aat-quality-surface-08 Cycle 12 / PR #3324 | unported | #3282 |
| `LinearRepair.exists_supportMinimalCircuit_of_no_normalizedRepair_of_target_ne_zero` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/LinearRepair.lean` | - | targetがprotected set外でresponseが非零のnonloop branchにおいて、normalized repair failureからtargetと少なくとも1つのprotected labelを含み、`P ∪ {target}`内にある有限support-minimal linear dependenceを構成 | なし | G-aat-quality-surface-08 Cycle 12 / PR #3324 | unported | #3282 |
| `BooleanCircleOperationResponsePrototype.selectedSupportCircleEdge_visible_and_response_ne_zero` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/BooleanCircleOperationResponsePrototype.lean` | - | 既存Boolean-circleの3つの相異なAAT patchをG-08専用3成分ringの3つの非零・相異なidempotent principal chartと対応させ、pairwise intersectionが非空、triple intersectionが空となるcircle nerveと全lawful openのcoverを生成し、選択support AtomのAAT patch上の可視性、`{0,1}` AAT overlapとの対応、同じtyped overlap上の具体的architecture operation導分の非零responseを証明 | なし | G-aat-quality-surface-08 Cycle 11 / PR #3323 | unported | #3282 |
| `LawGeneratedLabeledConormal.requiredGeneratorConormal_span_top` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/LabeledConormalGeneration.lean` | - | required `(lawIndex, atom)`の既存`violationWitness`がobstruction idealを生成することからambient・typed chart/overlapのfull `I/I²` conormal generationを導き、全labeled response零とfull response零の同値を証明 | なし | G-aat-quality-surface-08 Cycle 10 / PR #3322 | unported | #3282 |
| `QuotientValuedDerivation.mapsTo_iff_conormalResponse_quotientDerivation_eq_zero` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ConormalResponseKernel.lean` | - | ambient derivationがlaw idealを保つこととquotient-valued derivationのfull `I/I²` conormal responseが零であることの同値を証明し、typed chart/overlap full Jacobianへinstantiate | なし | G-aat-quality-surface-08 Cycle 9 / PR #3321 | unported | #3282 |
| `ArchitectureOperationPresentation.labeledResponse` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/ConormalJacobian.lean` | - | quotient-valued derivationからfull `I/I²` responseを構成し、required law/Atomの既存`violationWitness` class、G-07 context restriction、typed chart/overlap transport、allowed-operation sheafから`O_Y`へのlabeled response、任意の局所section上でのfull Jacobian評価とのchart/overlap比較、そこから導く左右restriction compatibilityを証明 | なし | G-aat-quality-surface-08 Cycle 8 / PR #3320 | unported | #3282 |
| `ArchitectureOperationPresentation.operation_image_factorization` | `AG/QualitySurface/IntrinsicLawResponseCircuitDescent/OperationImageSheaf.lean` | - | finite `Op` と明示的に同値なindex上の free `O_Y`-module sheafからJ3a係数層へのmorphismを生成し、`lawfulSpace.Modules`内のabelian image、epi/mono factorization、selected generatorのJ2 chart/overlap回収、左右restriction naturalityを構成 | なし | G-aat-quality-surface-08 Cycle 7 / PR #3319 | unported | #3282 |

<!--
既存の受理成果の遡及登録(初期整備)は別 PRD で実施する
(docs/note/codex_skill_audit_redesign_note.md B-3、2026-07-07 ユーザー決定)。
初期整備までは空欄の索引が正であり、空欄は「Research に成果が無い」ことを
意味しない。
-->
