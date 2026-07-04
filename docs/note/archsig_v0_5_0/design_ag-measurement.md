> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計次元2: 代数幾何 AAT 分析の充実と SAGA 定理の現場接続

- 作成日: 2026-07-04(査読反映改訂: 同日)
- 担当: 設計次元2(計測面)
- 位置づけ: 調査と設計のみ。PRD ではない。AAT 数学本文(`docs/aat/algebraic_geometric_theory/`)が正であり、本設計はそれに相対化される。
- 主な典拠: 第X部(SAGA、part_10)、第III部(law algebra)、第IV部(obstruction cohomology)、第VIII部(measurement theory)、`Formal/AG/SemanticRepair/SagaComparison.lean` / `Boundary.lean`、責務憲章、調査レポート4本(saga / ag-theory / archsig-code / measurement-notes)

---

## 1. 目的

v0.5.0 の計測面を、AG 版 AAT の到達点(SAGA 定理連鎖、Lean 全段 proved)に合わせて再設計する。核は次の一文に尽きる:

> 「局所修理はそれぞれ成功している。それは単一の大域修理へ貼り合うか?」(第X部の問い)を、選ばれた有限入力の内部で、CI が読める肯定的結論として判定できるようにする。

具体的には:

1. **SAGA packet**: 定理7.5 の10結論(law-dependent 1〜3 / law-independent 4〜10)を artifact 上で表現し、law-equation witness を入力 contract から受ける。
2. **cover-relative Čech H^1 計測と descent / global gluing 診断**の CLI・出力を設計する。
3. 第III部(obstruction ideal / lawful locus)、第IV部(H^1・nerve 幾何)、第VIII部(measurement theory)から**追加計測ファミリ**を、理論根拠・入力要件・claim 境界付きで列挙する。
4. **境界定理 8.4 / 8.5 / 6.4**(comparison / refinement / incidence はデータ)を tool 側 guardrail として強制する。
5. 現場エンジニアが読める**肯定的結論への翻訳規律**を定める。

主張の範囲はすべて certified bounded inference の内側に置く。theorem candidate に依存する読みは candidate と型区別する(第VIII部の certified / candidate 分離、appendix B.1)。

設計は全段(層 B〜E)を固定するが、**v0.5.0 の確約範囲は Stage 単位に切る(§5.1)**。Stage 3 以降(grounded 10結論 / harmonic debt / refactor transport / compare)は次版への先行設計である。

---

## 2. 現状の問題

v0.4.0 の AG 経路(archmap/v2 + measurement-profile/v1 → measurement-packet/v1、evaluator 11種)は骨格として健全だが、v0.5.0 の目標に対して次のギャップがある。

### 2.1 SAGA(第X部)の計測が存在しない

- 現行 evaluator は第III〜VIII部を anchor とし、第X部(semantic repair descent、additive H^1、SAGA 比較、10結論 packet、境界定理)に対応する計測が一つもない。理論側は 2026-07-03 に SAGA 全連鎖が Lean proved(`target-theorem-proved`)であり、「evaluator + profile 検証 + assumption 定理参照」の3点セットで受け皿は既にある(archsig-code レポート §12.3)のに、繋がっていない。
- 「repair が貼り合うか」という現場で最も需要のある問い(PR review、AI 生成パッチの検収)に対する出力語彙がない。

### 2.2 residual・repair・faithfulness を受け取る入力 contract がない

- SAGA の supplied 層(charts / overlaps / repair primitives C^0 / residual r / supp / semantic projection π / faithfulness data / comparison data)は、ArchMap(観測)にも LawPolicy(制度選択)にも属さない第三の入力である。「repair の提案」は観測でも政策でもなく、修理提案者の contract。現行 schema にこの置き場がない。
- 特に alias(同一 component へ射影される相異なる semantic atom、Λ/K 二層)は SAGA の十分性方向の核心(例2.6 / 3.6)だが、これを observation contract 上でどう保持するかが未定義。

### 2.3 計測間比較(CI 差分)が理論的に無防備

- 境界定理 8.5(refinement naturality is data)と 8.4(full sheaf comparison is data)は「comparison data なしの transport は存在しない」を反例付きで確定しているが、現行 tool には計測間比較の surface 自体がなく(pr-review は v1 専用)、将来 CI 連携で「前回と比べて改善/悪化」を安易に語る設計事故が起きやすい。guardrail の設計が必要。

### 2.4 第VIII部の計測メニューの未消化分(実コード突き合わせ済み)

- 定理4.2(計算可能 invariant 一覧)・定理8.5-8.7(Hodge / harmonic debt 下限)・定理7.3(refactor invariance)は有限計算可能で Lean 側にも同型定理があるのに、evaluator 化されていないか proxy 止まり(sheaf-laplacian は proxy と自己申告)。
- 定理5.2(Alexander dual = minimal repair hitting sets)は**このギャップに含まれない**。v0.4.0 の `ag.square-free-repair@1` が既に `minimalForbiddenSupports`・`deltaComplex.faces`(Stanley-Reisner)・`alexanderDualRepair.minimalHittingSets`(minimality は有限 support 列挙で検査)・NSdepth certificate を computed invariant として出力し、insight card と ArchView 投影まで配線済み(ag_measurement.rs)。残る gap は summary conclusion token がないことのみ(§3.6 A2)。
- 定理8.1 / 8.2(law 充足は H^0 で作用し、H^1 は cover の幾何から来る)の分離が出力語彙に反映されておらず、「H^1 が零だから law 的に健全」という誤読を防ぐ装置がない。

### 2.5 出力の concrete class 規律が徹底されていない

- 第IV部 原則4.4(「群が非零になりうる」ではなく「この cocycle のこの class が非零」)に対し、現行 cech evaluator の cocycle 出力は parity marker 止まり(archview レポート)。修理対象を名指すには class の concrete support が要る。

---

## 3. 設計案

### 3.0 全体像: 診断の階段とデータフロー

SAGA の supplied / generated 規律(part_10:42-54)をそのまま artifact contract 境界にする。入力の充実度に応じて結論が強くなる**階段**を、そのまま evaluator の段にする。

```
入力層          artifact                        evaluator                出せる結論
─────────────────────────────────────────────────────────────────────────────
(A) 観測        archmap/v2                      (既存 ag.cech 等)        residual 生値(mismatch cocycle)
(B) 有限複体    + repair-plan/v1                ag.saga-descent@1        r∈B^1 生値
                                                                        r∉B^1 ⇒ 貼り合わない(無条件・否定的)
    + faithfulness(complete-support 宣言       同上                     r∈B^1 ⇒ REPAIR_GLUES(肯定的、定理3.4/3.5)
      または supplied data)
(C) additive    + cover triple 列挙・係数・      同上(class モード)      [r]∈Z^1/B^1 の class 零/非零、
    H^1 層        true sheaf certificate                                定理4.8 package
(D) 比較層      + incidence bridge              ag.saga-comparison@1     semantic H^1 ≅ cover-relative Čech H^1、
                + h1 comparison data                                     zero-predicate equivalence、非零 class 転送
(E) law 方程式  + measurement-profile の        ag.saga-grounded@1       10結論 packet(law-dep 1-3 / law-indep 4-10)、
    層            lawEquation ブロック                                   detector soundness、law-check 生値検査
```

データフロー(一次 workflow は引き続き `analyze` 一本):

```
archmap/v2 ──────────────┐
law-policy/v1(profiles) ─┼─→ archsig analyze ─→ measurement-packet(saga 区画込み)
repair-plan/v1(新規) ────┘         │               ├─ summary(conclusion-first)
(+ --residual-packet)              │               ├─ insight brief
                                   │               └─ viewer data(次元: ArchView へ)
measurement-packet ×2 + refinement-comparison/v1 ─→ archsig compare ─→ comparison-report
```

residual r の由来は二通りを許す:

- **measured(一次ルート)**: `ag.cech-obstruction` が archmap の生 section 値から計算した mismatch cocycle を、packet 内 invariant への参照で pin する。residual は生値であり判定ではない(part_10:98)ことと、観測純化(比較は ArchSig が独占)の両方に整合。**実行機構(単一 profile 制約・packet 参照解決・chart↔context 束縛)は §3.5 の3条件で固定する。**
- **supplied**: toy / 外部観測用。provenance を記録し、summary で由来を明示。

### 3.1 新入力 artifact: `archsig-repair-plan/v1`

repair 提案者(PR author の agent、または repair-plan authoring SKILL)が書く artifact。「観測(ArchMap)/ 制度(LawPolicy)/ 修理提案(RepairPlan)/ 計算(ArchSig)」の四者に責務が分かれる。列挙の完全性(charts / overlaps の completeness はデータの一部、定義3.1)は repair-plan author が一括して負う。

```json
{
  "schema": "archsig-repair-plan/v1",
  "id": "repair-plan:pr-4212-extract-tax@1",
  "targetProfileRef": "profile:saga-descent-default@1",

  "residual": {
    "kind": "measured",
    "packetRef": "archsig-measurement-packet:run-2026-07-04T10",
    "invariantRef": "invariant:cech-h1-cocycle:cover:main"
  },

  "complex": {
    "charts": ["chart:billing", "chart:payment", "chart:ledger"],
    "overlaps": [
      { "id": "ov:billing-payment", "left": "chart:billing", "right": "chart:payment" },
      { "id": "ov:payment-ledger",  "left": "chart:payment", "right": "chart:ledger" },
      { "id": "ov:ledger-billing",  "left": "chart:ledger",  "right": "chart:billing" }
    ],
    "tripleOverlaps": [
      { "id": "tri:b-p-l",
        "boundary": { "d01": "ov:billing-payment", "d12": "ov:payment-ledger", "d02": "ov:ledger-billing" } }
    ],
    "enumerationComplete": true
  },

  "primitives": [
    {
      "id": "prim:extract-tax-service",
      "restrictions": [
        { "overlap": "ov:billing-payment",
          "left":  ["atom:semantic:tax-rounding-billing"],
          "right": ["atom:semantic:tax-rounding-payment"] }
      ],
      "support": { "kind": "complete" }
    },
    {
      "id": "prim:pin-ledger-schema",
      "restrictions": [
        { "overlap": "ov:payment-ledger",
          "left":  ["atom:contract:ledger-entry-v2"],
          "right": ["atom:contract:ledger-entry-v2"] }
      ],
      "support": { "kind": "complete" }
    }
  ],

  "semanticProjection": {
    "lambda": "archmap-atoms",
    "kappa": "archmap-subjects",
    "pi": "subject-of-atom",
    "holonomySupport": { "kind": "generated-from-residual" }
  },

  "faithfulness": { "mode": "complete-support" },

  "coefficient": {
    "kind": "f2-additive"
  },

  "trueSheafCertificate": null,
  "gluingData": null,

  "comparison": null,

  "grounding": null
}
```

フィールドの意味と規律:

| フィールド | 意味(理論対応) | 責務者 | 検証 |
| --- | --- | --- | --- |
| `residual` | 選ばれた residual r(定義3.1)。measured なら packet 参照で pin | ArchSig 計測(measured)/ author(supplied) | 参照解決 + cocycle 条件 δ¹(r)=0(triple あるとき)。measured の参照解決は `--residual-packet` 経由(§3.5) |
| `complex.charts / overlaps / tripleOverlaps` | 有限 repair cover(定義3.1 / 4.1) | author | 参照整合。**完全性は検証せず assumption ledger 行にする** |
| `enumerationComplete` | 列挙の完全性宣言(定義3.1「列挙の完全性はデータの一部」) | author(一括払い) | 検証しない。`assumed_by: repair-plan author` |
| `primitives[].restrictions` | res_L / res_R(overlap ごとの左右制限) | author | restriction-difference rule(δ^0 の supplied 条件、part_10:199)を ArchSig が検査 |
| `primitives[].support` | supp: C^0 → P(Λ)。`complete` は supp(g)=Λ 宣言(定理3.5 regime)。`enumerated`(部分 support)は `faithfulness.mode: supplied / none` の run で使う | author | enumerated なら atom 参照解決 |
| `semanticProjection` | (Λ, K, π)(定義2.1)。標準は archmap の semantic 粒度 atom を Λ、subject(component)を K、subject 写像を π と読む | ArchMap 観測に載る | π の全域性。alias は許容(むしろ本質) |
| `faithfulness.mode` | `complete-support` \| `supplied` \| `none` | author | supplied 時は定義4.6 の3点(zero primitive / residual support predicate Q / faithfulness law)を受け、Q(r) を検査 |
| `coefficient` | Čech 型係数データ(定義4.2)。`f2-additive` は F_2 群を tool 側標準として生成 | tool 標準 or supplied | additive regime + δ¹∘δ⁰=0 + δ¹(0)=0 を検査 |
| `trueSheafCertificate` | 定義4.7(cover membership + global sheaf condition) | author(層 C を使うとき) | cover membership は site から検査可能、global sheaf condition は assumption 行 |
| `gluingData` | 定理7.3 用 gluing data | author | 適合検査 |
| `comparison` | 層 D(§3.3.2 参照) | author | 定義7.1 の可換・両側逆・zero 保存を検査 |
| `grounding` | 層 E への参照(profile の lawEquation ブロックを指す) | LawPolicy 側 | §3.2 |

**validator 規則(cross-field、hard error)**:

1. **complete-support 整合**: `faithfulness.mode: "complete-support"` のとき、全 primitive の `support.kind` が `"complete"` でなければ contract violation(hard error)。定理3.5 / Lean `CompleteSupportBoundaryComplex`(`support_eq : ∀ primitive, supportOf primitive = completeSupport`)は**すべての** primitive に complete support を要求する族であり、この検査なしでは `faithfulnessBasis: complete-support-theorem` が定理の族の外で発火しうる。
2. **measured residual の chart 束縛**: `residual.kind: "measured"` のとき、`complex.charts` は archmap の context 参照でなければならない(chart-indexed 必須)。measured residual は archmap cover の context 辺上に載る値であり、自由な chart id では層 B の δ⁰g = r が well-defined にならない。この束縛は層 D の incidence bridge を待たず**層 B から**課す。
3. 上記のほか、フィールド表に列挙した参照解決・restriction-difference rule・係数公理の各検査。

**anti-weakening 規律(schema レベル)**: `repair-plan/v1` は結論相当フィールド(`h1Zero`, `globalCoherent`, `descent`, `verdict`, `isomorphism`, `glues` など)を**持たない**。`deny_unknown_fields` に加え、archmap/v2 の diagnostic-shortcut 検査(R3)と同型の `check_repair_plan_no_conclusion_tokens` を入れ、結論語 token を含む入力を hard error にする。「定理の結論に現れる構造を supplied certificate として受け取らない」(part_10:52)と GOALS.md の anti-weakening rule(class membership / structure field に結論を隠さない)の実装形。

### 3.2 measurement profile 拡張: lawEquation ブロック(層 E の受け口)

law-equation witness は「law を不透明 predicate でなく方程式として書かせると係数と cohomology が政策から生成される」(第III部 定義11.3 / 定理11.4、原則11.6)の実装形。LawPolicy は selector という性格(憲章 C5)を守り、方程式の実体は measurement profile 側に置く。

```json
{
  "schema": "measurement-profile/v2",
  "profileId": "profile:saga-grounded-default@1",
  "siteRef": "archmap:contexts",
  "coverRef": "cover:main",
  "coefficient": "generated:quotient-of-witness-ideal",
  "effCoeff": "finite-presentation",
  "resolutionSelector": "taylor",
  "domain": "semantic-repair-residual",
  "zeroPredicate": "residual-class-zero-in-quotient",
  "nonZeroPredicate": "residual-class-nonzero-with-support",
  "certSelector": "concrete-cocycle-with-support",
  "verdictDiscipline": "part8/3.1-five-valued",

  "lawEquation": {
    "requiredLaws": [
      {
        "law": "law:no-cycle@1",
        "witnessVariables": [
          { "variable": "w_cycle", "chartScope": ["chart:billing", "chart:payment", "chart:ledger"] }
        ],
        "defectObservable": {
          "archmapAxis": "axis:dependency",
          "sectionValueKey": "cycleWitnessValue"
        },
        "holdsCriterion": {
          "kind": "defect-raw-value-zero",
          "zeroSense": "empty-witness-set"
        },
        "restrictionCompatibility": "arrow-level-declared"
      }
    ],
    "quotientSheafCondition": { "kind": "assumed" }
  }
}
```

規律:

- `coefficient: "generated:quotient-of-witness-ideal"` — 係数 Q = O/I_Ob は supplied certificate ではなく、witness ideal の語彙から**生成される**(第III部 定理11.4)。profile は生成の材料(witness 変数、defect observable の生値の在り処)だけを指す。
- **係数生成の計算可能クラス限定**: witness ideal からの商の構成と ideal 所属判定は、既存 AG evaluator と同じ **square-free / F_2 Boolean クラスに限定**し、既存の MAX_* 実装定数と同型の有限上限を課す。一般の多項式 ideal membership(Gröbner 基底級の機構)は導入しない。クラス外の入力は contract violation として入力検証で語る(profile 検証の一部)。
- `defectObservable` は ArchMap の**生 section 値**への参照であり、判定語ではない(観測純化 R2 と同じ流儀)。
- **`holdsCriterion` は必須入力 contract**: 「law が成り立つか」の評価意味論(chart-local holds-defect tie、定義11.3)を law ごとに宣言させ、ArchSig は defect observable の**生値**に対してこの criterion を検査する。premise `displayedRequiredLawsHold` の判定は**この生値検査からのみ**生成する。interpretation 零([d_i]=0 は d_i∈I_Ob を意味するだけ)や H^0 検査 pass からは生成しない — 系11.5 が確定した通り、消滅と同値なのは law の成立ではなく defect の ideal 所属であり、定理8.1 の向きも「laws hold ⇒ 0-cochain 零」で逆ではない。assumption ledger に「`displayedRequiredLawsHold` は holdsCriterion による tool check の operationalization であり、理論の holds とはこの宣言された tie を介して相対化された関係」を1行記録する。
- chart-local law-defect tie と arrow-level restriction 互換(定義11.3 の適合条件)は ArchSig が入力から**検査**し、検査で落とせないもの(global sheaf condition 等)は assumption ledger に `assumed` として残す。GOALS.md material premise ledger の線引き(「law-equation realization のフィールドは chart-local holds-defect tie と arrow-level restriction 互換に限る」)に一致。
- `quotientSheafCondition` は一般には仮定(part_10:576-577)。**単一 context 有限モデルの場合は ArchSig が判定して `discharged-by-finite-model`(例9.1 の定理)に格上げする** — 仮定が定理に変わる数少ない箇所で、実装しやすい最初の入口。

profile v1→v2 の版上げは設計次元「LawPolicy 再設計」との調整事項(§6)。本設計が要求する最小差分は `lawEquation` ブロックと `coefficient: generated:*` 語彙の追加のみ。

### 3.3 SAGA evaluator ファミリ(3種)

既存の「evaluator + profile 検証 + assumption 定理参照」3点セット様式に載せる。

**verdict 行の立て方の判別基準(一般則)**: **profile / repair-plan が選んでいない語彙(層)の行は立てない(選ばれた語彙の外)。選ばれた語彙の内で、入力不足により計測できない行は `unmeasured` 行 + boundary statement として立てる(語彙の内の沈黙)。** §4 の D 群規律「行を消さず内側を保護する」は語彙の内の行に適用される。以下の各行にこの基準の適用理由を付す。

#### 3.3.1 `ag.saga-descent@1` — 有限 descent と additive H^1(層 B / C)

- **理論根拠**: 定理3.4(必要性は無条件 / 十分性は faithfulness 下)、定理3.5(complete support regime では faithfulness が定理)、補題4.5([r]=[0] ⟺ r∈B^1)、定理4.8(true sheaf H^1 package)。
- **入力**: archmap/v2 + repair-plan/v1(層 B 必須、triple + 係数 + certificate があれば層 C)。
- **計算**: δ^0 の restriction-difference rule 検査 → supplied primitive 加群上で δ^0 g = r の可解性(F_2 なら線形代数)→ 境界所属 → triple があれば Z^1/B^1 の class 判定 → coverage / faithfulness の有限集合演算 → alias witness の列挙。
- **verdict 行**(structural verdict、5値):

| domain | zero predicate | 出るとき | 判別基準の適用理由 |
| --- | --- | --- | --- |
| `saga.residual-boundary-membership` | 選ばれた residual が supplied primitive 加群の B^1 に属す | 常時(層 B で計算可能) | 層 B は repair-plan 供給時点で常に語彙の内 |
| `saga.residual-class` | [r] = [0] in Z^1/B^1 | 層 C(triple + additive 係数)があるとき。ないときは行自体を立てない | 層 C は triple + 係数の供給によって初めて語彙に入る。未供給 run では語彙の外 → 行なし(商が存在しない段に class 行を立てない) |
| `saga.global-coherence` | GlobalCoherent(𝔎) | faithfulness 基盤(complete-support 宣言 or supplied data)があるとき。ないときは `unmeasured` + boundary statement `silence_by_design` | 大域整合は saga-descent を選んだ時点で語彙の内。faithfulness 不足は語彙内の計測不能 → unmeasured 行(行は消さない) |

- **computed invariants**:

```json
{
  "invariant": "saga-descent",
  "boundaryMembership": {
    "inB1": false,
    "witnessPrimitiveCombination": null,
    "residualSupport": ["ov:billing-payment", "ov:ledger-billing"]
  },
  "closureDiagnostics": {
    "residualComponentCovered": true,
    "residualComponentFaithful": false,
    "aliasWitnesses": [
      { "component": "subject:tax-engine",
        "residualAtoms": ["atom:semantic:tax-rounding-billing", "atom:semantic:tax-rounding-payment"],
        "supportedAtoms": ["atom:semantic:tax-rounding-billing"] }
    ]
  },
  "faithfulnessBasis": "none | complete-support-theorem | supplied-data"
}
```

  層 B(境界所属のみ、商が構成されない段)のフィールド名は `residualSupport` とし、**`class` を含む語は使わない**(part_10 定義3.2 の語彙規律: 障害の消滅は境界所属であり、商としての class と H^1 の語は §4 の構成にのみ使う)。層 C が供給され Z^1/B^1 が構成される run でのみ、class 語彙のフィールド(`residualClassSupport` 等)と token を emit する。

`aliasWitnesses` は例2.6 / 3.6 型の生値提示(「component 水準では覆われているが、この semantic atom 自身には戻れない」)。判定語ではなく π の fiber の有限計算であり、**ArchMap 抽出精度(Λ/K 二層を潰さない)への具体的フィードバック**として設計次元「ArchMap SKILL」に渡る。

- **assumption ledger 行**(代表):

| theoremRef | assumption | status |
| --- | --- | --- |
| part10/3.1 | charts / overlaps の列挙完全性 | `assumed`(assumed_by: repair-plan author) |
| part10/3.1 | δ^0 restriction-difference rule | `discharged_by_check` |
| part10/3.5 | complete support 宣言(mode 時。全 primitive complete は validator 検査済み) | `assumed`(宣言、author 責務) |
| part10/4.2 | δ¹∘δ⁰ = 0、δ¹(r) = 0 | `discharged_by_check` |
| part10/4.7 | global sheaf condition(certificate 供給時) | `assumed` |

#### 3.3.2 `ag.saga-comparison@1` — SAGA 比較と class 転送(層 D)

- **理論根拠**: 定理7.2(4結論: cocycle 対応 / coboundary 対応 / H^1 比較同値 / zero-predicate equivalence)、定理7.4(非零 class 転送)、定理6.4(incidence is data)。
- **入力**: 層 C までの全部 + `comparison` ブロック:

```json
"comparison": {
  "incidenceBridge": {
    "kind": "chart-indexed",
    "explicit": null
  },
  "h1ComparisonData": {
    "kind": "identity",
    "explicit": null
  }
}
```

  - `incidenceBridge.kind: "chart-indexed"`: repair cover が Čech cover と同じ chart 添字で組まれている場合、定理6.4 の構成的側(`chartIndexedZeroCover_constructs_zeroSimplexChartIncidence`)により tool が incidence を**生成**できる。それ以外は `explicit` に chart→0単体 / pairwise→1単体 / triple→2単体の対応表を**必ず供給**(no-go: 一様構成は存在しない)。
  - `h1ComparisonData.kind: "identity"`: 両辺が**同一の有限複体表示**(context 集合・overlap・triple 構造の一致)を持つ場合(例9.2 の identity comparison と同じ)。この正当化条件は §3.7(3) の fingerprint 要件と同一の内容であり、参照名の一致では代用できない。それ以外は `explicit` に次数 0/1/2 の両方向写像表を供給し、ArchSig が定義7.1 の適合条件(degree1 で両側逆・差を保つ / degree2 で zero 保存 / 微分と可換)を**検査**する。
  - **comparison data は結論を格納しない**(定義7.1、part_10:690)。explicit 表に商水準の対応・zero class・整合を書くフィールドは存在させない。
- **出力**: cochain 水準の写像は supplied、**商水準の同型と zero-predicate equivalence は generated(定理)**という区別を invariant に刻む:

```json
{
  "invariant": "saga-comparison",
  "suppliedData": { "incidence": "chart-indexed-generated", "comparison": "identity" },
  "generatedConclusions": {
    "quotientIsomorphism": "established",
    "zeroPredicateEquivalence": "established",
    "nonzeroClassTransfer": {
      "fired": true,
      "semanticSideClassSupport": ["ov:billing-payment", "ov:ledger-billing"],
      "cechSideClassSupport": ["simplex:1:billing-payment", "simplex:1:ledger-billing"]
    }
  }
}
```

- verdict 行: `saga.cover-relative-h1-residual`(Čech 側 residual class の零/非零)。semantic 側の非零を「AAT site 上の代数幾何的 class の非零」として読み替えられるのは、この evaluator が established を出したときだけ。

#### 3.3.3 `ag.saga-grounded@1` — law-equation grounded 10結論 packet(層 E)

(v0.5.0 確約範囲外、次版先行設計 — §5.1)

- **理論根拠**: 定理7.5(10結論、Lean `SemanticRepairGeneratedEndToEndSAGAPacket` の分割が正)、定理8.1(degree-zero law contribution)、定理8.2(law-independence)、第III部 定理11.4 / 系11.5。
- **入力**: 層 D までの全部 + profile の `lawEquation` ブロック(holdsCriterion 込み)+ repair-plan の `grounding` 参照。
- **計算**: law equation grounded surface(定義5.1 の5点組)の適合検査 → 係数 Q = O/I_Ob の生成(square-free / F_2 Boolean クラス限定、§3.2)→ 各 chart で defect observable の**生値**に holdsCriterion を適用して displayed required laws の成立を判定(law-check 生値検査)→ 生値を商に落とし interpretation [d_i] を計算 → 10結論 packet の組立。premise 判定(生値検査)と interpretation 計算(商での class)は**別の計算**であり、後者から前者を導かない(系11.5)。

### 3.4 SAGA packet: 10結論の artifact 表現

measurement-packet の `computedInvariants` に次の invariant を追加する(packet の6区画構造は変えない)。フィールド名は Lean 構造体(SagaComparison.lean:172-226)を鏡写しにするが、これは設計上の便宜であり **Rust と Lean の対応を contract として要求しない**(境界規律)。

```json
{
  "invariant": "saga-generated-end-to-end-packet",
  "schema": "archsig-saga-conclusions/v1",
  "groundedSurfaceRef": "repair-plan:pr-4212#grounding",
  "theoremRef": "part10/7.5",

  "lawDependent": {
    "premise": {
      "name": "displayedRequiredLawsHold",
      "status": "holds | fails",
      "checkKind": "holds-criterion-raw-value",
      "perChart": [
        { "chart": "chart:billing", "law": "law:no-cycle@1", "holds": true,
          "holdsCriterionRef": "profile:saga-grounded-default@1#lawEquation/law:no-cycle@1/holdsCriterion",
          "defectValueRef": "archmap:...#sections/billing/cycleWitnessValue" }
      ]
    },
    "conclusions": {
      "generatedInterpretationZero":                  { "status": "established", "theoremRef": "part10/7.5.1" },
      "generatedRestrictionEvaluator":                { "status": "established", "theoremRef": "part3/11.4" },
      "nonzeroInterpretationDetectsDisplayedLawFailure": { "status": "established", "theoremRef": "part10/7.5.3" }
    },
    "detectorFindings": [
      { "chart": "chart:payment", "law": "law:no-cycle@1",
        "interpretationClass": "nonzero",
        "reading": "非零 interpretation はこの chart の displayed required law の失敗を保証する(系11.5 detector soundness。定理は Lean proved、前提計算〔interpretation 非零〕は本 run の測定)" }
    ]
  },

  "lawIndependent": {
    "note": "以下は law の充足を仮定せずに従う(定理8.2)。law 充足の証拠として読まない。",
    "conclusions": {
      "groundedGlobalGluingPackage":              { "status": "established", "theoremRef": "part10/7.3" },
      "sheafConditionForSelectedCover":           { "status": "established" },
      "descent":                                  { "status": "established", "note": "sheaf 条件 + cover membership から導出(定理6.6)。独立 certificate は受け取らない" },
      "uniqueGlobalSection":                      { "status": "established" },
      "globalCoherentIffCoverRelativeH1Zero":     { "status": "established", "instanceReading": { "coverRelativeH1Zero": true } },
      "boundedAdditiveH1ZeroIffCoverRelativeH1Zero": { "status": "established" },
      "higherObstructionsVanish":                 { "status": "established", "note": "additive regime で自明に成立。外部仮定として供給されない(定理4.8 結論5)" }
    }
  },

  "degreeZeroLawContribution": {
    "theoremRef": "part10/8.1",
    "generatedC0PointwiseZero": true,
    "reading": "law 意味論が Čech 複体に到達する地点は正確に次数0。H^1 の内容は cover の幾何から来る(意味8.3)"
  }
}
```

表現上の要点:

1. **theorem-level と instance-level の分離**。`status: established` は「前提が検査/仮定台帳で確定した下で、この同値・構成が定理として成立している」ことを示す(結論そのものは Lean proved の定理で、tool は前提の充足を検査する)。一方 `instanceReading` は「この instance でどちら側が成り立っているか」の計測値。両者を同じフィールドに潰さない。
2. **law-dependent / law-independent の分割を一次構造にする**。これは定理7.5 の statement-level dependency boundary(AC14)であり、Cycle 350 の査読 veto(H^1 零 conjunct は law と無関係に構成的に真)への応答として理論側が確定させた分割。artifact がこの分割を持たないと、8.2 の誤読(構成的 H^1 零を law の証拠として売る)を summary 層で防げない。
3. **premise の判定源は holdsCriterion 生値検査のみ**(§3.2)。`perChart` の証拠は defect 生値参照 + criterion 参照の組であり、interpretation や H^0 から premise を導かない。premise が fail した場合、law-dependent 結論は `not_established` になり、代わりに `detectorFindings`(結論3の detector soundness)が発火する。「非零 interpretation はこの chart の displayed required law の失敗を保証する」— 沈黙ではなく、**系11.5 に帰属する肯定的な certified detection**(証明は定理側〔Lean proved〕、tool の主張は前提計算と検出)。
4. **grounded surface(7.5 経路)の residual は構成的に δ^0(primitive)** なので、この invariant 内の H^1 零は法の証拠ではない(`lawIndependent.note` に焼き込み)。**measured residual に対する貼り合わせ診断は §3.3.1 の `ag.saga-descent@1` が担い、両者を artifact 上でも分離する**。ここが本設計で最も事故りやすい線であり、schema コメントではなく構造(別 invariant、別 evaluator)で分ける。

### 3.5 CLI 設計

```bash
# 1. 通常計測(residual class の測定を含む。従来通り)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap .tmp/archmap.json \
  --law-policy .tmp/law_policy.json \
  --out-dir .tmp/archsig-analyze

# 2. repair plan の単体検証(archmap / law-policy 単体検証と同型の入口)
cargo run --manifest-path tools/archsig/Cargo.toml -- repair-plan \
  --input .tmp/repair_plan.json \
  --archmap .tmp/archmap.json \
  --residual-packet .tmp/run-a/archsig-measurement-packet.json \
  --out .tmp/repair-plan-validation.json

# 3. SAGA 診断込み analyze(repair-plan を渡すと policy 中の ag.saga-* が起動可能になる)
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap .tmp/archmap.json \
  --law-policy .tmp/law_policy.json \
  --repair-plan .tmp/repair_plan.json \
  --residual-packet .tmp/run-a/archsig-measurement-packet.json \
  --out-dir .tmp/archsig-analyze

# 4. 計測間比較(§3.7 の guardrail 参照。refinement/comparison data が原則必須)
cargo run --manifest-path tools/archsig/Cargo.toml -- compare \
  --before .tmp/run-a/archsig-measurement-packet.json \
  --after  .tmp/run-b/archsig-measurement-packet.json \
  --refinement .tmp/refinement_comparison.json \
  --out-dir .tmp/archsig-compare
```

**measured residual の実行機構(実行可能性の3条件)**:

現行コードの機構(law-policy/v1 は文書水準の `measurementProfileRef` 1本で run あたり単一 profile を選択し、各 AG evaluator は profile 固有フィールドを hard error で要求する — cech は `coefficient: F2` / `zeroPredicate: rank-zero@1`、saga 系 profile とは相互排他)の下では、「単一 analyze run で cech が residual を計測し同一 packet に saga 区画を積む」階段は実行できない。よって:

- **(a) 単一 profile 制約の解消は blocking 依存**: policy 行ごとの `profileRef` 化(LawPolicy 再設計次元)を、measured residual を単一 run で完結させるための **blocking 依存**として宣言する(§6-1)。これが入るまで単一 run 構成は設計上の目標形であって実装形ではない。
- **(b) 二 run 構成を v0.5.0 の正式経路とする**: `analyze` / `repair-plan` に `--residual-packet <path>` を追加し、`residual.packetRef` の参照解決(packet id 一致・invariant 存在)と cocycle 条件検査(δ¹(r)=0、triple あるとき)をそこで行う。(a) 解消後に同一 run pin を許す場合の profile 適合規則(residual を計測した profile と saga profile の site / cover の正規化表示一致)もその時に定義する。
- **(c) chart↔context 束縛は層 B から**: `residual.kind: "measured"` のとき `complex.charts` は archmap context 参照必須(§3.1 validator 規則2)。

設計判断:

- **一次 workflow は `analyze` 一本のまま**。SAGA は `--repair-plan` の追加で有効化される。policy の `policies[]` に `{"evaluator": "ag.saga-descent@1", ...}` があるのに repair-plan が渡されないときは、evaluator 行を `not_computed`(reason: `repair_plan_not_supplied`)にし boundary statement を置く(エラーにしない — 沈黙の手続き化)。
- `compare` は pr-review の AG 後継の計測部分(v0.5.0 確約範囲外、§5.1)。verdict 差分の表示は artifact 次元の設計と共有するが、**class の同一視は refinement data がある場合のみ**(§3.7)。
- **exit code / strict モードの方針(本設計で固定)**: 既存 `--strict-distance` は nonTerminal(unmeasured / unknown / not_computed)が1行でもあれば exit 1 にするが、この規律をそのまま SAGA 行へ適用すると、本設計が正常系とする層 B 入力の run(faithfulness 不在 → global-coherence が unmeasured)や repair-plan 不供給の run(not_computed)が strict CI で常に fail し、「沈黙の手続き化」と矛盾する。よって **strict の nonTerminal 拒否は「宣言済み入力が揃っている evaluator の行」に限定し、boundary statement `silence_by_design`(reason: `*_not_supplied` / 語彙内の入力不足)を伴う nonTerminal 行は strict 集計から除外する(carve-out)**。carve-out された行は pass に丸めるのではなく、strict 判定の分母から外して boundary statement 付きで報告する(unmeasured / unknown を pass/fail に丸めない規律と両立)。summary の nonTerminalCount 集計の分離実装と CI status への写像詳細は artifact/CI 次元と共有するが、この carve-out 自体は本設計で確定する。

### 3.6 追加計測ファミリ候補(第III / IV / VIII部)

各候補に理論根拠・入力要件・出力 claim の境界を固定する。**S1〜S2 + A1〜A2 を v0.5.0 中核(確約)、S3・A3・A4 を次版への先行設計、B 群を second wave、C 群を candidate 隔離**と段階付ける(§5.1)。

| # | evaluator | 理論根拠 | 入力要件 | 出力(肯定的結論の形) | claim 境界 |
| --- | --- | --- | --- | --- | --- |
| S1 | `ag.saga-descent@1` | X 定理3.4 / 3.5 / 4.8(CBI、Lean proved) | archmap/v2 + repair-plan/v1(層B/C) | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` / `MEASURED_NONGLUING_RESIDUAL`(層B、concrete support 付き)/ `MEASURED_NONGLUING_RESIDUAL_CLASS`(層C 供給時のみ) | 選ばれた複体の内部のみ。faithfulness 基盤なしでは大域整合を語らず境界所属の生値まで。class 語彙は層C でのみ。repair synthesis / 最小修復は非主張 |
| S2 | `ag.saga-comparison@1` | X 定理7.2 / 7.4、定理6.4(Lean proved) | + incidence bridge + comparison data(chart-indexed / identity は自動生成可) | `SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA` + 非零 class 転送 | 選ばれた comparison の下のみ。full sheaf cohomology へは言及しない(8.4) |
| S3 | `ag.saga-grounded@1`(次版) | X 定理7.5 / 8.1 / 8.2、III 定理11.4(Lean proved) | + profile lawEquation(witness 変数 + defect observable 生値参照 + holdsCriterion) | 10結論 packet、`MEASURED_LAW_DEFECT_AT_CHART`(detector)、`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`(law-check 生値検査) | law 充足は displayed required laws + 宣言された holdsCriterion に相対。H^1 零を law 証拠にしない(8.2 焼き込み)。係数生成は square-free / F_2 Boolean 限定(§3.2) |
| A1 | `ag.cech-obstruction@2`(版上げ) | IV 定義3.1-3.3、原則4.4、§12(系12.3 / 定理12.4、Lean proved) | 既存入力のまま(定理12.4 の3前提は既存入力から有限検査) | concrete cocycle 代表 + class support、`nerveShape { b1, capacityLowerBound, isForest, eulerCharacteristic }`、`COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION`(発火条件: isForest ∧ tripleOverlaps 空 ∧ 全 restriction map 全射性検査 pass — 定理12.4 の3前提を各 `discharged_by_check` に) | b1 等は選ばれた cover の nerve の性質であって codebase の性質ではない、を invariant 側に明記。排除結論は選ばれた abelian 係数 sheaf に相対化(H^1(U,F)=0)。non-abelian torsor / stacky descent / gerbe obstruction は非排除(boundary note 1行) |
| A2 | `ag.square-free-repair@1`(既存、版上げなし) | III 定理5.6C / 系5.6D、VIII 定理5.2(Alexander dual、Lean proved: {q},{p,r} example) | 既存入力のまま(evaluator は v0.4.0 実装済み) | **summary token `REPAIR_TARGETS_IDENTIFIED` の追加のみ**。既存 invariant(`minimalForbiddenSupports` / `deltaComplex.faces` / `alexanderDualRepair.minimalHittingSets`)を正とし token から参照する | hitting set は組合せ的 repair target。operation 意味論・大域最小性は非主張(原則5.3)。**@2 版上げ・フィールドリネームは行わない**(既存 fixture・CLI テスト・ArchView 投影の互換を壊す利益がない) |
| A3 | `ag.harmonic-debt@1`(次版) | VIII 定理8.5-8.7(Hodge / harmonic debt、explicit data 下 Lean proved) | cover complex + profile で宣言された内積/重み + **cost model(Lipschitz 定数 L の宣言 + harmonic-resolution 要求)を supplied data として必須(下界を出す場合)** | `harmonicDebtNorm`(analytic)+ certified 文「local adjustment では \\|h(g)\\| 未満に下げられない」(定理8.6 のみで支持)。cost model 供給時のみ `essentialRepairLowerBound`(系8.7、assumption ledger に L / Lipschitz / harmonic-resolution 要求を記録) | 内積は profile の選択。norm の小ささは lawfulness ではない(定義3.3)。**cost model 不供給の run では下界行を立てない(silence_by_design)** — 系8.7 の前提を入力 contract に載せずに結論だけ出さない。既存 sheaf-laplacian@1 の proxy ラベルは維持し、こちらを faithful 版として別 evaluator にする |
| A4 | `ag.refactor-transport@1`(次版) | VIII 定理7.3(refactor invariance、package proved) | 2つの packet + `refactor-morphism/v1`(site 射 + law / coefficient / witness 互換データ) | `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR`(同値時の zero verdict 保存) | morphism artifact なしに版間 transport なし(原則7.4 と 8.5 の実装形)。`compare` コマンドの土台 |
| B1 | `ag.nullstellensatz-certificate@1` | III 定理候補7.2A + 初等方向(1∈I ⇒ k点不在は無条件) | Boolean 座標宣言 + 生成元 + supplied unit certificate(1 = Σ a_i f_i)。**certificate は非観測 contract(repair-plan 系 artifact または profile 側参照)で受け、ArchMap には置かない**(観測純化 PRD の certificate 先書き禁止を維持) | `UNLAWFULNESS_CERTIFICATE_VERIFIED` + NSdepth(analytic) | **certificate の検証**(有限代数、無条件に健全)と **NSdepth の最小性主張**(theorem candidate)を分離。後者は candidate reading。純化 PRD の「certificate は ArchSig が発行する」原則との関係: 外部 supplied certificate は検証対象の入力であり、ArchSig が無条件検証してから結論を出すため、判定の先書き(計算結果の観測 contract への混入)には当たらない |
| B2 | `ag.hilbert-interference@1` | V 定理12.2(Hilbert 恒等式、Lean G5 proved) | 同一 ambient 上の monomial ideal 対(common ambient 必須) | 干渉級数 Int_{U,V}(t) の有限窓係数(次数別 conflict 会計、analytic) | audit reading であり政策優先度を決めない(原則12.3)。common ambient なしに比較なし(原則9.3) |
| B3 | boundary residue 拡張(`ag.boundary-residue@2`) | IV §8-9 定理9.2 + §13(period pairing、proved) | 既存 + feature extension cover(core / feature / boundary) | holonomy 値と pairing `<δ(b),γ>=<b,∂γ>` の Stokes 会計 | NoHigherBoundaryObstruction 等は仮定台帳。extension holonomy accounting(定義13.4)は convention であり定理でない、を invariant に注記 |
| C1 | stability / barcode / Wasserstein / hotspot | VIII 定理候補6.3 / 6.5 / 10.7 / 8.10(**statement-only candidate**) | — | 出すなら `regime: "candidate"` の analytic reading のみ | v0.5.0 では**見送り推奨**。structural verdict に接続しない。安定性定理のない計測値は noise/signal 分離の保証を持たない(原則6.4)ことを逆手に取り、candidate 隔離を schema で強制 |
| C2 | temporal(第IX部) | IX 定理4.2 / 5.3 | trace 系入力 | — | ArchSig 責務境界外(FieldSig / SFT 側)。artifact に拡張点だけ残す |

補足(A2 の詳細)— minimal repair hitting sets は現場価値が最も分かりやすい出力だが、invariant は v0.4.0 で実装・配線済みであり、追加するのは summary conclusion token だけである。token は既存フィールドを参照する:

```json
{
  "token": "REPAIR_TARGETS_IDENTIFIED",
  "invariantRef": "ag.square-free-repair@1#alexanderDualRepair.minimalHittingSets",
  "reading": "選ばれた forbidden パターン全てに交わる最小 witness 集合。q を解消すれば選択された全 obstruction パターンに当たる(組合せ的 repair target、操作意味論は別)"
}
```

既存フィールド名(`minimalForbiddenSupports` / `deltaComplex.faces` / `alexanderDualRepair.minimalHittingSets`)が正であり、リネームは既存 fixture・CLI テスト・ArchView 投影(`invariant["alexanderDualRepair"]["minimalHittingSets"]` 読取)を壊すだけなので行わない。

### 3.7 guardrail: 境界定理 8.4 / 8.5 / 6.4 の強制

「比較可能性はデータである。これが SAGA 比較定理の外周である」(part_10:857)を、schema・validator・CLI 挙動の三層で強制する。

**(1) schema レベル**

- `h1-comparison-data/v1` / `refinement-comparison/v1` / `incidence-bridge`(repair-plan 内)は**写像水準のフィールドしか持たない**。商水準の対応・zero 保存の結論・class 同一視を書くフィールドを定義しない(定義7.1「comparison data は結論を格納しない」の schema 化)。
- `deny_unknown_fields` + 結論語 token 検査(§3.1)。

**(2) validator レベル(契約検査 — 沈黙ではなく診断可能な contract violation)**

- comparison data: degree1 両側逆・差の保存、degree2 zero 保存、微分との可換を有限検査。落ちたら `COMPARISON_DATA_CONTRACT_VIOLATION` で fail(U-adequacy 検査と同じ扱い: 定理が使えない入力は入力検証で語る)。
- incidence: `explicit` 供給時は全単体の参照解決を検査。`chart-indexed` は構成条件(repair cover の添字集合が Čech cover の chart 集合と一致)を検査し、満たさなければ explicit を要求(定理6.4 no-go: 一様構成は存在しない)。
- refinement: 粗→細方向の residual / zero 保存写像であることを検査。**細→粗の申告は schema が受け取らない**(命題4.10 は片方向。逆方向は定理8.5 の反例で遮断)。

**(3) CLI 挙動レベル**

- `ag.saga-comparison@1` は comparison ブロックなしでは走らない: verdict 行を立てず boundary statement `{ "kind": "silence_by_design", "reason": "comparison_data_not_supplied", "text": "cover-relative 側への class 転送は供給された comparison data の下でのみ語る(part10/8.4-8.5)" }` を1行置く。エラーでも残タスクでもない。
- `compare` コマンド:
  - 両 packet の profile fingerprint(site / cover / coefficient / law universe / doctrine のハッシュ)が**一致**する場合のみ、identity comparison を自動採用して verdict 行の同一視比較を行う(例9.2 の identity comparison と同じ、追加データ不要の唯一のケース)。
  - **fingerprint の健全性要件(未決事項8 の解決空間の制約)**: identity comparison の自動採用条件は、profile の**参照名**(coverRef 等)の一致ではなく、**正規化後の有限複体表示(context 集合・overlap・triple 構造)の同一性を fingerprint が witness すること**を要件とする。これは §3.3.2 の identity 正当化条件(両辺が同一の有限複体表示を持つ)と同一の内容である。参照名のみのハッシュを許すと、before/after で archmap 側の cover 内容が変わっていても identity が自動採用され、定理8.5(comparison data なしの transport は存在しない)違反 = tool による入力 contract の推測補完が起きるため、この選択肢は設計段階で排除する。
  - fingerprint が異なる場合、`--refinement` 供給がなければ **class の同一視・「同じ障害の追跡」・改善/悪化の語りを一切せず**、両 packet の verdict を別 profile として並記した報告のみ出す。summary は `TWO_PROFILES_REPORTED_SEPARATELY` で、非結論の羅列はしない。
  - `--refinement` 供給時は検査済み refinement data の下で粗→細の zero 引き継ぎ(命題4.10)だけを語る。
- **full sheaf 語彙の出力 lint**: packet / summary / insight 生成コードは `H^n(X, ·)` 型の絶対 cohomology 表記を emit しない。出力語彙は常に `coverRelativeH1`・「選ばれた cover に相対的な」で統一(第IV部 定義3.3 の規律 + 定理8.4)。CI に語彙 lint テストを置く(既存 R3 の出力版)。
- **boundary-membership 段の class 語 lint**: 層 B(商が構成されない run)の invariant / token / summary 文に `class` 語彙を emit しない(part_10 定義3.2 の語彙規律)。上記 lint テストと同じ CI に置く。

### 3.8 肯定的結論への翻訳規律(エンジニア向け surface)

summary v3 の conclusion token(conclusion-first、readThisFirst 構造は踏襲):

| token | 発火条件 | エンジニア向け一行(Recommended) |
| --- | --- | --- |
| `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` | r∈B^1 ∧ faithfulness 基盤あり(定理3.4(ii)/3.5) | 「宣言された修理計画は、選ばれた chart 構成の中で単一の大域修理に貼り合う」 |
| `MEASURED_NONGLUING_RESIDUAL`(層B) | r∉B^1(定理3.4(i) 対偶、無条件) | 「各修理は局所では成功しているが、この 2 overlap にまたがる残差が貼り合わせを妨げている(場所を名指し。境界所属の生値)」 |
| `MEASURED_NONGLUING_RESIDUAL_CLASS`(層C 供給時のみ) | [r]≠[0] in Z^1/B^1(補題4.5) | 「この 2 overlap を support とする残差 class が貼り合わせを妨げている(商 Z^1/B^1 上の class として名指し)」 |
| `MEASURED_LAW_DEFECT_AT_CHART` | interpretation 非零(前提計算は本 run の測定) | 「chart X で law L の defect が測定された。非零 interpretation はこの law の失敗を保証する(系11.5 detector soundness、Lean proved)」 |
| `DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS` | lawEquation の holdsCriterion による生値検査が全選択 chart で pass(law-check contract、定義11.3 chart-local holds-defect tie) | 「選ばれた law はすべての選択 chart 上で成立している(宣言された criterion による chart 水準の生値検査)」 |
| `COVER_SHAPE_EXCLUDES_GLUING_OBSTRUCTION` | isForest ∧ tripleOverlaps 空 ∧ 全 restriction map 全射性検査 pass(定理12.4 の3前提、各 discharged_by_check) | 「選ばれた abelian 係数と cover の中で、cover の形と検査済み restriction から H^1 障害は排除される」 |
| `REPAIR_TARGETS_IDENTIFIED` | hitting sets 非空(定理5.2、既存 invariant 参照) | 「これらの witness を解消すれば、選択された禁止パターンすべてに当たる」 |
| `SAGA_COMPARISON_ESTABLISHED_UNDER_SUPPLIED_DATA` | 定理7.2 前提の検査 pass | 「意味論側の障害 class は AAT site 上の幾何的 class と一致して読める」 |
| `VERDICT_PRESERVED_UNDER_DECLARED_REFACTOR` | 定理7.3 前提の検査 pass | 「宣言されたリファクタの下で、前回の zero verdict は保存される」 |

翻訳規律(7項):

1. **主文は常に「選ばれた profile の内側での肯定形」**。`SAFE_WITHIN_POLICY` 型を先頭に、根拠(theoremRef + 具体 invariant)を直後に置く。
2. **H^1 語彙を law 充足の言葉に翻訳しない**(定理8.1 / 8.2 の分離)。**「law が守られている」は law-check 行(holdsCriterion による生値検査)からのみ生成し、interpretation 零・H^0 零からは生成しない**(系11.5: 消滅と同値なのは law の成立ではなく defect の ideal 所属。定理8.1 の向きは「laws hold ⇒ 0-cochain 零」であり逆ではない)。逆に「貼り合わせ障害」は law 違反ではなく cover の幾何の話として書く(意味8.3)。summary 生成コードにこの写像規則をテーブルとして持たせ、テストで固定する。
3. **非零は concrete class(層 C)/ concrete support(層 B)で名指す**(原則4.4 + 定義3.2 の語彙規律)。「H^1 が非零」ではなく「billing–payment と ledger–billing の 2 overlap を support とするこの class」。最小の非自明例は円 nerve(例9.2)であり、「点の欠陥(H^0)」と「輪の障害(H^1)」は別の現象として書き分ける。
4. **数値は readings に隔離**。distance / norm / spectrum / 干渉級数は analytic readings 区画に置き、verdict 文へ混ぜない。「debt norm が小さい ≠ lawful」(原則8.4)。
5. **沈黙は結論の近くに一言**。faithfulness 不在時の boundary statement は「本 run の結論は境界所属の生値まで。大域整合の判定には repair support の宣言(complete-support または faithfulness data)を repair-plan に追加する」のように、**次に何を供給すれば語れるようになるか**を1行で示す(残タスク一覧化はしない)。
6. **Avoid 対句を skills に載せる**(archsig-reader 後継)。例: Avoid「アーキテクチャは健全です」→ Recommended「選ばれた policy と cover の中で、測定された障害 class は零です」。Avoid「H^1 がゼロなので law 違反はありません」→ Recommended「law 検査(chart 水準)はすべて成立。貼り合わせ障害も測定されていません(別の検査)」。
7. **「証明する」は theoremRef 付きの定理帰属文でのみ使う**。含意の証明は Lean proved の定理側にあり、tool が計算するのは instance の前提(生値・interpretation)である。tool の一人称主張は certified detection(肯定的 diagnostic conclusion)に留め、証明強度を自称する文言(「本 run が…を証明した」)は emit しない(ArchSig は Rust tooling であり Lean 証明器ではない)。summary 生成テストで固定する。

### 3.9 fixture と Lean proved 面の接続(数値ロック)

Rust と Lean の対応は要求しない。ただし理論の worked example は数値が確定しているので、**fixture レベルの数値一致テスト**を CI に置く。proved の帰属は witness の形ごとに明示する:

| fixture | 期待値 | 典拠 |
| --- | --- | --- |
| circle nerve — Lean witness(3辺 circle instance、`Fin 3`、係数 Z/(2)) | residual class 非零、identity comparison 下で両側非零(転送発火) | `Formal/AG/Examples/SemanticRepairPart10.lean` の `circleSimplex` / `circleNext`(**Lean proved はこの3辺形**。lean_theorem_index も three-edge circle-nerve witness site と明記) |
| circle nerve — 本文 worked example(2頂点・逆向き2辺、係数 F_2) | 同現象(residual class 非零)の別 witness としての期待値 | 例9.2 / appendix B.9 の**理論本文仕様**(この形は Lean proved ではない。数値ロックの一次 fixture は上の3辺形とし、2頂点形は本文対応の補助 fixture) |
| lawful firing instance(単一 context) | displayed laws hold ⇒ interpretation 零 ∧ defect class 零、quotient sheaf condition が discharged-by-finite-model | 例9.1 / 定理8.1(Lean proved) |
| 擬円周 cover | cover-relative H^1 ≅ Z 相当の非零 class、period pairing = r_sync − r_async | IV 例9.3-9.4 / appendix B.3-B.7 |
| I_Ob = ⟨pq, qr⟩ | minimal hitting sets {q}, {p,r} | appendix B.5 / VIII 定理5.2(Lean proved) |
| Tor 共有 witness | Tor_1(R/⟨xy⟩, R/⟨xz⟩) ≠ 0 | V 命題9.2(Lean proved) |
| appendix B.8 toy(Atom family → 3 chart → mismatch (1,0,0)) | 検出汎関数 g_P + g_Q − g_R = 1 で H^1 非零 | appendix B.8(ArchMap→ArchSig 一気通貫 fixture の理論仕様) |

例9.1 と例9.2 は**別 witness**であり fixture でも混同しない(proof record boundary notes)。同様に、例9.2 の本文2頂点形と Lean の3辺 instance も**別 witness**であり、「(Lean proved)」の帰属を取り違えない。

### 3.10 可視化への引き渡し(ArchView 次元への interface)

計測=主、可視化=従。本設計が新たに供給する計測データと、それが解放する幾何表現の対応だけを渡す(描画設計は ArchView 次元):

| 新計測データ | 解放する幾何 | 計測なしに描くと捏造になるもの |
| --- | --- | --- |
| residual class の concrete support(A1) | nerve 上で class support の辺だけが光る「輪」 | 支持辺の特定なしの雰囲気 bloom |
| `saga.residual-boundary-membership` + witness primitive | 「repair ladder が residual を境界として消す」運動(descent snap) | 境界所属未計測での修理成功アニメ |
| aliasWitnesses(Λ/K 二層) | 同一 component ノードの中に複数 semantic atom を持つ入れ子表現、faithful でない atom の可視化 | component 粒度のみの表示(alias の消去) |
| degreeZeroLawContribution vs H^1 class | 「点の欠陥(chart 上のマーカー)」と「輪の障害(閉路)」の二重表現 | 両者を同色・同形で混ぜる表示 |
| nerveShape(b1 / forest / χ) | cover の形そのものの表示(容量、保存則) | b1 未計測での「余地」表示 |
| comparison established | semantic 側と Čech 側の 2 面を橋でつなぐ対応表示 | comparison data なしの 2 run 重ね描き(8.5 違反の可視化版) |

---

## 4. 境界規律との整合

philosophy レポートのチェックリスト(C 群 / D 群)に対する自己点検:

- **C1(観測境界の一括払い)**: 列挙完全性・complete-support 宣言・faithfulness data は repair-plan author が一括で負い、assumption ledger に `assumed_by` として一箇所に記録される。ArchSig 内部に補完・推測・fallback を置かない。residual の一次ルートを measured(生値からの計算)にしたのは、比較=判定を ArchSig が独占する憲章原則1の帰結。
- **C2(ArchMap は "X is the case" のみ)**: 本設計は ArchMap schema に判定語を一切追加しない。SAGA に必要な観測は「semantic 粒度の atom + subject(component)+ 生 section 値」であり、すべて既存 v2 語彙の範囲。alias の保持は観測の忠実さの問題であり、判定の混入ではない。B1 の supplied unit certificate も ArchMap には置かず非観測 contract で受ける(§3.6)。
- **C5(LawPolicy は selector)**: law-equation の実体は measurement profile に置き、LawPolicy 本体は profile の選択と law universe 指定のまま。witness predicate の手書き・score formula は導入しない。`lawEquation` ブロックが profile 側に立つのは「measurement profile 本体は LawPolicy の責務でなく profile の責務」という既存分担の延長。これは tool 設計上の選択であり理論の要求ではない(charter:52-56 と同じ精度で区別を明記した)。
- **C6(判定は ArchSig が独占)**: 境界所属・class 零性・closure 判定・detector 発火・適合条件検査はすべて ArchSig 内の計算。入力 artifact に結論フィールドを持たせない anti-weakening 検査で機械的に守る。
- **D1-D4(verdict 5値と packet 6区画)**: 新 verdict 行はすべて 5値規律に載る。行の立て方は §3.3 冒頭の判別基準(語彙の外は行なし / 語彙の内の計測不能は unmeasured 行)に従い、faithfulness 不在時の global-coherence は `unmeasured`(語彙の内)であり、行を消さず(内側の保護)、主役化しない(boundary statement 1行)。packet の6区画構造は変更せず、SAGA は computedInvariants + structural verdict 行 + assumptions + boundary statements として増築する。
- **B1 / B2(無制限 claim・extraction completeness の禁止)**: 本設計のどの結論も「選ばれた complex / cover / comparison / grounding の内部」に相対化される。GOALS.md G-06 claim boundary の非主張リスト(raw source extraction completeness、ArchMap correctness、repair synthesis completeness、コード全体の品質判定)をそのまま踏襲し、summary 語彙にもこれらへ触れる文型を置かない。
- **B5(Rust-Lean 対応の非要求)**: フィールド名の Lean 鏡写しと fixture 数値ロックは便宜であり contract ではない、と §3.4 / §3.9 に明記した。tool 出力が証明強度を自称しない規律(翻訳規律7)も同じ線の帰結。
- **肯定的結論の主役化**: すべての新 token は肯定形(GLUES / IDENTIFIED / HOLD / ESTABLISHED / PRESERVED)。否定的発見も `MEASURED_*`(測定された、という肯定形)で表現し、non-conclusion の羅列を summary に出さない。

---

## 5. 移行とリスク

### 5.1 実装順と v0.5.0 確約範囲

**v0.5.0 の確約範囲は Stage 1(条件が揃えば Stage 2 まで)に切る。Stage 3(S3 grounded 10結論・A3 harmonic-debt・A4 refactor-transport + `compare`)と Stage 4 は次版(v0.6.0 以降)へ送る。** §3.2 / §3.3.3 / §3.4 / §3.6 A3-A4 / §3.7(3) compare の設計本文は次版のための先行設計として保持する(設計は固定、確約はしない)。他の設計次元(LawPolicy 再設計・artifact/CI・skills・ArchView・コード分割)と同一版で並走するため、計測面の新規実装は Stage 単位で完結させる。

1. **Stage 1(v0.5.0 確約、最短の現場価値)**: `ag.cech-obstruction@2`(concrete class support + nerveShape + 定理12.4 3前提の有限検査)、summary token `REPAIR_TARGETS_IDENTIFIED`(既存 `ag.square-free-repair@1` invariant 参照、版上げ・リネームなし)、repair-plan/v1 schema + `repair-plan` 検証コマンド(`--residual-packet` 込み)、`ag.saga-descent@1` の **complete-support regime 限定**実装(faithfulness 供給不要 — 定理3.5 が実装の入口。mode↔support cross-check validator 込み)。circle nerve(3辺 Lean witness 形)/ B.8 fixture のロック。
   - 統合チェックリスト: `schema_catalog.rs` への `archsig-repair-plan/v1` 登録 / minimal fixture の `schema_version_catalog.json` 更新 / `STRUCTURAL_VERDICT_EVALUATORS`(現9種)への `ag.saga-descent@1` 追加 / 既存 CLI テスト(166本)の期待値更新 / summary token 追加が lean.yml の FieldSig handoff e2e(archsig-analysis-sft-input / schema-compatibility 検査)の期待値に与える影響の確認。
2. **Stage 2(v0.5.0 条件付き)**: `ag.saga-descent@1` の supplied faithfulness / true sheaf certificate 対応(層 C、class 語彙の解禁)、`ag.saga-comparison@1`(chart-indexed / identity の自動生成ケースから)、boundary statement / summary 翻訳テーブル + 出力語彙 lint(full sheaf 語 + 層 B class 語)、strict carve-out(§3.5)の実装。
   - 統合チェックリスト: `h1-comparison-data/v1` 等の schema catalog 登録 / catalog fixture 更新 / summary v2→v3 化が FieldSig schema-compatibility e2e に与える影響の期待値固定 / `STRUCTURAL_VERDICT_EVALUATORS` への `ag.saga-comparison@1` 追加。
3. **Stage 3(次版)**: `ag.saga-grounded@1`(lawEquation + holdsCriterion、10結論 packet、係数生成の square-free / F_2 Boolean 限定)、`ag.harmonic-debt@1`(cost model contract 込み)、`ag.refactor-transport@1` + `compare` コマンド。**前提: LawPolicy 次元の policy 行ごと profileRef 化(blocking 依存、§3.5)が入っていること。**
   - 統合チェックリスト: measurement-profile 版上げ(または v1 拡張)の catalog 反映 / `refactor-morphism/v1`・`refinement-comparison/v1` 登録 / compare の e2e fixture / profile fingerprint 正規化の実装(§3.7 の健全性要件)。
4. **Stage 4(second wave)**: `ag.nullstellensatz-certificate@1`(非観測 contract 経由)、`ag.hilbert-interference@1`、boundary residue 拡張。

### 5.2 リスクと対策

| リスク | 対策 |
| --- | --- |
| 単一 profile 制約(law-policy/v1 の measurementProfileRef 1本)により measured residual 一次ルートが単一 run で完結しない | 二 run 構成 + `--residual-packet` を v0.5.0 の正式経路とし(§3.5)、policy 行ごと profileRef 化を LawPolicy 次元への blocking 依存として宣言(§6-1)。単一 run 化はその解消後 |
| repair-plan の authoring コストが高く使われない | complete-support mode を既定にし(faithfulness 記述不要)、repair-plan authoring SKILL(archmap-creater と同型の規律: 読んだ証拠 → 機械検証 → complete-first ループ)を skills 次元で用意。chart-indexed の場合 incidence は自動生成 |
| 構成的 H^1 零(grounded 経路)と measured H^1 の混同 | evaluator を分離(S1 vs S3)、invariant を分離、lawIndependent.note を焼き込み、summary 翻訳規則2をテストで固定 |
| 「law が守られている」の判定源が interpretation / H^0 に滑る(系11.5 の逆向き推論) | holdsCriterion を必須入力 contract 化(§3.2)、premise 判定は生値検査のみ、token 発火条件から H^0 検査を排除(§3.8)、翻訳規則2 + summary 生成テストで固定 |
| comparison data が現場でほぼ供給されず S2 が死蔵 | 供給不要の 2 ケース(profile fingerprint 一致 = identity〔正規化複体表示の witness 要件込み〕、chart-indexed incidence)を自動化し、階段の下段(S1)だけでも独立に価値が出る設計にした |
| ArchMap が alias を潰す抽出をすると SAGA 十分性が退化 | aliasWitnesses 出力を ArchMap SKILL 次元への計測フィードバックとして供給。SKILL 側に「同一 subject に複数 semantic atom を許す(潰さない)」規律を要求(次元間 interface) |
| ag_measurement.rs(11,840行)への増築が破綻 | SAGA ファミリは新モジュール(例 `src/ag/saga.rs`)として追加し、dispatch の if-else 連鎖には乗せない。モジュール分割はコード次元の再設計と同時に行う |
| profile v2 版上げが LawPolicy 再設計と衝突 | 本設計の要求は「lawEquation ブロック + generated 係数語彙」の2点のみに絞ってあり、v1 拡張でも v2 新設でも載る。決定は LawPolicy 次元に委ねる(ただし policy 行ごと profileRef 化は blocking 依存) |
| registry manifest に残る判定語 predicate 名(tripleMismatch 等の残存ドリフト) | Stage 1 のレガシー整理と同時に一掃(観測純化 PRD の残件消化と同一 PR で) |
| candidate 系(stability / Wasserstein)を求められて境界が緩む | C1 行の通り v0.5.0 では見送り推奨。入れる場合も `regime: "candidate"` を schema 必須にし structural verdict への参照を禁止する検査を先に入れる |
| strict CI と沈黙の手続き化の衝突(層 B 正常系 run が strict で常に fail) | silence_by_design 行の strict 集計 carve-out を本設計で固定(§3.5)。実装詳細は artifact/CI 次元と共有 |

### 5.3 レガシー破棄との関係

本設計は v1 typed evaluator 経路に依存しない(AG path はコード独立)。pr-review(v1 専用)の消滅に対し、`compare` + `ag.refactor-transport@1` + repair-plan フローが AG 版の後継系となる(compare 系は次版確約、§5.1)。第1世代の monodromy / ACTS / homotopy ファミリは AG 経路に後継(第VI部沈黙 / sheaf-laplacian proxy / period-stokes-audit)が既にあり、本設計で再実装しない。

---

## 6. 未決事項

1. **measurement profile の版と LawPolicy blocking 依存**: `lawEquation` を v1 拡張で入れるか `measurement-profile/v2` を新設するか。LawPolicy 再設計次元の案(profile の ref 化・非対称解消を含む)との統合判断。**本設計は policy 行ごとの profileRef 化を measured residual 一次ルートの blocking 依存として宣言済み(§3.5)** — 版の形式は開くが、この依存自体は開かない。
2. **repair-plan の作者と CI 配線**: PR フローで誰が repair-plan を書くか(PR author の agent / 専用 SKILL / 半自動生成)。repair-plan-creater SKILL の要否は skills 次元へ。
3. **`ag.saga-descent@1` の層 B / C を単一 evaluator にするか分割するか**: 本設計は単一(triple の有無でモード分岐)としたが、profile 検証の単純さを優先して `ag.saga-class@1` を分ける案もある。実装時に決定。
4. **B^1 所属判定の計算量上限**: supplied primitive 加群が大きい場合の探索上限(既存の MAX_* const と同様の実装定数にするか、profile から選べるようにするか)。第VIII部語彙との対応表(profile ↔ 有限上限)の整備は artifact 次元と共同。
5. **NSdepth 探索**: certificate 検証のみ(supplied、非観測 contract 経由)から始めるか、有界探索(次数上限付き)まで入れるか。
6. **conormal 係数(I_U/I_U²)の読み**: 相異なる非零 lawful reading が貼り合う係数は理論側の open question(G-04 の入口)。tool 側は受け皿を作らず沈黙。理論の進展後に別設計。
7. **exit code / CI status 写像の最終形**: strict carve-out の方針(silence_by_design 行の集計除外)は §3.5 で本設計が固定済み。残る未決は unknown をどの CI status に写像するか等の表示詳細のみで、artifact/CI 次元の設計と統合して決める。
8. **`compare` の profile fingerprint の定義**: doctrine / law universe 等をハッシュにどこまで含めるかの付加範囲と、正規化手順の詳細は artifact 次元と共同で確定する。ただし**健全性要件は本設計で固定済み(§3.7)**: identity 自動採用の条件は参照名一致ではなく、正規化後の有限複体表示(context 集合・overlap・triple 構造)の同一性を fingerprint が witness すること。この要件を満たさない解決(参照名のみのハッシュ)は解決空間から除外する。

---

## 査読対応

15件の指摘すべてを検討し、全件を採用した(一部は反映形を調整)。コード・Lean 事実に関わる指摘(7・8・10・11・13・15)は実ファイルで裏取りした上で反映した。

| # | 種別 | 採否 | 反映箇所と要点 |
| --- | --- | --- | --- |
| 1 | boundary/minor | **採用** | §3.7(3) に fingerprint の健全性要件(正規化後の有限複体表示の同一性 witness、参照名ハッシュの排除)を追加。§3.3.2 の identity 条件と同一内容であることを相互参照で明示。未決事項8 を「付加範囲と正規化手順のみ未決、健全性要件は固定済み」に書き換え、不健全な解決空間を設計段階で排除した。 |
| 2 | boundary/minor | **採用** | §3.4 detectorFindings の reading と §3.8 token 一行を定理帰属型(「保証する(系11.5 detector soundness。定理は Lean proved、前提計算は本 run の測定)」)に変更。§3.4 要点3 も同様。翻訳規律に第7項「『証明する』は theoremRef 付きの定理帰属文でのみ使う」を追加し、summary 生成テストで固定する方針を明記。 |
| 3 | boundary/minor | **採用** | §3.6 B1 の入力要件に「supplied unit certificate は非観測 contract(repair-plan 系 artifact または profile 側参照)で受け、ArchMap には置かない」を明記。観測純化 PRD(nsdepthCertificate 廃止)との関係(検証専用の外部 certificate 受け入れは判定の先書きに当たらない)を claim 境界列に1文追加。§4 C2 にも同旨を反映。 |
| 4 | theory/major | **採用** | 逆向き推論(interpretation / H^0 → law 成立)を全面排除。(1) `holdsCriterion`(chart-local holds-defect tie の生値評価意味論)を lawEquation の必須入力 contract に追加し(§3.2)、premise 判定はそこからのみ生成、operationalization の assumption ledger 行を規定。(2) §3.8 の `DISPLAYED_LAWS_HOLD` 発火条件から「H^0 検査 pass(定理8.1)」を削除し law-check contract(定義11.3)へ付け替え。(3) 翻訳規律2 を「law-check 行からのみ生成し、interpretation 零・H^0 零からは生成しない(系11.5)」に書き換え。§3.3.3 の計算列・§3.4 の premise 証拠(checkKind / holdsCriterionRef)も同期。§5.2 にリスク行を追加。 |
| 5 | theory/major | **採用** | §3.6 A1 と §3.8 の発火条件を定理12.4 の3前提(isForest ∧ tripleOverlaps 空 ∧ 全 restriction map 全射性検査 pass、各 discharged_by_check)に明記。token 一行を「選ばれた abelian 係数と cover の中で、cover の形と検査済み restriction から H^1 障害は排除される」に相対化し、non-abelian torsor / stacky descent / gerbe obstruction の非排除を invariant 側 boundary note に規定。 |
| 6 | theory/minor | **採用** | 層 B の token を `MEASURED_NONGLUING_RESIDUAL`、フィールドを `residualSupport` に改名(§3.3.1 / §3.6 S1 / §3.8)。class 語彙の token(`MEASURED_NONGLUING_RESIDUAL_CLASS`)・フィールドは層 C(Z^1/B^1 構成)供給時のみ emit と規定。§3.7 の出力 lint に「boundary-membership 段での class 語」を追加(part_10 定義3.2 の語彙規律)。 |
| 7 | theory/minor | **採用** | Lean `CompleteSupportBoundaryComplex` の `support_eq`(全 primitive)を確認。§3.1 の validator 規則に「mode=complete-support のとき全 primitive の support.kind=complete でなければ hard error」を cross-field 検査として追加し、例 JSON の `prim:pin-ledger-schema` を complete に修正。enumerated support の用途(mode=supplied/none)はフィールド表の注記に移動。 |
| 8 | theory/minor | **採用** | `SemanticRepairPart10.lean` の `circleSimplex` が `Fin 3`(3辺)であることを確認。§3.9 の circle nerve 行を「Lean witness = 3辺 instance(proved 帰属はこちら、数値ロックの一次 fixture)」と「本文 worked example = 2頂点・逆向き2辺(理論本文仕様、Lean proved ではない、補助 fixture)」の2行に書き分け、witness の形ごとの proved 帰属を明示。 |
| 9 | theory/minor | **採用** | §3.6 A3 の入力要件に cost model(Lipschitz 定数 L の宣言 + harmonic-resolution 要求)の supplied 必須化と assumption ledger 記録を追加。cost model 不供給の run では定理8.6 の \\|h(g)\\| certified 文までとし、`essentialRepairLowerBound` 行は立てない(silence_by_design)と明記。系8.7 の前提を入力 contract に載せずに結論を出す形を解消。 |
| 10 | feasibility/major | **採用** | law_policy.rs(measurementProfileRef 1本)と validate_cech_profile_v1 の相互排他を確認。§3.5 に「measured residual の実行機構(3条件)」を新設: (a) policy 行ごと profileRef 化を LawPolicy 次元への blocking 依存として宣言(§6-1 にも固定)、(b) `--residual-packet` CLI 入力を analyze / repair-plan に追加し参照解決 + cocycle 検査を規定、二 run 構成を v0.5.0 正式経路化、(c) residual.kind=measured 時の chart-indexed 必須を §3.1 validator 規則として層 B から課す。§3.0 / §5.2 にも反映。 |
| 11 | feasibility/major | **採用** | ag_measurement.rs(minimalForbiddenSupports / deltaComplex / alexanderDualRepair.minimalHittingSets の invariant 出力、ArchView 投影 4556 行)を確認し、§2.4 の gap リストから定理5.2 を外して実装済み事実を明記。§3.6 A2 を「summary token `REPAIR_TARGETS_IDENTIFIED` の追加のみ(既存 @1 invariant 参照)」に縮退し、@2 版上げ・フィールドリネームを撤回。補足 JSON も既存フィールド参照形に差し替え。Stage 1 も同期。 |
| 12 | feasibility/major | **採用** | §5.1 を「v0.5.0 確約範囲 = Stage 1(条件付きで Stage 2)。Stage 3(S3・A3・A4 + compare)以降は次版へ送る」と明示し、§1 / §3.3.3 / §3.6 表 / §5.3 に確約範囲外の注記を同期。S3 の設計本文は次版先行設計として保持。あわせて §3.2 に係数生成の計算可能クラス限定(square-free / F_2 Boolean + MAX_* 有限上限、Gröbner 級機構の不導入)を規律として書き込んだ。 |
| 13 | feasibility/minor | **採用** | main.rs の strict 挙動(nonTerminal 1行で exit 1)を確認。§6.7 への全面先送りをやめ、§3.5 で方針を固定: strict の nonTerminal 拒否を「宣言済み入力が揃っている evaluator の行」に限定し、silence_by_design を伴う行を strict 集計から carve-out する(pass への丸めではなく分母からの除外 + boundary statement 報告)。§5.2 にリスク行、§6.7 を表示詳細のみの未決に縮小。 |
| 14 | feasibility/minor | **採用** | §3.3 冒頭に一般則「選ばれた語彙の外(profile が層を選んでいない)は行を立てない / 語彙の内で計測不能は unmeasured 行を立てる」を明文化し、§3.3.1 の verdict 表に「判別基準の適用理由」列を追加して residual-class(語彙の外 → 行なし)と global-coherence(語彙の内 → unmeasured 行)の非対称を基準から導出。§4 D1-D4 に「D 群の行保護は語彙の内の行に適用」と整合を明記。 |
| 15 | feasibility/minor | **採用** | §5.1 の各 Stage に統合チェックリスト(schema_catalog.rs 登録 / schema_version_catalog.json 更新 / STRUCTURAL_VERDICT_EVALUATORS〔現9種〕への追加 / 166 CLI テスト期待値 / lean.yml FieldSig handoff e2e〔archsig-analysis-sft-input / schema-compatibility〕への影響確認)を追加。 |

不採用とした指摘はない。ただし #12 は「S3 以降の設計記述の削除」までは行わず、確約範囲の宣言 + 先行設計としての保持という形で反映した(設計文書の役割は次版の設計を先に固定することにもあるため)。
