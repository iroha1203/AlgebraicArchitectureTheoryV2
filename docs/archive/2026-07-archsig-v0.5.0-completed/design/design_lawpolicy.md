> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計ノート: LawPolicy の再設計(設計次元3)

日付: 2026-07-04(査読反映改訂)。担当: LawPolicy 再設計。
本ノートは docs/note 向け設計文書のドラフトであり、調査レポート
(archmap-lawpolicy / saga / philosophy / ag-theory / archsig-code / skills-workflow)と
一次ファイル(`tools/archsig/src/schema/law_policy.rs`、`law_policy/registry.rs`、
`src/ag_measurement.rs`、`tests/fixtures/ag_measurement/law_policy_*.json` /
`archmap_v2_*.json`、`Formal/AG/LawAlgebra/LawEquation.lean`、
`docs/tool/archmap_lawpolicy_archsig_responsibility_charter.md`、
`docs/aat/algebraic_geometric_theory/part_3` / `part_8` / `part_10`)に基づく。
AAT 数学本文が正であり、本ノートはそれに相対化される(責務憲章:6 と同じ規律)。

---

## 1. 目的

v0.5.0 のユーザー方針「Law ポリシーは設計を見直した方がいいかもしれない。いくつか案を出してほしい」に応え、
対立する 4 案を schema フィールドレベルで提示し、比較表と推奨を付ける。

再設計の判定規律として、次の 3 つを固定する。

1. **理論忠実性**: G-06 で確定した「law は方程式である」(第III部 定義11.3 / 定理11.4、Lean proved)。
   原則11.6 が核心を一行で言う — 「predicate does not determine the equation. no coefficient, no cohomology.」
   不透明な述語名だけを選ぶ政策からは、係数も cohomology も生成されない。
   SAGA(第X部)を現場接続するには、law-equation データがどこかに supplied されなければならない。
   設計問題は「**方程式をどこに置くか**」に帰着する(registry 焼き込み / LawPolicy 内 / 独立 artifact / 統合文書)。
2. **責務憲章との整合**: LawPolicy は selector + law universe 指定(何が forbidden かの選択)。
   witness predicate の手書き・score formula・circuit 定義・profile 本体は持たない(charter:84-94)。
   inclusion-minimal 列挙・obstruction ideal 構成の実行者は ArchSig(charter:93-94)。
   責務線を動かす案は「theory 由来か tool 設計選択か」を明示する(charter:52-56 の A8 の扱いが手本)。
3. **v0 の轍を踏まない**: LawPolicy v0 は全部入り(witnessRules / moleculePatterns /
   obstructionCircuitDefinitions / part4DistanceProfile / spectrumMeasurementProfile …)で破棄された。
   v1 は selector に振り切った。v0.5.0 は振り子の中間点を「理論が定理で正当化する範囲だけ」開く。

---

## 2. 現状の問題(証拠付き)

現行 `law-policy/v1`(`schema/law_policy.rs:5-18`)の実測形状:

```json
{
  "schema": "law-policy/v1",
  "id": "...",
  "distanceProfileRef": "distance-profile:architecture-default@1",
  "measurementProfileRef": "profile:ag-default@1",
  "measurementProfiles": [ { "schema": "measurement-profile/v1", "...": "本体埋め込み" } ],
  "policies": [ { "pack|law": "...", "evaluator": "...", "basis": [], "scope": [], "severity": "high" } ]
}
```

| # | 問題 | 証拠 |
| --- | --- | --- |
| P1 | **方程式データの供給経路が二形態に分裂し、いずれも政策文書から書けない**。cech 系では law の内容(cocycle / coboundary 判定)が `ag_measurement.rs` の evaluator 実装に焼き込みで、政策を変えても方程式は変わらない。square-free / tor 系では forbidden 生成元が ArchMap の生 support atom(+ profile witnessFamily)から供給され、観測された support 集合がそのまま I_Ob 生成元になる(`square_free_generators`、src/ag_measurement.rs:9204)— すなわち **law universe データが観測 artifact 側に混入**している。どちらの経路でも SAGA level E(law-equation grounded surface)を政策文書から組めない | 原則11.6(part_3:1821-1834)、ag_measurement.rs の if-else dispatch(archsig-code 調査)、src/ag_measurement.rs:9204, 9246 |
| P2 | **記述力の欠如**。basis registry は `policy-basis:solid` / `policy-basis:layering` の 2 種のみ(registry.rs:81-83)。PRD の例示 `"basis": ["docs.architecture.layering"]` すら検証を通らない。リポジトリ固有の設計文書を根拠として指す道がない | archmap-lawpolicy 調査 §2.3 |
| P3 | **MeasurementProfile の非対称と意味論不在**。profile 本体が LawPolicy に埋め込み(distanceProfileRef の ref 方式と非対称)。siteRef / domain / zeroPredicate 等は非空検査のみで意味は実装内解釈。有限上限(12/16、7 定数)は実装定数で profile から選べない | law_policy.rs:20-44、validate.rs:312-355、ag_measurement.rs:31-37 |
| P4 | **witnessFamily の置き場所が law-equation realization 構造とずれる**。witness 変数は定理11.4 の law equation realization では violation coordinates として law 側成分(第III部 定義11.3)だが、現行は計測手段側の profile に置かれ、変数名は自由文字列で ArchMap との突合せ規約がない。なお第VIII部 定義2.1 は selected witness variables E を measurement profile M の成分として明記しており、「E を law 側 artifact に置く」こと自体は theory 由来ではなく **theory 整合的な tool 設計選択**である(M は law 側データも束ねる包括 profile であり、artifact 分割は M の細分という設計。§5 参照) | part_3 定義11.3、part_8 定義2.1(part_8:60-79)、fixture `law_policy_square_free.json`、skills-workflow 調査 |
| P5 | **v1 レガシーの同居**。`distanceProfileRef` + コンパイル内蔵 distance profile 2 種は古典 AAT(Part IV 距離)経路専用。solid pack / domain evaluator も v1 typed evaluator 専用。registry manifest には観測純化前の判定語 predicate 名(`legacy-coherence-token` / `legacy-boundary-token` / `legacy-section-token`)が残存 | registry.rs:85-90, 184-207, 284, 318, 388 |
| P6 | **CI 連携の台紙がない**。SAGA 定理8.4(cover-relative Čech H^1 と sheaf cohomology の比較)/ 定理8.5(refinement に沿う自然性)は「比較可能性はデータである」を定理水準で確定している。その示唆を受けた **tool 設計選択**として、計測間比較には profile / 政策の同一性・差分を fingerprint 付き artifact として持ち回るのが自然だが、埋め込み構造では政策変更と計測手段変更が単一文書に混ざり、指紋が分離できない。fingerprint は比較の前提(どの成分が固定されたか)の記録であって 8.4/8.5 が要求する comparison / refinement data そのものではない(comparison data 本体、および 8.4/8.5 の射程外である版間差分の比較は設計次元4 の管轄) | part_10:837-857、saga 調査 §6.4.7 |

---

## 3. 設計案

4 案を提示する。案1 は最小主義の純化、案2 は law-equation の LawPolicy 内一級化、
案3 は LawPolicy と MeasurementProfile の統合、案4 は 3 artifact への層化(政策バンドル)。
案2 と案4 は「方程式の一級化」を共有し、置き場所(単一文書 vs 独立 artifact)で対立する。

共通前提(全案共通):

- v1 レガシー削除に伴い `distanceProfileRef` と solid/domain 系 evaluator・pack を schema / registry から除去する。
- verdict 五値・measurement packet 6 区画・fail-closed(`ag.*` evaluator は profile 必須)は全案で不変。
- 政策文書にも ArchMap R3 と同型の**判定語 hard error**(結論相当フィールドの禁止)を課す(§5 参照)。

### 3.1 案1: Selector 純化案(現行 v1 の徹底)

**思想**: LawPolicy は selector である、を純化する。方程式は registry(コード内 evaluator)の所有のままとし、
v1 レガシー削除・profile の独立 artifact 化・basis の開放という「掃除と非対称解消」だけを行う。

**schema 概形** `law-policy/v2`:

```json
{
  "schema": "law-policy/v2",
  "id": "policy:shop-backend@1",
  "measurementProfileRef": "profile:ag-default@2",
  "policies": [
    {
      "law": "ag.cech-obstruction",
      "evaluator": "ag.cech-obstruction@1",
      "basis": ["basis:adr-0007"],
      "scope": ["src/"],
      "severity": "high"
    }
  ],
  "basisLedger": [
    {
      "basisId": "basis:adr-0007",
      "kind": "repo-document",
      "path": "docs/adr/0007-context-ownership.md",
      "revision": "git:abc1234"
    }
  ]
}
```

変更点:

- `distanceProfileRef` 削除(v1 経路と同時破棄)。`pack` は当面削除(solid pack が唯一の実体で v1 専用のため)。
- `measurementProfiles[]` 埋め込みを廃止し、`measurementProfileRef` + 独立ファイル
  `measurement-profile/v2`(CLI で渡す)に統一。ref 方式へ対称化。
- `basisLedger` 新設: basis を registry ハードコードから**政策文書内の宣言台帳**に開く。
  `policies[].basis` は `basisLedger[].basisId` に解決必須(内部整合検査)。
  `kind` は `repo-document` / `external-standard` / `registry` の 3 値。
  ArchSig が検査するのは台帳内解決のみで、文書内容の意味検証はしない(evidence contract の宣言)。

**CLI**:

```bash
archsig analyze \
  --archmap archmap.json \
  --law-policy law_policy.json \
  --measurement-profile measurement_profile.json \
  --out-dir .tmp/archsig-analyze
```

**ArchMap との責務分割**: 現行と同じ。ArchMap = 生値観測、LawPolicy = evaluator/basis/scope/severity の選択、
方程式の実体 = registry(ArchSig コード)。一括払い哲学との緊張はないが、
「制度選択」の実質が registry に前払いされたまま author の手が届かない。

**SAGA 接続**: evaluator 追加方式(現行の受け皿 = evaluator + profile 検証 + assumption 定理参照の 3 点セット)で
SAGA 系 evaluator(`ag.saga-boundary-membership@1` 等)を registry に足す。
law-equation grounded surface のデータ(skeleton / defect source / quotient sheaf condition)は
profile フィールドか ArchMap 側へ押し込むことになり、**P1 と P3 が再生産される**
(profile フィールドの意味論が実装内解釈のまま肥大する)。

**移行コスト**: 小。schema 改版 + fixture 書き換え + registry 掃除。
**リスク**: SAGA level E の政策記述力が得られない。「代数幾何 AAT に基づく分析の充実」という
v0.5.0 の主方針に対して受け皿が evaluator ハードコードのままで、
law を足すたびに Rust 実装追加になる(現場の law は政策で書けない)。

### 3.2 案2: Law-Equation 一級化案(LawPolicy 内に方程式)

**思想**: G-06 の成果を schema に直結させる。LawPolicy に `laws[]` セクションを新設し、
各 law を**witness 方程式**として宣言的に書かせる。

ArchSig が宣言から**自動生成する**のは次の範囲に限る:
`I_Ob = ⟨x_S : S ∈ Forb⟩ = I_Δ`(定理5.6C)、minimal forbidden supports・
Alexander dual hitting sets(**第VIII部 定理5.2**、Stanley-Reisner / Alexander Dual Repair Theorem)、
商環 `Q = O/I_Ob`。

**defect class と restriction evaluator(第III部 定理11.4)はこの宣言だけからは生成できない**。
定理11.4 の law equation realization(定義11.3)は、displayed local reading の
defect observable `d_i`・非空 required law support・chart-local law-defect tie を
**supplied 成分**として要求し(Lean 実装では `LawEquationDefectSource` の
`defect` / `lawSupport` / `holds_defect_mem` が supplied フィールド、
`Formal/AG/LawAlgebra/LawEquation.lean:223-245`)、さらに restriction evaluator は
「displayed required laws が充足されるならば」という条件付き結論である
(`DisplayedRequiredLawsHoldOn` を仮定に取る、同 331-335)。
したがって defect class・restriction evaluator は
**defect source が供給され、かつ law 充足前提が満たされる場合のみ**生成対象になる。
案2 の schema(witnessVariables + forbiddenSupportGenerators)には defect source の入力欄がなく、
**案2 単体では SAGA level E に届かない**(下記リスク (c))。

**schema 概形** `law-policy/v2`:

```json
{
  "schema": "law-policy/v2",
  "id": "policy:shop-backend@1",
  "measurementProfileRef": "profile:ag-default@2",
  "laws": [
    {
      "lawId": "law:no-cross-context-write@1",
      "conditionType": "closed-equational",
      "witnessVariables": [
        {
          "variable": "x_checkout",
          "binding": { "axis": "square-free", "predicate": "support" }
        },
        {
          "variable": "x_inventory",
          "binding": { "axis": "square-free", "predicate": "support" }
        }
      ],
      "forbiddenSupportGenerators": [
        { "support": ["x_checkout", "x_inventory"] }
      ],
      "basis": ["basis:adr-0007"],
      "scope": ["src/"],
      "severity": "high"
    },
    {
      "lawId": "law:gateway-timeout-present@1",
      "conditionType": "open",
      "evaluatorRef": "ag.section-factorization@1",
      "basis": ["basis:runbook-timeouts"],
      "scope": ["src/gateway/"],
      "severity": "medium"
    }
  ],
  "basisLedger": [ "…(案1 と同じ)…" ]
}
```

**フィールド意味論**:

- `conditionType`: 第III部 原則5.8 の law condition 6 型
  `closed-equational | open | constructible | descent | temporal | stacky` の enum。
  **`closed-equational` 型のみ ideal 意味論(方程式→係数生成)を持つ**。
  他の 5 型は `evaluatorRef` 必須で registry evaluator に委ね、ideal 化を schema validation で拒否する
  (「closed law だけを ideal 化し、他を不自然に ideal 化しない」claim boundary の schema 化)。
- `witnessVariables[].binding`: ArchMap の生値語彙への束縛宣言。binding は判定を書く場所ではなく、
  「law universe のこの変数は観測のこの生値座標である」という**束縛宣言**。
  変数の外延(**観測上 — すなわち ArchMap 生値上 — で**この support が生起しているか)は
  ArchMap 生値との突合せで ArchSig が決める。ArchSig が語るのは ArchMap が記録した生値についてのみで、
  source extraction の健全性(現実コードベースとの対応)は主張しない
  (第VIII部 原則2.2 Measurement Is Internal、責務憲章)。
- `forbiddenSupportGenerators`: square-free monomial 生成元(witness 変数集合の部分集合)の列挙。
  inclusion-minimal である必要はない(minimal 化は ArchSig の仕事、charter:93-94)。
  係数・重み・スコアは書けない(square-free monomial のみ)。
  hitting sets を出力・表示する箇所には第VIII部 原則5.3 の boundary
  (hitting set は combinatorial repair target であって repair semantics ではない)を必ず併記する。

**binding と NormalizedAtomV2 の対応規則**(v0.4.0 実データ形状に基づく。案4 も同一規則を共有):

- 照合対象は NormalizedAtomV2(subject / object / axis / predicate / contextMemberships)。
  predicate は R2 中立語彙 `support` / `cooccurrence` / `sectionValue` に限定。
- `axis: "square-free"`(tor 系も同形): 実データでは support atom が subject / object に
  **カンマ区切りの witness 変数名リストを直接運ぶ**
  (`square_free_atom_variables`、src/ag_measurement.rs:9246。
  fixture `archmap_v2_square_free_repair.json` の `subject: "x_checkout", object: "x_inventory"`)。
  したがって束縛は**変数名の同一性照合**とする: law surface の `variable` 名が、
  選ばれた context 内の support atom の変数リスト要素として現れるとき、
  その atom はこの変数を含む観測 support である。subject / object の区別は照合に使わない
  (両者を合併したリストが 1 atom の観測 support)。law surface 側で別名を使いたい場合のみ
  `binding.archmapVariable` を明示する(省略時は `variable` と同名)。
- `axis: "cech"`: 実データでは sectionValue atom は subject に context id(`ctx:*`)、
  値を object(key=value)に運び、`overlap:*` という subject 語彙は存在しない
  (fixture `archmap_v2_cech_h1_visible.json`)。overlap 座標は contexts の `restricts_to` から
  ArchSig が導出する Čech 1-skeleton の辺である。したがって束縛は
  `binding.edge: ["ctx:a", "ctx:b"]` で宣言し、ArchSig が導出 1-skeleton の辺に解決する
  (解決不能は validation fail)。変数の生値材料は両 context を subject に持つ sectionValue atom。
- **既存 atom の意味論移行(Stage 2)**: v0.4.0 では観測された support 集合が
  **そのまま I_Ob 生成元になる**(`square_free_generators`、src/ag_measurement.rs:9204)。
  Stage 2 では forbidden 生成元は law surface の宣言(Forb)へ移り、ArchMap の support atom は
  「変数集合の共起という観測事実」(observed complex 側)へ**再解釈**される。
  archmap/v2 の schema 形状は不変だが、これは意味論の反転であり、
  ArchMap authoring 規約・archmap-creater SKILL・fixture の改訂を要する(§6 Stage 2)。
  したがって「観測側に何も要求を追加しない」という主張は成り立たず、正しくは
  「**schema 形状水準では不変、authoring 規約水準では改訂が必要**」である。

**CLI**: 案1 と同じ(文書が 1 つ増えないのが利点)。

**ArchMap との責務分割**:

| 層 | 所有 |
| --- | --- |
| ArchMap | 生値のみ(support / cooccurrence / sectionValue の生起事実) |
| LawPolicy | law universe = 変数宣言 + 束縛 + forbidden support 生成元 + 型分類 + selector 面 |
| ArchSig | minimal 化・I_Δ・Alexander dual・Q・verdict の全計算(class 生成は defect source 供給時のみ) |

「何が forbidden か」の選択が registry から政策文書へ移り、charter:86-87
「law は loci を切り出す」の実装位置が author の手に入る。
**憲章の「witness predicate 手書き禁止」との関係**: 憲章が排するのは判定ロジックの自由記述
(評価式・スコア・circuit DSL)。forbidden support の宣言は「何が forbidden か(law universe)」の
指定そのもので、憲章が LawPolicy の所有と明記する側にある。ただしこの線引きの精密化は
**theory 由来(定理5.6C / 原則5.8 / 原則11.6)+ tool 設計選択(binding を名前照合・edge 宣言に制限)**の
複合であることを設計文書に明示する。

**SAGA 接続**: 定理11.4 の law equation realization の方程式面(変数 + Forb)に対応する。
level E の残り(defect source、quotient sheaf condition、skeleton)は `laws[]` の姉妹フィールドとして
LawPolicy に足していけるが、文書が単調に肥大し、政策の変更(severity 変更)と
方程式面の変更(witness 変数追加)が同一 fingerprint に混ざる。

**移行コスト**: 中〜大。schema 新設 + 「宣言→ evaluator 実行計画」の generic 化
(現行 if-else dispatch の再編)+ fixture / SKILL / docs の全面改訂。
**リスク**: (a) DSL 肥大の坂道 — v0 の轍。緩和策は上記の制限
(closed のみ ideal 化・square-free monomial のみ・binding は名前照合 / edge 宣言のみ)を
deny_unknown_fields と validation で強制すること。
(b) 単一文書の肥大で CI 差分比較(P6)が改善しない。
(c) **案2 単体では SAGA level E に届かない**(defect source の入力欄がない。
姉妹フィールドを足すと (a)(b) が加速する)。

### 3.3 案3: 統合案(LawPolicy ⊕ MeasurementProfile → 単一 measurement-policy/v2)

**思想**: 現実の運用では LawPolicy と MeasurementProfile は常に対で使われ(fail-closed)、
分けておく利便が薄い。1 文書 1 CLI 引数に統合して authoring を最小化する。

**schema 概形** `measurement-policy/v2`:

```json
{
  "schema": "measurement-policy/v2",
  "id": "mpolicy:shop-backend@1",
  "site": { "siteRef": "archmap:/contexts", "domain": "finite-poset-site" },
  "cover": { "coverRef": "cover:order-inventory" },
  "coefficient": { "ring": "F2", "effCoeff": "finite-linear-algebra@1" },
  "resolutionSelector": "taylor@1",
  "verdict": {
    "zeroPredicate": "rank-zero@1",
    "nonZeroPredicate": "rank-positive@1",
    "certSelector": "finite-certificate@1",
    "discipline": "five-valued-structural-verdict@1"
  },
  "witnessFamily": [ { "law": "ag.square-free-repair", "variable": "x_checkout" } ],
  "policies": [
    { "law": "ag.square-free-repair", "evaluator": "ag.square-free-repair@1",
      "basis": ["basis:adr-0007"], "scope": ["src/"], "severity": "high" }
  ],
  "basisLedger": [ "…" ]
}
```

**CLI**:

```bash
archsig analyze --archmap archmap.json --measurement-policy mpolicy.json --out-dir .tmp/a
```

**ArchMap との責務分割**: ArchMap は不変。制度選択と計測手段選択が単一文書に同居する。

**SAGA 接続**: 案1 と同水準(方程式は registry のまま)。統合しても P1 は解けない。

**移行コスト**: 中(schema 統合 + CLI 簡素化 + fixture 改訂)。
**リスク**: **責務憲章の機能条件を弱める**。三層分離の根拠は「誤結論時に観測 / ポリシー / 計算の
どれが誤ったかの切り分け」(charter:12-14)であり、統合文書では
「law の選択が誤った」と「cover / 係数の選択が誤った」が単一 artifact の中で混ざる。
さらに SAGA 8.5 の観点で、cover 変更(計測手段変更)のたびに政策文書全体の fingerprint が変わり、
「政策は同一のまま計測だけ変えた」ことを artifact 水準で言えなくなる。P6 が悪化する。

### 3.4 案4: 政策バンドル層化案(law-policy / law-equation-surface / measurement-profile の 3 artifact)★推奨

**思想**: SAGA の supplied / generated 境界(part_10:42-54)を artifact contract 境界に写す。
方程式の一級化(案2 の内容)は行うが、置き場所を LawPolicy 本体ではなく
**独立 artifact `law-equation-surface/v1`** にする。LawPolicy は selector のまま保存され(憲章 C5 不変)、
3 文書がそれぞれ独立に fingerprint を持ち、CI 連携の比較データの台紙になる。

**構成**: 3 artifact + 任意の bundle manifest。

(a) `law-policy/v2` — selector(案1 とほぼ同形、任意フィールド `lawSurfaceRef` が加わる):

```json
{
  "schema": "law-policy/v2",
  "id": "policy:shop-backend@1",
  "lawSurfaceRef": "law-surface:shop-backend@1",
  "measurementProfileRef": "profile:ag-default@2",
  "policies": [
    {
      "law": "law:no-cross-context-write@1",
      "evaluator": "ag.square-free-repair@1",
      "basis": ["basis:adr-0007"],
      "scope": ["src/"],
      "severity": "high"
    },
    {
      "law": "law:order-inventory-gluing@1",
      "evaluator": "ag.cech-obstruction@1",
      "basis": ["basis:context-map"],
      "scope": ["src/"],
      "severity": "high"
    }
  ],
  "basisLedger": [
    { "basisId": "basis:adr-0007", "kind": "repo-document",
      "path": "docs/adr/0007-context-ownership.md", "revision": "git:abc1234" },
    { "basisId": "basis:context-map", "kind": "repo-document",
      "path": "docs/architecture/context_map.md", "revision": "git:abc1234" }
  ]
}
```

- severity / scope / basis という「運用判断」はここに残る。方程式を一切書かない。
- **`policies[].law` の解決規則は `lawSurfaceRef` の有無で条件化する**(下表)。
  law surface の利用は CLI フラグではなく**政策文書自身の contract 選択**であり、
  入力欠落を引き金にした fallback は存在しない。

| 文書に `lawSurfaceRef` | CLI に `--law-surface` | 挙動 |
| --- | --- | --- |
| あり | あり | 供給された surface の `id` と `lawSurfaceRef` の一致を検査。`policies[].law` は surface の `lawId` に解決必須。未解決は validation fail |
| あり | なし | **fail-closed**(入力契約違反)。宣言済み参照の未供給を黙殺しない |
| なし | あり | **fail-closed**(契約不一致)。文書が宣言しない artifact を暗黙採用しない |
| なし | なし | **v0.4.0 相当 contract**(schema 水準の明示宣言として受理)。`policies[].law` は registry law id(`ag.*` 形)として検証。closed-equational 系の ideal 意味論・law surface 由来機能は無効。`ag.*` evaluator は従来どおり profile fail-closed の下で直接駆動 |

  この条件化により、Stage 1 で書かれた `lawSurfaceRef` なしの政策文書・fixture は
  Stage 2 以降も同じ schema 文字列 `law-policy/v2` のまま有効であり続ける(無告知の意味変更がない)。
  条件化で足りるため v3 への版上げは行わない。
  4 行目の v0.4.0 相当 contract は**author が文書で選ぶ縮退契約**であって、
  ArchSig が law universe を registry の方程式で補完する fallback ではない(§5 参照)。

(b) `law-equation-surface/v1` — law universe の方程式面(案2 の `laws[]` 語彙を移設。
binding の意味論と NormalizedAtomV2 対応規則は §3.2 と同一):

```json
{
  "schema": "law-equation-surface/v1",
  "id": "law-surface:shop-backend@1",
  "laws": [
    {
      "lawId": "law:no-cross-context-write@1",
      "conditionType": "closed-equational",
      "witnessVariables": [
        { "variable": "x_checkout",
          "binding": { "axis": "square-free", "predicate": "support" } },
        { "variable": "x_inventory",
          "binding": { "axis": "square-free", "predicate": "support" } }
      ],
      "forbiddenSupportGenerators": [
        { "support": ["x_checkout", "x_inventory"] }
      ]
    },
    {
      "lawId": "law:order-inventory-gluing@1",
      "conditionType": "closed-equational",
      "witnessVariables": [
        { "variable": "x_order_inventory",
          "binding": { "axis": "cech", "predicate": "sectionValue",
                       "edge": ["ctx:order", "ctx:inventory"] } }
      ],
      "forbiddenSupportGenerators": [
        { "support": ["x_order_inventory"] }
      ]
    },
    {
      "lawId": "law:replay-idempotent@1",
      "conditionType": "temporal",
      "evaluatorRef": "ag.period-stokes-audit@1"
    }
  ],
  "skeleton": [
    { "simplex": "vertex:order-section",
      "supportAtomRef": "atom:section-order",
      "requiredLawId": "law:order-inventory-gluing@1" }
  ],
  "defectSources": [
    {
      "lawId": "law:order-inventory-gluing@1",
      "coverRef": "cover:order-inventory",
      "chartDefects": [
        { "chart": "ctx:order",
          "defectObservable": { "axis": "cech", "predicate": "sectionValue" } },
        { "chart": "ctx:inventory",
          "defectObservable": { "axis": "cech", "predicate": "sectionValue" } }
      ]
    }
  ],
  "quotientSheafCondition": { "mode": "single-context-theorem" }
}
```

- `laws[]` の意味論は案2 と同一(6 型 enum、closed のみ ideal 化、square-free monomial 生成元、
  名前照合 / edge 宣言 binding)。
- `skeleton`: SAGA 定義5.1 の (E) skeleton(0-単体ごとの support atom と required law)の宣言欄。
  `supportAtomRef` は analyze 時に ArchMap atom id へ、`requiredLawId` は `laws[].lawId` へ解決必須。
  schema 欄は Stage 2 で予約(定義のみ)、**有効化は Stage 3**(§6)。
- `defectSources` / `quotientSheafCondition` は SAGA level E(law equation grounded surface、定義5.1)の
  政策側成分。`defectObservable` は「この law の defect 座標は観測のこの生値である」という
  **chart-local law-defect tie の宣言**であり、defect の値・class・結論は書けない
  (anti-weakening: 結論相当フィールドは schema validation で reject。§5 参照)。
- `quotientSheafCondition.mode`: `single-context-theorem` |
  `assumed`(assumption ledger に `status: assumed` で記録)| `not-selected`(level E 結論は出さない)。
  仮定を暗黙に飲まず、packet の assumptions 区画へ流す入口。
  **`single-context-theorem` は例9.1 regime だが、例9.1 の定理成立(part_10:867-874)は
  context がただ一つの有限モデルという premise に限定される。したがって本 mode の宣言時、
  ArchSig validation は ArchMap の selected context poset が単元(選ばれた context がちょうど 1 つ)で
  あることを検査し、不成立なら fail-closed(validation fail)とする**。移行レポートは
  `assumed` への書き換え(assumption ledger 記録)を authoring 選択肢として提示するが、
  自動格下げ(仮定の暗黙飲み込み)はしない。

(c) `measurement-profile/v2` — 計測手段(独立ファイル化 + 意味論の schema 化):

```json
{
  "schema": "measurement-profile/v2",
  "profileId": "profile:ag-default@2",
  "siteRef": "archmap:/contexts",
  "coverRef": "cover:order-inventory",
  "coefficient": "F2",
  "effCoeff": "finite-linear-algebra@1",
  "resolutionSelector": "taylor@1",
  "domain": "finite-poset-site",
  "zeroPredicate": "rank-zero@1",
  "nonZeroPredicate": "rank-positive@1",
  "certSelector": "finite-certificate@1",
  "verdictDiscipline": "five-valued-structural-verdict@1",
  "finiteBounds": {
    "maxSquareFreeWitnessVariables": 12,
    "maxCoherenceContexts": 12,
    "maxTorWitnessVariables": 12,
    "maxBoundaryResidueVariables": 16,
    "maxLaplacianCells": 16,
    "maxPeriodCycles": 16,
    "maxTransferTargets": 16
  },
  "diagnosticCeiling": "descent"
}
```

- `witnessFamily` は profile から**削除**し law surface へ移す(P4 の解消。
  witness 変数は law equation realization の violation coordinates 側 — 定義11.3 — であり、
  計測手段ではない。theory 整合的な tool 設計選択としての M の細分、§5 参照)。
- `finiteBounds`: 実装定数だった有限上限を profile フィールドに昇格(P3 の解消)。
  第VIII部 定義4.1 finite measurement regime の宣言に対応。
  フィールドは実装定数 7 種(src/ag_measurement.rs:31-37 の
  MAX_SQUARE_FREE_WITNESS_VARIABLES 12 / MAX_COHERENCE_CONTEXTS 12 /
  MAX_TOR_WITNESS_VARIABLES 12 / MAX_BOUNDARY_RESIDUE_VARIABLES 16 /
  MAX_LAPLACIAN_CELLS 16 / MAX_PERIOD_CYCLES 16 / MAX_TRANSFER_TARGETS 16)と
  1 対 1 の対応表で全数定義する(上記概形の 7 フィールド)。
  **registry 側 hard ceiling**: `all_subsets` が 2^n 個の部分集合を実体化する
  (src/ag_measurement.rs:9602。minimal hitting sets も同関数を使う)ため、
  上限は author が自由に引き上げられる安全ヒントではなく資源制約である。
  measurement-profile/v2 validation は registry 所有の hard 上限
  (v0.5.0 では現行定数値を cap とする)を強制し、超過は validation fail とする。
  profile が宣言できるのは cap **以下**への引き下げのみ。
- `diagnosticCeiling`: SAGA の診断階段の**要求上限**を
  `raw-values | boundary-membership | descent | class-transfer | law-grounded` の enum で宣言。
  実際に到達する段は supplied データの充実度で決まり、ArchSig は
  「要求 ceiling ≤ 到達段」なら肯定的結論、届かない段は boundary statement
  (`out_of_selected_vocabulary` 等)として静かに記録する。
  段の定義は SAGA 入力 5 層(saga 調査 §6: B=境界所属生値+無条件否定診断、
  B+faithfulness=肯定的 descent、D=class 転送、E=law-grounded)に対応。
  **law-grounded 段の出力範囲(段定義に明記)**: law 依存の肯定的結論
  (定理7.5 結論1〜3・定理8.1 型)は law-equation witness
  (displayed required laws の充足証人)の供給を前提とする。系11.5(part_3:1812-1819)が
  「消滅と同値なのは law の成立ではなく defect の ideal 所属である」と逆向きを遮断するため、
  ArchSig の計測([d]=0)だけから law 成立は導出できない。witness の入力 slot が
  確保される(§7 未決事項3)までの law-grounded 段は、
  **law 非依存結論(ideal 所属 reading)と、非零 class からの否定的 law 診断
  (系11.5 の許す向き)に限定**し、law 依存肯定結論は出力しない。

(d) `archsig-policy-bundle/v1` — 任意の束ね manifest(CI 用):

```json
{
  "schema": "archsig-policy-bundle/v1",
  "id": "bundle:shop-backend@1",
  "lawPolicyRef": "law_policy.json",
  "lawSurfaceRef": "law_surface.json",
  "measurementProfileRef": "measurement_profile.json",
  "componentFingerprints": {
    "lawPolicy": "sha256:…",
    "lawSurface": "sha256:…",
    "measurementProfile": "sha256:…"
  }
}
```

- **fingerprint の意味論**: sha256 の対象は raw file bytes ではなく **canonical JSON bytes** とする。
  正準化規則: JSON として parse → object キーを辞書順ソート → 区切り最小
  (不要空白なし)で UTF-8 再直列化。整形・キー順・改行コードの差で指紋が変わらないことが、
  「政策は同一のまま cover だけ変更」という CI 判定の成立条件である。
- **計算と検証の責務**: 計算は bundle author(人または CI スクリプト)。
  ArchSig は `archsig policy-bundle --policy-bundle bundle.json` および
  `analyze --policy-bundle` で fingerprint を再計算・照合し、不一致は validation fail とする。
- **依存追加**: hash 実装は自前で書かず `sha2` crate を追加する
  (現行依存は clap / serde / serde_json / walkdir のみ)。

CI での計測間比較は component 単位の fingerprint 一致で「政策は同一・cover だけ変更」を
artifact 水準で言える。SAGA 8.4 / 8.5 が定理水準で確定した「比較可能性はデータ」の示唆を受け、
**比較の前提(どの成分が固定されたか)の明示データ**として実装する tool 設計選択である。
fingerprint は 8.4/8.5 の comparison / refinement data そのものではない(P6 参照。本体は設計次元4)。

**CLI**:

```bash
# 個別指定
archsig analyze \
  --archmap archmap.json \
  --law-policy law_policy.json \
  --law-surface law_surface.json \
  --measurement-profile measurement_profile.json \
  --out-dir .tmp/archsig-analyze

# bundle 指定(CI 推奨形)
archsig analyze --archmap archmap.json --policy-bundle bundle.json --out-dir .tmp/archsig-analyze

# 各 artifact の単独検証
archsig law-policy --law-policy law_policy.json --law-surface law_surface.json
archsig law-surface --law-surface law_surface.json
archsig measurement-profile --measurement-profile measurement_profile.json
archsig policy-bundle --policy-bundle bundle.json
```

既存 `law-policy` サブコマンドの `--input` から `--law-policy` への改名は
**意図的 breaking change** であり、§6 Stage 1 で告知先(commands.md / README / SKILL)と共に扱う。

**ArchMap との責務分割(一括払い哲学との整合)**:

| artifact | 主観の種類 | 書くもの | 書かないもの |
| --- | --- | --- | --- |
| ArchMap v2 | 観測の主観(守る) | 生値のみ(sectionValue / support / cooccurrence、contexts、covers) | 評価語・比較結果・計算済み成果物(現行 R1-R3 のまま不変) |
| law-policy/v2 | 運用判断 | どの law を・どの重さで・どの範囲に・何を根拠に選ぶか | 方程式・witness 変数・計測手段 |
| law-equation-surface/v1 | 制度選択(law universe) | 変数宣言・束縛・forbidden support 生成元・型分類・skeleton・defect tie | 判定式・スコア・重み・結論相当フィールド |
| measurement-profile/v2 | 計測手段選択 | cover・係数・resolution・predicate selector・有限上限・診断上限 | witness 変数・law の内容 |
| ArchSig | 計算(判定の独占) | minimal 化・I_Δ・dual・Q・class・verdict・certificate | 入力の補完・推測・拡張 |

観測者境界は従来どおり ArchMap author + evidence contract に一括。
新設 2 artifact が観測側に課すものは **schema 形状水準では無し**
(archmap/v2 の schema・R1-R3・判定語 hard error は不変。binding は既存の生値語彙への参照)だが、
**authoring 規約水準では Stage 2 の意味論移行がある**
(square-free 系 support atom の役割が「forbidden 生成元の供給」から「共起の観測事実」へ反転する。
§3.2 の対応規則と §6 Stage 2 参照)。ArchSig 内部に法則の補完・fallback は置かない
(law surface に無い law の `ag.*` 評価は fail-closed、現行の profile fail-closed と同型。
law surface を使わない選択は §3.4(a) の表のとおり政策文書の明示 contract であり、
入力欠落を引き金にした挙動分岐ではない)。

**SAGA 接続**: 定理11.4(方程式→係数生成)と定義5.1(grounded surface)への最短経路。
配置の対応は、**本設計が実際に slot を用意した成分に限って**次のとおり:
(E) の方程式面(laws / skeleton / defect source / quotient sheaf condition)が law surface に、
計測選択(cover・係数環・resolution・診断上限)が profile に、
(A) の観測と (B) のうち**観測部分**が ArchMap に配置される。
supplied 層の全体が 3 artifact で尽くされるわけではない:
(B) の repair primitives(C^0・δ^0・supp — 提案された修理であって観測生値ではない)は
観測層に置かず観測層外の新 artifact の管轄(§7 未決事項1)、
gluing data(定理7.3 の前提、part_10:726-731)・(D) 段の supplied H^1 comparison data(定義7.1)・
supplied Čech 係数データ(定義4.2)・law-equation witness(displayed required laws の充足証人)は
本設計に置き場がなく、供給者を §7 未決事項3 で明示的に残す。
これらが供給されるまで、対応する段の law 依存肯定結論は出力しない((c) の diagnosticCeiling 段定義)。
generated 側(境界所属・H^1 class・比較同値・restriction evaluator・law-grounded 結論)は
すべて ArchSig の出力。「結論を supplied certificate として受け取らない」(part_10:52)が
schema の禁止フィールド規則としてそのまま実装できる。

**移行コスト**: 中〜大だが**段階分割可能**(§6)。
**リスク**: artifact 数の増加による authoring 負荷。緩和策は bundle manifest と
authoring SKILL(law surface 用の対例集・良例集)、および小規模利用向けには
`lawSurfaceRef` を持たない政策文書による **v0.4.0 相当 contract の明示選択**(§3.4(a) の表)。
CLI フラグ省略を引き金とする縮退 fallback は設けない(fail-closed 規律と矛盾するため。§8 指摘1)。

---

## 4. 比較表と推奨

| 軸 | 案1 純化 | 案2 方程式一級化 | 案3 統合 | 案4 層化バンドル |
| --- | --- | --- | --- | --- |
| 理論忠実性(定理11.4・原則11.6・原則5.8) | △ 方程式は registry 焼き込みのまま | ○ 方程式面は supplied(defect source 欄なし) | △ 案1 と同じ | ◎ 方程式面 + defect tie + supplied/generated 境界 = artifact 境界 |
| 憲章 C5(selector 性格の保存) | ◎ | ○(LawPolicy が方程式を持つ分、性格が変わる) | ✕ 制度選択と計測手段が混合 | ◎ LawPolicy は selector のまま |
| 誤結論時の責任切り分け(charter:12-14) | ○ | ○ | ✕ 弱化 | ◎ 4 artifact で最も細かい |
| SAGA level E 接続 | ✕ evaluator 追加のみ | △ 単体では届かない(姉妹フィールド増設が前提) | ✕ | ◎ grounded surface の直接の置き場(witness 等の残 slot は §7) |
| 現場記述力(P1/P2) | △ basis のみ改善 | ◎ | △ | ◎ |
| CI 連携(P6、fingerprint 分離) | ○ profile 独立化で部分改善 | △ 単一文書肥大 | ✕ 悪化 | ◎ component fingerprint |
| authoring 負荷 | ◎ 最小 | ○ 1 文書 | ◎ 1 文書 | △ 3 文書(bundle + SKILL + v0.4.0 相当 contract の明示選択で緩和) |
| 移行コスト | 小 | 中〜大 | 中 | 中〜大(段階分割可) |
| 主リスク | 主方針(AG 分析充実)に届かない | DSL 肥大・文書肥大・level E 未達 | 憲章の機能条件を弱める | artifact 数増 |

**推奨: 案4(政策バンドル層化案)**。理由は 3 点。

1. **理論との整合**。SAGA が定理水準で確定した supplied / generated 境界と
   「比較可能性はデータ」(8.4/8.5)を、slot を用意した成分の範囲で
   artifact contract 境界と fingerprint 分離として実装できる。これは他案では書けない性質。
2. **憲章の保存**。LawPolicy の selector 性格・「書かないものリスト」・三層分離の機能条件を
   一切動かさずに、方程式の一級化(G-06 の受け皿)を新しい層として足せる。
   責務線の変更は「law universe の方程式面を registry から独立 artifact へ移す」の一点だけで、
   これは theory 由来(原則11.6: 述語は方程式を決めない)+ tool 設計選択(置き場所)として
   明示的に正当化できる。
3. **段階移行可能**。Stage 1 が案1 と同一作業(掃除 + 対称化)なので、
   案4 を選んでも案1 の作業が無駄にならない(§6)。

案2 は「artifact を増やしたくない」場合の fallback として有効(語彙は案4 と共通)。
案3 は非推奨(責務憲章の機能条件を弱め、P6 を悪化させる)。

---

## 5. 境界規律との整合

- **一括払い哲学(AGENTS.md:65-67)**: 全案で観測者境界は ArchMap author + evidence contract に
  一括のまま。案4 の新 artifact は制度・計測側の前払いを増やすだけで、
  ArchSig 内部に観測ヘッジ・法則補完・fallback を分散させない。
  law surface / profile に関する挙動は次の 3 つに限る:
  (i) 入力契約違反(宣言済み参照の未供給、未解決 lawId 等)は **fail-closed**、
  (ii) 選ばれていない語彙は **boundary statement 付き沈黙**、
  (iii) `lawSurfaceRef` を持たない政策文書は **v0.4.0 相当 contract の明示選択**
  (§3.4(a) の 4 行表)。(iii) は author が schema 水準で宣言する contract であって、
  入力欠落を ArchSig が registry の方程式で埋める補完ではない。補完はどの挙動にも存在しない。
- **anti-weakening(`research/goals/G-aat-quality-surface-06.md` の material premise 規律)**: law-equation-surface/v1 と
  measurement-profile/v2 の schema に、結論相当フィールド
  (verdict / h1Zero / boundaryMembership / nsdepth / minimalForbiddenSupports /
  globalCoherent 等)を**定義しない**。さらに ArchMap R3 と同型の
  `check_law_surface_no_conclusion_shortcuts`(禁止語: nonzero / obstruction / violation /
  mismatch / lawful / certificate 系を lawId・variable 名の語境界 exact match で拒否)を validation に置く。
  これは観測純化 PRD の判定語 hard error の政策文書版であり、
  「定理の結論に現れる構造を supplied certificate として受け取らない」(part_10:52)の実装。
- **判定の主観を観測層に戻さない(purity PRD の却下条件)**: binding は生値語彙への
  参照(名前照合 / edge 宣言)のみで、ArchMap 側の schema・判定語 hard error は変更しない。
  semantic `meaning` の意味読み取り(観測の主観)にも触れない。
  Stage 2 の意味論移行(§3.2)は support atom の**役割**の再解釈であり、
  観測層に判定の主観を持ち込むものではない(atom は引き続き生の共起事実のみを書く)。
- **verdict 規律(第VIII部)**: 五値 verdict・structural / analytic 分離・packet 6 区画は全案不変。
  `diagnosticCeiling` に届かない段は failure ではなく boundary statement
  (`out_of_selected_vocabulary` / `unmeasured_support`)として記録し、主文は到達段の肯定的結論
  (例: `MEASURED_BOUNDARY_MEMBERSHIP` / `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`)に置く。
  law-grounded 段の law 依存肯定結論は law-equation witness の供給を前提とする(§3.4(c)、系11.5)。
- **theory 由来 / tool 選択の区別(charter:52-56 の手本)**:
  - theory 由来: 6 型分類(原則5.8)、closed のみ ideal 化(同)、square-free monomial 生成元と
    minimal 化の ArchSig 帰属(定理5.6C、charter:93-94)、witness 変数が law equation realization の
    violation coordinates であること(定義11.3)、比較可能性が data であること(定理8.4/8.5)、
    quotient sheaf condition の theorem/assumed 二相(例9.1 / 定義5.1)、
    law 依存肯定結論の witness 前提(定理11.4 / 系11.5)。
  - theory 整合的な tool 設計選択: **witness 変数を law 側 artifact に置くこと**
    (第VIII部 定義2.1 は selected witness variables E を measurement profile M の成分として持つ。
    M は law 側データも束ねる包括 profile であり、本設計の artifact 分割は M の細分という選択)、
    artifact を 3 分割すること、bundle manifest と fingerprint 分離(8.4/8.5 の示唆を受けた選択)、
    binding の名前照合 / edge 宣言への制限、`diagnosticCeiling` の段名、finiteBounds の既定値。
- **可視化との接点(参考、詳細は ArchView 設計次元)**: law surface は ArchView に
  「law 方程式パネル」(law ごとの witness 変数・forbidden support 生成元・
  ArchSig が計算した minimal supports と hitting sets の対置)という表示面を与えるが、
  ArchView は表示専用で verdict を生成・昇格しない(guideline.md:14, 36)。
  hitting sets の表示には第VIII部 原則5.3 の boundary
  (hitting set は combinatorial repair target であって repair semantics ではない)を併記する。

---

## 6. 移行とリスク

**v0.5.0 の版境界(受け入れ範囲の宣言)**:
v0.5.0 で出荷するのは **Stage 1 + Stage 2 の全部、および Stage 3 の入口 evaluator のみ**
(complete support regime + single-context quotient sheaf theorem regime)。
`skeleton` / `defectSources` / `quotientSheafCondition` / `diagnosticCeiling` の schema 欄は
Stage 2 で予約(定義と validation のみ。既定は `not-selected` 相当で無効)し、有効化は Stage 3。
repair primitives の供給 artifact・comparison data 本体・law-equation witness slot(§7)は後続版。
PRD 化時の acceptance criteria は Stage 単位で切る。

**段階移行計画**(案4 前提。各 Stage が独立に着地可能):

- **Stage 1(= 案1 相当の掃除)**: `law-policy/v2` 新設(distanceProfileRef / pack 削除、
  basisLedger 新設、`lawSurfaceRef` は未使用の任意フィールドとして予約)、
  `measurement-profile/v2` の独立ファイル化と finiteBounds 昇格(7 定数対応表 + registry hard cap)、
  registry から solid/domain 系と判定語 predicate manifest(`legacy-coherence-token` 等)を除去、
  `witness_violation_support_refs` 残置コード削除。v1 経路削除(設計次元1)と同一 PR 群で実施。
  **schema catalog**: `src/schema_catalog.rs` に law-policy/v2・measurement-profile/v2 を登録し、
  lock fixture `tests/fixtures/minimal/schema_version_catalog.json` を改訂。
  **CLI breaking change**: `law-policy` サブコマンドの `--input` → `--law-policy` 改名と
  `--measurement-profile` 追加を意図的 breaking change として、
  `tools/archsig/docs/commands.md`・`tools/archsig/README.md`・関連 SKILL を同一 PR で改訂
  (docs/tool/guideline.md の CLI 変更規律)。
- **Stage 2(方程式一級化)**: `law-equation-surface/v1` と `archsig-policy-bundle/v1` を新設し
  schema catalog / lock fixture に登録。`sha2` 依存追加と canonical JSON fingerprint 実装。
  既存 AG evaluator の再編は **P1 の二経路を別々に移行する**:
  (i) square-free / tor 系 — forbidden 生成元の供給を ArchMap 生 support atom から
  law surface 宣言(Forb)へ移し、support atom を「共起の観測事実」へ再解釈する
  (§3.2 の意味論移行。ArchMap authoring 規約・archmap-creater SKILL・fixture 改訂を含む)。
  (ii) cech / section-factorization 系 — evaluator 焼き込みの law 内容を
  「law surface 宣言 → 実行計画」駆動へ再編(edge 宣言 binding の解決を含む)。
  witnessFamily を profile から law surface へ移動。fixture・golden corpus・SKILL 改訂。
  law-policy/v2 の条件化解決規則(§3.4(a) の 4 行表)を validation に実装。
- **Stage 3(SAGA level E 入口)**: `skeleton` / `defectSources` / `quotientSheafCondition` /
  `diagnosticCeiling` を有効化し、SAGA 系 evaluator(境界所属 → descent → class 転送 →
  law-grounded)を diagnosticCeiling の階段に沿って実装。最初の実装入口は
  complete support regime(定理3.5: faithfulness 供給不要)と
  single-context quotient sheaf theorem regime(例9.1。単元 context poset の validation 検査付き、
  §3.4(b))。law-grounded 段は witness slot 確保まで law 非依存結論と否定的 law 診断に限定(§3.4(c))。

**移行ツール**: `archsig migrate law-policy --from v1 --law-policy old.json --out-dir migrated/`
(embedded profile の切り出し、distanceProfileRef の除去報告、witnessFamily の law surface 移設案の生成)。
機械変換できない部分(forbidden support 生成元の宣言)は移行レポートに
authoring タスクとして列挙する(結論の推測はしない)。

**リスクと緩和**:

| リスク | 緩和 |
| --- | --- |
| DSL 肥大(v0 の轍) | 3 制限(closed のみ ideal 化 / square-free monomial のみ / binding は名前照合・edge 宣言のみ)を deny_unknown_fields + validation で強制。重み・スコア・circuit は将来も schema に足さないと設計文書に明記 |
| artifact 数増による authoring 負荷 | bundle manifest、law surface authoring SKILL(良悪対例集)、`lawSurfaceRef` を持たない政策文書による v0.4.0 相当 contract の明示選択(§3.4(a)。CLI 省略 fallback ではない) |
| Stage 2 の atom 意味論移行による ArchMap authoring drift | §3.2 の対応規則(名前照合 / edge 宣言)を law surface validation・archmap-creater SKILL・fixture の三点で同一規則として固定し、Stage 2 の同一 PR 群で移行 |
| binding 語彙と ArchMap SKILL の drift | binding で参照可能な axis/predicate 語彙を `aat-atom-vocabulary/v1` 側の manifest として一元化し、ArchMap SKILL(設計次元2)と law surface validation が同一 manifest を参照 |
| profile 意味論の実装内解釈が残る | measurement-profile/v2 の各フィールドに第VIII部 定義2.1 の対応語(site X_M / cover U_M / k_M / EffCoeff_M / Dom_M / Zero_M / Cert_M / Verdict_M)と定義4.1(finiteBounds の 7 上限)を docs/tool/law_policy.md 改訂版で対応表化し、enum 値を registry manifest で検証 |
| finiteBounds の引き上げによる CI 資源破綻 | registry 所有の hard cap(現行 7 定数値)を validation で強制。profile は cap 以下への引き下げのみ宣言可(§3.4(c)) |
| 統合 e2e の破壊 | Stage ごとに golden fixture(擬円周 H^1、hitting sets {q}/{p,r}、Tor_1 非零、F_2 circle nerve)の executable lock を先に移植してから経路を切り替える |

---

## 7. 未決事項

1. **repair primitives / semantic projection の供給 artifact の形状**: まず境界を固定する —
   **repair primitives(C^0・δ^0・supp)は「提案された修理」という処方的・反実仮想的 supplied データであり、
   観測ではないので ArchMap には置かない**(責務憲章の観測層規律)。
   割り当て先は観測層外の新 artifact(`repair-proposal/v1` 等)とする。
   ArchMap 拡張が選択肢になるのは**観測成分に限る**: 二粒度 atom(Λ/K)、
   projection 辺(semantic projection π の観測部分)、faithfulness data の観測部分。
   この境界(観測層に処方は置かない)は本設計で確定し、未決なのは
   repair-proposal 系 artifact の具体形状・供給 workflow のみ
   (SAGA ワークフロー設計 = 別次元と共同で決める)。
   本設計は law surface / profile 側の受け口(diagnosticCeiling の段)だけを確保した。
2. **comparison data / refinement data の artifact 形状**: CI の計測間比較(8.4/8.5)と
   版間差分の比較は出力 artifact 再設計(設計次元4)の管轄。本設計からの要求は
   「policy-bundle の componentFingerprints を比較 artifact が参照できること」のみ。
3. **SAGA supplied データの残る供給者**: 本設計の 3 artifact に置き場がない supplied 成分 —
   gluing data(定理7.3 の前提、part_10:726-731)、(D) 段の supplied H^1 comparison data(定義7.1)、
   supplied Čech 係数データ(定義4.2)、law-equation witness
   (displayed required laws の充足証人。law 依存肯定結論の前提、系11.5)— の供給 artifact と
   validation 形状。各 slot が確保されるまで、対応する段の law 依存肯定結論は出力しない
   (§3.4(c) の段定義)。
4. **basisLedger の存在検査の深さ**: path 解決検査(ファイル実在)を default off の
   `--check-basis-paths` にするか、常時検査にするか。evidence contract の宣言主義
   (内容の意味検証はしない)とは独立の論点。
5. **pack 機構の将来**: solid pack 廃止後、AG 系の定型 law 束(例: 「bounded-context 標準束」)を
   pack として復活させるか。Stage 2 の law surface 良例集が貯まってから判断。
6. **descent / temporal / stacky 型の evaluator メニュー**: 第IX部 temporal は
   FieldSig 側スコープの可能性が高い。law surface の `conditionType: temporal` は
   宣言だけ許して evaluator を ArchSig に置かない(沈黙)選択もある。
7. **conormal 係数(I_U/I_U², G-04 の入口)**: 理論側の open question。
   schema には拡張点(profile の coefficient enum)だけ残し、v0.5.0 では実装しない。

---

## 8. 査読対応

査読指摘 17 件の採否。全件について引用元(Lean `LawEquationDefectSource` の supplied 成分と
evaluator 定理の `DisplayedRequiredLawsHoldOn` 前提、part_8 定義2.1 / 定理5.2、part_3 定義5.6B / 系11.5、
part_10 例9.1、fixture の atom 形状、`square_free_generators` / `square_free_atom_variables` /
`all_subsets`、有限上限定数 7 種)を一次ファイルで確認した上で判断した。

| # | 区分 | 採否 | 対応 |
| --- | --- | --- | --- |
| 1 | boundary/major | **採用** | 縮退モードを「CLI フラグ省略 fallback」から「政策文書の明示 contract 選択」に再設計。§3.4(a) に lawSurfaceRef 有無 × --law-surface 有無の 4 行表を置き、宣言済み参照の未供給と宣言なし供給は fail-closed、v0.4.0 相当 contract は lawSurfaceRef を持たない文書の schema 水準宣言に限定。§3.4 リスク・§5(i)-(iii)・§6 リスク表を整合させた。査読の提案 (1)(2)(3) をそのまま採った形 |
| 2 | boundary/minor | **採用** | §7 未決事項1 で境界を先に固定: repair primitives は観測層に置かず観測層外の新 artifact(repair-proposal/v1 等)へ。ArchMap 拡張の選択肢は観測成分(二粒度 atom・projection 辺・faithfulness の観測部分)に限定。未決は artifact 形状と workflow のみ |
| 3 | boundary/minor | **採用** | §3.2 binding 説明を「観測上(ArchMap 生値上)での生起」に相対化し、source extraction の健全性を主張しない旨(第VIII部 原則2.2)を明記 |
| 4 | theory/major | **採用** | §3.2 の自動生成リストを定理5.6C / 第VIII部 定理5.2 の範囲(I_Ob・minimal supports・hitting sets・Q)に限定。defect class / restriction evaluator は defect source(Lean: defect / lawSupport / holds_defect_mem)供給 + DisplayedRequiredLawsHoldOn 前提の条件付きと明記。案2 リスク (c) に「単体では level E に届かない」を追加し、§4 比較表の案2 評価も △ に修正 |
| 5 | theory/major | **採用** | §3.4 SAGA 接続を「slot を用意した成分に限る」対応へ書き直し。(B) の repair primitives を ArchMap 配置から除外。gluing data・(D) 段 comparison data・supplied Čech 係数データ・law-equation witness の供給者を §7 未決事項3 に新設。diagnosticCeiling の law-grounded 段定義に「witness 供給まで law 依存肯定結論は出力しない(系11.5 の逆向き遮断)」を明記 |
| 6 | theory/minor | **採用** | P4 と §5 の citation を定義5.6B から定義11.3(violation coordinates)へ差し替え、「witness 変数を law 側 artifact に置くこと」を theory 由来から theory 整合的な tool 設計選択へ格下げ。part_8 定義2.1 が E を profile M の成分に持つこと(artifact 分割 = M の細分)を両所に注記 |
| 7 | theory/minor | **採用** | 「第VIII部 定理5.2」と part を明記(part_3 には定理5.2 が存在しないことを確認)。hitting sets の出力・表示箇所(§3.2・§5 可視化)に第VIII部 原則5.3 の boundary を併記 |
| 8 | theory/minor | **採用** | §3.4(b) quotientSheafCondition に「single-context-theorem 宣言時は selected context poset の単元性を validation で検査、不成立は fail-closed。assumed への書き換えは authoring 選択肢として提示、自動格下げはしない」を明記 |
| 9 | theory/minor | **採用**(skeleton 欄追加の側) | law-equation-surface/v1 に `skeleton` 欄(0-単体ごとの supportAtomRef + requiredLawId)を追加し、Stage 2 で予約・Stage 3 で有効化として §6 に配線。配置主張(§3.4 SAGA 接続)と schema・移行計画が一致した |
| 10 | theory/minor | **採用** | P6 を「8.4/8.5 は比較可能性が data であることを定理で確定。fingerprint 分離はその示唆を受けた tool 設計選択」へ帰属を弱め、「fingerprint は固定成分の記録であって comparison data ではない。comparison data 本体と版間差分(射程外)は設計次元4」を P6・§3.4(d)・§7 に明記 |
| 11 | feasibility/major | **採用** | §3.2 に「binding と NormalizedAtomV2 の対応規則」を新設: square-free 系は変数名の同一性照合(subject/object のカンマ区切りリスト要素。fixture の実形状に一致)、cech 系は edge 宣言(restricts_to 由来の導出 1-skeleton へ解決。overlap:* 語彙は存在しないため廃止)。案2 / 案4 の例示 JSON を実形状に合わせて修正。Stage 2 の意味論反転(観測 support = forbidden 生成元 → 共起の観測事実)を明示し、「観測に何も要求を追加しない」claim を「schema 形状水準では不変、authoring 規約水準では改訂が必要」に修正。§6 Stage 2 と §5・リスク表に配線 |
| 12 | feasibility/major | **採用**(条件化の側、v3 版上げは不採用) | policies[].law の解決規則を lawSurfaceRef の有無で条件化(§3.4(a) の 4 行表)。Stage 1 の lawSurfaceRef なし文書は Stage 2 以降も同一 schema 文字列のまま有効で、無告知 fail が生じないため版上げ不要と判断。縮退の発動条件は 4 通り全てを表で確定(指摘1 と一体で解決) |
| 13 | feasibility/minor | **採用** | finiteBounds を実装定数 7 種と 1 対 1 の対応表に拡張(schema 概形も 7 フィールド化)。registry 所有 hard cap(現行定数値)を validation で強制し、profile は cap 以下への引き下げのみ可と明記(all_subsets の 2^n 実体化を根拠として記載)。§6 リスク表に行を追加 |
| 14 | feasibility/minor | **採用** | §3.4(d) に fingerprint の正準化規則(canonical JSON: キー辞書順・最小区切り・UTF-8)、計算者(bundle author)と検証者(archsig policy-bundle / analyze --policy-bundle が再計算・照合、不一致 fail)、依存方針(sha2 crate 追加、自前実装しない)を明記 |
| 15 | feasibility/minor | **採用** | §6 Stage 1 / Stage 2 に schema_catalog.rs 登録と schema_version_catalog.json lock fixture 改訂を明記。law-policy サブコマンドの --input → --law-policy 改名を意図的 breaking change として告知先(commands.md / README / SKILL)と共に Stage 1 に列挙(§3.4 CLI 節にも注記) |
| 16 | feasibility/minor | **採用** | P1 を「方程式データの供給経路は evaluator 焼き込み(cech 系)と ArchMap 混入(square-free/tor 系)の二形態に分裂」と書き直し(square_free_generators の観測 support → I_Ob 生成元直結を証拠に追加)。§6 Stage 2 の移行対象を経路別 (i)(ii) に特定 |
| 17 | feasibility/minor | **採用** | §6 冒頭に版境界を宣言: v0.5.0 = Stage 1 + Stage 2 + Stage 3 入口 evaluator のみ(complete support regime / single-context theorem regime)。level E 残 slot は後続版。acceptance criteria は Stage 単位 |

不採用(部分不採用を含む)としたのは指摘12 の「law-policy/v3 への版上げ」選択肢のみで、
同指摘が併記するもう一方の案(条件化解決規則)で目的(無告知の意味変更防止)が達成でき、
版数の増殖を避けられるため。他 16 件は一次ファイルの確認結果と矛盾せず、全面採用した。
