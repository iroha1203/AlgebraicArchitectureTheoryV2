# relationComplexity 設計

Lean status: `empirical hypothesis` / design decision.

Issue [#36](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/36) の設計判断として、`relationComplexity` はまず Lean core の定理対象ではなく、extractor tooling が有限な測定 universe 上で計算する empirical metric として扱う。

## 決定

`relationComplexity` は状態遷移代数層の複雑さを表す Signature v1 empirical extension の候補軸である。

初期段階では次のどれとして扱うかを分ける。

| レイヤー | 扱い | Lean status |
| --- | --- | --- |
| Lean proof | 導入しない。状態遷移設計と運用リスクの相関は全称定理として主張しない。 | `empirical hypothesis` |
| executable metric | extractor が出力する有限測定データ上の計算として定義する。 | tooling design |
| empirical analysis | 障害復旧コスト、補償失敗、整合性違反との関係を検証する。 | `empirical hypothesis` |

将来、状態遷移構造を Lean に導入する場合も、最初から `ArchitectureSignature` v0/v1 core に混ぜない。小さな `TransitionSystem` 風の構造と、その上の executable metric を別モジュールで育て、graph-level facts とは bridge theorem で接続する。

## 初期 metric

初期の観測レコードは、単一の `Nat` ではなく構成要素を保持する。

```text
RelationComplexityObservation =
  constraints              : Nat
  compensations            : Nat
  projections              : Nat
  failureTransitions       : Nat
  idempotencyRequirements  : Nat
```

派生値として、初期の `relationComplexity` は次で計算する。

```text
relationComplexity =
  constraints
  + compensations
  + projections
  + failureTransitions
  + idempotencyRequirements
```

ただし、研究上の解釈では常に構成要素ベクトルを残す。集約値だけで Event Sourcing / Saga / CRUD の優劣を決めない。

各構成要素の意味は次の通り。

| 要素 | 数える対象 | リスクの読み |
| --- | --- | --- |
| `constraints` | 一意性、順序、状態不変条件、相互排他などの明示制約 | 変更時に守るべき関係式の多さ |
| `compensations` | Saga step の補償処理、手動復旧操作、取消 API | 回復経路の分岐と失敗可能性 |
| `projections` | event log から read model / view / cache を作る投影 | 派生状態の同期・再構築コスト |
| `failureTransitions` | retry, timeout, dead-letter, rollback, partial failure state | 障害時の状態空間の広がり |
| `idempotencyRequirements` | 重複実行を許すための key, guard, dedup rule | 再試行安全性を保つための追加制約 |

## Event Sourcing / Saga / CRUD

この軸は、状態遷移設計の不変量とリスクを分けて見るために使う。

| 設計 | 保証する不変量 | 増えやすい構成要素 | 注意 |
| --- | --- | --- | --- |
| Event Sourcing | 履歴再構成性、監査可能性 | `projections`, `idempotencyRequirements`, `constraints` | 基盤ログは自由モノイドに近いが、派生 read model は projection と順序制約を持つ。 |
| Saga | 局所回復性、長い transaction の分割 | `compensations`, `failureTransitions`, `idempotencyRequirements` | 補償射は一般に逆射ではなく、許容状態へ戻す弱い回復構造である。 |
| CRUD | 操作単純性、直接更新 | `constraints` | 履歴喪失により `projections` は小さく見えるが、監査・復旧の情報を失う可能性がある。 |

したがって、`relationComplexity` が高い設計を単純に悪い設計とは呼ばない。履歴再構成性や局所回復性を得るために複雑度を引き受けている場合があるため、Signature は多軸診断として読む。

## 測定方法

extractor tooling は、リポジトリごとに次を入力として `RelationComplexityObservation` を作る。

- application service / workflow / saga orchestrator の状態遷移定義
- event handler, projection updater, read model builder
- retry / timeout / dead-letter / rollback / compensation の実装箇所
- idempotency key, dedup table, exactly-once 風の guard
- schema constraint, validation rule, domain invariant

最初の pilot study では、完全自動抽出を目標にしない。静的抽出で候補を出し、人手レビューで false positive / false negative を記録する。

### JSON schema

`RelationComplexityObservation` は、まず workflow 単位の観測レコードとして保存する。
repository-level の `relationComplexity` は、対象期間・対象 commit・対象 rule set を固定した
うえで workflow-level observation を集約した派生値である。

最小 schema:

```json
{
  "schemaVersion": "relation-complexity-observation/v0",
  "repository": "owner/name",
  "revision": "git-sha",
  "measurementUniverse": {
    "root": ".",
    "languages": ["example-language"],
    "frameworks": ["example-framework"],
    "ruleSetVersion": "relation-complexity-rules/v0"
  },
  "workflow": {
    "id": "checkout-payment",
    "name": "Checkout payment",
    "component": "Billing",
    "entrypoints": ["src/billing/checkout.example"]
  },
  "counts": {
    "constraints": 0,
    "compensations": 0,
    "projections": 0,
    "failureTransitions": 0,
    "idempotencyRequirements": 0
  },
  "relationComplexity": 0,
  "evidence": [
    {
      "id": "evidence-1",
      "path": "src/billing/checkout.example",
      "symbol": "CheckoutWorkflow",
      "line": 42,
      "tags": ["constraints"],
      "ownership": "application-owned",
      "reviewStatus": "candidate",
      "notes": "domain invariant candidate"
    }
  ],
  "excludedEvidence": [
    {
      "path": "src/framework/generated.example",
      "reason": "framework-generated"
    }
  ]
}
```

`counts` は `evidence.tags` から再計算できる値として扱う。保存する場合も、
`evidence` と `ruleSetVersion` を source of truth とし、`relationComplexity` は
`counts` の合計として再計算可能にする。

### counting unit

counting unit は次の階層に分ける。

| unit | 役割 | 集計規約 |
| --- | --- | --- |
| evidence item | 実装上の 1 箇所。file path, symbol, line range, rule hit を持つ。 | 同じ rule hit を同じ workflow 内で二重に数えない。 |
| workflow observation | 1 つの user-visible workflow, saga, command handler, batch job, projection pipeline。 | 初期分析の基本単位。 |
| component aggregate | 同じ component に属する workflow observation の集約。 | component 間比較に使う補助値。 |
| repository aggregate | 対象 repository / revision / rule set 全体の集約。 | Signature empirical extension の候補値として使う。 |

初期 pilot では workflow observation を主単位にする。component aggregate と repository
aggregate は派生値であり、workflow の切り方や component mapping が変われば再計算する。

### 重複タグ方針

1 つの evidence item が複数の構成要素に該当する場合は、`tags` に複数値を持たせる。
例えば timeout 付きの補償処理は `compensations` と `failureTransitions` の両方に
タグ付けしてよい。

重複の扱い:

- 同じ evidence item は、同じ tag について workflow 内で 1 回だけ数える。
- 同じ evidence item が複数 tag を持つ場合、各 tag の count に 1 ずつ寄与する。
- 複数 workflow から同じ実装箇所を共有している場合は、workflow ごとに evidence を持つ。
  ただし repository aggregate では `evidence.id` または `(path, symbol, tag)` による
  dedup view を別途作り、共有実装の過大評価を感度分析で確認する。
- `relationComplexity` は tag ごとの count の合計であり、distinct evidence item 数ではない。

この方針により、状態遷移設計の多面的な責務を保持する。単一箇所が複数の責務を持つこと自体が
複雑さの候補であるため、初期 metric では tag ごとの寄与を落とさない。

### framework-generated behavior

framework-generated behavior と application-owned behavior は `ownership` で区別する。

| ownership | 扱い |
| --- | --- |
| `application-owned` | アプリケーションコード、設定、明示的 workflow 定義。初期 metric に含める。 |
| `application-configured` | framework 機能だが、retry, timeout, projection, compensation などをアプリケーションが明示設定している。初期 metric に含める候補とし、reviewStatus で確認する。 |
| `framework-generated` | framework が暗黙に生成する処理。アプリケーション設計上の責務として扱わず、初期 metric から除外する。 |
| `unknown` | 自動抽出では判定できない候補。主要分析では欠損または review 待ちとして扱う。 |

framework の既定挙動は、アプリケーションが明示的に policy / annotation / configuration で
選んでいる場合だけ `application-configured` として数える。単に framework に存在する機能は
`framework-generated` として除外し、除外理由を `excludedEvidence` に残す。

## 除外条件

次は初期 metric から除外する。

- コメントだけに現れる設計意図
- 実行経路から到達できない dead code
- テスト専用の fake / fixture
- framework が内部で生成する retry や projection のうち、アプリケーション設計上の責務として扱わないもの
- 単なる CRUD field validation で、状態遷移の分岐や復旧経路を増やさないもの

除外理由は分析データに残す。将来の extractor 改善では、除外条件ごとの誤差を確認する。

## 前提の分離

extractor tooling 側の前提:

- 測定 universe は対象リポジトリ、期間、対象 language / framework で明示する。
- 抽出できるのは観測可能な実装上の候補であり、設計意図の完全性は主張しない。
- event, saga, projection, compensation の検出ルールは versioned rule set として管理する。

data analysis 側の前提:

- `relationComplexity` と障害・変更コストの関係は相関仮説として扱う。
- リポジトリ規模、チーム規模、変更量、期間を交絡要因として記録する。
- 集約値だけでなく構成要素別の係数や分布を見る。

## 正規化候補

初期 metric は raw count を保存する。規模補正は pilot study の将来課題として、
raw count とは別の派生指標に分ける。

候補:

- `relationComplexityPerWorkflow`: repository aggregate を workflow 数で割る。
- `relationComplexityPerComponent`: component aggregate を component 数または対象 component 数で割る。
- `relationComplexityPerKLOC`: 対象 measurement universe の KLOC で割る。
- `relationComplexityPerChange`: 対象期間の PR 数または変更 component 数で割る。
- component vector normalization: `constraints`, `compensations`, `projections`,
  `failureTransitions`, `idempotencyRequirements` を別々に正規化する。

これらは repository 間比較のための補助指標であり、raw `RelationComplexityObservation`
を置き換えない。初期分析では raw count、構成要素ベクトル、欠損・除外 metadata を残したまま、
正規化指標の感度を見る。

## 後続 Issue 候補

- extractor rule set v0 は [#124](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/124)
  で `sig0-extractor relation-complexity --input ...` として実装した。候補 evidence
  から workflow-level `RelationComplexityObservation` JSON を出力し、counts と
  `relationComplexity` は counted evidence tags から再計算可能にしている。
- Event Sourcing / Saga / CRUD を含む pilot baseline は
  [#154](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/154)
  で
  [relation_complexity_pilot](../empirical/relation_complexity_pilot/README.md)
  に追加した。手動ラベル、extractor output、差分 0 の確認、除外 evidence、
  unsupported framework probe を記録している。
- 状態遷移構造を Lean に入れるかどうかを、pilot の後に改めて判断する。
