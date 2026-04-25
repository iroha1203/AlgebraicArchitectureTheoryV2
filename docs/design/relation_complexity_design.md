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

## 後続 Issue 候補

- `RelationComplexityObservation` の JSON schema と extractor rule set を定義する。
- Event Sourcing / Saga / CRUD の pilot repository を選び、手動ラベルつき baseline dataset を作る。
- 状態遷移構造を Lean に入れるかどうかを、pilot の後に改めて判断する。
