# PRD: Algebraic Signature Extension for ArchSig

## 1. プロダクト概要

### 仮称

**AlgSig v0: Algebraic Architecture Signature Extension**

### 一文要約

既存の依存グラフ中心の ArchSig に、**設計原則が要求する代数法則・状態遷移法則・履歴再構成性・副作用境界・表現変換の健全性**を測る `algebraic-signature-v0` を追加する。

### 背景

研究全体のゴールでは、ソフトウェアアーキテクチャを「依存・抽象・観測・状態遷移・実行時依存の複数グラフまたは代数構造」として表現し、不変量の破れを `ArchitectureSignature` として定量評価することが掲げられています。さらに、目標は単一スコアではなく、分解可能性、置換可能性、履歴再構成性、障害局所性、変更容易性など、どの不変量が破れているかを多軸で診断することです。([GitHub][2])

現行の ArchSig は、依存グラフ由来の `hasCycle`, `sccMaxSize`, `maxDepth`, `fanoutRisk`, boundary / abstraction violation などを扱えます。また、`Relation Complexity` では `constraints`, `compensations`, `projections`, `failureTransitions`, `idempotencyRequirements` をcandidate evidenceから数える足場があります。([GitHub][1])

今回の拡張では、この `Relation Complexity` を単なる数え上げから一段進めて、

> 補償が本当に準逆射として振る舞うか
> retryable operation が本当に冪等か
> event replay がモノイド準同型として振る舞うか
> DTO / Entity / Event の変換が roundtrip law を守るか
> domain が禁止された effect を発生させていないか

を測る。

---

# 2. 解決したい課題

## 現状の課題

既存の依存グラフ方式では、次のような診断は難しい。

### 依存は綺麗だが、操作法則が壊れている

例:

```text
CancelOrder は retryable と宣言されているが、
2回呼ぶと OrderCancelled event が2回出る。
```

依存グラフでは変化なしでも、アーキテクチャ上は重大な冪等性違反。

### 依存は増えていないが、Event Sourcing の再構成性が壊れている

例:

```text
project(xs ++ ys) と projectFrom(project(xs), ys) が一致しない。
```

これは依存関係ではなく、履歴再構成性の破れ。

### 補償処理は存在するが、補償射としては弱い

例:

```text
reservePayment の後に releasePayment を実行しても、
外部観測上は元状態に戻らない。
```

現行の `relationComplexity` では「compensation がある」と数えられても、それが代数的に妥当かは評価できない。

### import graph は綺麗だが、effect が漏れている

例:

```text
Domain layer は DB module を import していないが、
Repository.write effect を直接発生させている。
```

これは依存辺ではなく、effect signature の漏洩。

---

# 3. プロダクトゴール

## Goal 1: 依存グラフとは別軸の `AlgebraicArchitectureSignature` を追加する

既存の `archsig-sig0-v0` を壊さず、別artifactとして以下を出力する。

```text
algebraic-signature-v0
```

これは、既存の `signature-diff-report-v0` や `empirical-signature-dataset-v0` に接続できるようにする。

---

## Goal 2: 「法則違反」「法則未評価」「法則未宣言」を分ける

既存CLIの強みである、

```text
測定済み 0 ≠ 未評価
```

を代数指標にも継承する。

MVPでは `lawResults[].status` を次の3状態に固定する。

| 状態           | 意味                                                      |
| ------------ | ------------------------------------------------------- |
| `satisfied`  | 宣言済みlawに対して、少なくとも1つの conclusive satisfied evidence がある |
| `violated`   | 宣言済みlawに対して、少なくとも1つの conclusive violated evidence / witness / counterexample がある |
| `unmeasured` | law は宣言されているが、conclusive evidence がない |

`undeclared` は `lawResults[].status` に入れない。law registry に存在しない `lawId` への evidence は、`danglingEvidence`, `excludedEvidence`, validation check, candidate law state として扱う。

`law-evidence/v0` の `evidence[].status` は次の3状態に固定する。

```text
satisfied
violated
inconclusive
```

`failed`, `passed`, `error` は evidence status には使わず、test runner の実行結果として `runnerResult` などの payload に入れる。

同一 law に複数 evidence がある場合は、以下で解決する。

```text
1. violated evidence が1つ以上ある
   -> lawResult.status = violated

2. violated evidence がなく、satisfied evidence が1つ以上ある
   -> lawResult.status = satisfied

3. satisfied / violated がなく、inconclusive evidenceのみ、またはevidenceなし
   -> lawResult.status = unmeasured
```

`satisfied` と `violated` が同一 law に混在する場合、集計上は保守的に `violated` とし、validation report に `conflictingEvidence` warning を出す。

これにより、AI reviewer が、

```text
violatedLawCount = 0
```

だけを見て「安全」と誤読するのを防ぐ。

---

## Goal 3: Leanで「指標の意味」を保証し、実コード診断はCLIが行う

Lean側では、任意の実コードが正しいことを証明しない。
代わりに、以下を証明する。

```text
この法則が成り立つなら、どの不変量が保存されるか。
この counterexample が存在するなら、その law は成り立たない。
この metric は、宣言された law universe に対して何を数えているか。
```

CLI側では、JSON evidence、property test結果、replay check結果、手動candidate evidenceを読み、実コード上の観測値を集計する。

---

# 4. 非ゴール

この拡張でやらないこと。

1. **任意のアプリケーションコードから全ての代数法則を自動推論すること**
   MVPでは law registry と evidence JSON を明示入力にする。

2. **Leanで実アプリ全体の正しさを証明すること**
   Leanは理論中核と指標意味論の証明に限定する。

3. **単一スコアでアーキテクチャ品質を判定すること**
   研究目標と同様、多軸Signatureとして扱う。研究目標でも単一スコアではなく、どの軸が悪化したか、どの不変量が破れているかを説明する方針が示されています。([GitHub][2])

4. **依存グラフ指標を置き換えること**
   既存の `hasCycle`, `fanoutRisk`, `boundaryViolationCount` などは維持し、AlgSigは別軸として追加する。

---

# 5. 対象ユーザー

## Primary

### 研究者

代数的アーキテクチャ論の仮説を、実コードベース上のデータで検証したい。

### アーキテクト / Tech Lead

PR単位で、

```text
この変更はどの不変量を壊したか？
依存関係は綺麗でも、設計法則は壊れていないか？
```

を確認したい。

### AI code review agent

diff report を読み、

```text
このPRは fanout は増やしていないが、retryable command の冪等性を破っている
```

のようなレビューコメントを出したい。

---

# 6. 追加する主要指標

## 6.1 Core Law Metrics

まず全ての代数指標に共通する基本軸。

| 指標                    |          型 | 意味                                           |
| --------------------- | ---------: | -------------------------------------------- |
| `declaredLawCount`    |        int | law registry に宣言された distinct law ID 数                    |
| `requiredLawCount`    |        int | `required=true` の distinct law ID 数                        |
| `satisfiedLawCount`   |        int | required law のうち `status=satisfied` の law ID 数          |
| `violatedLawCount`    |        int | required law のうち `status=violated` の law ID 数    |
| `unmeasuredLawCount`  |        int | required law のうち `status=unmeasured` の law ID 数               |
| `lawDebt`             |        int | MVPでは `unmeasuredLawCount` の派生値 |
| `lawCoverageRatio`    | float/null | required law のうち評価済みの割合                      |
| `manualEvidenceRatio` | float/null | conclusive evidence のうち manual attestation 由来の割合        |
| `counterexampleCount` |        int | validかつdeclared lawに紐づく concrete counterexample / witness の件数                  |

MVPでは `satisfiedLawCount`, `violatedLawCount`, `unmeasuredLawCount` は law ID 単位で数える。`counterexampleCount` は witness 単位であり、`violatedLawCount` と一致しなくてよい。

また、MVP v0では `lawDebt = unmeasuredLawCount` である。将来版では `unsupported`, `invalid`, `waived=false` などを含める余地を残すが、`algebraic-signature-v0` では独立指標として読まない。

`lawCoverageRatio` は次で定義する。

```text
lawCoverageRatio =
  (satisfiedLawCount + violatedLawCount) / requiredLawCount
```

`requiredLawCount = 0` の場合、`lawCoverageRatio` は `null` とし、`metricStatus.lawCoverageRatio.measured = false` にする。`1.0` にはしない。

### 診断例

```text
violatedLawCount = 0
unmeasuredLawCount = 12
```

この場合、診断は「違反なし」ではなく、

```text
宣言された law の多くが未評価であり、lawfulness は判断不能
```

になる。

### kind別 violation metric の `metricStatus`

`idempotencyViolationCount`, `compensationDefectCount`, `replayHomomorphismDefect`, `roundtripLossCount` などの kind別 violation metric は、MVPでは required law ID 単位で数える。

ただし、値だけで安全とは読まない。対象 kind の required law が存在し、その一部が `unmeasured` の場合、violation count が0でも `metricStatus.<axis>.measured = false` にする。

例:

```json
{
  "idempotencyViolationCount": 0,
  "metricStatus": {
    "idempotencyViolationCount": {
      "measured": false,
      "source": "law-evidence:v0",
      "reason": "2 required idempotency laws are unmeasured"
    }
  }
}
```

対象 kind の required law が1つも宣言されていない場合は、集計対象が空であることを明示した上で `measured = true` とする。

```json
{
  "idempotencyViolationCount": 0,
  "metricStatus": {
    "idempotencyViolationCount": {
      "measured": true,
      "source": "law-registry:no-required-laws-for-kind",
      "reason": "no required idempotency laws declared; value is vacuous zero"
    }
  }
}
```

---

## 6.2 Idempotency Metrics

対象:

```text
retryable command
message handler
webhook handler
cancel / close / deactivate 系 operation
```

### 追加指標

| 指標                          | 意味                                               |
| --------------------------- | ------------------------------------------------ |
| `idempotencyLawCount`       | 冪等性 law の宣言数                                     |
| `idempotencyViolationCount` | `f ∘ f = f` が破れた件数                               |
| `idempotencyGap`            | retryable と宣言された operation のうち、冪等性 evidence がない数 |
| `duplicateEffectRisk`       | 2回実行時に重複 event / 重複 side effect が観測された件数         |
| `retrySafetyCoverage`       | retryable operation のうち冪等性が評価済みの割合               |

### Law

```text
Idempotent(f) := ∀ s, f(f(s)) = f(s)
```

または観測同値版:

```text
Obs(f(f(s))) = Obs(f(s))
```

### 診断例

```text
CancelOrder is declared retryable,
but second execution emits duplicate OrderCancelled event.
```

---

## 6.3 Compensation / Saga Metrics

対象:

```text
Saga
workflow
transaction boundary
forward operation + compensation operation
```

### 追加指標

| 指標                               | 意味                                                |
| -------------------------------- | ------------------------------------------------- |
| `compensationLawCount`           | compensation law の宣言数                             |
| `compensationCoverageGap`        | forward operation はあるが compensation evidence がない数 |
| `compensationDefectCount`        | `compensate ∘ action ≈ id` が破れた数                  |
| `nonInvertibleCompensationCount` | compensation が明示されているが逆射/準逆射ではない数                 |
| `failureRecoveryGap`             | failure transition に対する recovery law がない数         |

### Law

厳密な逆射:

```text
compensate(action(s)) = s
```

現実的には観測同値:

```text
Obs(compensate(action(s))) = Obs(s)
```

### 診断例

```text
ReserveInventory has compensation CancelReservation,
but stock version and audit observation are not restored.
```

重要なのは、研究目標にある通り、Sagaは局所回復性を与えるが、補償射は一般に逆射ではないという前提を守ることです。([GitHub][2])

---

## 6.4 Event Log Homomorphism Metrics

対象:

```text
Event Sourcing
projection
read model
snapshot
event replay
event schema migration
```

### 追加指標

| 指標                               | 意味                                         |
| -------------------------------- | ------------------------------------------ |
| `eventProjectionLawCount`        | event projection law の宣言数                  |
| `replayHomomorphismDefect`       | 一括replayと分割replayが一致しない件数                  |
| `snapshotRoundtripDefect`        | snapshot + replay と full replay が一致しない件数   |
| `projectionOrderSensitivity`     | 独立eventの順序交換でread modelが変わる件数              |
| `eventMigrationNaturalityDefect` | migration と projection の順序を変えると結果が変わる件数    |
| `historyReconstructionGap`       | event log から現状態を再構成できない law / evidence 欠落数 |

### Law

event列を自由モノイド `E*` と見て、

```text
project(xs ++ ys) = replayFrom(project(xs), ys)
```

または fold 表現:

```text
project = fold applyEvent initialState
```

### 診断例

```text
OrderProjection violates replay homomorphism:
project(xs ++ ys) != replayFrom(project(xs), ys)
```

これは依存グラフでは検出できない、Event Sourcing固有の履歴再構成性リスク。

---

## 6.5 Effect Algebra Leakage Metrics

対象:

```text
Clean Architecture
Hexagonal Architecture
DIP
domain purity
application service
infrastructure effect
```

### 追加指標

| 指標                            | 意味                                                   |
| ----------------------------- | ---------------------------------------------------- |
| `effectOperationCount`        | 観測された effect operation 数                             |
| `effectLeakageCount`          | 許可されていない zone で発生した effect 数                         |
| `unhandledEffectCount`        | effect は発生しているが handler がない数                         |
| `handlerCoverageRatio`        | effect operation のうち handler が定義されている割合              |
| `ambientAuthorityUsageCount`  | global env / default credential / implicit IO 等への依存数 |
| `nonCommutingEffectPairCount` | 可換と宣言された effect pair が順序依存した件数                       |

### Law / Policy

```text
AllowedEffects(zone) ⊆ EffectSignature
ActualEffects(component) ⊆ AllowedEffects(zone)
```

handler coverage:

```text
∀ e ∈ ActualEffects, ∃ handler, Handles(handler, e)
```

### 診断例

```text
Domain layer has no forbidden import edge,
but emits SqlWrite effect.
```

これは依存グラフではなく、effect signature の違反。

---

## 6.6 Projection / Functor Soundness Metrics

対象:

```text
abstract architecture
concrete implementation
port / adapter
use case composition
DIP projection
```

### 追加指標

| 指標                                 | 意味                                                    |
| ---------------------------------- | ----------------------------------------------------- |
| `projectionCompletenessGap`        | concrete operation が abstract operation に写らない件数       |
| `projectionAmbiguityCount`         | 1つの concrete operation が複数abstract operationに曖昧対応する件数 |
| `compositionPreservationViolation` | `F(g ∘ f) = F(g) ∘ F(f)` が破れる件数                       |
| `identityPreservationViolation`    | no-op / identity が抽象側で identity として保存されない件数           |
| `projectionSoundnessViolation`     | 抽象射影全体のsoundness違反数                                   |

### Law

```text
F(id) = id
F(g ∘ f) = F(g) ∘ F(f)
```

### 診断例

```text
approveAndNotify should project to notify ∘ approve,
but notification failure leaves approve state committed.
```

これは「依存しているか」ではなく、「抽象設計上の合成として正しく振る舞うか」を見る。

---

## 6.7 Domain Representation / Roundtrip Metrics

対象:

```text
DTO
DB Entity
Domain Model
API Response
Event Payload
Serializer / Deserializer
Mapper
Adapter
```

### 追加指標

| 指標                             | 意味                                              |
| ------------------------------ | ----------------------------------------------- |
| `roundtripLawCount`            | roundtrip law の宣言数                              |
| `roundtripLossCount`           | `decode(encode(x)) = x` が破れた件数                  |
| `lossyProjectionWithoutPolicy` | 情報を落とす変換なのにpolicyがない件数                          |
| `conceptRedundancyIndex`       | 同一domain conceptに対する表現数                         |
| `semanticFieldDriftCount`      | 同名/同概念fieldの意味ズレ件数                              |
| `adapterLawViolationCount`     | adapterがidentity/composition/roundtrip lawを破る件数 |

### Law

```text
fromDto(toDto(domain)) = domain
```

または観測同値:

```text
Obs(fromDto(toDto(domain))) = Obs(domain)
```

### 診断例

```text
Money is represented as DomainMoney, PaymentAmount, PriceDto, InvoiceAmount,
and conversion loses currency precision.
```

---

## 6.8 Invariant Preservation Metrics

対象:

```text
business invariant
validation rule
database constraint
state machine guard
workflow precondition
```

### 追加指標

| 指標                               | 意味                                        |
| -------------------------------- | ----------------------------------------- |
| `invariantLawCount`              | invariant preservation law の宣言数           |
| `invariantPreservationGap`       | operation が保存すべき invariant の evidence 欠落数 |
| `invariantViolationWitnessCount` | invariant violation の counterexample 件数   |
| `constraintInconsistencyCount`   | 複数constraintのmeetがunsatになる件数              |
| `constraintDuplicationCount`     | 同じinvariantが複数箇所に重複実装されている件数              |
| `monotonicityViolationCount`     | 単調であるべき状態更新がpartial orderを逆行する件数          |

### Law

```text
Inv(s) -> Inv(f(s))
```

合成閉包:

```text
Preserves Inv f
Preserves Inv g
----------------
Preserves Inv (g ∘ f)
```

---

# 7. 新しいSignature構造

## 7.1 出力artifact

```json
{
  "schemaVersion": "algebraic-signature-v0",
  "signatureKind": "algebraic-laws",
  "repository": {
    "owner": "example",
    "name": "service"
  },
  "revision": {
    "sha": "abc123",
    "ref": "feature/order-cancel"
  },
  "lawUniverse": {
    "id": "order-service-laws-v0",
    "policyVersion": "2026-04-26",
    "equivalencePolicy": "observational-v0"
  },
  "signature": {
    "declaredLawCount": 24,
    "requiredLawCount": 21,
    "satisfiedLawCount": 13,
    "violatedLawCount": 2,
    "unmeasuredLawCount": 6,
    "lawDebt": 6,
    "lawCoverageRatio": 0.714,
    "manualEvidenceRatio": 0.25,
    "counterexampleCount": 1,

    "idempotencyViolationCount": 1,
    "idempotencyGap": 2,
    "compensationDefectCount": 1,
    "compensationCoverageGap": 1,
    "replayHomomorphismDefect": 0,
    "snapshotRoundtripDefect": 0,
    "effectLeakageCount": 3,
    "unhandledEffectCount": 1,
    "projectionSoundnessViolation": 0,
    "roundtripLossCount": 2,
    "invariantViolationWitnessCount": 1
  },
  "metricStatus": {
    "lawDebt": {
      "measured": true,
      "source": "derived:unmeasuredLawCount",
      "reason": "in algebraic-signature-v0, lawDebt is a derived alias of unmeasuredLawCount"
    },
    "replayHomomorphismDefect": {
      "measured": true,
      "source": "event-replay-check:v0"
    },
    "projectionSoundnessViolation": {
      "measured": false,
      "reason": "no projection evidence provided"
    }
  },
  "lawResults": [
    {
      "lawId": "order.cancel.idempotent",
      "kind": "idempotency",
      "status": "violated",
      "severity": "high",
      "evidenceIds": ["ev-order-cancel-001"],
      "counterexampleCount": 1,
      "evidence": [
        {
          "id": "ev-order-cancel-001",
          "evidenceKind": "property-test",
          "status": "violated",
          "runnerResult": {
            "outcome": "failed",
            "framework": "proptest",
            "exitCode": 1
          },
          "counterexamples": [
            {
              "operation": "CancelOrder(orderId=123)",
              "observation": "second execution emits duplicate OrderCancelled"
            }
          ]
        }
      ]
    }
  ],
  "excludedEvidence": [
    {
      "id": "framework-generated-handler-001",
      "reason": "framework-generated"
    }
  ]
}
```

---

# 8. 入力スキーマ

## 8.1 `architecture-laws/v0`

law registry。
MVPでは自動推論せず、このregistryを中心にする。

```json
{
  "schemaVersion": "architecture-laws/v0",
  "lawUniverse": {
    "id": "order-service-laws-v0",
    "policyVersion": "2026-04-26",
    "equivalencePolicy": "observational-v0"
  },
  "laws": [
    {
      "id": "order.cancel.idempotent",
      "kind": "idempotency",
      "required": true,
      "subject": {
        "operation": "CancelOrder",
        "component": "Order.Application.CancelOrder"
      },
      "equivalence": "observational",
      "observation": {
        "events": true,
        "publicState": true,
        "auditLog": false
      },
      "severity": "high",
      "tags": ["retryable-command", "order-workflow"]
    },
    {
      "id": "order.projection.homomorphism",
      "kind": "event-log-homomorphism",
      "required": true,
      "subject": {
        "projection": "OrderReadModelProjection",
        "eventStream": "OrderEvents"
      },
      "equivalence": "strict",
      "severity": "high"
    },
    {
      "id": "payment.reserve.compensated",
      "kind": "compensation",
      "required": true,
      "subject": {
        "forward": "ReservePayment",
        "compensate": "ReleasePayment"
      },
      "equivalence": "observational",
      "severity": "medium"
    },
    {
      "id": "user.dto.roundtrip",
      "kind": "roundtrip",
      "required": true,
      "subject": {
        "forward": "User.toDto",
        "backward": "UserDto.toDomain"
      },
      "equivalence": "observational",
      "severity": "medium"
    }
  ]
}
```

---

## 8.2 `law-evidence/v0`

property test、replay check、Lean proof、manual attestationなどを受け取る。

```json
{
  "schemaVersion": "law-evidence/v0",
  "repository": {
    "owner": "example",
    "name": "service"
  },
  "revision": {
    "sha": "abc123"
  },
  "evidence": [
    {
      "id": "ev-order-cancel-001",
      "lawId": "order.cancel.idempotent",
      "evidenceKind": "property-test",
      "status": "violated",
      "artifactPath": "target/law-checks/order_cancel_idempotent.json",
      "runnerResult": {
        "outcome": "failed",
        "framework": "proptest",
        "exitCode": 1
      },
      "counterexamples": [
        {
          "input": {
            "orderId": "123",
            "initialState": "Cancellable"
          },
          "expectedObservation": "single OrderCancelled event",
          "actualObservation": "two OrderCancelled events"
        }
      ]
    },
    {
      "id": "ev-order-projection-001",
      "lawId": "order.projection.homomorphism",
      "evidenceKind": "replay-check",
      "status": "satisfied",
      "sampleCount": 1200
    },
    {
      "id": "ev-user-dto-001",
      "lawId": "user.dto.roundtrip",
      "evidenceKind": "property-test",
      "status": "inconclusive",
      "runnerResult": {
        "outcome": "timeout",
        "framework": "proptest",
        "exitCode": 124
      }
    }
  ]
}
```

---

## 8.3 `effect-policy/v0`

```json
{
  "schemaVersion": "effect-policy/v0",
  "zones": [
    {
      "zone": "domain",
      "allowedEffects": ["Pure", "Validate", "Decide"]
    },
    {
      "zone": "application",
      "allowedEffects": ["ReadRepo", "WriteRepo", "PublishEvent"]
    },
    {
      "zone": "infrastructure",
      "allowedEffects": ["SqlRead", "SqlWrite", "HttpCall", "QueueSend"]
    }
  ],
  "handlers": [
    {
      "effect": "WriteRepo",
      "handlerComponent": "Order.Infrastructure.OrderRepository"
    }
  ]
}
```

---

## 8.4 `effect-evidence/v0`

```json
{
  "schemaVersion": "effect-evidence/v0",
  "observations": [
    {
      "component": "Order.Domain.CancelOrder",
      "zone": "domain",
      "effects": ["Validate", "WriteRepo"],
      "evidenceKind": "static-marker",
      "source": "effect annotations"
    }
  ]
}
```

---

# 9. CLI要件

## 9.1 新規サブコマンド

### `algebraic-laws`

law registry と evidence を読み、`algebraic-signature-v0` を出す。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-laws \
  --laws architecture-laws.json \
  --evidence law-evidence.json \
  --out .lake/algebraic-signature.json
```

### `effect-signature`

effect policy と evidence を読み、effect leakage metrics を出す。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- effect-signature \
  --policy effect-policy.json \
  --evidence effect-evidence.json \
  --out .lake/effect-signature.json
```

### `algebraic-validate`

`algebraic-signature-v0` の妥当性を検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-validate \
  --laws architecture-laws.json \
  --evidence law-evidence.json \
  --out .lake/algebraic-validation.json
```

生成済みsignatureを検査する形も許す。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-validate \
  --input .lake/algebraic-signature.json \
  --out .lake/algebraic-validation.json
```

検査内容:

| Check | 内容 |
| --- | --- |
| `duplicateLawId` | law registry内に同じlaw IDが複数ある |
| `unsupportedLawKind` | MVP非対応のlaw kindがrequired lawとして存在する |
| `danglingEvidence` | evidenceのlawIdがregistryに存在しない。デフォルトではaggregateから除外し、strict modeではfailにできる |
| `duplicateEvidenceId` | evidence IDが重複している |
| `invalidEvidenceStatus` | statusが`satisfied` / `violated` / `inconclusive`以外 |
| `conflictingEvidence` | 同一lawに`satisfied`と`violated`が混在する。集計上は`violated`を優先し、warningを出す |
| `missingEvidenceForRequiredLaw` | required lawにconclusive evidenceがない |
| `counterexampleMissingForViolation` | violated evidenceなのにcounterexample / witnessがない |
| `lawDebtDerivedInvariant` | `lawDebt != unmeasuredLawCount` |
| `countConsistency` | `requiredLawCount != satisfiedLawCount + violatedLawCount + unmeasuredLawCount` |
| `invalidEquivalencePolicy` | equivalence policy が未定義 |
| `manualEvidenceRatioWarning` | manual attestation が多すぎる場合にwarn |

---

## 9.2 既存 `snapshot` の拡張

既存snapshotは `sig0.json` を保存する。
拡張後は複数signature artifactを扱えるようにする。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- snapshot \
  --input .lake/sig0.json \
  --algebraic-signature .lake/algebraic-signature.json \
  --validation-report .lake/sig0-validation.json \
  --algebraic-validation-report .lake/algebraic-validation.json \
  --repo-owner example \
  --repo-name service \
  --revision-sha "$(git rev-parse HEAD)" \
  --out .lake/signature-current/snapshot.json
```

snapshot内では以下のように保持する。

```json
{
  "signatureArtifacts": [
    {
      "schemaVersion": "archsig-sig0-v0",
      "path": ".lake/sig0.json"
    },
    {
      "schemaVersion": "algebraic-signature-v0",
      "path": ".lake/algebraic-signature.json"
    }
  ]
}
```

---

## 9.3 `signature-diff` の拡張

既存のdiffは、悪化軸、改善軸、未評価軸、evidence diff、PR attribution candidateを出します。([GitHub][1])
AlgSigでも同じ考え方を使う。

追加diff項目:

```json
{
  "algebraicDiff": {
    "worsenedAxes": [
      {
        "axis": "idempotencyViolationCount",
        "before": 0,
        "after": 1,
        "delta": 1
      }
    ],
    "improvedAxes": [],
    "unmeasuredAxes": [
      {
        "axis": "projectionSoundnessViolation",
        "reason": "no projection evidence provided"
      }
    ],
    "lawStatusDiff": {
      "newlyViolatedLaws": ["order.cancel.idempotent"],
      "newlySatisfiedLaws": [],
      "newlyUnmeasuredLaws": []
    },
    "evidenceDiff": {
      "addedCounterexamples": [
        {
          "lawId": "order.cancel.idempotent",
          "summary": "second CancelOrder emits duplicate OrderCancelled"
        }
      ]
    }
  }
}
```

### primary diff eligibility

`comparisonStatus.primaryDiffEligible = false` にする条件:

| 条件                              | 理由                        |
| ------------------------------- | ------------------------- |
| `lawUniverse.id` が違う            | 比較対象のlaw集合が違う             |
| `equivalencePolicy` が違う         | 観測同値の定義が違う                |
| `ruleSetVersion` が違う            | 集計規則が違う                   |
| before/afterの片方でvalidation fail | 入力artifactが比較不能           |
| evidence sourceのcoverageが大きく異なる | observed violation数の比較が偏る |

---

## 9.4 `dataset` の拡張

既存datasetは、before / after の両方で測定済みかつ値が `null` でない軸だけを `deltaSignatureSigned` に出す設計です。([GitHub][1])
AlgSigでも同じルールを守る。

追加dataset項目:

```json
{
  "algebraicSignatureBefore": {
    "violatedLawCount": 1,
    "lawDebt": 8,
    "idempotencyViolationCount": 0
  },
  "algebraicSignatureAfter": {
    "violatedLawCount": 2,
    "lawDebt": 6,
    "idempotencyViolationCount": 1
  },
  "deltaAlgebraicSignatureSigned": {
    "violatedLawCount": 1,
    "lawDebt": -2,
    "idempotencyViolationCount": 1
  },
  "algebraicAttribution": {
    "changedLaws": ["order.cancel.idempotent"],
    "changedComponents": ["Order.Application.CancelOrder"],
    "newCounterexampleCount": 1
  }
}
```

---

# 10. Leanで証明すべきこと

## 10.1 基礎定義

Lean側では、まず以下を定義する。

```lean
Law
LawKind
LawUniverse
EvidenceStatus
MetricStatus
ObservedViolation
ArchitectureOperation
Observation
```

概念的には、

```lean
structure Law where
  id : String
  kind : LawKind
  required : Bool
```

ただし、実装上はString中心ではなく、有限型や識別子型で扱える形が望ましい。

---

## 10.2 指標意味論の証明

### 証明すべきこと

```text
MVP v0では
lawDebt = required laws without conclusive satisfied/violated evidence
        = unmeasuredLawCount
```

Leanで示すべき定理:

```text
lawDebt = 0
↔
全 required law が satisfied または violated の status を持つ
```

ただし、これは「全lawが真」という意味ではない。

また、

```text
violatedLawCount > 0
→
少なくとも1つの law に counterexample evidence が存在する
```

も証明する。

### 重要な非主張

```text
violatedLawCount = 0
→
全lawが真
```

これは証明してはいけない。
`unmeasuredLawCount = 0` や evidence の完全性仮定がない限り、成立しない。

---

## 10.3 Idempotency

### 定義

```lean
def Idempotent (f : S → S) : Prop :=
  ∀ s, f (f s) = f s
```

観測同値版:

```lean
def ObservationallyIdempotent
  (obs : S → O)
  (f : S → S) : Prop :=
  ∀ s, obs (f (f s)) = obs (f s)
```

### 証明すべき定理

```text
Idempotent f
→
任意回数 retry しても1回実行と同じ状態になる
```

観測同値版:

```text
ObservationallyIdempotent obs f
→
任意回数 retry しても外部観測は1回実行と同じ
```

CLI診断との接続:

```text
idempotencyViolationCount > 0
→
少なくとも1つの retryable operation について、
f(f(s)) ≠ f(s) または Obs(f(f(s))) ≠ Obs(f(s)) の witness がある
```

---

## 10.4 Compensation / Saga

### 定義

厳密補償:

```lean
def IsLeftInverse (comp f : S → S) : Prop :=
  ∀ s, comp (f s) = s
```

観測補償:

```lean
def ObservationalCompensation
  (obs : S → O)
  (f comp : S → S) : Prop :=
  ∀ s, obs (comp (f s)) = obs s
```

### 証明すべき定理

```text
ObservationalCompensation obs f comp
→
f実行後にcompを実行すると、外部観測上は元に戻る
```

さらに、Saga全体について:

```text
各stepに観測補償があり、
補償順序が逆順で適用されるなら、
失敗prefixに対して観測回復が成立する
```

### 注意

Sagaの補償は一般に完全な逆射ではない。
したがってLeanでは、`inverse` ではなく `observational retraction` や `compensation under observation` として扱う。

---

## 10.5 Event Log Homomorphism

### 定義

event列を自由モノイドとして扱う。

```lean
def Project (events : List E) : R
```

またはfoldとして:

```lean
def project : List E → R :=
  List.foldl apply initial
```

### Law

```lean
project (xs ++ ys) = replayFrom (project xs) ys
```

### 証明すべき定理

```text
projection が fold として定義されているなら、
append に対する homomorphism law が成り立つ
```

```text
project(xs ++ ys) = replayFrom(project(xs), ys)
```

snapshotについて:

```text
snapshot = project xs
→
replayFrom snapshot ys = project (xs ++ ys)
```

migrationについては自然性として扱う。

```text
migrateReadModel(project_old events)
=
project_new(migrateEvents events)
```

CLI診断との接続:

```text
replayHomomorphismDefect > 0
→
append分解に対するprojection不一致のcounterexampleがある
```

---

## 10.6 Roundtrip / Representation Isomorphism

### 定義

```lean
def RoundTripLeft (encode : A → B) (decode : B → A) : Prop :=
  ∀ a, decode (encode a) = a
```

観測同値版:

```lean
def ObservationalRoundTrip
  (obs : A → O)
  (encode : A → B)
  (decode : B → A) : Prop :=
  ∀ a, obs (decode (encode a)) = obs a
```

### 証明すべき定理

```text
RoundTripLeft encode decode
→
encode後decodeしてもA側の情報は失われない
```

合成について:

```text
A ↔ B が roundtrip
B ↔ C が roundtrip
なら、
A ↔ C も roundtrip
```

ただし、観測同値版では observation の整合条件が必要。

---

## 10.7 Invariant Preservation

### 定義

```lean
def Preserves (Inv : S → Prop) (f : S → S) : Prop :=
  ∀ s, Inv s → Inv (f s)
```

### 証明すべき定理

合成閉包:

```text
Preserves Inv f
Preserves Inv g
→
Preserves Inv (g ∘ f)
```

workflowへの拡張:

```text
各commandがInvを保存するなら、
command列全体もInvを保存する
```

CLI診断との接続:

```text
invariantViolationWitnessCount > 0
→
Inv s は真だが Inv(f(s)) が偽になる witness がある
```

---

## 10.8 Effect Algebra Leakage

### 定義

```lean
ActualEffects : Component → Set Effect
AllowedEffects : Zone → Set Effect
ComponentZone : Component → Zone
```

law:

```lean
∀ c, ActualEffects c ⊆ AllowedEffects (ComponentZone c)
```

handler coverage:

```lean
∀ e ∈ ActualEffects c, ∃ h, Handles h e
```

### 証明すべき定理

```text
全componentでActualEffects ⊆ AllowedEffectsが成立
→
effect leakage は0
```

```text
effectLeakageCount > 0
→
あるcomponent c と effect e が存在し、
e ∈ ActualEffects c かつ e ∉ AllowedEffects(zone c)
```

---

## 10.9 Projection / Functor Soundness

### 定義

Concrete architecture と Abstract architecture を小さなcategoryまたはcomposition structureとして定義する。

```lean
F : Concrete → Abstract
```

law:

```lean
F id = id
F (g ∘ f) = F g ∘ F f
```

### 証明すべき定理

```text
Fがidentityとcompositionを保存するなら、
concrete workflowの抽象像は、abstract operationの合成として解釈できる
```

CLI診断との接続:

```text
compositionPreservationViolation > 0
→
F(g ∘ f) ≠ F(g) ∘ F(f) の witness がある
```

---

# 11. 実装ロードマップ

## Phase 0: Schema and Aggregation MVP

目的:

```text
law registry + evidence JSON から algebraic-signature-v0 を生成する
```

実装するもの:

* `architecture-laws/v0`
* `law-evidence/v0`
* `algebraic-signature-v0`
* `algebraic-laws` subcommand
* `algebraic-validate` subcommand
* `declaredLawCount`
* `requiredLawCount`
* `satisfiedLawCount`
* `lawDebt`
* `violatedLawCount`
* `unmeasuredLawCount`
* `lawCoverageRatio`
* `manualEvidenceRatio`
* `counterexampleCount`
* `idempotencyViolationCount`
* `compensationDefectCount`
* `replayHomomorphismDefect`
* `roundtripLossCount`

この段階では、ソースコード自動解析はしない。
property testやreplay checkの結果JSONを読む。
また、snapshot / signature-diff / dataset 統合は Phase 4 に回し、Phase 0 の最初のPRには含めない。

---

## Phase 1: Relation ComplexityからLawfulnessへ拡張

目的:

現行の `relation-complexity` を、単なるtag countからlaw候補生成へ拡張する。

現在の relation complexity は `constraints`, `compensations`, `projections`, `failureTransitions`, `idempotencyRequirements` を数えます。([GitHub][1])
これを以下に発展させる。

```text
idempotencyRequirements
  -> idempotency law candidate

compensations
  -> compensation law candidate

projections
  -> event-log-homomorphism / projection law candidate

constraints
  -> invariant preservation law candidate

failureTransitions
  -> recovery / compensation law candidate
```

新規コマンド案:

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- law-candidates \
  --relation-complexity relation-complexity-candidates.json \
  --out architecture-laws.generated.json
```

ただし、generated law は `required=false` または `candidate=true` として扱い、人間が昇格させる。

---

## Phase 2: Event Replay Checker連携

目的:

Event Sourcing系のlawを実データで測る。

実装するもの:

* `event-log-evidence/v0`
* `replayHomomorphismDefect`
* `snapshotRoundtripDefect`
* `eventMigrationNaturalityDefect`

CLIは直接アプリコードを実行しない。
外部replay checkerが出したJSONを読む。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-laws \
  --laws architecture-laws.json \
  --evidence law-evidence.json \
  --event-replay-evidence event-replay-evidence.json \
  --out .lake/algebraic-signature.json
```

---

## Phase 3: Effect Signature

目的:

Clean Architecture / Hexagonal / DIP を import graph ではなく effect leakage として測る。

実装するもの:

* `effect-policy/v0`
* `effect-evidence/v0`
* `effectLeakageCount`
* `unhandledEffectCount`
* `handlerCoverageRatio`
* `ambientAuthorityUsageCount`

MVPでは、effect evidence は以下から受け取る。

```text
annotations
static markers
manually generated JSON
language-specific analyzer output
```

---

## Phase 4: Snapshot / Diff / Dataset統合

目的:

既存のPR診断フローにAlgSigを統合する。

実装するもの:

* snapshotで `algebraic-signature-v0` を保存
* signature-diffで `algebraicDiff` を生成
* datasetで `deltaAlgebraicSignatureSigned` を生成
* `primaryDiffEligible` 判定に `lawUniverse`, `equivalencePolicy`, `ruleSetVersion` を追加

---

## Phase 5: Lean Formal Core

目的:

CLI指標の理論的意味をLeanで保証する。

成果物:

```text
Formal/Arch/Algebraic/Law.lean
Formal/Arch/Algebraic/Metric.lean
Formal/Arch/Algebraic/Idempotency.lean
Formal/Arch/Algebraic/Compensation.lean
Formal/Arch/Algebraic/EventLog.lean
Formal/Arch/Algebraic/Roundtrip.lean
Formal/Arch/Algebraic/Invariant.lean
Formal/Arch/Algebraic/Effect.lean
Formal/Arch/Algebraic/Projection.lean
```

---

# 12. 受け入れ基準

## 12.1 MVP受け入れ基準

### Case 1: idempotency violation

入力:

* `architecture-laws.json` に `order.cancel.idempotent`
* `law-evidence.json` に violated evidence

期待出力:

```json
{
  "signature": {
    "violatedLawCount": 1,
    "idempotencyViolationCount": 1,
    "lawDebt": 0
  },
  "lawResults": [
    {
      "lawId": "order.cancel.idempotent",
      "status": "violated"
    }
  ]
}
```

---

### Case 2: law未評価

入力:

* law registryに required law が3つ
* evidenceは1つだけ

期待出力:

```json
{
  "signature": {
    "requiredLawCount": 3,
    "satisfiedLawCount": 1,
    "violatedLawCount": 0,
    "unmeasuredLawCount": 2,
    "lawDebt": 2
  }
}
```

診断文:

```text
violatedLawCount = 0 だが、lawDebt = 2 のため lawfulness は未評価。
```

---

### Case 3: before/after diff

before:

```json
"idempotencyViolationCount": 0
```

after:

```json
"idempotencyViolationCount": 1
```

期待diff:

```json
{
  "algebraicDiff": {
    "worsenedAxes": [
      {
        "axis": "idempotencyViolationCount",
        "before": 0,
        "after": 1,
        "delta": 1
      }
    ],
    "lawStatusDiff": {
      "newlyViolatedLaws": ["order.cancel.idempotent"]
    }
  }
}
```

---

### Case 4: lawUniverse不一致

before:

```json
"lawUniverse": { "id": "order-service-laws-v0" }
```

after:

```json
"lawUniverse": { "id": "order-service-laws-v1" }
```

期待出力:

```json
{
  "comparisonStatus": {
    "primaryDiffEligible": false,
    "reasons": [
      "law universe differs"
    ]
  }
}
```

---

# 13. AI reviewer向け診断テンプレート

## 13.1 Red診断

```text
このPRは依存グラフ上のfanoutを増やしていませんが、
algebraic signature上では idempotencyViolationCount が 0 -> 1 に悪化しています。

新たに violated になった law:
- order.cancel.idempotent

counterexample:
- CancelOrder(orderId=123) を2回実行すると OrderCancelled event が2回発行されます。

このoperationが retryable-command として宣言されている場合、
重複実行時の観測を1回実行と一致させる必要があります。
```

---

## 13.2 Yellow診断

```text
このPRでは violatedLawCount は増えていません。
ただし lawDebt が 4 -> 7 に増えています。

つまり、違反がないのではなく、
新しく追加されたworkflowに対する代数法則のevidenceが不足しています。

未評価law:
- payment.reserve.compensated
- order.projection.homomorphism
- user.dto.roundtrip
```

---

## 13.3 Green診断

```text
このPRでは以下の代数指標が改善しています。

- lawDebt: 5 -> 2
- replayHomomorphismDefect: 1 -> 0

Event projection の分割replay lawが満たされるようになり、
履歴再構成性のriskが下がっています。
```

---

# 14. 優先順位

## P0: 必須

* `architecture-laws/v0`
* `law-evidence/v0`
* `algebraic-signature-v0`
* `algebraic-laws` command
* `algebraic-validate` command
* core law metrics
* idempotency metrics
* compensation metrics
* event replay homomorphism metrics
* roundtrip metrics

## P1: 強く推奨

* relation-complexityからlaw candidate生成
* effect signature metrics
* invariant preservation metrics
* snapshot / diffの最小統合
* dataset統合
* AI reviewer用diagnostic summary

## P2: 将来拡張

* projection / functor soundness
* observability kernel
* LSP / behavioral trace inclusion
* configuration algebra
* capability algebra
* language-specific static analyzers

---

# 15. 成功指標

## Product success

```text
PR diff report上で、
依存グラフに変化がないにもかかわらず、
代数法則の悪化を検出できる。
```

具体的には:

* 新規 idempotency violation を検出できる
* 新規 replay homomorphism defect を検出できる
* compensation law の未評価 / 破れを区別できる
* roundtrip loss を evidence 付きで報告できる
* `lawDebt` と `violatedLawCount` を分離できる

## Research success

```text
algebraic signature の悪化と、
review cost / bug fix cost / incident recurrence / change propagation の関係をdatasetで検証できる。
```

研究目標では、signatureの悪化と変更ファイル数、SCCと障害修正時間、fanoutとレビューコスト、境界違反と将来の変更波及、relation complexityと運用リスクの関係を実データで検証する方針が示されています。AlgSigはここに、lawDebt、idempotencyViolation、replayHomomorphismDefect、compensationDefectなどを追加する位置づけです。([GitHub][2])

---
