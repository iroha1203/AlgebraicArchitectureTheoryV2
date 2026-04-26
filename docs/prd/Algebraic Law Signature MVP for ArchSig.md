# PRD: Algebraic Law Signature MVP for ArchSig

Status: Draft v0.1

Lean status: `empirical hypothesis` / tooling output. This PRD is not a Lean proof claim.

## 1. 概要

この文書は、[Algebraic Signature Extension for ArchSig](<Algebraic Signature Extension for ArchSig.md>) の Phase 0 実装仕様である。

MVPでは、自動解析器ではなく、明示された law registry と evidence JSON を集計する **law registry + evidence aggregator** に絞る。

```text
architecture-laws/v0
+ law-evidence/v0
-> algebraic-signature-v0
-> algebraic-validate
```

現行 ArchSig は Lean 証明器ではなく、CI や AI agent が読む JSON artifact を生成する architecture telemetry generator である。現行フローも `scan -> validate -> snapshot -> signature-diff` を中心とし、`metricStatus` によって「測定済み 0」と「未評価」を区別する。このMVPも同じ思想を継承する。([1])

## 2. MVPスコープ

### やること

- `architecture-laws/v0` schema
- `law-evidence/v0` schema
- `algebraic-signature-v0` output
- `algebraic-laws` command
- `algebraic-validate` command
- law result status の解決
- law単位 count と witness単位 count の分離
- kind別 violation metric の `metricStatus` ルール
- fixtures と README 更新

### MVPではやらないこと

- snapshot 統合
- signature-diff 統合
- dataset 統合
- effect-signature
- relation-complexity からの law candidate 自動生成
- language-specific static analyzer
- 実アプリ全体の正しさを Lean で証明すること

現行 Rust 実装では `SignatureSnapshot` と `SignatureSnapshotStoreRecordV0` が単一の `signature` と単一の `metric_status` を持つ。`signatureArtifacts[]` 方向の拡張は妥当だが、最初のPRに含めると後方互換とレビュー範囲が大きくなるため、MVP後の follow-up に分ける。([2])

## 3. Status語彙

### 3.1 Law result status

`lawResults[].status` は次の3状態に固定する。

```text
satisfied
violated
unmeasured
```

| status | 意味 |
| --- | --- |
| `satisfied` | 宣言済み law に対して、少なくとも1つの conclusive satisfied evidence がある。 |
| `violated` | 宣言済み law に対して、少なくとも1つの conclusive violated evidence / witness / counterexample がある。 |
| `unmeasured` | law は宣言されているが、conclusive evidence がない。 |

`undeclared` は `lawResults[].status` に入れない。

law registry に存在しない `lawId` への evidence は、`lawResults` ではなく、validation report の `danglingEvidence`、`excludedEvidence`、または candidate law state として扱う。

### 3.2 Evidence status

`law-evidence/v0` の `evidence[].status` は次の3状態に固定する。

```text
satisfied
violated
inconclusive
```

`failed`, `passed`, `error` は evidence status には使わない。これらは test runner の実行結果として `runnerResult` などの payload に入れる。

悪い例:

```json
{
  "evidenceKind": "property-test",
  "status": "failed"
}
```

良い例:

```json
{
  "evidenceKind": "property-test",
  "status": "violated",
  "runnerResult": {
    "outcome": "failed",
    "framework": "proptest",
    "exitCode": 1
  }
}
```

CLI は evidence status を次のように集計する。

| evidence status | 集計上の意味 |
| --- | --- |
| `satisfied` | law を satisfied 候補にする。 |
| `violated` | law を violated 候補にする。 |
| `inconclusive` | law を discharge しない。 |

### 3.3 Resolution rule

同一 law に複数 evidence がある場合は、次の順で解決する。

1. `violated` evidence が1つ以上ある場合、`lawResult.status = violated`
2. `violated` evidence がなく、`satisfied` evidence が1つ以上ある場合、`lawResult.status = satisfied`
3. `satisfied` / `violated` がなく、`inconclusive` evidence のみ、または evidence がない場合、`lawResult.status = unmeasured`

`satisfied` と `violated` が同一 law に混在する場合、集計上は保守的に `violated` とし、validation report に `conflictingEvidence` warning を出す。

```json
{
  "lawId": "order.cancel.idempotent",
  "status": "violated",
  "resolution": "violated-precedence",
  "validationNotes": [
    "both satisfied and violated evidence exist"
  ]
}
```

## 4. Count単位

MVPでは **law単位の count** と **evidence / witness単位の count** を分離する。

### 4.1 Law単位の指標

| 指標 | 単位 | 定義 |
| --- | ---: | --- |
| `declaredLawCount` | law ID数 | registry 内の distinct law ID 数。 |
| `requiredLawCount` | law ID数 | `required = true` の distinct law ID 数。 |
| `satisfiedLawCount` | law ID数 | required law のうち `status = satisfied` の数。 |
| `violatedLawCount` | law ID数 | required law のうち `status = violated` の数。 |
| `unmeasuredLawCount` | law ID数 | required law のうち `status = unmeasured` の数。 |
| `idempotencyViolationCount` | law ID数 | required かつ `kind = idempotency` かつ `status = violated` の数。 |
| `compensationDefectCount` | law ID数 | required かつ `kind = compensation` かつ `status = violated` の数。 |
| `replayHomomorphismDefect` | law ID数 | required かつ `kind = event-log-homomorphism` かつ `status = violated` の数。 |
| `roundtripLossCount` | law ID数 | required かつ `kind = roundtrip` かつ `status = violated` の数。 |

MVPの signature count は required law のみを対象にする。optional law は `lawResults` には出してよいが、P0 signature count には入れない。

### 4.2 Evidence / witness単位の指標

| 指標 | 単位 | 定義 |
| --- | ---: | --- |
| `counterexampleCount` | witness数 | valid かつ declared law に紐づく counterexample / witness 数。 |
| `manualEvidenceRatio` | evidence比率 | conclusive evidence のうち `evidenceKind = manual` の割合。 |

`violatedLawCount` と `counterexampleCount` は一致しなくてよい。

例:

```json
{
  "violatedLawCount": 1,
  "counterexampleCount": 3
}
```

## 5. `lawDebt`

MVP v0では `lawDebt` は `unmeasuredLawCount` の派生値である。

```text
lawDebt :=
  required law のうち、
  satisfied でも violated でもない law 数
```

MVPでは `lawResults.status` が3状態なので、validation は次を保証する。

```text
lawDebt = unmeasuredLawCount
```

`algebraic-signature-v0` では、次の注意を README と output の `metricStatus` に残す。

```text
In algebraic-signature-v0, lawDebt is currently a derived alias of unmeasuredLawCount.
Do not treat it as an independent metric.
```

将来版では、`unsupported`, `invalid`, `inconclusive`, `waived = false` などを含めて、次のように拡張する余地を残す。

```text
lawDebt :=
  required law のうち、
  satisfied によって discharge されておらず、
  waived でもない law 数
```

## 6. `metricStatus` ルール

### 6.1 Core count metrics

次の指標は、`--laws` が正常に読め、validation が fatal でなければ `measured = true` にする。

```text
declaredLawCount
requiredLawCount
satisfiedLawCount
violatedLawCount
unmeasuredLawCount
lawDebt
counterexampleCount
```

理由は、registry と evidence を読んだ結果として law 単位の分類が確定しているためである。

### 6.2 `lawCoverageRatio`

定義:

```text
lawCoverageRatio =
  (satisfiedLawCount + violatedLawCount) / requiredLawCount
```

`requiredLawCount = 0` の場合は `null` にする。`1.0` にはしない。

```json
{
  "lawCoverageRatio": null,
  "metricStatus": {
    "lawCoverageRatio": {
      "measured": false,
      "reason": "undefined because requiredLawCount is 0"
    }
  }
}
```

これは、AI reviewer が「全部カバー済み」と誤読するのを防ぐためである。

### 6.3 Kind別 violation metrics

対象:

```text
idempotencyViolationCount
compensationDefectCount
replayHomomorphismDefect
roundtripLossCount
```

これらは値だけで読まず、対象 kind の required law 群が評価可能だったかを `metricStatus` とセットで読む。

#### ケースA: required law of kind が存在しない

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

これは「冪等性違反がない」という意味ではなく、required idempotency law が宣言されていないため集計対象が空、という意味である。

#### ケースB: required law of kind があり、全て conclusive

```json
{
  "idempotencyViolationCount": 1,
  "metricStatus": {
    "idempotencyViolationCount": {
      "measured": true,
      "source": "law-evidence:v0"
    }
  }
}
```

#### ケースC: required law of kind があるが、一部 unmeasured

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

このケースでは、値が 0 でも risk 0 とは読まない。

## 7. Schema

### 7.1 `architecture-laws/v0`

```json
{
  "schemaVersion": "architecture-laws/v0",
  "lawUniverse": {
    "id": "order-service-laws-v0",
    "version": "2026-04-26",
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
      "severity": "high",
      "tags": ["retryable-command"]
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
      "severity": "medium",
      "tags": ["saga"]
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
      "severity": "high",
      "tags": ["event-sourcing"]
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
      "severity": "medium",
      "tags": ["representation"]
    }
  ]
}
```

### 7.2 `law-evidence/v0`

```json
{
  "schemaVersion": "law-evidence/v0",
  "repository": {
    "owner": "example",
    "name": "order-service"
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

### 7.3 `algebraic-signature-v0`

```json
{
  "schemaVersion": "algebraic-signature-v0",
  "signatureKind": "algebraic-laws",
  "lawUniverse": {
    "id": "order-service-laws-v0",
    "version": "2026-04-26",
    "equivalencePolicy": "observational-v0"
  },
  "signature": {
    "declaredLawCount": 4,
    "requiredLawCount": 4,
    "satisfiedLawCount": 1,
    "violatedLawCount": 1,
    "unmeasuredLawCount": 2,
    "lawDebt": 2,
    "lawCoverageRatio": 0.5,
    "manualEvidenceRatio": 0.0,
    "counterexampleCount": 1,
    "idempotencyViolationCount": 1,
    "compensationDefectCount": 0,
    "replayHomomorphismDefect": 0,
    "roundtripLossCount": 0
  },
  "metricStatus": {
    "lawDebt": {
      "measured": true,
      "source": "derived:unmeasuredLawCount",
      "reason": "in algebraic-signature-v0, lawDebt is a derived alias of unmeasuredLawCount"
    },
    "compensationDefectCount": {
      "measured": false,
      "source": "law-evidence:v0",
      "reason": "1 required compensation law is unmeasured"
    },
    "roundtripLossCount": {
      "measured": false,
      "source": "law-evidence:v0",
      "reason": "1 required roundtrip law is unmeasured"
    }
  },
  "lawResults": [
    {
      "lawId": "order.cancel.idempotent",
      "kind": "idempotency",
      "required": true,
      "status": "violated",
      "evidenceIds": ["ev-order-cancel-001"],
      "counterexampleCount": 1
    },
    {
      "lawId": "payment.reserve.compensated",
      "kind": "compensation",
      "required": true,
      "status": "unmeasured",
      "evidenceIds": []
    },
    {
      "lawId": "order.projection.homomorphism",
      "kind": "event-log-homomorphism",
      "required": true,
      "status": "satisfied",
      "evidenceIds": ["ev-order-projection-001"]
    },
    {
      "lawId": "user.dto.roundtrip",
      "kind": "roundtrip",
      "required": true,
      "status": "unmeasured",
      "evidenceIds": ["ev-user-dto-001"],
      "notes": [
        "inconclusive evidence does not discharge the law"
      ]
    }
  ],
  "excludedEvidence": [],
  "validationSummary": {
    "result": "pass",
    "failedCheckCount": 0,
    "warningCheckCount": 0
  }
}
```

## 8. Validation仕様

### 8.1 `algebraic-validate`

law registry と evidence を直接検査する。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-validate \
  --laws architecture-laws.json \
  --evidence law-evidence.json \
  --out algebraic-validation.json
```

生成済み signature を検査する形も許す。

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-validate \
  --input algebraic-signature.json \
  --out algebraic-validation.json
```

### 8.2 Validation checks

| check | result | 内容 |
| --- | --- | --- |
| `duplicateLawId` | fail | law registry 内に同じ law ID が複数ある。 |
| `unsupportedLawKind` | fail | MVP非対応の law kind が required law として存在する。 |
| `danglingEvidence` | warn/fail option | evidence の `lawId` が registry に存在しない。 |
| `duplicateEvidenceId` | fail | evidence ID が重複している。 |
| `invalidEvidenceStatus` | fail | status が `satisfied` / `violated` / `inconclusive` 以外。 |
| `conflictingEvidence` | warn | 同一 law に `satisfied` と `violated` が混在する。 |
| `missingEvidenceForRequiredLaw` | warn | required law に conclusive evidence がない。 |
| `counterexampleMissingForViolation` | warn | violated evidence なのに counterexample / witness がない。 |
| `lawDebtDerivedInvariant` | fail | `lawDebt != unmeasuredLawCount`。 |
| `countConsistency` | fail | `requiredLawCount != satisfiedLawCount + violatedLawCount + unmeasuredLawCount`。 |

`danglingEvidence` はデフォルトでは aggregate から除外する。strict mode では fail にできる。

## 9. CLI要件

### 9.1 `algebraic-laws`

```bash
cargo run --manifest-path tools/archsig/Cargo.toml -- algebraic-laws \
  --laws architecture-laws.json \
  --evidence law-evidence.json \
  --out algebraic-signature.json
```

責務:

1. law registry を読む。
2. evidence を読む。
3. evidence を declared law に join する。
4. `lawResults` を resolution rule で解決する。
5. signature counts を生成する。
6. `metricStatus` を生成する。
7. `excludedEvidence` を生成する。
8. `validationSummary` を埋める。

### 9.2 `algebraic-validate`

責務:

1. schema 語彙の検査。
2. law ID / evidence ID の重複検査。
3. dangling evidence 検査。
4. count consistency 検査。
5. `lawDebt` derived invariant 検査。
6. required law の missing evidence warning。

## 10. Rust側の型追加案

MVPでは現行 snapshot 構造に触らず、新規型を追加する。

```rust
pub struct ArchitectureLawsV0 {
    pub schema_version: String,
    pub law_universe: LawUniverseRef,
    pub laws: Vec<ArchitectureLaw>,
}

pub struct ArchitectureLaw {
    pub id: String,
    pub kind: LawKind,
    pub required: bool,
    pub subject: serde_json::Value,
    pub equivalence: Option<String>,
    pub severity: Option<String>,
    pub tags: Vec<String>,
}

pub enum LawKind {
    Idempotency,
    Compensation,
    EventLogHomomorphism,
    Roundtrip,
}

pub struct LawEvidenceFileV0 {
    pub schema_version: String,
    pub repository: Option<RepositoryRef>,
    pub revision: Option<RepositoryRevisionRef>,
    pub evidence: Vec<LawEvidence>,
}

pub struct LawEvidence {
    pub id: String,
    pub law_id: String,
    pub evidence_kind: EvidenceKind,
    pub status: EvidenceStatus,
    pub counterexamples: Vec<serde_json::Value>,
    pub artifact_path: Option<String>,
    pub runner_result: Option<serde_json::Value>,
}

pub enum EvidenceStatus {
    Satisfied,
    Violated,
    Inconclusive,
}

pub enum LawResultStatus {
    Satisfied,
    Violated,
    Unmeasured,
}
```

## 11. Fixtures

MVPで必ず作る fixture:

```text
fixtures/algebraic/minimal_satisfied
fixtures/algebraic/idempotency_violated
fixtures/algebraic/unmeasured_required_law
fixtures/algebraic/inconclusive_evidence
fixtures/algebraic/dangling_evidence
fixtures/algebraic/duplicate_law_id
fixtures/algebraic/no_required_laws
fixtures/algebraic/no_required_laws_for_kind
fixtures/algebraic/conflicting_evidence
fixtures/algebraic/multiple_counterexamples_one_law
```

重要な期待値:

```json
{
  "violatedLawCount": 1,
  "idempotencyViolationCount": 1,
  "counterexampleCount": 3
}
```

```json
{
  "satisfiedLawCount": 0,
  "violatedLawCount": 0,
  "unmeasuredLawCount": 1,
  "lawDebt": 1
}
```

```json
{
  "idempotencyViolationCount": 0,
  "metricStatus": {
    "idempotencyViolationCount": {
      "measured": true,
      "source": "law-registry:no-required-laws-for-kind"
    }
  }
}
```

```json
{
  "idempotencyViolationCount": 0,
  "metricStatus": {
    "idempotencyViolationCount": {
      "measured": false,
      "reason": "1 required idempotency law is unmeasured"
    }
  }
}
```

## 12. Leanで証明すべきこと

MVPのLean側は、各アーキテクチャ法則そのものの深い証明より、まず指標意味論の正しさを対象にする。

### 12.1 Required law partition

validation pass、distinct law IDs、resolution rule applied を前提に、required laws が `satisfied` / `violated` / `unmeasured` に分割されることを示す。

```lean
theorem required_law_partition :
  requiredLawCount = satisfiedLawCount + violatedLawCount + unmeasuredLawCount
```

### 12.2 `lawDebt` derived invariant

MVPでは以下を証明する。

```lean
theorem lawDebt_eq_unmeasured_v0 :
  lawDebt = unmeasuredLawCount
```

### 12.3 Violation count witness theorem

```lean
theorem violatedLawCount_pos_exists :
  violatedLawCount > 0 →
  ∃ law, law.required ∧ result law = Violated
```

kind別にも同様の witness theorem を置く。

```lean
theorem idempotencyViolationCount_pos_exists :
  idempotencyViolationCount > 0 →
  ∃ law, law.required ∧ law.kind = Idempotency ∧ result law = Violated
```

### 12.4 Counterexample soundness

CLIが valid evidence だけを集計しているという前提のもとで、次を示す。

```text
counterexampleCount > 0
ならば、
少なくとも1つの violated evidence に counterexample witness が存在する。
```

### 12.5 ゼロ違反の非含意

次は成立しない。

```text
violatedLawCount = 0
→
全lawが正しい
```

Lean側では、反例モデルとして次を構成する。

```text
requiredLawCount = 1
violatedLawCount = 0
unmeasuredLawCount = 1
```

これにより、zero violation でも all satisfied ではないことを明示する。

## 13. Phase 1以降の代数法則

MVP後に、各 law kind の理論的意味を Lean 側で追加する。

### Idempotency

```lean
def Idempotent (f : S → S) : Prop :=
  ∀ s, f (f s) = f s
```

証明対象:

```text
Idempotent f なら、任意回 retry しても1回実行と同じ状態になる。
```

### Compensation

```lean
def ObservationalCompensation
  (obs : S → O)
  (f comp : S → S) : Prop :=
  ∀ s, obs (comp (f s)) = obs s
```

証明対象:

```text
補償射が観測同値上の retraction であるなら、失敗 prefix の観測回復が成立する。
```

### Event log homomorphism

```text
project(xs ++ ys) = replayFrom(project(xs), ys)
```

証明対象:

```text
projection が fold として定義されるなら、append 分割に対する homomorphism law が成立する。
```

### Roundtrip

```lean
def RoundTripLeft (encode : A → B) (decode : B → A) : Prop :=
  ∀ a, decode (encode a) = a
```

証明対象:

```text
RoundTripLeft encode decode なら、encode 後 decode で A 側情報は失われない。
```

## 14. Issue分割案

### Issue 1: Algebraic Laws MVP schema and aggregator

内容:

- `architecture-laws/v0`
- `law-evidence/v0`
- `algebraic-signature-v0`
- `algebraic-laws` command
- basic fixtures
- README update

完了条件:

```text
law registry + evidence JSON から algebraic-signature-v0 が生成できる。
```

### Issue 2: Algebraic validate

内容:

- `algebraic-validate` command
- `duplicateLawId`
- `danglingEvidence`
- `unsupportedLawKind`
- `conflictingEvidence`
- `countConsistency`
- `lawDebtDerivedInvariant`

完了条件:

```text
fixtures で pass / warn / fail が安定して出る。
```

### Issue 3: MetricStatus hardening

内容:

- kind別 `metricStatus` rules
- `no-required-laws-for-kind`
- `unmeasured-required-laws-for-kind`
- `lawCoverageRatio` null handling

完了条件:

```text
0がrisk 0なのか、対象law未宣言なのか、未評価なのかを区別できる。
```

### Issue 4: Lean metric semantics

内容:

- `LawResultStatus`
- required law partition
- `lawDebt = unmeasuredLawCount`
- violation count witness theorem
- zero violation does not imply all satisfied

完了条件:

```text
MVP signature count の意味論が Lean で整理される。
```

### Issue 5: Snapshot / diff follow-up

MVP後に、後方互換を守って `signatureArtifacts` の optional 追加を検討する。

```json
{
  "schemaVersion": "signature-snapshot-store-v0",
  "signature": { "... existing sig0 shape ...": "..." },
  "metricStatus": { "... existing metric status ...": "..." },
  "signatureArtifacts": [
    {
      "kind": "sig0",
      "schemaVersion": "archsig-sig0-v0",
      "path": ".lake/sig0.json"
    },
    {
      "kind": "algebraic-laws",
      "schemaVersion": "algebraic-signature-v0",
      "path": ".lake/algebraic-signature.json"
    }
  ]
}
```

既存フィールドは残す。`signatureArtifacts` は optional 追加にする。

## 15. MVP指標一覧

最初のP0指標は次の通り。

```text
declaredLawCount
requiredLawCount
satisfiedLawCount
violatedLawCount
unmeasuredLawCount
lawDebt
lawCoverageRatio
manualEvidenceRatio
counterexampleCount
idempotencyViolationCount
compensationDefectCount
replayHomomorphismDefect
roundtripLossCount
```

必須注記:

- `satisfiedLawCount` / `violatedLawCount` / `unmeasuredLawCount` は law ID 単位。
- `counterexampleCount` は witness 単位。
- kind別 violation metric は required law ID 単位。
- `lawDebt` は `algebraic-signature-v0` では `unmeasuredLawCount` の派生値。
- evidence status は `satisfied | violated | inconclusive` のみ。
- `lawResults` status は `satisfied | violated | unmeasured` のみ。
- `undeclared` は law status ではなく validation / dangling evidence として扱う。

## 16. AI reviewer向け読み方

AI reviewer は signature 値だけで判断せず、必ず `metricStatus` を併読する。

誤読:

```text
idempotencyViolationCount = 0
だから冪等性問題なし。
```

正しい読み方:

```text
idempotencyViolationCount = 0
だが、metricStatus.idempotencyViolationCount.measured = false。
required idempotency law の一部が未評価なので、冪等性リスクは未判断。
```

## 17. 参照

[1]: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/tools/archsig/README.md "AlgebraicArchitectureTheoryV2/tools/archsig/README.md at main"
[2]: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/blob/main/tools/archsig/src/lib.rs "AlgebraicArchitectureTheoryV2/tools/archsig/src/lib.rs at main"
