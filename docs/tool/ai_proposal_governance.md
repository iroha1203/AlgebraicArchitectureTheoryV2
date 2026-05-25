# AI Proposal Governance Protocol

この文書は、AI-mediated software evolution を SFT の bounded field model 内で
governance するための protocol を定義する。対象は AI proposal stream の
input-output-boundary、allowed operation support、shortcut witness、review / CI feedback、
posterior field update であり、一般的な AI safety theorem、LLM benchmark、
または autonomous coding policy の本番運用を主張しない。

Lean status: `empirical hypothesis` / tooling design.

## Scope

AI proposal governance は、AI agent の出力を architecture lawfulness と同一視せず、
proposal がどの field boundary で作られ、どの operation support に属し、
どの review / CI mediation を受け、どの evidence として field memory に残るかを記録する。

| 入力 | 役割 |
| --- | --- |
| Prompt / policy ref | AI agent に与えた目的、禁止事項、review requirement を記録する。 |
| Source artifact refs | PRD、Issue、Spec、design memo、既存 code refs を proposal context として保持する。 |
| AI proposal JSON / patch refs | generated operation candidate、scope、claim、missing evidence を保持する。 |
| AAT theorem boundary refs | formal/proved claim と未 discharge precondition を分ける。 |
| SFT forecast artifact refs | `ArtifactDescriptor`、`OperationSupportEstimate`、`ConsequenceEnvelope` を接続する。 |
| Review / CI refs | human review、test、type check、policy decision、blocked reason を feedback として保持する。 |
| Observed outcome refs | merge、rework、rollback、incident、follow-up issue を posterior evidence として保持する。 |

## Input-Output Boundary

最小 protocol は次の 7 段階である。

```text
prompt / policy boundary
  -> proposal source normalization
  -> allowed operation support check
  -> shortcut witness classification
  -> review / CI mediation
  -> posterior field update
  -> calibration / benchmark linkage
```

各段階の境界は次の通りである。

| 段階 | 入力 | 出力 | 境界 |
| --- | --- | --- | --- |
| Boundary capture | prompt、policy、source refs、agent metadata | governance boundary record | policy compliance は architecture lawfulness ではない。 |
| Source normalization | AI proposal JSON / patch refs | `artifact-descriptor-v0` candidate | supplied artifact の正規化であり、model evaluation ではない。 |
| Support check | descriptor + policy constraints | bounded allowed / forbidden / unknown support | accepted PR history や actual future support ではない。 |
| Shortcut classification | support estimate + theorem / forecast boundary | shortcut witness report | witness candidate であり、semantic unsafety の証明ではない。 |
| Review mediation | witness report + review / CI refs | review / CI intervention record | reviewer decision を補助する artifact であり、自動 governance correctness ではない。 |
| Field update | intervention + observed outcome refs | posterior field update note | field memory update であり、causal proof ではない。 |
| Calibration linkage | forecast / witness refs + observed refs | benchmark input | `docs/tool/sft_calibration_benchmark.md` の held-out protocol で読む。 |

## Allowed Operation Support

allowed operation support は、AI proposal が selected boundary の下で許可される可能性がある
operation family を列挙するための estimate である。これは reviewer が確認する
bounded candidate set であり、AI agent へ無条件の実行権限を与えるものではない。

| Category | 読み |
| --- | --- |
| allowedCandidate | policy、scope、source refs と矛盾しない candidate operation。 |
| conditionallyAllowed | theorem precondition、test、owner review、issue split などの条件付き candidate。 |
| forbiddenSupport | policy、architecture rule、known invariant boundary と衝突する candidate。 |
| unknownSupport | evidence が足りず、allowed / forbidden に分類しない candidate。 |
| outOfScope | prompt / issue / selected universe の外側にある candidate。 |

allowedCandidate は lawfulness proof ではない。conditionallyAllowed は、必要な review、
test、type boundary、theorem precondition、runtime guard を明示する。
unknownSupport と outOfScope は safe path へ丸めず、review / issue decomposition の入力として残す。

## Shortcut Witness Taxonomy

shortcut witness は、AI proposal が local pattern を増幅し、低コストに見えるが
architecture boundary を越える可能性がある path を示す report item である。
allowed operation support と shortcut witness は別物として扱う。

| Witness | 読み |
| --- | --- |
| forbidden-edge shortcut | 禁止された依存方向、layer bypass、adapter bypass に接続する candidate。 |
| missing-invariant shortcut | 必要な invariant、type boundary、test boundary が未提示の candidate。 |
| hidden-state shortcut | state transition、migration、rollback、idempotency を暗黙化する candidate。 |
| runtime-boundary shortcut | timeout、retry、ownership、incident response など runtime governance を落とす candidate。 |
| theorem-boundary shortcut | formal/proved claim の precondition を満たさないまま theorem language を使う candidate。 |
| review-load shortcut | large patch、mixed concern、ambiguous source refs により review mediation を弱める candidate。 |

shortcut witness は review cue であり、AI model が危険であることや proposal が必ず失敗することを
証明しない。後続の review / CI / incident trace と対応付けて初めて empirical benchmark の
入力になる。

## Review / CI Feedback Update

review / CI feedback は、proposal を単に pass / fail へ分類するためではなく、
field の operation support、selection policy、observation boundary を更新するために保存する。

```text
AI proposal
  + allowed / forbidden / unknown support
  + shortcut witness report
  + review / CI outcome
  -> posterior field update note
```

posterior update は少なくとも次を区別する。

| Update | 読み |
| --- | --- |
| accepted lawful path | reviewer / CI が条件を確認し、bounded support 内で採用された path。 |
| redirected path | issue split、design clarification、test addition、owner review へ誘導された path。 |
| blocked shortcut | forbidden / missing boundary により止めた candidate。 |
| inconclusive | evidence が足りず、accepted / blocked の学習信号として使わない item。 |
| false positive / false negative candidate | held-out protocol で後から分類する benchmark input。 |

この update は causal theorem ではない。feedback は future policy tuning と
`SoftwareFieldEstimate` の field-memory evidence として読む。

## Artifact Plan

Rust tooling では `ai-proposal-governance-v0` を最小 projection として追加し、
既存 artifact の source refs と boundary field を接続して AI governance を表す。

| Artifact | 用途 |
| --- | --- |
| `artifact-descriptor-v0` | AI proposal JSON / patch refs、prompt / policy refs、missing evidence を保持する。 |
| `operation-support-estimate-v0` | allowed / forbidden / unknown support、policy constraints、unknown remainder を保持する。 |
| `consequence-envelope-report-v0` | affected axes、obstruction candidates、theorem boundary、review / CI recommendation を保持する。 |
| `forecast-calibration-hook-v0` | shortcut witness refs と observed PR / review / CI / outcome refs を対応付ける。 |
| `ai-proposal-governance-v0` | prompt / policy boundary、allowed / conditionallyAllowed / forbidden / unknown / outOfScope support、shortcut witness、review / CI mediation、posterior field update を保持する。 |
| B10 / B11 operational artifacts | review mediation、incident、rollback、ownership boundary、hypothesis refresh を保存する。 |

この governance artifact でも、AI policy compliance、review pass、CI pass、schema validation pass を
architecture lawfulness や forecast correctness に昇格しない。

## Non-Conclusions

この protocol は次を結論しない。

- AI agent の一般的安全性。
- prompt / policy compliance からの architecture lawfulness。
- review pass / CI pass からの semantic preservation。
- AI proposal JSON adapter による model capability evaluation。
- shortcut witness と incident / rollback / MTTR の因果関係。
- unavailable / private / unknown support の安全性。
- autonomous coding policy の本番 governance correctness。


## FieldSig boundary

FieldSig lives in `tools/fieldsig` and owns SFT software evolution measurement artifacts: `software-field-measurement-v0`, forecast / intent artifacts, workflow evidence refs, operational feedback, governance candidates, unknown remainder, and calibration hooks. ArchSig remains the AAT structural telemetry generator and passes evidence through JSON artifact refs. FieldSig validation is not a Lean proof, forecast correctness proof, probability claim, causal theorem, or replacement for CI, tests, and human review.
