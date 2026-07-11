---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability, certificate-transport, invariance, profile-curvature, atom-supported-quality-geometry
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-4
tags: [quality-surface, traceability, certificate-transport, profile-curvature, atom-support]
created: 2026-06-20
cycle: 4
lean: proved-in-research
---

# Trace-natural certificate transport bridge

## 主張

有限 profile change に沿って、certificate の supporting atom family を運ぶ atom transport と、
利用可能な trace token を運ぶ trace-token map を固定する。source certificate の support 上で trace field が
定義され、target trace field が atom transport と trace-token map の自然性 square を満たすなら、
transport 後の target support 上でも trace token への追跡可能性は保存される。

主成果は、support transport は保存されていても trace naturality が破れる有限例では、target support に
trace-missing atom が残ることを示す点に置く。保存 theorem は補助結果であり、finite missing-trace witness が
support transport と trace transport を分離する。したがって traceability は certificate tuple の飾りではなく、
profile transport が保つべき certificate geometry の成分である。

## 候補種別

`bridge`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- `docs/note/aat_quality_surface.md` の source reference claim boundary と trace locus
- cycle 1 の `research/lean/ResearchLean/QualitySurface/SupportHitting.lean`
- cycle 3 の `research/lean/ResearchLean/QualitySurface/ProfileCurvature.lean`

## 非自明性

cycle 1 は atom support が repair frontier を制約することを示し、cycle 3 は support / repair の path
discrepancy を profile curvature として固定した。しかし trace field はまだ support transport と結合していない。
この候補は、support を運ぶことと trace token を運ぶことの可換性を naturality 条件として置き、
traceability を certificate transport の保存対象に入れる。さらに、support transport が成立しても
trace naturality がなければ target trace availability は落ちることを finite witness で分離する。

## 数学的興味

AAT 内部が持つのは supporting atom family までであり、source reference への対応は ArchMap / observation
layer が供給する token として扱う。この候補は、source completeness を主張せずに、利用可能な trace token が
profile transport に沿って保存される条件を数学的に固定する。trace naturality が破れる場合、support は運ばれても
trace certificate は transport されず、trace-curvature の候補になる。

## GOAL への前進

traceability / certificate-transport / invariance を増やし、atom-supported quality geometry の certificate tuple
にある trace component を、profile-indexed comparison map と接続する。cycle 3 の profile-curvature detector と、
次の finite trace / measured-zero separation frontier を橋渡しする。

## SCORE 見込み

- `score_reason`: Lean で support transport は成立するが trace naturality が破れる finite missing-trace witness
  を主証拠として固定し、あわせて trace naturality による trace availability preservation を補助定理として証明できれば、
  traceability と transport の未接続 frontier を直接進める。
- `dullness_risk`: trace field を certificate tuple に足すだけでは弱い。atom transport、trace-token map、
  partial trace field、naturality square、missing-trace witness をすべて明示する。
- `proof_or_evidence_plan`: finite source atom / target atom、source trace token / target trace token、
  source support、atom transport、trace-token map、source trace field、target trace field を置く。
  `TraceNatural`、`TraceAvailableOn`、`TransportedSupport`、`TraceMissingOn` を定義する。
  同じ support transport を持つが target trace field が欠ける finite witness を主証拠として置き、
  trace naturality failure と missing trace を証明する。補助的に、自然性から target trace availability が
  保存される theorem を証明する。

## CS / SWE への帰結

品質 certificate が修正対象 atom family を返せても、その atom が利用可能な source reference へ trace できるとは限らない。
trace-natural transport が成り立つ profile change では、support と trace token が一緒に運ばれるため、Quality Surface の
drill-down は repair frontier と説明可能性を同時に保持できる。

## 証明・根拠の見込み

Lean では `TraceAvailableOn support trace`、`TransportedSupport atomMap sourceSupport`、
`TraceNatural sourceSupport atomMap traceMap sourceTrace targetTrace` を定義する。
source support 上の trace availability と trace naturality から target support 上の trace availability を導く。
finite witness では atoms `{a,b}` を target atoms `{a',b'}` へ運び、source trace は両 atom で定義される一方、
target trace が `b'` で欠ける例を置く。support transport は保存されるが、trace naturality は破れ、target support に
trace-missing atom が残ることを証明する。

## 審判メモ

- 厳密性: 初回 `revise`、Lean evidence 後に `accept`。preservation theorem だけでは即時系に近いため、
  finite missing-trace witness を主証拠にすることを要求。base score 55。
- 研究価値: `accept`。base score 70。trace naturality と missing-trace witness により、
  `T_p` を drill-down metadata ではなく certificate transport の保存成分として扱える。
- repo 全体価値: `accept`。base score 70。AAT / SFT / tooling / website の将来 surface に価値があるが、
  現状は toy finite witness であり、ArchMap source ref つき finite codebase trace example ではない。
  SCORE 監査では base 60 / multiplier 2.0 / final 120 に reduce。

## 関連

- `Finite square cell profile-curvature detector`
- `Finite trace-locus certificate example`
- `Measured-zero / unmeasured / trace-missing trichotomy`

## 進捗ログ

- 2026-06-20: cycle 4 の G1 候補生成から審判対象として作成。
- 2026-06-20: G2 revise を受け、主成果を trace availability preservation から
  support transport と trace transport を分離する finite missing-trace witness へ寄せ、expected base score を 70 に調整。
- 2026-06-20: `research/lean/ResearchLean/QualitySurface/TraceTransport.lean` を追加。`lake build ResearchLean`
  pass。G2 再審判は accept。G3 公理検査 pass: requested declarations depend on no axioms。G3 形式化品質監査 pass。
- 2026-06-20: G4 SCORE 監査 reduce: base 60, multiplier 2.0, penalty 0, final 120。
