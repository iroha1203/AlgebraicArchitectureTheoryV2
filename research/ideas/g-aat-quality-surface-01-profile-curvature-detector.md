---
status: picked
goal: G-aat-quality-surface-01
candidate_type: computability
capability_category: profile-curvature, certificate-transport, computability, ridge-fold, repair-potential
expected_base_score: 85
expected_evidence_multiplier: 2.0
expected_final_score: 170
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-3
tags: [quality-surface, profile-curvature, certificate-transport, support-antichain, repair]
created: 2026-06-20
cycle: 3
lean: proved-in-research
---

# Finite square cell profile-curvature detector

## 主張

有限二次元 profile square を固定する。横方向の profile change を `u`、縦方向を `v` とし、
四つの edge comparison map を明示し、二つの経路合成

```text
Phi_v' o Phi_u
Phi_u' o Phi_v
```

が同じ初期 certificate を右上 profile の certificate space へ transport するとする。
regular square cell は、二つの path composite が full certificate geometry
(selected scalar reading、verdict、selected minimal atom support antichain、repair hitting requirement)
を一致させる square として定義する。二つの合成後 certificate が同じ scalar reading と verdict を持っていても、
selected minimal atom support antichain または repair hitting requirement が異なるなら、その square は
path coherence を満たさず、profile-curvature cell である。

## 候補種別

`computability`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- `docs/note/aat_quality_surface.md` の profile curvature、finite profile grid、regular cell / curvature cell
- cycle 1 の `research/lean/ResearchLean/AG/QualitySurface/SupportHitting.lean`
- cycle 2 の `research/lean/ResearchLean/AG/QualitySurface/ScalarCollapse.lean`

## 非自明性

各 profile 頂点の測定値を並べるだけではなく、四つの edge comparison map と二つの path composite が
certificate geometry をどう運ぶかを比較する。scalar reading と verdict が一致しても、support antichain と
repair hitting requirement が一致しない場合を検出するため、単なる noncommuting function の有限例ではなく、
cycle 1 / 2 で固定した support / repair frontier を path-ordered transport の coherence failure として読む。

## 数学的興味

Quality Surface を surface と呼ぶための二次元性は、値の grid ではなく、square transport の整合性にある。
この候補は、cover refinement と law strengthening の順序が同じ scalar view に落ちても、背後の
certificate support と repair frontier を異なる位置へ送る有限例を固定する。これにより
`profile curvature` が可視化上の比喩ではなく、certificate transport の非可換性として現れる。

## GOAL への前進

profile-curvature / certificate-transport / computability のカテゴリを直接増やし、既存の
support-local repair theorem と scalar-collapse counterexample を、有限二次元 Quality Surface 上の
curvature detector へ接続する。

## SCORE 見込み

- `score_reason`: finite profile square と Lean proof で、二つの profile change order が同じ scalar / verdict
  へ落ちながら異なる support / repair frontier を作ることを固定できれば、GOAL の profile curvature
  frontier を直接進める。
- `dullness_risk`: 単に二つの関数値が異なるという例や、cycle 2 の endpoint certificate に square label を
  貼っただけの例に落ちると弱い。四つの edge comparison map、二つの path composite、regular square の
  full-certificate coherence 条件を明示し、scalar view では見えない二次元 transport の欠陥として述べる。
- `proof_or_evidence_plan`: finite square profile、四つの edge transport、右上への二つの path transport、
  finite certificate tuple を Lean Research 側に置く。二つの path transport 後 certificate が同じ
  scalar reading / verdict を持つこと、support family と repair hitting requirement が異なること、
  support family が nonempty antichain であること、regular square cell が full certificate geometry の
  path coherence を要求すること、従ってこの square が regular cell でなく curvature cell であることを証明する。

## CS / SWE への帰結

law universe を先に強めてから cover を細かくした場合と、その逆の場合で、同じ品質点・同じ verdict
に見えても、修正が hit すべき atom family が変わることを説明できる。Quality Surface の UI は
profile grid の高さだけでなく、edge transport と square curvature を保持する必要がある。

## 証明・根拠の見込み

Lean では `SquareProfile` と `SquareCertificate` を有限型として置く。四辺の transport
`transportLawBottom`、`transportCoverLeft`、`transportCoverRight`、`transportLawTop` を定義し、
同じ初期 certificate から右上へ行く二つの path composite を `lawThenCover` と `coverThenLaw` として定義する。
両者の scalar reading と verdict が一致する一方で、selected support family と repair hitting number が異なる
finite witness を作る。さらに `RegularSquareCell` を path transport 後の full certificate geometry が一致すること、
`CurvatureCell` を path coherence failure として定義し、support / repair discrepancy が regularity を破ることを示す。
最後に `same_scalar_verdict_but_curved_square` と
`curvatureCell_of_supportRepair_path_discrepancy` を証明する。

## 審判メモ

- 厳密性: 初回と再審判は `revise`。四辺の edge transport、二つの path composite、full-certificate
  regularity、support / repair discrepancy を Lean で明示することを要求。G3 で typed `CertificateAt`
  と `EdgeTransport` を導入し、公理検査 pass。
- 研究価値: `accept`。base score 85。support-local repair と scalar-collapse を profile-curvature
  detector へ圧縮し、Quality Surface の二次元性を square transport coherence として固定する。
- repo 全体価値: `accept`。base score 85。AAT Research / Lean / paper seed の前進として自然で、
  tooling / website へは将来 surface の設計根拠として接続可能。ただし現サイクルでは tooling claim
  へ直結させない。

## 関連

- `Minimal-support hitting theorem for local repair`
- `Scalar-collapse separation by support antichains`
- `Trace-natural certificate transport bridge`
- `Measured zero / unmeasured / trace-missing separation`

## 進捗ログ

- 2026-06-20: cycle 3 の G1 候補生成から審判対象として作成。
- 2026-06-20: G2 revise を受け、証拠段階を `none` に戻し、四つの edge transport、二つの path composite、
  regular square の full-certificate coherence 条件、curvature cell の path coherence failure を主張に明示。
- 2026-06-20: `research/lean/ResearchLean/AG/QualitySurface/ProfileCurvature.lean` を追加。`lake build ResearchLean`
  pass。G3 公理検査 pass: requested declarations depend on no axioms。G3 形式化品質監査 pass。
