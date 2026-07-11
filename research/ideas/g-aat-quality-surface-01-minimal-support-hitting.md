---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: obstruction, repair-potential, atom-supported-quality-geometry
expected_base_score: 60
expected_evidence_multiplier: 2.0
expected_final_score: 120
evidence_stage: proved-in-research
origin: G1-quality-surface-cycle-1
tags: [quality-surface, atom-support, repair, obstruction, hitting-set]
created: 2026-06-20
cycle: 1
lean: proved-in-research
---

# Minimal-support hitting theorem for local repair

## 主張

有限 certificate calculus を固定し、obstruction class `[z]` ごとに nonempty antichain としての
minimal atom support family `MinSupportFamily([z])` を持つとする。repair support `H` が
`H` 外の atom support を変えない local repair であるなら、`[z]` を消す repair support `H` は
`MinSupportFamily([z])` の全要素を hit しなければならない。

特に、ある minimal support `M ∈ MinSupportFamily([z])` について `H ∩ M = ∅` なら、
その local repair の後も `[z]` の obstruction は残る。

## 候補種別

`closure`

## 依拠

- `research/goals/G-aat-quality-surface-01.md` の `G-aat-quality-surface-01`
- `docs/note/aat_quality_surface.md` の 10 節 Atom support と 13 節 Atom-support repair theorem
- `Formal/AG/Measurement/SquareFreeRepair.lean` の minimal repair hitting set surface
- `Formal/AG/Measurement/SupportTransfer.lean` の support-localized repair path surface

## 非自明性

support を certificate の付属情報ではなく、repair 不可能性の下界を与える構造的不変量として使う。
minimal support family が複数ある場合、単一 support との交差では足りず、family 全体への hitting
condition が必要になる。この点で、obstruction、minimal representative、repair locality、hitting set
を同じ finite certificate calculus に束ねる。

## 数学的興味

この候補は atom-supported quality geometry の中で、obstruction certificate の support が repair
reachability を制約することを示す。Quality Surface 上では、repair direction が存在する領域と
obstruction が残る領域の境界を、minimal atom support family への hitting condition として読める。

## GOAL への前進

atom support を主成果にしながら、repair reachability を certificate geometry 内の hitting-set
theorem として扱えるようにする。

## SCORE 見込み

- `score_reason`: Lean で finite support locality と hitting-set 必要条件を証明し、複数 minimal support を持つ toy calculus を固定できれば、最初の `proved-in-research` 候補として成立する。
- `dullness_risk`: repair relation の仮定を強くしすぎると「H 外を変えないから残る」という即時系になる。abstract theorem だけでなく、複数 minimal support の finite example を添えて、family 全体への hitting condition を証拠化する。
- `proof_or_evidence_plan`: finite atom type、support predicate、nonempty antichain としての minimal support family、local repair relation を Research 側に抽象化し、`Eliminates` と `RepairLocalOutside` から hitting condition を Lean で証明する。さらに `{a,b}` と `{c}` の二つの distinct minimal support を持つ finite calculus で、family nonempty / antichain、`{a}` repair が obstruction を残すこと、`{a,c}` repair が hitting condition を満たすことを固定する。

## CS / SWE への帰結

修正案が obstruction certificate の minimal atom support family に触れていない場合、その修正は対象 obstruction を消せない。
これにより、品質判定は単なる違反数ではなく、どの atom family を hit しなければならないかという repair
frontier を返せる。

## 証明・根拠の見込み

Research 側では、obstruction class `c`、nonempty antichain としての support family
`S : Set Atom -> Prop`、repair support `H : Set Atom`、repair 後の support family `S'` を抽象化する。
locality は `H` と交わらない support
が repair 後にも残るという命題で表す。`Eliminates H c` は repair 後の minimal support family が空になる
こととして置く。このとき `H` と交わらない `M ∈ MinSupportFamily(c)` があれば locality により
`M` が repair 後にも残るため、`Eliminates H c` と矛盾する。従って `Eliminates H c` なら全ての
minimal support `M` が `H` と交わる。

## 審判メモ

- 厳密性:
- 研究価値:
- repo 全体価値:

## 関連

- scalar-collapse separation by support antichains
- finite profile-curvature detector on a square cell
- trace-natural certificate transport bridge

## 進捗ログ

- 2026-06-20: G1 候補生成から cycle 1 の審判対象として作成。
- 2026-06-20: G2 三審判後に picked。A の revise を受け、traceability を主 category から外し、finite two-support Lean example を追加。
- 2026-06-20: G3 axiom check / 形式化品質監査 pass。G4 SCORE 監査 confirm: base 60, multiplier 2.0, penalty 0, final 120。
