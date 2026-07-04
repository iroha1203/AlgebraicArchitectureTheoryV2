---
status: picked
goal: G-sft-conway-01
exploration_role: obstruction
candidate_type: bridge
capability_category:
  - restricted-span
  - conway-obstruction
  - projection-nonfaithfulness
  - local-global-boundary
expected_base_score: 45
expected_evidence_multiplier: 2.0
expected_final_score: 90
evidence_stage: proved-in-research
rival_advantage: Team Topologies / CODEOWNERS / org-network analysis can show local owners, but do not prove that owner-uniform subfamily support fails to glue to one family-level owner.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
origin: G-sft-conway-01 Cycle 16
tags: [conway, owner-uniform, descent, restricted-span]
created: 2026-07-04
---

# Owner-uniform subfamily descent failure

## 主張

Cycle 15 の restricted two-fork family を、API singleton subfamily と DB singleton subfamily に分ける。
それぞれの singleton subfamily は owner-uniform coherent common-refinement support を持つが、両方を
含む full family は owner-uniform coherent support を持たない。したがって owner-uniform support は
forkwise local support だけでなく、selected subfamily cover 上の局所 support からも自動では貼り合わない。

ここでいう `descent failure` は、selected finite subfamily cover 上の receiver であり、overlap
compatibility、arbitrary cover naturality、quotient object、true sheaf `H^1` は主張しない。

## 候補種別

`bridge`

## 依拠

- `Formal/AG/Research/SFT/ConwayRestrictedCoherentFamily.lean`
- Cycle 14: unrestricted coherent support は forkwise local support から Sigma assembly できる
- Cycle 15: restricted two-fork family は forkwise local support を持つが owner-uniform coherent support を持たない

## 非自明性

Cycle 15 は full family の negative receiver だった。この候補はそれを selected subfamily cover 上の
descent failure に上げる。各 subfamily では owner-uniform support が明示的に存在するため、単に
「各 fork が local support を持つ」という弱い言い換えではなく、restricted owner-uniform support
そのものの局所成立と大域不成立を分離する。

## 数学的興味

owner-uniform support は ordinary coherent support より強いだけでなく、subfamily cover に対しても
descent data を要求する構造である。局所 subfamily support の存在を、大域 owner-uniform support と
同一視できないことが、true quotient / sheaf `H^1` へ進む前の有限比較 functor 失敗として読める。

## GOAL への前進

`restricted-span` と `local-global-boundary` の能力を増やし、Cycle 15 の restricted local/shared separation を
subfamily descent obstruction として phase-boundary 向け statement にする。

## ライバルに対する有効性

Team Topologies、CODEOWNERS、org-network analysis、AI review は「API には API owner、DB には DB owner がいる」
という局所 support を返せる。しかしこの候補は、局所 subfamily support があっても family-level の
shared owner witness が存在しないことを Lean theorem として固定する。これは mismatch visualization ではなく、
選択済み subfamily cover からの owner-uniform gluing failure である。

## SCORE 見込み

- `score_reason`: Cycle 15 の反例を、selected finite subfamily cover 上の local-support / full-family failure receiver として固定した。ただし Cycle 15 の negative theorem に近く、arbitrary cover naturality や quotient object には届かないため base45 に下げる。
- `dullness_risk`: singleton support の存在だけなら Cycle 15 の補足に留まる。`SupportForkFamilySubcover` と `OwnerUniformSubfamilyDescentFailure` によって、selected finite subfamily-cover receiver として限定して読む。
- `proof_or_evidence_plan`: `Formal/AG/Research/SFT/ConwayOwnerUniformSubfamilyDescent.lean` で `restrictedApiSingletonFamily` と `restrictedDbSingletonFamily` を定義し、それぞれの owner-uniform support を構成した。full family については Cycle 15 の `restrictedTwoForkFamily_notOwnerUniformCoherent` を接続し、local subfamily support だが full family owner-uniform support なしの receiver を証明した。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## CS / SWE への帰結

局所的には各 bounded team / subsystem に coherent owner がいても、それらを一つの owner-uniform Conway witness
として貼り合わせるには追加の共有 owner / transport 条件が必要である、と有限 theorem として言える。

## 証明・根拠の見込み

Lean で次を固定した。

- `restrictedApiSingletonFamily`
- `restrictedDbSingletonFamily`
- `SupportForkFamilySubcover`
- `OwnerUniformSubfamilyDescentFailure`
- `restrictedApiSingletonFamily_ownerUniformSupport`
- `restrictedDbSingletonFamily_ownerUniformSupport`
- `restrictedSingletonSubfamilies_cover`
- `restrictedSingletonSubfamilies_ownerUniformSupport`
- `restrictedTwoForkFamily_ownerUniformSubfamilyDescentFailure`
- `selectedOwnerUniformSubfamilyDescentPackage`

## 審判メモ

- 厳密性: revise, base 45。`descent` を selected finite subfamily cover receiver に限定すること。
- 研究価値: accept, base 50。Cycle 15 に近いため base 65 は高い。
- repo 全体価値: revise, base 50。subfamily cover / descent receiver を明示すれば通せる。
- ライバル比較: accept, base 60。local owner support と family-level owner-uniform gluing failure の分離に価値あり。

## 監査メモ

- G3 axiom audit: pass。`SupportForkFamilySubcover` と `OwnerUniformSubfamilyDescentFailure` は axiom-free。
  reported finite package は `propext` のみに依存し、`sorryAx`、`Classical.choice`、`Quot.sound` はない。
- G3 formalization quality: pass。`selectedOwnerUniformSubfamilyDescentPackage` は、selected singleton
  subfamily cover、各 singleton の owner-uniform support、full `restrictedTwoForkFamily` の
  owner-uniform support 不存在を固定しており、修正後 claim boundary と一致する。
- G3.5 sync audit: synced。候補カード、Lean evidence、report、G2/G3/G4 の score と claim boundary は一致する。
- G4 SCORE audit: confirm。base 45、evidence multiplier 2.0、penalty 0、final +90。

## 関連

- `research/ideas/g-sft-conway-01-owner-uniform-restricted-family.md`
- `research/ideas/g-sft-conway-01-coherent-family-local-exactness.md`

## 進捗ログ

- 2026-07-04: Cycle 16 候補として作成。
- 2026-07-04: G2 revise を反映し、selected finite subfamily-cover receiver に限定。Lean evidence を追加し、base45/final90 に同期。
