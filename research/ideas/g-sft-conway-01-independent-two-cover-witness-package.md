---
status: picked
goal: G-sft-conway-01
exploration_role: closer / obstruction / unifier / wildcard convergence
candidate_type: closure
capability_category: two-topology-comparison, conway-obstruction, finite-witness, reorg-refactor-duality, projection-nonfaithfulness, rival-separation
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
lean: proved-in-research
cycle: 1
score_reason: GOAL の初回採否条件である独立二被覆、適合例と障害非零例の対、定義循環回避、reorg/refactor 双対の入口を一つの Lean witness package に固定する。ただし refinement / common refinement / nerve map と障害類の受け皿は未固定なので base は 75 に下げる。
mathematical_interest: Conway 対応を経験的 mirroring 主張ではなく、独立に宣言された二つの finite cover の比較と obstruction witness として扱う。
goal_advancement: G-sft-conway-01 の two-topology-comparison、conway-obstruction、finite-witness、reorg-refactor-duality を同時に立ち上げる。
dullness_risk: cover record の定義だけなら低価値だが、零例、非零例、片側 repair、ownership-index 自明化を theorem として同時に固定しているため回避する。
proof_or_evidence_plan: Formal/AG/Research/SFT/ConwayTwoTopology.lean に `TwoCoverAtlas`、`ConwayObstructionWitness`、`compatibleAtlas_zeroConwayObstruction`、`mismatchedAtlas_nonzeroConwayObstruction`、`reorgedAtlas_zeroConwayObstruction`、`refactoredAtlas_zeroConwayObstruction`、`ownershipIndexedFromCommunication_zeroConwayObstruction`、`selectedConwayTwoCoverWitnessPackage` を未証明穴なしで置く。
planned_theorem_names: TwoCoverAtlas, ConwayObstructionWitness, compatible_no_conwayObstruction, compatibleAtlas_zeroConwayObstruction, mismatchedAtlas_allCommunication_notSupported, mismatchedAtlas_nonzeroConwayObstruction, mismatchedAtlas_notCommunicationCompatible, reorgedAtlas_zeroConwayObstruction, refactoredAtlas_zeroConwayObstruction, ownershipIndexedFromCommunication_zeroConwayObstruction, selectedConwayTwoCoverWitnessPackage
rival_advantage: Team Topologies、mirroring 研究、CODEOWNERS / org-network dashboard、AI review は不一致を指摘または可視化できるが、独立 cover 条件下の zero/nonzero witness と退化的 ownership-indexing の分離を Lean theorem として返さない。
visible_projection: communication cover と ownership cover の membership table。
protected_structure: cover independence、communication block support、selected obstruction witness、片側 repair でどちらの cover を動かしたか。
exactness_or_minimality_claim: selected finite family では communication block が単一 owner support を持つと obstruction は消え、split ownership に対する all-communication block は support を持たない。
nonfaithfulness_or_failure_mode: ownership を communication index から導くと obstruction が定義上消え、Conway 問題が自明化する。
previous_cycle_delta: cycle 0 / SCORE 0 から、初回 proved-in-research finite witness package を追加する。
rival_stress_test: 同じような ownership 表や不一致説明でも、independence provenance と support obstruction を保持しない rival はこの zero/nonzero 分離を theorem として保持できない。
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
tags: [sft, conway, two-topology, finite-witness]
created: 2026-07-04
---

# 独立二被覆の正準有限 witness package

## 主張

有限 context family 上で、communication cover と ownership cover を独立データとして持つ
`TwoCoverAtlas` を置く。communication block が単一 ownership block に支えられるとき
selected Conway obstruction witness は存在しない。一方、同じ有限二 module family で、
communication 側が両 module を一つの block として見て、ownership 側が二つに割れる場合、
単一 owner support が存在せず、selected Conway obstruction witness が存在する。

さらに、その mismatch は communication 側を ownership 側へ割る `reorgedAtlas` でも、
ownership 側を communication 側へまとめる `refactoredAtlas` でも消える。最後に、
ownership index を communication index から導く退化 construction では obstruction が
定義上消えることを示し、GOAL が禁じる定義循環を finite theorem として分離する。

## 候補種別

`closure`

## 依拠

- `research/GOALS.md` の `G-sft-conway-01`
- `docs/sft/software_field_theory.md` 第V部予告
- `docs/note/sft_development_spacetime_dynamics_skeleton.md` 第V部 Conway 対応

## 非自明性

単に cover record を置くのではなく、零例、非零例、reorg/refactor の片側 repair、退化的
ownership-indexing の自明化を一つの Lean package で同時に固定する。これにより、Conway
対応が「ownership を architecture cover index として定義したから成立する」という循環を避ける。

## 数学的興味

Conway 対応を mirroring の経験則ではなく、二つの独立 selected cover の比較問題として立てる。
最初の obstruction は cohomology 名から始めず、finite communication block support の失敗として
固定される。

## GOAL への前進

`two-topology-comparison`、`conway-obstruction`、`finite-witness`、`reorg-refactor-duality` の
初回 proved-in-research 証拠を与える。

## ライバルに対する有効性

組織設計論や mirroring 研究は対応関係を語れる。CODEOWNERS / org-network dashboard は所有と
コミュニケーションの差分を可視化できる。AI review は不一致を自然言語で指摘できる。しかし、
この候補は「独立 cover として置く場合は非零 witness が残るが、ownership を communication
index から導くと自明に消える」という theorem-level の分離を持つ。

## SCORE 見込み

- `score_reason`: GOAL rubric の 80-100 帯のうち、受け皿つき障害類までは未到達だが、適合例と非零例の対、定義循環回避、片側 repair を proved-in-research として固定する。
- `dullness_risk`: record 定義だけなら低価値。`selectedConwayTwoCoverWitnessPackage` が通っていることを SCORE の根拠にする。
- `proof_or_evidence_plan`: `lake env lean Formal/AG/Research/SFT/ConwayTwoTopology.lean` と `lake build FormalAGResearch` で検証する。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## CS / SWE への帰結

Conway 対応を実組織の因果主張として扱わず、選択された communication cover と ownership cover の
finite mismatch として扱える。reorg と refactor は、この selected mismatch をどちら側の cover
編集で消すかという二方向として読める。

## 証明・根拠の見込み

Lean file:

- `Formal/AG/Research/SFT/ConwayTwoTopology.lean`

Lean declarations:

- `Formal.AG.Research.SFT.ConwayTwoTopology.compatible_no_conwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.compatibleAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_nonzeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.mismatchedAtlas_notCommunicationCompatible`
- `Formal.AG.Research.SFT.ConwayTwoTopology.reorgedAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.refactoredAtlas_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.ownershipIndexedFromCommunication_zeroConwayObstruction`
- `Formal.AG.Research.SFT.ConwayTwoTopology.selectedConwayTwoCoverWitnessPackage`

## 審判メモ

- 厳密性: accept。finite support-obstruction witness として claim boundary 内。`independent` は structural selected-data independence であり provenance independence ではない。`reorg/refactor` は一般操作でなく example atlas。
- 研究価値: accept。base 75。初回 foothold として高価値だが、受け皿つき障害類や nerve mismatch には未到達。
- repo 全体価値: accept。base 80。SFT 第V部を Lean-backed research surface へ動かすが、操作論はまだ薄い。
- ライバル比較: accept。base 80。rival の可視化・自然言語指摘に対し zero/nonzero theorem package と ownership-indexing 退化の分離を与える。
- G3 Lean 形式化品質監査: pass。候補の有限 selected two-cover witness package を適切な強さで表現している。
- build / placeholder scan: `lake env lean Formal/AG/Research/SFT/ConwayTwoTopology.lean` と `lake build FormalAGResearch` が通過。対象 Lean file に `axiom/admit/sorry/unsafe` はない。
- axiom audit: pass。`selectedConwayTwoCoverWitnessPackage` と `mismatchedAtlas_nonzeroConwayObstruction` は `propext` に依存。`ownershipIndexedFromCommunication_zeroConwayObstruction` は axiom-free。G3 公理検査は `propext` を Prop 外延性の標準依存として許容した。

## 関連

G1 の four-lane exploration は、closer / obstruction / unifier / wildcard の全てで、この finite
two-cover witness package を初回 picked として推奨した。

## 進捗ログ

- 2026-07-04: 作成。`lake env lean Formal/AG/Research/SFT/ConwayTwoTopology.lean` と `lake build FormalAGResearch` 通過。G2 四審判は accept、G3 形式化品質監査と公理検査は pass。G3.5 初回同期監査の revise 指摘により theorem 名と axiom audit 状態を更新。
