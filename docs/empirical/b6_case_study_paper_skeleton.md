# B6 case study paper skeleton

Lean status: `empirical hypothesis` / research validation.

この skeleton は Phase B6 の case study paper / technical note を書くための骨子である。
目的は、Feature Extension Report / Architecture Signature / obstruction profile と
開発 outcome の対応を、反証可能な empirical hypothesis として報告することである。

この文書は theorem proof ではない。Lean theorem package が与える bounded claim と、
tooling output、dataset、review / incident outcome を明確に分ける。

## Working title

Architecture Signature as Multi-Axis Review Evidence: A Phase B6 Case Study

## Abstract

- 対象 repository、期間、PR 件数、Feature Extension Report artifact 数を述べる。
- H1-H5 のうち primary / exploratory / not evaluated を明記する。
- 結果は correlation / descriptive evidence として報告し、causal proof とは書かない。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。

## 1. Introduction

- AAT v2 の研究目標を、設計原則と architecture invariant / obstruction profile の対応として説明する。
- Lean theorem package と empirical validation の責務境界を置く。
- Feature Extension Report を architecture review の evidence artifact として導入する。
- paper の主張範囲を、dataset construction、measurement boundary、H1-H5 の観測結果に限定する。

## 2. Research questions

Phase B6 の研究質問は次である。

| ID | question | expected evidence |
| --- | --- | --- |
| H1 | `non_split` feature extension は review cost や follow-up fix の増加と相関するか。 | split group 別の review / follow-up outcome 分布。 |
| H2 | hidden interaction witness は semantic defect や rollback と相関するか。 | hidden witness count と rollback / follow-up issue の対応。 |
| H3 | runtime exposure witness は incident scope や MTTR と相関するか。 | runtime witness と affected component count / MTTR の対応。 |
| H4 | split extension と判定された PR は後続変更で再利用・置換・移行しやすいか。 | 30 / 90 / 180 日の future co-change、migration、replacement observation。 |
| H5 | Feature Extension Report は architecture review の合意形成を速めるか。 | approval latency、review rounds、architecture discussion thread count proxy。 |

H5 の合意形成は、reviewer の主観ではなく、測定可能な review outcome として扱う。
最小 proxy は approval latency、review round count、review thread count、
architecture-related label / thread count である。

## 3. Dataset boundary

使用する dataset:

- `pr-history-dataset-v0`
- `feature-extension-dataset-v0`
- `outcome-linkage-dataset-v0`
- 必要に応じて `empirical-signature-dataset-v0` と Signature snapshot store

記録する boundary:

- repository、期間、対象 PR、除外 PR。
- extractor version、rule set version、policy version。
- Feature Extension Report schema version と artifact path。
- measured / unmeasured / unavailable / private の区別。
- linked issue / incident / rollback data の欠損理由。
- review policy、incident policy、ownership の期間差分。

`null`、`unmeasured`、`unavailable`、`private` は measured zero として補完しない。

## 4. Method

1. PR history dataset を固定する。
2. 各 PR の Feature Extension Report と theorem precondition boundary を join する。
3. review / follow-up / rollback / incident outcome を outcome linkage dataset に join する。
4. H1-H5 ごとに primary / exploratory / not evaluated を決める。
5. PR size、changed components、reviewer count、repository segment を stratification に残す。
6. 効果量、順位相関、分布差、外れ値、欠損率を報告する。

pilot 件数が小さい場合、多変量モデルや有意差を主張の中心にしない。

## 5. Results skeleton

### H1: split status and review / follow-up cost

- input record count:
- excluded record count and reasons:
- descriptive statistics:
- effect size summary:
- limitations:

### H2: hidden interaction and rollback / semantic defects

- input record count:
- excluded record count and reasons:
- descriptive statistics:
- effect size summary:
- limitations:

### H3: runtime exposure and incident scope / MTTR

- input record count:
- excluded record count and reasons:
- descriptive statistics:
- effect size summary:
- limitations:

### H4: split extension and future reuse / migration

- observation window:
- input record count:
- excluded record count and reasons:
- descriptive statistics:
- effect size summary:
- limitations:

### H5: Feature Extension Report and review consensus speed

- report-present / report-absent grouping:
- input record count:
- excluded record count and reasons:
- descriptive statistics:
- effect size summary:
- limitations:

## 6. Threats to validity

- repository selection bias。
- PR size、team size、review policy、incident policy の交絡。
- extractor rule set の coverage limitation。
- missing / private outcome data。
- follow-up issue と原因 PR の link incompleteness。
- report-present PR が難しい PR に偏る、または逆に review discipline の高い期間に偏る可能性。
- observation window が短い場合、H4 の future reuse / migration を過小評価する可能性。

## 7. Non-conclusions

- causal proof を主張しない。
- theorem proof を追加したとは主張しない。
- extractor completeness を主張しない。
- Feature Extension Report が単独で review latency を改善したとは主張しない。
- Architecture Signature を単一スコアの品質 ranking として扱わない。
- measured witness がないことを universe-wide obstruction absence と読まない。

## 8. Reproducibility checklist

- input dataset artifact paths:
- schema versions:
- extractor / policy versions:
- excluded PR list:
- missing / private data summary:
- analysis script or notebook ref:
- generated summary artifact ref:
