---
name: issue-creater
description: docs や proof_obligations から未実装・未証明・未整理のタスクを読み取り、重複を避けて GitHub Issue を作成する。Use when the user says "issue-creater", "docs から Issue を作って", "次に実装すべきタスクを Issue 化して", or asks Codex to derive GitHub Issues from repository documentation.
---

# Issue Creater

リポジトリ内の docs を根拠に、次に実装・証明・設計すべきタスクを GitHub Issue として起票する。
このリポジトリでは、応答・Issue タイトル・Issue 本文は日本語で書く。

## 対象入力

- 明示された docs ファイルやセクションがあれば、それを優先する。
- 指定がなければ、まず `docs/proof_obligations.md` を読む。
- 必要に応じて `README.md`, `docs/aat_v2_overview.md`, `docs/research_goal.md`, `docs/design_principle_classification.md` も参照する。
- Lean の識別子、定理名、ファイル名、label 名、milestone 名は英語のまま残してよい。

## 標準手順

1. 現在の作業ツリーを確認する。
   - `git status --short --branch`
   - 未コミット変更があっても勝手に戻さない。
2. docs から候補を抽出する。
   - `future proof obligation`
   - `defined only` から正当性 theorem が必要なもの
   - `empirical hypothesis` のうち tooling / validation task として切れるもの
   - `TODO`, `未解決課題`, `発展課題`, `検討`, `design`
3. 既存 Issue と照合する。
   - `gh issue list --state all --limit 100 --json number,title,state,labels,milestone,url`
   - タイトルが違っても、同じ proof obligation / design decision / empirical task を扱う Issue があれば新規作成しない。
4. Issue 化する候補を絞る。
   - ユーザーが数を指定していなければ、通常は 3-5 件まで。
   - 依存順は `priority:blocking`, `status:ready`, milestone の研究順、後続 Issue をブロックするものを優先する。
5. Issue を作成する。
   - 既存 label / milestone を使う。存在しない label や milestone は、明示依頼なしに増やさない。
   - title / body は日本語。
   - body には `目的`, `背景`, `関連 docs`, `完了条件`, `Lean status` を入れる。
6. docs 側の索引更新が必要なら提案する。
   - ユーザーが依頼している場合だけ docs を編集する。
   - docs を編集したら `git diff --check` と hidden / bidirectional Unicode scan を行う。
7. 作成結果を報告する。
   - 作成した Issue URL
   - 重複として作成しなかった候補
   - 次に着手すべき Issue

## Issue 化の判断基準

- `proved`: 原則として新規 Issue は不要。rename, docs sync, theorem generalization など追加作業が明確な場合だけ候補にする。
- `defined only`: 対応する correctness theorem, API design decision, naming stabilization が残るなら Issue 化する。
- `future proof obligation`: 既存 Issue がなければ Issue 化する。
- `empirical hypothesis`: Lean proof をブロックしない。extractor, dataset, validation protocol, metric definition など tooling / research task として分割できる場合だけ Issue 化する。

## Label / milestone の目安

- Lean theorem: `type:lean-proof`
- 定義や API 設計: `type:definition`
- docs の索引や status 整理: `type:docs`
- 実証研究: `type:research-hypothesis`
- extractor や自動化: `type:tooling`
- 前提タスク: `priority:blocking`
- 高優先だが即ブロックではない: `priority:high`
- 着手可能: `status:ready`
- 設計判断待ち: `status:needs-design`
- 前提 Issue 待ち: `status:blocked`

area label は docs の主題に合わせる。

- finite universe: `area:finite-universe`
- reachability / walk / path: `area:reachability`
- SCC / cycle / depth: `area:scc-depth`
- signature / metrics: `area:signature`
- layering / decomposability: `area:layering`
- projection / observation / DIP / LSP: `area:projection-observation`
- adjacency matrix / nilpotence / spectral: `area:path-matrix`
- empirical extraction / validation: `area:empirical`

## Issue 本文テンプレート

```markdown
目的: ...

背景:
...

関連 docs:
- `docs/proof_obligations.md` の「...」

完了条件:
- ...
- ...

Lean status: future proof obligation.
```

docs にない内容を推測で増やす場合は、本文内で「推定」と分かるように書く。
