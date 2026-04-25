---
name: issue-creater
description: docs や proof_obligations から未実装・未証明・未整理のタスクを読み取り、重複を避け、必要なら新規 Issue を sub-issue の親子構造で整理して作成する。Use when the user says "issue-creater", "create-issue", "docs から Issue を作って", "次に実装すべきタスクを Issue 化して", or asks Codex to derive GitHub Issues from repository documentation.
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
5. 新規作成する Issue の親子構造を計画する。
   - 既存 Issue 群をまとめ直すだけの大規模な整理は、明示依頼がない限り行わない。
   - 新規 Issue を作るときは、Codex が既存の親 Issue に追加するか、新規親 Issue を作るか、親なしで作るかを判断する。
   - 既存の親 Issue が同じ研究テーマ・milestone・完了条件を自然に包含するなら、新規 Issue をその親の sub-issue にする。
   - 既存の親 Issue では範囲がずれるが、同じ研究テーマや milestone に属する新規子タスクが 2 件以上ある場合は、親 Issue を 1 件作る。
   - 単独で完結する小さなタスク、または既存親にも新規親にも自然に収まらないタスクは、親なしで作る。
   - 親 Issue は tracking / epic として、目的、背景、子タスク一覧、完了条件を持つ。
   - 子 Issue は実装・証明・docs・tooling の単位まで小さく切る。
   - 既存 Issue と重複する候補は作成しない。既存 Issue を親子構造へ組み込み直す必要がある場合は、別の改善タスクとして扱う。
6. Issue を作成する。
   - 既存 label / milestone を使う。存在しない label や milestone は、明示依頼なしに増やさない。
   - title / body は日本語。
   - body には `目的`, `背景`, `関連 docs`, `完了条件`, `Lean status` を入れる。
   - 新規親 Issue を作る場合は、親 Issue を先に作り、その後で子 Issue を作る。
   - 新規親 Issue の初回本文では、子タスク名だけを仮一覧にしてよい。
   - 子 Issue の本文には、親 Issue が決まっている場合は `親 Issue: #N` を入れる。
   - 既存親 Issue に新規子 Issue を追加する場合、必要なら子 Issue 本文の `親 Issue: #N` で関係を明示する。
7. 親 Issue が決まっている場合のみ、新規 Issue を sub-issue として紐付ける。
   - 親なしで作ると判断した Issue では、この手順をスキップする。
   - `gh issue` に sub-issue 専用コマンドがない場合は REST API を `gh api` で呼ぶ。
   - 子 Issue の REST `id` を取得する。
     - `gh api repos/:owner/:repo/issues/<child-number> --jq .id`
   - 親 Issue に子 Issue を追加する。
     - `gh api -X POST repos/:owner/:repo/issues/<parent-number>/sub_issues -F sub_issue_id=<child-rest-id>`
   - 子 Issue に既に別の親がある可能性がある場合、明示依頼なしに `replace_parent=true` は使わない。
   - sub-issue 紐付けに失敗した場合は、Issue 本文内リンクだけで代替せず、失敗理由を報告する。
   - 新規作成した親 Issue は、子 Issue 番号が確定した後に `gh issue edit <parent-number> --body-file <file>` で子 Issue 一覧を更新してよい。
   - 既存親 Issue に新規子 Issue を追加した場合、親 Issue の本文更新が親子関係の理解に必要なら Codex 判断で最小限更新してよい。
8. docs 側の索引更新が必要なら提案する。
   - ユーザーが依頼している場合だけ docs を編集する。
   - docs を編集したら `git diff --check` と hidden / bidirectional Unicode scan を行う。
9. 作成結果を報告する。
   - 作成した Issue URL
   - 作成した親子構造
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

### 子 Issue

```markdown
目的: ...

背景:
...

親 Issue: #N

関連 docs:
- `docs/proof_obligations.md` の「...」

完了条件:
- ...
- ...

Lean status: future proof obligation.
```

docs にない内容を推測で増やす場合は、本文内で「推定」と分かるように書く。

### 親 Issue

```markdown
目的: 関連する Issue 群をまとめ、依存順と完了条件を明確にする。

背景:
...

子 Issue:
- [ ] #N ...
- [ ] #N ...

関連 docs:
- `docs/proof_obligations.md` の「...」

完了条件:
- 子 Issue がすべて完了している。
- docs / Lean status が子 Issue の結果と一致している。

Lean status: docs index / design tracking.
```
