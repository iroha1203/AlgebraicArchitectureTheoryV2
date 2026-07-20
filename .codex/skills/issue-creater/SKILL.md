---
name: issue-creater
description: 指定docsやproof obligationから未実装・未証明・未整理タスクを抽出し、既存Issueとの重複、依存、親子関係、source of truth、タスク型を確認してGitHub Issueを作る。"$issue-creater"、"create issue"、docsからIssueを起票する依頼で使う。実装やPR作成には使わない。
---

# Issue Creater

リポジトリ内の docs を根拠に、次に実装・証明・設計すべきタスクを GitHub Issue として起票する。

## 対象入力

- 明示された docs ファイルやセクションがあれば、それを優先する。
- 指定がなければ、まず `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` を読む。
- 必要に応じて `docs/aat/algebraic_geometric_theory/README.md`, `docs/sft/software_field_theory.md`, `docs/sft/aat_interface.md`, `docs/tool/**`, `README.md`, `README.jp.md` も参照する。
- Issue 本文の構造は `.github/ISSUE_TEMPLATE/implementation_request.yml` と `.github/ISSUE_TEMPLATE/documentation_request.yml` に合わせる。
- 本文の中心は `現状の課題`、`解決方針`、`期待する成果物`、`受け入れ要件`、`備考` とする。
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
   - `gh api --paginate 'repos/{owner}/{repo}/issues?state=all&per_page=100' --jq '.[] | select(.pull_request == null) | {number,title,state,labels:[.labels[].name],milestone:(.milestone.title // null),url:.html_url}'`
   - pagination を最後まで完走し、照合した範囲を報告する。取得不能なら
     重複なしと判定せず停止する。
   - 例外: prd-loop の tracking Issue 配下への sub-issue 起票では、照合範囲を
     tracking Issue の既存 sub-issue と対象 PRD に関連する open Issue に
     限定してよい(全件走査を省略できる)。それ以外の起票は従来どおり全件照合する。
   - タイトルが違っても、同じ proof obligation / design decision / empirical task を扱う Issue があれば新規作成しない。
4. Issue 化する候補を絞る。
   - 候補数は固定しない。docs から抽出した未実装・未証明・未整理タスクを、
     重複を避けながら自然な作業単位で Issue 化する。
   - 依存順は `priority:blocking`, `status:ready`, milestone の研究順、後続 Issue をブロックするものを優先する。
   - 実装変更が必要な候補と、ドキュメント修正だけで閉じてよい候補を分ける。
   - 実装依頼では、docs 更新だけでは完了しないことを本文で明示する。
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
   - タスクに対応するIssue Formのrequired fieldをすべて使い、
     [Issue補助field](references/issue-templates.md)のうち該当するものだけを`備考`へ追加する。
   - `期待する成果物`と`受け入れ要件`は「Issue本文」の規律で検査する。
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

## タスク型宣言(全 Issue 必須)

実装IssueではIssue Formの**タスク型**を選択する。docs Issueはフォームが付ける
title prefix `[doc]`をタスク型宣言として扱う。

- **移植(Research→本体)**: `research/lean/ResearchLean/` の受理成果を本体へ
  蒸留するタスク。必須fieldとResearch下限原則は
  [Issue補助field](references/issue-templates.md#移植issue)をそのまま使う。
  移植元はまず Issue の source-of-truth pointer、次に `research/lean/ResearchLean/` を検索する。
- タスク型を判断する材料が Issue 起票時点で不足している場合は、
  推定と明記した上で最も規律の強い型に倒す(移植の疑いがあれば移植)。

## 是正 Issue の source of truth ポインタ(必須)

既存実装の未達・欠陥を直す是正 Issue は
[Issue補助field](references/issue-templates.md#是正issue)を使い、単体で一次仕様へ
遡れる状態にする。レビュー・実装はコメントの応酬ではなく、その参照先を読む。

## PRD 由来 Issue の規律(prd-loop 連携)

PRD の完了条件を Issue 化する場合に適用する。

- Issueの受け入れ要件には PRD の該当 AC を文言のまま引用する。要約や再表現で弱めない。
- PRD の採否規律(処置の降格が許される対象、anti-weakening 等)を Issue 側で
  拡張・緩和しない。例: PRD が「B級のみ降格可」とする場合、「高コスト項目」などの
  対象拡大を AC に書かない。
- 実装・証明・発火を要求する完了条件に対し、docs / 台帳記載だけで閉じられる
  Issue を作らない。
- 許可外の降格が必要と判明した場合は Issue 化せず、`status:blocked` で
  ユーザー判断を求める。

## Issue 化の判断基準

statusの意味は `docs/aat/guideline.md` の現行 status discipline を正本とする。

- `proved`: 原則として新規 Issue は不要。rename, docs sync, theorem generalization など追加作業が明確な場合だけ候補にする。
- `defined only`: 対応する correctness theorem, API design decision, naming stabilization が残るなら Issue 化する。
- `future proof obligation`: 既存 Issue がなければ Issue 化する。
- `empirical hypothesis`: Lean proof をブロックしない。extractor, dataset, validation protocol, metric definition など tooling / research task として分割できる場合だけ Issue 化する。
- `packaged (assumption-relative)`: 未放電premiseや生成すべきpackageが残るなら、その具体的な放電・構成をIssue化する。
- `statement-only`: 証明または実装のIssueとして扱い、証明済みに数えない。
- `unported (Research-proved)`: 移植Issueとして扱い、別statusへ置換してcloseしない。

## Label / milestone の目安

- 主対象領域に合わせて `area:*` を付ける。formal / doc / tool / website の区別が曖昧な場合は、Issue 本文で主対象領域と影響範囲を明示してから既存 label に寄せる。
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

## Issue本文

`.github/ISSUE_TEMPLATE/`を正本とし、不足fieldは
[references/issue-templates.md](references/issue-templates.md)で補う。
本文は次の責務を混ぜない。

- `現状の課題`: 現在の状態、問題となる理由、確認できる根拠
- `解決方針`: 採用する方向と維持すべき本質的要件
- `期待する成果物`: PRに含める具体的な成果物
- `受け入れ要件`: 成立条件と確認証拠を持つ客観的な完了契約
- `備考`: source of truth、依存、対象外、候補ファイル、補助field

受け入れ要件が成果物より弱い、曖昧、またはbuild / testの通過だけで閉じられる
場合は、そのまま起票せず具体化する。docsにない内容を推測で増やす場合は
「推定」と明記する。
