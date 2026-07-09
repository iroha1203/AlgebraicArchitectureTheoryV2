---
name: issue-creater
description: docs / proof_obligations から未実装・未証明・未整理タスクを抽出し、重複を避けて GitHub Issue 化する。"issue-creater"、"create-issue"、docs から Issue を作る依頼で使う。
---

# Issue Creater

リポジトリ内の docs を根拠に、次に実装・証明・設計すべきタスクを GitHub Issue として起票する。
このリポジトリでは、応答・Issue タイトル・Issue 本文は日本語で書く。

## 対象入力

- 明示された docs ファイルやセクションがあれば、それを優先する。
- 指定がなければ、まず `docs/aat/proof_obligations.md` と `docs/aat/lean_theorem_index.md` を読む。
- 必要に応じて `docs/aat/algebraic_geometric_theory/README.md`, `docs/sft/software_field_theory.md`, `docs/sft/aat_interface.md`, `docs/tool/**`, `README.md`, `README.jp.md` も参照する。
- Issue 本文の構造は `.github/ISSUE_TEMPLATE/implementation_request.yml` と `.github/ISSUE_TEMPLATE/documentation_request.yml` に合わせる。
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
   - body には Issue Forms と同等の情報を入れる。最低限、`背景・課題`, `主対象領域`, `影響範囲`, `修正対象ファイル・候補`, `追加するもの`, `更新するもの`, `削除・置換するもの`, `この Issue ではやらないこと`, `完了条件`, `想定する検証`, `Lean status` を入れる。
   - ドキュメント修正 Issue では `照合すべき source of truth` を入れる。
   - 実装依頼 Issue では `期待する成果物` を入れ、実装変更が必須かどうかを明確にする。
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

すべての新規 Issue に、本文冒頭で**タスク型**を宣言する:

```text
タスク型: 新規実装 | 修正 | 移植(Research→本体) | docs
```

- **移植(Research→本体)**: `Formal/AG/Research/` の受理成果を本体へ
  蒸留するタスク。次を必須フィールドにする。
  - `移植元 theorem`: Research 側の宣言名とファイル
    (まず `docs/aat/research_evidence_index.md` を検索し、無ければ
    `rg` で Research 直接検索)
  - `移植元 conjuncts`: 移植元 statement の結論一覧の引用
  - Research 下限原則の明記: 「本体 statement はこの conjuncts 一覧を
    全被覆すること。結論の削減不可(分解・補題化は可)。下限到達が
    不能と判明した場合は実装で回避せず停止して報告する」
- タスク型を判断する材料が Issue 起票時点で不足している場合は、
  推定と明記した上で最も規律の強い型に倒す(移植の疑いがあれば移植)。

## 是正 Issue の source of truth ポインタ(必須)

既存実装の未達・欠陥を直す是正 Issue には、次のポインタを必須で入れる:

```text
source of truth:
- PRD: <path> の <節番号 / R番号 / AC番号>
- 本文: <部・定理番号などのラベル>(該当する場合)
- 移植元: <Research theorem 名とファイル>(移植型の場合)
```

是正が重なると直近の Issue / PR コメントが仕様を覆い隠すため、
どの是正 Issue も単体で source へ遡れる状態を保つ。レビュー・実装は
コメントの応酬ではなく、このポインタの先を一次仕様として読む。

## PRD 由来 Issue の規律(prd-loop 連携)

PRD の完了条件を Issue 化する場合に適用する。

- 完了条件には PRD の該当 AC を文言のまま引用する。要約や再表現で弱めない。
- PRD の採否規律(処置の降格が許される対象、anti-weakening 等)を Issue 側で
  拡張・緩和しない。例: PRD が「B級のみ降格可」とする場合、「高コスト項目」などの
  対象拡大を AC に書かない。
- 実装・証明・発火を要求する完了条件に対し、docs / 台帳記載だけで閉じられる
  Issue を作らない。
- 許可外の降格が必要と判明した場合は Issue 化せず、`status:blocked` で
  ユーザー判断を求める。

## Issue 化の判断基準

- `proved`: 原則として新規 Issue は不要。rename, docs sync, theorem generalization など追加作業が明確な場合だけ候補にする。
- `defined only`: 対応する correctness theorem, API design decision, naming stabilization が残るなら Issue 化する。
- `future proof obligation`: 既存 Issue がなければ Issue 化する。
- `empirical hypothesis`: Lean proof をブロックしない。extractor, dataset, validation protocol, metric definition など tooling / research task として分割できる場合だけ Issue 化する。

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

## Issue 本文テンプレート

### 実装 Issue

```markdown
背景・課題:
...

タスク型: 新規実装 | 修正 | 移植(Research→本体) | docs

主対象領域:
- formal | tool | website | doc

親 Issue: #N

影響範囲:
- formal:
- tool:
- website:
- doc:

期待する成果物:
- コード実装が必須

修正対象ファイル・候補:
- `...`

追加するもの:
- ...

更新するもの:
- ...

削除・置換するもの:
- なし

この Issue ではやらないこと:
- ドキュメント修正だけで完了扱いにしない

関連 docs:
- `docs/aat/proof_obligations.md` の「...」

完了条件:
- [ ] 指定した実装変更が入っている
- [ ] 必要なテストまたは build が通っている
- [ ] 必要な Lean status / docs / website copy が更新されている
- [ ] 対象外の主張や過剰な claim を追加していない

想定する検証:
- [ ] `lake build`
- [ ] `git diff --check`
- [ ] hidden / bidirectional Unicode scan

Lean status: future proof obligation.
```

docs にない内容を推測で増やす場合は、本文内で「推定」と分かるように書く。

### ドキュメント Issue

```markdown
背景・課題:
...

主対象領域:
- docs | formal status | tool docs | website copy | entry docs

確認が必要な領域:
- formal:
- tool:
- website:
- doc:

修正対象ファイル・候補:
- `...`

必要な修正:
追加:
- ...

更新:
- ...

削除:
- なし

照合すべき source of truth:
- `Formal/Arch/...`
- `docs/aat/proof_obligations.md`

この Issue ではやらないこと:
- Lean theorem の追加はしない

完了条件:
- [ ] 対象文書が source of truth と矛盾していない
- [ ] Lean status を `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` のいずれかで明確にしている
- [ ] docs と website の責務を混同していない
- [ ] 過剰な claim や未証明の主張を追加していない

想定する検証:
- [ ] `git diff --check`
- [ ] hidden / bidirectional Unicode scan
- [ ] Lean status / theorem index / proof obligations の整合確認

Lean status: docs index / design tracking.
```

### 親 Issue

```markdown
目的: 関連する Issue 群をまとめ、依存順と完了条件を明確にする。

背景:
...

子 Issue:
- [ ] #N ...
- [ ] #N ...

関連 docs:
- `docs/aat/proof_obligations.md` の「...」

完了条件:
- 子 Issue がすべて完了している。
- docs / Lean status が子 Issue の結果と一致している。

Lean status: docs index / design tracking.
```
