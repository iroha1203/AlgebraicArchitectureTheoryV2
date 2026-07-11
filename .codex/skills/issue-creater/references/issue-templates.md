# Issue補助field

`.github/ISSUE_TEMPLATE/implementation_request.yml` と
`.github/ISSUE_TEMPLATE/documentation_request.yml` を本文構造の正本とする。
同じfieldをこのreferenceへ複製しない。Issue Formsから作成した本文の`備考`に、
次のうち該当する不足fieldだけを追加する。

## 関係・status

```markdown
親 Issue: #N

Lean status: <`docs/aat/guideline.md` の「Lean status discipline」にある現行語彙>
```

親Issueがない、またはLean statusが非該当の場合はfield自体を省略してよい。

## 是正Issue

```markdown
source of truth:
- PRD: <path> の <節番号 / R番号 / AC番号>
- 本文: <部・定理番号などのラベル>(該当する場合)
- 移植元: <Research theorem名とファイル>(移植型の場合)
```

## 移植Issue

```markdown
移植元 theorem:
- <declaration名> (`research/lean/ResearchLean/...`)

移植元 conjuncts:
- <移植元statementの結論一覧>

Research下限原則:
- 本体statementは移植元conjunctsをすべて覆う。
- 結論を削減しない。分解・補題化は可。
- 下限到達が不能と判明した場合は、実装で回避せず停止して報告する。
```

## 親Issue

Issue Formsを使わないtracking親Issueの独立template。新規親Issueを作る場合だけ使う。

```markdown
目的: 関連するIssue群をまとめ、依存順と完了条件を明確にする。

背景:
...

子 Issue:
- [ ] #N ...

関連 docs:
- `...`

完了条件:
- 子Issueがすべて完了している。
- docs / Lean statusが子Issueの結果と一致している。

Lean status: 非該当(tracking Issue)。
```

docsにない内容を推測で増やす場合は「推定」と明記する。
