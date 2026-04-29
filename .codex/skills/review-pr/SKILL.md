---
name: review-pr
description: PR 番号を受け取り、GitHub PR をレビューする。Use when the user asks Codex to review a PR, judge whether a PR is mergeable, verify linked Issue completion criteria, check implementation/test/docs gaps, or says "$review-pr <PR number>". This skill compares the PR against its linked Issue(s), inspects diffs and CI, runs appropriate local checks when needed, and reports whether it can be merged.
---

# Review PR

GitHub PR を、紐づく Issue の完了条件・実装内容・テスト・docs 更新・CI 状態に照らしてレビューする。
このリポジトリでは、ユーザーへの報告は日本語で行う。

## 入力

- ユーザーが `$review-pr 123` や `PR #123 をレビューして` と言った場合、`123` を PR 番号として扱う。
- PR 番号が見つからない場合だけ、短く確認する。
- PR 番号以外の追加観点があれば、通常レビューに加えて確認する。

## 基本方針

- コードレビュー姿勢を取る。バグ、仕様未達、Issue 完了条件の不足、回帰、テスト不足、docs drift を優先する。
- PR の良い点より、マージを止めるべき事実を先に出す。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。
- 破壊的操作をしない。`git reset --hard`, `git checkout --`, force push は使わない。
- PR ブランチを現在の作業ツリーへ checkout する必要がある場合は、作業ツリーが clean か確認する。dirty の場合は `/tmp` の一時 worktree を優先する。
- Lean 変更を含む PR では、原則として `lake build` を確認する。既存 CI が既に同等の `lake build` を成功させていても、ローカルで実行できない場合はその理由を報告する。

## 手順

1. 作業ツリーと PR メタデータを確認する。
   - `git status --short --branch`
   - `gh pr view <PR> --json number,title,state,isDraft,author,baseRefName,headRefName,headRefOid,mergeStateStatus,reviewDecision,body,url,files,commits,labels,closingIssuesReferences`
   - `gh pr checks <PR>`
   - `gh pr diff <PR> --name-only`

2. 紐づく Issue を読む。
   - `closingIssuesReferences` があれば、その Issue を `gh issue view <N> --json number,title,state,body,labels,milestone,url` で確認する。
   - PR 本文の `Closes #N`, `Fixes #N`, `Resolves #N` も確認する。
   - 明示的な Issue がなければ、PR 本文・タイトル・ブランチ名から推測せず、「紐づく Issue 不明」としてレビュー上のリスクにする。
   - Issue の `目的`, `背景`, `完了条件`, `Lean status`, sub-issue / checklist を抜き出し、PR が満たしているか照合する。

3. 差分を読む。
   - `gh pr diff <PR>` を主入口にする。
   - 大きい PR では `gh pr view <PR> --json files` と `gh pr diff <PR> -- <path>` 相当の分割確認を行う。`gh pr diff` に path filter が使えない場合は、PR head を一時 worktree に取得して `git diff base...head -- <path>` を使う。
   - Lean 定理名、docs status、Issue 番号、PR template の記載と実装の一致を確認する。

4. 必要なら一時 worktree で検証する。
   - 現在の作業ツリーを汚さないため、通常は `/tmp/aat-review-pr-<PR>` を使う。
   - 例:
     - `git fetch origin pull/<PR>/head:refs/remotes/pr/<PR>`
     - `git worktree add --detach /tmp/aat-review-pr-<PR> refs/remotes/pr/<PR>`
   - 検証後、一時 worktree を不要に長く残さない。削除が必要なら非破壊的に `git worktree remove /tmp/aat-review-pr-<PR>` を使う。
   - sandbox やネットワーク制約で fetch / build が失敗した場合は、承認付きで再実行する。

5. チェックを実行する。
   - Lean 変更がある場合:
     - `lake build`
     - `git diff --check`
     - `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal docs`
     - hidden / bidi scan: `rg -n "[\\u200B-\\u200F\\u202A-\\u202E\\u2066-\\u2069]" <changed-files>`
   - docs-only PR でも、Lean status や import に影響する記述なら `lake build` を検討する。
   - tooling 変更なら該当テストも確認する。例: `cargo test --manifest-path tools/archsig/Cargo.toml`

6. マージ可否を判定する。
   - **Mergeable**: Issue 完了条件を満たし、CI / 必要なローカル検証が通り、重大な未対応がない。
   - **Needs changes**: 完了条件未達、証明不足、テスト不足、docs drift、実装バグ、CI failure がある。
   - **Blocked / cannot determine**: PR head を取得できない、CI 未完了、紐づく Issue 不明、必要な検証が環境制約で実行できない。

## 報告形式

レビュー結果は簡潔に、次の順で出す。

1. 判定: `Mergeable`, `Needs changes`, `Blocked / cannot determine`
2. Findings: 重大度順。各 finding はファイル / 行、Issue 完了条件との関係、なぜ問題か、必要な修正を含める。
3. Issue 完了条件の照合: 満たした項目 / 未達項目。
4. 実行した検証: コマンドと結果。実行できなかったものは理由。
5. 重複・残リスク: マージ判断に影響する不確実性。

問題がない場合は、無理に finding を作らず「重大な指摘なし」と明記する。
