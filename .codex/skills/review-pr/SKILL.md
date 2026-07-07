---
name: review-pr
description: PR 番号を受け取り、GitHub PR をレビューするマージゲート。責務境界で分野を判定し、分野別の敵対レビュー SKILL(math-lean-review / tool-review / website-review / docs-review)へサブエージェントで必ず委譲し、統合判定と監査コメントの PR 投稿までを行う。Lean 実装(Formal/)を触る PR は差分の大きさを問わず math-lean-review の4並列査読を必須とする。Use when the user asks Codex to review a PR, judge whether a PR is mergeable, or says "$review-pr <PR number>".
---

# Review PR

GitHub PR のマージゲート。紐づく Issue の完了条件・CI 状態の照合は本体で
行い、**内容レビューは分野別の敵対レビュー SKILL へ委譲する**。
このリポジトリでは、ユーザーへの報告は日本語で行う。

## 敵対レビュー原則

これは**敵対レビュー**のゲートである。目的は PR を通すことではなく、
マージを止めるべき事実を探すこと。承認は反証の失敗としてのみ与える。
反証の手がかりの正本は `.codex/skills/_shared/refutation-checklist.md`。
本体・委譲先とも finding ゼロの報告には資格条件(反証試行3件の明記)が
課される(同 reference §7)。

## 基本方針

- **実装者の自己申告を証拠から除外する。** PR 本文の「証明した定理」
  リスト、「セルフレビュー実施済み」チェック、台帳・checklist の記載は
  監査対象であって証拠ではない。claim mapping はレビュー側で**独立に
  再構築**し、PR 本文の申告(conjunct 対応表を含む)と**突合**する。
- 既存の未コミット変更はユーザー変更として扱い、勝手に戻さない。
  破壊的操作をしない。`git reset --hard`, `git checkout --`, force push は
  使わない。
- PR ブランチの checkout が必要な場合は一時 worktree
  (`/tmp/aat-review-pr-<PR>`)を使う。
- 処置種別の降格を含む PR は、PRD の降格許容リストと照合する。許可外の
  降格は `Needs changes` とし、ユーザー判断事項として報告する(PRD が正)。

## 手順

1. 作業ツリーと PR メタデータを確認する。
   - `git status --short --branch`
   - `gh pr view <PR> --json number,title,state,isDraft,author,baseRefName,headRefName,headRefOid,mergeStateStatus,reviewDecision,body,url,files,commits,labels,closingIssuesReferences`
   - `gh pr checks <PR>`
   - `gh pr diff <PR> --name-only`

2. 紐づく Issue を読む。
   - `closingIssuesReferences` と PR 本文の `Closes #N` を確認する。
   - 明示的な Issue がなければ「紐づく Issue 不明」としてレビュー上の
     リスクにする。
   - Issue の `完了条件`、タスク型宣言、source of truth ポインタ
     (PRD 節番号・本文ラベル・移植元 theorem 名)を抜き出す。
     タスク型が「移植」の PR では、移植元 theorem 名を委譲先に渡す。

3. **分野判定と委譲(このゲートの中心)。**
   changed files から分野を判定し、対応する分野別レビュー SKILL を
   **サブエージェントで必ず**実行する。分野判定はファイルパスの集合では
   なく責務境界で行う(各分野は自分の claim に隣接する docs を所有する):

   | 分野 | 対象 | 委譲先 |
   | --- | --- | --- |
   | AAT / Lean | `Formal/`、`docs/aat/` の台帳類・数学本文整合 | `$math-lean-review` |
   | Tooling | `tools/`、`docs/tool/`、schema catalog | `$tool-review` |
   | Website | `website/`、`docs/website/` | `$website-review` |
   | Docs | docs-only、`docs/sft/`、`docs/note/`、PRD、`.codex/skills/` | `$docs-review`(レビューモード) |

   - **Lean 実装(`Formal/`)を触る PR は、差分の大きさを問わず(1行でも)
     `$math-lean-review` を必須とする。** 4並列査読はユーザー承認なしで
     無条件に立てる。**4本すべてが承認しない限り `Mergeable` を出せない**
     (棄却には該当レーンの再実行承認が必要。math-lean-review の
     4本全承認ゲート参照)。
   - Lean 実装+`docs/aat/` 台帳更新の PR は math-lean-review のみで
     足りる(statement と台帳の一致は一体で監査する)。
   - 真の分野横断(例: Lean + SFT 本文)は該当する複数分野で実行する。
   - サブエージェントが起動できない場合、親が代替レビューをせず、
     判定を `Blocked / cannot determine` に落とす(fail-closed)。

4. 本体で照合する(委譲と並行してよい)。
   - Issue 完了条件と diff の照合(条件文言と実体の対応)。
   - CI 状態(`gh pr checks`)。
   - checklist §6 の横断機械 scan(hidden/bidi、privacy / local-path、
     `git diff --check`)。
   - 必要なら一時 worktree で `lake build` / cargo test を実行する。

5. 統合判定する。
   - **委譲先判定の写像(合格の定義)**:
     - `math-lean-review`: 合格 = `No major findings`、または
       `Minor issues` かつ全 finding が中心 claim に触れない場合
       (その finding は監査コメントに残し、対応要否を明記する)。
       `Major revisions` / `Reject` / `Blocked` は不合格。
     - `tool-review` / `website-review` / `docs-review`:
       合格 = `No major findings` のみ。`Needs changes` / `Blocked` は不合格。
   - **Mergeable**: 委譲した全分野レビューが上記の意味で合格
     (Lean 系は4本全承認を含む)、Issue 完了条件を満たし、
     CI / 必要なローカル検証が通り、重大な未対応がない。
   - **Needs changes**: 委譲先の不合格、完了条件未達、テスト不足、
     docs drift、CI failure がある。
   - **Blocked / cannot determine**: PR head を取得できない、CI 未完了、
     紐づく Issue 不明、サブエージェント起動不能、必要な検証が実行できない。

6. **監査コメントを PR に投稿する(マージ前提条件)。**
   マージ手順(呼び出し元の prd-loop 等)に進む前に、次を含むレビュー
   監査コメントを PR へ投稿する。投稿が存在しない PR はマージ手順に
   進めない。
   - 統合判定
   - 分野・レーン別結論(math-lean-review なら4本それぞれの verdict)。
     **レーン別結論は親の要約に置き換えず、各レーンの報告原文
     (findings・反証試行・coverage limits の各節)をそのまま含める。**
     原文なしの要約だけの監査コメントはレビュー未実施として扱われる
   - 反証試行記録(finding ゼロの分野は反証試行3件以上)
   - Issue 完了条件の照合結果(満たした / 未達)
   - 実行した検証(コマンドと結果)、coverage / 残リスク
   資格条件(reference §7)を満たさない監査コメントは、後続のフル
   レビューで「レビュー未実施」として扱われる。

## 報告形式

ユーザーへの報告は監査コメントと同じ構成で簡潔に出し、監査コメントの
URL を添える。問題がない場合も、反証試行の記録なしに「重大な指摘なし」
とは書かない。
