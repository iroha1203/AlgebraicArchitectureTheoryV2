---
name: prd-loop
description: PRD を入力に、完了条件を満たすまで「ギャップ分析 → Issue 作成 → 実装 PR → レビュー → マージ」を反復する実装ループを回す。Use when the user says "$prd-loop <PRD path>", "PRD を完了まで回して", "ループエンジニアリング", "PRD 駆動で実装を進めて", or wants Codex to autonomously iterate issue-creater / issue-to-pr / review-pr until a PRD's acceptance criteria are satisfied.
---

# PRD Loop

PRD の Acceptance Criteria / 完了条件を満たすまで、実装ループを反復する。
このリポジトリでは、応答・Issue・PR・コミットは日本語で行う。

ループの1周は次である。

```text
1. ギャップ分析:    PRD の完了条件と現状実装を突き合わせる(完了判定もここで行う)
2. Issue 作成:      $issue-creater で未達ギャップを Issue 化する
3. 実装:            $issue-to-pr で Issue を PR まで進める
4. レビューとマージ: $review-pr で判定し、Mergeable ならマージする
5. 同期:            main を最新化し、ループ台帳を更新して 1 に戻る
```

## 入力

- PRD ファイルパスは必須。`$prd-loop docs/tool/archsig_v0_4_0_algebraic_geometry_measurement_prd.md` のように受け取る。
  見つからない場合だけ短く確認する。
- 任意入力:
  - `max-iterations <N>`: この実行で回す最大周回数。既定は無制限であり、
    完了または他の停止条件に達するまで回り続ける。明示指定された場合のみ
    budget として扱う。
  - 対象の絞り込み(例: 「R1-R2 のみ」「schema 関係だけ」)。指定があれば
    ギャップ分析の対象をその範囲に限定する。

## 基本方針(ループ工学)

- **完了判定はループ先頭で行う。** 各周回の最初に PRD と実装を突き合わせ、
  完了条件がすべて満たされていれば、作業せずに完了報告して終了する。
- **状態は GitHub に置く。** ループの進行状態(どの完了条件が満たされ、どの Issue / PR が
  対応するか)は tracking Issue とその sub-issue / PR に記録する。セッション内の記憶に
  依存しない。これにより、ループは中断後も新しいセッションで同じ地点から再開できる。
- **1周 = 1 Issue = 1 PR。** 小さく切り、レビュー可能な単位で回す。複数の完了条件が
  単一の実装で自然に閉じる場合だけ、1 Issue にまとめてよい。
- **PRD はループの不変条件である。** ループ中に PRD を編集しない。実装の途中で
  PRD 自体の欠陥(矛盾、実装不能な要求、誤った理論参照)が判明したら、それを直さずに
  停止し、欠陥の内容と修正案を報告する。PRD の変更は人間の判断である。
- **進捗ゼロを検出して止まる。** 同じ完了条件で2周連続して PR がマージに至らない場合、
  その条件を `stalled` として停止条件に従う。回り続けることより、止まって報告することを優先する。
- **PRD が要求していない巨大な一般 claim を、未完了タスクとして追加しない**
  (`docs/tool/guideline.md` の PRD 規律)。ギャップ分析は PRD の完了条件の文言に限定する。
- **完了まで回り続ける。** 既定では周回数に上限を置かない。止まるのは、完了したとき、
  または停止条件(全 blocked / stall / PRD 欠陥 / 明示指定された budget)に
  該当したときだけである。

## サブエージェント活用

Codex は明示しない限りサブエージェントを使わない。この SKILL では、次の工程を
明示的にサブエージェントで実行する。

- **レビュー(手順4)**: `$review-pr` は必ずサブエージェントで実行する。
  実装を行った本体の文脈を引き継がない独立した文脈でレビューさせることで、
  自己レビューバイアス(自分の実装意図でコードを読んでしまう)を避け、判定精度を上げる。
- **再レビュー(手順4)**: Needs changes 後の修正は本体(実装文脈)が行い、
  再レビューは毎回新しいサブエージェントで行う。修正とレビューを同じ文脈で完結させない。
- **セルフレビュー(手順3内)**: `$issue-to-pr` が内部で使う `$local-review` は
  4観点 multi-agent review をデフォルトとする。周回を急ぐ目的で省略しない。
- **ギャップ分析(手順1)**: 完了条件の項目数が多い場合、項目群ごとの実装照合を
  サブエージェントへ分割して並列実行してよい。結果の統合、分類の最終判断、
  次周回の対象選定は本体が行う。

サブエージェントには、対象(PR 番号、完了条件の項目、照合対象ファイル)と
期待する出力形式を明示して渡す。本体の推測や途中経過は渡さない。

## ループ台帳(tracking Issue)

- 初回実行時、対象 PRD の tracking Issue を探す。タイトル `PRD Loop: <PRD ファイル名>` で
  open Issue を検索し、なければ作成する。
- tracking Issue の本文には次を置く。
  - PRD パスとコミット時点の参照
  - 完了条件の checklist(PRD の Acceptance Criteria を1項目1行で写す)
  - 各項目の分類: `実装検証系`(コード・テスト・fixture で検証する)/
    `PRD 記述系`(PRD 本文自体が満たしている。初回に check 済みにする)
- 各周回の終わりに、tracking Issue へコメントを1件追加する。
  - 形式: `iteration N: <対象完了条件> → Issue #X → PR #Y → merged | needs-changes | blocked`
- 完了条件を満たした項目は checklist を check する。根拠(PR 番号、テスト、fixture)を併記する。
- すべて check されたら tracking Issue を close し、ループを終了する。

## 標準手順

0. 前提を確認する。
   - `git status --short --branch` で作業ツリーを確認する。未コミット変更があれば
     ループを開始せず報告する(ユーザー変更を勝手に戻さない)。
   - `git switch main` と `git pull --ff-only` で最新化する。
   - PRD ファイルを読み、Acceptance Criteria / 完了条件の節を抽出する。
   - ループ台帳(tracking Issue)を確認または作成する。

1. ギャップ分析(プランニング)。
   - PRD の完了条件を1項目ずつ、現状の実装(対象コード、schema、テスト、fixtures、docs)と
     突き合わせ、`満たした / 未達 / blocked / stalled` に分類する。
   - 照合は文言ではなく実体で行う: 完了条件が要求するテスト・fixture・検証が
     実際に存在し、通ることを確認する(必要なら `cargo test` 等を実行する)。
   - すべて `満たした` なら: tracking Issue を close し、完了報告して終了する。
   - 未達項目から次の1周で扱う対象を選ぶ。選定基準は、他の完了条件の前提になるもの
     (schema・入力契約が evaluator より先)、依存が少ないもの、の順。
   - `blocked`(設計判断・理論証明・ユーザー入力が必要)は対象にせず、台帳に理由を記録する。

2. Issue を作成する。
   - `$issue-creater` を使い、選んだ完了条件のギャップを Issue 化する。
   - Issue は tracking Issue の sub-issue として紐付ける。
   - Issue の `完了条件` には、PRD のどの Acceptance Criteria 項目に対応するかを明記する。
   - 既存の open Issue が同じギャップを既に扱っている場合は、新規作成せずそれを使う。

3. 実装する。
   - `$issue-to-pr` を使い、その Issue を PR まで進める。
   - `$issue-to-pr` 内のセルフレビュー(`$local-review`)・検証・PR 規律はそのまま適用する。

4. レビューし、マージする。
   - `$review-pr` をサブエージェントで実行し、PR を判定する(「サブエージェント活用」参照)。
   - **Mergeable**: CI が green であることを確認し、`gh pr merge <PR> --merge --delete-branch`
     でマージする(このリポジトリは merge commit 方式)。
   - **Needs changes**: 指摘を修正して再検証し、新しいサブエージェントで再度
     `$review-pr` にかける。修正は同一周回で最大2回まで。2回で Mergeable に
     ならなければ、その完了条件を `stalled` として PR を open のまま残し、
     停止条件の判定に進む。
   - **Blocked / cannot determine**: 理由を台帳に記録し、停止条件の判定に進む。

5. 同期して次の周回へ。
   - `git switch main` と `git pull --ff-only`。
   - tracking Issue に iteration コメントを追加し、checklist を更新する。
   - `max-iterations` が明示指定されていてその周回数に達した場合を除き、手順1に戻る。

## 停止条件

次のいずれかで、ループを止めて報告する。止まることは失敗ではなく、ループの仕様である。

```text
完了:       すべての完了条件が「満たした」。tracking Issue を close する。
全 blocked: 未達項目がすべて blocked / stalled で、この実行で進められるものがない。
stall:      同一の完了条件が2周連続でマージに至らない。
budget:     max-iterations が明示指定された場合のみ。その周回数に達した。
PRD 欠陥:   実装中に PRD 自体の矛盾・実装不能が判明した。
```

既定では budget 停止はなく、完了まで回り続ける。
stall / 全 blocked / budget で止まった場合も、状態はすべて tracking Issue に残っているため、
次回 `$prd-loop` を同じ PRD で実行すれば同じ地点から再開できる。

## 報告形式

終了時に次の順で日本語で報告する。

1. 終了理由: `完了` / `全 blocked` / `stall` / `budget` / `PRD 欠陥`
2. 完了条件スコアボード: 満たした / 未達 / blocked / stalled の項目数と一覧
3. この実行の周回ログ: iteration ごとの Issue / PR / 結果
4. マージした PR と main の最新コミット
5. blocked / stalled 項目の理由と、人間の判断が必要な点
6. 次回再開時に最初に扱うべき項目

## 安全規則

- 破壊的操作をしない。`git reset --hard`、`git checkout --`、force push は使わない。
- PRD・既存の未コミット変更・他人の open PR を勝手に変更しない。
- マージは `$review-pr` の Mergeable 判定と CI green の両方が揃った場合だけ行う。
- `axiom`, `admit`, `sorry`, `unsafe` を相談なしに導入しない(`$issue-to-pr` の規律を継承)。
- 1周の中で複数 PR を並行して open しない。レビュー・マージの追跡可能性を優先する。
