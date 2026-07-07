---
name: prd-loop
description: PRD を入力に、完了条件を満たすまで「ギャップ分析 → Issue 作成 → 実装 PR → レビュー → マージ → 最終達成条件レビュー」を反復する実装ループを回す。Use when the user says "$prd-loop path/to/prd.md", "PRD を完了まで回して", "ループエンジニアリング", "PRD 駆動で実装を進めて", or wants Codex to autonomously iterate issue-creater / issue-to-pr / review-pr / prd-completion-review until a PRD's acceptance criteria are satisfied.
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
6. 最終レビュー:    全条件が満たされたように見える時だけ $prd-completion-review を実行する
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

- **完了判定は二段階で行う。** 各周回の最初に PRD と実装を突き合わせる。
  すべて満たしたように見える場合でも、tracking Issue を close する前に
  `$prd-completion-review` を最終達成条件レビューとして実行する。
  `達成済み` 以外なら完了扱いにせず、finding を次のギャップとして扱う。
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
- **完了への最安経路を塞ぐ(インセンティブ規律)。** ループは放置すると
  「マージが通る最も安い経路」(記載の付け替え、条件の再解釈)へ収束する。次を禁止する。
  - 実装・証明・発火を要求する完了条件を、docs / 台帳記載のみの PR で check しない。
    docs-only PR で check してよいのは、PRD がその条件に docs 処置を要求している場合だけ。
  - 処置種別の降格(昇格 → 実質化 / 宣言 / 削除 など)は、PRD が明示的に許可した項目
    (等級リスト等)に限る。許可外の降格が必要と判明した項目は `blocked` として
    ユーザーへエスカレートする。降格を Issue や台帳の文言で再定義しない。
  - stall 回避のために完了条件を再解釈・降格しない。進まない項目は stalled として
    正直に止まる。止まることは失敗ではなく、ループの仕様である。
- **Issue の完了条件は PRD 文言の引用で書く。** 採否規律・中心方針を弱める再表現
  (降格許容対象の拡大、限定の削除)を sub-issue に持ち込まない。
  sub-issue と PRD が食い違う場合は PRD が正である。
- **完了まで回り続ける。** 既定では周回数に上限を置かない。止まるのは、完了したとき、
  または停止条件(全 blocked / stall / PRD 欠陥 / 明示指定された budget)に
  該当したときだけである。

## サブエージェント活用

Codex は明示しない限りサブエージェントを使わない。この SKILL では、次の工程を
明示的にサブエージェントで実行する。レビュー系サブエージェントが起動できない
環境では、親が代替せず該当工程を `Blocked` に落とす(fail-closed)。

- **レビュー(手順4)**: `$review-pr` は必ずサブエージェントで実行する。
  実装を行った本体の文脈を引き継がない独立した文脈でレビューさせることで、
  自己レビューバイアス(自分の実装意図でコードを読んでしまう)を避け、判定精度を上げる。
  `$review-pr` は内部で分野別の敵対レビュー SKILL(Lean 実装を触る PR は
  差分1行でも `$math-lean-review` 4並列)へ委譲する。
- **再レビュー(手順4)**: Needs changes 後の修正は本体(実装文脈)が行い、
  再レビューは毎回新しいサブエージェントで行う。修正とレビューを同じ文脈で完結させない。
- **エスカレーション(手順4)**: 同一 Issue で `Needs changes` が2回続いたら、
  3回目は同じレビューを繰り返さず、より強いゲートに切り替える。Lean 系は
  `$math-lean-review` 正式判定(4本+Material Premise Discharge Audit)を
  直接実行する。それでも通らなければ従来どおり `stalled` として停止する。
  ゲートのセマンティクス(無条件4並列・fail-closed・4本全承認)は
  `math-lean-review` 側の定義が正であり、ここでは「いつ呼ぶか」だけを規定する。
- **セルフレビュー(手順3内)**: `$issue-to-pr` が内部で使う分野別レビュー
  SKILL(`math-lean-review` / `tool-review` / `website-review` /
  `docs-review`)の multi-agent review を周回を急ぐ目的で省略しない。
- **ギャップ分析(手順1)**: 完了条件の項目数が多い場合、項目群ごとの実装照合を
  サブエージェントへ分割して並列実行してよい。結果の統合、分類の最終判断、
  次周回の対象選定は本体が行う。
- **最終達成条件レビュー(手順6)**: `$prd-completion-review` は必ず
  サブエージェントで実行する(起動できなければ fail-closed で
  `Blocked` 停止。本体の順次実行での代替は不可)。ループを進めた本体の
  「全部満たしたはず」という前提を渡さず、PRD パス、tracking Issue、
  関連 PR / Issue、現在の main の状態だけを raw context として渡す。

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
  - **requirement matrix**: PRD の `改修`(R 番号)と `Implementation Plan`(PR 区分)を
    1項目1行で写し、各 AC がどの R / PR 区分に依存するかを併記する。R 群は AC を
    置き換える合否条件ではなく、周回の対象選定と「実装計画の丸ごと欠落」の検出に使う。
    どの周回にも接続していない R / PR 区分が残ったまま全 AC が check される状態は、
    checklist の写し漏れか充足の空洞化を疑うシグナルとして扱う。
  - **must-not-remain リスト**: PRD の `現状診断` が解消対象として名指しした
    旧構造・旧挙動を1項目1行で写す。PRD が明示的に別 PRD の管轄・既知の残置とした
    項目は除外し、除外理由を併記する。
- 各周回の終わりに、tracking Issue へコメントを1件追加する。
  - 形式: `iteration N: <対象完了条件> → Issue #X → PR #Y → merged | needs-changes | blocked`
- 完了条件を満たした項目は checklist を check する。根拠(PR 番号、テスト、fixture)を併記する。
  テストを根拠にする場合はテスト名でなく「何を assert しているか」を書く。
  条件文言と assertion 内容の対応が書けないテストは根拠にしない。
- すべて check されても、`$prd-completion-review` の総合判定が `達成済み` になるまでは
  tracking Issue を close しない。
- 最終達成条件レビューの結果は tracking Issue にコメントする。
  - `達成済み`: レビュー結果、検証、main commit を記録して close する。
  - `未達あり` / `未確認あり` / `PRD欠陥あり`: finding を未達ギャップとして記録し、
    対応 Issue を作成または既存 Issue に紐付け、ループを継続または停止条件に従う。

## 標準手順

0. 前提を確認する。
   - `git status --short --branch` で作業ツリーを確認する。未コミット変更があれば
     ループを開始せず報告する(ユーザー変更を勝手に戻さない)。
   - `git switch main` と `git pull --ff-only` で最新化する。
   - PRD ファイルを読み、Acceptance Criteria / 完了条件の節に加えて、
     `改修` / `Implementation Plan` / `現状診断` / `Failure Contract` /
     `Changed / Removed Fields` を抽出する(台帳の requirement matrix と
     must-not-remain リストの材料)。
   - ループ台帳(tracking Issue)を確認または作成する。

1. ギャップ分析(プランニング)。
   - **工程0(問いの再読)**: PRD 冒頭の「## 問い」を読み直し、現状が
     その問いに答えているかを AC より先に判定する。AC がすべて check 済み
     でも問いが未回答なら、完了扱いにせず、その乖離をユーザーへ
     エスカレートする(ループ自身で問いを再解釈したりスコープを
     拡大したりしない)。AC は問いに答えるための手段であり、
     AC の充足はアウトカムの代理にすぎない。
   - PRD の完了条件を1項目ずつ、現状の実装(対象コード、schema、テスト、fixtures、docs)と
     突き合わせ、`満たした / 未達 / blocked / stalled` に分類する。
   - 照合は文言ではなく実体で行う: 完了条件が要求するテスト・fixture・検証が
     実際に存在し、通ることを確認する(必要なら `cargo test` 等を実行する)。
   - tracking Issue の checklist が check 済みであることを `満たした` の根拠にしない。
     check は「過去の周回がそう主張した」ことしか意味しない。疑いがあれば実体を再確認する。
   - requirement matrix を突合し、どの周回にも接続していない R / PR 区分が残っていないかを
     確認する。未接続の R 群が依存先 AC の充足を空洞化している場合、その AC は
     check 済みでも `未達` に戻す。
   - すべて `満たした` と分類できた周回では、close 前に **must-not-remain 検査**を行う:
     台帳の must-not-remain リストの各項目を `rg` と実読で再検査し、PRD が解消を宣言した
     旧構造・旧挙動(旧挙動を「正」として固定し続けるテストを含む)が残存していれば、
     対応する完了条件を `未達` に戻す。
   - すべて `満たした` なら: tracking Issue を close せず、手順6の最終達成条件レビューへ進む。
   - 未達項目から次の1周で扱う対象を選ぶ。選定基準は、他の完了条件の前提になるもの
     (schema・入力契約が evaluator より先)、依存が少ないもの、の順。
   - `blocked`(設計判断・理論証明・ユーザー入力が必要)は対象にせず、台帳に理由を記録する。

2. Issue を作成する。
   - `$issue-creater` を使い、選んだ完了条件のギャップを Issue 化する。
   - Issue は tracking Issue の sub-issue として紐付ける。
   - Issue の `完了条件` には、PRD のどの Acceptance Criteria 項目に対応するかを明記し、
     該当 AC の文言を引用する。その条件に関わる拘束(降格可否、要求される処置種別)も併記する。
   - 既存の open Issue が同じギャップを既に扱っている場合は、新規作成せずそれを使う。

3. 実装する。
   - `$issue-to-pr` を使い、その Issue を PR まで進める。
   - `$issue-to-pr` 内のセルフレビュー(分野別レビュー SKILL)・検証・PR 規律はそのまま適用する。

4. レビューし、マージする。
   - `$review-pr` をサブエージェントで実行し、PR を判定する(「サブエージェント活用」参照)。
   - **Mergeable**: 次の3条件が揃った場合だけ
     `gh pr merge <PR> --merge --delete-branch` でマージする
     (このリポジトリは merge commit 方式)。
     1. `$review-pr` の Mergeable 判定(Lean 系は math-lean-review 4本全承認を含む)
     2. CI が green
     3. **レビュー監査コメントが PR に投稿済み**(`$review-pr` の手順6。
        投稿が無い PR はマージしない)
   - **Needs changes**: 指摘を修正して再検証し、新しいサブエージェントで再度
     `$review-pr` にかける。修正は同一周回で最大2回まで。2回目の
     `Needs changes` の後は「サブエージェント活用」のエスカレーション
     規則に従い、3回目をより強いゲートで実行する。それでも Mergeable に
     ならなければ、その完了条件を `stalled` として PR を open のまま残し、
     停止条件の判定に進む。
   - **Blocked / cannot determine**: 理由を台帳に記録し、停止条件の判定に進む。

5. 同期して次の周回へ。
   - `git switch main` と `git pull --ff-only`。
   - tracking Issue に iteration コメントを追加し、checklist を更新する。
   - `max-iterations` が明示指定されていてその周回数に達した場合を除き、手順1に戻る。

6. 最終達成条件レビューを実行する。
   - 手順1で PRD の完了条件がすべて `満たした` と分類された場合だけ実行する。
   - `$prd-completion-review <PRD パス>` を、必ずサブエージェントで実行する
     (起動できなければ fail-closed で `Blocked` 停止)。
   - 入力には、PRD パス、tracking Issue 番号、関連 Issue / PR、main の最新 commit、
     実行済み検証だけを渡す。親 Codex の完了見込みや期待結論は渡さない。
     tracking Issue の checklist の check 状態を完了根拠として渡さない
     (番号は証拠検索の索引に留める。checklist・台帳はループの出力であり、
     最終レビューの監査対象であって証拠ではない)。
   - **達成済み**: tracking Issue に最終レビュー結果をコメントし、tracking Issue を close して終了する。
   - **未達あり / 未確認あり**: finding を PRD 条件単位のギャップとして台帳に戻す。
     既存 open Issue がなければ `$issue-creater` で Issue 化し、手順2以降を続ける。
   - **PRD欠陥あり**: tracking Issue に理由を記録し、`PRD 欠陥` 停止として報告する。
   - **範囲限定レビュー**: 完了判定に必要な範囲が未確認なら `未確認あり` と同じ扱いにする。

## 停止条件

次のいずれかで、ループを止めて報告する。止まることは失敗ではなく、ループの仕様である。

```text
完了:       すべての完了条件が「満たした」かつ `$prd-completion-review` が `達成済み`。
            tracking Issue を close する。
全 blocked: 未達項目がすべて blocked / stalled で、この実行で進められるものがない。
stall:      同一の完了条件が2周連続でマージに至らない。
budget:     max-iterations が明示指定された場合のみ。その周回数に達した。
PRD 欠陥:   実装中に PRD 自体の矛盾・実装不能が判明した。
final review gap:
            `$prd-completion-review` が未達 / 未確認を返し、この実行では新規周回に進めない。
```

既定では budget 停止はなく、完了まで回り続ける。
stall / 全 blocked / budget で止まった場合も、状態はすべて tracking Issue に残っているため、
次回 `$prd-loop` を同じ PRD で実行すれば同じ地点から再開できる。

## 報告形式

終了時に次の順で日本語で報告する。

1. 終了理由: `完了` / `全 blocked` / `stall` / `budget` / `PRD 欠陥` / `final review gap`
2. 完了条件スコアボード: 満たした / 未達 / blocked / stalled の項目数と一覧
3. 最終達成条件レビュー結果: `$prd-completion-review` の総合判定、findings、未達 / 未確認項目
4. この実行の周回ログ: iteration ごとの Issue / PR / 結果
5. マージした PR と main の最新コミット
6. blocked / stalled / final review gap 項目の理由と、人間の判断が必要な点
7. 次回再開時に最初に扱うべき項目

## 安全規則

- 破壊的操作をしない。`git reset --hard`、`git checkout --`、force push は使わない。
- PRD・既存の未コミット変更・他人の open PR を勝手に変更しない。
- マージは `$review-pr` の Mergeable 判定、CI green、レビュー監査コメントの
  PR 投稿済みの3つが揃った場合だけ行う。
- `axiom`, `admit`, `sorry`, `unsafe` を相談なしに導入しない(`$issue-to-pr` の規律を継承)。
- 1周の中で複数 PR を並行して open しない。レビュー・マージの追跡可能性を優先する。
