---
name: prd-loop
description: PRDを不変入力として、ギャップ分析、Issue化、実装PR、敵対レビュー、マージ、台帳同期、独立最終レビューを完了または明示停止条件まで反復する。"$prd-loop path/to/prd.md"、"PRDを完了まで回して"で使う。完了可否のレビューだけならprd-completion-review、単一Issueの実装ならissue-to-prを使う。
---

# PRD Loop

PRD の Acceptance Criteria / 完了条件を満たすまで、実装ループを反復する。
1周は、ギャップ分析 → `$issue-creater` → `$issue-to-pr` → `$review-pr` →
マージと台帳同期で構成する。全条件が満たされた候補状態でのみ
`$prd-completion-review`を実行する。

監査は二層構造とする。周回側は次の1周を選ぶための差分駆動の作業判定、
完了の最終判定は `$prd-completion-review` の全数・独立監査である。
周回側の記録(台帳・checklist)は進行ログであって証拠ではないため、
最終監査が独立に再抽出する情報を周回側で複製・維持しない。
実装前のshadow実装、大規模または恒久的なevidence packet、または事前監査だけを目的とする全条件の
実装対応表を作らない。
実装・検証の証拠はPRの固定headとその検証結果に一本化する。

## 入力

- PRD ファイルパスは必須。`$prd-loop docs/prd/<prd-file>.md` のように受け取る。
  見つからない場合だけ短く確認する。
- 任意入力:
  - `max-iterations <N>`: この実行で回す最大周回数。既定は無制限であり、
    完了または他の停止条件に達するまで回り続ける。明示指定された場合のみ
    budget として扱う。
  - 対象の絞り込み(例: 「R1-R2 のみ」「schema 関係だけ」)。指定があれば
    ギャップ分析の対象をその範囲に限定する。

## 基本方針(ループ工学)

- **完了判定は二段階で行う。** 周回側のギャップ分析は次の1周を選ぶための
  作業判定であり、差分駆動でよい(手順1)。すべて満たしたように見える場合でも、
  tracking Issue を close する前に `$prd-completion-review` を最終達成条件
  レビューとして実行する。`達成済み` 以外なら完了扱いにせず、finding を
  次のギャップとして扱う。全数の実体照合は最終レビューの責務であり、
  最終監査の強度を各周回に持ち込まない。
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
- **Issue の受け入れ要件は PRD 文言の引用で書く。** 採否規律・中心方針を弱める再表現
  (降格許容対象の拡大、限定の削除)を sub-issue に持ち込まない。
  sub-issue と PRD が食い違う場合は PRD が正である。
- **完了まで回り続ける。** 既定では周回数に上限を置かない。止まるのは、完了したとき、
  または停止条件(全 blocked / stall / PRD 欠陥 / 明示指定された budget)に
  該当したときだけである。

## サブエージェント活用

次の工程を明示的にレビューgateへ委譲する。レビューgateが実行不能、または`Blocked`を
返した場合は、本体が代替せず該当工程を `Blocked` に落とす(fail-closed)。

- **レビュー(手順4)**: `$review-pr` を実行する。
  PR のレビュー責務は `$review-pr` 側に閉じる。
- **再レビュー(手順4)**: Needs changes後の修正と確認は、共有review protocolの
  「レビューバッチと修正後確認」に従う(直接対応の資格条件と確認subagentの検査義務は
  同節が正本)。修正はfindingをまとめて行う。直接対応の確認が未解消または資格喪失を
  返した場合は、`Needs changes` 1回として数える。
- **エスカレーション(手順4)**: 同一 Issue で `Needs changes` が2回続いたら、
  3回目は同じレビューを繰り返さず、より強いゲートに切り替える。Lean 系は
  `$math-lean-review` の正式判定に切り替える。それでも通らなければ
  従来どおり `stalled` として停止する。
  ゲートのセマンティクスは `math-lean-review` 側の定義が正であり、
  ここでは「いつ呼ぶか」だけを規定する。
- **自己点検(手順3内)**: `$issue-to-pr` のローカル自己点検・検証・
  PR 規律を周回を急ぐ目的で省略しない。
- **ギャップ分析(手順1)**: 完了条件の項目数が多い場合、項目群ごとの実装照合を
  サブエージェントへ分割して並列実行してよい。結果の統合、分類の最終判断、
  次周回の対象選定は本体が行う。
- **最終達成条件レビュー(手順6)**: `$prd-completion-review` を実行する。
  PRD 完了レビューの責務は `$prd-completion-review` 側に閉じる(実行不能または
  `Blocked` の場合は fail-closed で停止。本体の順次実行での代替は不可)。
  ループを進めた本体の
  「全部満たしたはず」という前提を渡さず、PRD パス、tracking Issue、
  関連 PR / Issue、現在の main の状態だけを raw context として渡す。

サブエージェントには、対象(PR 番号、完了条件の項目、照合対象ファイル)と
期待する出力形式を明示して渡す。本体の推測や途中経過は渡さない。

## ループ台帳(tracking Issue)

台帳は進行ログであり、証拠ではない。最終達成条件レビューは PRD から条件・
拘束・must-not-remain を独立に再抽出し、台帳を監査対象として扱う。
したがって台帳には再開に必要な最小情報だけを置き、PRD の内容を複製しない。

- 初回実行時、対象 PRD の tracking Issue を探す。タイトル `PRD Loop: <PRD ファイル名>` で
  open Issue を検索し、なければ作成する。
- tracking Issue の本文には次だけを置く。
  - PRD パスとコミット時点の参照
  - 完了条件の checklist(PRD の Acceptance Criteria を1項目1行で写す)
  - 各項目の分類: `実装検証系`(コード・テスト・fixture で検証する)/
    `PRD 記述系`(PRD 本文自体が満たしている。初回に check 済みにする)
- 各周回の終わりに、tracking Issue へコメントを1件追加する。
  - 形式: `iteration N: <対象完了条件> → Issue #X → PR #Y → merged | needs-changes | blocked`
- 完了条件を満たした項目は checklist を check し、根拠として PR 番号と
  実行した検証コマンドを併記する。証拠の資格判定(条件文言と assertion
  内容の対応を含む)は最終達成条件レビューが一次証拠で行う。
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
   - PRD ファイルを読み、冒頭の「## 問い」と Acceptance Criteria / 完了条件の節に加えて、
     `改修` / `Implementation Plan` / `現状診断` / `Failure Contract` /
     `Changed / Removed Fields` を確認し、次に実装する対象だけを選ぶ。
     requirement matrix と must-not-remain リストの全数抽出は、最終達成条件レビューに委ねる。
   - PRD が Lean 実装(`Formal/`)を要求する場合、作業ごとに指定された
     target statementの一次仕様を一意に特定し、実装中に参照できることを確認する
     (`docs/aat/lean_quality_standard.md` §5: target claim、必要な結論、明示された
     仮定・受け入れ条件)。完全Lean signatureは任意の補助情報とする。一次仕様から対象 claimを
     特定できなければ、ループを開始せず `PRD 欠陥` として停止・報告する。
   - ループ台帳(tracking Issue)を確認または作成する。

1. ギャップ分析(プランニング)。
   - **差分駆動で行う。** 現在の対象と、その実装に必要な直接依存だけを
     現状の実装(対象コード、schema、テスト、fixtures、docs)と突き合わせる。
     未着手の全条件を事前監査したり、完成形の実装を先取りして作らない。
   - 照合は文言ではなく実体で行う: 完了条件が要求するテスト・fixture・検証が
     実際に存在し、通ることを確認する(必要なら `cargo test` 等を実行する)。
   - Lean 実装系の完了条件では、指定された一次仕様のtarget claimと
     実装 declaration を直接突合する(`docs/aat/lean_quality_standard.md`
     §5.2)。完全Lean signatureがある場合はそれも照合する。premise の追加・結論の弱化・対象の縮小があれば、AC が check 済み
     でも `未達` に戻す。固定 statement の変更が必要と判明した場合は
     `PRD 欠陥` としてユーザーへエスカレートする(§5.3 drift 規則。
     ループ内で PRD を編集しない既存規律の適用)。
   - tracking Issue の checklist が check 済みであることを `満たした` の根拠にしない。
     check は「過去の周回がそう主張した」ことしか意味しない。疑いがあれば実体を再確認する。
   - 現在の対象が満たされたら、PRDを索引として読み、未着手の受入条件から次の対象を選ぶ。
     この選定では全条件の実装照合、対応表、旧構造の全数検索を行わない。
   - 未着手の受入条件と、既知の未達 / blocked / stalled 項目がなければ、tracking Issue を close せず
     手順6の最終達成条件レビューへ進む。
     PRD全体の全数照合は、この時点で一度だけ行う。
   - 次の対象は、他の完了条件の前提になるもの(例: schema・入力契約が evaluator より先)、
     依存が少ないもの、の順に選ぶ。
   - `blocked`(設計判断・理論証明・ユーザー入力が必要)は対象にせず、台帳に理由を記録する。

2. Issue を作成する。
   - `$issue-creater` を使い、選んだ完了条件のギャップを Issue 化する。
   - ループ内の sub-issue 起票では、重複照合は tracking Issue の既存 sub-issue と
     この PRD に関連する open Issue に限定してよい(`$issue-creater` の
     全件走査は省略できる。Issue 本文の規律はそのまま適用する)。
   - Issue は tracking Issue の sub-issue として紐付ける。
   - Issue の `受け入れ要件` には、PRD のどの Acceptance Criteria 項目に対応するかを明記し、
     該当 AC の文言を引用する。その条件に関わる拘束(降格可否、要求される処置種別)も併記する。
   - 既存の open Issue が同じギャップを既に扱っている場合は、新規作成せずそれを使う。

3. 実装する。
   - `$issue-to-pr` を使い、その Issue を PR まで進める。
   - `$issue-to-pr` 内のローカル自己点検・検証・PR 規律はそのまま適用する。
   - CI の完走は待たない。CI は手順4の内容レビューと並行して進め、
     マージ直前に本体が確認する。

4. レビューし、マージする。
   - PR 作成後、CI の完走を待たずに `$review-pr` を実行し、PR の内容を判定する
     (「サブエージェント活用」参照)。`$review-pr` は内容レビュー専任であり、
     CI 状態はその判定に含まれない。内容レビューと CI は並行して進む。
   - **Mergeable**: 次の3条件が揃った場合だけ
     `gh pr merge <PR> --merge --delete-branch` でマージする
     (このリポジトリは merge commit 方式)。
     1. `$review-pr` の Mergeable(内容合格)判定。修正が直接対応だけの場合は、初回正式レビューの
        finding全解消と、共有review protocolに従う親の修正後確認・PR監査記録を代用証拠にできる。
     2. CI が green(マージ直前に本体が `gh pr checks <PR>` で確認する。
        未完了なら完走までマージだけを保留する。CI failure は
        `Needs changes` として実装フェーズへ戻す)
     3. **レビュー監査コメントが PR に投稿済み**(`$review-pr` の手順6。
        投稿が無い PR はマージしない)
   - **Needs changes**: 共有review protocolに従って指摘をまとめて修正し、修正後確認
     (有資格な直接対応、または資格喪失時の正式ゲート再実行)で再判定する。直接対応の確認が
     未解消または資格喪失を返した場合も `Needs changes` として数える。修正は同一周回で最大2回まで。2回目の
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
   - 手順1で、未着手の受入条件と既知の未達 / blocked / stalled 項目がない候補状態になった場合だけ実行する。
   - `$prd-completion-review <PRD パス>` を実行する。
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

終了時に次の順で報告する。

1. 終了理由: `完了` / `全 blocked` / `stall` / `budget` / `PRD 欠陥` / `final review gap`
2. 完了条件スコアボード: 満たした / 未達 / blocked / stalled の項目数と一覧
3. 最終達成条件レビュー結果: `$prd-completion-review` の総合判定、findings、未達 / 未確認項目
4. この実行の周回ログ: iteration ごとの Issue / PR / 結果
5. マージした PR と main の最新コミット
6. blocked / stalled / final review gap 項目の理由と、人間の判断が必要な点
7. 次回再開時に最初に扱うべき項目

## ループ固有の安全規則

- マージは `$review-pr` の Mergeable 判定、または共有review protocolに従う直接対応確認、
  CI green、修正後確認を含むレビュー監査記録のPR投稿済み、の3条件が揃った場合だけ行う。
- 1周の中で複数 PR を並行して open しない。レビュー・マージの追跡可能性を優先する。
