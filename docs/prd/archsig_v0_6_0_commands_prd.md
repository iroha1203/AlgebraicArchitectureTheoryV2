# ArchSig v0.6.0 コマンド実装 PRD

## 問い

利用者は、現状と変更候補が設計上の要求を満たすかを確かめ、
進める変更を根拠とともに判断できるか。

目的は、利用者が要求の成立・反例・不足情報を区別し、変更の検討を進められるようにすることである。
そのために、[製品コンセプト](../tool/archsig_v0_6_0_concept.md)の利用体験を、
[v0.6.0 I/O 仕様](../tool/archsig_v0_6_0_io/README.md)の全コマンドで支える。
公開動作の一次仕様はこの I/O 仕様とする。失敗通知の仕様変更も同仕様へ反映する。
本 PRD は実装対象、依存順、受け入れ条件を定める。

## 現状診断

以下は実装着手点を選ぶための診断であり、作業の充足状況は記録しない。
対象クレートは `tools/archsig_v0.6.0`。

| 入口・層 | 現在の実体 | 実装上の差分 |
| --- | --- | --- |
| `version` | `src/run.rs` の `VERSION_LINE`、`src/main.rs` の配送 | 仕様どおりの一行出力を維持する |
| `check` | `src/run/args.rs`、`src/run.rs`、`src/run/output.rs` が静的検査、入力コピー、結果公開を行う | 静的検査の責務と成功成果物を保ち、失敗通知は後述の方針へ改める |
| `run` | 引数解析の `Command` は Check/Version のみ。正しい Counter 三入力・問いを与えても usage で拒否する試験がある | 引数、問い、制御、評価、結果、配送の接続が必要 |
| 観測評価 | `src/observed/mod.rs` の準備 API、`evaluate_observed_bytes`、共有 `Control`、型付き DAG がある | 観測環境の `evaluate/check` を CLI に接続する。内部表示だけでは公開結果にならない |
| 他の計算 | 要求 resolver は他10問と Architecture 環境を `NotApplicable` で区別する。評価の未実装には `NotImplemented` がある | 対象・写像・局所構造・候補域などの構成と評価が必要。式内 Path と保存済み Operation は別の型として扱う |

根拠は[実装 README](../../tools/archsig_v0.6.0/README.md)、
[引数解析](../../tools/archsig_v0.6.0/src/run/args.rs)、
[観測要求解決](../../tools/archsig_v0.6.0/src/observed/request.rs)、
[内部失敗](../../tools/archsig_v0.6.0/src/observed/result.rs)、
[公開 run の拒否試験](../../tools/archsig_v0.6.0/tests/cli_rejections.rs)で確認できる。
[観測評価器の tracker #5371](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5371)
は依存成果への索引であり、その完了を全 CLI または全12問の完成根拠にはしない。

## 対象と非対象

完成対象は `check`・`run`・`version` と、`run` の固定12問すべてである。
共通の要求解決・結果・制御・配送を先に整え、既存の観測評価から一周ずつ実装する。
最初の一周の完成と本 PRD 全体の完成を区別する。
各段は実装・検証の順序であり、全体完成前の配布・公開を要件に含めない。

| コマンド | 実装対象の責務 | 公開動作の参照先 |
| --- | --- | --- |
| `check` | 三入力の静的検査と宣言の解決説明。ArchMap 省略も扱い、問いの計算を開始しない | [実行 §1](../tool/archsig_v0_6_0_io/execution.md#1-コマンド)、[結果 §1](../tool/archsig_v0_6_0_io/results.md#1-resultjson) |
| `run` | 同じ静的検査の後、問いを解決し、型付き結果の依存に従って計算する。予算・再利用・配送を含む | [実行 §§1–7](../tool/archsig_v0_6_0_io/execution.md)、[型付き結果](../tool/archsig_v0_6_0_io/results.md) |
| `version` | 製品版と意味の版を機械向けに表示する | [実行 §5](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力) |

| `run` の問い | 完成に必要な計算・接続 | 主な依存 |
| --- | --- | --- |
| `evaluate` | 観測値と Architecture の変更後環境の view 評価 | 観測評価、Architecture/overrides、公開射影 |
| `check` | Law の部分束縛・全称化と成立・反証・未決の評価 | 同じ入力表、量化域、変更後環境 |
| `build` | Architecture、object algebra、方程式等の標準構成 | 読みの解決、対象族、内部操作の保存検査 |
| `map` | configuration/object algebra の保存を別々に検査し、型付き写像・操作を構成 | 始終域の reading、候補対応、標準構成 |
| `compose` | Operation 同士または Path 同士の合成 | 端点・owner・reading、全作用と名前付き語 |
| `compare` | value/word/action/relation/diagnostics の比較 | 比較対象の型。diagnostics は実 Operation と局所診断 |
| `solve` | 許す変更の全候補と全解を構成 | 基準 Architecture、change、Law、有限・整数アフィン計算 |
| `repair` | 全解の元 Assignment の一意性と具体値を検査し、再代入した対象を構成 | solve、元の更新と Law、変更後評価 |
| `quotient` | CandidateSpace または SolutionSet を view で商にし、指定時は Law 評価族の降下を検査 | 候補域・全解、view、実際の fiber/格子計算 |
| `localize` | 読取りの圏・cover・topology、方程式側と意味状態側を生成 | 標準構成、local、選択 Law と change |
| `diagnose` | 空間・対象類・貼り合わせを side/degree に応じて計算 | LocalSystem、正確な加群計算または有限全列挙 |
| `needed` | 問いの未観測位置とその他の未決理由を収集 | 全問いに共通する依存と理由の保持 |

各行の引数・既定値・型・成立条件は[実行 §§2–3](../tool/archsig_v0_6_0_io/execution.md#2-問いの構文と参照)、
生成手続きは[核の構成](../tool/archsig_v0_6_0_io/computations.md)、
公開射影は[結果 §2](../tool/archsig_v0_6_0_io/results.md#2-回答条件導出)に従う。
12問を新しいトップレベルコマンドへ分割する要求はない。

今回の実装計画の対象外は、旧版 `tools/archsig` の analyze/compare/gate 等の移植、
ArchView/FieldSig の改修、観測器・製品 skill の作成、配布・公開作業、CI への新規 task 追加、
Lean の形式化である。実装対象の説明は同クレートの README と既存 I/O 仕様へ反映する。
website と Claude 側の文書・skill は別作業とする。

## 入出力・失敗・中断の受け入れ範囲

永続的な書式と動作は既存仕様を参照し、失敗通知については後述の変更点を含めて実装・試験の対象とする。

| 対象 | 確認する公開動作 | 参照先 |
| --- | --- | --- |
| 引数と入力 | 全 flag の検査、明示された複数定義、三入力の検査順と同じ開始時 byte 列、未使用宣言も含む検査 | [実行 §1・§5・§7](../tool/archsig_v0_6_0_io/execution.md)、[定義 §4](../tool/archsig_v0_6_0_io/definitions.md#4-検査と責務) |
| 問いと依存 | 後方参照、依存順と回答指定順、explicit/defaulted、型・owner、循環、静的拒否と動的不適合の区別 | [実行 §§2–3](../tool/archsig_v0_6_0_io/execution.md#2-問いの構文と参照) |
| 結果と由来 | result/2 の全必須欄、元入力コピー・digest・Location、型付き DAG、支持・Scope・理由、表示用証人の非消費 | [結果 §§1–6](../tool/archsig_v0_6_0_io/results.md) |
| 終了コード | 確定反証と未決、入力不正・版非対応・I/O・内部障害・予算・signal の区別、および併発時の優先順位 | [実行 §6](../tool/archsig_v0_6_0_io/execution.md#6-状態終了コード予算) |
| 出力配送 | 既存出力の保護、一時 directory と flush/非置換 rename、一行 receipt、stderr、公開前後の配送失敗 | [実行 §§5–6](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力) |
| 中断 | 入力検査・要求解決・評価・再利用を含む soft limit、確定済み結果の保持、finalize の状態確定、signal と SIGPIPE | [実行 §6](../tool/archsig_v0_6_0_io/execution.md#6-状態終了コード予算) |
| 再利用 | 現在の三入力からの再検査、不正候補の記録、変更後の根・束縛・由来、計画によらない意味 | [実行 §7](../tool/archsig_v0_6_0_io/execution.md#7-版正規化再利用) |

## 内部評価器との接続と互換性

ファイル読込み、OS の計測・signal、出力配送は CLI が担い、値・命題の判断は核が担う。
現在の `prepare_checked_observed` 等で使う同じ検査済み三表を利用し、
CLI 用の別評価器や、result JSON を内部 IR として再入力する経路を増やさない。
共通化する内部型・モジュール配置は実装時に選べるが、既存 API の対応範囲に問い全体を合わせない。

`CheckResult` と観測評価の内部表示は、公開結果全体と同一ではない。
現在の CLI `Status` にない partial、評価の反証、requests/answers/nodes、limits、reuse を含めて
結果と配送の接続を設計し、内部出力に欄を継ぎ足しただけで公開適合と判定しない。
既存の `Control` と CLI 開始時の時計・実測 RSS・捕捉 signal を接続し、
入力を再読せず、finalize の状態確定まで同じ実行を追えることを確かめる。

v0.5.x との互換性の判断は[製品コンセプト §7](../tool/archsig_v0_6_0_concept.md#7-設計の判断基準)に従う。
v0.6.0 の入力形式、意味の版、result/2、receipt/1、check/version の通常の成果物・出力を保つ。
失敗通知は、標準出力へ具体的なエラーを返す新しい仕様へ実装を合わせる。
`run` を usage で拒否する現行の試験は、新しい正常経路と実際の不正要求の試験へ置き換える。
旧版のコマンド名・出力・バイナリ位置との暗黙互換や、新しい意味の flag は追加しない。
観測 API の既存利用例・呼出しを変える必要が生じた場合は、同クレートの利用例と独立 fixture で
移行を検証する。未実装を意味の版や入力不正の問題へ置き換えて互換性を説明しない。

## 失敗通知と成果物の分離・停止条件

コマンドの不正引数、入力不正、未対応版、I/O・内部障害等の実行失敗は、
標準出力へその場で分かる具体的なエラーを返し、終了コードで失敗を伝える。
失敗記録の result.json や入力コピーを作らず、出力先の回復や選び直しを要求しない。
通常の検査結果、計算した値・反例・診断・導出、確定済みの部分成果は依頼された成果物として保持する。
反証や数学的な未決を実行失敗へ読み替えない。

公開動作は[実行 §§2・5–6](../tool/archsig_v0_6_0_io/execution.md)と
[結果 §1](../tool/archsig_v0_6_0_io/results.md#1-resultjson)にある。
実行仕様は、失敗時の保存先回復・失敗記録ファイルの規定を削り、既存 receipt の issues に具体的なエラーを載せる。
循環の問いIDと依存辺も標準出力で説明し、内部の依存グラフ保持とは分ける。
結果仕様は、ファイルを依頼された成果物に位置付け、検査失敗時の空表だけを保存する要求を外す。
終了コードと成果物の通常配送は維持する。

現行製品コードは旧仕様の失敗ファイル保存・receipt を実装している。今回変更するのは仕様と PRD であり、
新しい失敗通知への実装変更は以下の受け入れ条件で検証する。
独立した計算・fixture の実装順は先に進められる。
既存仕様の矛盾、必要な算法の欠落、全体対象を縮める必要が判明した場合も、根拠と変更案を示して停止する。

## Acceptance Criteria

以下は全体完成の必要条件である。各条件は実装と独立 fixture による検証で判定する。
AC2・AC4–8 で要求の成立・反例・不足情報を区別し、AC9 で判断の根拠を元入力まで確認できることを確かめる。

- **AC1 コマンド面:** 全3コマンドと[実行 §1](../tool/archsig_v0_6_0_io/execution.md#1-コマンド)の
  全 flag を扱う。複数定義、複数 ask、必須欠落、単数重複、未知 flag、位置引数、予算の文法を
  正常系・拒否系で検証する。check は ArchMap の有無とも成功時に問いの出力を持たず、version は指定の一行と exit0。
  check/run の不正引数は、出力先の有無や不正にかかわらず標準出力の具体的なエラーと終了コードから失敗を読み取れ、失敗記録ファイルを作らない。
- **AC2 観測評価の一周:** Counter 三入力を実バイナリへ渡し、count=2 で型 Z の値2と両 Law 成立・exit0、
  count=12 で bounded の反証・exit1、count Atom 除去で subject を保持し不足位置付き未決・exit2。
  Bool=false の値確定と Law 反証、guard=false の不適用も区別する。
  根拠は[適合例](../tool/archsig_v0_6_0_io/validation.md#最小の一周)と[結果 §2](../tool/archsig_v0_6_0_io/results.md#2-回答条件導出)。
- **AC3 要求解決:** 後方参照、同優先度の指定順、回答指定順、部分束縛と既定規則を検証する。
  ID/引数重複、未知名、型・owner・静的 index・非公開射影は usage。循環は exit64 とし、
  標準出力に各 request の cycle と循環する問いID・依存辺を返す。内部の依存グラフ保持と nodes/answers が空であることも検証する。
  動的射影不適合と、その後続の dependency_blocked は元理由付きで区別する。
- **AC4 対象と写像:** build が構成する対象・代数と、map の configuration/object algebra 保存を
  [標準構成](../tool/archsig_v0_6_0_io/computations.md#1-対象作用law-instance)に従って検証する。
  Reservations の端点不保存で candidate と反例を残し Operation を生成しない。
  configuration 保存済みで追加条件だけが反証される場合の Operation の保持も検証する。
- **AC5 操作と比較:** compose と compare の全5 kind を実入力から計算する。
  同作用・別名の語、恒等、合成順、Path/Operation の区別、relation、値比較を独立の期待値で確認する。
  diagnostics は実写像と対象類の運搬を検査し、同じ表示値だけで成立させない。
  型・owner・reading・degree/side/係数の不適合を[実行 §3](../tool/archsig_v0_6_0_io/execution.md#3-固定の12の問い)どおり区別する。
- **AC6 候補・修復・商:** solve/repair/quotient を、有限域と整数アフィン域で実行する。
  [Pair.total/pinned](../tool/archsig_v0_6_0_io/validation.md#修復の存在と一意性)で、非一意の全解と存在、
  一意な元 Assignment、再代入を区別する。非一意 repair 単独は exit1、未生成 object を読む後続があれば exit2、
  pinned の一意 object を読む evaluate は値0と exit0。異なる Assignment が同じ更新状態になる例でも一意としない。
  CandidateSpace と SolutionSet の各商、Law 評価族の降下の成立・反証を確認する。
- **AC7 局所診断:** localize/diagnose が方程式側と意味状態側、選択 cover と生成 topology、
  degree=0/1/その他の仕様上の出力を区別する。
  [三辺の例](../tool/archsig_v0_6_0_io/validation.md#3-三辺の修復と局所大域)で γ=2/3/欠測を比較し、
  H¹=Z と対象類の零性、非零証拠、対象値の未決を区別する。入力へ行列や診断値を補給しない。
- **AC8 needed と計算範囲:** needed が元の未観測位置とその他の未決理由を依存先まで追う。
  [必須決定範囲](../tool/archsig_v0_6_0_io/computations.md#9-v060-の必須決定範囲)の各手続きに、
  小さい exact fixture と検査可能な値・証拠を用意する。必須算法の未実装を unsupported_algorithm で埋めない。
  仕様上の算法非対応の例では原式・型・域・理由を保持する。
- **AC9 公開結果:** 全12問の生成出力について、型、Ref、導出 DAG、原式の出現、支持、Scope、
  条件、反例、未決理由から入力コピーへ戻れる。成果物のない静的検査失敗に空の結果ファイルを要求しない。
  表示用の特解・基底・証人から後続 Law の束縛を作る抜け道を、[公開射影](../tool/archsig_v0_6_0_io/results.md#公開する意味上の射影)の拒否系で確認する。
- **AC10 終了と配送:** [実行 §§5–6](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力)の
  全終了条件と優先順位を検証する。通常の成果物配送と実行失敗の CLI 通知を分け、
  公開した result と receipt・プロセス終了 code の一致、既存 out と競合先の保護、
  読込み失敗、write/flush/rename 失敗、公開後 receipt 失敗と SIGPIPE を区別する。
  今回の実行が作成した未完成の一時directoryは片付け、利用者の既存ファイルと有効な成果物は削除しない。
  不正引数・不正入力・未対応版・I/O・内部障害の失敗通知だけを目的とするファイルを生成せず、
  成立・反証・未決の計算成果物と確定済み部分成果は保持することを独立 fixture で検証する。
- **AC11 予算と signal:** run の入力検査、要求解決、各計算、再利用の途中に固定 checkpoint の停止を注入し、
  確定値・反例を保持し新規導出を止め、未着手へ理由を付ける。実 CLI の SIGINT/SIGTERM と
  finalize 前後も小さい同期試験で確認し、130/143/75 と状態確定の扱いを検証する。
  check の検査途中の取消しは、検査完了を待たずに処理を止め、未完成の成果物を公開しない。
  確定済み成果物のない中断では CLI 通知を検証し、空の失敗記録ファイルを要求しない。
  試験の経過時間やホスト RSS の偶然だけを期待値にしない。
- **AC12 再利用と決定性:** reuse なし・有効候補・不正候補・入力/束縛/由来変更を比較する。
  採用する各推論を現在入力から再検査し、採用しなければ再計算する。
  不正候補の rejected、accepted/recomputed の実数、修復の全解・一意性の再検査を確認する。
  全再計算も[実行 §7](../tool/archsig_v0_6_0_io/execution.md#7-版正規化再利用)が許す選択とする。
  予算増加で確定した主張を反転させず、入力順や provenance の変更は対応する由来へ反映する。
- **AC13 独立検証と説明:** 各条件に対応する同クレート内の独立 fixture・明示引数・期待値で、
  内部計算と実バイナリの配送を検証する。README/マニュアル/website 本文やこの PRD を入力・期待値の取得元にしない。
  実装 README に提供範囲と実行例を反映し、未実装と数学的未決を区別できる。
  通常の導入例は run 一回から回答の状態・値を読むまでを示し、事前 check や複数の出力先を必須にしない。
- **AC14 出力方針と完了整理:** 仕様に定めた失敗通知と成果物の分離を実装へ反映し、
  AC1–13 の実装・分野別 review・必要な test を確認する。
  [削除条件](guideline.md#完了と削除)を満たして本 PRD を削除し、archive を作らない。

## 独立 fixture と検証方法

fixture は `tools/archsig_v0.6.0/tests/` 配下で所有する。
既存の Counter/Reservations/Engine を再利用し、Pair・三辺・有限比較等は、
上記の仕様例の意味と手計算した小さい期待値から独立に作成する。
本文と byte 一致を製品テストで強制せず、試験時は fixture だけを読む。
期待値を同じ生成器・評価器から作るだけの試験にせず、反例・残差・解の再代入や全候補の検算で確認する。

実バイナリの試験で CLI から receipt・result・入力コピー・終了 code を確認し、
内部試験では型・導出と停止地点・配送失敗を小さく固定する。
各実装単位に直接関係する既存試験と新規試験を、次の形式で一件ずつ直列実行する。

```sh
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test TARGET NAME -- --exact --test-threads=1
```

検証は[Tool guideline](../tool/guideline.md#テスト責務と実行経路)と
[共通確認](../workflow/guideline.md#pr-前の共通確認)に従う。
選択した試験の成功、全体の受け入れ条件、CI の成否はそれぞれの実証範囲で判定する。

## 実装順序

1. **共通の実行基盤と観測評価の一周。** 失敗通知と成果物の分離を実装する。check/version の通常経路の独立試験を保持し、
   run の引数・要求・結果全体・時計/signal・配送を接続して Counter の成立・反証・欠測を実行する。
   後方参照、循環、射影、予算、I/O、再利用の全再計算経路もこの一周で成立させる。
   新しい問いを既存の観測 API へ無理に通す前提を作らない。
2. **対象と操作の一周。** build/map と構成条件を実装し、compose と value/word/action/relation 比較を接続する。
   Architecture を読む evaluate/check、型付き結果を消費する共通 resolver を拡張する。
3. **変更候補の一周。** solve/repair/quotient と、修復後の evaluate/check・再度の変更を接続する。
   有限・整数アフィン全解、一意性、再代入、表示用射影の拒否まで同じ利用経路で検証する。
4. **局所・大域の一周。** localize/diagnose、方程式側と意味状態側、有限・加群計算、
   実 Operation による diagnostics 比較を接続する。共通計算は前段と共有する。
5. **全体照合と削除。** needed は理由生成とともに各段で接続する。
   各段の確定結果・中断・再利用・由来と全12問の合成を照合し、全受け入れ条件を判定する。
   実装範囲の説明と必要な恒久仕様を反映し、削除条件を満たして整理する。

各段は利用経路を単位として実装・検証する。Issue の切り方と進行状態は GitHub で管理し、
この順序を進捗表にしない。

## Failure Contract

次のいずれかが残れば、本作業は未達とする。

- 観測評価の一周だけで全コマンド完成と判定する、または固定12問・必須算法を任意の部分集合へ縮める。
- 未実装の評価経路を、反証、入力不正、版非対応、数学的な算法非対応へ置き換えて成功扱いする。
- 原始観測、許す変更、表示用証人を混ぜ、供給された結論や都合のよい一解で判断する。
- 入力から由来を追えない結果、未検査の DAG、停止中の暫定値、未生成 object を後続へ渡す。
- 配送の成功と計算結果の確定を取り違える、または既存 out を上書きする。
- 実行失敗だけを記録するファイルの生成を要件に残す、またはその削除とともに利用者が求めた計算成果物まで失う。
- 文書本文を読む製品テストや、文書の記載だけを根拠とした実装条件の充足判定を残す。
- 公開動作を PRD だけに置く、作業台帳を本文に作る、完了後の PRD を現行仕様として残す。
