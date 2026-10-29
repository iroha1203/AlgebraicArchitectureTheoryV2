# Tooling 編集ガイドライン

この文書は、`tools/` と `docs/tool` を編集するときの作業方針を定める。

## 位置づけ

- ArchSig の製品像は [ArchSig v0.6.0 製品コンセプト](archsig_v0_6_0_concept.md) にある。
- このガイドラインは作り方の規律だけを書く。コマンド、欄、計算の決まりはマニュアルに書く。
- 文書と作業台帳の分担は [Workflow guideline](../workflow/guideline.md) の
  「ドキュメントをステートレスに保つ規則」、PRD の lifecycle は [PRD guideline](../prd/guideline.md) に従う。
- ArchView と FieldSig は ArchSig の結果を読む側にあり、ArchSig の結論を作らない。

## 責務範囲(入力トライアドの正本)

- ArchSig の意味上の入力は Atom 定義・Law・ArchMap である。Atom 定義は共通の語彙・型・意味を
  持つ独立した定義元であり、Law と ArchMap が参照する。ファイルの包装と入力の役割を区別する。
- ArchMap には、コードから観測した Atom を書く。判定、結論、局所の分け方は書かない。
- Law は意味上の設計の出発点として必要な区別を決め、Atom 定義を参照して関係・制約・読みを
  宣言する。特定のコードで観測した値は書かない。複数 Law は同じ定義を共有できる。
- ArchSig が保証するのは、結論が Atom 定義・Law・ArchMap から正しく導かれたことまでである。
  観測が正しいかは観測する側(製品の SKILL)が担う。ツールや CI で担保しない。共通語彙だけで観測結果の一致は保証しない。
- エンジンは定義・宣言・事実の型と参照を検査し、計算構造・equation realization・写像を構成する。
  計算パイプラインを Law 作者へ移したり、処理系の検証を AAT の追加定理義務へ転嫁したりしない。
- 入力から決まらないことは、沈黙として理由とともに返す。沈黙を失敗や残タスクとして扱わない。
- 計算の中核は、プログラミング言語やフレームワークを知らない。
  名前の付け方やファイルとモジュールの対応のような言語の知識は、解析器と製品の SKILL の側に置く。
- 観測するのは実装コードの構造である。テストコードと、実行時に起きることは扱わない。
- ArchSig の説明は、何を入力に何を計算するかを肯定形で書く。「〜ではない」を主文にしない。

## 作り方

- マニュアルが決めていない振る舞いを実装で決めたら、同じ変更でマニュアルに書く。
  仕様をコードの中だけに置かない。
- 実装は、マニュアルにある具体的な一つの使い方(第2章の一周など)を単位に進める。
  その使い方に要るものだけを入れる。
- CI との連携、終了コード、エラーの形式、キャッシュ、入力の拒否や守りの規則は、
  実装して必要が見えてから足す。
- レビューは Issue の受け入れ要件と、このガイドラインの品質規約に照らす。
  具体的な不変条件違反・逆向き依存・不正なテストは修正し、仮想の将来要件や個人の好みで設計を広げない。
- Claude の実装は PRD に沿って進め、手順は `.claude/skills/prd-loop` と `.claude/skills/pr-review` に従う。
- PRD の完了は、PRD の受け入れ要件と、実装済みのテストで判定する。
  PRD が求めていない一般的な主張を残タスクにしない。

## Rust 品質規約

### 設計と実装

- 数学・判定の中核は CLI、filesystem、OS 計測に依存させない。責務と依存方向が分かる構成を選び、
  分離自体を目的に層やクレートを増やさない。
- 意味のある状態と不変条件を型・検証済みの構築経路で表す。未観測と観測済みの零、未検証と検証済みを
  区別し、検証済みの値を外から不正な状態へ変更できる API を作らない。
- API の入力・出力・エラー・副作用を明確にし、利用者に必要な失敗条件を説明する。
  不正入力を既定値・無制限予算・成功へ黙って変換しない。
- 想定される入力・I/O 失敗は `Result` で返す。`panic!` / `unwrap` / `expect` は成立根拠のある
  不変条件に限る。テストの準備失敗を `expect` で明示することは妨げない。
- 所有権・借用を素直に使い、不要な `clone` / `Arc` / `Mutex` を増やさない。
  一つのコピーを避けるだけのために lifetime や API を複雑にしない。
- `unsafe` は必要性を示せる最小範囲に限定し、安全条件とその成立根拠を説明する。
- `rustfmt` を使い、変更に関係する Clippy lint を選んで確認する。全 restriction lint の一括有効化や
  警告の一括抑制を品質の代用にしない。

### 簡素化と引き算

- 現在の要求に使わない機能・設定・将来用の拡張点を残さない。既存の検証・変換を再利用し、
  同じ責務の並行実装を増やさない。
- trait・wrapper・層は、実際の依存分離・再利用・読みやすさで必要性を説明できる場合に置く。
  仮想の別 backend だけを理由に一般化しない。
- 不要な公開範囲・依存・保持状態・cache・出力を減らす。行数ではなく、理解・変更・運用の費用で判断する。
  必要な振る舞いや安全検査は保持し、削除件数を目標にしない。

### レビューでの扱い

- 指摘は箇所・具体的な問題・最小の修正を簡潔に示す。問題がなければ指摘を作らない。
  既存の独立査読と共有 review protocol が求める反証根拠・未確認範囲は、必要な分量で残す。
- 引き算は既存レビューの観点として行い、別の必須工程や削除ノルマを作らない。
  個人の書き方の好みだけで merge を止めない。

## テスト責務と実行経路

- ツールのテストは、そのツールの計算と出力だけを確かめる。
  ArchSig のテストから ArchView、website、SKILL、docs を検査しない。
- README、マニュアル、website の文言、見出し、配置を製品テストで固定しない。
  文書本文をテスト入力や期待値の保存先・取得元にせず、本文からそれらを読み込む・抽出する構成にしない。
  文書編集で製品テストが落ちる依存を作らない。
- ArchSig のテストは、マニュアルに説明された振る舞い・公開 contract を、文書から独立した
  fixture、明示的な引数、期待値で検証する。例を基にテストを設計し、コマンドを実行して結果を確かめる。

### テストの書き方

- 検査できる最も狭い層を選ぶ。数学・判定の組合せは unit / 内部 integration、component・公開 API の
  contract は integration、引数・終了状態・出力・保存・再利用は実バイナリの E2E で確認する。
  同じ網羅表を各層で反復しない。下層へ移す場合も E2E 固有の確認は残す。
- 関連する値・状態・エラー種別を assert する。件数や成功だけでは contract を検査できない場合、
  それだけで済ませない。期待値は検査対象と同じ誤実装を再現する方法で作らない。
- 回帰テストは可能な範囲で修正前に失敗し、修正後に成功することを確かめる。
  偶然の呼出順序より振る舞い・contract を検査し、fixture・harness は条件と期待値が読める最小構成にする。
- file・process 環境を隔離し、clock・乱数を制御する。固定 sleep を同期の根拠にせず、
  自分が起動した子プロセスには独立した待機上限を設け、終了・回収する。
- assertion の弱化、snapshot の無検討な更新、製品予算の緩和で green にしない。
  重複を除き、適切な層へ配置する。性能測定と正しさの検査は区別する。

### 検証対象の選択

変更したクレートに対応する manifest を選ぶ。複数クレートに影響する変更は、それぞれを検証する。

| 対象 | manifest |
| --- | --- |
| `tools/archsig/**` | `tools/archsig/Cargo.toml` |
| `tools/archsig_v0.6.0/**` | `tools/archsig_v0.6.0/Cargo.toml` |
| `tools/fieldsig/**` | `tools/fieldsig/Cargo.toml` |

両 ArchSig は package 名が同じため、名前だけで選ばず manifest を明示する。
docs / schema のみの変更は、対象 contract・version が指定するクレートを選ぶ。
対象が不明なら特定してから検証し、旧版を既定にしない。

検証記録は対象 commit、manifest・version、選択した test target と、実行結果 / compile のみ / 未実行を
短く区別する。`cargo test --manifest-path <対象manifest>` に変更範囲に応じた target・filter を指定する。
対象選択だけで全 suite の実行を要求せず、CI の対象・実行結果は実際の workflow と照合する。

CI への追加は [Workflow guideline](../workflow/guideline.md#ci-への恒久追加の禁止) の承認規律に加え、
想定する CI 環境で準備・compile・test の合計が3分以内である実測を条件とする。
この時間条件は本プロジェクトの要件であり、Rust の一般標準ではない。

### 参考と採用範囲

上記は本プロジェクトで採用する規約である。以下の資料から設計・検査の考え方を参照し、
各プロジェクト固有の禁止事項や構成を一律には取り込まない。

- [Google Code Review](https://google.github.io/eng-practices/review/reviewer/looking-for.html): 現在必要な設計、複雑さ、テストの妥当性。
- Rust API Guidelines: [型安全性](https://rust-lang.github.io/api-guidelines/type-safety.html)、
  [表現の隠蔽](https://rust-lang.github.io/api-guidelines/future-proofing.html)、[失敗条件の文書化](https://rust-lang.github.io/api-guidelines/documentation.html)。
- rust-analyzer: [依存分離](https://rust-analyzer.github.io/book/contributing/architecture.html)、
  [style review](https://rust-analyzer.github.io/book/contributing/style.html)。
- Rust Book: [Result と panic](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)、
  [テスト構成](https://doc.rust-lang.org/book/ch11-03-test-organization.html)、[実行と共有環境](https://doc.rust-lang.org/book/ch11-02-running-tests.html)。
  Rust Compiler Development Guide の[回帰テスト](https://rustc-dev-guide.rust-lang.org/tests/adding.html)、
  [Clippy の lint 選択](https://doc.rust-lang.org/clippy/usage.html)も参照する。

PR 前の共通確認は [workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。
