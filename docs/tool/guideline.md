# Tooling 編集ガイドライン

この文書は、`tools/` と `docs/tool` を編集するときの作業方針を定める。

## 位置づけ

- ArchSig の製品像は [ArchSig v0.6.0 製品コンセプト](archsig_v0_6_0_concept.md) にある。
- このガイドラインには作り方の規律を書き、コマンド・フィールド・計算仕様の詳細はマニュアルに置く。
- 文書と作業記録の分担は [Workflow guideline](../workflow/guideline.md) の
  「ドキュメントをステートレスに保つ規則」に、PRD の扱いは [PRD guideline](../prd/guideline.md) に従う。
- ArchView と FieldSig は ArchSig の出力を読み、AAT の構造解析の判定・結論には ArchSig の計算結果を用いる。

## 責務範囲(入力トライアドの正本)

- ArchSig の意味上の入力は、Atom 定義・Law・ArchMap の3つである。Atom 定義は共通の語彙・型・意味を
  持つ独立した定義元であり、Law と ArchMap の両方から参照する。ファイル形式としてのまとめ方と、
  意味上の入力の役割は区別する。
- ArchMap にはコードから観測した Atom だけを記述する（判定・結論・局所の分け方は計算側・Law 側の責務とする）。
- Law は特定のコードの観測値から独立に、設計上の出発点として必要な区別を定め、Atom 定義を参照して
  関係・制約・読み方を宣言する。複数の Law が同じ Atom 定義を共有できる。
- AAT の理論本体の所在は
  [AGENTS.md「理論本文の参照先」](../../AGENTS.md#理論本文の参照先)にある。
- ArchSig は、与えられた Atom 定義・Law・ArchMap から結論が正しく導かれたことを保証する。
  観測自体がコードに忠実であることの担保は、観測を行う側（製品の SKILL）の責務とする。
- エンジンは定義・宣言・観測事実の型と参照を検査し、計算構造・equation realization・写像の構成までを
  処理系側の責務として完結させる。
- 入力から決まらない事項は、正常な出力の一種である判断不能（沈黙）として理由とともに返す。
- 計算の中核はプログラミング言語やフレームワークから独立に設計し、命名規則やファイルとモジュールの対応といった
  言語固有の知識は解析器と製品の SKILL の側に置く。
- 観測の対象は実装コードの構造とする。
- ArchSig の説明では、何を入力して何を計算するかを肯定形で書く。

## 作り方

- マニュアルに書かれていない振る舞いを実装で決めたら、同じ変更の中でマニュアルにも反映し、
  仕様を文書と同期して保つ。
- 実装は、マニュアルにある具体的な使い方の一つ（第2章の一連の流れなど）を単位として進め、
  その使い方に必要なものだけを入れる。
- CI との連携、終了コード、エラー形式、キャッシュ、入力の拒否や防御的な制約は、
  実際に動かして必要性がはっきりしてから追加する。
- レビューは Issue の受け入れ要件とこのガイドラインの品質規約に照らして行い、
  具体的な不変条件違反・逆向き依存・不正なテストを修正対象とする。
- Claude による実装は PRD に沿って進め、手順は `.claude/skills/prd-loop` と `.claude/skills/pr-review` に従う。
- PRD の完了は、PRD の受け入れ要件と実装済みのテストで判定する
  （判定範囲は [Workflow guideline](../workflow/guideline.md#完了レビューの判定範囲) に従う）。

## Rust 品質規約

### 設計と実装

- 数学・判定の中核は CLI、ファイルシステム、OS 計測から独立させ、責務と依存の向きが明確で自然な粒度の構成を選ぶ。
- 意味のある状態と不変条件は、型や検証済みの構築経路で表現する。未観測と観測済みの零、未検証と検証済みを
  型で区別し、検証済みの不変条件が外部から保たれる API を設計する。
- API の入力・出力・エラー・副作用を明確にし、利用者に必要な失敗条件を説明する。
  不正な入力は既定値・無制限予算・成功へ黙って変換せず、明示的なエラーとして返す。
- 想定される入力エラーや I/O 失敗は `Result` で返す。`panic!`、`unwrap`、`expect` は成立根拠のある
  不変条件やテストの準備失敗に限る。
- 所有権と借用は素直に扱い、不要な `clone`・`Arc`・`Mutex` と過度な lifetime 複雑化のバランスを
  読みやすさ基準で取る。
- `unsafe` は必要性を説明できる最小範囲に限定し、安全条件とその成立根拠を明記する。
- `rustfmt` を使い、変更に関係する Clippy lint を選んで品質を確認する。

### 簡素化と引き算

- 現在の要求で使う機能・設定・拡張点に絞り、既存の検証や変換を再利用して実装を一本化する。
- trait、ラッパー、層は、実際の依存分離・再利用・読みやすさへの具体的な効果がある場所に置く。
- 必要な振る舞いや安全検査を保ったうえで、理解・変更・運用の負担を下げる方向で
  公開範囲・依存・保持状態・キャッシュ・出力をスリムに保つ。

### レビューでの扱い

- 指摘では、該当箇所・具体的な問題・最小の修正案を簡潔に示す。
  既存の独立査読と共有の review protocol が求める反証根拠や未確認範囲は、必要な分だけ残す。
- 簡素化の確認は既存レビューの観点の一つとして、具体的な設計上の負担を基準に行う。

## テスト責務と実行経路

- ツールのテストは、そのツール自身の計算と出力を確かめる。
- テスト入力と期待値は、README・マニュアル・website の本文から独立したフィクスチャと明示的な引数で用意し、
  文書の編集から独立して製品テストが成立する構成を保つ。
- ArchSig のテストは、マニュアルに書かれた振る舞いと公開仕様（contract）を検証する。
  マニュアルの例を基にテストを設計し、コマンドを実行して結果を確かめる。

### テストの書き方

- 検査できる最も狭い層を選び、役割を分担する。数学・判定の組合せは単体テストまたは内部統合テスト、
  コンポーネントや公開 API の仕様は統合テスト、引数・終了状態・出力・保存・再利用は実バイナリの
  E2E テストで確認する。
- 仕様の成立に直結する値・状態・エラー種別を検証し、期待値は検査対象から独立した根拠に基づいて構成する。
- 回帰テストは、可能な範囲で修正前に失敗し、修正後に成功することを確かめる。
  振る舞いと仕様を検査対象とし、フィクスチャやテスト補助コードは条件と期待値が読み取れる最小構成にする。
- ファイルやプロセス環境を隔離し、時刻や乱数を制御する。同期は状態遷移や完了通知で行い、
  自分が起動した子プロセスには独立した待機上限を設けて確実に終了・回収する。
- アサーションの弱化、スナップショットの無検討な更新、製品予算の緩和でテストを通してはならない。
  重複を除いて適切な層へ配置し、性能測定と正しさの検査を区別する。

### CI への追加

CI への追加は [Workflow guideline](../workflow/guideline.md#ci-への恒久追加の禁止) の承認規律に加え、
想定する CI 環境で準備・コンパイル・テストの合計が3分以内である実測を条件とする。
この時間条件は本プロジェクト固有の要件である。

### 参考と採用範囲

上記は本プロジェクトで採用する規約である。以下の資料から設計・検査の考え方を参照し、
本プロジェクトの要件に合う範囲で取り入れている。

- [Google Code Review](https://google.github.io/eng-practices/review/reviewer/looking-for.html): 現在必要な設計、複雑さ、テストの妥当性。
- Rust API Guidelines: [型安全性](https://rust-lang.github.io/api-guidelines/type-safety.html)、
  [表現の隠蔽](https://rust-lang.github.io/api-guidelines/future-proofing.html)、[失敗条件の文書化](https://rust-lang.github.io/api-guidelines/documentation.html)。
- rust-analyzer: [依存分離](https://rust-analyzer.github.io/book/contributing/architecture.html)、
  [style review](https://rust-analyzer.github.io/book/contributing/style.html)。
- Rust Book: [Result と panic](https://doc.rust-lang.org/book/ch09-03-to-panic-or-not-to-panic.html)、
  [テスト構成](https://doc.rust-lang.org/book/ch11-03-test-organization.html)、[実行と共有環境](https://doc.rust-lang.org/book/ch11-02-running-tests.html)。
  Rust Compiler Development Guide の[回帰テスト](https://rustc-dev-guide.rust-lang.org/tests/adding.html)、
  [Clippy の lint 選択](https://doc.rust-lang.org/clippy/usage.html)も参照する。

PR 前の共通確認は [Workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。
