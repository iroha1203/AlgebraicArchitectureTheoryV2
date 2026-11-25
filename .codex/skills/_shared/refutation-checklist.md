# 共有反証チェックリスト(refutation checklist)

全レビュー SKILL が読む横断 reference。scope 記載要件、帰属、機械 scan、
ArchSig の3つの基本入力、finding ゼロの条件、identity 記述を扱う。Lean 固有の statement・自明化・移植監査は
`lean-refutation-checklist.md`、実行手順は `review-protocol.md` を参照する。

## 4. no-go 適用範囲(scope 記載の要件)

台帳・docs・PR 本文が scope 制限(selected input、no-go、判断不能、
「〜とは主張しない」)を記載する場合、その根拠を検証する
(`docs/aat/guideline.md` の禁止語対応表も参照):

1. 不可能性の証拠(no-go 定理、反例)が**宣言名で名指し**されているか。
2. その定理の statement を実読し、**量化対象(任意ペアか、生成・特定
   ペアか)が scope 制限の対象を実際に包含するか**。
3. 包含の仕方が一文で書かれているか。

いずれかを満たさない scope 制限記載は、scope 制限ではなく `unported`
または未達であり、その記載自体を finding とする(先例: #3159 初回の
「任意ペア no-go による生成ペア scope 制限の正当化」)。

## 5. 帰属・ロック値・fixture の実体(全分野)

- **帰属の実在と方向**: theoremRef・部/定理番号・本文ラベルへの帰属は、
  参照先に該当番号の定理が実在し、主張の方向(肯定/否定、対偶)が
  本文・設計仕様の写像と一致するかを本文で確認する
  (先例: #3152 の part4/3.4 誤帰属)。
- **ロック値の出自**: golden / lock テストの期待値は設計仕様・本文まで
  遡って検証する。誤値がロックされるとテスト成功が誤った期待値を固定してしまう。
- **名前だけの付け替え**: 仕様上の名前(本文ラベル、fixture 名、
  theorem 名)を名乗る実体は、名前ではなく中身を仕様と突合する。
  テストは名前でなく assertion 内容で証拠にする。
- **監査カバレッジの過大表示**: 台帳が「AxiomAudit 収載・監査済み・
  lint 済み」を主張する行は、実際の検査対象リスト
  (`#assert_standard_axioms_only` の allowlist 等)と突合する。

## 6. 横断機械 scan(全分野 SKILL の必須検証)

分野を問わず、レビュー対象の changed files に対して実行する。
実行できない場合は理由と残リスクを報告する。

```bash
git diff --check
# ローカル作業ツリーを対象にする場合(セルフレビュー)は未追跡ファイルも列挙する
git status --short --branch && git ls-files --others --exclude-standard
# hidden / bidirectional Unicode
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
# Lean placeholder(Formal に加え docs 側も。docs の方針説明文中の語は文脈で除外)
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
# privacy / local-path(public / release surface と changed files。
# スキル・設計 docs 自身が定義・引用する検査パターン文字列は文脈で除外してよい)
rg -n "(\/Users\/|\/home\/|C:\\\\Users\\\\|Documents\/|HelloLean|private\/internal|\.codex|AlgebraicArchitectureTheoryV2)" <changed-files>
# Research import方向(本体から ResearchLean.AG への import 禁止。)
rg -n "import ResearchLean\.AG" Formal Formal.lean
# 語彙の禁止・置換表(docs/workflow/vocabulary.md を参照)
rg -n "錨|正本|裁定|契約|右サイズ化|正枝|負枝|帳簿|玩具|衛生規則|足場衛生|湧|幻|裏取り|放電|正典|憲章|最安経路|空虚化|空洞化|蒸留|審判|反証面|資格喪失|有資格|起動資格|証拠保全|捏造|解禁|入力トライアド|合法状態" <changed-files>
```

Research import方向scanの判定規則: ヒットが**差分で新規に追加された行**なら
hard fail(レーン裁量なし)。差分と無関係な既存ヒット(main 由来)は、
その PR の Reject 理由にはせず、**既存のimport方向違反 blocker** として
ユーザーへ即時報告する(黙認しない)。

語彙scanの判定規則: ヒットが**差分で新規に追加された行**なら finding とし、
[語彙ルール](../../../docs/workflow/vocabulary.md)の禁止・置換表に従う置換を求める。
既存行のヒットは対象外(既存本文への遡及置換はしない)。ファイル名・Lean 識別子・
既存の英語識別子・置換表自身の引用は文脈で除外してよい。
対象範囲は語彙ルールの「適用範囲」節に従う(`outreach/` / `website/` の
記事本文・公開 copy のヒットは finding にしない)。

- **横断 privacy 報告義務**: sub-agent は担当観点にかかわらず、
  センシティブなローカルパス・個人名・private/internal 風 fixture 値・
  作業環境固有名を見つけたら報告する。
- Tooling / release 出力では、repo-local docs path や読めない
  source-of-truth path の露出も確認し、必要なら `aat-theory:*` /
  `archsig-contract:*` のような安定 ID を求める。

## 7. finding ゼロ報告の条件

「重大な指摘なし」を報告してよいのは、**担当観点に適用可能な確認観点を
網羅し、何を反証しようとして、どの証拠で失敗したか、対象外とした観点と
理由を明記した場合のみ**。件数を先に固定しない。確認範囲の根拠のない finding ゼロ
報告は、レビュー未実施として扱う(統合判定で採用しない)。

## 8. ArchSig 入力区分と数学対応(v0.6.0・SHIGURE 基準)

`docs/tool/guideline.md`「責務範囲（3つの基本入力）」の入力区分
(Atom 定義=共通語彙・型・意味 / Law=特定コードに依存しない規則・制約・reading・局所公開情報・許容変換仕様・目的評価条件 /
ArchMap=由来付きの観測事実・複数解釈の実現族、および実行指定の問い)を hard gate として適用する。
ArchSig への入力、CLI flag、schema field を導入・拡張する差分では次を検査する:

1. **入力帰属**: 新規・拡張される入力が Atom 定義・Law・ArchMap・問いのどれに帰属するかが一文で説明でき、
   §5「名前だけの付け替え」に従い名前ではなく中身で成立しているか。
   Law 側の要件は特定のコード実体や観測値に依存しない規則・制約・許容変換・目的評価条件であること。
   ArchMap 側の観測事実には由来(静的解析・実行観測・LLM 読解候補・人間採用)を区別して保持し、
   複数解釈が残る場合は実現族として保持しているか。
2. **結論注入と由来混同の禁止**: 成立・不整合・障害類・修復解・比較同型そのものなど、
   計算の結論相当データを外部入力として受け取っていないか。読解候補・観測事実・計算結果・数学的証明の
   種別を混ぜていないか。validator や未供給時の判断不能、fixture lock、schema 登録は帰属の代替にならない。
3. **実導出と数学対応**: その入力によって導出可能になる結論語彙を、ArchSig が実際に定義・Law・観測から計算しているか。
   論文・SHIGURE GOAL・Lean 定理の有限特殊化を実装する場合は、対応する定理参照・適用条件のコード上での
   明示検査・条件外入力に対する未対応理由の返却・実コード復元と再観測の境界が揃っているか。

いずれかを満たさない入力追加・拡張は major finding とする。

## 9. identity 記述の因果順(肯定形で書く)

- ツール・artifact・定理の identity 文は「どの入力から何を計算する /
  何を主張する」の肯定形で書く(`docs/tool/guideline.md`「責務範囲（3つの基本入力）」)。結論の相対性は
  入力仕様に由来する帰結として書かれているかを確認する。
- identity 文に否定形免責(「theorem prover ではない」「global truth では
  ない」等)が習慣的に併記されている場合、それが防ぐ読者の具体的な誤解を
  特定できなければ finding とする。防ぐ必要のある否定は、結論の近くで
  一度だけ書く。
