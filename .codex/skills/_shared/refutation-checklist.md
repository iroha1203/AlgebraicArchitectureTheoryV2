# 共有反証チェックリスト(refutation checklist)

全レビュー SKILL が読む横断 reference。scope資格、帰属、機械scan、
findingゼロ資格を扱う。Lean固有のstatement・空虚化・移植監査は
`lean-refutation-checklist.md`、実行契約は`review-protocol.md`を正本とする。
各SKILLは項目を複製せず参照する。

## 4. no-go 適用範囲(scope 記載の資格条件の正本)

台帳・docs・PR 本文が scope 制限(selected input、no-go、沈黙、
「〜とは主張しない」)を記載する場合、その資格を検証する
(AGENTS.mdの禁止語対応表も参照):

1. 不可能性の証拠(no-go 定理、反例)が**宣言名で名指し**されているか。
2. その定理の statement を実読し、**量化対象(任意ペアか、生成・特定
   ペアか)が scope 制限の対象を実際に覆うか**。
3. 覆い方が一文で書かれているか。

いずれかを満たさない scope 制限記載は、scope 制限ではなく `unported`
または未達であり、その記載自体を finding とする(先例: #3159 初回の
「任意ペア no-go による生成ペア scope 制限の正当化」)。

## 5. 帰属・ロック値・fixture の実体(全分野)

- **帰属の実在と方向**: theoremRef・部/定理番号・本文ラベルへの帰属は、
  参照先に該当番号の定理が実在し、主張の方向(肯定/否定、対偶)が
  本文・設計正本の写像と一致するかを本文で確認する
  (先例: #3152 の part4/3.4 誤帰属)。
- **ロック値の出自**: golden / lock テストの期待値は設計正本・本文まで
  遡って検証する。誤値がロックされると green が誤りの証拠保全になる。
- **名前だけ repackage**: 仕様上の名前(本文ラベル、fixture 名、
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
```

Research import方向scanの判定規則: ヒットが**差分で新規に追加された行**なら
hard fail(レーン裁量なし)。差分と無関係な既存ヒット(main 由来)は、
その PR の Reject 理由にはせず、**既存のimport方向違反 blocker** として
ユーザーへ即時報告する(黙認しない)。

- **横断 privacy 報告義務**: sub-agent は担当観点にかかわらず、
  センシティブなローカルパス・個人名・private/internal 風 fixture 値・
  作業環境固有名を見つけたら報告する。
- Tooling / release 出力では、repo-local docs path や読めない
  source-of-truth path の露出も確認し、必要なら `aat-theory:*` /
  `archsig-contract:*` のような安定 ID を求める。

## 7. finding ゼロ報告の資格条件

「重大な指摘なし」を報告してよいのは、**担当観点に適用可能な反証面を
被覆し、何を反証しようとして、どの証拠で失敗したか、対象外とした反証面と
理由を明記した場合のみ**。件数を先に固定しない。被覆根拠のないfindingゼロ
報告は、レビュー未実施として扱う(統合判定で棄却)。
