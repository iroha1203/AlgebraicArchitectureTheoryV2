# 共有反証チェックリスト(refutation checklist)

全レビュー SKILL(`math-lean-review`, `tool-review`, `website-review`,
`docs-review`, `review-pr`, `prd-completion-review`)が読む共有 reference。
チェックリスト内容の正本はこのファイルであり、各 SKILL は項目を
複製せずここを参照する。設計根拠は
`docs/note/codex_skill_audit_redesign_note.md`。

ここにある項目は**反証の手がかり**であり、消化して終える確認リストではない。
各レビュワーは「この主張を落とすとしたらどこか」を先に立て、該当する項目で
反証を試み、その試行と失敗を報告する(敵対レビュー原則)。

## 1. Lean 反証チェックリスト(基底6項目)

昇格・証明・発火を主張する対象では、statement を実読して反証を試みる。
台帳・inventory・checklist の status 記載は根拠にしない。

- **結論射影**: 定理の結論が仮定 structure のフィールド取り出しに
  なっていないかを疑う。
- **True 充足**: 仮定・フィールドが `True` で充足可能な `Prop`
  (`field : Prop` + `field_holds` 型)でないかを疑う。
- **instance 実在**: 主張された instance / witness がリポジトリに
  実在するかを疑う。`(E : …)` 前提の条件文しか無い場合、その定理は
  未発火として扱う。
- **非退化発火**: 発火例の係数・担体が PUnit、自明群、singleton site、
  `True` 充填でないかを疑う(PRD / 本文が退化例を明示的に許容する場合を除く)。
- **公理**: 対象定理が kernel 公理検査(`#assert_standard_axioms_only` /
  AxiomAudit)に収載され、公理依存が標準公理のみかを疑う。
- **anti-weakening**: statement が本文ラベル・PRD・移植元宣言の主張より
  弱まっていないかを疑う。疑いの有無にかかわらず、蒸留・移植タスクでは
  §3 の移植元 conjunct 対応を必須で実施する。

## 2. 意味レベルの空虚化(字面 scan では捕まらない)

PUnit / True / False の字面パターンが禁止された後、同じ空虚化は
**意味レベル**へ改名 repackage される(#3099 / #3139 再レビューの実例)。
statement の意味を読んで反証を試みる。

- **subsingleton 等式型**: 等式・命題の型が subsingleton 上にあり、
  主張が自動的に成立していないか。
- **proof-irrelevance 恒真連言**: 連言・conjunct が proof irrelevance で
  恒真になっていないか。
- **answer-encoding**: 結論相当の情報が入力(引数・フィールド・
  型パラメータ)にエンコードされていないか。
- **装飾的係数**: 見かけ上非自明な型(ZMod 2 等)が使われているが、
  証明の中でその非自明性が実際には使われていないか。
- **恒真フィールド**: `Nonempty (X = X)` 型など、rfl で常に充足可能な
  証明書フィールドがないか。是正の推奨形は、等式証明書を型レベルの
  固定に置き換えること(先例: #3159 の `ofAddCommGrpValued` 化)。
- **instance ペアの欠如**: 新規の Prop 述語・certificate 構造に、
  満たす instance と満たさない instance の両方が提供されているか。
  片方しか無い述語は空虚化(常に真/常に偽)を疑う。実装者が
  「片方は作れない」と申告している場合、その理由を実読で検証する —
  理由自体が空虚性(常に真/常に偽であること)を示唆しているなら
  それが finding である。

## 3. 移植元 conjunct 対応(Research 下限原則)

**タスク型宣言は信用しない(宣言も監査対象)。** 差分が本体
(`Formal/AG` 本線)に新しい theorem・定理群を追加する場合、宣言が
「修正」「新規実装」であっても、Research に同主題の宣言が無いかを
`docs/aat/research_evidence_index.md` と `Formal/AG/Research/` の `rg`
検索で**必ず**確認し、検索語と結果を報告に記録する(索引が空の期間は
特に、直接検索を省略しない)。同主題の受理宣言が見つかれば、宣言に
かかわらず本節の移植監査を適用する — **疑わしきは移植に倒す**。

対象が蒸留・移植タスク(Issue / PR のタスク型宣言が「移植」)の場合、
または上記の検索で Research 由来と判明した場合:

1. 移植元(`Formal/AG/Research/` の受理 theorem、または
   `docs/aat/research_evidence_index.md` の該当行)の statement を実読し、
   結論一覧(conjuncts)を列挙する。
2. 本体 statement の結論と 1 対 1 の対応表を作る(実装者が PR 本文に
   置いた対応表は監査対象の**申告**であり、レビュー側は独立に再構築して
   申告と突合する。申告をそのまま証拠採用しない)。
3. 対応が取れない結論が1つでもあれば anti-weakening finding とする。
   移植元が構成していた対象(comparison、witness、certificate)を
   本体が入力 premise に移していれば、それも弱化である。
4. Research 側に同等以上の statement が受理済みである限り、本体側の
   欠落は「境界」ではなく `unported (Research-proved)`(未移植)と呼ぶ。
5. **依存 repackage の禁止(移植 ≠ import)**: 「移植した」という主張の
   実体が `Formal.AG.Research` の import +再導出ラッパーなら、それは
   蒸留ではなく依存 repackage であり、status は `unported` のまま。
   本体(`Formal/AG` 本線・`Formal.lean` 配線)から Research への import は
   方向規律違反(Research → 本体のみ可)として、レーンの裁量なしに
   hard fail とする(検査コマンドは §6)。
6. **移植 ≠ 逐語コピペ**: 蒸留とは、本体の規律(命名、台帳同期、
   AxiomAudit 収載、instance ペア、足場を持ち込まない)に従った本体内での
   再構成である。Research ファイルの逐語複製は、cycle 足場・補題群・
   公理面を無審査で本体へ持ち込む経路になる。コピペ由来が疑われる差分
   (Research 側と同名・同構造の宣言群)では、`#print axioms` の差分、
   AxiomAudit 収載、持ち込まれた補助宣言の要否を必ず検査する。

## 4. no-go 適用範囲(境界資格条件の正本)

台帳・docs・PR 本文が境界(selected input、no-go、沈黙、
「〜とは主張しない」)を記載する場合、その資格を検証する:

1. 不可能性の証拠(no-go 定理、反例)が**宣言名で名指し**されているか。
2. その定理の statement を実読し、**量化対象(任意ペアか、生成・特定
   ペアか)が境界化対象を実際に覆うか**。
3. 覆い方が一文で書かれているか。

いずれかを満たさない境界記載は、境界ではなく `unported` または未達で
あり、境界記載自体を finding とする(先例: #3159 初回の
「任意ペア no-go による生成ペア境界の正当化」)。

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
rg -n "(\/Users\/|\/home\/|C:\\\\Users\\\\|Documents\/|HelloLean|nakahata|private\/internal|\.codex|AlgebraicArchitectureTheoryV2)" <changed-files>
# Research 境界(本体から Formal.AG.Research への import 禁止。
# Research 集約ルート Formal/AG/Research.lean 自身の内部 import は正当なので除外)
rg -n "import Formal\.AG\.Research" Formal Formal.lean \
  --glob '!Formal/AG/Research/**' --glob '!Formal/AG/Research.lean'
```

Research 境界 scan の判定規則: ヒットが**差分で新規に追加された行**なら
hard fail(レーン裁量なし)。差分と無関係な既存ヒット(main 由来)は、
その PR の Reject 理由にはせず、**既存の境界違反 blocker** として
ユーザーへ即時報告する(黙認しない)。

- **横断 privacy 報告義務**: sub-agent は担当観点にかかわらず、
  センシティブなローカルパス・個人名・private/internal 風 fixture 値・
  作業環境固有名を見つけたら報告する。
- Tooling / release 出力では、repo-local docs path や読めない
  source-of-truth path の露出も確認し、必要なら `aat-theory:*` /
  `archsig-contract:*` のような安定 ID を求める。

## 7. finding ゼロ報告の資格条件

「重大な指摘なし」を報告してよいのは、**何を反証しようとして、
どの証拠で失敗したかを最低3件明記した場合のみ**。反証試行の記載がない
finding ゼロ報告は、レビュー未実施として扱われる(統合判定で棄却)。
