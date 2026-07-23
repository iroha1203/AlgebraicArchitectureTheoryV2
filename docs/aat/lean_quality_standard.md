# Lean 品質基準(mathlib 型 statement review 基準の正本)

AGENTS.md「「境界」という言葉の使用を禁止する」節が採用を宣言した
mathlib 型 statement review 基準の正本。AAT / Lean 形式化
(`Formal/` の新規・変更宣言)に適用する。

- この文書が正本であり、各 SKILL(`math-lean-review`, `prd-loop`,
  `research-loop`, `target-theorem-loop`)は項目を複製せず参照する
  (`refutation-checklist.md` と同じ運用)。
- 適用対象は**新規・変更宣言**。既存宣言への遡及適用は別タスクとして
  扱い、この基準を理由に無関係な既存コードを書き換えない。
- mathlib の規律のうち採用するものと採用しないものを明示する(§3.5)。
  黙って省かれた項目を実装者が再解釈する余地を残さない。

各規則には判定方法のタグを付ける。

- **[機械]**: リンター・script・elaboration で判定可能。CI 執行の対象
  (§7 の送り状)。CI 配線が未整備の間もレビューで同じ判定を行う。
- **[査読]**: レビュー(math-lean-review、研究ループの品質監査)が
  statement・proof term の実読で判定する。

## §1 Statement 品質

### 1.1 material premise の三分類申告 [査読]

theorem の各仮定(明示引数、typeclass、structure field、
certificate field)を、実装者が PR 本文・候補カード・GOAL ledger で
次の三分類に申告する。

1. **本文由来**: 数学本文の対応する定理が同じ仮定を置いている。
   本文ラベル(部・定理番号)を併記する。
2. **放電済み**: 別 theorem / construction / instance chain がこの
   premise を対象の入力 data から生成する。放電する宣言名を併記する。
3. **未放電**: 上のどちらでもない。

規則:

- **申告がない仮定はデフォルト未放電**として扱う。
- 未放電仮定を持つ theorem の status は `proved` を名乗れない。
  最大で `packaged (assumption-relative)`(`docs/aat/guideline.md` の
  Lean status discipline)。
- 申告は**監査対象の申告であって証拠ではない**。レビュー側は premise を
  独立に列挙して申告と突合する(refutation-checklist §3 の移植対応表と
  同じ扱い)。
- 未放電仮定を「明示 scope」「stated scope」と呼び替えて close 根拠に
  しない(AGENTS.md 禁止語対応表)。scope を名乗れるのは本文由来の
  仮定だけである。

### 1.2 premise 使用性 [機械: `unusedArguments`]

theorem statement に現れる全 premise が proof term で実際に使われて
いること。未使用 premise は「statement を強く見せる装飾」であり
major finding とする(mathlib `unusedArguments` リンター相当)。
未使用が意図的な場合(API の将来互換など)はその理由を docstring に
書き、レビューが妥当性を判定する。

### 1.3 API 接続義務 [査読]

新規 def は、mathlib の既存概念または本体既存 API への接続
(comparison map、instance、同値定理、restriction との互換)を
最低1つ持つ。どの既存 API とも接続しない閉じた wrapper は査読を
通さない(AGENTS.md の宣言の具体化)。theorem は次のどちらかの
位置づけを宣言する。

- 固定 statement(§5)または本文ラベルに対応する主定理
- 主定理を支える API 補題(どの定義の API かを docstring に書く)

### 1.4 instance ペア [査読]

新規の Prop 述語・certificate 構造には、満たす instance と満たさない
instance の両方を提供する(空虚化検査。refutation-checklist §2 と
同一項目。判定の観点は checklist 側、提供義務はこの基準側が正本)。
片方が作れない場合はその理由を書き、レビューが理由自体の空虚性を
検査する。

## §2 定義品質

### 2.1 小さい定義、data と Prop の分離 [査読]

定義は小さく保ち、data(構成)と Prop(性質)を分離する。性質は
定義の field に混ぜず、別の述語・theorem として育てる
(`docs/aat/guideline.md` の既存方針の再掲。正本はこちら)。

### 2.2 definitional escape の禁止 [査読]

結論相当の性質を定義の field・構成の選択に埋めて、statement 固定
(§5)を定義側で迂回しない。固定 statement が参照する def の
signature 変更は statement 変更と同じ扱い(§5.3 drift 規則)。

### 2.3 mathlib 再発明の禁止 [査読]

mathlib に同型の概念(順序、束、圏、位相、コホモロジーの部品など)が
あれば再発明しない。mathlib の概念をそのまま使うか、使えない理由を
Implementation notes(§2.5)に書いた上で comparison 定理で接続する。
AAT 専用の仮置き wrapper や名前だけの analogue で満足しない
(`docs/aat/guideline.md` 位置づけの再掲)。

### 2.4 no-unfold API 規律 [査読]

定義を作ったら、下流の証明が定義を unfold しなくて済む API 補題を
揃える。下流の証明が `unfold` / `show` による定義展開 /
`simp only [Foo]` で定義の中身を剥いている箇所は API 欠落のシグナル
として finding にする。定義直後の基本補題(constructor / destructor /
ext / 特徴づけ)までを定義とセットで1つの作業単位とする。

### 2.5 Implementation notes [査読]

自明でない設計選択を持つ新規 def・structure には、module docstring
または宣言 docstring に `Implementation notes` を書く。最低限:

- なぜこの定義形か(本文のどの概念・どの presentation に対応するか)
- 退けた代替案と理由

証明しやすさに合わせて定義形を選んだ場合、それ自体は禁止しないが
必ずここに申告する。申告のない target-fitting な定義形は、
target-theorem-loop の route_integrity_audit / math-lean-review で
「ズルい proof route」側に分類される。

## §3 スタイル(mathlib 準拠の採用サブセット)

### 3.1 命名 [査読]

mathlib 命名規約に従う。theorem 名は結論を記述する
(`foo_of_bar`、`foo_iff_bar`、`foo_comm` 式)。宣言種別ごとの
大文字小文字(def / structure / class は upperCamelCase 型名、
theorem は snake_case)も mathlib に合わせる。AAT 固有語彙
(Atom、LawAlgebra など)は AAT の語彙のまま名前に使ってよい。

### 3.2 docstring [機械: `docBlame`]

新規・変更宣言には `/--` docstring を付け、新規ファイルには
module docstring(`/-! -/`)を置く。docstring は主張の言い直しでは
なく、本文ラベルとの対応、position(主定理か API 補題か)、
仮定の由来(§1.1 の要約)を書く。既存宣言への遡及は要求しない。

### 3.3 補題分解 [査読]

証明は小さい補題に分解する。1つの長大な証明ブロックより、
再利用できる中間補題の列を優先する(mathlib の「小さい補題+API」
哲学)。ただし cycle 足場の量産と区別するため、研究ループでは
足場衛生規律(research-loop G3)に従う。

### 3.4 def / theorem 区別 [機械: `defLemma` 相当]

Prop を証明する宣言は `theorem`(または `lemma`)、data を作る宣言は
`def` にする。Prop を `def` で包むと statement 突合・公理検査の
対象から見えにくくなるため、区別違反は repackage の疑いとして
finding にする。

### 3.5 不採用項目(明示)

次の mathlib 規律は現時点で採用しない。採用しない理由ごと明示する
ことで、実装者の再解釈を防ぐ。

- **simp normal form の全面運用**: 採用しない。ただし `@[simp]` を
  付ける場合は、simp ループを作らないこと・normal form の方向を
  docstring に書くことだけを義務とする。
- **universe polymorphism の強制**: 採用しない。AAT は有限・具体対象
  中心であり、必要になった時点で個別判断する。
- **mathlib 本体への upstreaming 前提の一般化**: 採用しない。AAT 固有
  概念は AAT の語彙で書き、mathlib 概念への接続は §1.3 の
  comparison map で行う。

## §4 検証と記録

### 4.1 公理検査 [機械]

- 新規 theorem は `#print axioms` で公理依存を確認し、標準公理のみで
  あることを AxiomAudit(`#assert_standard_axioms_only`、
  `Formal/AG/AxiomAudit.lean` / `Formal/Util/AssertStandardAxioms.lean`)
  に収載する。
- `axiom` / `admit` / `sorry` / `unsafe` は明示的な相談なしに導入しない
  (既存規律の再掲)。

### 4.2 rename の deprecation 規律 [査読]

`Formal/` または Research側sourceに実在する宣言を rename する
場合、次のどちらかを同一 PR で行う。

- `@[deprecated (since := "<日付>")]` alias を残す
- 対応するLean source、GOAL、Issueを同時に更新する

silent rename は対応するLean source・GOAL・Issueの追跡を切り、監査を空振りさせる repackage
経路なので finding とする。

## §5 Target statement の一次仕様と直接査読

### 5.1 一次仕様の固定と参照可能性

- **Lean実装計画**: 実装開始前に、作業が指定する一次仕様を一つ特定し、target claim、
  必要な結論、明示された仮定・受け入れ条件を参照可能にする。target theoremや新規defの
  **名前+完全なLean signature**を記録してよいが、これは開始条件ではない。
- 一次仕様はPRD、GOAL・候補カード、GitHub Issue、現行docs、数学本文、その他の
  task artifactのいずれでもよい。tracking Issueまたは作業artifactから正確な位置を
  特定でき、実装者と査読者が実装中に参照できることを必須とする。
- 同じclaimやsignatureを複数箇所へ正本として複製しない。別artifactでは一次仕様の位置を参照する。
  実装ループ中は指定した一次仕様を不変入力として扱い、変更が必要なら§5.3で停止する。
- **research-loop**: 候補カードの`planned_lean_statement`は、固定statement本体または
  指定した一次仕様への正確な参照を持つ。G2審判はその正本を審査し、G3は実装との一致を
  合格条件とする。
- **target-theorem-loop**: GOALカードは、固定statement本体または指定した一次仕様への
  正確な参照を持つ。ループ中はその正本を変更しない。

### 5.2 一致判定[査読]

固定 statement と実装 declaration の一致は、一次仕様と実装本体を直接突合して判定する。
一次仕様に完全Lean signatureがある場合、査読者はtarget theoremと新規defについて、名前、
universe、明示・暗黙引数、typeclass、structure / certificate field、結論を照合する。
完全signatureがない場合は、一次仕様のclaim、必要な結論、明示された仮定・受け入れ条件から
査読対象を再構成して実装 declaration、premise、proof-useを検査する。premise の追加・結論の
弱化・対象の縮小はanti-weakening finding とする。

補助Leanファイル、aggregate import、CI step、commit順、fixture lockの有無や形式は
この判定の根拠にしない。`lake build`、AxiomAudit、lint、premise diff reportはそれぞれの
規律を確認するが、固定 statement の一致は代替しない。

一次仕様が参照するdef側の改変(§2.2 definitional escape)も、def signatureと実装本体を
同時に読む。signatureだけの一致を完了根拠にせず、仮定放電、certificate provenance、
proof-use、actual APIへの接続を査読する。

一次仕様から対象 claim、必要な結論、受け入れ条件を判定できない場合だけ、実装開始または
完了判定を止めて作業入力の明確化を求める。完全Lean signatureの不在そのものは停止理由にしない。

### 5.3 drift 規則

実装中に固定 statement(参照される def の signature を含む)の変更が
必要になったら、その時点で**未達として停止して報告する**
(AGENTS.md の停止規則の手続き化)。

- PRD: PRD 欠陥または要求未達としてユーザーへエスカレートする。
  ループ内で PRD を編集しない。
- research-loop: G3 合格を出さず G2 再審判へ戻す。乖離した statement の
  まま G4 / G5 へ進む経路を残さない。
- target-theorem-loop: GOAL 改訂提案を tracking Issue に残して止まる
  (現行規律のまま)。

## §6 Research sandbox での適用点

この基準の適用点は**受理点**である。

- 適用する: `lean-verified` 判定(research-loop G3)、スパイン宣言、
  proof-obligation-discharged(target-theorem-loop)、本体
  (`Formal/AG` 本線)への全変更。
- 適用しない: サイクル途中の探索足場(premise 順列帯、再入口変種、
  checkpoint 帯)。ただし足場衛生規律(受理ルートと足場が命名・
  ファイル分割で区別できること)が前提であり、区別できない場合は
  受理ルート全体にこの基準を適用する。

探索の自由度は殺さない。錨になる瞬間(受理・登録・蒸留元化)だけ
締める。

## §7 機械検査一覧(執行層への送り状)

[機械] タグ項目は CI の現行AAT代数幾何ジョブまたは Research integrity gates で執行する。

| 検査 | 規則 | 実装状態 |
| --- | --- | --- |
| AxiomAudit | §4.1 | CI step `Kernel axiom audit`: `lake env lean Formal/AG/AxiomAudit.lean` と末尾 `#assert_standard_axioms_only AAT.AG.AxiomAudit` 確認 |
| Research import 方向 | refutation-checklist §6 | CI step `Research import direction scan`: `.github/lean_quality/check_research_import_direction.sh` が `research/lean/ResearchLean` 外への新規 `import ResearchLean.AG` 追加を fail |
| premise 一覧 | §1.1 | CI step `Premise diff report`: `.github/lean_quality/list_premise_diff.sh` が `.tmp/lean-quality/premise-diff.txt` を出力する。これはレビュー突合用で hard fail ではない |

Research import 方向 scan は diff 上の新規追加行だけを hard fail にする。
Lean 内 `assert_not_exists` 方式は、現時点では採用しない。既存 main に
残る import を含めて全履歴を無条件 fail にし、Issue #3172 の
「既存 finding は baseline 固定し増分だけ fail」の条件と衝突するためである。
