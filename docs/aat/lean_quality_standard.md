# Lean 品質基準（mathlib 型 statement review 基準）

この文書は、[guideline.md](guideline.md) の「「境界」という言葉の使用を禁止する」節で
採用を定めた mathlib 型 statement review 基準を定義する。AAT / Lean の形式化
（`Formal/` の新規・変更宣言）に適用する。

- 各 SKILL（`math-lean-review`、`prd-loop`、`research-loop`、`target-theorem-loop`）は
  この基準の項目を複製せず参照する（`refutation-checklist.md` と同じ運用）。
- 適用対象は**新規・変更宣言**に限る。既存宣言への遡及適用は別タスクとして扱い、
  この基準を理由に無関係な既存コードを書き換えない。
- mathlib の規律のうち採用するものと採用しないものを明示し（§3.5）、
  省かれた項目を実装者が独自に再解釈する余地を残さない。

各規則には判定方法のタグを付ける。

- **[機械]**: リンター、スクリプト、elaboration で判定できる項目。CI での自動検査の対象
  （§7 を参照）。CI への組み込みが未整備の間も、レビューで同じ基準を判定する。
- **[査読]**: レビュー（`math-lean-review` や研究ループの品質監査）で
  statement と proof term を直接読んで判定する項目。

## §1 Statement 品質

### 1.1 material premise の三分類申告 [査読]

定理の各仮定（明示引数、typeclass、structure field、certificate field）について、
実装者は PR 本文・候補カード・GOAL 台帳に次の三分類を申告する。

1. **本文由来**: 数学本文の対応する定理が同じ仮定を置いている。
   本文ラベル（部・定理番号）を併記する。
2. **放電済み**: 別の定理・構成・instance chain が、この premise を対象の入力データから生成する。
   放電する宣言名を併記する。
3. **未放電**: 上のどちらにも当たらない。

規則:

- **申告がない仮定は既定で未放電**として扱う。
- 未放電仮定を持つ定理の状態は `proved` と名乗れず、
  最大で `packaged (assumption-relative)` とする（`docs/aat/guideline.md` の
  Lean status discipline を参照）。
- 申告は**監査の対象であり、それ自体は証拠ではない**。レビュー側は premise を
  独立に列挙して申告と突合する（`refutation-checklist.md` §3 の移植対応表と同じ扱い）。
- 未放電仮定を「明示 scope」「stated scope」と呼び替えて完了の根拠にしない
  （`guideline.md` の禁止語対応表を参照）。scope を名乗れるのは本文由来の仮定だけである。

### 1.2 premise 使用性 [機械: `unusedArguments`]

定理の statement に現れるすべての premise が、proof term の中で実際に使われていること。
未使用の premise は主張を実際より強く見せてしまう不要な要素であり、
重大な指摘（major finding）とする（mathlib の `unusedArguments` リンター相当）。
未使用が意図的な場合（API の将来互換など）はその理由を docstring に書き、
レビューで妥当性を判断する。

### 1.3 API 接続義務 [査読]

新規の `def` は、mathlib の既存概念または本体既存 API への接続
（comparison map、instance、同値定理、制限写像との互換など）を最低1つ持つ。
どの既存 API とも接続しない閉じたラッパーは査読を通さない
（`guideline.md` の禁止語規律の具体化）。定理は次のどちらの位置づけかを明示する。

- 固定 statement（§5）または本文ラベルに対応する主定理
- 主定理を支える API 補題（どの定義に対する API かを docstring に書く）

### 1.4 instance ペア [査読]

新規の `Prop` 述語や certificate 構造には、条件を満たす instance と満たさない instance の
両方を用意する（空虚化の検査。`refutation-checklist.md` §2 と同一項目であり、
判定の観点はチェックリスト側、提供義務はこの基準側に定める）。
片方が作れない場合はその理由を書き、レビューでその理由自体が空虚でないかを確認する。

## §2 定義品質

### 2.1 小さい定義、data と Prop の分離 [査読]

定義は小さく保ち、data（構成）と `Prop`（性質）を分離する。性質は
定義のフィールドに混ぜず、別の述語や定理として証明する
（`docs/aat/guideline.md` にある方針の基準）。

### 2.2 definitional escape の禁止 [査読]

結論に相当する性質を定義のフィールドや構成の選択に埋め込み、statement 固定（§5）を
定義側で迂回しない。固定 statement が参照する `def` の signature 変更は、
statement の変更と同じ扱いとする（§5.3 の drift 規則）。

### 2.3 mathlib 再発明の禁止 [査読]

mathlib に同型の概念（順序、束、圏、位相、コホモロジーの部品など）がある場合は再発明しない。
mathlib の概念をそのまま使うか、使えない理由を Implementation notes（§2.5）に書いたうえで
comparison 定理で接続する。AAT 専用の仮置きラッパーや名前だけの対応物で済ませない。

### 2.4 API 設計規律（mathlib 準拠） [査読]

他モジュールや後続の部から再利用される公開の数学的概念（主要な `def` / `structure` / 圏・関手など）を定義したら、利用者が実装詳細を毎回展開せずに操作できるよう、基本 API（`ext`、`@[simps]` による射影補題、constructor / destructor、特徴づけ `_iff` 等）を定義と一体で揃える。構造体・関手・射の射影補題には `@[simps]` を積極的に用いてよく、手書きの定型補題を量産しない。

- **適用範囲**: 他モジュールから参照される公開 `def` / `structure` のインターフェースと、それを使う下流の主証明における明示的な定義展開（`unfold Foo`、`simp only [Foo]`、`dsimp [Foo]` 等）を対象とする。
- **対象外**: 単一ファイル内・証明内部の補助定義（`private` 含む）、具体例・反例の証明、および通常の `semireducible` 定義に対する Lean の definitional equality（型照合、軽い `rfl`、`change`）は対象外とする。
- **抜き打ち `irreducible` 試験の禁止**: 査読時に既存定義を局所的に `irreducible` にして暗黙の definitional equality 依存を洗い出す検査は行わない（mathlib と同じく、抽象化障壁や型検査性能の保護が必要な中核定義だけは、定義側で最初から `@[irreducible]` や `structure` として明示する）。
- **重大度の区分**: §2.4 の不足は原則として非中心 finding（設計・保守性の指摘）とし、PR 単位の直接対応で扱う。数学的主張の成立を否定する中心 finding（Major）や `$prd-completion-review` の完了ブロック条件にはしない（定義の中身を利用して仮定や結論を迂回する欠陥は、§2.2 definitional escape の中心 finding として別途扱う）。

### 2.5 Implementation notes [査読]

自明でない設計選択を含む新規の `def` や `structure` には、module docstring
または宣言 docstring に `Implementation notes` を書く。最低限、次を記す。

- なぜこの定義形を選んだか（本文のどの概念・表示に対応するか）
- 採用しなかった代替案とその理由

証明しやすさに合わせて定義形を選ぶこと自体は禁止しないが、必ずここに申告する。
申告のない都合合わせの定義形は、`target-theorem-loop` の `route_integrity_audit` や
`math-lean-review` で不適切な証明経路として指摘対象になる。

## §3 スタイル（mathlib 準拠の採用サブセット）

### 3.1 命名 [査読]

mathlib の命名規約に従う。定理名は結論を表す形にする
（`foo_of_bar`、`foo_iff_bar`、`foo_comm` など）。宣言種別ごとの大文字・小文字
（`def` / `structure` / `class` の型名は upperCamelCase、定理は snake_case）も
mathlib に合わせる。AAT 固有の語彙（Atom、LawAlgebra など）はそのまま名前に使ってよい。

### 3.2 docstring [機械: `docBlame`]

新規・変更した宣言には `/--` docstring を付け、新規ファイルには
module docstring（`/-! -/`）を置く。docstring には主張の単なる言い直しではなく、
本文ラベルとの対応、位置づけ（主定理か API 補題か）、仮定の由来（§1.1 の要約）を書く。
既存宣言への遡及的な追加は求めない。

### 3.3 補題分解 [査読]

証明は小さい補題に分解する。長大な一つの証明ブロックより、
再利用できる中間補題の列を優先する（mathlib の「小さい補題＋API」の考え方）。
ただし探索サイクルの仮足場を量産しないよう、研究ループでは
足場衛生規律（`research-loop` G3）に従う。

### 3.4 def / theorem 区別 [機械: `defLemma` 相当]

`Prop` を証明する宣言は `theorem`（または `lemma`）、data を作る宣言は `def` にする。
`Prop` を `def` で包むと statement 突合や公理検査の対象から見えにくくなるため、
この区別に反するものは repackage の疑いとして指摘対象にする。

### 3.5 不採用項目（明示）

次の mathlib 規律は現時点では採用しない。採用しない理由まで明示しておくことで、
実装者の勝手な再解釈を防ぐ。

- **simp normal form の全面運用**: 採用しない。ただし基本 API への `@[simps]` や局所的な `@[simp]` の付与は mathlib 準拠として推奨・許容する。`@[simp]` を付ける場合は、simp ループを作らないことと、normal form の向きを docstring に書くことを義務とする。
- **全定義に対する `irreducible` 展開不可耐性の強制**: 採用しない。mathlib でも `irreducible` は性能保護や明確な抽象化障壁が必要な一部の中核定義に限られるため、通常の `semireducible` 定義に対して局所 `irreducible` による暗黙展開の全面排除を求めない（§2.4）。
- **universe polymorphism の強制**: 採用しない。AAT は有限・具体的な対象を中心に扱うため、
  必要になった時点で個別に判断する。
- **mathlib 本体への upstreaming 前提の一般化**: 採用しない。AAT 固有の概念は
  AAT の語彙で書き、mathlib の概念への接続は §1.3 の comparison map で行う。

## §4 検証と記録

### 4.1 公理検査 [機械]

- 新規の定理は `#print axioms` で公理依存を確認し、標準公理のみであることを対応する監査に記録する。
  `Formal/AG` では `Formal/AG/AxiomAudit.lean` の `#assert_standard_axioms_only` を使う。
  `Formal/SHIGURE` の入口と検証手順は [SHIGURE の形式化](guideline.md#shigure-の形式化) に従う。
- `axiom`、`admit`、`sorry`、`unsafe` は明示的な相談なしに導入しない。

### 4.2 rename の deprecation 規律 [査読]

`Formal/` または Research 側のソースに実在する宣言を改名する場合は、
次のどちらかを同じ PR で行う。

- `@[deprecated (since := "<日付>")]` の alias を残す
- 対応する Lean ソース、GOAL、Issue を同時に更新する

予告や同期のない改名は、Lean ソース・GOAL・Issue の追跡を切って監査を空振りさせる
repackage 経路になるため、指摘対象とする。

## §5 Target statement の一次仕様と直接査読

### 5.1 一次仕様の固定と参照可能性

- **Lean 実装計画**: 実装を始める前に、作業が指定する一次仕様を一つ特定し、対象の主張、
  必要な結論、明示された仮定と受け入れ条件を参照できる状態にする。target theorem や新規 `def` の
  **名前と完全な Lean signature** を記録してよいが、これは開始の必須条件ではない。
- 一次仕様は PRD、GOAL・候補カード、GitHub Issue、現行ドキュメント、数学本文、その他の
  作業文書のいずれでもよい。tracking Issue または作業文書から正確な位置を特定でき、
  実装者と査読者が実装中に参照できることを必須とする。
- 同じ主張や signature を複数箇所へ基準として複製せず、別の文書からは一次仕様の位置を参照する。
  実装ループ中は指定した一次仕様を変更しない入力として扱い、変更が必要なら §5.3 に従って停止する。
- **research-loop**: 候補カードの `planned_lean_statement` には、固定 statement 本体または
  指定した一次仕様への正確な参照を置く。G2 審判はその内容を審査し、G3 は実装との一致を
  合格条件とする。
- **target-theorem-loop**: GOAL カードには、固定 statement 本体または指定した一次仕様への
  正確な参照を置く。ループ中はその内容を変更しない。

### 5.2 一致判定 [査読]

固定 statement と実装宣言の一致は、一次仕様と実装本体を直接突合して判定する。
一次仕様に完全な Lean signature がある場合、査読者は target theorem と新規 `def` について、
名前、universe、明示・暗黙引数、typeclass、structure / certificate field、結論を照合する。
完全な signature がない場合は、一次仕様の主張、必要な結論、明示された仮定と受け入れ条件から
査読対象を組み立て、実装宣言・premise・proof-use を検査する。premise の追加、結論の弱化、
対象の縮小は弱化違反（anti-weakening finding）とする。

補助 Lean ファイル、集約 import、CI step、コミット順、フィクスチャロックの有無や形式は
この判定の根拠にしない。`lake build`、AxiomAudit、lint、premise diff report はそれぞれの
規律を確認するものであり、固定 statement との一致確認の代わりにはならない。

一次仕様が参照する `def` 側の改変（§2.2 definitional escape）も確認するため、`def` の
signature と実装本体を同時に読む。signature の一致だけを完了根拠にせず、仮定放電、
certificate の来歴（provenance）、proof-use、既存 API への接続を査読する。

一次仕様から対象の主張、必要な結論、受け入れ条件を読み取れない場合だけ、実装開始または
完了判定を止めて作業入力の明確化を求める。完全な Lean signature がないこと自体は停止理由にしない。

### 5.3 drift 規則

実装中に固定 statement（参照される `def` の signature を含む）の変更が必要になったら、
その時点で**未達として停止して報告する**（`guideline.md` の停止規則の手続き化）。

- PRD: PRD の欠陥または要求未達としてユーザーへ報告する。ループ内で PRD を編集しない。
- research-loop: G3 合格を出さず G2 再審判へ戻す。乖離した statement のまま G4 / G5 へ進む経路を残さない。
- target-theorem-loop: GOAL 改訂提案を tracking Issue に残して止まる。

## §6 Research sandbox での適用点

この基準を適用するのは**受理点**である。

- 適用する: `lean-verified` 判定（`research-loop` G3）、スパイン宣言、
  `proof-obligation-discharged`（`target-theorem-loop`）、本体（`Formal/AG` 本線）への全変更。
- 適用しない: サイクル途中の探索足場（premise 順列帯、再入口変種、checkpoint 帯）。
  ただし足場衛生規律（受理ルートと足場が命名・ファイル分割で区別できること）が前提であり、
  区別できない場合は受理ルート全体にこの基準を適用する。

探索途中の試行錯誤を妨げないため、この基準は受理・登録・本体への蒸留元となる時点に限って
厳格に適用する。

## §7 機械検査一覧（CI での自動検査）

[機械] タグの項目は、CI の現行 AAT 代数幾何ジョブまたは Research integrity gates で検査する。

| 検査 | 規則 | 実装状態 |
| --- | --- | --- |
| AxiomAudit | §4.1 | CI step `Kernel axiom audit`: `lake env lean Formal/AG/AxiomAudit.lean` と末尾の `#assert_standard_axioms_only AAT.AG.AxiomAudit` を確認 |
| Research import 方向 | refutation-checklist §6 | CI step `Research import direction scan`: `.github/lean_quality/check_research_import_direction.sh` が `research/lean/ResearchLean` 外への新規 `import ResearchLean.AG` 追加を失敗させる |
| premise 一覧 | §1.1 | CI step `Premise diff report`: `.github/lean_quality/list_premise_diff.sh` が `.tmp/lean-quality/premise-diff.txt` を出力する（レビュー突合用で、自動失敗にはしない） |

Research import 方向の検査は、差分上の新規追加行だけを失敗にする。
Lean 内の `assert_not_exists` 方式は現時点では採用しない。既存の `main` に残る
import を含めて全履歴が無条件に失敗してしまい、Issue #3172 の
「既存指摘はベースライン固定し増分だけ失敗にする」という条件と衝突するためである。
