# AAT / Lean 編集ガイドライン

この文書は、`Formal/AG` と `docs/aat` を編集するときの作業方針を定める。

## Claim discipline

- AAT / Lean の定理・定義・レビュー説明では、選んだ atom vocabulary、Law、cover、
  係数、仮定、証明済み theorem package の範囲を肯定形で明確に述べる。
- 良い例: 「選んだ atom vocabulary と有限 cover の範囲で XXX を証明する」
  「Lean で証明済みの sheaf condition と明示された comparison map のもとで YYY が成り立つ」のように、
  主張の成立範囲を正面から示す。
- AAT の外側にある事柄（実コードベース全体の品質判定など）は通常の説明や定型の但し書きに含めず、
  実際に範囲を越えた主張を指摘する監査理由として必要な場面だけで最小限に述べる。

## 位置づけ

- 現行の AAT は代数幾何的アーキテクチャ論であり、最新の理論本体は
  [AGENTS.md「理論本文の参照先」](../../AGENTS.md#理論本文の参照先)にある。
  Law に基づいて Atom を観測し、幾何を構成する方針のもとで理論と作業を進める。
- AAT は Atom を土台に、site、Grothendieck topology、sheaf、ringed topos、scheme、
  Čech cohomology、derived / stacky structure といった代数幾何の概念へ接続する
  純粋数学理論として扱う。
- Lean 形式化は、有限で小さい対象から始める場合でも、定義、comparison map、同値、
  境界定理を通じて、可能な限り既存の数学的構造（mathlib を含む）と接続する方向へ育てる。
- Atom、Law、obstruction、flatness、signature は代数幾何版の基礎データや局所表示として、
  AAT の語彙のまま説明する。
- 実コードベースの抽出器、ArchMap の観測、LawPolicy / MeasurementProfile による計測条件の選択、
  ArchSig / FieldSig の検証・測定、実証データセットは、AAT への入力生成または後段の計測・実証層として管理する。
- Lean ソース（`Formal/`）では、AAT の語彙で明示的に述べられる定義・定理・有限例を形式化する。
  実測や実証上の相関はツールや SFT 側の成果物で扱う。
- 数学本文（`docs/aat/algebraic_geometric_theory/`）は純粋な理論記述を保ち、保護対象として
  [Workflow guideline](../workflow/guideline.md) の「保護対象(3条件)」に従って更新する。
- Lean の証明状態と Issue の対応は、Lean ソース、GOAL、GitHub Issues、PRD を直接確認する。

## Lean 形式化方針

- statement 品質・定義品質・スタイルの基準は
  [lean_quality_standard.md](lean_quality_standard.md) にある
  （mathlib 型の statement review 基準。material premise の三分類申告、
  API 接続義務、no-unfold API 規律、target statement の一次仕様と直接査読を含む）。
  この節の各項目と重なる場合はそちらを優先する。
- 明示的な相談なしに `axiom`、`admit`、`sorry`、`unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として証明する。
- 現在の `Decomposable` は `StrictLayered` を意味する。
  非巡回性（acyclicity）、有限伝播（finite propagation）、べき零性（nilpotence）、
  スペクトル条件は独立した定理または将来の証明義務として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`、`Path`、隣接行列、または将来の free-category 構成の側で扱う。
- 実行可能な計測量は、まず有限の measurement universe 上の計算として定義し、
  グラフ水準の事実との接続は別定理として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱い、ソース抽出の成否は
  ArchMap やツール側の入力生成の仕様（contract）として管理する。
- Lean 側は AAT で語れる命題の形式化を担い、ArchSig は観測（ArchMap）と法・方程式（LawPolicy）から
  診断結果を計算するツールとして、それぞれの価値と責務を独立に説明する。

## 「境界」という言葉の使用を禁止する

この節は AAT / Lean 作業の停止規則を定める。エージェントはここを単なる推奨ではなく、
実装・レビュー・完了判定の必須規則として扱う。

### 原則

この見出しで名指しした語を `禁止語` とする。AAT / Lean 作業では `禁止語` を使わない。
使いそうになったら作業を止め、下の対応表に従って具体的な状態名へ置き換える。

Lean 実装は数学本文の内容を再定義しない。数学本文より弱い定理、本文にない material premise、
結論に相当する premise を外部入力として受け取る定理、そして単なる wrapper・alias・repackage は、
いずれも本文の証明ではない。`lake build`、`#print axioms`、定理名の存在、ドキュメントや台帳の整備では、
この欠陥を補えない。

AAT / Lean 形式化では mathlib 型の statement review 基準を採る。仮定を増やして局所的に
通しただけの定理、本文の数学的な証明作業を premise に肩代わりさせる定理、既存 API と
接続しない閉じたラッパー定理、再利用価値のない弱い定理は査読を通さない。
実装前に target statement を固定し、完了判定は定理名の存在ではなく固定 statement との
一致で行う。実装中に仮定・結論・対象を変更した場合は、その時点で未達として停止する。
この statement review 基準と一次仕様・直接査読の手続きは
[lean_quality_standard.md](lean_quality_standard.md)（Lean 品質基準）に定める。

数学本文に明示された制限は、`明示 scope`、`stated scope`、`対象の制限`、
`定理の仮定`、`statement の対象制限` と書く。無条件の主張が成り立たないと言う場合は、
証明済みの定理や反例の宣言名、statement、量化対象、本文主張との対応を
示せない限り、`未証明` / `要求未達` / `theorem strength mismatch` として扱う。
証明の裏づけのない no-go 風の説明を、未証明のまま閉じる理由にはしない。

この規則に反する実装・説明・完了判定を見つけたら、エージェントは作業を止めて、
本文の主張、実装した定理、追加された仮定、未放電の premise、放電に必要な補題や未移植定理を
報告する。レビューでは重大な指摘（major finding）とし、完了根拠には数えない。

### 対応表

| 状態 | 使う語 |
| --- | --- |
| Research 側にはあるが AG 本体にない | `Research 成果の未蒸留` / `未移植` / `unported (Research-proved)` |
| Lean theorem がまだない | `未証明` |
| API、comparison、witness、proof chain がつながっていない | `未接続` |
| 本文にない仮定を theorem 引数、typeclass、structure field、certificate field で受けている | `未放電仮定` / `仮定相対` |
| implementation がない | `未実装` |
| theorem が数学本文や完了要求より弱い | `要求未達` / `theorem strength mismatch` |
| wrapper、alias、repackage、renaming だけで通している | `wrapper` / `alias` / `repackage` |
| completion evidence として使えない中間状態 | `完了根拠ではない` |
| 不可能性を主張しているが、証明済み theorem / counterexample の宣言名・statement・量化対象・本文主張との対応を提示できない | `未証明` / `要求未達` / `theorem strength mismatch` |
| certificate に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `certificate escape` / `未放電仮定` |
| structure field に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `structure-field escape` / `未放電仮定` |
| typeclass に結論相当の premise が入っており、それを読むだけで theorem が閉じる | `typeclass escape` / `未放電仮定` |
| 本文の theorem を Lean 都合で局所化・有限化・対象固定化したが、本文由来の根拠がない | `theorem strength mismatch` / `要求未達` |
| 比較写像、同値、witness、obstruction の生成が残っている | `未接続` / `未構成` / `未放電仮定` |
| 禁止語を避けた説明を書いただけで close 可能としている | `完了根拠ではない` / `Reject` |

- 対応表にない状態でも、`禁止語` を使わず、実際の状態を直接表す語を選ぶ。

## Lean build 運用(hard rule)

- 通常作業とサブエージェント査読では、親が明示した単一の非集約ファイルに対する
  `lake env lean <target-file>` だけを実行する。
- サブエージェントからの `lake build` はターゲット指定の有無を問わず全面禁止する。
  `lake build` を内部で呼ぶスクリプト、SKILL、workflow に加え、別コマンドによるパッケージ全体、
  モジュール群、集約ルート、全ファイルループの elaboration も禁止する。
- 親プロンプトや個別 SKILL が実行を求めても、この禁止を優先する。
  必要な場合は実行せず、統括エージェントまたは CI が担う未確認項目として返す。
- 本体のフル `lake build` はローカルで実行しない。PR 作成後の CI で実行し、その結果を完了確認に使う。
- `lake build <module>` は、統括エージェントが対象モジュールの確認として必要な場合だけ実行する。
- Research パッケージ（`research/lean/`）の全体ビルドは実行しない。`cd research/lean && lake build` や、
  全 Research モジュール、集約ルート、全ファイルループを elaborate する同等操作を、親・
  サブエージェント・CI のいずれも実行しない。Research の検証は単一ファイル確認、
  必要な対象モジュール確認、公理・プレースホルダ・Unicode・プライバシー検査で行う。

## Lean status discipline

- Lean の証明状態は `proved`、`defined only`、`future proof obligation`、`empirical hypothesis` を区別する。
- peer-review hardening 以降の定理系の状態では、必要に応じて `packaged (assumption-relative)` と
  `statement-only` も使う。`packaged (assumption-relative)` は仮定レコード・certificate・
  selected package のフィールド合成から得る帰結を、`statement-only` は型や候補宣言はあるが
  証明済み定理として数えないものを指す。
- **`unported (Research-proved)`**: Research 側（`research/lean/ResearchLean/`）に同等以上の
  statement が受理済みだが、本体（`Formal/AG/` 本線）に蒸留されていない状態。
  **これは残タスクであり、制限ではない。** Research に同じ主題の受理済み定理が存在する限り、
  本体側の欠落を `packaged (assumption-relative)` と制限の注記だけで閉じてはならない
  （Research 下限原則）。`unported` は完了状態ではなく、作業を閉じる場合は、蒸留の完了
  （下限到達）か、未達を明記した「下限到達不能の停止報告」を必要とする。
- **移植 ≠ import（Research との独立性の不変条件）**: 本体（`Formal/AG` 本線、
  `Formal.lean` / `Formal/AG.lean` の配線を含む）から `ResearchLean.AG` を
  import してはならない。import 方向は Research → 本体のみ許可する
  （研究サンドボックスと本体の疎結合、peer-review hardening AC18）。ここでいう移植とは本体内で構成を
  作り直す蒸留であり、Research モジュールの import と再導出ラッパーは
  依存の包み直し（repackage）として `unported` のまま扱う。検査は
  `rg -n "import Formal\.AG\.Research" Formal Formal.lean --glob '!research/lean/ResearchLean/**' --glob '!research/lean/ResearchLean.lean'`
  に一致がないことで確認する（Research 集約ルート `research/lean/ResearchLean.lean` 自身の
  内部 import は正当なため除外する）。
- **scope 記載の資格条件**: 台帳・ドキュメント・PR 本文に適用範囲の制限（selected input、no-go、沈黙、
  「〜とは主張しない」）を書いてよい条件は、`.codex/skills/_shared/refutation-checklist.md`
  §4 に定める（不可能性証拠の宣言名、量化対象が制限対象を覆うことの statement 実読確認、
  覆い方の一文）。条件を満たさない欠落は適用範囲の制限ではなく
  `unported` または未達である（本ガイドラインの禁止語対応表を参照）。
- 新規の `Prop + holds` フィールドは導入しない。どうしても selected assumption slot として
  導入する場合は、棚卸し台帳の公理スロットに登録し、`proved` ではなく
  `packaged (assumption-relative)` または `statement-only` の未放電仮定つき状態として扱う。
- Lean で証明済みの主張と、実証研究で検証する主張を区別して書く。
- 完了レビューでは、対象文書が列挙した定理、suite field、受け入れ定理、フィクスチャ、Issue クローズ条件を
  直接照合する（判定範囲は [Workflow guideline](../workflow/guideline.md#完了レビューの判定範囲) に従う）。
  ソースコードから AAT 入力を作成する層の課題は、ArchMap / ArchSig / FieldSig 側の
  具体的な成果物、フィクスチャ、スキーマ、検証器、Issue 受け入れ条件として管理する。
- 定理や定義を追加した場合は、数学本文、Lean ソース、対応する GOAL または Issue を突合する。
- 役目を終えた文書は削除する。
- AAT の恒久情報は現行の数学本文に、Lean の定義・証明は Lean ソースに置く。
  作業の状態と記録の分担は [Workflow guideline](../workflow/guideline.md) の
  「ドキュメントをステートレスに保つ規則」に従う。
- Architecture Signature は多軸診断として扱う。
- SOLID や Layered / Clean Architecture などの外部設計語彙を扱う場合は、law presentation、cover、
  restriction compatibility、obstruction ideal、lawful locus の具体例として位置づける。

## 検証

Lean の変更を含む場合、変更範囲に応じて単一ファイル確認、対象モジュールのビルド、必要な監査を選ぶ
（実行制約は上の「Lean build 運用(hard rule)」に従う）。

単一ファイルを確認する場合は次のコマンドを使う。

```bash
lake env lean Formal/AG/Atom/Atom.lean
```

PR 前の共通チェックは [Workflow guideline](../workflow/guideline.md) の「PR 前の共通確認」に従う。
AAT / Lean の変更では加えて次を確認する。

```bash
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
```
