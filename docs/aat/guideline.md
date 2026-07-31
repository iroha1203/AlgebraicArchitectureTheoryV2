# AAT / Lean 編集ガイドライン

この文書は `Formal/AG` と `docs/aat` を編集するときの作業方針をまとめる。

## Claim discipline

- 語らないことは語らない。語るべきことは強く精密に語る。
- AAT / Lean の定理・定義・レビュー説明では、選択された atom vocabulary、law、cover、
  coefficient、仮定、証明済み theorem package の範囲を肯定形で述べる。
- 禁止: 「実コードベースは対象としない」「この定理はコード全体の品質を判定しない」のように、
  AAT の外側を定型 caveat として主張に付け足すこと。外側は失敗・残タスク・補足説明ではなく沈黙で扱う。
- OK: 「選択された atom vocabulary と finite cover の範囲で XXX を証明する」
  「Lean で証明済みの sheaf condition と明示された comparison map に相対化して YYY が成り立つ」のように、
  claim scope を正面から限定して述べること。
- anti-weakening / overclaim 防止のための negative list は、通常の説明文に再掲しない。
  実際に境界を越えた claim を止めるときだけ、監査理由として最小限に使う。

## 位置づけ

- 現行 AAT は代数幾何的アーキテクチャ論である。Atom は primitive architectural fact
  として公理化され、Atom family / configuration から architecture object が生成される。
  その上で固定された law universe、coverage topology、係数環 / 係数 sheaf から
  architecture geometry を構成し、AAT site、sheaf、ringed AAT topos、law algebra、
  obstruction ideal sheaf、lawful locus、architecture scheme、Čech descent、
  derived / stacky geometry として読む。
- AAT は代数幾何の比喩ではない。Atom を土台に、site、Grothendieck topology、sheaf、
  ringed topos、scheme、Čech cohomology、derived / stacky structure などの本物の
  代数幾何概念へ接続していく理論として扱う。
- Lean 形式化でも、AAT 専用の仮置き wrapper や名前だけの analogue で満足しない。
  有限・小さい対象から始めても、定義、comparison map、同値、boundary theorem を通じて、
  可能な限り既存の数学的構造と接続する方向へ育てる。
- Atom / law / obstruction / flatness / signature は代数幾何版の基礎データや局所
  presentation である。外部設計パターン語彙へ潰して説明しない。
- 実コードベース抽出器、ArchMap observation、tooling validation は、AAT 入力を提示・検査する
  前段または後段 surface であり、AAT の theorem package の完了条件ではない。
- AAT 自体に observation / measurement / tooling boundary はない。境界を持つのは、ArchMap、
  LawPolicy / MeasurementProfile による選択、ArchSig / FieldSig の測定 artifact、または
  empirical dataset である。
- Lean source は代数幾何版 AAT の定義・定理・finite examples を形式化する場所である。
  実測や empirical correlation は、AAT ではなく tooling / SFT 側の artifact に相対化して扱う。
- Lean 形式化は全知の検査器ではない。形式化対象は、AAT の語彙で明示的に述べられる命題に限る。
  全 runtime、全 semantic universe、source extraction completeness、tooling validation completeness を
  AAT theorem package のスコープに入れない。
- `docs/aat/algebraic_geometric_theory/` は現行 AAT 数学本文の正典である。Lean status、Issue 番号、実装済み API の進捗管理は本文に混ぜない。
- `docs/aat/algebraic_geometric_theory/` は AAT の根幹文書である。更新は、人間の明示的な編集指示、
  実装者以外の LLM によるレビュー、人間による差分確認と merge の3条件がすべて揃う場合に限る
  (正本は [workflow guideline](../workflow/guideline.md) の「保護ファイル」)。
- Lean status とIssueとの対応は、Lean source、GOAL、GitHub Issues、PRDを直接確認する。

## Lean 形式化方針

- statement 品質・定義品質・スタイルの正本は
  [lean_quality_standard.md](lean_quality_standard.md)
  (mathlib 型 statement review 基準。material premise 三分類申告、
  API 接続義務、no-unfold API 規律、target statement の一次仕様と直接査読を含む)。
  この節の各項目と重なる場合は正本側を参照する。
- 明示的な相談なしに `axiom`, `admit`, `sorry`, `unsafe` を導入しない。
- 定義は小さく保ち、同値性や対応関係は定理として育てる。
- 現在の `Decomposable` は `StrictLayered` を意味する。
- acyclicity、finite propagation、nilpotence、spectral conditions は `Decomposable` の定義に混ぜない。別個の定理または将来の proof obligation として扱う。
- `ComponentCategory` は thin category であり、path count や walk length を意図的に忘れる。
- 定量指標は `Walk`, `Path`, adjacency matrix、または将来の free-category construction 側で扱う。
- executable metrics は、まず有限な measurement universe 上の計算として定義し、graph-level facts との接続は別 theorem として証明する。
- `ComponentUniverse` は proof-carrying measurement universe として扱う。source extraction の成否は
  AAT の定理ではなく、ArchMap / tooling 側の入力生成 contract として扱う。
- ArchSig や Rust tooling の有用性を Lean との対応で正当化しない。Lean 側は AAT の語れる命題を支える
  形式化であり、ArchSig は別に観測(ArchMap)と法・方程式(LawPolicy)から診断結論を出す tool である。

## 「境界」という言葉の使用を禁止する

この節は AAT / Lean 作業の停止規則の正本である。エージェントはここを「推奨」ではなく
実装・レビュー・完了判定の hard rule として扱う。

### 原則

この見出しで名指しした語を `禁止語` とする。AAT / Lean 作業では `禁止語` を使用しない。
使いそうになった場合は停止し、下の対応表に従って具体的な状態名へ置き換える。

Lean 実装は数学本文を再定義しない。数学本文より弱い theorem、本文にない material premise、
結論相当の premise を外部入力として受け取る theorem、wrapper / alias / repackage は、
いずれも本文の証明ではない。`lake build`、`#print axioms`、theorem 名の存在、docs / ledger の整備は、
この欠陥を補わない。

AAT / Lean 形式化は mathlib 型の statement review 基準を採用する。仮定を増やして局所的に
通るだけの theorem、本文の数学的仕事を premise に肩代わりさせる theorem、既存 API と
接続しない閉じた wrapper theorem、再利用価値のない弱い theorem は査読を通さない。
実装前に target statement を固定し、完了判定は theorem 名の存在ではなく固定 statement との
一致で行う。実装中に仮定・結論・対象を変更した場合は、その時点で未達として停止する。
この statement review 基準と一次仕様・直接査読の手続きの正本は
[lean_quality_standard.md](lean_quality_standard.md)(Lean 品質基準)である。

数学本文側に明示された制限は、`明示 scope`、`stated scope`、`対象の制限`、
`定理の仮定`、`statement の対象制限` と書く。無条件主張の不可能性を言う場合は、
証明済み theorem / counterexample の宣言名、statement、量化対象、本文主張との対応を
示せない限り、`未証明` / `要求未達` / `theorem strength mismatch` として扱う。
no-go 風の説明は免罪符にしない。

この規則に反する実装・説明・完了判定を見つけたら、エージェントは作業を止めて
本文主張、実装 theorem、追加された仮定、未放電 premise、放電に必要な補題または未移植 theorem を
報告する。レビューでは major finding とし、完了根拠として数えない。

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

- 対応表にない状態でも、`禁止語` を使わず、状態を直接表す語を選ぶ。

## Lean build 運用(hard rule)

- 通常作業とサブエージェント査読では、親が明示した単一の非aggregate fileに対する
  `lake env lean <target-file>` だけを実行する。
- サブエージェントからの `lake build` はtarget指定の有無を問わず全面禁止する。
  `lake build` を内部で呼ぶscript、skill、workflowに加え、別commandによるpackage全体、
  module群、aggregate root、全file loopのelaborationも禁止する。
- 親プロンプトや個別SKILLが実行を求めてもこの禁止を優先する。
  必要な場合は実行せず、統括エージェントまたはCIが担う未確認項目として返す。
- 本体のフル `lake build` はローカルで実行しない。PR 作成後の CI で実行し、その結果を完了確認に使う。
- `lake build <module>` は、統括エージェントが対象 module の確認として必要な場合だけ実行する。
- Research package(`research/lean/`)の full build は CI で実行しない。必要な場合だけ
  統括エージェントが `cd research/lean && lake build` をローカルで1回実行し、
  サブエージェントは実行しない。

## Lean status discipline

- Lean status は `proved`, `defined only`, `future proof obligation`, `empirical hypothesis` を区別する。
- peer-review hardening 以降の theorem 系 status では、必要に応じて `packaged (assumption-relative)` と
  `statement-only` も使う。`packaged (assumption-relative)` は仮定 record / certificate /
  selected package の field 合成から得る帰結、`statement-only` は型・candidate surface はあるが
  証明済み theorem として数えないものを指す。
- **`unported (Research-proved)`**: Research 側(`research/lean/ResearchLean/`)に同等以上の
  statement が受理済みだが、本体(`Formal/AG/` 本線)に蒸留されていない状態。
  **残タスクであり、境界ではない。** Research に同主題の受理 theorem が存在する限り、
  本体側の欠落を `packaged (assumption-relative)` +境界注記で close してはならない
  (Research 下限原則)。`unported` は完了 status ではなく、close は蒸留完了
  (下限到達)または「下限到達不能の停止報告」のみで行う。
- **移植 ≠ import(Research 境界の不変条件)**: 本体(`Formal/AG` 本線、
  `Formal.lean` / `Formal/AG.lean` の配線を含む)から `ResearchLean.AG` を
  import してはならない。import 方向は Research → 本体のみ可
  (研究 sandbox と正本の疎結合、peer-review hardening AC18)。「移植」とは本体内で構成を
  再構成する蒸留であり、Research module の import +再導出ラッパーは
  依存 repackage として `unported` のまま扱う。検査:
  `rg -n "import Formal\.AG\.Research" Formal Formal.lean --glob '!research/lean/ResearchLean/**' --glob '!research/lean/ResearchLean.lean'`
  が no match であること(Research 集約ルート `research/lean/ResearchLean.lean` 自身の
  内部 import は正当なので除外する)。
- **scope 記載の資格条件**: 台帳・docs・PR 本文に scope 制限(selected input、no-go、沈黙、
  「〜とは主張しない」)を書いてよい条件は、`.codex/skills/_shared/refutation-checklist.md`
  §4 を正本とする(不可能性証拠の宣言名名指し+量化対象が scope 制限の対象を覆うことの
  statement 実読確認+覆い方の一文)。資格を満たさない欠落は scope 制限ではなく
  `unported` または未達である(本 guideline の禁止語対応表)。
- 新規の `Prop + holds` フィールドは導入しない。どうしても selected assumption slot として
  導入する場合は、棚卸し台帳の公理スロットに登録し、`proved` ではなく
  `packaged (assumption-relative)` または `statement-only` の未放電仮定つき status として扱う。
- Lean で証明済みの主張と、実証研究で検証する主張を混同しない。
- 完了レビューでは、対象文書が列挙した theorem、suite field、acceptance theorem、fixture、Issue closure を
  直接照合する。対象文書が要求していない無制限 claim を「未完了部分」として追加しない。
- 禁止: AAT の完了レビューで source-observation layer の性質を `non-conclusion`、残タスク、
  未完了 claim、証明不能な限界として列挙しない。source code から AAT 入力を提示する過程は
  AAT theorem package の外側にある。必要なら ArchMap / ArchSig / FieldSig の
  具体的な artifact、fixture、schema、validator、Issue acceptance として別管理する。
- non-conclusion / claim boundary は、具体的な theorem や artifact の近くで必要な分だけ記録する。
  レビュー報告や残タスク欄を、一般的に証明不能な巨大 claim の一覧にしない。
- 語れることだけを確かに語る。AAT / Lean docs では、語れない外部領域を `non-conclusion` 一覧として
  主役化しない。必要な boundary は、定理や artifact の有効範囲を示すために最小限だけ置く。
- theorem や定義を追加した場合は、数学本文、Lean source、対応するGOALまたはIssueを突合する。
- 役目を終えた文書は削除する。
- AATの恒久情報は現行数学本文に置き、Lean・作業状態はLean source、GOAL、Issue、PRDで管理する。
- Architecture Signature は単一スコアではなく、多軸診断として扱う。
- SOLID や Layered / Clean Architecture などの外部設計語彙は AAT の primitive ではない。
  必要な場合だけ、law presentation、cover、restriction compatibility、obstruction ideal、
  lawful locus の具体例として読む。

## 検証

Lean 変更を含む場合、変更範囲に応じて focused check、対象moduleの targeted build、必要な監査を選ぶ
(実行制約は上の「Lean build 運用(hard rule)」)。

単一ファイルを確認する場合は次の形を使う。

```bash
lake env lean Formal/AG/Atom/Atom.lean
```

PR 前には次も確認する。

```bash
git diff --check
rg -nP "[\x{200B}-\x{200F}\x{202A}-\x{202E}\x{2066}-\x{2069}]" <changed-files>
rg -n "\b(axiom|admit|sorry|unsafe)\b" Formal docs
```
