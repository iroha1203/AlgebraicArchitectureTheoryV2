# Atom 定義

Atom 定義は、観測対象・属性・関係の語彙、型、その意味を持つ独立した定義元である。
Law は意味上の設計の出発点として、何を区別して要求するかを決める。
その区別を共通語彙として定義し、Law と ArchMap は同じ定義を参照する。
複数の Law は一つの定義を共有でき、定義の作成・版管理は Law からの生成を前提としない。

## 1. ファイルと識別

Atom 定義は UTF-8 JSON。JSON の検査、Id、Digest、canonical JSON は
[入力仕様](inputs.md)に従う。次の欄をすべて必須とする。

```text
AtomDefinition = {format:"archsig.atom-definition/1", semantics:"archsig/0.6.0",
                  vocabularies:Vocabulary[]}
Vocabulary = {semantics:"archsig/0.6.0", namespace:Name, version:String,
              dependencies:VocabularyBinding[], declarations:Declaration[]}
VocabularyBinding = {namespace:Name, version:String, digest:Digest}
Declaration = {kind:"entity"|"arrow"|"correspondence", name:QName, meaning:String,
               parameters:Field[], fields:Field[], alignments:Alignment[]}
            | {kind:"data", name:QName, meaning:String, constructors:Constructor[]}
Field = {name:Name, type:Type, meaning:String}
Alignment = {source:QName, target:QName, meaning:String}
Constructor = {name:Name, arguments:Type[], meaning:String}
```

Name と QName の字句は [Law](law.md#1-ファイル名前再利用)に従う。
namespace は一つの Name。宣言名は `Namespace.Declaration`、field は
`Namespace.Declaration.field`、constructor は `Namespace.Data.Constructor`。
JSON の Field/Constructor.name は短名、Declaration.name と Alignment の両端は完全名である。
namespace の直下では宣言名を、同じ宣言では parameters と fields の名を、data 内では
constructor 名を一意にする。予約語と固定演算の名前に関する制限も Law に従う。
version と meaning は非空文字列。version は作者が付ける識別値であり、完全一致で比較する。
版の大小比較、範囲指定、最新版選択は行わない。
meaning は定義された対象・位置・値の読みを記す。診断結果や観測済み値を置かない。
constructor の meaning は arguments の順序と各位置の意味も記す。
核は meaning の存在と文字列型を検査して出力に保持する。文章を条件式へ翻訳しない。
数値・関係の適用条件は型と Law の式で計算する。

一ファイルは一つ以上の Vocabulary を包装する。同じ実行に同じ namespace を二度指定すると、
版・digest・内容が等しくても duplicate_id。同じ namespace の複数版を同時に使わない。
ファイル名・配置と namespace の対応は要求しない。
型の QName は原始宣言を指し、Law の view 等を参照しない。
原始宣言の中に Path や結果専用型を置かない。Type は [原始型](inputs.md#3-型と値)に従い、
依存参照には `["Owned",QName,parameterName]` を使う。

## 2. 原始宣言の意味と型

entity / arrow / correspondence の parameters と fields は原始属性の定義であり、両者の名は一意。
parameters は後続 field の依存型から参照できる。fields の型から別の fields を参照しない。
単なる表示位置ではなく、この依存順を語彙に保持する。

- `entity` の `owner` は省略可能な唯一の所属 field。型は owner を持たない entity とする。
  owner なし entity の各 instance が対象の根となる。所有の多段化は導入しない。
  所属以外の共有・依存は通常の参照 field で書く。
- `arrow` は `owner: R, from: E[owner], to: E[owner]` を必須とする。
  R は根 entity、E は R に属する entity。追加 field を許す。
  from→to がこの名前付き内部遷移の作用である。追加の値・式は Law で読める。
- `correspondence` は `from: R, to: S` を必須とし、R/S は根 entity。
  fields の型は `Map<E[from], F[to]>`。対応する各 owned entity/arrow の組を一度ずつ宣言する。
  source/target 側の構成対象に含まれる各 owned 型を覆うことを要求する。
  同じ型間では同名 field の位置を対応させる。異なる型間では alignments で source と target の
  field の対応をすべて明記する。所属・参照は対応表に沿って、量は位置だけを対応させる。
  align は field の意味の対応であり、値が一致するという判定を入力しない。
  同じ型の間で明記した align は、その field の同名の対応に代わる。
  参照を含む field の型は、R を S へ、対応表の始域の型を終域の型へ、依存型の添字を対応先の
  field 名へ移したときに一致させる。量の field は位置だけを対応させ、型の一致を求めない。

data の有限木、正の自己再帰、ground value、Set/Map/Term の型適格性は
[型の規則](law.md#3-型と有限の観測族)に従う。
原始構造の型検査と同名 field の既定対応は核が行う。量の保存や関係の成立は Law が宣言する。

## 3. 依存、参照、digest

各 Vocabulary の外部 namespace への型・Alignment 参照に必要な binding を dependencies に列挙する。
共通ライブラリとして準備した未使用の dependency も列挙でき、使い切ることは要求しない。
各 dependency は版付き参照宣言なので、使用の有無によらず登録先と版・digest を照合する。
自己 namespace は列挙しない。
namespace 登録後、依存グラフの循環を digest 照合より先に検査する。
依存の有向グラフは非循環である。自己再帰 data は同じ namespace 内の型規則で扱い、
namespace の自己 dependency とは区別する。Atom 定義は Law に依存しない。

CLI の各 `--atom-definition` で明示されたファイルを開始時に読み、全 Vocabulary を登録する。
依存参照はその登録表だけから、namespace・version・digest の完全一致で解決する。
ファイル内外で同じ規則を用い、依存先の追加読込み・path探索・downloadをしない。
Law の各 reading は、直接使う原始 namespace を次で明示する。

```text
use vocabulary Counter version "1" digest "sha256:...";
```

`sha256:...` は説明用の省略。実ファイルは64桁の digest を持つ。
Law が直接参照する namespace はすべて明示し、型からたどる依存は上の定義の依存表で解決する。
ArchMap の binding は [入力仕様 §4](inputs.md#4-語彙-binding)に従う。

Vocabulary を正規化した manifest の canonical JSON の SHA-256 を語彙 digest とする。
正規化では declarations は完全名順、dependencies は namespace 順、alignments は
(source,target)順。parameters、fields、constructors、arguments の順は保持する。
declarations は空でもよい。二重の dependency、constructor、field、alignment は duplicate_id。
自己 dependency は cycle。未使用の dependency も manifest に保持し、digest に含める。
use/view/law/local/change/relation を manifest に入れない。
meaning、version、全原始宣言と dependency binding は digest に含める。
意味の説明だけの変更も参照する版・digest の更新を必要とする。内容変更には新しい version を付け、
同じ版の内容を置換しない。未使用情報の追加も定義・manifest の変更であり版・digest を更新する。
条件や読取りだけを変えた Law は定義の digest を変えない。
依存先の更新は参照元の dependency binding と版の更新を伴う。

AtomDefinition 全体の model_digest は、各 Vocabulary を上記の順序で正規化し、
vocabularies を namespace 順にした文書全体の canonical JSON の SHA-256。
包装やファイル分割を変えるとファイルの digest は変わり得るが、各語彙の digest は変わらない。
全入力の semantics は同一とする。

## 4. 検査と責務

検査は次の段階で行い、check/run が同じ手順を使う。利用者によるモード選択は増やさない。
段階1・2は定義→Law→ArchMap の入力種別順に適用する。定義と Law の検査が完了した後の
ArchMap の不正では、確認済みの manifest と宣言一覧を保持する。

1. 提示した全ファイルの構文・版・schema・名前の一意性を検査する。未知欄は syntax。
2. 定義と Law の宣言の型・明示参照を解決し、ArchMap の binding・事実・補完の整合性を検査する。
   未使用の定義、語彙、import、dependency、Law 宣言も受理し、使われないことをエラーにしない。
   宣言内の参照や dependency binding 自体は明示された参照なので、欠落・型・版・digest の不正は検出する。
3. run の問いで選んだ reading・対象・束縛から、必要な構造と計算を生成して成立条件を検査する。
   未使用の語彙について事実を観測したり、未使用の field に値を埋めたり、全宣言を評価したりする義務は課さない。

宣言された field の Atom が欠ける場合は、subject があれば未観測 slot、subject 自体がなければ
当該個体の追加生成をしない。値を必要とする問いへ未観測の理由を伝播する。
型検査に通る Law の不成立や、選んだ構成の保存失敗は段階3の判定であり、不正入力とは区別する。
未使用情報を黙って捨てず、入力コピー・manifest・解決済み宣言に保持する。
参照先 namespace が未登録なら reference、登録済みだが版・digest が異なるなら
vocabulary_mismatch、循環は cycle、重複は duplicate_id。型不一致は type、
不正な欄・型表記・空 meaning/version は syntax、未知 format/semantics は unsupported_version。
位置は誤った宣言・binding の入力位置へ戻す。状態・終了コードは [実行仕様](execution.md#6-状態終了コード予算)に従う。

観測者は、定義の意味と選択した Law の読みを理解し、コードを正しく観測して ArchMap を作る。
同じ定義を使うことは語彙と型の適合を固定する。観測対象の選択、抽出方法、欠測、誤記によって
観測結果は異なり得る。共通語彙だけで観測結果の一致や source への忠実性は保証されない。
ArchSig は受け取った定義・宣言・事実の型と参照を検査し、DSL から計算構造・equation realization・
写像を構成する。その正確性と数学の適用条件の確認は ArchSig の設計・実装・検証責務である。
作者が計算パイプラインを記述する入力や、追加の AAT 定理を処理系の検証の代替にする条件は設けない。
