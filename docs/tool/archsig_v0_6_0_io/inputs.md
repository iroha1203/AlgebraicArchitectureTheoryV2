# ArchMap、語彙、原始値

ArchMap は、先に選んだ Law の語彙で観測した原始 Atom と由来を持つ。
Law は [宣言言語](law.md) のテキスト、ArchMap と結果は JSON である。
原始入力は対象の値・参照・式・候補対応までとし、計算済みの cover、行列、判定、保存証拠を
受け取る型を設けない。核は言語固有の source parser を持たない。

## 1. ファイルと版

JSON は UTF-8、BOM なし。重複 key、未知 field、不正 UTF-8、非有限 number、
unpaired surrogate を拒否する。`null` は使わない。省略可能 field を本仕様の表記では `?` と書く。
空配列は宣言型で読み、欠測と区別する。object key 順は意味を持たない。
文字列を正規化したり case folding したりしない。

format は ArchMap=`archsig.archmap/1`、Law=`archsig.law/1`、結果=`archsig.result/1`。
型・評価・核の構成規則の意味の版は `archsig/0.6.0`。両入力の semantics を一致させる。
未知版は `unsupported_version`、対応版の未知 field や宣言は不正入力。
同じ semantics の意味を実装版によって変更しない。変更には別の semantics を用いる。

Id は `[A-Za-z][A-Za-z0-9_.-]*`。QName は Law の完全名であり `.` 区切り。
Digest は `sha256:` と小文字16進64桁。Nat は metadata 用の JSON number で
0..9007199254740991 の整数。数学的な整数の表現とは異なる。

## 2. ArchMap の schema

```text
ArchMap = {
  format: "archsig.archmap/1", semantics: "archsig/0.6.0",
  vocabularies: VocabularyBinding[], sources: Source[], origins: Origin[],
  snapshots: Snapshot[]
}
VocabularyBinding = {reading: Name, digest: Digest}
Source = {id: Id, uri: String, revision: String, digest: Digest}
Origin = {id: Id, mode: "observed"|"proposed"|"specification",
          method: String, locations: Location[], note?: String}
Location = {source: Id, path: String, span?: [Nat,Nat]}
Snapshot = {id: Id, origin: Id, subjects: Subject[], atoms: Atom[]}
Subject = {id: Id, type: QName, origin: Id}
Atom = {id: Id, subject: Id, field: QName, value: Value, origin: Id}
```

各表は ID を key とする有限集合。vocabularies は reading を key とし、重複を拒否する。
subject/atom ID は snapshot 内で一意。Subject.type は entity/arrow/correspondence の宣言。
Subject は、その型の個体の存在という原始事実である。ID を Law の値として公開せず、
文字列分解・件数の水増し・未登録 subject の補完を行わない。

Atom.field はその subject の型に宣言した field の完全名。
同じ subject/field の二重記録は同値でも `duplicate_fact`。
五成分 `(kind, axis, element, attribute, value)` は、kind=宣言種別
`entity|arrow|correspondence`、axis=subject の型完全名、element=subject 参照、
attribute=field 完全名、value=型付き原始値として生成する。
subject の存在にも origin を持つ構成要素を生成し、明示した field Atom と区別する。
kind/axis を ArchMap に重ねて指定しない。

多項関係は Tuple、複数の参照は Set/List、名前付き操作は arrow の別 subject で表す。
同じ端点でも名前を消さず、List の順序・重複を保持する。有限の操作列・式の反復出現を
Set に変換しない。量は構造関係に先取りして同一視せず、保存を Law で検査する。

snapshot とその subjects/atoms の origin.mode は一致させる。
同じ型・同じ ID でも別 snapshot の subject は別物。参照は必ず snapshot を含む。
候補設計や候補対応は proposed、合成した仕様例は specification とする。
これらの成立を observed の実装についての成立へ付け替えない。

## 3. 型と値

型の wire 表現を Type と呼ぶ。

```text
Type = "Unit" | "Bool" | "Z" | "Q" | "Text"
     | ["Fp", DecimalPrime] | ["Ref", QName] | ["Data", QName]
     | ["Tuple", Type, Type, ...] | ["List", Type] | ["Set", Type]
     | ["Option", Type] | ["Map", Type, Type] | ["Term", [Type,...], Type]
```

語彙 manifest の依存参照だけは `["Owned", QName, parameterName]` を用いる。
実際の値の型は、その parameter の参照を束縛した Ref と所属条件を持つ。
DecimalPrime は正の10進整数文字列で、核が素数性を確認する。
原始 Value は次の一つの encoding に従う。

| 型 | JSON の Value | 意味・検査 |
| --- | --- | --- |
| Unit | `[]` | 唯一の値 |
| Bool | `true` / `false` | 真偽の原始値 |
| Z | `"-12"` | `0|-?[1-9][0-9]*`。`-0` を拒否 |
| Q | `["-2","3"]` | 分母正、互いに素。零は `["0","1"]` |
| Fp(p) | `"4"` | 0 ≤ 値 < p |
| Text | `"..."` | 原始文字列。等値以外の言語固有解析をしない |
| Ref(E) | `["snapshot","subject"]` | 参照先の存在・宣言型・依存 owner を検査 |
| Tuple | `[v1,v2,...]` | 成分数と型を一致させる |
| List / Set | `[v1,v2,...]` | List は順序・重複を保持。Set は重複拒否、順序は意味なし |
| Option | `{"none":true}` / `{"some":v}` | 観測した不在 / 存在 |
| data D | `{"tag":"Ctor","args":[v,...]}` | tag は D 内の短い constructor 名。引数型と順序を検査 |
| Map<E,F> | `[[key,value],...]` | 両値は参照。key は一意で source の登録族を全て覆う。値は target 族に属する |
| Term | `{"params":["x",...],"body":"x + 1"}` | field の Term 型と同じ parameter 個数・順序。body は Law の式 fragment |

例: `Map<State[from],State[to]>` の値は
`[[["v","p"],["v","r"]],[["v","q"],["v","s"]]]`。
型は field 宣言から決まり、pair ごとの型 wrapper は置かない。
空の Map もその定義域が空なら全域であり、domain/codomain の型を捨てない。
全域性は型検査、端点・構造・Law の保存は候補に対する核の検査である。
Set の要素型は Law の型規則に従い、Term を直接・間接に含まない。
重複は型に沿う構造的等値で検査する。List 内の項の外延等値を入力検査へ移さない。

Term body は閉じた純粋式で、自由変数は params のみ。field、観測族、Path、with、
結果参照を含めない。呼出しは原始値の演算・data constructor のみで、reading の view を
名前で参照しない。型の分かる有限なコード上の作用を観測するために用い、外部 code を実行しない。
型・原始式を記録することと、その関数の外延等値が決定可能なことを区別する。

## 4. 語彙 binding

`archsig check --law L --out DIR` が出力する vocabulary manifest を観測側が使用する。
ArchMap に現れる subject 型と、field 型から推移的に参照する宣言を持つ reading ごとに
binding を必須とする。過剰な binding もその reading の manifest と照合する。
一致しなければ `vocabulary_mismatch`。型が偶然似ていることでは読み替えない。

manifest は次の JSON。全ての欄を必須とする。reading の全原始宣言を含める。

```text
Vocabulary = {semantics:"archsig/0.6.0", reading:Name, declarations:Declaration[]}
Declaration = {kind:"entity"|"arrow"|"correspondence", name:QName,
               parameters:Field[], fields:Field[], alignments:Alignment[]}
            | {kind:"data", name:QName, constructors:Constructor[]}
Field = {name:Name, type:Type}
Alignment = {source:QName, target:QName}
Constructor = {name:Name, arguments:Type[]}
```

entity の括弧内は parameters、body は fields。全名を展開し、依存型の parameterName は
その宣言の括弧内の名を使う。暗黙の同名 align は manifest に追加せず、明記分だけを保持する。
declarations は完全名、alignments は source,target の順で整列する。
parameters、fields、constructors、constructor arguments の順は元の宣言順。
use、view、law、local、change、relation は manifest に入れない。
原始 Term が view を参照しないため、Law の条件や読取りの変更は原始語彙 binding を変えない。

この manifest の canonical JSON の SHA-256 が binding の digest である。
canonical JSON は key を Unicode scalar 順、空白なし、非 ASCII を UTF-8 で出力する。
引用符・backslash を escape し、U+0000..001F は小文字4桁の `\u00xx`、その他は escape しない。
`/` は escape しない。metadata number は先頭零のない10進整数。文字列の正規化はしない。
全入力の bytes digest、モデル digest、再利用は [実行仕様](execution.md)に従う。

## 5. 未観測、不在、矛盾

subject が存在して field の Atom がない場合、その slot は未知。
identity は `(snapshot,subject,field)`、型は field 宣言。owner・Map も省略すれば未知であり、
構造の構成や関係の列挙がそれに依存する場合は、その理由を保持する。
空の Set/List、Option none、零は既知の値。未記録をそれらに置換しない。

補完は既知値・登録 subject・型・参照・由来を固定し、欠測 field だけを型の値で埋める。
Law の成立を補完の条件に使わない。既知の Map の全域性・owner 条件などを満たす補完が
一つもない入力は `inconsistent_observation`。既知の不正型・dangling ref はそれぞれ
`type` / `reference`。補完の存在検査を完了できなければ検査を中断し、計算成功へ進まない。
ref と Map の制約は有限 subject 族、その他の原始型は有限 ground value を持つため、
原始提示の整合性は有限の構造検査で決定する。

Law が破れることは有効な入力への反証である。
型が正しい対応表でも端点保存は失敗し得る。これは原始値を捨てる入力エラーにしない。
未知の評価と確定の規則は [Law §6](law.md#6-未観測の意味)に従う。

## 6. 由来

Source は観測に使った source tree/content の識別。uri/revision は非空文字列で、
digest は観測側が指定する内容 digest。核はネットワークから uri を解決しない。
Location.path は source root 相対の `/` 区切りで、空・絶対 path・`.` / `..` segment を拒否する。
span は UTF-8 byte の半開区間 `[start,end)`、start≤end。省略時はファイル全体。
観測者（agent / SKILL）は、Law の語彙と読み、選択した抽出規則に従い、計算に必要な
実装コードの原始事実を由来付きで記録する。必要情報の確保、実 source の存在・範囲、
観測の正しさ、source と ArchMap の忠実な対応は観測者の責務である。
核は入力モデルの型・参照・整合性と、生成する構造の数学的適用条件を検査する。
この入力検査は source を抽出し直す処理や、実コードについての網羅性の認定を含まない。

Atlas に基づいて観測の十分性を述べる場合、観測者は対象 source の族、選択 Law の
評価族と読みを固定する。同じ観測結果を持つ source で各評価が一致することが、
その族に対する Law 評価の十分性である。対応する数学的条件とコードの読みとの対応も
観測者が確保する。核の `quotient` は提示された候補域・view・Law 評価族について
十分性を検査し、この結論の域を未提示の source へ広げない。
被覆・係数・複体・対象類を含む診断保存は、実比較とその条件について別に検査する。

observed の locations は1件以上で、実装コードの使用箇所を指す。
テストコードや runtime trace は観測の対象に含めない。核がファイル名から適格性を認定することはない。
proposed/specification の locations は空でもよいが、そのとき note は非空必須。
method は作り方を説明する非空文字列。由来の prose を計算の数値へ戻さない。

原始値・参照を固定して provenance だけを変えた場合、数学的結果は変わらず、artifact digest と
出力の由来は変わる。古い source revision を現在の実装についての結論へ付け替えない。
