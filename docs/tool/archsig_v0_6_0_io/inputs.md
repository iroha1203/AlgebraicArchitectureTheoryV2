# 二入力、原始値、参照

## 1. 共通のファイル規則

入力・出力は UTF-8 の JSON。BOM、重複 object key、不正 UTF-8、非有限数、
unpaired surrogate を拒否する。未知の欄を拒否する。欄の省略を許す箇所は本仕様で
`?` と記す。`?` は文法の記号であってファイルの key の一部ではない。
`null` は省略・欠測・零のいずれにも使わない。空 array/object は明示した型で解釈する。

ID は `[A-Za-z][A-Za-z0-9_.-]*`、長さは1以上。ID の比較は case-sensitive。
完全修飾名は `module/name`。module ID と module 内の宣言名はそれぞれ一意。
自然文だけに任意の Unicode を許し、文字列の正規化・case folding を行わない。
JSON の object key 順は意味を持たず、array 順は特記がない限り意味を持つ。
同じ値の Set 要素や同じ ID の重複定義を拒否し、先勝ち・後勝ちを行わない。

版は format と semantics を分ける。
`archsig.archmap/1`、`archsig.law/1`、`archsig.result/1` が wire format、
`archsig/0.6.0` が型・組込み演算・判断規則の意味である。
両入力は同一 semantics を指定する。未知版は `unsupported_version`。
同じ semantics の下で演算の意味を変えない。新しい意味を追加する版は別の semantics とする。

## 2. ArchMap の全体

以下は欄と型の表記であり、`T[]` は T の有限 array、`Id` は上記 ID、`Digest` は
`sha256:` に続く小文字16進64桁である。

```text
ArchMap = {
  format: "archsig.archmap/1", semantics: "archsig/0.6.0",
  vocabularies: VocabularyBinding[], sources: Source[], origins: Origin[],
  snapshots: Snapshot[]
}
VocabularyBinding = {module: Id, digest: Digest}
Source = {id: Id, uri: String, revision: String, digest: Digest}
Origin = {id: Id, mode: "observed"|"proposed"|"specification",
          method: String, locations: Location[], note?: String}
Location = {source: Id, path: String, span?: [Nat, Nat]}
Snapshot = {id: Id, role: QName, origin: Id, subjects: Subject[], atoms: Atom[]}
Subject = {id: Id, sort: QName, origin: Id}
Atom = {id: Id, subject: Id, predicate: QName, value: Value, origin: Id}
```

`Nat` の JSON number は 0..9007199254740991 の整数。これは位置・添字・件数用であり、
数学的な数値の encoding とは別である。全 ID は同じ種類の表内で一意。
subject ID と atom ID は snapshot 内で一意。snapshot の array 順は意味を持たない。
subject/atom/origin/source/vocabulary の表も ID による集合であり、順序は意味を持たない。

`VocabularyBinding` は L に含まれる module の `sort`・`data`・`predicate`・`pure` 宣言の
canonical JSON array（宣言名順）の SHA-256。import 先の参照型を含め、実際に使用する
全 module の binding を必須とする。Law の query を変えても同じ語彙なら再観測を要求しない。
binding 不一致は `vocabulary_mismatch` であり、型の偶然の一致で読み替えない。

snapshot の `role` は Law の `roles` に宣言した完全修飾名。`current`、`candidate` などは
利用する Law の語彙であり、核が特別な意味を付けない。同一 role の複数 snapshot を許す。
`mode` は計算の根の区分であり、snapshot とその subjects/atoms の origin は同じ mode とする。
role は計算による選択に使えるが、mode は結果の由来に使い、要件の真偽を決めない。

subject の列挙は、その sort の対象の存在という原始事実である。ID は参照 handle であり、
文字列分解・順序比較・数への変換を Law に公開しない。同じ sort の同じ綴りの ID も
異なる snapshot では異なる subject。跨る参照は明示する。
subject を生成した観測箇所を `origin` に記録する。宣言された有限 family の外にある
未登録 subject を核が想像して追加しない。

Atom の五成分は、predicate 宣言 P を用い
`(P.atom_kind, P.axis, subject, P.name, value)` と一意に復元する。
kind/axis の二重記入は許さない。subject の sort は P.domain と一致しなければならない。
同じ subject/predicate に値を二つ記録することは、同じ値であっても `duplicate_fact`。
多項関係は payload の Tuple、複数関係は Set/List、名前付き操作・セルは独立した subject と
その field によって表す。平行辺、反復する incidence、操作名を Set 化して失わない。
面の各出現は位置・向き・整数係数を保持し、微分では出現ごとの符号付き和を取る。

## 3. 原始型と値の唯一の encoding

型の JSON 表現は次の通り。

```text
P ::= "Unit" | "Bool" | "Z" | "Q" | "Text"
    | ["Fp", DecimalPrime]
    | ["Ref", QName] | ["Tuple", P, ...] | ["List", P] | ["Set", P]
    | ["Option", P] | QName
    | ["Term", [P, ...], P]
```

QName は Law の有限 `data` 宣言（有限木の帰納型）を指す。Ref は `sort` を指す。
`data` の再帰は自己参照の直接出現または List/Option/Tuple を通る正の出現だけ。相互再帰は禁止。関数域・Set 要素・Term 内を通る
再帰を禁止する。全値は有限木であり、Ref 以外の循環表現はない。

| 型 | JSON 値 | 検査 |
| --- | --- | --- |
| Unit | `[]` | 唯一の値 |
| Bool | `true` / `false` | 文字列は拒否 |
| Z | `"-12"` | `0` または `-?[1-9][0-9]*`。`-0`を拒否 |
| Q | `["-2","3"]` | 分母は正、最大公約数1、零は `["0","1"]` |
| Fp | `"4"` | 宣言 p は素数、0 ≤ 値 < p |
| Text | `"..."` | 観測した原始文字列。provenance とは別 |
| Ref(S) | `["snapshot","subject"]` | subject が存在し sort=S |
| Tuple(P…) | `[v,…]` | 成分数と型が一致。空 Tuple=Unit |
| List(P) | `[v,…]` | 順序・重複を保持 |
| Set(P) | `[v,…]` | 順序を無視、重複拒否 |
| Option(P) | `{"none":true}` / `{"some":v}` | 明示的な不在 / 存在 |
| data D | `{"tag":"Constructor","args":[v,…]}` | constructor の引数型と一致 |
| Term(P…,Q) | `{"params":["x",…],"body":Expr}` | 後述の原始純粋部分言語 |

配列の型は前後の型から決定し、値の外見から推論しない。
Fp の p は文字列整数。素数判定に計算予算が足りなければ中断とし、合成数なら不正入力。
Text は等値とタグとしての保存だけに用いる。パスからモジュールを抽出する演算や正規表現は
核に設けない。意味の違いは観測者が別の原始事実として記録する。

Term はコードから観測した操作の有限な数式を保持する。body は [Law DSL](law.md) の
`lit,var,if,tuple,get,ctor,match,let,call` を使い、call は純粋演算と L の `pure` 関数だけ。
自由変数は params だけ。field lookup、snapshot 列挙、query、導出型 constructor、再帰関数の
呼出し、ネットワーク、外部 code、結果参照は含められない。closureは導出演算であり、
原始Termからの直接・間接呼出しをtypeエラーとして拒否する。
観測した原始演算を組み合わせる純粋関数が L に必要なら先に語彙として宣言する。
Term 自体の値は既知でも、その関数の等値を決定できるかは別の問いである。

## 4. 欠測と不在

subject が存在し、型の合う predicate の Atom がないとき、その field は未知である。
Hole の ID は `(snapshot, subject, predicate)`。型は宣言 payload。
同じ field を何度読んでも同じ Hole。異なる field は異なる Hole として保持する。値が等しい補完も異なる補完も許す。
ArchMap に `null`、`unknown`、架空の数値を入れる必要はない。

空 Set/List は「この有限モデルで記録する関係が空」、Option none は「不在を観測した」。
未記録の Set field は空集合と違う。predicate はすべて単一値であり、欠測が許容される。
`required` な Law の operand であっても入力全体を不正にせず、その評価を未決にする。
未知 field の型が空型になる `data` 宣言は拒否し、空の補完集合から全称成立を作らない。
すべての data は少なくとも一つの有限 ground value を持つことを型検査する。

入力の矛盾は、型違い、dangling ref、重複単一値等の提示違反である。
異なる predicate の値が Law を破ることは、有効な入力についての反証である。
Law を満たすように値を補完してから Law を検査することはない。
補完では既知値・登録 subject・origin を固定し、欠測 field だけをその型の値で満たす。
subject の集合まで拡張する「全実装について」の量化は、この有限 snapshot の量化と別であり、
v0.6.0 の query scope に宣言できない。コード全体への対応は観測側の責務である。

## 5. 由来とソース

`Source` は観測に使った source tree/content の識別子。uriとrevisionは非空文字列。uri・revision・digest の文字列から
Law の結果を変えない。uri の解決や source の正しさの検証は CLI が自動で行わない。
`digest` は観測側が指定する内容 digest であり、kernel certificate として使わない。
Location.path は source root 相対の `/` 区切り。空、絶対path、`.`、`..` segment を拒否する。
span は UTF-8 byte の半開区間 `[start,end)`、start ≤ end。省略はファイル全体。
存在確認、byte 範囲と実 source の一致は観測側が扱う。

observed の Origin.locations は1件以上で、実装コードの使用箇所を指す。
テストコードや runtime trace はこの観測に含めない。この意味上の適格性を
ファイル名の heuristics で核が認定することはない。
proposed/specification は locations が空でもよいが、その場合 note は非空必須。
method は観測・提案の作り方を説明する非空文字列。結果の prose を読んで数値へ戻さない。

provenance を変更すると artifact digest と出力の由来は変わる。原始値と参照を固定した
場合、数学的な結果は変わらない。古い source revision を新しい版の結果と呼ばない。

## 6. Law document と再利用

Law document の詳細は [Law DSL](law.md)。全 module を一つのファイルに同梱する。
ネットワーク import、探索パス、暗黙 stdlib、外部 package lock はない。
module は digest と alias を用いて同梱 module を参照する。共有 module をコピーして再利用し、
変更は新 digest になる。展開済み L の内容を結果に保存する。

結果・中間行列・候補証明・cover は ArchMap の形式へ読み込まない。
候補設計は原始語彙の snapshot として追加できる。候補対応の表は、実装に記述された対応、
または提案された対応という原始関係として記録できるが、保存成立の判定は入力に持たない。
これは同じ二入力で再計算する対象であり、前回の結論の輸入ではない。
