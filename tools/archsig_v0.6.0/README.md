# ArchSig v0.6.0

[v0.6.0 I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md)に従い、独立Atom定義と、
その共通語彙を参照するLaw・ArchMapを検査する。
旧版 `tools/archsig` とは独立したクレートである。

## 現在の範囲

- 独立 Atom 定義の API (`archsig::definition::check_definitions`): JSON schema・namespace・
  依存 DAG・binding・原始型を検査し、meaning・入力位置・語彙 manifest と digest を保持する。
- Law の静的検査: 構文・版・名前・型・依存型・構造再帰・純粋性。
- 型付きの宣言と原式、出現位置、参照の解決、既定規則(`archsig::law::check_law`)。
- Atom定義の語彙 manifest と digest、各定義ファイルとLawの `bytes_digest`・`model_digest`。
- ArchMap の静的検査: 版・schema・ID・由来・語彙 binding・原始値の型と encoding・参照・
  依存型の所属・Map の全域性・欠測 slot の補完の存在。既知値と欠測 slot を持つ内部表現と
  `model_digest`(`archsig::archmap::check_archmap`)。
- 観測環境の準備 API (`archsig::observed::prepare_observed`): 元 byte 列・入力識別・
  digest と検査済み三表を保持し、`evaluate` / `check` の束縛・型・公開射影・
  依存順を解決する。循環は該当する問いの ID と依存グラフを保持して拒否する。
  検査済み bundle を再利用する入口と、検査・要求解決で共有する予算・取消制御を持つ。
- 観測評価 API (`archsig::observed::evaluate_observed_bytes` / `evaluate_observed`):
  明示束縛した原始参照、Z/Q/Fp/Bool/Unit/Text/一般Tuple/List/Set/Option の fieldと
  型付きliteral、`rat`、Tupleの構成・射影、括弧を共通の AST 評価器で読む。
  Z/Q/Fp と数値Tupleの加減乗算・負号・等値、Z/Q の順序、
  Bool の等値と not/and/or/implies を計算する。
  Q は正分母の既約形、Fp は宣言した法、数値Tuple は入れ子の成分型を保つ。
  Listは順序と重複を保ち、Setの構成は重複を除いて外延的に比較する。
  元literalの全要素評価・順序・支持を導出に保持し、空List/Setとnoneにも要素型を保つ。
  `count`・数値要素の`sum`・`in`を評価し、空の和は元の数値型の零を返す。
  一般Tupleを数値演算の対象にせず、none・空・零・欠測を区別する。
  既知List/Setを域とするSet内包は、各要素の束縛でfilterと要素式を評価する。
  反復の束縛を元域のEvaluationとList位置またはSet要素へ接続し、
  入れ子内包・view呼出し・let/ifの親環境へ戻る。
  falseのfilterでは要素式を実行せず、空域は元要素型の空Setを返す。
  未観測の域・filter・必要な要素で結果が決まらない場合は、元missingと依存式を保つ。
  既知List/Setの明示`forall/exists ... in ...`は、元collectionと型付きの有限Domain、
  実binder・body評価・元順の量化Scopeを保持する。Domainは重複しない意味上の要素域とし、
  元Listの順序・重複出現はcollection評価に残す。空域はforall=true・exists=falseとなる。
  全域に依存する確定判断は全要素・bodyのcoverageを再検査したfinite_exhaustionへ接続し、
  forallの既知false instanceは他instanceの欠測によらず反例として保持する。
  existsは既知true instanceでtrueとなり、既読のmissing・支持を保持する。
  `forall/exists x:T`はUnit/Bool/Fp・登録済みplain参照族と、それらからなる有限な非再帰Data・Tuple・Option・Setの
  全値域を元型・宣言から列挙する。未使用binderも元の検査済み型を保持し、
  型付きDomain・実要素・全coverage・反例へ接続する。型域にはcollection評価を作らず、
  全列挙は同じ中断制御の下で行う。
  plain参照族は全snapshotの完全型名が一致するsubjectを(snapshot,id)ごとに列挙し、
  fieldやownerの欠測で除かない。空snapshotを含む範囲とsnapshot/subjectの由来mode、
  subject存在の支持を、型域・実binder・判断の導出へ保持する。
  数値等式には元左右と同じ型・形の残差を保持し、一般Boolには数値残差を付けない。
  検査済み既知Mapは元の参照pairと両端型を保ち、行順によらず同じ域上の値で等値を判定する。
  空域の空表、Mapを含むTuple/List/Set/Optionも型を保つ。欠測Mapは元slotのまま通常値へ補わない。
  Map適用・有限Map型全域と参照制約付きMap補完は未実装である。
  これらの値型と原始参照について、letの入れ子・名前使用とifを評価する。
  letの名前は元の右辺評価へ戻り、未観測右辺を通常値や全称parameterにしない。
  ifは条件と両枝を保持し、未観測条件でも両枝が同じ既知値なら全補完で確定する。
  これらの値型・検査済みの有限data木を引数・返り値に持ち、ownerに依存しない署名のview呼出しを評価する。
  左端data parameterのmatchから得た直接subtermへの構造再帰も、各実引数とcall frameを保持して評価する。
  引数なし・複数引数・入れ子・import aliasを扱い、呼出しごとに元の引数評価・parameter束縛・
  callee bodyの導出を保持し、呼出し元のlexical bindingへ戻る。
  未観測の実引数は欠測理由を保ち、その引数を使わないbodyは既知値を返せる。
  上記の値型・原始Refと有限data木を引数に持つdataについて、
  観測field・constructorを評価し、data型・正規constructor・引数の型と順序を保つ。
  これらのdata値をlet/if/viewで渡し、構造的な等値・不等値を計算する。
  既知値のmatchはconstructor・wildcard・名前・入れ子patternを扱い、
  pattern束縛を元scrutineeのconstructor引数位置へ接続する。
  data以外の既知値もwildcard・名前patternで受ける。
  未観測dataのmatchは元missingを保ち、constructorやpattern束縛値を作らない。
  Tuple/List/Optionを通る正の自己参照も個別の有限木として扱い、再帰型の全域を有限とは扱わない。
  ドット列は束縛変数から既知参照を順にたどり、各prefixの元span・型・実owner・支持を保持する。
  Z/Q全域式内のドット列は一つのfieldまで扱う。
  Bool は false and x / true or x などを全補完で確定し、元の両子評価と欠測理由を保持する。
  Bool の view は false も評価値として確定し、Law は要求する Bool の成立を判断する。
  Z/Qの欠測slotは同じ記号として係数をまとめ、加減算・負号・定数倍で係数が消えた式の値を確定する。
  元fieldの欠測と全出現を保持し、`h-h`の零から`h-h=0/1`の通常比較・Law判断へ接続する。
  左右に欠測が残るZ/Qの等値・不等値も、差の全係数が消えたときは定数残差から判断する。
  元左右Evaluationと差のExpression・normalization証拠を保持し、未知の左右へ具体値を補わない。
  未束縛Law parameterと明示forallのZ/Qアフィン等値は、型Domainと元binderを保ち全代入で判断する。
  parameterと欠測slotの係数を分け、Zの整除条件とQの正確な解から、全補完での成否を判断する。
  反証の具体代入は元式へ戻し、共通の代入が存在しない場合はwholeの正規化から反証する。
  補完で成否が変わる場合は型付き補完対を保持し、その値を観測に追加しない。
  有限型slotの各補完でも先に全域のwholeを判断し、元の支持・欠測・量化を保って集約する。
  有限型のLaw parameterとZ/Q parameterの混在も、元宣言順の有限族の各instanceでZ/Q全域を判断する。
  view内で追加されるZ/Q forallも、外側の自由parameterと区別して評価する。
  この全域評価で必須範囲外の式は、原式・型Domainとunsupported_algorithm理由を保持する。
  未束縛Law parameterのcheckは、plain参照族と上記の有限型を元宣言順に列挙し、
  明示Ref束縛を固定した実直積の各LawInstanceを検査する。自由parameter・型Domain・実bindingsと
  全称命題を保ち、既知違反の実反例は他rowの欠測によらず残す。空直積は成立・全検査0件となる。
  guard=falseのrowはbodyを評価せず非適用として残し、全非適用N件の族は成立・全検査N件となる。
  既知ownerに依存する未束縛Law parameterは、先行束縛ごとに同snapshot・owner一致の参照族を使う。
  固定ownerと自由child、自由ownerと固定childを含め、各prefixの実Domain・元順の束縛と適合するrowを保持する。
  所属を判断したownerの原始事実を支持へ接続し、空fiberも範囲へ残す。
  既知ownerの `State[a]` 式は、同snapshotでownerが一致するentity/arrowの登録族を
  型付きSetとして返し、Set演算・内包・明示In量化へ接続する。
  owner子式のEvaluation・束縛・実producerと所属の原始事実を保持する。
  明示 `forall s:State[a]` / `exists` と、owner添字を持つ参照を含む有限Tuple/Option/Setは、
  元型の添字と現在の実束縛に従う登録族を使い、実Domain・元binder・件数と所属の支持を保持する。
  ownerが未観測で族を確定できない場合は、全補完の範囲と元slotの欠測、
  unsupported_algorithmを未決回答に保持する。
  Law の guard が false なら非適用となり、元の guard/body から条件付き要求を判断する。
  明示 guard と元の body の評価・支持を条件付き Law の導出へ接続する。
  型付きの値・回答・原式の各出現・Law instance・判断・反証の証拠を導出 DAG に保持し、
  欠測 slot と由来を元入力へ接続する。検査・要求解決と同じ制御で評価を中断できる。
  参照を含まない有限型の欠測slotはsnapshot・subject・fieldごとに共有し、元型の全補完域を列挙する。
  Unit/Bool/Fp、非再帰の有限Data、それらのTuple/Option/Setを扱い、各slotの型に従う直積を使う。
  単一Tuple fieldは全体を一slotとして保持し、Optionのnoneと空Setも型の値として区別する。
  各補完内で元の問い全体（未束縛Law parameterの全族を含む）を評価してから集約し、
  全caseで同じ既知値なら値を確定する。Lawは全case成立/全case違反を区別し、
  補完で結果が異なるときは元slot・実代入・whole評価に接続するcompletion_pairを保持する。
  元の欠測理由・各caseの反例・全検査の証拠を残し、他型の欠測は根拠なく値に置き換えない。
  上記以外のpayloadを持つdataの評価、その他の式形・
  上記以外の無限型・Answer 由来の束縛・
  ownerに依存するparameter・返り値を宣言したviewの呼出し・
  有限型補完でも確定しない参照からのfield読取り・上記以外の動的 owner 制約の評価は未実装であり、
  専用の内部 `EvaluationFailure::NotImplemented` を返す。この失敗を result/2 の
  `unsupported_algorithm` や未決回答へ変換しない。
- CLI の `archsig check` と `archsig version`。入力のコピー、`result.json`、stdout の receipt を
  [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md) §§5–7 に従って出す。

提供するコマンドは `check` と `version` だけであり、v0.6.0 全体の適合版ではない。
`run` は CLI の不正(`usage`)として拒否する。

## テスト

```bash
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test TARGET NAME -- --exact --test-threads=1
```

`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md) の
`examples/` と同じ byte 列である。テストは docs を読み込まない。
小さい試験名を個別に指定し、同時には一件だけ実行する。

## 利用手順

```bash
cargo build --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
```

以下の `archsig` は、作られた `tools/archsig_v0.6.0/target/debug/archsig` を指す。

共通定義とLawを検査し、語彙manifest、型付き宣言と元の位置を得る。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --out result-law
```

ArchMapを指定すると、同じ定義へのbindingと原始値・参照・由来・補完の整合性を検査する。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json --out result-both
```

`--out` は存在しない path を指定する。結果は `result-law/result.json` などに書かれ、
stdout には一行の receipt が出る。`archsig version` は版を一行で出す。

定義ファイルを複数指定する場合は `--atom-definition` を指定順に繰り返す。
読込みは明示したファイルだけで完結し、未使用の語彙・依存・importも検査して保持する。
結果は `archsig.result/2`。定義コピーは `inputs/definitions/0.json` 等に保存し、
入力ID `definition0` 等とJSON Pointerで元の定義位置を追える。
