# ArchSig v0.6.0 観測値の Law・view 評価コア PRD

## 問い

検査済みの Atom 定義・Law・ArchMap から、選択した view の値と Law の成立・反証・未決を
計算し、原式の各出現と観測事実まで辿れる型付き回答を内部 API で返せるか。

## 対象と参照先

実装先は `tools/archsig_v0.6.0`。観測環境での `evaluate(View,B)` と `check(Law,B)` を対象とし、
三入力の読込み・静的検査から Request 解決、評価、回答データの生成までを接続する。
仕様は [v0.6.0 I/O](../tool/archsig_v0_6_0_io/README.md)、提供済みの範囲は
[実装 README](../../tools/archsig_v0.6.0/README.md) に従う。

| 参照先 | 今回実装する部分 |
| --- | --- |
| [Atom 定義 §4](../tool/archsig_v0_6_0_io/definitions.md#4-検査と責務)、[入力 §§3–6](../tool/archsig_v0_6_0_io/inputs.md#3-型と値) | 三入力の検査、原始値・参照・欠測・由来 |
| [Law §§3–6](../tool/archsig_v0_6_0_io/law.md#3-型と有限の観測族) | 型付き式、束縛、適用域、補完に対する評価 |
| [核の構成 §§1・9・10](../tool/archsig_v0_6_0_io/computations.md#9-v060-の必須決定範囲) | Law instance、有限評価、Z/Q アフィン等値、意味を保つ計算計画 |
| [実行 §§2・3・6](../tool/archsig_v0_6_0_io/execution.md#2-問いの構文と参照) | 対象二種の Request・依存解決、観測環境、内部の状態・中断 |
| [型付き結果 §§1–3・6](../tool/archsig_v0_6_0_io/results.md) | result/2 の Request・Answer・Node・証拠・理由・射影 |
| [適合例](../tool/archsig_v0_6_0_io/validation.md) | Counter、Reservations、Engine と入力・評価・空域の例 |

公開 CLI は現在の `check` / `version` を維持する。`run` の公開、ファイル出力・receipt・
終了コードへの評価結果の接続、`--reuse` は後続とする。
`build` の ObjectAlgebra・equation realization、`map/compose/compare` の問い、局所化・
貼り合わせ診断、`solve/repair/quotient/needed` の問い、コード観測エージェント、
性能最適化、巨大例、マニュアル作成は対象外。
式内の Path 構成・合成・等値は Law の評価として対象に含める。

Law 作者は値の読みと規則を宣言し、エンジンは必要な構成・算法・計画とその検査を引き受ける。
利用者に計算手順や証明フラグを追加入力させない。コードと観測の忠実な対応は観測者の責務とし、
評価器は三入力からの導出を検査する。v0.5.x の依存・コピー・移植・互換層は導入しない。

## 現状と接続

| 実体 | 再利用するもの／追加するもの |
| --- | --- |
| [definition](../../tools/archsig_v0.6.0/src/definition/mod.rs)、[model](../../tools/archsig_v0.6.0/src/definition/model.rs) | `check_definitions` / `CheckedDefinitions` の原始定義、meaning、binding、依存、入力位置・digest を再利用する |
| [law](../../tools/archsig_v0.6.0/src/law/mod.rs)、[AST](../../tools/archsig_v0.6.0/src/law/ast.rs)、[model](../../tools/archsig_v0.6.0/src/law/model.rs) | `check_law` / `CheckedLaw` の宣言署名、原式 arena、式型、名前の解決先・出現位置を再利用し、評価用の lexical binding と呼出し接続を作る |
| [archmap](../../tools/archsig_v0.6.0/src/archmap/mod.rs)、[model](../../tools/archsig_v0.6.0/src/archmap/model.rs)、[value](../../tools/archsig_v0.6.0/src/archmap/value.rs) | `check_archmap` / `CheckedArchMap` の既知値・欠測 slot・snapshot・origin/source、検査済み Term body を再利用する。`Value` の構文上の比較を Law の外延等値へ流用しない |
| [補完検査](../../tools/archsig_v0.6.0/src/archmap/complete.rs) | 補完の存在検査を再利用する。現在の内部探索は存在を確認して止まるため、評価に必要な全補完の列挙・相関保持・証拠への接続を追加する |
| [run.rs](../../tools/archsig_v0.6.0/src/run.rs)、[result.rs](../../tools/archsig_v0.6.0/src/result.rs) | 前者は `run_check` と `version` の実行器。後者の `CheckResult` は requests/answers/nodes を空で出す専用構造。入力識別・宣言表示を再利用し、評価の Request、Answer、導出 DAG、動的な理由・状態を新設する |
| [types.rs](../../tools/archsig_v0.6.0/src/types.rs)、[issue.rs](../../tools/archsig_v0.6.0/src/issue.rs) | 既存 Type は Law の型、Issue は入力検査用。結果専用型と Ref、request・依存 node・missing を持つ評価理由、partial を含む状態の表現を追加する |

## 実装要求

### R1. 三入力から回答までの内部 API

次の三段階を同じ内部入口から実行でき、検査済み三表を渡して評価だけを呼ぶこともできるようにする。

1. `check_inputs`: 明示された定義ファイル列・Law・ArchMap の byte 列と入力識別を読み、
   既存の検査を定義→Law→ArchMap の順で呼ぶ。元 byte 列、digest、位置、検査済み三表を
   一つの入力 bundle に保持する。三表は同じ定義 identity を参照し、別の定義で検査した表を混ぜない。
2. `resolve_observed_requests`: 観測環境用の要求を構文解析・型解決し、束縛・既定規則・
   公開射影・依存グラフを確定する。内部の受付対象は上記二種で、`on` を省略した形に限る。
   対象外操作や Architecture 環境はこの入口の適用外として区別し、result/2 の成功・
   `unsupported_algorithm`・公開 CLI の `usage` に読み替えない。
3. `evaluate_observed`: 解決済みの要求を依存順に評価し、result/2 に従う
   inputs/declarations/vocabularies、requests/answers/nodes/issues と状態を持つ内部結果を返す。
   回答・導出データは仕様の欄・型で JSON 化して検査できるようにする。
   CLI の `command`・`exit_code`・配送情報を持つ完成した run 出力は今回の成果に含めない。

要求の原文、完全名、明示束縛と `observed_environment` / `universal_parameters` を保持する。
`@snapshot/subject` と同一 batch の `$id.output...` を解決し、view は全 parameter、Law は
指定された parameter を束縛する。固定引数名と衝突する名前は `bind.` を使い、短形との重複を拒否する。
値・式・仮定を Request から追加せず、引数不足、未知名、型・owner 不一致、不正射影を検出する。
後方参照を許し、同順位は指定順、Answer は要求の指定順とする。

未使用の定義・語彙・dependency・import・宣言を検査して保持し、未使用だけを理由に拒否したり、
観測を要求したりしない。実在する不正参照、型・版・digest 不一致は選択外でも検出する。
計算は選択した問いとその依存に限る。

### R2. 観測環境と式の評価

三表から subject/slot の索引、型・owner に従う有限参照族、lexical binding、
Law instance、量化域、型付き原始値・導出値を構成する。`on` なしの参照型 parameter は
全 snapshot の登録族を使い、依存 parameter は左から束縛した owner の族を使う。
未知 owner のため所属が変わる族は条件付きで保持し、subject を削除しない。

[Law §4](../tool/archsig_v0_6_0_io/law.md#4-式束縛純粋性) の view/law で使える式を評価する。
let、if、match、field/tuple 射影、constructor、container、内包表記、有限量化、view 呼出し、
検査済みの有限木に対する構造再帰、Map/Term 適用、数値・論理・集合演算を含める。
Z は任意精度、Q は既約有理数、Fp は宣言した体で計算し、Tuple も成分型を保つ。
未知の木や無限型の全域を、観測した有限例で代用しない。

Path の端点・生成元名と順序、式内の合成・等値に必要な共通 Atom carrier と有限作用を
標準規則から構成する。`identity`、`path`、`then`、`source`、`target` と Path を含む
List/Tuple/Option の導出値を扱う。Path の等値は実作用、Term の等値は関数外延を比較し、
語や構文の相違だけで不等にしない。無効な `then` の端点は `condition_failed` とする。

これらは評価に必要な内部構成であり、Architecture・ObjectAlgebra・EquationPresentation、
保存済み Operation や ConfigurationMap を完成した出力として生成しない。
等号の左右・数値成分の差の評価と Z/Q アフィン正規化は今回行う。
共有環・記号座標 ν・評価 ε・ideal・AAT 接続の生成は後続の equation realization に残す。
軽い構造生成を `build` の実装と扱わない。

### R3. 量化・欠測・決定範囲

未束縛 Law parameter と明示量化の意味を [Law §§3・5・6](../tool/archsig_v0_6_0_io/law.md#5-law-の表示と適用)
に従って保つ。有限参照族、Unit/Bool/Fp、非再帰の有限 data と有限な Tuple/Option/Set、
明示 List/Set の要素域、型・参照制約に適合する有限 Map を列挙する。
空域も型・量化・件数を保持する。guard=false は not_applicable、未知 guard は条件付きの
適用として扱い、body の未評価を成立済みと表示しない。

未知 slot の identity を `(snapshot,subject,field)` で共有し、同じ slot の全出現と
異なる slot を区別する。有限型・原始参照の補完を、既知値・owner・Map 全域性などの
入力制約を保って列挙する。独立に slot ごとの値を選んで不整合な補完を混ぜない。
補完を絞る条件に Law の成立を使わない。

数値アフィン式は同じ未知を同じ記号とする正確な Z/Q 係数正規化を行う。
全代入等値は正規形と必要な反例で判定し、未束縛・量化 parameter の全域と、
欠測を埋める全補完を区別する。ある補完で偽というだけで観測 Law を反証しない。
有限補完とアフィン式が混在する場合も、各補完の条件・共有記号・量化順序を保つ。

全補完で同じ値／真／偽を確認した場合に値／成立／反証を確定する。
確認できない場合は未決とし、missing と依存式を保持する。
Bool の短絡、同じ未知の差、既知反例による全称の反証を必須とする。
一般の非線形・無限域で必須決定範囲外の判定には、原式・型・量化域と
`unsupported_algorithm` の必要な判定を残す。欠測も原因ならその理由を併記する。
既知値での非線形算術や有限計算を、式の形だけで非対応にしない。
補完不能は入力検査の `inconsistent_observation` とし、空虚な成立へ進めない。

### R4. 型付き回答・導出・依存

[結果 §§1–3・6](../tool/archsig_v0_6_0_io/results.md#2-回答条件導出) の型・規則を使って
Expression、Domain、LawInstance、Evaluation、Proposition、Evidence と値 node、
および各 payload 内の Binding を生成する。
各問いへ一件の Answer を返し、`evaluate` の確定値と `check` の命題の判断を分ける。
反証には claim と検査可能な証拠、未決には必要な理由を付ける。

原式の各出現、呼出し・量化ごとの束縛、role、guard、適用、等号両辺と数値成分の残差を保持する。
Evaluation.parts から子評価と元 AST の位置へ辿れ、簡約・共有後も原式の支持を消さない。
Scope は reading、snapshot、由来の mode、量化域、全補完の範囲を保持する。
定義の Location、Law の byte span、原始事実の FactPointer から origin/source まで追跡できる。
計算した値や補完内の証拠値を観測 Atom に追加しない。

全 Ref（payload・型・条件・証拠・理由を含む）が既出 node だけを指す DAG を構成し、
型と導出条件を検査する。Proposition の判断と node の value/blocked を区別し、
未決命題の式は保持できる。blocked の通常値や partial の表示を後続の値に使わない。
生成値・正規化・全列挙・反例を原式と入力へ照合して検査する。

公開射影は、今回生成する Evaluation、Path、Law の結果型 T に関係する
[結果の射影表](../tool/archsig_v0_6_0_io/results.md#公開する意味上の射影) に従う。
未生成の出力を読む問いは `dependency_blocked` と元理由を推移的に保持する。
実値で初めて分かる index/constructor/Option の不適合や、省略された
Evaluation.environment の射影は `condition_failed` と依存先の `dependency_blocked` に分ける。
静的に確定しない型・owner は制約を保持し、射影後の不適合も同じ規則で扱う。
表示用の証拠や metadata を束縛値として取り出す経路を作らない。

### R5. 内部の状態と中断

[実行 §6](../tool/archsig_v0_6_0_io/execution.md#6-状態終了コード予算) の状態と優先順位を
内部結果へ適用する。確定のみは complete、未決を含むと partial、要求・入力不正は invalid、
未知 format/semantics は unsupported、予算消尽・取消は interrupted、内部障害は error とする。
Law の反証は有効な完了結果、算法非対応は問いの未決であり、版非対応と混同しない。

入力検査・要求解決・評価へ同じ中断制御を渡し、式評価と有限反復の前後で確認する。
時間・メモリ使用量と SIGINT/SIGTERM の取消通知を注入可能にし、小さい試験で停止を再現する。
`budget_exhausted` の resource/limit/observed と `cancelled` の signal を理由に保持する。
停止後は新たな導出を始めず、検査済みの値・反例と元の理由を保持し、
解決済みの未着手問いにも undetermined と停止理由を返す。
検査不成立・中断時の宣言表、要求解決前の requests、入力不正・依存循環時の空の
nodes/answers は現行仕様の段階規則に従う。依存循環は意味計算前に検出する。
ここで検証するのは内部データであり、OS signal 捕捉・finalize・CLI exit code 連携の完成は要求しない。

## 受入条件

以下は実装の受入条件である。各条件を小さい内部 API テストで検証し、
三入力の byte 列→既存検査→Request 解決→評価→型付き回答データを通す。
下位算法の単体テストだけで一貫した接続の代わりにしない。

| ID | 入力・操作と期待結果 |
| --- | --- |
| AC1 | 既存 `counter.*` で amount=Z の `"2"`、nonnegative/bounded は成立。count=12 では nonnegative 成立・bounded 反証、count Atom 除去では subject を保持し三問とも missing_observation。入力不正にはしない |
| AC2 | Bool=false を返す view の evaluate は established、同じ false を要求する Law の check は refuted。guard=false は not_applicable、guard 未観測で body=false は未決、body=true は全補完で成立。一般 Bool を整数残差にしない |
| AC3 | 未束縛の参照・有限値 parameter、依存 owner、複数 snapshot、明示 `in`/型量化を評価し、域・束縛・件数を保持する。空域は forall=true / exists=false、空 sum/count は型付き零。空域の不正な body も事前に拒否し、field が欠測の subject は域から除かない |
| AC4 | let/if/match、view 呼出し、有限木の構造再帰、Map/Term 適用、container・内包表記・数値/論理演算を小さい値で評価する。List の順序・重複、Set の外延等値、明示 none・空・零・欠測を区別し、Q/Fp/Tuple の正確な型・値を保つ |
| AC5 | 同じ未知 h:Z/Q の h−h は零、h−h=0 は成立、h−h=1 は反証。2−h、h=0、全 z に対する z+h=z は未決で missing=h。量化 parameter と欠測を区別し、補完2/3などの証拠値を観測値にしない。別 slot h/k の h−k は相関させない。false and x / true or x は x 未観測でも確定し、原式の出現・支持は残す |
| AC6 | 未観測 Bool/Fp・有限 data/container・参照・Map と未知 owner の小さい例で、入力制約に整合する全補完を扱う。例えば A/B の根と owner 未観測の一 subject では A の族への所属を勝手に確定しない。族の件数が変わる問いは未決、各補完で同じ値を返す問いは確定する。既知 Map が owner を制約する場合もその制約を保つ |
| AC7 | 全称の一 instance に既知反例、別 instance に欠測があると、欠測を先に読んでも refuted と反例を保持する。全補完が空になる入力は inconsistent_observation。有限の全検査で成否が変わる場合は未決と補完対を保持する |
| AC8 | 既存 `engine.*` の Engine.preserves は add で全 Z 代入について成立、subtract で原式へ再代入できる反例、operator 欠測で未決。生成 IR・各 view・係数正規化・原始事実を追跡する。Q の全代入で `q+rat(1,2)+rat(1,2)=q+1` は成立、右辺を `q+2` にすると反証。有限 Term 外延等値と異なる構文の同じアフィン Term を確認する。必須範囲外の無限非線形判定は原式・型・量化域付きの unsupported_algorithm |
| AC9 | 既存 `reservations.*` の conserved は成立。q-free=2 で左右3/2・残差1と反証、q-free 欠除で missing=(v,q,Reservations.State.free)。短名・省略 guard と完全名・明示 true の宣言は判断を保ち、各自の原式 span・出現・束縛へ戻る |
| AC10 | Path と Option<Path> を返す view を評価し、名前付き列、端点、実作用、非原始 container の Ref encoding を保持する。恒等・合成・作用が等しい別の語の式内等値を確認し、不正端点の then は condition_failed。原始 Atom や保存済み Operation へ昇格しない |
| AC11 | 同一 batch の評価値を後続 view/Law の束縛へ渡し、後方参照・依存順・指定順の Answer・explicit/defaulted を確認する。不足束縛、重複 ID/引数、未知名、静的な型/owner/index 不正、非公開射影を拒否する。動的な射影不適合と、省略された Evaluation.environment は condition_failed、依存先は dependency_blocked。未生成 value の参照は元の missing/unsupported 理由も保持する |
| AC12 | 二つの evaluate が互いの出力を束縛に使う循環を作る。内部状態 invalid、循環する各 Request ID の cycle、解決済み依存グラフを保持し、nodes/answers は空。Law/ArchMap の位置を原因にしない。未使用宣言内の不正循環は既存の静的検査で入力位置付きに拒否する |
| AC13 | Answer/claim/judgment の整合、全 Ref の型と既出参照、blocked/partial の非消費、各 AST 出現・量化束縛・数値残差・support・origin/source・Scope をデータで検査する。未決出力があっても確定値・反例を残す。provenance のみ変更した対で数学的判断を保ち、新しい由来へ戻れることを確認する |
| AC14 | 定義や Law の検査失敗では宣言・語彙表を空にし、検査済みの定義/Law の後に ArchMap が失敗した場合は両表を保持する。未知版は unsupported、入力不正は invalid、反証のみは complete、反証と未決の混在は partial。検査・要求解決・評価の途中へ取消／予算消尽を注入し、段階に応じた結果保持と未着手の停止理由を確認する。内部障害を成立・反証に変換しない。予算増加で確定判断を反転させない |
| AC15 | `counter-library.atoms.json`、未使用 import/dependency、選択しない有効な宣言を追加しても Counter の回答は同じで、未使用情報は保持する。選択外の不正参照・型・版/digest 不一致は拒否する。既存 check/version の意味と check の空 requests/answers/nodes、公開 run の usage を維持し、v0.5.x 参照・移植を含めない |

## 実装計画と検証

1. 三入力 bundle と対象二種の要求解決を実装し、依存・射影・中断制御を接続する。
2. 観測環境、型付き値、束縛、式・有限木・Path の評価を実装する。
3. 有限量化・整合する補完・Z/Q アフィン相関と、成立・反証・未決の判定を接続する。
4. 型付き回答・証拠・DAG 検査を接続し、上記の一貫した API テストを完成させる。

既存 [fixtures](../../tools/archsig_v0.6.0/tests/fixtures/) の Counter / Reservations / Engine を
基礎に、欠測や空域などに必要な小さい変種を使う。テストは crate 内の fixture を読み、docs を読み込まない。
実装時の検証は [実装 README のテスト手順](../../tools/archsig_v0.6.0/README.md#テスト)に従い、
対象テスト名を指定して一件ずつ実行する。全 cargo test、並列重量テスト、大規模負荷測定を要件にしない。
マニュアルを追加せず、実装 README の提供範囲だけを実装と合わせる。

## 失敗判定と停止条件

次は当該実装の未達とする。

- 欠測を零・none・空などの確定値へ補完する、欠測で存在する subject を除く、
  または原式の出現統合により支持・由来を失う。
- 必須の有限評価・アフィン等値を未実装のまま unsupported_algorithm で済ませる。
- 三入力の検査や Request 解決を迂回した単体評価だけで受入完了とする。
- CheckResult の空出力を評価結果として扱う、対象外操作を空の成功にする、
  build を軽い構造生成へ縮める、または内部 API の完成を公開 run の完成と扱う。
- 評価器の保証を source 観測の忠実性へ拡張する、または v0.5.x に依存・移植する。

現行 I/O の意味変更や対象外の公開機能が不可欠と判明した場合は、その箇所と必要な判断を示して停止する。
要求解決・補完・相関・導出・状態の接続は今回の必須実装として扱い、後続判断へ送って完了にしない。
