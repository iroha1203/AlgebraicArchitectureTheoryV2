# ArchSig v0.6.0

共通の Atom 定義を参照する Law・ArchMap を検査し、観測環境の view の値と Law の
成立・反証・未決を、型と導出元を持つ結果として計算する Rust クレートである。
旧版 [`tools/archsig`](../archsig/) とは独立している。

## ビルドと利用

リポジトリルートで実行する。Rust 2024 edition 対応のツールチェーンが必要であり、
`--offline` は依存 crate がローカルに取得済みであることを前提とする。

```bash
cargo build --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
export PATH="$PWD/tools/archsig_v0.6.0/target/debug:$PATH"
archsig version
```

三入力と問いを一回の run へ渡す。`--out` には存在しないディレクトリを指定する。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json \
  --ask 'n=evaluate(CountCheck.amount,s=@v/s)' \
  --ask 'ok=check(CountCheck.nonnegative,s=@v/s)' \
  --ask 'audit=check(CountAudit.bounded,s=@v/s)' --out result-counter
jq '.answers[] | {id, status}' result-counter/result.json
jq -r '. as $r | .answers[] | select(.id == "n") | .outputs.value.node as $id
  | $r.nodes[] | select(.id == $id) | .value' result-counter/result.json
```

回答は3件とも established、値は2で、終了コードは0となる。値を12へ変えるとboundedは
refutedで終了コード1、count Atomを除くと不足位置付きundeterminedで終了コード2となる。
型、導出、支持と入力コピーは同じresult.jsonから確認できる。

同じrunへ `--ask 'need=needed($audit)'` を加えると、依存先の未観測位置を
`need.outputs.plan` のObservationPlanで読める。`requirements` はslot・依存Ref・元位置、
`blockers` は欠測以外の理由を保持する。この例のcount=12の反証には追加の観測要求はない。

原始 correspondence の configuration 保存は次のように問い合わせる。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/reservations.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json \
  --ask 'm=map(Reservations.Migration,on=@v/m,reading=Reservations)' --out result-map
```

`kind` の既定値は `configuration`、`to_reading` の既定値は `reading` と同じ読みである。
候補は始終 Architecture と共通 U 上の総作用を持ち、保存を確認した場合だけ map と
Operation を返す。両nodeの `conditions` は同じ保存確認命題を指す。
数量の一致や Law の成立はこの保存条件に加えない。
後続の問いでは `$m.candidate.subject`、`$m.operation.word[0]` などの公開参照を束縛できる。
原始参照を含む Option・Tuple・List の意味上の成分も `on` に指定できる。
動的に成分が存在しない場合は射影条件の反証を残し、後続へ元の理由を伝える。
未観測の所属・対応は部分結果と必要 slot に残り、未生成の出力に依存する問いは元の理由を保持する。
終域に対応する field 宣言がなければ、候補の既知部分・構成条件の反証・元の原始位置を返す。

以前の出力directoryは `--reuse result-counter` で候補として指定できる。
現在の三入力から全再計算し、検査済みの導出へ候補の型・内容・全依存・由来を照合する。
node番号や共有方法の違いは吸収し、候補の推論は計算へ採用しない。
照合できない候補も通常の評価を妨げず、理由は結果の `reuse.rejected` に残す。

### 入力だけの検査

共通定義・Law・ArchMap を一回の check で検査する。

`--out` には存在しないディレクトリを指定する（出力先が既に存在する場合は別の名前にする）。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/reservations.atoms.json --law tools/archsig_v0.6.0/tests/fixtures/reservations.law --archmap tools/archsig_v0.6.0/tests/fixtures/reservations.archmap.json --out result-check
```

`status=complete`、終了コード0となる。結果は `result-check/result.json` に保存し、stdout には一行の receipt を出す。
結果の形式は `archsig.result/2`。定義のコピーは `inputs/definitions/0.json` に置き、
入力 ID `definition0` と JSON Pointer から元の定義位置を追える。

複数の定義ファイルは `--atom-definition` を指定順に繰り返す。
明示したファイルだけを読み込み、未使用の語彙・依存・import も検査して保持する。
ファイル操作と終了コードの詳細は [実行仕様 §§5–7](../../docs/tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力)を参照する。

## Rust API で観測値を評価する

呼出し側の crate から、このディレクトリを `archsig` の path dependency として指定する。
次の例の実行時 cwd はリポジトリルートとする。三入力の byte 列を渡すと、入力検査と
要求解決を経て Counter の値と二つの Law を評価できる。

```rust
use archsig::observed::{
    control::{Control, Limits, Usage},
    evaluate_observed_bytes,
    input::InputSources,
};

fn main() -> std::io::Result<()> {
    let fixtures = std::path::Path::new("tools/archsig_v0.6.0/tests/fixtures");
    let sources = InputSources::from_bytes(
        vec![std::fs::read(fixtures.join("counter.atoms.json"))?],
        std::fs::read(fixtures.join("counter.law"))?,
        std::fs::read(fixtures.join("counter.archmap.json"))?,
    );
    let asks = [
        "n=evaluate(CountCheck.amount,s=@v/s)",
        "ok=check(CountCheck.nonnegative,s=@v/s)",
        "audit=check(CountAudit.bounded,s=@v/s)",
    ];
    // この小例は予算制限・取消通知を設定しない。
    let mut control = Control::new(Limits::default(), |_| Usage::default());
    let result = evaluate_observed_bytes(sources, &asks, &mut control)
        .expect("対応範囲内の Counter 例");
    println!("{}", result.wire().canonical());
    Ok(())
}
```

結果の `status` は `complete`、`n` の値は型 `Z`・payload `"2"`、`ok` と `audit` は
`established` となる。Bool=false の view も値が確定すれば `established`、同じ false を
要求する Law は `refuted` となる。`guard=false` の行は `not_applicable` として保持する。

入力検査と要求解決を分ける場合は [`prepare_observed`](src/observed/mod.rs) と
`evaluate_observed`、検査済み bundle を使う場合は `prepare_checked_observed` を使う。
view は全 parameter の束縛を必要とし、Law の未束縛 parameter は型の全域で検査する。
同じ batch の `$id.value`・`$id.evaluation.value` と公開成分射影を後続の束縛へ渡せる。
計算は依存順、回答は指定順に返し、循環は要求 ID と依存グラフを保持して拒否する。
`Control` は入力検査・要求解決・評価で共有し、呼出し側が予算と計測・取消通知を設定できる。

複数の読取りで同じ検査済み三表を使う場合は、`PreparedObserved::shared_inputs()` の
不変handleを `prepare_shared_observed(handle, &asks, &mut control)` に渡す。
準備・評価結果・要求失敗は同じ入力を保持し、要求と回答・証拠graphはbatchごとに構成する。
共有handleと要求失敗の `PrepareFailure::Requests.inputs` は `Arc<CheckedInputs>` を使う。
既存の所有入力APIもこの入口を使い、入力の再読込み・表の複製を行わない。

検査済み三入力の対象構成を読むには
`construction::construct(&checked, "CountCheck", "v", "s", &mut control)` を使う。
`universe()` は全snapshotの存在事実と既知field Atom、`base()` と `components()` は
選択rootとowned entityのConfiguration候補を返す。候補の `configuration()` は構成が
確定した場合に値を返す。未観測の所属・参照がある場合は `known()` の断片と
`blocking_slots()` を読み、未観測の数量slotは `requirements()` で確認する。
`recheck()` は現在の検査済み入力と同じ選択から構成を再照合する。
このRust APIのConfigurationと、LawやObjectAlgebraの成立は別の計算結果である。

`construction::profiles::construct_profiles(&checked, "CountCheck", "v", "s", &mut control)`
はbaseと部分対象の読取り適用域とquery patternを構成する。
`profiles()` の各行に対象identity、Configuration候補、`domain()`、`pattern()` を保持する。
baseの適用域はrootとowned entity/arrow、部分対象の適用域はそのsubjectとなる。
未知のownerは `domain().conditional()` と候補行の `membership()` で確認する。
確定したpatternの `queries()` は共通Uのatom、全順序対のrelation、全順序対のidentificationの順で、
各queryの真偽を返す。未決の行はpatternを確定せず、他の確定行は保持する。
`known_classes()` は確定patternが等しい行の添字をまとめ、全行確定時には `classes()` を返す。
各行のidentityと適用域は保たれる。Law・viewの読取りの互換性は、それぞれの条件と値の検査を要する。

`construction::maps::correspondence(&checked, "v", "m", "Reservations", None, &mut control)`
は原始correspondenceから共通U上の候補作用とConfiguration保存を計算する。
`correspondence_retained` は失敗の `cause()` と、停止までに検査済みの `partial()` も返す。
別の終域の読みは第5引数へ `Some("TargetReading")` として指定する。
`candidate()` は総作用、`map()` は保存確認済みの写像、`counterexamples()` は保存を破る
原始位置、`missing()` は未観測slotを返す。欠測がある場合も確定した反例を保持する。
Listの順序・重複と参照を含む値の構造を検査し、量leafの一致を保存条件へ加えない。
候補と保存済み写像は、選んだreadingと検査対象のConfigurationを保持する。
各値の `recheck(&checked, &mut control)` で、候補作用と保存の成立をそれぞれ再照合できる。

`construction::maps::internal_arrows(&checked, "Reservations", "v", "A", &mut control)`
は選択rootの全owned arrowを検査する。各 `arrows()` 行に候補・保存済みmap・反例・不足slotを
保持し、ownerが未観測のarrowも候補行として残す。`all_preserved()` は全件完了かつ全行の保存確認を表す。
停止等の失敗は `InternalArrowsFailure::cause()/partial()` で原因と構成済み表を返す。
表の `pending()` は列挙中なら `None`、列挙後なら未処理arrowの列を返し、
`is_complete()` で全件の処理完了を確認する。完成した反例・不足行も `arrows()` に保持する。
一つのarrowは `internal_arrow(&checked, "Reservations", "v", "A", "v", "e", &mut control)`
で検査できる。作用はfromの部分Configurationをtoへ移し、そのF外では恒等となる。
`candidate.subject()` の `Some` で元arrow/correspondence、`source_object()/target_object()` で
reading・root・部分対象のsubject identityを読める。`candidate.correspondence()` は
correspondence由来のときだけ `Some` を返す。各結果の `recheck()` は現在入力から再計算する。

保存済みconfiguration操作は
`ConfigurationOperation::from_map(&checked, verified_map, &mut control)` で構成する。
`from_map_retained` の失敗は `cause()/partial()` から停止理由と完成済み操作を読める。
`construction::maps::identity(&checked, "Reservations", "v", "A", None, &mut control)`
はbaseの恒等を構成し、部分対象には第5引数へ `Some(("v", "p"))` を指定する。
結果の `configuration()/missing()` で構成を読み、確定時の `operation()` を使う。
恒等は共通Uの全元を固定し、`word()` は空となる。
`f.compose(&checked, &g, &mut control)` は g∘f の総作用を作り、元操作を指す有限表を
`derivation()` に残す。語は原始生成元名の順序列へ平坦化する。
`word_equal()` と `action_difference()` は語と全域作用をそれぞれ比較し、作用の不一致では
元位置と両像を返す。後者は同じ始終対象・readingを要求する。
操作とそのmapの `recheck()` は元入力から構成を再実行する。恒等・合成の候補は
`subject()/correspondence()` を `None` とし、由来を操作の構成表に保持する。

`construction::maps::configuration_transport(&checked, verified_map, &mut control)`
は保存済みの原始correspondenceから、baseと全部分対象の対応、内部生成操作との全域自然性を検査する。
`objects()` は対応する対象identity・Configuration・保存反例、`generators()` は原始arrowの対応と
両端・自然性の結果を持つ。全対象成分は `action()` の同じ総写像を使う。
自然性の反例には元位置と二つの合成像を保持する。`source()/target()` は未確認の内部arrowも含めた
全検査結果を持ち、`all_preserved()` はこの構造側の全検査の成立を表す。
実像が終域の対象・生成元の族に属さない場合は、構成条件の不成立として `condition_failure()` に元位置と像を保持する。
対象行の `target()/target_configuration()` は該当対象を構成できたときに値を返す。
追加検査が反証・未決でも `operation()` にconfiguration操作を保持する。
`ConfigurationTransportFailure::cause()/partial()` は原因と、検査済みOperation以降の部分結果を返す。
部分結果の `source()/target()` は構成できた表、`objects()/generators()` は完成した行を持ち、
`outcome()` は全比較の完了後だけ `Some` となる。Law/view運搬の停止結果も
`transport` にこの構造側の部分結果を保持する。
Law・方程式・不変量等の運搬はそれぞれの追加読取りを要し、再照合は `recheck()` で行う。

`construction::maps::declaration_correspondence(&checked, verified_map, &mut control)`
は保存済み原始correspondenceから、選択reading間の宣言候補と署名対応を構成する。
`types()` は原始型の移送、`candidates()` はsourceの全Law/view/local/change/relationを持つ。
各候補の `source()/target()` で元metadataと式・依存先の位置、`failures()` で名前・kind・
parameter数・移送後の型の不適合を読める。位置によるowner名対応と複合型・view戻り型まで
適合した場合だけ `pair()` を返す。別readingやaliasから候補を補わない。
`all_signatures_compatible()` は署名照合の結果であり、role・guard・body・値の保存は追加検査を要する。
不適合時も `operation()` を保持し、現在の入力での再照合には `recheck()` を使う。

`construction::maps::reference_type_transport(&checked, &declarations, "Left.Child", &mut control)`
は宣言対応からplain Ref型の全snapshotのsubject域と候補像を構成する。
source ConfigurationのF内は対応表で移し、F外の値は固定する。
`source()/target()/images()` は全候補、`failures()` は型違い・衝突・未到達の具体的な参照を持つ。
全域で順逆合成が恒等のときだけ `bijection()` の `forward()/inverse()` を返し、
不成立時も `operation()` を保持する。現在入力での全域検査には `recheck()` を使う。
Ownedの所属添字・複合値・式評価の可換性はそれぞれの追加検査で扱う。

`construction::maps::finite_declaration_value_transport(&checked, &declarations, "Before.values",
DeclarationValuePosition::Parameter(0), &mut control)` は署名対応済み宣言の有限な値型を選び、
既存の有限域計算で全値を列挙する。view戻り型は `DeclarationValuePosition::Return` で選ぶ。
`source()/target()/images()` は型付きの全値と構造による候補像を持つ。`wire()` で値を表示できる。
`failures()` は終域外の像・衝突・未到達を列挙し、`bijection()` は両全域の順逆対応の添字を返す。
衝突は終域外の候補像も含めて検査する。`Collision.image` は具体的な像、`target` は
終域の添字で、終域外なら `None` である。
Mapの全域性と一価性、Setの像集合を検査し、空の積・関数域も全体の値型で判定する。
`support()/snapshots()/modes()` は参照域の由来、`operation()` は追加条件不成立時も保持する操作である。
Unit/Bool/Fp/Refと有限なTuple/Option/Set/Map/dataを扱い、適用域の判定・列挙・等値は同じ核を使う。
`recheck()` で現在入力から全域と順逆対応を再検査する。

`construction::maps::numeric_declaration_value_transport(&checked, &declarations, "Before.values",
DeclarationValuePosition::Parameter(0), &mut control)` は署名対応済み宣言のZ/Q/Fpと数値Tuple型に、
各数値とTuple位置を固定する順逆写像を生成する。戻り型は `DeclarationValuePosition::Return` で選ぶ。
順逆とも恒等写像なので、有限の値の試行によらず型の全域で互いに逆になる。
`forward()/inverse()` の `apply(&primitive_value, &mut control)` は同じ数値核で正規値を検査し、
`apply_value(&typed_value, &mut control)` は型付きの出力を消費する。出力の `ty()/wire()` で型と値を読む。
`operation()` は元操作、`declaration()/position()` は選択位置を保持する。
`recheck()` は現在入力の宣言対応と数値型から順逆写像を再構成する。式の値の可換性は追加検査で扱う。

`construction::maps::object_law_transport(Arc::clone(&checked), &declarations,
object_index, instance_index, &mut control)` は対応する参照束縛済みLawを同じ対象別評価器で読み、
required status・適用条件・適用時の原式成立の保存を計算する。
`source_reading()/target_reading()` は `required()/application()/body()/conditional()` を持ち、
対象への非適用、所属条件、guardの真偽、元bodyとguard付き命題の真偽を区別する。
有限補完では各caseの元guardとbodyを読み、条件付き命題全体の真偽と分けて保持する。
`outcome()` の成立はLawの読取りの保存を表す。両側の元Lawが反証されても、同じ真偽を保てる。
`source()/target()` は元の評価DAG・支持・Scopeを保持し、`operation()` は確認済み操作を返す。
有限の残scalar parameterには `family()` が全型域の順逆対応 `parameters()` と各代入の比較 `rows()` を持つ。
各行の `source_bindings()/target_bindings()` は位置対応した名前と型付き値、
`source()/target()` は元guard・body・条件付き命題の読取り、`outcome()` はその点での保存結果を返す。
`source_evaluations()/target_evaluations()` は対応する側の元評価DAGのnodes配列添字であり、
有限欠測補完では全caseの行を保持する。全称checkの集約真偽とは分けて全直積の各行を比較する。
族を比較する場合の `source_reading()/target_reading()` は `None` で、読取りは各行から得る。
この有限native APIの型域に接続していないparameterは、対象・元instance・Operationを持つ `NotImplemented` になる。
再検査後の停止では `Stopped` がOperationと部分結果を保持し、部分結果の `outcome()` は比較完了時だけ `Some` になる。
`recheck()` は現在入力からrole・適用・原式の評価・全parameter域と各行の保存条件を再検査する。

`construction::maps::object_view_transport(Arc::clone(&checked), &declarations,
object_index, instance_index, &mut control)` は元の対象別view instanceの参照束縛を運び、
同じ三表と対象別評価器による実評価と、戻り型全域の値写像との可換性を検査する。
`outcome()` は成立・追加条件の不成立・未決を区別し、`operation()` は確認済み操作を保持する。
`source()/target()` は両側の適用状態と評価DAG、`equivalence()` は有限または数値型の全域対応を持つ。
`source_value()/image()/target_value()` の `ty()/wire()` で比較した型付き値を読む。
両側の適用外、適用の不一致、条件付き所属、値の欠測をそれぞれ保持する。
残parameter付きviewと値域対応の適用域外は、元対象・instance・型・操作を持つ `NotImplemented` を返す。
宣言対応の再検査後の停止は `Stopped` に理由と確認済み操作を保持し、`partial` から停止前の評価・型対応・値を読める。
部分結果の `outcome()` は比較が完了した場合だけ `Some` を返す。評価途中のDAGと未着手の比較を区別する。
`recheck()` は現在入力の対象・宣言・束縛・実評価・可換性を再検査する。

`construction::readings::object_reading_instances(&checked, &configuration, &mut control)`
は選択readingのLaw/viewを、標準対象域に適用する参照束縛instanceへ展開する。
`objects()` はbaseとowned entityの部分対象をidentityで保持し、未知所属の候補には
`conditions()` の原始owner slot条件を付ける。`instances()` の `bindings()` は参照束縛、
`parameters()` は残る値parameterの全型域、`applications()` は同じ対象順の適用条件を持つ。
外部参照型の束縛は原始有限族を固定し、同じ未知slotに異なるownerを要求する組合せを除く。
量fieldが未観測でもinstanceを保持する。元宣言・role・式・helper依存・位置は
`declaration()` に保持する。`source_law()` は式・guard・helperを含む元Lawのbyte列を持ち、
metadataの位置をこの入力へ結び付ける。`recheck()` は現在入力から構成を再実行し、元Lawも照合する。
このAPIは型付き実評価へ渡すinstanceを構成し、各式の評価にはその全域parameterと元入力を使う。

`construction::readings::evaluate_object_instance(shared, &instances, object_index, instance_index, &mut control)`
は現在の三入力でinstanceを再検査し、選択対象のLaw/viewを同じ型付き評価器で読む。
`ObjectEvaluation::outcome()` は適用外、原始slotの所属条件、型付き実評価を区別する。
baseの参照binderはrootとowned、部分対象ではそのsubjectへ制限し、外部helperと
複合scalarの参照leafは型全域を保つ。所属が補完されたcaseでは、その同じ代入で域を再構成する。
量化域の所属判断に使う既知owner Atomは、除外された候補も含めて支持とorigin/sourceを保持する。
実評価の `prepared().object_identity()/object_instance()` は対象identityと元の参照束縛を保持する。
Lawの残るparameterは既存の有限・アフィン全域族として評価する。値parameterを残すviewの関数族は
`ObjectEvaluationFailure::NotImplemented` に対象・元instance・全parameterを保持する。
これは実装経路の失敗であり、成立・反証・数学的未決とは区別する。

`construction::readings::evaluate_object_table(shared, &instances, &mut control)` は
objects順、instances順の全組を同じ評価器で評価する。`rows()` の各行は
`position()` と元の `evaluation()` を持ち、適用外・所属条件付き・未決も保持する。
`inputs()/shared_inputs()` は元の検査済み三入力とその共有参照を返し、空族でも保持する。
`is_complete()` は全行の処理完了、`pending()` は次の行位置を返す。
これはLawの成立や代数の構成成功とは別の完了状態である。
`ObjectEvaluationTableFailure::cause()/position()` は原因と評価中の行、
`partial()` は以前の完成行、`active()` は停止中の行の既存DAGを返す。
単一行の失敗が部分DAGを持つ場合は `cause()` 内の元の失敗に保持する。
最後の停止は全完成行を保持し、`recheck()` は現在入力から表全体を再計算して照合する。

## 仕様

- [I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md): 入力・問い・型付き結果の形式と意味。
- [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md): コマンド構文、出力、終了コード。
- [計算仕様](../../docs/tool/archsig_v0_6_0_io/computations.md): 対象・写像・診断・修復の構成と決定範囲。

## テスト

クレート内の小さい試験を exact 名で一件ずつ実行する。入力検査と
上の Rust API 例に対応する試験は次のとおり。

```bash
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test cli normative_examples_complete_both_checks -- --exact --test-threads=1
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test observed_counter_evaluation counter_two_has_typed_ordered_complete_answers -- --exact --test-threads=1
```

他の試験は `--test TARGET NAME -- --exact --test-threads=1` で対象を指定する。
`tests/fixtures/` の規範例は [適合例](../../docs/tool/archsig_v0_6_0_io/validation.md)の
`examples/` と同じ byte 列を保持し、テスト入力はクレート内の fixture を使う。
