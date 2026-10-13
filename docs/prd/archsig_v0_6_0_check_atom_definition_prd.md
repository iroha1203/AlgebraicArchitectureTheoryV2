# ArchSig v0.6.0 共通 Atom 定義 I/O への check/version 適合 PRD

## 問い

既存の `check/version` を、Atom 定義が語彙・型・meaning を所有し、複数の Law と
ArchMap が同じ定義を参照する I/O に適合させられるか。観測語彙を安定させ、
未使用のライブラリも保持したまま、型・明示参照の不整合を元の入力位置で確認できることを目指す。

## 基準と位置づけ

一次仕様は [I/O 仕様](../tool/archsig_v0_6_0_io/README.md)の `check/version` に関わる規定とする。
調査基準は [PR #5346](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5346) の
merge commit `53f340116aa1449c23d193cd02a455171c18f54e`。
構成の補助資料は [エンジン設計](../tool/archsig_atom_law_engine/README.md)と
[設計判断](../tool/archsig_atom_law_engine/decisions.md)であり、その設計記法を入力構文へ追加しない。

これは [check/version の完成実装](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5338)
への後続改修である。完了済みの作業の要求・履歴を上書きせず、
[PR #5343](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5343) と
[PR #5345](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/5345) の責務分離を利用する。
以下は仕様への実装受入条件であり、schema や状態規則の新たな定義を置かない。

## 対象と入出力の変更

対象は `tools/archsig_v0.6.0` の入力読込み、名前解決、binding、静的検査、内部表現、
serializer、関連する小さいテスト・fixture・README とする。利用経路は
[実行仕様 §1](../tool/archsig_v0_6_0_io/execution.md#1-コマンド)の次の範囲である。

```text
archsig check --atom-definition D [--atom-definition D ...] --law L --out OUT
archsig check --atom-definition D [--atom-definition D ...] --law L --archmap A --out OUT
archsig version
```

| 入出力 | 現行から適合させる内容 | 規範参照 |
| --- | --- | --- |
| Atom 定義 | `archsig.atom-definition/1` の独立 JSON を一件以上読む。全ファイルの namespace 登録表で version・digest・依存を照合する | [定義 §§1–4](../tool/archsig_v0_6_0_io/definitions.md) |
| Law | `archsig.law/2` と `use vocabulary`。原始宣言を定義から共有し、reading は参照・条件・読みを所有する | [Law §§1–4](../tool/archsig_v0_6_0_io/law.md) |
| ArchMap | `archsig.archmap/2`。reading/digest binding を namespace/version/digest へ変更し、共通定義に照合する | [入力 §§2–5](../tool/archsig_v0_6_0_io/inputs.md) |
| 結果と位置 | `archsig.result/2`、`InputIdentity.id`、`definitionN`、定義コピー、manifest の location、reading の import 一覧を出す。原始宣言は定義の JSON Pointer、Law は元 byte span を指す | [結果 §1](../tool/archsig_v0_6_0_io/results.md#1-resultjson)、[実行 §§5–7](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力) |
| 版と receipt | semantics は `archsig/0.6.0`、receipt は `archsig.receipt/1`、version の一行出力を保つ | [入力 §1](../tool/archsig_v0_6_0_io/inputs.md#1-ファイルと版)、[実行 §5](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力) |

既存 v0.6.0 の型・式・値の検査と出力処理を再利用する。v0.5.x 系の依存、呼出し、
ソース共有、移植・コピー、fixture・期待値の流用、互換機能は導入しない。
旧 v0.6.0 の /1 入力や Law 内の原始宣言を受理する互換経路も作らず、現行仕様に従って拒否する。

対象外はエンジン全体、`run` の問い解決・評価・計算算法、solver、repair、結果再利用、
コード観測 PoC、Formal 移植、配布・CI の追加である。提供範囲は引き続き `check/version` とする。
構造・realization・写像の生成と検証は処理系の責務に置き、Law 作者への配線要求や
AAT の追加定理義務を本改修の条件にしない。

`reading/to_reading` は [実行仕様 §3](../tool/archsig_v0_6_0_io/execution.md#3-固定の12の問い)と
[構成仕様 §1](../tool/archsig_v0_6_0_io/computations.md#1-対象作用law-instance)の `run map` の選択である。
本改修は各 reading の import、宣言の kind・署名・role・guard・原式・出現を保持する。
reading 間の宣言対応や保存を `check` の入力受理条件にせず、選択・既定の `to_reading`・
実対応と保存判定の生成は後続 `run` に残す。

## 現状診断と実装の割当て

既存ソースは `tools/archsig_v0.6.0/src/` 以下、tests と README は同クレート直下。
新規 module 名は実装時に調整できる。

| 区分・ファイル | 確認した現状と必要な変更 | 対応 AC |
| --- | --- | --- |
| 再利用・接続: [json.rs](../../tools/archsig_v0.6.0/src/json.rs)、[canonical.rs](../../tools/archsig_v0.6.0/src/canonical.rs)、[types.rs](../../tools/archsig_v0.6.0/src/types.rs)、`prime.rs` | JSON 構文検査・canonical JSON/SHA-256・型表現・素数検査を再利用する。JSON のエラー位置は現在 ArchMap 固定なので、定義の入力 ID にも接続する。定義の JSON Type 読込みを追加する | AC2・5・6 |
| 新規・移設: `src/definition/` 等、[law/check.rs](../../tools/archsig_v0.6.0/src/law/check.rs)、[law/model.rs](../../tools/archsig_v0.6.0/src/law/model.rs) | 独立定義 reader、namespace 登録、依存 DAG、binding、meaning と定義位置を持つ原始定義表、manifest/digest を追加する。既存 `check_primitives` の owner・arrow・correspondence/align・data 再帰・ground value・型適格性の検査を共通定義側へ接続する。Law AST と span への依存を外す | AC2・3・6 |
| 接続: [law/parser.rs](../../tools/archsig_v0.6.0/src/law/parser.rs)、`law/ast.rs`、`law/check.rs` | 現在は reading 内の原始宣言と `use Other as O` を読む。/2 header、`use vocabulary` と予約語、直接 import の scope、短名の曖昧性、定義と Law の完全名の衝突検査へ変更する。namespace と reading を区別し、同名の namespace を reading 間依存と誤認しない | AC1–3 |
| 再利用・接続: [law/mod.rs](../../tools/archsig_v0.6.0/src/law/mod.rs)、`law/body.rs`、`law/expr.rs`、[law/metadata.rs](../../tools/archsig_v0.6.0/src/law/metadata.rs) | `CheckedLaw` は原始署名も持ち、`metadata::vocabularies` が reading ごとに manifest を生成する。式 arena・型・各出現・純粋性・構造再帰の検査は使い、原始型 lookup と constructor lookup を共通表へ接続する。manifest の生成元を定義へ移し、Law metadata に直接 import を保持する | AC2・3・5・7 |
| 接続: [archmap/mod.rs](../../tools/archsig_v0.6.0/src/archmap/mod.rs)、`archmap/schema.rs`、`archmap/model.rs`、`archmap/canonical.rs` | 現在の binding は reading/digest、必要集合は `required_readings` が `CheckedLaw.declarations` から求める。namespace/version/digest と原始定義表へ変更し、subject/field 型の推移参照で必要な binding を求める。Law が import しない語彙も ArchMap から使えるようにする | AC4・6 |
| 再利用・接続: [archmap/value.rs](../../tools/archsig_v0.6.0/src/archmap/value.rs)、`archmap/complete.rs`、`law/mod.rs::check_term_body` | 値・欠測 slot・snapshot・由来・有限構造の補完検査を使い、原始署名を読む先を変更する。観測 Term は現在 field 所属宣言の reading を使うため、定義元 namespace とその依存に基づく scope へ変更する | AC4・7 |
| 接続: [run/args.rs](../../tools/archsig_v0.6.0/src/run/args.rs)、[run.rs](../../tools/archsig_v0.6.0/src/run.rs) | `CheckArgs` は Law/ArchMap のみ。反復定義の指定順と開始時 byte 列を保持し、全入力の読込み後、定義→Law→ArchMap の検査へ接続する。定義と Law の完了を両結果表の公開条件にする | AC1・2・5・8 |
| 再利用・接続: [issue.rs](../../tools/archsig_v0.6.0/src/issue.rs)、[result.rs](../../tools/archsig_v0.6.0/src/result.rs)、[run/output.rs](../../tools/archsig_v0.6.0/src/run/output.rs) | `Location` は Law/ArchMap の二択、宣言 metadata は Law span 固定、InputIdentity に id がなく path も固定文字列。定義 ID・Pointer・動的コピー先、/2 serializer と整列規則へ拡張する。`Io`/`Signals`、状態確定・非上書き公開・receipt の処理を再利用する | AC5・8 |
| 更新・追加: [tests](../../tools/archsig_v0.6.0/tests/)、[README](../../tools/archsig_v0.6.0/README.md) | 既存 fixture と helper は /1 と Law 内原始宣言を使う。/2 と独立定義へ適合させ、小さい既存 assertion を保持・再配置する。Counter と未使用ライブラリの fixture を追加し、利用手順を更新する | AC1–8 |

内部では [結果仕様 §1](../tool/archsig_v0_6_0_io/results.md#1-resultjson)の原始定義表・Law 表・
観測表を別々に保持し、同じ原始型を reading ごとに複製しない。解決済み表をメモリ上で
後続処理へ渡せるようにし、表示用 JSON からの復元や外部 IR 再入力は導入しない。

## Acceptance Criteria

以下は実装完了の条件であり、今回の文書作成で実装済みとはしない。
正負例の期待値は各規範参照から定める。規範例は新しい仕様の byte 列をクレート内 fixture に置き、
runtime test が docs や旧版を読み込む構成にしない。

1. **AC1: 新しい利用経路。** [最小の一周](../tool/archsig_v0_6_0_io/validation.md#最小の一周)の
   Counter、既存の Reservations/Engine を、定義＋Law、定義＋Law＋ArchMap の両経路で
   `complete/0` とする。`version` は規定の一行 JSON と exit 0 を保つ。
   必須定義なし・未知 flag・単数 flag の重複は `usage/invalid/64`。
   /1 の Law/ArchMap は未知版、/2 Law 内の原始宣言は構文不正として扱い、互換変換しない。
2. **AC2: 定義の登録と検査。** [定義仕様](../tool/archsig_v0_6_0_io/definitions.md)の
   schema、名前、原始型・所属・align・data の検査、全 dependency の解決を行う。
   同一 namespace は内容が同じでも二重登録を拒否する。依存循環は digest 照合に先立ち検出する。
   未使用の定義・語彙・import・dependency・宣言だけを理由に拒否・issue 生成しない。
   一方、未使用 dependency も登録先・version・digest を照合する。
   空宣言の語彙も受理し、CLI が明示したファイル群だけで解決する。
3. **AC3: 共通語彙と Law の scope。** [Law §§1–4](../tool/archsig_v0_6_0_io/law.md)に従い、
   Counter を使う二つの reading の `State` を同じ `Counter.State` へ解決する。
   直接名指す原始 namespace は完全名の場合も直接 import を要求し、署名をたどるための
   間接依存だけなら定義の依存表を使う。未使用 import も照合・保持する。
   同名の namespace/reading を許し、完全名衝突は `duplicate_id`、曖昧な短名は `reference`。
   束縛射影・alias・最長一致、constructor、全 Law 宣言・分岐の型・再帰・純粋性の検査を保つ。
4. **AC4: ArchMap と観測 Term。** [入力 §§3–5](../tool/archsig_v0_6_0_io/inputs.md)に従い、
   subject 型と field 型から推移的に必要な namespace の binding を検査する。
   必要な binding 欠落は `/vocabularies` の `vocabulary_mismatch`、未登録先は `reference`、
   登録済みの版・digest 不一致は `vocabulary_mismatch`。余分な binding も正しければ受理する。
   Law から未参照の語彙だけを使う ArchMap も検査できる。観測 Term は定義元の短名、
   依存 namespace の完全名で解決し、Law view・reading alias への依存を許さない。
   既存の値・参照・由来・Map 全域性と補完検査を共通定義に接続する。
5. **AC5: 出力の追跡と保持。** [結果 §1](../tool/archsig_v0_6_0_io/results.md#1-resultjson)の
   全 check 出力を /2 に揃える。定義は kind=`atom_definition` とし、指定順に `definition0` 等を割り当て、
   `inputs/definitions/0.json` 等へ開始時 byte 列をコピーし、inputs は id の辞書順にする。
   manifest、原始宣言・constructor・型/align 参照・既定対応は該当定義の Pointer へ戻り、
   Law の宣言・式・参照は元 span へ戻る。reading の `vocabularies` は直接 import を
   namespace 順に持ち、他の宣言では空にする。未使用情報も全 manifest・宣言とコピーに保持する。
   定義/Law が検査未完了なら両表は空、完了後の ArchMap 不正では両表を保持する。
   成否によらず requests/answers/nodes は空。ArchMap 省略時は inputs にその項目を作らない。
6. **AC6: digest と identity。** [定義 §3](../tool/archsig_v0_6_0_io/definitions.md#3-依存参照digest)と
   [実行 §7](../tool/archsig_v0_6_0_io/execution.md#7-版正規化再利用)の正規化を適用する。
   meaning・version・未使用 dependency を含めた manifest digest、定義ファイルの model_digest、
   Law の字句列 digest、各入力の bytes_digest を区別する。Counter の固定 digest は規範例と一致する。
   ファイル分割・定義の指定順・集合表順の変更は語彙 digest を変えず、元の入力位置は保つ。
   Law の条件だけの変更は語彙 digest を変えない。definition の meaning・版・dependency の変更は
   語彙 digest に反映し、古い binding を不一致とする。順序を持つ field/parameter/constructor/argument、
   List と文字列は仕様どおり保持する。
7. **AC7: 静的検査と後続計算の分担。** Counter の count=12 と count 欠測も check は成功する。
   欠測は型付き slot のまま保持し、存在しない subject を生成せず、零・空・none で埋めない。
   [Before/After とその変種](../tool/archsig_v0_6_0_io/validation.md#reading-間の宣言対応)も
   個々の宣言が有効なら受理する。共通原始型を保持しつつ各 reading の署名・role・原式を分離する。
   非アフィン式・無限量化・未使用宣言も型が正しければ受理し、全宣言の評価や全語彙の観測を要求しない。
   型の正しい端点不保存 Map や偽となる Law を不正入力にせず、成立・反証・構造生成は行わない。
8. **AC8: エラーと軽量な回帰確認。** [実行 §§5–7](../tool/archsig_v0_6_0_io/execution.md#5-ファイル操作と出力)と
   [IssueCode](../tool/archsig_v0_6_0_io/results.md#6-証拠と理由)に従い、定義→Law→ArchMap の検査順を保つ。
   JSON は構文→版→対応 schema→型・参照、Law は UTF-8/header の版→残りの字句・文法→型・参照とする。
   未知版の新しい欄を
   未知欄エラーで先に拒否しない。新しい位置と入力コピーでも result/receipt/終了コードが整合する。
   読めない定義の unread、読めた入力コピー、検査開始前の I/O 失敗、内部障害時の入力非保持を確認する。
   既存の `Io`/`FakeSignals` による小さい検証で非上書き公開と finalize の状態確定を保ち、
   README の二つの check 手順を独立定義付きへ更新する。

## 小さい受入例と検証範囲

| 例・一箇所ずつの変種 | 確認する期待結果 | AC |
| --- | --- | --- |
| [Counter](../tool/archsig_v0_6_0_io/examples/counter.atoms.json)、[Law](../tool/archsig_v0_6_0_io/examples/counter.law)、[ArchMap](../tool/archsig_v0_6_0_io/examples/counter.archmap.json) | 共通原始宣言一件、二 reading の import と同じ型。count=2/12/欠測を check が受理し、評価結果を出さない | 1・3・5・7 |
| [Counter ライブラリ](../tool/archsig_v0_6_0_io/examples/counter-library.atoms.json)を一ファイル、次に二ファイルに分割して逆順指定 | Extras.Note と未使用 dependency を保持して成功。Counter の語彙 digest は基本例と同じで、定義ファイルの model_digest は包装に応じて変わる。明示ファイル外の探索なし | 2・5・6 |
| 同ライブラリに、未使用 Extras import／余分な ArchMap binding／Extras だけの小さい観測を個別追加 | 正しい参照は受理。Extras の全 field や、Law の全宣言に対応する観測を追加要求しない | 2–4 |
| dependency・import・ArchMap binding の登録先、版、digest を個別に誤らせる | 未登録は reference、版・digest 不一致は vocabulary_mismatch。未使用 dependency にも同じ判定 | 2–4・8 |
| 重複 namespace、自己 dependency、二 namespace の循環、空 meaning/version、未知キー meanng、原始型不整合 | duplicate_id、cycle、syntax、type 等を規範位置で返す。循環例の不一致 digest より cycle を優先 | 2・5・8 |
| 二語彙に同じ短名 State／Law に直接 import のない完全名／同名 namespace と reading | 曖昧な短名と直接 import 欠落を拒否し、完全名で一意に解決できる正例と衝突のない同名例を受理 | 3 |
| 定義元の data constructor と依存先の constructor を呼ぶ小さい観測 Term | 定義元の短名と依存先の完全名は受理。依存先の短名・Law view 呼出しは拒否 | 4 |
| 定義、Law、ArchMap の順に一つずつ不正化／未知版に未知欄を追加／第二定義だけ読込み不可 | 正しい入力 ID・Pointer/span・status/exit、両表の空/保持、unread とコピーの対応 | 5・8 |
| Reservations/Engine と既存の小さい値・metadata・digest ケース | Owned/align/data・構造再帰・欠測・由来・原式の保持を新しい接続でも確認 | 1・3–7 |

実装時の検証は、`tests/law_resolution.rs`、`law_digest.rs`、`archmap_values.rs`、
`archmap_reservations.rs`、`cli.rs`、`cli_rejections.rs`、`cli_files.rs` 等の小さい既存ケースを
変更箇所に応じて選び、上表の新 I/O 差分を小さい fixture で補う。
試験名を個別指定し、同時には一件だけ、1 job / 1 thread で実行する。

```text
cargo test --offline --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1 --test TARGET NAME -- --exact --test-threads=1
```

本改修の完了条件に load measurement、full cargo test、並列 build/test、深い入力、巨大な
completion、実 process の signal/race/配送失敗など削除済みの負荷ケースとその代替負荷ケースを含めない。
小さい選択試験を削除済みの被覆や性能の証拠として扱わない。今回の PRD 作成は文書・リンク・
仕様対応・差分の検証までとし、runtime test や実装ループを実行しない。

## 実装順と停止条件

1. 共通の位置・binding・原始定義表と定義 reader を作り、既存の原始型検査を接続する。
2. Law の import・名前解決・metadata、ArchMap の binding・値・観測 Term を共通表へ接続する。
3. CLI・検査順・入力コピー・/2 serializer を接続し、規範 fixture、選択試験、README を揃える。

完了は AC1–8 の実装と、各 AC を覆う上記の軽量検証で判定する。
意味の縮小、未使用情報の拒否・破棄、追加の入力モード、仕様にない制限によって AC を満たしたことにしない。
規範仕様間に重要な矛盾が見つかった場合は、該当箇所と影響する AC を示して当該部分を停止・報告し、
PRD や実装の判断だけで規範を変更しない。
