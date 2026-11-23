# ArchSig v0.6.0

## リリース状況

度重なる実行時の審査の誤判定により、作業の進行が難しいため、ArchSig v0.6.0のリリースは差し止めする。

共通の Atom 定義を参照する Law・ArchMap から、観測した値と設計上の要求の
成立・反証・未決を計算する CLI ツールです。結果から型、根拠、入力の元位置を確認できます。

## ビルド

リポジトリルートで実行します。Rust 2024 edition 対応のツールチェーンを使用してください。

```bash
cargo build --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
export PATH="$PWD/tools/archsig_v0.6.0/target/debug:$PATH"
archsig version
```

## 開発時のクレート構成

Cargo workspaceは次の順に依存します。下位から上位への依存はありません。

| package | 担当 | entry point |
| --- | --- | --- |
| `archsig-common` | 型・名前・JSON・canonical表現・診断・中断制御 | `crates/common/src/lib.rs` |
| `archsig-input` | 定義・Law・ArchMapの検査、入力と結果の共通表示 | `crates/input/src/lib.rs` |
| `archsig-computation` | construction・observedとowner補完 | `crates/computation/src/lib.rs` |
| `archsig-shigure` | SHIGURE 原始表示 IR・多項式/構成可能集合計算核・保存/解空間/相互作用/図式/経路/移送/頑健性/Chevalley 分類/追加観測エンジン・入力変換層 | `crates/shigure/src/lib.rs` |
| `archsig` | run・main | `src/lib.rs`、`src/main.rs` |

下位4 packageのmanifestとソースはそれぞれ`crates/<名前>/`に置きます。
依存の向きは `archsig-common` → `archsig-input` → `archsig-computation` / `archsig-shigure` → `archsig` であり、
`archsig-shigure` は `crates/computation/src/observed/` へ依存しません。
各モジュールは担当crateで一度だけコンパイルします。統合テストも
`archsig_input::archmap`、`archsig_computation::observed`、`archsig_shigure::solver` など所有crateを直接参照し、
CLI packageから下位モジュールを再公開しません。
検査済み入力は共有参照のgetterで読み取り、上位crateから構築・更新できません。

workspaceの`default-members`は5 packageすべてです。既存のmanifest指定の
`cargo test`とCIのnextest partitionで、各crateのunit testとCLIの統合テストを実行します。
`-p archsig`だけでは下位crateのunit testを実行しません。
`cargo test --doc --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml`で
入力の不変性を含むdoctestを検査できます。

`test-support` featureはdev-dependencyだけから有効にし、停止しない制御と既存の
最終検算失敗の注入をcrate間テストへ提供します。通常のbuildでは無効です。
ビルド速度の改善はこの分割の目的ではありません。

## 実行

`archsig --help`と`archsig help run`で引数と例を確認できます。

`run` では、値を読む問いと要求を確かめる問いをまとめて渡せます。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json \
  --ask 'n=evaluate(CountCheck.amount,s=@v/s)' \
  --ask 'ok=check(CountCheck.nonnegative,s=@v/s)' \
  --ask 'audit=check(CountAudit.bounded,s=@v/s)'
```

## 結果を読む

標準出力に一行のJSON summaryを返します。`answers`から値・状態・反例・未決理由を読めます。
次の表示例は`jq`を使用します。上のコマンドに`| jq '.answers[] | {id, status, outputs}'`を付けて確認できます。

全量の値と入力を保存する場合は、上のコマンドへ`--out result-counter`を追加します。
標準出力の回答と警告は同じまま、`result`欄に保存先が加わります。
保存先には既存ディレクトリの下の未使用パスを指定します。
`result-counter/result.json`の`answers`から、型付きの値を持つ`nodes`を参照できます。

検査だけなら次を繰り返し実行できます。保存する場合だけ`--out`を加えます。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json
```

上の `run` の例は3件とも `established`、値は2、終了コードは0です。
要求が成り立たない回答は `refuted`、入力から決まらない回答は `undetermined` と理由を返します。
実行失敗は標準エラー出力の機械可読JSONと終了コードで確認できます。
終了コードと中断時の扱いは実行仕様を参照してください。

### SHIGURE の実行例

SHIGURE 宣言を含む入力では、`shigure_preservation`・`shigure_solve`・`shigure_interaction`・
`shigure_diagram`・`shigure_path`・`shigure_transfer`・`shigure_robustness`・`shigure_chevalley`・
`shigure_observations` の 9 種別の問いを実行できます。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-ledger/ledger.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-ledger/ledger.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-ledger/ledger.archmap.json \
  --ask 'p6c=shigure_solve(LedgerMigration.P6cEditableBusy)' \
  --ask 'p6d=shigure_solve(LedgerMigration.P6dFixedOldBusy)'
```

この例では `p6c` が `established`（`rho = 1`・`finish` と Busy Law を復元し再評価一致）、
`p6d` が `refuted`（検算済み空性 witness 付き）となり、反証を含むため終了コードは 1 です。

図式補完・変更経路・合法状態移送は対応する問いで実行します。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/diagrams.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.archmap.json \
  --ask 'sq=shigure_diagram(DiagSuite.ForkSquareStateMap)'

archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/paths.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.archmap.json \
  --ask 'p51=shigure_path(PathSuite.LedgerP51Paths)' \
  --ask 'p52=shigure_path(PathSuite.LedgerP52ProtocolPaths)'

archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/transfers.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase2/phase2.archmap.json \
  --ask 'g3=shigure_transfer(TransferSuite.G3ThreeStepChain)' \
  --ask 'p53=shigure_transfer(TransferSuite.P53BusyRefuted)'
```

1 つ目の例は四角形補完（`k = "1"`, `established`, 終了コード 0）、
2 つ目の例は固定 protocol 間 4 順序と拡大 protocol 4 実行経路（両件 `established`, 終了コード 0）、
3 つ目の例は 3 段移送合成（`domain_relation = "full_isomorphic"`, `established`）と Busy 状態移送反証（`p53` が `refuted`, 終了コード 1）を返します。

複数解釈族の頑健性判定・Chevalley 四分類・包含極小の追加観測は次のように実行します。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/robustness.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.archmap.json \
  --ask 'ex=shigure_robustness(RobustnessSuite.ExistentialRob)' \
  --ask 'prov=shigure_robustness(RobustnessSuite.ProvenanceRob, snapshot=snap1)'

archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/chevalley.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.archmap.json \
  --ask 'four=shigure_chevalley(ChevalleySuite.FourRegionsChev)' \
  --ask 'w5=shigure_chevalley(ChevalleySuite.W5Chev)' \
  --ask 'w6=shigure_chevalley(ChevalleySuite.W6Chev)'

archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/observations.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.archmap.json \
  --ask 'w4=shigure_observations(ObsSuite.W4Obs)' \
  --ask 'nd=shigure_observations(ObsSuite.NoDiffObs)'

archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/silence.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/shigure-phase3/phase3.archmap.json \
  --ask 'miss=shigure_robustness(SilenceSuite.MissingObsRob, snapshot=snap_missing)' \
  --ask 'nl=shigure_robustness(SilenceSuite.NonlinearRob, snapshot=snap1)'
```

1 つ目の例は存在型 witness 復元（`w = "2"`, `reevaluation.matched = true`）と 4 種由来保持の頑健成立（両件 `established`, 終了コード 0）、
2 つ目の例は Chevalley 4 領域分類・有理 fiber probe / Laurent 障害・双対数全係数移送対照（全件 `established`, 終了コード 0）、
3 つ目の例は W4 の両包含極小集合（`["e1"]` と `["e2", "e3"]`）＋費用順位と差なし空集合解（両件 `established`, 終了コード 0）、
4 つ目の例は未観測座標依存（`unobserved_dependency`）と非線形有理点範囲外（`nonlinear_point_existence_out_of_scope`）を理由付き `undetermined`（`status = "partial"`, 終了コード 2）として返します。

## 仕様

- [I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md): Atom 定義・Law・ArchMap と問いの全体像。
- [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md): コマンド、問い、出力と終了コード。
- [型付き結果](../../docs/tool/archsig_v0_6_0_io/results.md): 回答、値、根拠と入力の元位置。

## 観測の補助

同梱の `skills/archsig-observe/SKILL.md` が使う根拠照合と有限表計算は、同じRust実行ファイルで完結します。利用時にPythonを要求しません。

```sh
archsig evidence --archmap observation.json --atom snapshot/atom --source code=source.rs
archsig law-fibers --table table.json
```

`evidence` は既存参照を辿り、ローカルファイルのSHA256・UTF-8 byte spanと抜粋を照合します。
`law-fibers` は完全列挙した有限表の等号から反例対・partition・descentを計算します。
両者の入力と出力、読解側の前提は[観測補助の実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md#8-観測補助)に従います。
結果は標準出力JSON、エラーは標準エラー出力JSONです。保存先の指定は不要です。
