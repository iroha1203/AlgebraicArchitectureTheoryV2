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
| `archsig-common` | 型・名前・JSON・canonical表現・診断・中断制御 | `src/common_lib.rs` |
| `archsig-input` | 定義・Law・ArchMapの検査、入力と結果の共通表示 | `src/input_lib.rs` |
| `archsig-computation` | construction・observedとowner補完 | `src/computation_lib.rs` |
| `archsig` | run・main、既存ライブラリ経路のre-export | `src/lib.rs`、`src/main.rs` |

各packageのmanifestは`crates/`にあり、ソースは既存の`src/`配置を保持します。
各モジュールは担当crateで一度だけコンパイルします。統合テストの
`archsig::archmap`などの経路はCLI packageのre-exportで維持します。
検査済み入力は共有参照のgetterで読み取り、上位crateから構築・更新できません。

workspaceの`default-members`は4 packageすべてです。既存のmanifest指定の
`cargo test`とCIのnextest partitionで、各crateのunit testとCLIの統合テストを実行します。
`-p archsig`だけでは下位crateのunit testを実行しません。
`cargo test --doc --workspace --manifest-path tools/archsig_v0.6.0/Cargo.toml`で
入力の不変性を含むdoctestを検査できます。

`test-support` featureはdev-dependencyだけから有効にし、停止しない制御と既存の
最終検算失敗の注入をcrate間テストへ提供します。通常のbuildでは無効です。
ビルド速度の改善はこの分割の目的ではありません。

## 実行

Atom 定義・Law・ArchMap を検査します。`--out` には、既存ディレクトリの下にある
未使用のパスを指定してください。

```bash
archsig check --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json --out result-check
```

`run` では、値を読む問いと要求を確かめる問いをまとめて渡せます。

```bash
archsig run --atom-definition tools/archsig_v0.6.0/tests/fixtures/counter.atoms.json \
  --law tools/archsig_v0.6.0/tests/fixtures/counter.law \
  --archmap tools/archsig_v0.6.0/tests/fixtures/counter.archmap.json \
  --ask 'n=evaluate(CountCheck.amount,s=@v/s)' \
  --ask 'ok=check(CountCheck.nonnegative,s=@v/s)' \
  --ask 'audit=check(CountAudit.bounded,s=@v/s)' --out result-counter
```

## 結果を読む

標準出力に一行の receipt、指定したディレクトリに `result.json` と入力コピーを保存します。
回答は `answers`、型と根拠を持つ値は `nodes` にあり、回答の `outputs` から参照できます。
次の表示例は `jq` を使用します。

```bash
jq '.answers[] | {id, status}' result-counter/result.json
jq -r '. as $r | .answers[] | select(.id == "n") | .outputs.value.node as $id
  | $r.nodes[] | select(.id == $id) | .value' result-counter/result.json
```

この例は3件とも `established`、値は2、終了コードは0です。
要求が成り立たない回答は `refuted`、入力から決まらない回答は `undetermined` と理由を返します。
実行失敗は標準出力の具体的なエラーと終了コードで確認できます。
終了コードと中断時の扱いは実行仕様を参照してください。

## 仕様

- [I/O 仕様](../../docs/tool/archsig_v0_6_0_io/README.md): Atom 定義・Law・ArchMap と問いの全体像。
- [実行仕様](../../docs/tool/archsig_v0_6_0_io/execution.md): コマンド、問い、出力と終了コード。
- [型付き結果](../../docs/tool/archsig_v0_6_0_io/results.md): 回答、値、根拠と入力の元位置。
