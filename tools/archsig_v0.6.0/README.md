# ArchSig v0.6.0

共通の Atom 定義を参照する Law・ArchMap から、観測した値と設計上の要求の
成立・反証・未決を計算する CLI ツールです。結果から型、根拠、入力の元位置を確認できます。

## ビルド

リポジトリルートで実行します。Rust 2024 edition 対応のツールチェーンを使用してください。

```bash
cargo build --manifest-path tools/archsig_v0.6.0/Cargo.toml -j 1
export PATH="$PWD/tools/archsig_v0.6.0/target/debug:$PATH"
archsig version
```

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
