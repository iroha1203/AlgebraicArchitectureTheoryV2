# ArchSig 0.6.0 候補バンドル

共通の Atom 定義を参照する Law・ArchMap から、観測した値と要求の成立・反証・未決を計算します。
このバンドルの CLI は `bin/archsig`、入力作成の手順と例は
[ArchSig Observe](skills/archsig-observe/SKILL.md)、利用仕様は [I/O 仕様](docs/io/README.md) にあります。
実行には同梱 CLI に対応する OS/CPU を使います。Rust・Python は利用時に不要です。

展開したディレクトリの絶対パスを `bundle` に指定してください。生成物は別の場所に保存します。

```sh
bundle='/path/to/extracted-bundle'
work='/path/to/new-output-directory'
mkdir -p "$work"
cli="$bundle/bin/archsig"
skill="$bundle/skills/archsig-observe"
"$cli" version
"$cli" check --atom-definition "$skill/assets/operation.atoms.json" \
  --law "$skill/assets/operation.law" --archmap "$skill/assets/operation.archmap.json" --out "$work/check"
"$cli" run --atom-definition "$skill/assets/operation.atoms.json" \
  --law "$skill/assets/operation.law" --archmap "$skill/assets/operation.archmap.json" \
  --ask 'v=evaluate(OperationReading.normalExit,bind.branch=@v/rejected)' \
  --ask 'c=check(OperationReading.guardedUpdate,bind.branch=@v/rejected)' \
  --ask 'n=needed($c)' --out "$work/run"
```

`version` の product は `archsig`、version は `0.6.0`、semantics は `archsig/0.6.0`。
同梱例の `run` は出口の値 false、要求成立、必要な欠測なしを返し、終了コードは0です。
自分の入力は SKILL の「問いから読解へ」「三入力の書き方」に従って作り、
根拠照合は同じ CLI の `evidence` を使います。詳細は [実行仕様](docs/io/execution.md#8-観測補助) にあります。

`PROVENANCE.txt` は source commit・tree、source archive と binary の SHA-256、
ツールチェーン、target、ビルド引数を記録します。`VERSION.json` は包装時の実行結果です。
候補 archive と併せて渡される `SHA256SUMS` で archive と `source.tar` を照合します。

```sh
shasum -a 256 -c SHA256SUMS
shasum -a 256 "$bundle/bin/archsig"
cat "$bundle/PROVENANCE.txt"
```

SHA-256 は手元の bytes と記録の対応を検査します。配布者の本人性は別途、記録の入手元で確認します。
