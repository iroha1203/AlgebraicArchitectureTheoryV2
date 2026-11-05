# 未決のmapと確認済みOperation

`map(kind=object_algebra)` が完全なObjectAlgebraMapを生成できなくても、
baseのconfiguration保存を確認済みなら `outputs.operation` を保持する場合がある。
回答全体の `status` と、実際に生成された各outputを分けて読む例である。

## 三つの表現を対応づける

同梱の [Atom定義](transfer.atoms.json)、[Law](transfer.law)、
[ArchMap](transfer.archmap.json) は架空の仕様モデルで、実OSSの観測や実測ではない。
二つの名前付き座標を持つ表現 `old`、`owned`、`adapter` を一つのsnapshot `v` に置く。
各表現の `coordinates` はその表現のX、Yへの順序付き参照、座標の `name` はx、y。
対応 `extract` はold→owned、`adapt` はowned→adapter、`direct` はold→adapterで、
いずれもXをX、YをYへ写す。存在、owner、列、名前、対応を原始値として記録している。

`Representation.coordinateOwner` は列の各参照がそのStoreに所属することを要求する。
`TransferSafety.names` は元のownerに所属する座標全てについて、対応先との名前値の一致を
独立に要求する。configuration保存の成立だけから名前値の保存を結論しない。

`coordinates` の型 `List<Ref<Coord>>` は任意長の列を許す。
各入力値が長さ2でも、ObjectAlgebraの方程式表示に必要な全型域は二つの観測列に限られない。
この例では `finite_primitive_domain` の算法非対応となる。欠測を埋める操作では解決しない。
列をSetに変えたり、観測された長さだけへ型域を制限して成功扱いにしない。

## 同じrunで確認済みoutputを使う

`cli`、`skill`、`work` は [SKILLのバンドル指定](../SKILL.md#バンドルを使う)を使う。
`--out` には未存在のディレクトリを指定する。

```sh
"$cli" run \
  --atom-definition "$skill/assets/transfer.atoms.json" \
  --law "$skill/assets/transfer.law" \
  --archmap "$skill/assets/transfer.archmap.json" \
  --ask 'm=map(TransferModel.Transfer,on=@v/extract,reading=Representation,kind=object_algebra)' \
  --ask 'n=map(TransferModel.Transfer,on=@v/adapt,reading=Representation,kind=object_algebra)' \
  --ask 'd=map(TransferModel.Transfer,on=@v/direct,reading=Representation,kind=object_algebra)' \
  --ask 'c=compose($m.operation,then=$n.operation)' \
  --ask 'same=compare($c.operation,to=$d.operation,kind=action)' \
  --ask 'word=compare($c.operation,to=$d.operation,kind=word)' \
  --ask 'extractNames=check(TransferSafety.names,bind.t=@v/extract)' \
  --ask 'adaptNames=check(TransferSafety.names,bind.t=@v/adapt)' \
  --ask 'directNames=check(TransferSafety.names,bind.t=@v/direct)' \
  --out "$work/transfer-run"
```

| 問い | status | 確認する内容 |
| --- | --- | --- |
| m / n / d | undetermined | `outputs.operation` とcandidateあり、`outputs.map`なし。理由は `unsupported_algorithm`、methodは `finite_primitive_domain`、型は `List<Ref<TransferModel.Coord>>` |
| c | established | 端点の合う二つのOperationの合成。operationとconfiguration mapを生成 |
| same | established | 合成と直接対応のU全域での作用が一致 |
| word | refuted | `[extract, adapt]` と `[direct]` は異なる名前付き操作列 |
| 三つのNames | established | 各対応で名前値の一致を独立に確認 |

全体は未決を含むので終了2。後続の成立でm/n/dの未決を上書きしない。
summaryの `answers` をIDで読み、`outputs` の存在と `reasons` を確認する。
保存resultではOperationのRefから `configuration_map` とその保存条件へたどれる。
例の `$m.operation` 等は、未決回答に保持された確認済み出力を選択している。
未生成の `$m.map` を仮定して使わない。configuration保存自体を反証された場合は
Operationも生成されず、これを読む後続は `dependency_blocked` となる。

Uは全入力snapshotのsubject存在事実と既知field Atomからなる有限のcarrier。
ここでのaction比較は、同じ三入力・readingから作ったU上の総作用を比較する。
名前値の一致、完全なObjectAlgebraMapの存在、実プログラム全体の同値、
実行時の共有・copy・更新挙動は、それぞれ別の問いと証拠を要する。

## 二つの負例を分ける

同梱ArchMapを作業先へコピーし、以下をそれぞれ元入力から一箇所だけ変更して、
上のコマンドの `--archmap` と未存在の `--out` を差し替えて実行する。

| 変更するAtom id | 変更 | 期待する区別 |
| --- | --- | --- |
| `adapterX.name` | 値を `"changed"` にする | configurationのOperation、compose、action一致は保持される。adaptNames/directNamesがrefuted、extractNamesはestablished。完全mapの未決は残る |
| `adapter.coordinates` | 値を `[["v","adapterY"],["v","adapterX"]]` にする | 元の座標対応は変更しない。n/dのconfiguration保存がrefutedとなりOperationなし。c/same/wordはdependency_blocked。Namesは全てestablished |

どちらも全体の終了は2である。後者でもmのObjectAlgebraMapは未決のまま残る。
順序を変えてもowner条件と名前値は満たせるが、Listの参照像は順序・重複を保つため、
固定した対応候補はconfiguration保存で拒否される。列の順序検査を名前保存Lawの役割へ移さない。

実ソースへ適用するときは、各表現、変換の対応、Listの順序、名前の受渡しを根拠へ戻す。
この有限モデルの成立を、任意データ・全更新経路の保存へ広げない。
実行テストやruntime witnessは、実装観測Atomと分けて報告する。
