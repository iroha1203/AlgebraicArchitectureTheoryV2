# 有限の変更範囲比較

[Saleorの既存記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6163#issuecomment-6680390970)
の「taskのみ・paymentまででは解なし、共有部分を含めると代替案が残る」という問いを、
6個のBoolへ移した小さい適合例。Saleorの972候補や実ソースの観測入力ではない。

x / y / zをtask / payment / 共有部分の変更座標へ対応させ、a / b / cは常時変更可能とする。
全基準値はfalse、元changeのparameterは各instanceにつきBool一つ。
Lawはx=true、x=y、y=zを要求する。許可範囲{x} / {x,y} / {x,y,z}の解数は0 / 0 / 8。
`independent.asks` は同じ固定条件を別々のLawで指定し、既存solveで独立に解く。
`shared.asks` は同じ条件を一つのRepairProblemと範囲への固定で解く。
両経路とも番号0の元Assignmentを選び、適用後に元Lawをcheckする。

入力と期待値の整備は共通であり、基準側の候補や局所関係を手書きしない。
両経路とも最初の4問でinternalと範囲の型付き値を読み、提示した許可範囲を確認する。
独立側では各Lawが同じ固定条件を指定し、共有側ではその範囲値を共通問題へ渡す。
共有側には一つのRepairProblemを準備する問いが加わる。独立側の3回のsolve内の準備と、
共有側のprepare一回＋3回の範囲選択は、同じ3判断を得る二つの経路として比較する。
候補選択と適用は両経路で同じ公開操作を使い、既存solve結果からの選択では有限結果への接続も含む。
時間と保持量に加え、この追加の仕事と保存出力の違いを記録する。

リポジトリ根から一経路を実行する例（zsh、`name`を切り替える）:

```zsh
cargo build --offline --release --manifest-path tools/archsig_v0.6.0/Cargo.toml -p archsig
fixture=tools/archsig_v0.6.0/tests/fixtures/shared-repair-saleor
name=shared
args=(run --atom-definition "$fixture/definition.json" --archmap "$fixture/input.archmap.json" --law "$fixture/input.law" --out "/tmp/archsig-shared-repair-$name")
while IFS= read -r ask; do args+=(--ask "$ask"); done < "$fixture/$name.asks"
/usr/bin/time -l -p tools/archsig_v0.6.0/target/release/archsig "${args[@]}"
```

既存の出力先を使い回さず、外側から180秒で停止する条件で比較する。
実時間、user+sys CPU、最大RSS、保存result.jsonのbyte数を分けて記録する。
計数を加えたテスト実行は通常binaryの測定へ混ぜない。実測は実装Issue / PRに置く。
