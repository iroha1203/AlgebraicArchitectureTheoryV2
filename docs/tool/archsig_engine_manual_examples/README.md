# ArchSig の入出力例

ArchMap と Law の二つを入力に使い、expected/ の JSON と結果を照合できる。
以下のコマンドは、このディレクトリをカレントディレクトリにして実行する。
expected/ は入力に含めない。再実行するときは、新しい出力先を指定する。

## 料金計算

[変更前のコード](checkout-before/checkout.py)と[変更後のコード](checkout-after/checkout.py)は、
quote_total の加算値400→300だけが異なる。入力は origin.kind = observation で、
全 Atom に実装コードの版・位置への参照が付いている。

| ケース | 完全な ArchMap | 完全な Law | 完全な result.json |
| --- | --- | --- | --- |
| 変更前 | [checkout-before](checkout-before.archmap.json) | [CheckoutTotals](checkout.law) | [反証：2300 ≠ 2400](expected/checkout-before.result.json) |
| 変更後 | [checkout-after](checkout-after.archmap.json) | [CheckoutTotals](checkout.law) | [成立：両経路とも2300](expected/checkout-after.result.json) |

~~~sh
archsig engine run --archmap checkout-before.archmap.json --law checkout.law --out out/checkout-before
archsig engine run --archmap checkout-after.archmap.json --law checkout.law --out out/checkout-after
~~~

subtotal=2000 は出力例の反例への代入である。Law は全ての有理数代入で二経路を比較する。
[コードから Atom・Law・出力を読む手順](../archsig_engine_manual.md#1-コードから観測する)を参照する。

## 三操作の座標と局所・大域

p→q の a は1、q→r の b は1を加える。p→r の c の加算値だけを変え、
paths で経路の等号、coordinates で座標の解集合、descent で局所状態の統合を調べる。

| ケース | 完全な ArchMap | 完全な Law | 完全な result.json |
| --- | --- | --- | --- |
| shift=3 | [triangle-3](triangle-3.archmap.json) | [Coordinates](coordinates.law) | [反証](expected/triangle-3.result.json) |
| shift=2 | [triangle-2](triangle-2.archmap.json) | [Coordinates](coordinates.law) | [成立と大域座標](expected/triangle-2.result.json) |
| shift 未観測 | [triangle-missing](triangle-missing.archmap.json) | [Coordinates](coordinates.law) | [情報不足と計算済みの幾何](expected/triangle-missing.result.json) |

~~~sh
archsig engine run --archmap triangle-3.archmap.json --law coordinates.law --out out/triangle-3
archsig engine run --archmap triangle-2.archmap.json --law coordinates.law --out out/triangle-2
archsig engine run --archmap triangle-missing.archmap.json --law coordinates.law --out out/triangle-missing
~~~

shift=3 は解なしの証人、shift=2 は全解 (h,h+1,h+2) と大域座標 (0,1,2) を返す。
未観測なら c を残したまま必要な shift を指す。H¹ の次元は全ケースで1、
具体的な障害座標は −1、0、未決となる。
[係数・微分・補正の導出](../archsig_atom_law_engine/local_global_example.md)も確認できる。

## コンパイル保存

source の式 ((x+1)+2)=0 と、二重加算をまとめる原始の書換え規則を入力する。
Law は、生成した IR の残差と source 残差が全 x∈Q で一致することを要求する。

| ケース | 完全な ArchMap | 完全な Law | 完全な result.json |
| --- | --- | --- | --- |
| add | [compiler-add](compiler-add.archmap.json) | [CompilerPreservation](compiler.law) | [保存成立](expected/compiler-add.result.json) |
| sub | [compiler-sub](compiler-sub.archmap.json) | [CompilerPreservation](compiler.law) | [反例](expected/compiler-sub.result.json) |
| 演算子未観測 | [compiler-missing](compiler-missing.archmap.json) | [CompilerPreservation](compiler.law) | [情報不足](expected/compiler-missing.result.json) |

~~~sh
archsig engine run --archmap compiler-add.archmap.json --law compiler.law --out out/compiler-add
archsig engine run --archmap compiler-sub.archmap.json --law compiler.law --out out/compiler-sub
archsig engine run --archmap compiler-missing.archmap.json --law compiler.law --out out/compiler-missing
~~~

add は残差 x+3 を保存する。sub は IR 残差 x−1 を生成し、差 −4 と反例 x=1 を返す。
演算子が未観測なら、source 残差は計算し、IR と比較結果を未決にする。
[式・規則と比較の意味](../archsig_atom_law_engine/compiler_preservation_example.md)を参照する。

各期待出力の inputs は、対応する入力ファイルの SHA-256 を記録している。
入力を変えたら再計算し、[書式と結果の比較方法](../archsig_engine_reference.md)に従って読む。
