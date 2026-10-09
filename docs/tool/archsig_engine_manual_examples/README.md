# ArchSig の入出力例

ArchMap と Law の二つを入力に使い、expected/ の JSON と結果を照合できる。
以下の製品 CLI の呼出形式は、このディレクトリをカレントディレクトリとして使う。
expected/ は入力に含めない。再実行するときは、新しい出力先を指定する。

## ゲーム操作と記録形式

同じルールでプレイ・観戦・リプレイを動かすため、入力機器や視点から独立した操作仕様を求める。
Law を先に固定し、原始の一手の作用から同値類と作用表を構成する。
記録候補の式を入力し、その十分性を別に判定する。

| 完全な ArchMap | 完全な Law | 完全な result.json |
| --- | --- | --- |
| [ゲームの原始項・使用関係](game/game.archmap.json) | [有限作用と記録の Law](game/game.law.json) | [7類・作用表・候補の判定と反例](game/expected/result.json) |

~~~sh
archsig engine run --archmap game/game.archmap.json --law game/game.law.json --out out/game
~~~

[ソースコード](game/game.py)、[役割束縛と補助計算](game/README.md)、
[標準解像度・因子化の検証資料](game/verification.md)がある。
二入力だけの再計算と、同じ Law のまま参照 ID を改名する検査を実行できる。

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
