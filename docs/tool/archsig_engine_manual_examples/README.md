# ArchSig の入出力例

各例は、原始事実を記録した ArchMap と規則・問いを記述した Law の二つを入力に使う。
`*.archmap.json` と `.law` が入力ファイル、`expected/*.result.json` が対応する出力例である。

[分析別のコマンド](../archsig_engine_manual.md#6-分析別の使い方)は、このディレクトリを
カレントディレクトリにして実行する。`expected/` のファイルは入力に含めない。
出力の表示順・基底・特解・反例が例と異なる場合は、
[計算結果の比較](../archsig_engine_manual.md#8-計算結果を比較する)で意味の一致を確かめる。

| 分析 | 完全な ArchMap | 完全な Law | 期待する result.json |
| --- | --- | --- | --- |
| 三操作・shift=3 | [triangle-3](triangle-3.archmap.json) | [Coordinates](coordinates.law) | [反証](expected/triangle-3.result.json) |
| 三操作・shift=2 | [triangle-2](triangle-2.archmap.json) | [Coordinates](coordinates.law) | [成立と大域座標](expected/triangle-2.result.json) |
| 三操作・shift 未観測 | [triangle-missing](triangle-missing.archmap.json) | [Coordinates](coordinates.law) | [情報不足と構成済みの幾何](expected/triangle-missing.result.json) |
| コンパイル・add | [compiler-add](compiler-add.archmap.json) | [CompilerPreservation](compiler.law) | [保存成立](expected/compiler-add.result.json) |
| コンパイル・sub | [compiler-sub](compiler-sub.archmap.json) | [CompilerPreservation](compiler.law) | [反例](expected/compiler-sub.result.json) |
| コンパイル・演算子未観測 | [compiler-missing](compiler-missing.archmap.json) | [CompilerPreservation](compiler.law) | [情報不足](expected/compiler-missing.result.json) |

期待出力の `inputs` は入力ファイルの SHA-256 を記録する。これは入力の同一性を照合する値であり、
導出を検査したことの代わりにはしない。ファイル内容を変えた例は別の入力として再計算する。
