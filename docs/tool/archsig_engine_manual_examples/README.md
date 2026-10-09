# エンジンマニュアルの完全な入出力例

[マニュアル](../archsig_engine_manual.md)で定める外部インターフェースの入出力例である。
`.law` と ArchMap は省略のない入力ファイル、`expected/*.result.json` は実装が生成すべき
出力ファイルを表す。マニュアルとともに、利用者への約束と実装の受け入れ基準を定める。
外部仕様として採用する形式・機能の選択肢は、マニュアルの「確認する外部仕様」にまとめている。

マニュアルのコマンドは、このディレクトリをカレントディレクトリとした形で記載する。
`expected/` をエンジンに入力しない。受け入れテストでは、エンジン自身が二入力から作った出力と
照合する。期待例中の表示順・基底・証人は一例であり、意味の一致の基準はマニュアルに従う。

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
